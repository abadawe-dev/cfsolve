//! Runs a challenge-page orchestrator, a separate session on the page's origin, around its
//! widget. Its first response renders the widget; its second payload reports the widget's
//! completion, and the response submits a clearance form that sets `cf_clearance`. On a
//! precursor interstitial, the first response loads Cloudflare's precursor script instead of a
//! widget, and the second payload reports that the script ran.

use anyhow::{Context, Result, bail, ensure};
use serde::Serialize;
use url::Url;
use wreq::StatusCode;

use super::Sink;
use super::channel::{Channel, Origin, Stage, Submission};
use super::initial::{self, EmbeddingPage, FirstPayload};
use super::timing::{self, Timer};
use super::widget::{Clearance, Completion, Embedding, WidgetSession};
use crate::browser::Page;
use crate::challenge::orchestrator::{self, ChallengePage};
use crate::challenge::payload;
use crate::challenge::program::{PreparedSession, SessionEncoder};
use crate::challenge::reduced_timing::{Entry, ResourceTiming};
use crate::challenge::source::InitialRequest;
use crate::challenge::state::{Intervals, ScriptState};
use crate::embedding_page::challenge_page::WIDGET_HOST;
use crate::embedding_page::extra_params::{self, ApiScript};
use crate::embedding_page::page::{Params, RenderedPage};
use crate::embedding_page::render_sample::RenderSample;
use crate::engine::{self, Engine, Lines};
use crate::error::Refused;
use crate::http::{self, BrowserClient, PageDocument, ReferrerPolicy, ScriptLoad};
use crate::js::{JsValue, Options, Payload, Window};
use crate::resource_timing::{LoadTiming, Phases, ResourceMeasurement};
use crate::script::Source;
use crate::stage2::call_stack::{self, CaseOpcodes, ScriptPosition};
use crate::stage2::challenge_page::{self, CompletionTarget, Form, PrecursorProgram, Settled, WidgetProgram};
use crate::stage2::payload::{Environment, State};
use crate::{embedding_page, performance_clock};

/// `clearance-form.json`: where the clearance form posts, and its fields in order.
#[derive(Serialize)]
struct ClearanceFormJson<'form> {
    action: &'form str,
    fields: &'form [(String, String)],
}

/// The orchestrator's state between its first payload and its second, whichever program its
/// first response runs.
struct Orchestration {
    challenge: ChallengePage,
    /// The deobfuscated orchestrator, whose VM runs every returned program.
    source: Source,
    request: InitialRequest,
    encoder: SessionEncoder,
    state: ScriptState,
    /// The first payload, which the response program receives.
    first: Payload,
    /// Window values read by the response program.
    window: Window,
    /// When the response program created its record.
    record_started_ms: i64,
    /// Page navigation and subsequent orchestrator, loader, and icon requests.
    navigation: LoadTiming,
    loads: Vec<LoadTiming>,
    post: LoadTiming,
    /// Fetch phase estimates used when only total duration is measured.
    phases: Phases,
}

/// The orchestrator's session, between its first payload and its second, around the widget its
/// first response renders.
pub(crate) struct OrchestratorSession {
    orchestration: Orchestration,
    widget: WidgetProgram,
    callback_ms: i64,
}

/// A precursor interstitial's orchestrator session, between its first payload and its second.
/// Its first response loads the precursor script instead of rendering a widget.
pub(crate) struct PrecursorSession {
    orchestration: Orchestration,
    program: PrecursorProgram,
}

/// The orchestrator after its first response, by what that response's program does.
pub(crate) enum Begun {
    /// It rendered a widget, whose completion the orchestrator reports.
    Widget(Box<OrchestratorSession>, Box<EmbeddingPage>),
    /// It loads the precursor script, whose completion the orchestrator reports instead.
    Precursor(Box<PrecursorSession>),
}

/// Builds the orchestrator's first payload, with frame-check results and timestamps based on
/// build time, since no `extraParams` merge happens.
pub(crate) fn first_payload(
    sink: &dyn Sink,
    source: &Source,
    page: &Url,
    intervals: &Intervals,
) -> Result<FirstPayload> {
    let prepared = PreparedSession::try_new(source, page)?;
    let state = prepared.state()?;
    FirstPayload::build(
        sink,
        prepared.into_program(),
        state,
        intervals,
        "orchestrator-options.json",
        |options| {
            let framing = orchestrator::frame_options(source, options);
            options.extend(framing);
            // Marked as long before now as the payload's timestamps say it takes to send, so it
            // goes out as soon as it is built rather than idling after the time spent
            // deobfuscating: a browser whose script ran that much shorter.
            let send = intervals.handoff + 1 + intervals.send;
            (None, performance_clock::epoch_ms() - send)
        },
    )
}

/// Rebuilds the stack sampled by the loader during the orchestrator's `turnstile.render` call.
/// Includes loader frames and session-script frames from the VM call to the listener running
/// the widget program's `onload` callback.
///
/// In Chrome captures, the program calls the callback inside its own exception handler. In iOS
/// Safari captures, the loader finishes later and its timer calls the callback without a
/// registered handler.
pub(super) fn render_sample(
    api: &ApiScript,
    challenge: &ChallengePage,
    javascript: &str,
    cases: &CaseOpcodes,
    widget: &WidgetProgram,
    engine: Engine,
) -> Result<RenderSample> {
    // The session script puts the page's inline script before the orchestrator.
    let (inline_lines, _) = engine::line_and_column(&challenge.javascript(""), Lines::Script);
    let guarded = engine == Engine::Chromium;
    let geometry = call_stack::recover_method_call(javascript, cases, widget.render_call, guarded)?
        .rebased(inline_lines);
    let origin = ScriptPosition {
        url: challenge.orchestrator.to_string(),
        line: 0,
        column: 0,
    };
    let frames = geometry.placed(&origin, engine);
    RenderSample::explicit(&api.source, api.stack_url(engine), frames, engine)
}

/// Runs the orchestrator through its first response. If that response renders a widget,
/// reconstructs the page around the widget.
pub(crate) async fn begin(
    client: &BrowserClient,
    sink: &dyn Sink,
    page: &Page,
    navigation: LoadTiming,
    challenge: ChallengePage,
    referrer_policy: ReferrerPolicy,
) -> Result<Begun> {
    sink.save("page.html", challenge.html.as_bytes())?;
    let pacing = &page.orchestrator_pacing;
    let timer = Timer::start();
    let script = http::fetch_page_script(client, &challenge.orchestrator, &challenge.loading)
        .await
        .context("loading the orchestrator")?;
    let script_fetch = timer.overall(challenge.orchestrator.as_str(), script.len() as u64);
    sink.save("orchestrator.js", script.as_bytes())?;
    // The orchestrator's header shows the site's icon as it starts. Deobfuscation runs on its
    // own thread meanwhile.
    let icon_url = challenge.url.join("/favicon.ico")?;
    let icon = async {
        let timer = Timer::start();
        let icon = http::fetch_page_image(client, &challenge.url, &icon_url).await?;
        anyhow::Ok(timer.overall(icon_url.as_str(), icon.encoded_bytes))
    };
    let javascript = challenge.javascript(&script);
    sink.progress(&format!(
        "Fetched the {}-byte orchestrator; deobfuscating it with the page's options",
        script.len()
    ));
    let ((text, cases), icon) =
        tokio::try_join!(initial::deobfuscate(sink, javascript.clone()), icon)?;
    sink.save("orchestrator.deobfuscated.js", text.as_bytes())?;
    let source = Source::try_new(&text).context("parsing the deobfuscated orchestrator")?;

    let intervals = &pacing.intervals;
    let mut first = first_payload(sink, &source, &challenge.url, intervals)?;
    let options = &first.program.request.options;
    let send_at = first.marked_ms + intervals.handoff + 1 + intervals.send;
    payload::append_send_time_at(&mut first.plaintext, &first.state, options, send_at);
    let submission = Submission {
        plaintext: first.plaintext,
        send_at,
    };
    let encoder = first.program.session_encoder()?;
    let channel = Channel {
        client,
        sink,
        origin: Origin::Page(&challenge.url),
        request: &first.program.request,
        encoder: &encoder,
    };
    let returned = channel.submit(&submission, Stage::Orchestrator).await?;
    let listing = source.disassemble(&returned.program)?;
    let record_started_ms = returned.received_ms + i64::from(pacing.program_startup_ms);
    // The response program's template reads initial-program globals, values read by the first
    // payload, then globals set by the response program.
    let mut window = first.window;
    window.extend(first.globals);
    if !challenge_page::renders_widget(&listing) {
        let program =
            PrecursorProgram::recover(&listing).context("reading the precursor program")?;
        window.extend(program.window.clone());
        let orchestration = Orchestration {
            challenge,
            source,
            request: first.program.request,
            encoder,
            state: first.state,
            first: submission.plaintext,
            window,
            record_started_ms,
            navigation,
            loads: vec![script_fetch, icon],
            post: returned.fetch,
            phases: page.resource_timing.phases,
        };
        return Ok(Begun::Precursor(Box::new(PrecursorSession {
            orchestration,
            program,
        })));
    }
    let widget = WidgetProgram::recover(&listing).context("reading the widget program")?;
    window.extend(widget.window.clone());
    let parameters = widget.render_parameters(options, &window)?;
    sink.json("widget-parameters.json", &parameters)?;
    let loader = orchestrator::loader_url(&source, options)?;
    // Use the server-selected language from the message table as the document's `lang`.
    let language = orchestrator::language(options)
        .context("the orchestrator's message table names no one language")?;
    let ray = first.program.request.ray()?;
    let rendered = embedding_page::challenge_page::render(&challenge, &loader, language, ray)?;
    sink.save("rendered-page.html", rendered.as_bytes())?;
    let rendered = RenderedPage::render_explicit(
        &rendered,
        challenge.url.clone(),
        &extra_params::widget_id(),
        WIDGET_HOST,
        Params::from_render(&parameters)?,
    )?;
    let (mut api, api_fetch) = initial::fetch_loader(
        client,
        loader,
        ScriptLoad::Anonymous,
        &challenge.url,
        referrer_policy,
        page,
    )
    .await?;
    match render_sample(
        &api,
        &challenge,
        &javascript,
        &cases,
        &widget,
        client.engine(),
    ) {
        Ok(sample) => api.render_sample = sample,
        Err(error) => sink.progress(&format!(
            "Warning: the orchestrator's render call has no recovered stack, so the loader \
             reports a markup render: {error:#}"
        )),
    }
    let embedding_page = EmbeddingPage::new(
        sink,
        rendered,
        api,
        page.layout.on_challenge_page(),
        referrer_policy,
        Embedding::ChallengePage,
    );
    let orchestration = Orchestration {
        challenge,
        source,
        request: first.program.request,
        encoder,
        state: first.state,
        first: submission.plaintext,
        window,
        record_started_ms,
        navigation,
        loads: vec![script_fetch, api_fetch, icon],
        post: returned.fetch,
        phases: page.resource_timing.phases,
    };
    let orchestrator = OrchestratorSession {
        orchestration,
        widget,
        callback_ms: pacing.callback_ms.into(),
    };
    Ok(Begun::Widget(
        Box::new(orchestrator),
        Box::new(embedding_page),
    ))
}

impl OrchestratorSession {
    /// Reports the completion of `widget`'s session and submits the returned clearance form for
    /// the protected page, through the same client.
    pub(crate) async fn clear(
        &self,
        widget: &WidgetSession<'_>,
        completion: Completion,
    ) -> Result<Clearance> {
        let orchestration = &self.orchestration;
        let settled = Settled {
            after_challenge: challenge_page::completion_extra(&completion.listing),
            token: completion.token,
            started_ms: orchestration.record_started_ms,
            ended_ms: completion.received_ms + self.callback_ms,
        };
        let mut options = orchestration.request.options.clone();
        if let Some(timing) = &widget.merged.state.timing {
            let iframe = ProgramLoad::Iframe(&widget.fetched.navigation);
            let entries = orchestration.page_resource_timing(timing, Some(iframe));
            options.insert(timing.option.clone(), JsValue::Array(entries));
        }
        let calls = Window::new();
        let state = State {
            environment: Environment {
                options: &options,
                window: &orchestration.window,
                calls: &calls,
            },
            input: &orchestration.first,
        };
        let plaintext = self.widget.payload(&state, &settled)?;
        let send_at = settled.ended_ms + 1;
        orchestration
            .clear(widget.client, widget.sink, &options, plaintext, send_at)
            .await
    }
}

impl PrecursorSession {
    /// Runs the first response's program as it loads the challenge address it built, reports that
    /// it ran, and submits the returned clearance form for the protected page.
    ///
    /// Two builds reach here. A script-loading precursor concatenates a script address on the
    /// page's own origin, which the program inserts and whose `onload` closes the record; it is
    /// fetched over a GET. A direct-submit build (EB Games) concatenates the challenge's own
    /// `/fo/` payload endpoint and hands it to the orchestrator's sender, which posts the second
    /// payload straight to it — the same endpoint the first payload used — with no script to load.
    pub(crate) async fn clear(&self, client: &BrowserClient, sink: &dyn Sink) -> Result<Clearance> {
        let orchestration = &self.orchestration;
        let target = self.program.target(
            &orchestration.request.options,
            &orchestration.window,
            &orchestration.challenge.url,
        )?;
        match target {
            CompletionTarget::Script(script) => self.load_script(client, sink, &script).await,
            CompletionTarget::Submit(endpoint) => self.submit(client, sink, &endpoint).await,
        }
    }

    /// The script-loading precursor path: fetches the precursor script over a GET, times the load,
    /// reports that it ran, and submits with the script's resource-timing entry included.
    async fn load_script(
        &self,
        client: &BrowserClient,
        sink: &dyn Sink,
        script: &Url,
    ) -> Result<Clearance> {
        let orchestration = &self.orchestration;
        // The program creates its record, then inserts the script into the page, whose address
        // the orchestrator has restored by now. The script calls back as soon as it has run,
        // which closes the record.
        timing::sleep_until(orchestration.record_started_ms).await;
        let timer = Timer::start();
        let source = http::fetch_page_script(client, script, &orchestration.challenge.url)
            .await
            .context("loading the precursor script")?;
        let load = timer.overall(script.as_str(), source.len() as u64);
        sink.save("precursor.js", source.as_bytes())?;
        sink.progress(&format!(
            "The orchestrator loaded the {}-byte precursor script instead of a widget; reporting \
             that it ran",
            source.len()
        ));
        let ended_ms = load.ended_ms() as i64;
        let plaintext = |options: &Options| {
            let calls = Window::new();
            let state = State {
                environment: Environment {
                    options,
                    window: &orchestration.window,
                    calls: &calls,
                },
                input: &orchestration.first,
            };
            self.program
                .payload(&state, orchestration.record_started_ms, ended_ms)
        };
        orchestration
            .report(
                client,
                sink,
                Some(ProgramLoad::Script(&load)),
                ended_ms,
                plaintext,
            )
            .await
    }

    /// The direct-submit path (EB Games): the program built the challenge's own `/fo/` payload
    /// endpoint, not a script, so there is no load. It opens and closes its record in the same
    /// synchronous turn (duration zero) and posts the second payload straight to that endpoint,
    /// which is the orchestrator's own POST URL.
    async fn submit(&self, client: &BrowserClient, sink: &dyn Sink, address: &Url) -> Result<Clearance> {
        let orchestration = &self.orchestration;
        ensure!(
            *address == orchestration.request.url,
            "the program posts its second payload to {address}, not the orchestrator's endpoint {}",
            orchestration.request.url
        );
        sink.progress(
            "The orchestrator posts its second payload straight to the challenge endpoint instead \
             of loading a precursor script; reporting that it ran",
        );
        // No script loads, so the record spans no time: it opens when the program starts and
        // closes in the same turn, before the orchestrator sends.
        let marked_ms = orchestration.record_started_ms;
        let plaintext = |options: &Options| {
            let calls = Window::new();
            let state = State {
                environment: Environment {
                    options,
                    window: &orchestration.window,
                    calls: &calls,
                },
                input: &orchestration.first,
            };
            self.program.payload(&state, marked_ms, marked_ms)
        };
        orchestration
            .report(client, sink, None, marked_ms, plaintext)
            .await
    }
}

impl Orchestration {
    /// The page's resource timing as the response program reads it, ending with `load` when the
    /// program starts one. A program that posts straight to the challenge endpoint starts none,
    /// so `load` is `None` and the snapshot omits the trailing load entry.
    fn page_resource_timing(
        &self,
        timing: &ResourceTiming,
        load: Option<ProgramLoad<'_>>,
    ) -> Vec<JsValue> {
        page_resource_timing(
            timing,
            self.phases,
            &self.navigation,
            &self.loads,
            &self.post,
            load,
        )
    }

    /// Reports a first-response program's completion. Adds the program's resource-timing read
    /// (ending with `load`, or omitting the trailing entry when the program started none) to the
    /// options, builds the second payload from those options, and clears the page by sending it
    /// one millisecond after the record's `ended_ms`.
    async fn report(
        &self,
        client: &BrowserClient,
        sink: &dyn Sink,
        load: Option<ProgramLoad<'_>>,
        ended_ms: i64,
        plaintext: impl FnOnce(&Options) -> Result<Payload>,
    ) -> Result<Clearance> {
        let mut options = self.request.options.clone();
        if let Some(timing) = &self.state.timing {
            let entries = self.page_resource_timing(timing, load);
            options.insert(timing.option.clone(), JsValue::Array(entries));
        }
        let plaintext = plaintext(&options)?;
        self.clear(client, sink, &options, plaintext, ended_ms + 1)
            .await
    }

    /// Sends the second payload, `plaintext`, at `send_at`, and obtains the protected page.
    ///
    /// Two terminal shapes reach the page. A managed challenge grants clearance on the completion
    /// POST itself: the response sets `cf_clearance` and its program reloads the protected page.
    /// A precursor or widget challenge returns a clearance form whose submission sets the cookie.
    /// They are told apart by whether the POST set `cf_clearance`.
    async fn clear(
        &self,
        client: &BrowserClient,
        sink: &dyn Sink,
        options: &Options,
        mut plaintext: Payload,
        send_at: i64,
    ) -> Result<Clearance> {
        payload::append_send_time_at(&mut plaintext, &self.state, options, send_at);
        let channel = Channel {
            client,
            sink,
            origin: Origin::Page(&self.challenge.url),
            request: &self.request,
            encoder: &self.encoder,
        };
        let submission = Submission { plaintext, send_at };
        let returned = channel.submit(&submission, Stage::Clearance).await?;
        // A managed challenge grants clearance on the completion POST itself (its response sets
        // `cf_clearance` and reloads the page it rewrote itself to while orchestrating); a
        // precursor or widget challenge returns a clearance form whose submission sets the cookie.
        let cleared = if self.granted_clearance(client) {
            sink.progress("The completion POST set cf_clearance; reloading the page it cleared");
            http::navigate(client, &self.challenge.loading).await?
        } else {
            self.submit_clearance_form(client, sink, options, &returned.program)
                .await?
        };
        sink.save("cleared.html", cleared.html.as_bytes())?;
        // The cleared page must come back unchallenged. A cookie that leaves the guarded page
        // still challenging is not a working clearance, so `accept_clearance` rejects it.
        let challenged = ChallengePage::parse(&cleared.html, &cleared.url)?.is_some();
        let cookies = client.cookies(&cleared.url);
        let clearance = cookies
            .iter()
            .find(|cookie| cookie.name() == "cf_clearance")
            .map(|cookie| cookie.value().to_owned());
        let clearance = accept_clearance(cleared.status, challenged, clearance)?;
        sink.progress(&format!(
            "Cleared the challenge: {} answered HTTP {} with the page ({} bytes)",
            cleared.url,
            cleared.status,
            cleared.html.len()
        ));
        Ok(Clearance {
            clearance,
            cookies,
            page: cleared,
        })
    }

    /// Whether the challenge URL now carries a `cf_clearance` cookie, which a managed challenge's
    /// completion POST sets. This selects the reload terminal over the clearance-form one; the
    /// reload must still come back unchallenged for the clearance to count.
    fn granted_clearance(&self, client: &BrowserClient) -> bool {
        client
            .cookies(&self.challenge.url)
            .iter()
            .any(|cookie| cookie.name() == "cf_clearance")
    }

    /// Recovers the clearance form from the completion response `program` and submits it, with the
    /// restored page address as its referrer. Returns the protected page the form submission
    /// reaches.
    async fn submit_clearance_form(
        &self,
        client: &BrowserClient,
        sink: &dyn Sink,
        options: &Options,
        program: &[u8],
    ) -> Result<PageDocument> {
        let listing = self.source.disassemble(program)?;
        let form = Form::recover(&listing).context("reading the clearance program")?;
        let form = form.resolve(options, &self.window, &self.challenge.url)?;
        let saved = ClearanceFormJson {
            action: form.action.as_str(),
            fields: &form.fields,
        };
        sink.json("clearance-form.json", &saved)?;
        let referer = self
            .challenge
            .answered
            .as_ref()
            .unwrap_or(&self.challenge.url);
        http::submit_form(client, referer, &form.action, &form.fields).await
    }
}

/// Decides whether the challenge cleared, from the cleared page — the clearance form's response,
/// or the reload after a managed grant: its HTTP status, whether it is another challenge page,
/// and the `cf_clearance` cookie, if any. Returns the cookie's value.
///
/// Cloudflare sets `cf_clearance` when the challenge passes. After that, the protected page can
/// still answer with an error status. For example, a site's waiting room can answer HTTP 429 to
/// the visitors it is queueing. So an error status with the cookie still counts as a pass.
/// Another challenge page means the clearance does not work — the guarded page is still
/// challenged, so the cookie is no clearance — and an error status without the cookie means the
/// answers were refused.
pub(crate) fn accept_clearance(
    status: StatusCode,
    challenged: bool,
    clearance: Option<String>,
) -> Result<String> {
    let refused = || {
        let message = format!("the protected page returned HTTP {status} without clearing");
        Refused::new(Stage::Clearance, message)
    };
    if challenged {
        bail!(refused());
    }
    match clearance {
        Some(clearance) => Ok(clearance),
        None if !status.is_success() => bail!(refused()),
        None => bail!("the challenge set no `cf_clearance` cookie"),
    }
}

/// The load a first response's program starts, which ends the page's resource timing.
#[derive(Clone, Copy)]
pub(crate) enum ProgramLoad<'load> {
    /// The widget's iframe. Only its end time is exposed for the cross-origin iframe.
    Iframe(&'load LoadTiming),
    /// The precursor script, on the page's own origin.
    Script(&'load LoadTiming),
}

/// Builds two resource timing snapshots for the response program. The first includes the
/// unfinished navigation and later loads. The second includes the finished navigation, first
/// POST, a second icon entry, and the program's own `load` when it starts one. Estimates
/// unmeasured phases.
#[must_use]
pub(crate) fn page_resource_timing(
    timing: &ResourceTiming,
    phases: Phases,
    navigation: &LoadTiming,
    loads: &[LoadTiming],
    post: &LoadTiming,
    load: Option<ProgramLoad<'_>>,
) -> Vec<JsValue> {
    // Times run from the challenge page's navigation.
    let since = |load: &LoadTiming| (load.started_ms - navigation.started_ms) as f64;
    let reduce = |load: &LoadTiming, measured: ResourceMeasurement| {
        timing.reduce(&Entry {
            name: &load.url,
            start: since(load),
            measured,
        })
    };
    let estimate = |fetch: &LoadTiming| {
        reduce(
            fetch,
            ResourceMeasurement::estimated(fetch.duration_ms, fetch.body_bytes, phases),
        )
    };
    let loading = ResourceMeasurement {
        duration: 0.0,
        ..ResourceMeasurement::estimated(navigation.duration_ms, navigation.body_bytes, phases)
    };
    let loaded_ms = loads
        .iter()
        .map(LoadTiming::ended_ms)
        .fold(navigation.ended_ms(), f64::max);
    let loaded = ResourceMeasurement {
        duration: loaded_ms - navigation.started_ms as f64,
        ..loading
    };
    let mut entries = vec![reduce(navigation, loading)];
    entries.extend(loads.iter().map(estimate));
    entries.push(reduce(navigation, loaded));
    entries.push(timing.entry(post, navigation.started_ms));
    entries.extend(loads.last().map(estimate));
    entries.extend(load.map(|load| match load {
        ProgramLoad::Iframe(iframe) => {
            let end = since(iframe) + iframe.duration_ms;
            reduce(
                iframe,
                ResourceMeasurement::restricted(iframe.duration_ms, end),
            )
        }
        ProgramLoad::Script(script) => estimate(script),
    }));
    entries
}
