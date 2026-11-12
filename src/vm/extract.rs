//! Recognizes VM structure in script syntax: the dispatch class, constructor, opcode handlers,
//! helper functions, state fields, and program runner. [`super::session`] evaluates what this
//! module finds.

use std::ptr;

use anyhow::{Context, Result, bail, ensure};
use oxc::ast::AstKind;
use oxc::ast::ast::{
    Argument as CallArgument, AssignmentExpression, AssignmentTarget, BindingIdentifier,
    BindingPattern, CallExpression, Class, ClassElement, Expression, FormalParameters, Function,
    FunctionBody, IdentifierReference, MemberExpression, MethodDefinitionKind, NewExpression,
    Statement, SwitchStatement,
};
use oxc::ast_visit::{Visit, walk};
use oxc::semantic::{ScopeFlags, SymbolId};
use oxc::span::GetSpan;
use oxc::syntax::operator::AssignmentOperator;

use super::registers::Derived;
use super::output::Position;
use super::{HashMap, convert};
use crate::candidates;
use crate::js::ast::{self, Binding, Script};

/// How the program runner reaches the machine's `run`: as a method on the machine, or as a free
/// function with the machine as its first argument. The two forms are the same machinery; which one
/// a build uses is not a VM change.
#[derive(Clone, Copy)]
pub(super) enum Receiver {
    /// `new Machine(p).run(...)`; the receiver is `this`.
    This,
    /// `run(new Machine(p), ...)`; the receiver is the run function's first parameter.
    Param(SymbolId),
}

/// The VM a program runner installs: the enclosing function body, the machine class, its `run`
/// function, and how `run` names the machine.
pub(super) struct Found<'a> {
    pub body: &'a FunctionBody<'a>,
    pub class: &'a Class<'a>,
    pub run: &'a Function<'a>,
    pub receiver: Receiver,
}

/// Finds the VM the unique program runner installs.
pub(super) fn vm<'a>(script: Script<'a>) -> Result<Found<'a>> {
    let runner = Runner::find(script)?;
    let class_symbol = script
        .symbol(runner.machine_class)
        .context("the program runner constructs a machine from no local class")?;
    // The machine class is declared as a statement in the enclosing function body; take the
    // innermost such body, as nested VMs may reuse names.
    let (body, class) = script
        .functions()
        .filter_map(|function| {
            let body = function.body.as_deref()?;
            let class = body.statements.iter().find_map(|statement| match statement {
                Statement::ClassDeclaration(class)
                    if class.id.as_ref().map(BindingIdentifier::symbol_id) == Some(class_symbol) =>
                {
                    Some(&**class)
                }
                _ => None,
            })?;
            Some((body, class))
        })
        .last()
        .context("the runner's machine class is declared in no function body")?;
    let (run, receiver) = match runner.run {
        RunCallee::Method => (
            method(class, "run").context("the machine class has no run method")?,
            Receiver::This,
        ),
        RunCallee::Free(name) => {
            let symbol = script
                .symbol(name)
                .context("the run function is not a local")?;
            let run = *functions(&body.statements)
                .get(&symbol)
                .context("the run function is not declared beside the machine class")?;
            let machine = parameter(&run.params, 0)
                .context("the run function takes no machine parameter")?;
            (run, Receiver::Param(machine.symbol_id()))
        }
    };
    Ok(Found {
        body,
        class,
        run,
        receiver,
    })
}

/// The register-file class, recognized by its digest accessor (a getter or setter). Every build so
/// far keeps the digest in a getter/setter pair, and no other VM class has accessors.
pub(super) fn register_class<'a>(script: Script<'a>) -> Result<&'a Class<'a>> {
    let classes = script.nodes.iter().filter_map(|node| match node.kind() {
        AstKind::Class(class) if has_accessor(class) => Some(class),
        _ => None,
    });
    candidates::exactly_one(classes, "register-file class")
}

/// Whether a class declares a getter or setter, other than in its constructor.
fn has_accessor(class: &Class<'_>) -> bool {
    class.body.body.iter().any(|element| {
        matches!(element, ClassElement::MethodDefinition(method)
            if matches!(method.kind, MethodDefinitionKind::Get | MethodDefinitionKind::Set))
    })
}

/// Collects the statements that run before the VM's scope is entered, both at script level and
/// in each enclosing function: at each level, the statements before the one containing `body`.
pub(super) fn prelude<'a>(
    script: Script<'a>,
    body: &'a FunctionBody<'a>,
) -> Vec<&'a Statement<'a>> {
    let mut enclosing: Vec<&'a [Statement<'a>]> = script
        .nodes
        .ancestor_kinds(body.node_id.get())
        .filter_map(|kind| match kind {
            AstKind::Function(function) => function.body.as_deref(),
            _ => None,
        })
        .filter(|enclosing| !ptr::eq(*enclosing, body))
        .map(|enclosing| &enclosing.statements[..])
        .collect();
    enclosing.push(&script.program.body);
    let mut prelude = Vec::new();
    for statements in enclosing.into_iter().rev() {
        let Some(index) = statements
            .iter()
            .position(|statement| statement.span().contains_inclusive(body.span))
        else {
            break;
        };
        prelude.extend(&statements[..index]);
    }
    prelude
}

/// Functions declared beside the class: handlers and their helpers.
pub(super) fn functions<'a>(
    statements: &'a [Statement<'a>],
) -> HashMap<SymbolId, &'a Function<'a>> {
    statements
        .iter()
        .filter_map(|statement| match statement {
            Statement::FunctionDeclaration(function) => {
                Some((function.id.as_ref()?.symbol_id(), &**function))
            }
            _ => None,
        })
        .collect()
}

/// Every parameter, if each is a plain identifier: no pattern, default, or rest.
pub(super) fn parameters<'a>(
    parameters: &'a FormalParameters<'a>,
) -> Option<Vec<&'a BindingIdentifier<'a>>> {
    if parameters.rest.is_some() {
        return None;
    }
    (0..parameters.items.len())
        .map(|index| parameter(parameters, index))
        .collect()
}

/// The parameter at `index`, if it is a plain identifier.
pub(super) fn parameter<'a>(
    parameters: &'a FormalParameters<'a>,
    index: usize,
) -> Option<&'a BindingIdentifier<'a>> {
    let parameter = parameters.items.get(index)?;
    match &parameter.pattern {
        BindingPattern::BindingIdentifier(name) if parameter.initializer.is_none() => Some(name),
        _ => None,
    }
}

/// The number of parameters, including a rest parameter.
pub(super) fn parameter_count(parameters: &FormalParameters<'_>) -> usize {
    parameters.items.len() + usize::from(parameters.rest.is_some())
}

/// The constructor's statements.
pub(super) fn constructor<'a>(class: &'a Class<'a>) -> Result<&'a [Statement<'a>]> {
    class
        .body
        .body
        .iter()
        .find_map(|element| match element {
            ClassElement::MethodDefinition(method)
                if method.kind == MethodDefinitionKind::Constructor =>
            {
                Some(&method.value.body.as_deref()?.statements[..])
            }
            _ => None,
        })
        .context("the VM class has no constructor")
}

/// What a `run` local holds.
#[derive(Clone)]
enum Source {
    Parameter(usize),
    /// `this.<name>`.
    Field(String),
    /// Register read as `<registers>.read(<index>)`. Both the register file and index come from
    /// fields.
    Register {
        registers: String,
        index: String,
    },
}

/// Register layout and state setup recovered from `run`.
pub(super) struct RunMethod<'ast> {
    /// Field containing the register file. Fields on that file identify the program counter and
    /// dispatch key registers.
    pub registers: String,
    /// Fields containing the cells and program register indices.
    pub cells: String,
    pub program: String,
    pub dispatch: DispatchLoop<'ast>,
}

/// Dispatch function declared beside the class and called by `run` with the machine. Some builds
/// move both loops out of `run`; both dispatch the same handlers.
pub(crate) struct DispatchLoop<'ast> {
    pub function: &'ast Function<'ast>,
    /// Argument values passed by `run`, in parameter order.
    pub arguments: Vec<Argument>,
}

/// Argument passed from `run` to a dispatch loop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Argument {
    Machine,
    Registers,
    Program,
    Other,
}

impl DispatchLoop<'_> {
    /// The parameter receiving the machine.
    fn machine(&self) -> Option<SymbolId> {
        let position = self
            .arguments
            .iter()
            .position(|argument| *argument == Argument::Machine)?;
        Some(parameter(&self.function.params, position)?.symbol_id())
    }
}

/// Tracks assignments in `run`, including copies of register fields and indices, program counter
/// and key setup, storing the cells argument in the cells register, reading the program register,
/// and calling dispatch loops. An unsupported assignment clears the known value of its local.
///
/// `run` is either the machine's `run` method (receiver `this`) or a free function taking the
/// machine first (receiver that parameter); `receiver` says which, and `derived` names the register
/// read and write accessors, which are free functions in current builds and methods in older ones.
pub(super) fn run_method<'a>(
    script: Script<'a>,
    functions: &HashMap<SymbolId, &'a Function<'a>>,
    run: &'a Function<'a>,
    receiver: Receiver,
    derived: &Derived,
) -> Result<RunMethod<'a>> {
    let body = run.body.as_deref().context("the run function has no body")?;
    let sources = (0..run.params.items.len())
        .filter_map(|index| {
            let name = parameter(&run.params, index)?;
            Some((Binding::Symbol(name.symbol_id()), Source::Parameter(index)))
        })
        .collect();
    let mut locals = Locals {
        script,
        sources,
        receiver,
        read: derived.read,
    };
    // The cells array is the run function's last argument: the trailing `[]`.
    let cells_argument = parameter_count(&run.params).checked_sub(1);
    let mut cells = None;
    let mut loaded = Vec::new();
    for statement in &body.statements {
        let Statement::ExpressionStatement(statement) = statement else {
            continue;
        };
        let expressions: Vec<&Expression<'a>> = match &statement.expression {
            Expression::SequenceExpression(sequence) => sequence.expressions.iter().collect(),
            expression => vec![expression],
        };
        for expression in expressions {
            if let Some((registers, index)) =
                cells_write(&locals, derived, expression, cells_argument)
            {
                cells = Some((registers, index));
                continue;
            }
            let Expression::AssignmentExpression(assignment) = expression else {
                continue;
            };
            let AssignmentTarget::AssignmentTargetIdentifier(name) = &assignment.left else {
                continue;
            };
            let value = match assignment.operator {
                AssignmentOperator::Assign => locals.source(&assignment.right),
                _ => None,
            };
            if let Some(Source::Register { registers, index }) = &value {
                loaded.push((registers.clone(), index.clone()));
            }
            let binding = script.binding(name);
            match value {
                Some(value) => locals.sources.insert(binding, value),
                None => locals.sources.remove(&binding),
            };
        }
    }
    let (registers, cells) =
        cells.context("the run function writes its cells argument to no register")?;
    loaded.retain(|(file, index)| *file == registers && *index != cells);
    loaded.sort();
    loaded.dedup();
    let [(_, program)] = &loaded[..] else {
        bail!(
            "the run method loads {} registers besides its arguments",
            loaded.len()
        );
    };
    let program = program.clone();
    let mut calls = DispatchCall {
        script,
        functions,
        receiver,
        found: None,
    };
    calls.visit_function_body(body);
    let (function, call) = calls
        .found
        .context("the run function calls no dispatch loop with the machine")?;
    let arguments = call
        .arguments
        .iter()
        .map(|argument| {
            let expression = ast::argument_expression(argument);
            if is_receiver(script, receiver, expression) {
                return Argument::Machine;
            }
            match expression {
                Expression::Identifier(name) => match locals.sources.get(&script.binding(name)) {
                    Some(Source::Field(field)) if *field == registers => Argument::Registers,
                    Some(Source::Register { index, .. }) if *index == program => Argument::Program,
                    _ => Argument::Other,
                },
                _ => Argument::Other,
            }
        })
        .collect();
    Ok(RunMethod {
        registers,
        cells,
        program,
        dispatch: DispatchLoop {
            function,
            arguments,
        },
    })
}

/// Whether `expression` is the run function's receiver: `this`, or the machine parameter.
fn is_receiver(script: Script<'_>, receiver: Receiver, expression: &Expression<'_>) -> bool {
    match receiver {
        Receiver::This => matches!(expression, Expression::ThisExpression(_)),
        Receiver::Param(symbol) => script.refers_to(expression, symbol),
    }
}

/// Recognizes `run` storing its cells argument in a register, as the method
/// `<registers>.write(<index>, cells)` or the free-function `write(<registers>, <index>, cells)`.
/// Returns the register-file field and the cells index field.
fn cells_write<'a>(
    locals: &Locals<'a>,
    derived: &Derived,
    expression: &Expression<'a>,
    cells_argument: Option<usize>,
) -> Option<(String, String)> {
    let is_cells = |source: Option<&Source>| {
        matches!(source, Some(Source::Parameter(index)) if Some(*index) == cells_argument)
    };
    if let Some((Source::Field(registers), arguments)) = locals.method_call(expression, "write")
        && let [Some(Source::Field(index)), cells] = &arguments[..]
        && is_cells(cells.as_ref())
    {
        return Some((registers, index.clone()));
    }
    let (callee, arguments) = ast::direct_call(expression)?;
    let symbol = locals.script.symbol(callee)?;
    if !derived.writes.contains(&symbol) {
        return None;
    }
    let [file, index, value] = arguments else {
        return None;
    };
    let source = |argument| locals.source(ast::argument_expression(argument));
    match (source(file), source(index), source(value)) {
        (Some(Source::Field(registers)), Some(Source::Field(index)), value)
            if is_cells(value.as_ref()) =>
        {
            Some((registers, index))
        }
        _ => None,
    }
}

/// Finds the first call in `run` whose first argument is the machine and whose target contains a
/// dispatch switch.
struct DispatchCall<'functions, 'a> {
    script: Script<'a>,
    functions: &'functions HashMap<SymbolId, &'a Function<'a>>,
    receiver: Receiver,
    found: Option<(&'a Function<'a>, &'a CallExpression<'a>)>,
}

impl<'a> Visit<'a> for DispatchCall<'_, 'a> {
    fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
        if self.found.is_none()
            && call
                .arguments
                .first()
                .is_some_and(|first| is_receiver(self.script, self.receiver, ast::argument_expression(first)))
            && let Expression::Identifier(callee) = &call.callee
            && let Some(symbol) = self.script.symbol(callee)
            && let Some(&function) = self.functions.get(&symbol)
            && first_switch_in(function).is_some()
        {
            self.found = Some((
                function,
                self.script.lend(call, AstKind::as_call_expression),
            ));
        }
        walk::walk_call_expression(self, call);
    }
}

/// The locals of `run` and what they hold.
struct Locals<'a> {
    script: Script<'a>,
    sources: HashMap<Binding<'a>, Source>,
    receiver: Receiver,
    /// The register read accessor, called as `read(<registers>, <index>)` in current builds.
    read: SymbolId,
}

impl<'a> Locals<'a> {
    /// Resolves `<object>.<name>(<arguments>)`, including the values of the object and
    /// arguments.
    fn method_call(
        &self,
        expression: &Expression<'a>,
        name: &str,
    ) -> Option<(Source, Vec<Option<Source>>)> {
        let (object, arguments) = ast::method_call(expression, name)?;
        let arguments = arguments
            .iter()
            .map(|argument| self.source(ast::argument_expression(argument)))
            .collect();
        Some((self.source(object)?, arguments))
    }

    fn source(&self, expression: &Expression<'a>) -> Option<Source> {
        match expression {
            Expression::Identifier(name) => self.sources.get(&self.script.binding(name)).cloned(),
            Expression::ParenthesizedExpression(paren) => self.source(&paren.expression),
            Expression::CallExpression(_) => self.register_read(expression),
            expression => Some(Source::Field(self.receiver_field(expression)?.to_owned())),
        }
    }

    /// Recognizes a register read as the method `<registers>.read(<index>)` or the free-function
    /// `read(<registers>, <index>)`.
    fn register_read(&self, expression: &Expression<'a>) -> Option<Source> {
        if let Some((Source::Field(registers), arguments)) = self.method_call(expression, "read")
            && let [Some(Source::Field(index))] = &arguments[..]
        {
            return Some(Source::Register {
                registers,
                index: index.clone(),
            });
        }
        let (callee, arguments) = ast::direct_call(expression)?;
        if self.script.symbol(callee) != Some(self.read) {
            return None;
        }
        let [file, index] = arguments else {
            return None;
        };
        match (
            self.source(ast::argument_expression(file)),
            self.source(ast::argument_expression(index)),
        ) {
            (Some(Source::Field(registers)), Some(Source::Field(index))) => {
                Some(Source::Register { registers, index })
            }
            _ => None,
        }
    }

    /// The field `receiver.<field>` reads, where the receiver is `this` or the machine parameter.
    fn receiver_field(&self, expression: &Expression<'a>) -> Option<&'a str> {
        let member = expression.as_member_expression()?;
        is_receiver(self.script, self.receiver, member.object()).then(|| ast::member_str(member))?
    }
}

/// The field `this.<field>` reads.
pub(super) fn this_field<'a>(expression: &Expression<'a>) -> Option<&'a str> {
    let member = expression.as_member_expression()?;
    match member.object() {
        Expression::ThisExpression(_) => ast::member_str(member),
        _ => None,
    }
}

/// Finds the string decryption function the register `read` accessor calls as
/// `decrypt(<registers>.<values>[index])`, where `registers` and `index` are `read`'s parameters.
pub(super) fn record_decoder<'a>(
    script: Script<'a>,
    read: &'a Function<'a>,
) -> Option<SymbolId> {
    /// Matches `<decoder>(<registers>.<values>[<index>])`.
    struct Decoders<'a> {
        script: Script<'a>,
        registers: SymbolId,
        index: SymbolId,
        found: Vec<Binding<'a>>,
    }

    impl<'a> Visit<'a> for Decoders<'a> {
        fn visit_call_expression(&mut self, call: &CallExpression<'a>) {
            if let Expression::Identifier(callee) = &call.callee
                && let [argument] = &call.arguments[..]
                && let Some(member) = ast::argument_expression(argument).as_member_expression()
                && member.object().as_member_expression().is_some_and(|values| {
                    self.script.refers_to(values.object(), self.registers)
                })
                && let MemberExpression::ComputedMemberExpression(member) = member
                && self.script.refers_to(&member.expression, self.index)
            {
                self.found.push(self.script.binding(callee));
            }
            walk::walk_call_expression(self, call);
        }
    }

    let mut decoders = Decoders {
        script,
        registers: parameter(&read.params, 0)?.symbol_id(),
        index: parameter(&read.params, 1)?.symbol_id(),
        found: Vec::new(),
    };
    decoders.visit_function(read, ScopeFlags::Function);
    let [Binding::Symbol(decoder)] = decoders.found[..] else {
        return None;
    };
    Some(decoder)
}

/// The method, getter, or setter named `name`, excluding the constructor.
pub(super) fn method<'a>(class: &'a Class<'a>, name: &str) -> Option<&'a Function<'a>> {
    class.body.body.iter().find_map(|element| match element {
        ClassElement::MethodDefinition(method)
            if method.kind != MethodDefinitionKind::Constructor
                && ast::static_key_str(&method.key, method.computed) == Some(name) =>
        {
            Some(&*method.value)
        }
        _ => None,
    })
}

/// Extracts opcode and handler pairs from `case <opcode>: <handler>(<machine>); break;`.
pub(super) fn handlers<'a>(
    script: Script<'a>,
    functions: &HashMap<SymbolId, &'a Function<'a>>,
    dispatch: &DispatchLoop<'a>,
) -> Result<HashMap<u8, &'a Function<'a>>> {
    let switch = first_switch_in(dispatch.function).context("the dispatch loop has no switch")?;
    let machine = dispatch.machine();
    let is_machine = |argument: &CallArgument<'_>| {
        argument.as_expression().is_some_and(|argument| {
            machine.is_some_and(|machine| script.refers_to(argument, machine))
        })
    };
    let mut handlers = HashMap::default();
    for case in &switch.cases {
        let Some(test) = &case.test else { continue };
        let Expression::NumericLiteral(opcode) = test else {
            bail!("a dispatch case is not a number");
        };
        let opcode = convert::byte(opcode.value).context("a dispatch case is not an opcode")?;
        let call = case
            .consequent
            .iter()
            .find_map(|statement| match statement {
                Statement::ExpressionStatement(statement) => match &statement.expression {
                    Expression::CallExpression(call) => Some(call),
                    _ => None,
                },
                _ => None,
            })
            .with_context(|| format!("dispatch case {opcode} calls no handler"))?;
        let Expression::Identifier(name) = &call.callee else {
            bail!("dispatch case {opcode} calls no named handler");
        };
        let function = script
            .symbol(name)
            .and_then(|symbol| functions.get(&symbol))
            .with_context(|| format!("no handler function {}", name.name))?;
        ensure!(
            matches!(&call.arguments[..], [argument] if is_machine(argument)),
            "dispatch case {opcode} does not pass {} only the machine",
            name.name
        );
        let previous = handlers.insert(opcode, *function);
        ensure!(previous.is_none(), "opcode {opcode} has two dispatch cases");
    }
    Ok(handlers)
}

/// Finds the first dispatch switch in the body of `function`.
fn first_switch_in<'a>(function: &'a Function<'a>) -> Option<&'a SwitchStatement<'a>> {
    function
        .body
        .as_deref()?
        .statements
        .iter()
        .find_map(first_switch)
}

/// Finds the first dispatch `switch`; both dispatch loops use the same form.
fn first_switch<'a>(statement: &'a Statement<'a>) -> Option<&'a SwitchStatement<'a>> {
    match statement {
        Statement::SwitchStatement(switch) => Some(switch),
        Statement::BlockStatement(block) => block.body.iter().find_map(first_switch),
        Statement::WhileStatement(looping) => first_switch(&looping.body),
        Statement::IfStatement(branch) => {
            first_switch(&branch.consequent).or_else(|| first_switch(branch.alternate.as_ref()?))
        }
        Statement::TryStatement(attempt) => attempt.block.body.iter().find_map(first_switch),
        _ => None,
    }
}

/// Where the program runner starts a program (see [`Runner`]).
pub(super) fn entry(body: &FunctionBody<'_>) -> Result<Position> {
    let runner = body
        .statements
        .iter()
        .find_map(|statement| match statement {
            Statement::ExpressionStatement(statement) => match &statement.expression {
                Expression::AssignmentExpression(assignment) => Runner::installed_by(assignment),
                _ => None,
            },
            _ => None,
        })
        .context("no program runner in the VM's scope")?;
    let pc = convert::position(runner.pc).context("the runner starts at no program position")?;
    let key = convert::byte(runner.key).context("the runner starts with no dispatch key")?;
    Ok(Position::new(pc, key))
}

/// How a runner body reaches `run`: as a method on the constructed machine, or as a free function
/// taking the machine first. Recognized by role, so a build moving `run` out of the class is not a
/// VM change.
enum RunCallee<'ast> {
    /// `new <Class>(p).run(pc, key, [])`.
    Method,
    /// `<run>(new <Class>(p), pc, key, [])`.
    Free(&'ast IdentifierReference<'ast>),
}

/// The program runner, installed by
/// `<global>.<name> = function(p) { return <run>(new <Class>(p), pc, key, []); }` (free-function
/// form) or `... return new <Class>(p).run(pc, key, []); ...` (method form).
struct Runner<'ast> {
    /// The global property the runner is installed under. The name is random.
    name: &'ast str,
    /// The class the runner constructs: the machine.
    machine_class: &'ast IdentifierReference<'ast>,
    /// How `run` is reached.
    run: RunCallee<'ast>,
    /// Initial program counter from the source.
    pc: f64,
    /// Initial dispatch key from the source.
    key: f64,
}

impl<'ast> Runner<'ast> {
    fn installed_by(assignment: &'ast AssignmentExpression<'ast>) -> Option<Self> {
        let target = assignment.left.as_member_expression()?;
        if matches!(target.object(), Expression::Super(_)) {
            return None;
        }
        let Expression::FunctionExpression(function) = &assignment.right else {
            return None;
        };
        let body = function.body.as_deref()?;
        if !body.directives.is_empty() {
            return None;
        }
        let [Statement::ReturnStatement(returned)] = after_bare_declarations(&body.statements)
        else {
            return None;
        };
        let name = ast::member_str(target)?;
        let (machine_class, run, pc, key) = run_invocation(returned.argument.as_ref()?)?;
        Some(Self {
            name,
            machine_class,
            run,
            pc,
            key,
        })
    }

    /// The single program runner the script installs.
    fn find(script: Script<'ast>) -> Result<Self> {
        let runners = script.nodes.iter().filter_map(|node| match node.kind() {
            AstKind::AssignmentExpression(assignment) => Runner::installed_by(assignment),
            _ => None,
        });
        candidates::exactly_one(runners, "program runner")
    }
}

/// Reads a runner's returned `run` invocation: the machine class, how `run` is reached, and the
/// initial program counter and dispatch key.
fn run_invocation<'ast>(
    returned: &'ast Expression<'ast>,
) -> Option<(&'ast IdentifierReference<'ast>, RunCallee<'ast>, f64, f64)> {
    // Method form: `new <Class>(p).run(pc, key, [])`.
    if let Some((object, [pc, key, ..])) = ast::method_call(returned, "run")
        && let Expression::NewExpression(new) = object
    {
        let (pc, key) = positions(ast::argument_expression(pc), ast::argument_expression(key))?;
        return Some((new_class(new)?, RunCallee::Method, pc, key));
    }
    // Free-function form: `<run>(new <Class>(p), pc, key, [])`.
    let Expression::CallExpression(call) = returned else {
        return None;
    };
    let Expression::Identifier(run) = &call.callee else {
        return None;
    };
    let [machine, pc, key, ..] = &call.arguments[..] else {
        return None;
    };
    let Expression::NewExpression(new) = ast::argument_expression(machine) else {
        return None;
    };
    let (pc, key) = positions(ast::argument_expression(pc), ast::argument_expression(key))?;
    Some((new_class(new)?, RunCallee::Free(run), pc, key))
}

/// The two numeric literals of a runner's initial program counter and key.
fn positions(pc: &Expression<'_>, key: &Expression<'_>) -> Option<(f64, f64)> {
    match (pc, key) {
        (Expression::NumericLiteral(pc), Expression::NumericLiteral(key)) => Some((pc.value, key.value)),
        _ => None,
    }
}

/// The class identifier a `new <Class>(...)` constructs.
fn new_class<'ast>(new: &'ast NewExpression<'ast>) -> Option<&'ast IdentifierReference<'ast>> {
    match &new.callee {
        Expression::Identifier(class) => Some(class),
        _ => None,
    }
}

/// Returns the installed program runner's name if exactly one exists (see [`Runner`]).
pub(crate) fn runner_name(script: Script<'_>) -> Option<String> {
    Runner::find(script).ok().map(|runner| runner.name.to_owned())
}

/// Whether `call` calls the runner `name` installs, as `name(...)` or `<global>.name(...)`.
pub(crate) fn calls_runner(call: &CallExpression<'_>, name: &str) -> bool {
    match call.callee.without_parentheses() {
        Expression::Identifier(callee) => callee.name == name,
        callee => callee.as_member_expression().is_some_and(|member| {
            !matches!(member.object(), Expression::Super(_))
                && ast::member_str(member) == Some(name)
        }),
    }
}

/// Skips leading `var x;` declarations. Deobfuscation removes helper objects used to calculate
/// `run` arguments but may leave their declarations.
fn after_bare_declarations<'b, 'a>(statements: &'b [Statement<'a>]) -> &'b [Statement<'a>] {
    let start = statements
        .iter()
        .position(|statement| {
            !matches!(statement, Statement::VariableDeclaration(declaration)
                if !declaration.kind.is_using()
                    && declaration.declarations.iter().all(|declarator| declarator.init.is_none()))
        })
        .unwrap_or(statements.len());
    &statements[start..]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::js::ast::ParsedScript;

    fn entry_of(source: &str) -> Result<Position> {
        let parsed = ParsedScript::parse("t", source).unwrap();
        let script = parsed.script();
        let Some(Statement::FunctionDeclaration(function)) = script.program.body.first() else {
            panic!("the test source declares no function");
        };
        entry(function.body.as_deref().unwrap())
    }

    #[test]
    fn finds_the_entry_past_leftover_declarations() {
        for source in [
            "function f(O) { O.vlJM8 = function(p) { return new M(p).run(0, 238, []); }; }",
            "function f(O) { O.vlJM8 = function(p) { var a; var b, c; return new M(p).run(0, 238, []); }; }",
        ] {
            assert_eq!(entry_of(source).unwrap(), Position::new(0, 238), "{source}");
        }
        let source = "function f(O) { O.vlJM8 = function(p) { var a = g(); return new M(p).run(0, 238, []); }; }";
        assert!(
            entry_of(source).is_err(),
            "a body that does more than return is not the entry"
        );
    }

    #[test]
    fn names_the_runner_its_callers_call() {
        let parsed = ParsedScript::parse(
            "t",
            "O.vlJM8 = function(p) { return new M(p).run(0, 238, []); }; \
             O.other = function(p) { return M(p).run(0, 238, []); }; O.vlJM8('a'); vlJM8('b');",
        )
        .unwrap();
        let script = parsed.script();
        let name = runner_name(script).unwrap();
        assert_eq!(name, "vlJM8");
        let calls: Vec<&CallExpression<'_>> = script
            .program
            .body
            .iter()
            .filter_map(|statement| match statement {
                Statement::ExpressionStatement(statement) => match &statement.expression {
                    Expression::CallExpression(call) => Some(&**call),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        assert_eq!(calls.len(), 2);
        assert!(calls.iter().all(|call| calls_runner(call, &name)));
    }
}
