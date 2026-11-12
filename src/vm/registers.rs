//! The VM register file, whose read and write accessors reach 256 registers.
//!
//! Each value has a type tag and is masked by a rolling `state`. A digest updated on every write
//! determines the mask. Separate fields hold the program counter and dispatch key. Handlers access
//! registers through the accessor functions, direct tag and value writes, or the counter and key
//! fields.
//!
//! The interpreter keeps the mask and digest at zero. Stored values are therefore unmasked, and
//! changing the mask has no effect.
//!
//! Field and accessor names are reshuffled by Cloudflare per build and collide across builds, so
//! [`Members`] derives each name's role from the structure of the accessor functions rather than a
//! fixed name table. [`derive`] recognizes the read accessor, the write router, and the counter and
//! key setters, extracts the role of every field they touch, and fails loudly on an ambiguous or
//! incomplete recovery.

use anyhow::{Context, Result, bail, ensure};
use oxc::ast::ast::{
    BinaryExpression, Class, ClassElement, Expression, Function, MethodDefinitionKind, Statement,
};
use oxc::ast_visit::{Visit, walk};
use oxc::semantic::SymbolId;
use oxc::syntax::operator::BinaryOperator;

use super::extract;
use super::{HashMap, HashSet};
use crate::candidates;
use crate::js;
use crate::js::ast::{self, Script};

/// Meaning of a field or accessor on the register file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Member {
    /// Read accessors: `read(index)` and `save(index)`. They differ only for closures.
    Read,
    /// Write accessors: `write(index, value)` and `restore(index, value)`. They differ only for
    /// closures.
    Write,
    /// Rolling mask, the digest used to compute it, and the digest's backing fields.
    Mask,
    /// Flag indicating whether the program counter or dispatch key holds a masked integer.
    Integer,
    Pc,
    Key,
    /// Program counter or dispatch key value when it is not an integer.
    OtherPc,
    OtherKey,
    /// Register indices for the program counter and dispatch key.
    PcIndex,
    KeyIndex,
    Values,
    Tags,
}

/// The role of each register-file field and accessor in one session's VM. Derived from structure;
/// see [`derive`].
#[derive(Clone, Debug, Default)]
pub(crate) struct Members {
    roles: HashMap<String, Member>,
}

impl Members {
    #[must_use]
    pub(crate) fn of(&self, name: &str) -> Option<Member> {
        self.roles.get(name).copied()
    }

    /// Inserts `name` as `role`, failing if `name` already holds a different role.
    fn insert(&mut self, name: &str, role: Member) -> Result<()> {
        if let Some(previous) = self.roles.insert(name.to_owned(), role)
            && previous != role
        {
            bail!("register field {name:?} is both {previous:?} and {role:?}");
        }
        Ok(())
    }

    /// The register name table the pattern templates are written in (one earlier build's names).
    /// Template matching resolves these to roles and compares roles with the actual build's
    /// derived names, so a reshuffle of the field names still matches. Also used by the interpreter
    /// unit tests that exercise recognition on synthetic old-shape helpers.
    pub(crate) fn legacy() -> Self {
        let roles = [
            ("read", Member::Read),
            ("save", Member::Read),
            ("write", Member::Write),
            ("restore", Member::Write),
            ("state", Member::Mask),
            ("digest", Member::Mask),
            ("I", Member::Mask),
            ("J", Member::Mask),
            ("i", Member::Integer),
            ("l", Member::Integer),
            ("h", Member::Pc),
            ("j", Member::Key),
            ("v", Member::OtherPc),
            ("u", Member::OtherKey),
            ("C", Member::PcIndex),
            ("D", Member::KeyIndex),
            ("values", Member::Values),
            ("H", Member::Tags),
        ];
        Self {
            roles: roles.iter().map(|(name, role)| ((*name).to_owned(), *role)).collect(),
        }
    }
}

/// The register-file roles plus the accessor functions the interpreter runs natively.
pub(crate) struct Derived {
    pub(crate) members: Members,
    /// The read accessor function (`registers.read`'s free-function form).
    pub(crate) read: SymbolId,
    /// The write-router functions (`registers.write`'s free-function form, and its simpler
    /// variants). Both route the program counter and dispatch key to their setters.
    pub(crate) writes: HashSet<SymbolId>,
}

/// Field roles a register setter (`In`/`Ig`) defines.
#[derive(Clone)]
struct Setter {
    symbol: SymbolId,
    /// `is-integer` flag field.
    flag: String,
    /// Masked integer value field.
    value: String,
    /// Non-integer value field.
    other: String,
    /// Mask field XORed with the integer value.
    mask: String,
}

/// A program-counter or dispatch-key route from the write router.
struct Route {
    /// Index field compared to the write index (`PcIndex`/`KeyIndex`).
    index: String,
    /// The setter the route calls.
    setter: SymbolId,
}

/// Fields the read accessor identifies.
struct Read {
    symbol: SymbolId,
    tags: String,
    values: String,
    pc_index: String,
}

/// Derives the register-file member roles for the VM `functions` declare beside the class.
///
/// `class` is the register-file class, found by its digest accessor; its backing fields are masks.
pub(crate) fn derive(
    script: Script<'_>,
    functions: &HashMap<SymbolId, &Function<'_>>,
    class: &Class<'_>,
) -> Result<Derived> {
    let setters: Vec<Setter> = functions
        .iter()
        .filter_map(|(symbol, function)| setter(script, *symbol, function))
        .collect();
    let routes: Vec<Route> = functions
        .values()
        .flat_map(|function| router_routes(script, function))
        .collect();
    let reads: Vec<Read> = functions
        .iter()
        .filter_map(|(symbol, function)| read(script, *symbol, function))
        .collect();
    let read = candidates::exactly_one(reads, "register read accessor")?;

    // The read accessor names the program-counter index; the route on it is the counter's.
    let pc_route = routes
        .iter()
        .find(|route| route.index == read.pc_index)
        .context("no write-router route for the program-counter index")?;
    let key_route = routes
        .iter()
        .find(|route| route.index != read.pc_index)
        .context("no write-router route for the dispatch-key index")?;
    let pc_setter = find_setter(&setters, pc_route.setter, "program counter")?;
    let key_setter = find_setter(&setters, key_route.setter, "dispatch key")?;
    ensure!(
        pc_setter.symbol != key_setter.symbol,
        "the counter and key write routes call the same setter"
    );
    // Every write router must route exactly the counter and key index fields to their two setters,
    // so a stray router-shaped function or a mis-recognized route fails loudly instead of supplying
    // a wrong pc/key mapping. The read accessor anchors which index is the counter's.
    for route in &routes {
        let setter = if route.index == read.pc_index {
            pc_route.setter
        } else if route.index == key_route.index {
            key_route.setter
        } else {
            bail!("a write router routes an unexpected index field {:?}", route.index);
        };
        ensure!(
            route.setter == setter,
            "a write router routes index {:?} to an unexpected setter",
            route.index
        );
    }

    let mut members = Members::default();
    members.insert(&read.tags, Member::Tags)?;
    members.insert(&read.values, Member::Values)?;
    members.insert(&read.pc_index, Member::PcIndex)?;
    members.insert(&key_route.index, Member::KeyIndex)?;
    members.insert(&pc_setter.value, Member::Pc)?;
    members.insert(&pc_setter.other, Member::OtherPc)?;
    members.insert(&pc_setter.flag, Member::Integer)?;
    members.insert(&key_setter.value, Member::Key)?;
    members.insert(&key_setter.other, Member::OtherKey)?;
    members.insert(&key_setter.flag, Member::Integer)?;
    ensure!(
        pc_setter.mask == key_setter.mask,
        "the counter and key setters use different masks: {:?} and {:?}",
        pc_setter.mask,
        key_setter.mask
    );
    members.insert(&pc_setter.mask, Member::Mask)?;
    for mask in digest_fields(class) {
        members.insert(&mask, Member::Mask)?;
    }

    let writes = functions
        .iter()
        .filter(|(_, function)| !router_routes(script, function).is_empty())
        .map(|(symbol, _)| *symbol)
        .collect();
    Ok(Derived {
        members,
        read: read.symbol,
        writes,
    })
}

fn find_setter<'a>(setters: &'a [Setter], symbol: SymbolId, what: &str) -> Result<&'a Setter> {
    setters
        .iter()
        .find(|setter| setter.symbol == symbol)
        .with_context(|| format!("the {what} route calls no recognized setter"))
}

/// Recognizes a counter/key setter: `f(file, v) { if (<test>) { file.FLAG = <int>; file.VAL = v ^
/// file.MASK; } else { file.FLAG = <int>; file.OTHER = v; } [return v;] }`.
fn setter(script: Script<'_>, symbol: SymbolId, function: &Function<'_>) -> Option<Setter> {
    let [file, value] = params(function)?[..] else {
        return None;
    };
    let body = function.body.as_deref()?;
    let branch = match &body.statements[..] {
        [Statement::IfStatement(branch)]
        | [Statement::IfStatement(branch), Statement::ReturnStatement(_)] => branch,
        _ => return None,
    };
    let consequent = block_pair(&branch.consequent)?;
    let alternate = block_pair(branch.alternate.as_ref()?)?;
    // Each branch assigns the flag an integer and one value field.
    let (flag, value_store) = split_flag(script, consequent, file)?;
    let (flag_else, other_store) = split_flag(script, alternate, file)?;
    if flag != flag_else {
        return None;
    }
    // The set branch stores `v ^ file.MASK`; the other stores `v`.
    let (value_field, mask) = masked_value(script, value_store, file, value)?;
    let (other_field, other_rhs) = field_assign(script, other_store, file)?;
    if !script.refers_to(other_rhs, value) {
        return None;
    }
    Some(Setter {
        symbol,
        flag,
        value: value_field,
        other: other_field,
        mask,
    })
}

/// Splits a `{ file.FLAG = <int>; file.FIELD = <rhs>; }` branch into the flag field and the other
/// assignment, in either order.
fn split_flag<'a>(
    script: Script<'a>,
    [first, second]: [&'a Statement<'a>; 2],
    file: SymbolId,
) -> Option<(String, &'a Statement<'a>)> {
    for (flag_stmt, other) in [(first, second), (second, first)] {
        let (field, rhs) = field_assign(script, flag_stmt, file)?;
        if ast::number(rhs).is_some_and(|value| value.fract() == 0.0) {
            return Some((field, other));
        }
    }
    None
}

/// The field and mask from `file.FIELD = v ^ file.MASK` (either XOR order).
fn masked_value<'a>(
    script: Script<'a>,
    statement: &'a Statement<'a>,
    file: SymbolId,
    value: SymbolId,
) -> Option<(String, String)> {
    let (field, rhs) = field_assign(script, statement, file)?;
    let xor = binary(rhs)?;
    if xor.operator != BinaryOperator::BitwiseXOR {
        return None;
    }
    let mask = |expr| field_of(script, expr, file);
    let is_value = |expr| script.refers_to(expr, value);
    let mask = if is_value(&xor.left) && mask(&xor.right).is_some() {
        mask(&xor.right)?
    } else if is_value(&xor.right) && mask(&xor.left).is_some() {
        mask(&xor.left)?
    } else {
        return None;
    };
    Some((field, mask.to_owned()))
}

/// The routes of a write router: `if (i === file.INDEX) SETTER(file, v); else if (...) ...`.
/// Returns every `(index field, setter symbol)` the function routes to.
fn router_routes(script: Script<'_>, function: &Function<'_>) -> Vec<Route> {
    let Some(params) = params(function) else {
        return Vec::new();
    };
    let [file, index, value] = params[..] else {
        return Vec::new();
    };
    let Some(body) = function.body.as_deref() else {
        return Vec::new();
    };
    let mut routes = Vec::new();
    collect_routes(script, &body.statements, file, index, value, &mut routes);
    routes
}

/// Walks an if/else-if chain collecting index-compare routes to setters.
fn collect_routes<'a>(
    script: Script<'a>,
    statements: &'a [Statement<'a>],
    file: SymbolId,
    index: SymbolId,
    value: SymbolId,
    routes: &mut Vec<Route>,
) {
    for statement in statements {
        let Statement::IfStatement(branch) = statement else {
            continue;
        };
        if let Some(field) = index_compare(script, &branch.test, file, index)
            && let Some(setter) = route_setter(script, &branch.consequent, file, value)
        {
            routes.push(Route {
                index: field.to_owned(),
                setter,
            });
        }
        // Follow both branches, through `else if` chains and `else { ... }` / `if { ... }` blocks,
        // so a router whose key route sits in a nested block is not missed.
        for nested in [branch.alternate.as_ref(), Some(&branch.consequent)]
            .into_iter()
            .flatten()
        {
            match nested {
                Statement::BlockStatement(block) => {
                    collect_routes(script, &block.body, file, index, value, routes);
                }
                other => {
                    collect_routes(script, std::slice::from_ref(other), file, index, value, routes);
                }
            }
        }
    }
}

/// The index field from `i === file.INDEX` or `file.INDEX === i`.
fn index_compare<'a>(
    script: Script<'a>,
    test: &'a Expression<'a>,
    file: SymbolId,
    index: SymbolId,
) -> Option<&'a str> {
    let compare = binary(test)?;
    if compare.operator != BinaryOperator::StrictEquality {
        return None;
    }
    let field = |expr| field_of(script, expr, file);
    let is_index = |expr| script.refers_to(expr, index);
    if is_index(&compare.left) {
        field(&compare.right)
    } else if is_index(&compare.right) {
        field(&compare.left)
    } else {
        None
    }
}

/// The setter a route calls: `SETTER(file, v)` or a block whose first statement is that call.
fn route_setter(
    script: Script<'_>,
    consequent: &Statement<'_>,
    file: SymbolId,
    value: SymbolId,
) -> Option<SymbolId> {
    let statement = match consequent {
        Statement::ExpressionStatement(statement) => statement,
        Statement::BlockStatement(block) => match block.body.first()? {
            Statement::ExpressionStatement(statement) => statement,
            _ => return None,
        },
        _ => return None,
    };
    let (callee, arguments) = ast::direct_call(&statement.expression)?;
    let [first, second] = arguments else {
        return None;
    };
    let first = ast::argument_expression(first);
    let second = ast::argument_expression(second);
    if !(script.refers_to(first, file) && script.refers_to(second, value)) {
        return None;
    }
    script.symbol(callee)
}

/// Recognizes the read accessor: `f(file, i)` reading `file.TAGS[i] & 3`, returning `file.VALUES[i]`,
/// and comparing `file.PCINDEX === i`.
fn read(script: Script<'_>, symbol: SymbolId, function: &Function<'_>) -> Option<Read> {
    let [file, index] = params(function)?[..] else {
        return None;
    };
    let body = function.body.as_deref()?;
    let mut scan = ReadScan {
        script,
        file,
        index,
        indexed: HashMap::default(),
        indexed_reads: Vec::new(),
        tag_locals: HashSet::default(),
        pc_index: None,
    };
    scan.visit_function_body(body);
    // Tags are read then bit-tested; values are indexed directly.
    let tags = candidates::at_most_one_distinct(
        scan.tag_locals
            .iter()
            .filter_map(|local| scan.indexed.get(local).copied()),
        "register tag field",
    )
    .ok()??;
    let values = candidates::at_most_one_distinct(
        scan.indexed_reads
            .iter()
            .copied()
            .filter(|field| *field != tags),
        "register value field",
    )
    .ok()??;
    Some(Read {
        symbol,
        tags: tags.to_owned(),
        values: values.to_owned(),
        pc_index: scan.pc_index?.to_owned(),
    })
}

/// Collects the fields the read accessor indexes and the field it compares to the index.
struct ReadScan<'a> {
    script: Script<'a>,
    file: SymbolId,
    index: SymbolId,
    /// Locals bound to an indexed field read, `x = file.FIELD[i]`.
    indexed: HashMap<SymbolId, &'a str>,
    /// Fields read as `file.FIELD[i]` directly in expression position.
    indexed_reads: Vec<&'a str>,
    /// Locals whose value is bit-tested with `& 3` or compared to the record tag.
    tag_locals: HashSet<SymbolId>,
    /// The field compared to the index, `file.FIELD === i`.
    pc_index: Option<&'a str>,
}

impl<'a> ReadScan<'a> {
    /// The field of `file.FIELD[i]` if the index refers to the index parameter.
    fn indexed_field(&self, expr: &Expression<'a>) -> Option<&'a str> {
        let member = expr.as_member_expression()?;
        let object = member.object();
        let field = ast::member_str(member.object().as_member_expression()?)?;
        if !matches!(object.as_member_expression()?.object(), Expression::Identifier(reference)
            if self.script.symbol(reference) == Some(self.file))
        {
            return None;
        }
        match member {
            oxc::ast::ast::MemberExpression::ComputedMemberExpression(member)
                if self.script.refers_to(&member.expression, self.index) =>
            {
                Some(field)
            }
            _ => None,
        }
    }
}

impl<'a> Visit<'a> for ReadScan<'a> {
    fn visit_variable_declarator(&mut self, declarator: &oxc::ast::ast::VariableDeclarator<'a>) {
        if let Some(init) = &declarator.init
            && let oxc::ast::ast::BindingPattern::BindingIdentifier(name) = &declarator.id
            && let Some(field) = self.indexed_field(init)
        {
            self.indexed.insert(name.symbol_id(), field);
        }
        walk::walk_variable_declarator(self, declarator);
    }

    fn visit_assignment_expression(&mut self, assignment: &oxc::ast::ast::AssignmentExpression<'a>) {
        if let oxc::ast::ast::AssignmentTarget::AssignmentTargetIdentifier(name) = &assignment.left
            && let Some(field) = self.indexed_field(&assignment.right)
            && let Some(symbol) = self.script.symbol(name)
        {
            self.indexed.insert(symbol, field);
        }
        walk::walk_assignment_expression(self, assignment);
    }

    fn visit_expression(&mut self, expression: &Expression<'a>) {
        if let Some(field) = self.indexed_field(expression) {
            self.indexed_reads.push(field);
        }
        if let Expression::BinaryExpression(binary) = expression {
            // A `& 3` or `=== -4` marks the operand local or field as the tag source.
            let tag_test = (binary.operator == BinaryOperator::BitwiseAnd
                && ast::number(&binary.right).is_some_and(|value| value == 3.0))
                || (binary.operator == BinaryOperator::StrictEquality
                    && (ast::number(&binary.left) == Some(-4.0)
                        || ast::number(&binary.right) == Some(-4.0)));
            if tag_test {
                for operand in [&binary.left, &binary.right] {
                    if let Expression::Identifier(name) = operand.without_parentheses()
                        && let Some(symbol) = self.script.symbol(name)
                    {
                        self.tag_locals.insert(symbol);
                    }
                    if let Some(field) = self.indexed_field(operand) {
                        self.indexed_reads.retain(|read| *read != field);
                        self.indexed.insert(self.index, field);
                        self.tag_locals.insert(self.index);
                    }
                }
            }
            if binary.operator == BinaryOperator::StrictEquality
                && self.pc_index.is_none()
            {
                let field = |expr| field_of(self.script, expr, self.file);
                let is_index = |expr| self.script.refers_to(expr, self.index);
                if is_index(&binary.left) {
                    self.pc_index = field(&binary.right);
                } else if is_index(&binary.right) {
                    self.pc_index = field(&binary.left);
                }
            }
        }
        walk::walk_expression(self, expression);
    }
}

/// The mask fields of the register-file class: its digest accessor and the fields that accessor
/// reads and writes.
fn digest_fields(class: &Class<'_>) -> Vec<String> {
    let mut fields = Vec::new();
    for element in &class.body.body {
        let ClassElement::MethodDefinition(method) = element else {
            continue;
        };
        if !matches!(
            method.kind,
            MethodDefinitionKind::Get | MethodDefinitionKind::Set
        ) {
            continue;
        }
        if let Some(name) = ast::static_key_str(&method.key, method.computed) {
            fields.push(name.to_owned());
        }
        let Some(body) = method.value.body.as_deref() else {
            continue;
        };
        let mut scan = ThisFields::default();
        scan.visit_function_body(body);
        fields.extend(scan.fields);
    }
    fields
}

/// Collects `this.FIELD` names.
#[derive(Default)]
struct ThisFields {
    fields: Vec<String>,
}

impl<'a> Visit<'a> for ThisFields {
    fn visit_member_expression(&mut self, member: &oxc::ast::ast::MemberExpression<'a>) {
        if matches!(member.object(), Expression::ThisExpression(_))
            && let Some(field) = ast::member_str(member)
        {
            self.fields.push(field.to_owned());
        }
        walk::walk_member_expression(self, member);
    }
}

/// The function's parameters as symbols, if each is a plain identifier.
fn params(function: &Function<'_>) -> Option<Vec<SymbolId>> {
    Some(
        extract::parameters(&function.params)?
            .into_iter()
            .map(|parameter| parameter.symbol_id())
            .collect(),
    )
}

/// The two statements of a single-block branch.
fn block_pair<'a>(statement: &'a Statement<'a>) -> Option<[&'a Statement<'a>; 2]> {
    let Statement::BlockStatement(block) = statement else {
        return None;
    };
    match &block.body[..] {
        [first, second] => Some([first, second]),
        _ => None,
    }
}

/// The field and right-hand side of `file.FIELD = <rhs>`.
fn field_assign<'a>(
    script: Script<'a>,
    statement: &'a Statement<'a>,
    file: SymbolId,
) -> Option<(String, &'a Expression<'a>)> {
    let Statement::ExpressionStatement(statement) = statement else {
        return None;
    };
    let Expression::AssignmentExpression(assignment) = &statement.expression else {
        return None;
    };
    if assignment.operator != oxc::syntax::operator::AssignmentOperator::Assign {
        return None;
    }
    let target = assignment.left.as_member_expression()?;
    let field = field_member(script, target, file)?;
    Some((field.to_owned(), &assignment.right))
}

/// The field of `file.FIELD` read as an expression.
fn field_of<'a>(script: Script<'a>, expr: &Expression<'a>, file: SymbolId) -> Option<&'a str> {
    field_member(script, expr.without_parentheses().as_member_expression()?, file)
}

/// The static field of a `file.FIELD` member expression.
fn field_member<'a>(
    script: Script<'a>,
    member: &oxc::ast::ast::MemberExpression<'a>,
    file: SymbolId,
) -> Option<&'a str> {
    match member.object() {
        Expression::Identifier(reference) if script.symbol(reference) == Some(file) => {
            ast::member_str(member)
        }
        _ => None,
    }
}

fn binary<'a>(expression: &'a Expression<'a>) -> Option<&'a BinaryExpression<'a>> {
    match expression.without_parentheses() {
        Expression::BinaryExpression(binary) => Some(binary),
        _ => None,
    }
}

/// Arrays storing register values and tags at matching indices.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Slots {
    Values,
    Tags,
}

/// Decoding rule used by `read` for a value with `tag`, assuming a zero mask.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Stored {
    /// Tag 1 stores an integer XORed with the tag's upper bits.
    Integer(i32),
    /// Tag 2 stores a boolean as a comparison with the tag's upper bits.
    Boolean(i32),
    /// Tag -4 stores an encrypted string record, decrypted by `read`.
    Record,
    /// All other tags store the value directly.
    Plain,
}

impl Stored {
    #[must_use]
    pub(crate) fn of(tag: f64) -> Self {
        let tag = js::int32(tag);
        if tag == -4 {
            return Self::Record;
        }
        match tag & 3 {
            1 => Self::Integer(tag >> 2),
            2 => Self::Boolean(tag >> 2),
            _ => Self::Plain,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::js::ast::ParsedScript;

    fn derive_from(source: &str) -> Result<Derived> {
        let parsed = ParsedScript::parse("t", source).unwrap();
        let script = parsed.script();
        let functions = extract::functions(&script.program.body);
        let class = script
            .program
            .body
            .iter()
            .find_map(|statement| match statement {
                Statement::ClassDeclaration(class) => Some(&**class),
                _ => None,
            })
            .expect("a register class");
        derive(script, &functions, class)
    }

    /// The shape of build 7c7fee70a876's register file, read/write accessors, and setters, with
    /// its reshuffled names.
    const NEW_BUILD: &str = r#"
        class se {
            constructor() { this.H = 0; this.J = 0; }
            get ["O"]() { return this.L | this.K << 16; }
            set ["O"](v) { this.L = v & 65535; this.K = v >>> 16; }
        }
        function IQ(f, i) {
            var t = f.J[i];
            var k = t & 3;
            if (k === 1) return f.H[i] ^ t >> 2;
            else if (k === 2) return 0 !== (f.H[i] ^ t >> 2);
            else if (k === 3) {
                if (f.D === i) { if (f.j === 1) return f.h ^ f.i; else return f.A; }
                else { if (f.m === 1) return f.l ^ f.h; else return f.v; }
            } else if (-4 === t) return Ty(f.H[i]);
            else return f.H[i];
        }
        function In(f, v) {
            if (typeof v === "number" && (0 | v) === v && (v !== 0 || 1 / v > 0)) { f.j = 1; f.i = v ^ f.h; }
            else { f.j = 0; f.A = v; }
        }
        function Ig(f, v) {
            if (typeof v === "number" && v === (v | 0) && (v !== 0 || 1 / v > 0)) { f.m = 1; f.l = f.h ^ v; }
            else { f.m = 0; f.v = v; }
        }
        function Iw(f, i, v) {
            if (i === f.D) In(f, v);
            else if (f.F === i) Ig(f, v);
            else if (typeof v === "number") qT(f, i, v, 1);
            else q1(f, i, v, 5);
        }
        function kib_1(f, i, v) {
            if (f.D === i) In(f, v);
            else { if (f.F === i) Ig(f, v); else q1(f, i, v, 5194314); }
        }
    "#;

    #[test]
    fn derives_the_new_build_roles() {
        let derived = derive_from(NEW_BUILD).expect("derivation");
        let m = &derived.members;
        assert_eq!(m.of("H"), Some(Member::Values));
        assert_eq!(m.of("J"), Some(Member::Tags));
        assert_eq!(m.of("D"), Some(Member::PcIndex));
        assert_eq!(m.of("F"), Some(Member::KeyIndex));
        assert_eq!(m.of("i"), Some(Member::Pc));
        assert_eq!(m.of("l"), Some(Member::Key));
        assert_eq!(m.of("j"), Some(Member::Integer));
        assert_eq!(m.of("m"), Some(Member::Integer));
        assert_eq!(m.of("A"), Some(Member::OtherPc));
        assert_eq!(m.of("v"), Some(Member::OtherKey));
        assert_eq!(m.of("h"), Some(Member::Mask));
        assert_eq!(m.of("O"), Some(Member::Mask));
        assert_eq!(m.of("L"), Some(Member::Mask));
        assert_eq!(m.of("K"), Some(Member::Mask));
        assert_eq!(derived.writes.len(), 2, "Iw and kib_1 are write routers");
    }

    /// The register file and its read, setter, and router accessors lifted verbatim from a real
    /// capture of build 7c7fee70a876's orchestrator, as cfsolve's own deobfuscation produces it (the
    /// form `derive` consumes). This tracks the shipped build's exact structure, where the synthetic
    /// snippet above only tracks its shape; `recognizes_saved_script` additionally runs `derive` over
    /// the whole captured script.
    #[test]
    fn derives_the_captured_build_roles() {
        let derived = derive_from(include_str!("testdata/registers-7c7fee70a876.js"))
            .expect("derivation from the captured build");
        let m = &derived.members;
        let roles = [
            ("H", Member::Values),
            ("J", Member::Tags),
            ("D", Member::PcIndex),
            ("F", Member::KeyIndex),
            ("i", Member::Pc),
            ("l", Member::Key),
            ("j", Member::Integer),
            ("m", Member::Integer),
            ("A", Member::OtherPc),
            ("v", Member::OtherKey),
            ("h", Member::Mask),
            ("O", Member::Mask),
            ("L", Member::Mask),
            ("K", Member::Mask),
        ];
        for (name, role) in roles {
            assert_eq!(m.of(name), Some(role), "role of {name}");
        }
        assert_eq!(derived.writes.len(), 2, "Iw and kib_1 are the write routers");
    }

    #[test]
    fn rejects_a_field_with_two_roles() {
        // The read accessor claims `h` is the mask; a setter that stored its value in `h` too
        // would make `h` both Mask and Pc.
        let broken = NEW_BUILD.replace("f.i = v ^ f.h", "f.h = v ^ f.i");
        assert!(derive_from(&broken).is_err());
    }
}
