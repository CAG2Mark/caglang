use crate::parsing::position::*;
use crate::parsing::tokens::Prim;
use std::fmt;

// All WIP.

pub struct ParamDef {
    pub name: String,
    pub ty: Option<TypePos>,
    pub nme_pos: PositionRange,
}

pub struct QualifiedName {
    pub first: String,
    pub nexts: Vec<String>,
}

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.nexts
                .iter()
                .fold(self.first.to_string(), |a, b| a + "." + b)
        )
    }
}

pub struct TypePos {
    pub ty: Type,
    pub pos: PositionRange,
}

pub enum Type {
    Primitve(Prim),
    UserType(QualifiedName),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Type::Primitve(t) => write!(f, "{}", t),
            Type::UserType(t) => write!(f, "{}", t),
        }
    }
}

pub struct FunDef {
    pub name: String,
    pub name_pos: PositionRange,
    pub ty: Option<TypePos>,
    pub params: Vec<ParamDef>,
    pub body: Box<ExprPos>,
}

pub struct AdtVariant {
    pub name: String,
    pub name_pos: PositionRange,
    pub params: Vec<ParamDef>,
}

pub struct AdtDef {
    pub name: String,
    pub name_pos: PositionRange,
    pub params: Vec<ParamDef>,
    pub variants: Vec<AdtVariant>,
}

pub enum Pattern {
    WildcardPattern,
    IdOrAdtPattern(String), // cannot distinguish between IDs and ADT variants with no parameters
    IntLiteralPattern(i64),
    FloatLiteralPattern(f64),
    StringLiteralPattern(String),
    BoolLiteralPattern(bool),
    AdtPattern(QualifiedName, Vec<Pattern>),
}

pub struct MatchCase {
    pub pat: Pattern,
    pub body: ExprPos,
}

pub enum Expr {
    Nested(Box<ExprPos>),
    FunDefn(FunDef, Box<ExprPos>), // id, ret type, params, body, after
    Variable(QualifiedName),
    Call(QualifiedName, Vec<ExprPos>),
    Ctor(QualifiedName, Vec<ExprPos>),
    Sequence(Box<ExprPos>, Box<ExprPos>),
    Ite(
        Box<ExprPos>,
        Box<ExprPos>,
        Vec<(Box<ExprPos>, Box<ExprPos>)>,
        Option<Box<ExprPos>>,
    ), // if Cond1 Expr1, elif Cond2 Expr2, ..., elif CondN, ExprN, ElseExpr
    Match(Box<ExprPos>, Vec<MatchCase>), // scrutinee, matches
    While(Box<ExprPos>, Box<ExprPos>),
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    BoolLit(bool),
    UnitLit,
    Infix(String, Box<ExprPos>, Box<ExprPos>), // Op, left, right
    Prefix(String, Box<ExprPos>),              // Op, expr
    Let(ParamDef, Box<ExprPos>, Box<ExprPos>), // let x (: Type)? = first <ExprSep> second
    AssignmentOp(String, Box<ExprPos>, Box<ExprPos>, Box<ExprPos>), // <assignment operator> lvalue rvalue <ExprSep> second
    AdtDefn(AdtDef, Box<ExprPos>),                                  // // adtdef, after

    // internal use for name analyzer
    FunDefId(u64, PositionRange, Box<ExprPos>),
}

pub struct ExprPos {
    pub expr: Expr,
    pub pos: PositionRange,
}

pub fn format_param_df(p: &ParamDef) -> String {
    match &p.ty {
        Some(t) => format!("{}: {}", p.name, t.ty),
        None => p.name.to_owned(),
    }
}

pub fn format_sep(items: &Vec<String>, sep: &str) -> String {
    if items.len() == 0 {
        return "".to_string();
    }

    let mut ret = items.get(0).unwrap().to_owned();

    for i in 1..items.len() {
        ret += sep;
        ret += items.get(i).unwrap();
    }

    ret
}

pub fn format_param_dfs(p: &Vec<ParamDef>) -> String {
    let inner = format_sep(&p.iter().map(|p| format_param_df(&p)).collect(), ", ");
    format!("({})", inner)
}

pub fn format_patterns(p: &Vec<Pattern>) -> String {
    let inner = format_sep(&p.iter().map(|x| format_pattern(x)).collect(), ", ");
    format!("({inner})")
}

pub fn format_pattern(v: &Pattern) -> String {
    match v {
        Pattern::WildcardPattern => "_".to_string(),
        Pattern::IdOrAdtPattern(id) => id.to_string(),
        Pattern::IntLiteralPattern(val) => val.to_string(),
        Pattern::FloatLiteralPattern(val) => val.to_string(),
        Pattern::StringLiteralPattern(val) => val.to_string(),
        Pattern::BoolLiteralPattern(val) => val.to_string(),
        Pattern::AdtPattern(qn, cases) => {
            let cases_str = format_patterns(&cases);
            format!("{qn}{cases_str}")
        }
    }
}

pub fn format_matchcase(v: &MatchCase, indent: u32) -> String {
    let mut indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
    }

    let pat_str = format_pattern(&v.pat);
    let body_str = format_tree(&v.body.expr, indent, false);

    format!("{indents}{pat_str} => {body_str}")
}

pub fn format_matchcases(v: &Vec<MatchCase>, indent: u32) -> String {
    format_sep(
        &v.iter().map(|x| format_matchcase(x, indent)).collect(),
        "\n",
    )
}

pub fn format_adt_variant(v: &AdtVariant, indent: u32) -> String {
    let mut indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
    }

    let nme = v.name.to_string();
    let params = format_param_dfs(&v.params);
    format!("{indents}{nme}{params}")
}

pub fn format_adt_variants(v: &Vec<AdtVariant>, indent: u32) -> String {
    format_sep(
        &v.iter()
            .map(|x| format_adt_variant(x, indent + 1))
            .collect(),
        ",\n",
    )
}

pub fn format_exprs(p: &Vec<ExprPos>, indent: u32) -> String {
    format_sep(
        &p.iter()
            .map(|p| format_tree(&p.expr, indent, false))
            .collect(),
        ", ",
    )
}

fn format_conds_expr(cond: &ExprPos, expr: &ExprPos, indent: u32, kw: &str) -> String {
    let mut indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
    }

    let cond = format_tree(&cond.expr, indent + 1, false);
    let body = match &expr.expr {
        Expr::Nested(inner) => format_tree(&inner.expr, indent + 1, true),
        e => format_tree(&e, indent + 1, true),
    };

    format!("{kw} {cond} {{\n{body}\n{indents}}}").to_string()
}

pub fn format_tree(e: &Expr, indent: u32, indent_first: bool) -> String {
    let mut indents = "".to_string();
    let mut first_line_indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
        if indent_first {
            first_line_indents = first_line_indents + "    "
        }
    }

    let ret = match e {
        Expr::Nested(expr) => match expr.expr {
            Expr::Nested(_) => format_tree(&expr.expr, indent, indent_first),
            _ => format!(
                "{}{{\n{}\n{}}}",
                first_line_indents,
                format_tree(&expr.expr, indent + 1, true),
                indents
            ),
        },
        Expr::FunDefn(df, after) => {
            let type_str = match &df.ty {
                Some(t) => format!(": {}", t.ty),
                None => "".to_string(),
            };

            let body_inner = match &df.body.expr {
                Expr::Nested(expr) => &expr.expr,
                other => other,
            };

            format!(
                "{}def {}{}{} = {{\n{}\n{}}};\n{}",
                first_line_indents,
                df.name,
                format_param_dfs(&df.params),
                type_str,
                format_tree(&body_inner, indent + 1, true),
                indents,
                format_tree(&after.expr, indent, true)
            )
        }
        Expr::Ite(cond1, expr1, more, elze) => {
            let first = first_line_indents + &format_conds_expr(&*cond1, &*expr1, indent, "if");
            let elifs = more
                .iter()
                .map(|x| {
                    let x0 = &x.0;
                    let x1 = &x.1;
                    format_conds_expr(x0, x1, indent, "elif")
                })
                .fold(first, |x, y| x + " " + &y);
            let last = match elze {
                Some(e) => {
                    let body = match &e.expr {
                        Expr::Nested(inner) => format_tree(&inner.expr, indent + 1, true),
                        e => format_tree(&e, indent + 1, true),
                    };
                    format!(" else {{\n{}\n{}}}", body, indents)
                }
                None => "".to_string(),
            };
            elifs + &last
        }
        Expr::While(cond, expr) => {
            first_line_indents + &format_conds_expr(&*cond, &*expr, indent, "while")
        }
        Expr::Let(id, e1, e2) => {
            let first = format_tree(&e1.expr, indent, false);
            let second = format_tree(&e2.expr, indent, true);
            format!(
                "{}let {} = {};\n{}",
                first_line_indents,
                format_param_df(id),
                first,
                second
            )
        }
        Expr::AssignmentOp(op, lval, e1, e2) => {
            let lval_ = format_tree(&lval.expr, indent, false);
            let first = format_tree(&e1.expr, indent, false);
            let second = format_tree(&e2.expr, indent, true);
            format!(
                "{}{} {} {};\n{}",
                first_line_indents, lval_, op, first, second
            )
        }
        Expr::Variable(x) => format!("{}{}", first_line_indents, x),
        Expr::Call(qn, args) => {
            format!(
                "{}{}({})",
                first_line_indents,
                qn,
                format_exprs(args, indent + 1)
            )
        }
        Expr::Sequence(e1, e2) => {
            let first = format_tree(&e1.expr, indent, indent_first);
            let second = format_tree(&e2.expr, indent, true);
            format!("{};\n{}", first, second)
        }
        Expr::IntLit(v) => format!("{}{}", first_line_indents, v),
        Expr::FloatLit(v) => format!("{}{}f", first_line_indents, v),
        Expr::StringLit(v) => format!("{}\"{}\"", first_line_indents, v),
        Expr::BoolLit(v) => format!("{}{}", first_line_indents, v),
        Expr::UnitLit => format!("{}()", first_line_indents),
        Expr::Infix(op, left, right) => format!(
            "{}({} {} {})",
            first_line_indents,
            format_tree(&left.expr, indent + 1, false),
            op,
            format_tree(&right.expr, indent + 1, false)
        ),
        Expr::Prefix(op, expr) => format!(
            "{}({}{})",
            first_line_indents,
            op,
            format_tree(&expr.expr, indent + 1, false)
        ),
        Expr::AdtDefn(adt, after) => {
            let nme = adt.name.to_string();
            let params_formatted = format_param_dfs(&adt.params);
            let variants = format_adt_variants(&adt.variants, indent);
            let after = format_tree(&after.expr, indent, true);

            format!("{first_line_indents}adt {nme}{params_formatted} = {{\n{variants}\n{indents}}};\n{after}")
        }
        Expr::Match(scrut, cases) => {
            let scrut_str = format_tree(&scrut.expr, indent + 1, false);
            let cases_str = format_matchcases(cases, indent + 1);
            format!("{first_line_indents}match {scrut_str} {{\n{cases_str}\n{indents}}}")
        }
        Expr::Ctor(qn, args) => {
            format!(
                "new {}{}({})",
                first_line_indents,
                qn,
                format_exprs(args, indent + 1)
            )
        }
        Expr::FunDefId(_, _, _) => unreachable!(),
    };

    ret
}
