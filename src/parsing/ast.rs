use crate::parsing::position::*;
use crate::parsing::tokens::Op;
use crate::parsing::tokens::Prim;
use std::fmt;

use super::tokens::AssignOp;

// All WIP.

pub struct ParamDef {
    pub name: String,
    pub ty: Option<TypePos>,
    pub nme_pos: PositionRange,
}

pub struct QualifiedName {
    pub scopes: Vec<(String, PositionRange)>,
    pub name: String,
    pub name_pos: PositionRange,
    pub members: Vec<(String, PositionRange)>,
}

impl QualifiedName {
    pub fn get_pos(&self) -> PositionRange {
        let first = match self.scopes.first() {
            Some(first) => first.1,
            None => self.name_pos,
        };

        let last = match self.members.last() {
            Some(last) => last.1,
            None => self.name_pos,
        };

        union_posr(first, last)
    }
}

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.members.iter().fold(
                self.scopes
                    .iter()
                    .rfold(self.name.to_string(), |a, b| b.0.to_string() + "::" + &a),
                |a, b| a + "." + &b.0
            )
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
    pub body: Box<StatExprPos>,
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

pub struct PatternPos {
    pub pat: Pattern,
    pub pos: PositionRange,
}

pub enum Pattern {
    WildcardPattern,
    IdOrAdtPattern(String), // cannot distinguish between IDs and ADT variants with no parameters
    IntLiteralPattern(i64),
    FloatLiteralPattern(f64),
    StringLiteralPattern(String),
    BoolLiteralPattern(bool),
    AdtPattern(QualifiedName, Vec<PatternPos>),
}

pub struct MatchCase {
    pub pat: PatternPos,
    pub body: StatExprPos,
}

pub type Expr = Vec<StatExprPos>;

pub enum StatExpr {
    Nested(Expr),
    FunDefn(FunDef),
    Variable(QualifiedName),
    Call(QualifiedName, Vec<StatExprPos>),
    Ctor(QualifiedName, Vec<StatExprPos>),
    Ite(
        Box<StatExprPos>,
        Box<StatExprPos>,
        Vec<(Box<StatExprPos>, Box<StatExprPos>)>,
        Option<Box<StatExprPos>>,
    ), // if Cond1 Expr1, elif Cond2 Expr2, ..., elif CondN, ExprN, ElseExpr
    Match(Box<StatExprPos>, Vec<MatchCase>), // scrutinee, matches
    While(Box<StatExprPos>, Box<StatExprPos>),
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    BoolLit(bool),
    UnitLit,
    Infix(Op, Box<StatExprPos>, Box<StatExprPos>), // Op, left, right
    Prefix(Op, Box<StatExprPos>),                  // Op, expr
    Let(ParamDef, Box<StatExprPos>),               // let x (: Type)? = first <ExprSep> second
    AssignmentOp(AssignOp, Box<StatExprPos>, Box<StatExprPos>), // <assignment operator> lvalue rvalue <ExprSep>
    AdtDefn(AdtDef),

    // internal use for name analyzer
    FunDefId(u64, PositionRange),
}

pub struct StatExprPos {
    pub expr: StatExpr,
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

pub fn format_patterns(p: &Vec<PatternPos>) -> String {
    let inner = format_sep(&p.iter().map(|x| format_pattern(x)).collect(), ", ");
    format!("({inner})")
}

pub fn format_pattern(v: &PatternPos) -> String {
    match &v.pat {
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
    let body_str = format_stat_expr(&v.body.expr, indent, false);

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

pub fn format_exprs(p: &Vec<StatExprPos>, indent: u32) -> String {
    format_sep(
        &p.iter()
            .map(|p| format_stat_expr(&p.expr, indent, false))
            .collect(),
        ", ",
    )
}

fn format_conds_expr(cond: &StatExprPos, expr: &StatExprPos, indent: u32, kw: &str) -> String {
    let mut indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
    }

    let cond = format_stat_expr(&cond.expr, indent, false);
    let body = match &expr.expr {
        StatExpr::Nested(inner) => format_expr(inner, indent, true),
        e => format_stat_expr(&e, indent + 1, true),
    };

    format!("{kw} {cond} {{\n{body}\n{indents}}}").to_string()
}

pub fn format_expr(e: &Expr, indent: u32, indent_first: bool) -> String {
    let mut ret = "".to_string();

    let mut first = true;

    for se in e {
        if first {
            ret += &format_stat_expr(&se.expr, indent, indent_first);
            first = false;
        } else {
            ret += ";\n";
            ret += &format_stat_expr(&se.expr, indent, true)
        }
    }

    ret
}

pub fn format_stat_expr(e: &StatExpr, indent: u32, indent_first: bool) -> String {
    let mut indents = "".to_string();
    let mut first_line_indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
        if indent_first {
            first_line_indents = first_line_indents + "    "
        }
    }

    let ret = match e {
        StatExpr::Nested(expr) => format!(
            "{}{{\n{}\n{}}}",
            first_line_indents,
            format_expr(expr, indent + 1, true),
            indents
        ),
        StatExpr::FunDefn(df) => {
            let type_str = match &df.ty {
                Some(t) => format!(": {}", t.ty),
                None => "".to_string(),
            };

            match &df.body.expr {
                StatExpr::Nested(_) => {
                    format!(
                        "{}def {}{}{} = {}",
                        first_line_indents,
                        df.name,
                        format_param_dfs(&df.params),
                        type_str,
                        format_stat_expr(&df.body.expr, indent, false),
                    )
                }
                other => {
                    format!(
                        "{}def {}{}{} = {{\n{}\n{}}}",
                        first_line_indents,
                        df.name,
                        format_param_dfs(&df.params),
                        type_str,
                        format_stat_expr(&other, indent + 1, true),
                        indents
                    )
                }
            }
        }
        StatExpr::Ite(cond1, expr1, more, elze) => {
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
                        StatExpr::Nested(inner) => format_expr(inner, indent, true),
                        e => format_stat_expr(&e, indent + 1, true),
                    };
                    format!(" else {{\n{}\n{}}}", body, indents)
                }
                None => "".to_string(),
            };
            elifs + &last
        }
        StatExpr::While(cond, expr) => {
            first_line_indents + &format_conds_expr(&*cond, &*expr, indent, "while")
        }
        StatExpr::Let(id, e1) => {
            let first = format_stat_expr(&e1.expr, indent, false);
            format!(
                "{}let {} = {}",
                first_line_indents,
                format_param_df(id),
                first
            )
        }
        StatExpr::AssignmentOp(op, lval, e1) => {
            let lval_ = format_stat_expr(&lval.expr, indent, false);
            let first = format_stat_expr(&e1.expr, indent, false);
            format!("{}{} {} {}", first_line_indents, lval_, op, first)
        }
        StatExpr::Variable(x) => format!("{}{}", first_line_indents, x),
        StatExpr::Call(qn, args) => {
            format!(
                "{}{}({})",
                first_line_indents,
                qn,
                format_exprs(args, indent + 1)
            )
        }
        StatExpr::IntLit(v) => format!("{}{}", first_line_indents, v),
        StatExpr::FloatLit(v) => format!("{}{}f", first_line_indents, v),
        StatExpr::StringLit(v) => format!("{}\"{}\"", first_line_indents, v),
        StatExpr::BoolLit(v) => format!("{}{}", first_line_indents, v),
        StatExpr::UnitLit => format!("{}()", first_line_indents),
        StatExpr::Infix(op, left, right) => format!(
            "{}({} {} {})",
            first_line_indents,
            format_stat_expr(&left.expr, indent + 1, false),
            op,
            format_stat_expr(&right.expr, indent + 1, false)
        ),
        StatExpr::Prefix(op, expr) => format!(
            "{}({}{})",
            first_line_indents,
            op,
            format_stat_expr(&expr.expr, indent + 1, false)
        ),
        StatExpr::AdtDefn(adt) => {
            let nme = adt.name.to_string();
            let params_formatted = format_param_dfs(&adt.params);
            let variants = format_adt_variants(&adt.variants, indent);

            format!("{first_line_indents}adt {nme}{params_formatted} = {{\n{variants}\n{indents}}}")
        }
        StatExpr::Match(scrut, cases) => {
            let scrut_str = format_stat_expr(&scrut.expr, indent + 1, false);
            let cases_str = format_matchcases(cases, indent + 1);
            format!("{first_line_indents}match {scrut_str} {{\n{cases_str}\n{indents}}}")
        }
        StatExpr::Ctor(qn, args) => {
            format!(
                "{}new {}({})",
                first_line_indents,
                qn,
                format_exprs(args, indent + 1)
            )
        }
        StatExpr::FunDefId(_, _) => unreachable!(),
    };

    ret
}
