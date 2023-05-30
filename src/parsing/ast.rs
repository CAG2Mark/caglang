use crate::tokens::Position;
use std::fmt;

pub enum Type {
    Primitve(String)
}

// All WIP.

pub struct ParamDef {
    pub name: String, 
    pub ty: Option<Type>, 
    pub pos: Position
}

pub enum Tree {
    
}

pub struct QualifiedName {
    pub first: String,
    pub nexts: Vec<String>
}

impl fmt::Display for QualifiedName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.nexts.iter().fold(
            self.first.to_string(),
            |a, b| a + "." + b
        ))
    }
}

pub enum Expr {
    Nested(Box<ExprPos>),
    FunDef(String, Option<Type>, Vec<ParamDef>, Box<ExprPos>),
    Variable(QualifiedName),
    Call(QualifiedName, Vec<ExprPos>),
    Sequence(Box<ExprPos>, Box<ExprPos>),
    Ite(Box<ExprPos>, Box<ExprPos>, Vec<(Box<ExprPos>, Box<ExprPos>)>, Option<Box<ExprPos>>), // if Cond1 Expr1, elif Cond2 Expr2, ..., elif CondN, ExprN, ElseExpr
    While(Box<ExprPos>, Box<ExprPos>),
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    BoolLit(bool),
    UnitLit,
    Infix(String, Box<ExprPos>, Box<ExprPos>), // Op, left, right
    Prefix(String, Box<ExprPos>), // Op, expr
    Let(ParamDef, Box<ExprPos>, Box<ExprPos>), // x = first <ExprSep> second
    AssignmentOp(String, Box<ExprPos>, Box<ExprPos>, Box<ExprPos>) // <assignment operator> lvalue rvalue <ExprSep> second
}

pub struct ExprPos {
    pub expr: Expr,
    pub pos: Position
}

pub fn format_param_df(p: &ParamDef) -> String {
    match &p.ty {
        Some(Type::Primitve(t)) => format!("{}: {}", p.name, t),
        None => p.name.to_owned()
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
    format_sep(&p.iter().map(|p| format_param_df(&p)).collect(), ", ")
}

pub fn format_exprs(p: &Vec<ExprPos>, indent: u32) -> String {
    format_sep(&p.iter().map(|p| format_tree(&p.expr, indent, false)).collect(), ", ")
}

fn format_conds_expr(cond: &ExprPos, expr: &ExprPos, indent: u32, kw: &str) -> String {
    let mut indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    ";
    }

    let cond = format_tree(&cond.expr, indent + 1, false);
    let body = match &expr.expr {
        Expr::Nested(inner) => format_tree(&inner.expr, indent + 1, true),
        e => format_tree(&e, indent + 1, true)
    };

    format!("{kw} ({cond}) {{\n{body}\n{indents}}}").to_string()
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
        Expr::Nested(expr) => {
            match expr.expr {
                Expr::Nested(_) => format_tree(&expr.expr, indent, indent_first),
                _ => format!("{}{{\n{}\n{}}}", first_line_indents, format_tree(&expr.expr, indent + 1, true), indents)
            }
        }
        Expr::FunDef(name, ty, param_dfs, body) => {
            let type_str = match ty {
                Some(Type::Primitve(t)) => format!(" : {}", t),
                None => "".to_string(),
            };

            let body_inner = match &body.expr {
                Expr::Nested(expr) => &expr.expr,
                other => other
            };

            format!("{}def {}({}){} = {{\n{}\n{}}}",
                first_line_indents,
                name,
                format_param_dfs(&param_dfs),
                type_str,
                format_tree(&body_inner, indent + 1, true),
                indents,
            )
        },
        Expr::Ite(cond1, expr1, more, elze) => {
            let first = first_line_indents + &format_conds_expr(&*cond1, &*expr1, indent, "if");
            let elifs = more.iter()
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
                        e => format_tree(&e, indent + 1, true)
                    };
                    format!(" else {{\n{}\n{}}}", body, indents)
                }
                None => "".to_string()
            };
            elifs + &last
        }
        Expr::While(cond, expr) => first_line_indents + &format_conds_expr(&*cond, &*expr, indent, "while"),
        Expr::Let(id, e1, e2) => {
            let first = format_tree(&e1.expr, indent, false);
            let second = format_tree(&e2.expr, indent, true);
            format!("{}{} = {};\n{}", first_line_indents, format_param_df(id), first, second)
        }
        Expr::AssignmentOp(op, lval, e1, e2) => {
            let lval_ = format_tree(&lval.expr, indent, false);
            let first = format_tree(&e1.expr, indent, false);
            let second = format_tree(&e2.expr, indent, true);
            format!("{}{} {} {};\n{}", first_line_indents, lval_, op, first, second)
        }
        Expr::Variable(x) => format!("{}{}", first_line_indents, x),
        Expr::Call(qn, args) => {
            format!("{}{}({})", first_line_indents, qn, format_exprs(args, indent + 1))
        }
        Expr::Sequence(e1, e2) => {
            let first = format_tree(&e1.expr, indent, indent_first);
            let second = format_tree(&e2.expr, indent, true);
            format!("{};\n{}", first, second)
        },
        Expr::IntLit(v) => format!("{}{}", first_line_indents, v),
        Expr::FloatLit(v) => format!("{}{}f", first_line_indents, v),
        Expr::StringLit(v) => format!("{}\"{}\"", first_line_indents, v),
        Expr::BoolLit(v) => format!("{}{}", first_line_indents, v),
        Expr::UnitLit => format!("{}()", first_line_indents),
        Expr::Infix(op, left, right) => format!("{}({} {} {})", first_line_indents, 
            format_tree(&left.expr, indent+1, false), op, format_tree(&right.expr, indent+1, false)),
        Expr::Prefix(op, expr) => format!("{}({}{})", first_line_indents, op, format_tree(&expr.expr, indent + 1, false)),
    };

    ret
}