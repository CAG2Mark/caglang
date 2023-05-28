use crate::tokens::Position;

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

pub enum Expr {
    Nested(Box<ExprPos>),
    FunDef(String, Option<Type>, Vec<ParamDef>, Box<ExprPos>),
    Variable(String),
    Sequence(Box<ExprPos>, Box<ExprPos>),
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    BoolLit(bool),
    UnitLit
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

pub fn format_param_dfs(p: Vec<ParamDef>) -> String {
    format_sep(&p.iter().map(|p| format_param_df(&p)).collect(), ", ")
}

pub fn format_tree(e: Expr, indent: u32) -> String {
    let mut indents = "".to_string();
    for _ in 0..indent {
        indents = indents + "    "
    }

    let ret = match e {
        Expr::Nested(expr) => {
            match expr.expr {
                Expr::Nested(_) => format_tree(expr.expr, indent),
                _ => format!("{}{{\n{}\n{}}}", indents, format_tree(expr.expr, indent + 1), indents)
            }
        }
        Expr::FunDef(name, ty, param_dfs, body) => {
            let type_str = match ty {
                Some(Type::Primitve(t)) => format!(" : {}", t),
                None => "".to_string(),
            };

            let body_inner : Expr = match body.expr {
                Expr::Nested(expr) => expr.expr,
                other => other
            };

            format!("{}def {}({}){} = {{\n{}\n{}}}",
                indents,
                name,
                format_param_dfs(param_dfs),
                type_str,
                format_tree(body_inner, indent + 1),
                indents,
            )
        },
        Expr::Variable(x) => format!("{}{}", indents, x),
        Expr::Sequence(e1, e2) => {
            let first = format_tree(e1.expr, indent);
            let second = format_tree(e2.expr, indent);
            format!("{};\n{}", first, second)
        },
        Expr::IntLit(v) => format!("{}{}", indents, v),
        Expr::FloatLit(v) => format!("{}{}f", indents, v),
        Expr::StringLit(v) => format!("{}\"{}\"", indents, v),
        Expr::BoolLit(v) => format!("{}{}", indents, v),
        Expr::UnitLit => format!("{}()", indents)
    };

    ret
}