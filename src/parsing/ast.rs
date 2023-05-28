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
    FunDef(String, Option<Type>, Vec<ParamDef>, Box<ExprPos>),
    Variable(String),
    Sequence(Box<ExprPos>, Option<Box<ExprPos>>)
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

pub fn print_sep(items: &Vec<String>, sep: &str) -> String {
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

pub fn format_tree(e: Expr) -> String {
    match e {
        Expr::FunDef(name, ty, param_dfs, body) => {
            let type_str = match ty {
                Some(Type::Primitve(t)) => format!(" : {}", t),
                None => "".to_string(),
            };

            format!("def {}({}){} = {{{}}}", 
                name,
                print_sep(&param_dfs.iter().map(|p| format_param_df(&p)).collect(), ", "),
                type_str,
                format_tree(body.expr)
            )
        },
        Expr::Variable(x) => x,
        Expr::Sequence(e1, e2) => {
            let first = format_tree(e1.expr);
            let second = match e2 {
                Some(expr) => format_tree(expr.expr),
                None => "".to_string()
            };
            format!("{};\n{}", first, second)
        },
    }
}