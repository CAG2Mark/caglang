#[derive(Copy, Clone)]
pub struct Position {
    pub line_no: usize,
    pub pos: usize
}

/*
pub enum DelimiterType {
    CurlyOpen,
    CurlyClose,
    SquareOpen,
    SquareClose,
    Open,
    Close,
    Arrow,
    Equal,
    Dot,
    Comma,
    Underscore,
    Colon
}

pub enum KeywordType {
    // def|if|else|while|continue|break|match
    Def,
    If,
    Else,
    While,
    Continue,
    Break,
    Match
}
*/

pub enum Token {
    Keyword(String),
    Delimiter(String),
    Identifier(String),
    IntLiteral(i64),
    FloatLiteral(f64),
    StringLiteral(String),
    BoolLiteral(bool),
    AssignmentOperator(String),
    Operator(String),
    PrimType(String),
    Whitespace,
    Comment,
    ImplicitExprSep,
    ExplicitExprSep
}

pub struct TokenPos {
    pub tk: Token,
    pub pos: Position
}

pub static IDENT_STR: &str = "<Identifier>";
pub static PRIM_STR: &str = "<Primitive Type>";
pub static INT_LIT_STR: &str = "<Integer Literal>";
pub static FLOAT_LIT_STR: &str = "<Float Literal>";
pub static STRING_LIT_STR: &str = "<String Literal>";
pub static BOOL_LIT_STR: &str = "<Boolean Literal>";
pub static WHITESPACE_STR: &str = "<Whitespace>";
pub static COMMENT_STR: &str = "<Comment>";
pub static IMPLICIT_EXPRSEP_STR: &str = "<Implicit Expression Separator>";
pub static EXPLICIT_EXPRSEP_STR: &str = ";";

impl Token {
    pub fn to_str(&self) -> String {
        match self {
            Token::Keyword(kw) => kw.to_string(),
            Token::Delimiter(d) => d.to_string(),
            Token::Identifier(_) => IDENT_STR.to_string(),
            Token::IntLiteral(_) => INT_LIT_STR.to_string(),
            Token::FloatLiteral(_) => FLOAT_LIT_STR.to_string(),
            Token::StringLiteral(_) => STRING_LIT_STR.to_string(),
            Token::Operator(op) | Token::AssignmentOperator(op) => op.to_string(),
            Token::PrimType(_) => PRIM_STR.to_string(),
            Token::BoolLiteral(_) => BOOL_LIT_STR.to_string(),
            Token::Whitespace => WHITESPACE_STR.to_string(),
            Token::Comment => COMMENT_STR.to_string(),
            Token::ImplicitExprSep => IMPLICIT_EXPRSEP_STR.to_string(),
            Token::ExplicitExprSep => EXPLICIT_EXPRSEP_STR.to_string()
        }
    }
}

impl TokenPos {
    pub fn to_str(&self) -> String {
        self.tk.to_str()
    }
}