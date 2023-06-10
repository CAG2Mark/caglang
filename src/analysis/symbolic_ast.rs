use std::collections::HashMap;

use crate::parsing::position::*;
use crate::parsing::tokens::Prim;

type Identifier = u64;

#[derive(Clone, Copy)]
pub enum SType {
    Top,
    Primitve(Prim),
    UserType(Identifier)
}

#[derive(Clone, Copy)]
pub enum TypeOrVar {
    Ty(SType),
    Var(u64, PositionRange),
}

pub struct SParamDef {
    pub name: Identifier,
    pub ty: TypeOrVar, 
    pub pos: PositionRange
}

pub struct SFunDef {
    pub name: Identifier, 
    pub name_pos: PositionRange,
    pub ty: TypeOrVar, 
    pub params: Vec<SParamDef>, 
    pub body: Box<SExprPos>
}

pub struct SAdtVariant {
    pub name: Identifier,
    pub name_pos: PositionRange,
    pub params: Vec<SParamDef>
}

pub struct SAdtDef {
    pub name: Identifier,
    pub params: Vec<SParamDef>,
    pub name_map: HashMap<String, Identifier>,
    pub variants: Vec<SAdtVariant>
}

pub enum SPattern {
    WildcardPattern,
    IdOrAdtPattern(Identifier), // cannot distinguish between IDs and ADT variants with no parameters
    IntLiteralPattern(i64),
    FloatLiteralPattern(f64),
    StringLiteralPattern(String),
    BoolLiteralPattern(bool),
    AdtPattern(Identifier, Vec<SPattern>)
}

pub struct SMatchCase {
    pub pat: SPattern,
    pub body: SExprPos
}

pub enum SExpr {
    Dummy,
    Nested(Box<SExprPos>),
    Variable(Identifier, Vec<Identifier>),
    Call(Identifier, Vec<SExprPos>),
    Ctor(Identifier, Vec<SExprPos>),
    Sequence(Box<SExprPos>, Box<SExprPos>),
    Ite(Box<SExprPos>, Box<SExprPos>, Vec<(Box<SExprPos>, Box<SExprPos>)>, Option<Box<SExprPos>>), // if Cond1 Expr1, elif Cond2 Expr2, ..., elif CondN, ExprN, ElseExpr
    Match(Box<SExprPos>, Vec<SMatchCase>), // scrutinee, matches
    While(Box<SExprPos>, Box<SExprPos>),
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    BoolLit(bool),
    UnitLit,
    Infix(String, Box<SExprPos>, Box<SExprPos>), // Op, left, right
    Prefix(String, Box<SExprPos>), // Op, expr
    Let(SParamDef, Box<SExprPos>, Box<SExprPos>), // let x (: Type)? = first <ExprSep> second
    AssignmentOp(String, Box<SExprPos>, Box<SExprPos>, Box<SExprPos>), // <assignment operator> lvalue rvalue <ExprSep> second
}

pub struct SExprPos {
    pub expr: SExpr,
    pub pos: PositionRange
}