use std::collections::{HashMap, BTreeMap};

use crate::parsing::position::*;
use crate::parsing::tokens::{Prim, Op, AssignOp};

type Identifier = u64;

#[derive(Clone, Copy)]
pub enum SType {
    Top,
    Primitve(Prim),
    UserType(Identifier),
}

#[derive(Clone, Copy)]
pub enum TypeOrVar {
    Ty(SType),
    Var(u64, PositionRange),
}

pub struct SParamDef {
    pub name: Identifier,
    pub ty: TypeOrVar,
    pub pos: PositionRange,
}

pub struct SFunDef {
    pub name: Identifier,
    pub name_pos: PositionRange,
    pub ty: TypeOrVar,
    pub params: Vec<SParamDef>,
    pub body: Box<SStatExprPos>,
}

pub struct SAdtVariant {
    pub name: Identifier,
    pub name_pos: PositionRange,
    pub params: Vec<SParamDef>
}

pub struct SAdtDef {
    pub name: Identifier,
    pub name_pos: PositionRange,
    pub params: Vec<SParamDef>,
    pub name_map: HashMap<String, Identifier>,
    pub variant_name_map: HashMap<String, Identifier>,
    pub variants: BTreeMap<Identifier, SAdtVariant>,
    // for internal use
    pub wildcard: SPatternPos
}

pub struct SPatternPos {
    pub pat: SPattern,
    pub pos: PositionRange,
    pub ty: SType
}

pub enum SPattern {
    WildcardPattern,
    IdPattern(Identifier),
    IntLiteralPattern(i64),
    FloatLiteralPattern(f64),
    StringLiteralPattern(String),
    BoolLiteralPattern(bool),
    AdtPattern(Identifier, Identifier, Vec<SPatternPos>), // adt id, ctor id, args
}

pub struct SMatchCase {
    pub pat: SPatternPos,
    pub body: SStatExprPos,
}

pub type SExpr = Vec<SStatExprPos>;

pub enum SStatExpr {
    Dummy,
    Nested(SExpr),
    Variable(Identifier, Vec<Identifier>),
    Call(Identifier, Vec<SStatExprPos>),
    Ctor(Identifier, Identifier, Vec<SStatExprPos>), // adt id, variant id
    Ite(
        Box<SStatExprPos>,
        Box<SStatExprPos>,
        Vec<(Box<SStatExprPos>, Box<SStatExprPos>)>,
        Option<Box<SStatExprPos>>,
    ), // if Cond1 Expr1, elif Cond2 Expr2, ..., elif CondN, ExprN, ElseExpr
    Match(Box<SStatExprPos>, Vec<SMatchCase>), // scrutinee, matches
    While(Box<SStatExprPos>, Box<SStatExprPos>),
    IntLit(i64),
    FloatLit(f64),
    StringLit(String),
    BoolLit(bool),
    UnitLit,
    Infix(Op, Box<SStatExprPos>, Box<SStatExprPos>), // Op, left, right
    Prefix(Op, Box<SStatExprPos>),               // Op, expr
    Let(SParamDef, Box<SStatExprPos>), // let x (: Type)? = first
    AssignmentOp(AssignOp, Box<SStatExprPos>, Box<SStatExprPos>), // <assignment operator> lvalue rvalue

    // built in conversions
    BoolToFloat(Box<SStatExprPos>),
    IntToFloat(Box<SStatExprPos>),
    BoolToInt(Box<SStatExprPos>),
    FloatToBool(Box<SStatExprPos>),
    IntToBool(Box<SStatExprPos>)
}

pub struct SStatExprPos {
    pub expr: SStatExpr,
    pub pos: PositionRange,
}
