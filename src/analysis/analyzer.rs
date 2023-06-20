use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use crate::parsing::ast::*;
use crate::parsing::position::*;

use crate::analysis::symbolic_ast::SStatExpr::*;
use crate::analysis::symbolic_ast::*;

use crate::parsing::tokens::AssignOp;
use crate::parsing::tokens::Op;
use crate::parsing::tokens::Prim;
use crate::util::union_find_int;
use crate::util::union_find_int::UnionFindInt;

use immutable_map::map::TreeMap;

type Identifier = u64;
type Local = (Identifier, TypeOrVar);
type LocalFn = Identifier;
type LocalAdt = Identifier;

type LocalsMap = TreeMap<String, Local>;
type FnMap = TreeMap<String, LocalFn>;
type AdtMap = TreeMap<String, LocalAdt>;

type Converted = Option<(SStatExprPos, Option<(LocalsMap, LocalsMap)>)>;

// for storing nominal exprs pending conversion
enum NSExprPos {
    N(StatExprPos),
    S(SStatExprPos),
}

enum Ctor {
    Arbitrary,
    BoolCtor(bool),
    AdtCtor(Identifier, Identifier),
}

enum Witness {
    Int,
    String,
    Float,
    Wildcard,
    Bool(bool),
    Adt(Identifier, Identifier, Vec<Witness>),
}

struct TmpFunDef {
    name_str: String,
    name: Identifier,
    name_pos: PositionRange,
    ty: TypeOrVar,
    params: Vec<(String, SParamDef)>,
    captured_locals: Option<LocalsMap>,
    body: NSExprPos,
}

pub struct Analyzer {
    // Name analysis part.
    fun_defs: HashMap<Identifier, TmpFunDef>,
    adt_defs: HashMap<Identifier, SAdtDef>,
    local_id: u64,

    // Useful to have
    id_map: HashMap<Identifier, String>,
    id_pos_map: HashMap<Identifier, PositionRange>,

    // Type analysis part. We use a union-find data structure
    // to compactly store type var equality.
    unions: UnionFindInt,
    type_map: HashMap<Identifier, SType>,
    type_map_all: HashMap<Identifier, TypeOrVar>,

    // Errors, add all of them and report the errors all at once
    pub name_errors: Vec<AnalysisError>,
    pub type_errors: Vec<TypeError>,
}

const INT_WILDCARD: SPatternPos = SPatternPos {
    pat: SPattern::WildcardPattern,
    pos: PositionRange {
        start: Position { line_no: 0, pos: 0 },
        end: Position { line_no: 0, pos: 0 },
    },
    ty: SType::Primitve(Prim::Int),
};

const FLOAT_WILDCARD: SPatternPos = SPatternPos {
    pat: SPattern::WildcardPattern,
    pos: PositionRange {
        start: Position { line_no: 0, pos: 0 },
        end: Position { line_no: 0, pos: 0 },
    },
    ty: SType::Primitve(Prim::Float),
};

const BOOL_WILDCARD: SPatternPos = SPatternPos {
    pat: SPattern::WildcardPattern,
    pos: PositionRange {
        start: Position { line_no: 0, pos: 0 },
        end: Position { line_no: 0, pos: 0 },
    },
    ty: SType::Primitve(Prim::Bool),
};

const STRING_WILDCARD: SPatternPos = SPatternPos {
    pat: SPattern::WildcardPattern,
    pos: PositionRange {
        start: Position { line_no: 0, pos: 0 },
        end: Position { line_no: 0, pos: 0 },
    },
    ty: SType::Primitve(Prim::String),
};

const TOP_WILDCARD: SPatternPos = SPatternPos {
    pat: SPattern::WildcardPattern,
    pos: PositionRange {
        start: Position { line_no: 0, pos: 0 },
        end: Position { line_no: 0, pos: 0 },
    },
    ty: SType::Top,
};

pub enum TypeError {
    TypeNeededError(PositionRange),
    InvalidOperandError(PositionRange),
    NotAssignableError(PositionRange),
    TypeMismatch(String, String, PositionRange), // expected, actual, location
    InvalidBlockRetError(String, PositionRange, PositionRange), // name of ret type, position of ADT defn, position of expression
}
pub enum AnalysisError {
    LocalNotFoundError(String, PositionRange),
    FnNotFoundError(String, PositionRange),
    WrongNoArgsError(String, usize, usize, PositionRange), // fn name, expected, got, position of call
    NoMemberError(String, String, PositionRange),          // type name, member, pos
    TypeNotFound(String, PositionRange),
    NameAlreadyUsedError(String, PositionRange, PositionRange), // name, offending position, original position
    VariableRedefError(String, PositionRange, PositionRange), // name, offending position, original position
    DuplicateMemberError(String, String, PositionRange, PositionRange), // adt name, name, offending position, original position
    DuplicateArgError(String, PositionRange),                           // name, offending position
    DuplicatePatIdError(String, PositionRange, PositionRange), // name, offending position, original position
    DuplicateVariantError(String, String, PositionRange, PositionRange), // name, offending position, original position
    InvalidCtorError(PositionRange),
    AdtNotFoundError(String, PositionRange),
    AdtVariantNotFoundError(String, String, PositionRange), // adt name, adt variant name, position
    AdtNoBaseError(String, PositionRange, PositionRange), // adt name, error position, suggested position to insert Base
    MatchNotExhaustiveErr(Vec<String>, PositionRange),    // candidate, position
}

fn is_type_var(ty: &TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Var(_, _))
}
fn matches_float(ty: &TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Ty(SType::Primitve(Prim::Float)))
}
fn matches_int(ty: &TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Ty(SType::Primitve(Prim::Int)))
}
fn matches_bool(ty: &TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Ty(SType::Primitve(Prim::Bool)))
}
fn matches_number(ty: &TypeOrVar) -> bool {
    matches_float(ty) || matches_int(ty)
}

fn matches_numerical(ty: &TypeOrVar) -> bool {
    matches_float(ty) || matches_int(ty) || matches_bool(ty)
}

pub fn get_local(name: &String, prev_locals: &LocalsMap, locals: &LocalsMap) -> Option<Local> {
    match locals.get(name) {
        Some(t) => Some(*t),
        None => match prev_locals.get(name) {
            Some(t) => Some(*t),
            None => None,
        },
    }
}

impl Analyzer {
    fn print_type(&self, ty: &TypeOrVar) {
        match ty {
            TypeOrVar::Ty(t) => match t {
                SType::Top => println!("Top"),
                SType::Primitve(p) => println!("{}", p),
                SType::UserType(t) => println!("{}", self.id_map.get(t).unwrap()),
            },
            TypeOrVar::Var(v, _) => println!("TypeVar({})", v),
        };
    }

    fn type_to_string(&self, ty: &TypeOrVar) -> String {
        match ty {
            TypeOrVar::Ty(t) => match t {
                SType::Top => "Top".to_string(),
                SType::Primitve(p) => format!("{}", p),
                SType::UserType(t) => format!("{}", self.id_map.get(t).unwrap()),
            },
            TypeOrVar::Var(v, _) => format!("TypeVar({})", v),
        }
    }

    fn witness_to_string(&self, witness: &Witness) -> String {
        match witness {
            Witness::Int => "_".to_string(),
            Witness::String => "_".to_string(),
            Witness::Float => "_".to_string(),
            Witness::Wildcard => "_".to_string(),
            Witness::Bool(b) => b.to_string(),
            Witness::Adt(id, variant, wits) => {
                let adt_name = self.id_map.get(id).unwrap().to_owned();
                let var_name = self.id_map.get(variant).unwrap();

                let mut wit_str = "".to_string();
                let mut first = true;

                for w in wits {
                    if !first {
                        wit_str += ", "
                    }
                    first = false;

                    wit_str += &self.witness_to_string(w);
                }

                adt_name + "::" + var_name + "(" + &wit_str + ")"
            }
        }
    }

    fn get_adt_def(&self, id: &Identifier) -> Option<&SAdtDef> {
        self.adt_defs.get(id)
    }

    fn get_fun_def(&self, id: &Identifier) -> Option<&TmpFunDef> {
        self.fun_defs.get(id)
    }

    fn fresh_id(&mut self, name: String, pos: PositionRange) -> u64 {
        self.id_map.insert(self.local_id, name.to_string());
        self.id_pos_map.insert(self.local_id, pos);

        let ret = self.local_id;
        self.local_id += 1;
        ret
    }

    // pos: whichever identifier it belongs to
    fn fresh_type_var(&mut self, pos: PositionRange) -> TypeOrVar {
        let id = self.unions.fresh_var();
        let ret = TypeOrVar::Var(id, pos);
        self.type_map_all.insert(id, ret);
        ret
    }

    fn types_ok(&self, expected: SType, actual: SType) -> bool {
        match (expected, actual) {
            (SType::Primitve(p), SType::Primitve(q)) => p == q,
            (SType::Primitve(_), SType::UserType(_)) => false,
            (SType::UserType(_), SType::Primitve(_)) => false,
            (SType::UserType(p), SType::UserType(q)) => p == q,
            (SType::Top, _) | (_, SType::Top) => true,
        }
    }

    fn resolve_type(&mut self, ty: TypeOrVar) -> TypeOrVar {
        match ty {
            TypeOrVar::Ty(_) => ty,
            TypeOrVar::Var(v, _) => {
                let rt = self.unions.find_set(v);
                match self.type_map.get(&rt) {
                    Some(t) => TypeOrVar::Ty(*t),
                    None => ty,
                }
            }
        }
    }

    fn resolve_type_imut(&self, ty: TypeOrVar) -> TypeOrVar {
        match ty {
            TypeOrVar::Ty(_) => ty,
            TypeOrVar::Var(v, _) => {
                let rt = self.unions.find_set_imut(v);
                match self.type_map.get(&rt) {
                    Some(t) => TypeOrVar::Ty(*t),
                    None => ty,
                }
            }
        }
    }

    fn stype_str(&self, t: &SType) -> String {
        match t {
            SType::Primitve(p) => p.to_string(),
            SType::UserType(id) => self.id_map.get(id).unwrap().to_string(),
            SType::Top => "<Top>".to_string(),
        }
    }

    fn add_constraint_pos(
        &mut self,
        expr: SStatExprPos,
        expected: TypeOrVar,
        actual: TypeOrVar,
    ) -> Option<SStatExprPos> {
        self.add_constraint(expr.expr, expected, actual, expr.pos)
    }

    // returns converted expression, type of new expression
    fn implicit_convert(
        &self,
        expr: SStatExprPos,
        expected: TypeOrVar,
        actual: TypeOrVar,
    ) -> (SStatExprPos, TypeOrVar) {
        use crate::parsing::tokens::Prim::*;

        let pos = expr.pos;

        match (expected, actual) {
            (TypeOrVar::Ty(SType::Primitve(p1)), TypeOrVar::Ty(SType::Primitve(p2))) => {
                let new_expr = match (p1, p2) {
                    (Float, Bool) => BoolToFloat(Box::new(expr)),
                    (Float, Int) => IntToFloat(Box::new(expr)),
                    (Int, Bool) => BoolToInt(Box::new(expr)),
                    (Bool, Float) => FloatToBool(Box::new(expr)),
                    (Bool, Int) => IntToBool(Box::new(expr)),
                    _ => return (expr, actual),
                };
                (
                    SStatExprPos {
                        expr: new_expr,
                        pos,
                    },
                    expected,
                )
            }
            _ => (expr, actual),
        }
    }

    // Also handles implicit conversions.
    fn add_constraint(
        &mut self,
        expr: SStatExpr,
        expected: TypeOrVar,
        actual: TypeOrVar,
        pos: PositionRange,
    ) -> Option<SStatExprPos> {
        // resolve types
        let r_expected = self.resolve_type(expected);
        let r_actual = self.resolve_type(actual);

        let res = self.implicit_convert(SStatExprPos { expr, pos }, r_expected, r_actual);

        let expr = res.0;
        let c_actual = res.1;

        if self.add_type_constraint(r_expected, c_actual, pos) {
            Some(expr)
        } else {
            None
        }
    }

    // Also handles implicit conversions.
    fn add_type_constraint(
        &mut self,
        expected: TypeOrVar,
        actual: TypeOrVar,
        pos: PositionRange,
    ) -> bool {
        // useful imports
        use crate::analysis::symbolic_ast::SType::*;

        let r_expected = self.resolve_type(expected);
        let r_actual = self.resolve_type(actual);

        match (r_expected, r_actual) {
            (TypeOrVar::Ty(p), TypeOrVar::Ty(q)) => {
                if self.types_ok(p, q) {
                    true
                } else {
                    self.type_errors.push(TypeError::TypeMismatch(
                        self.stype_str(&p),
                        self.stype_str(&q),
                        pos,
                    ));
                    false
                }
            }
            (TypeOrVar::Ty(t), TypeOrVar::Var(r, _)) | (TypeOrVar::Var(r, _), TypeOrVar::Ty(t)) => {
                // set root id in map to type
                if !matches!(t, Top) {
                    self.type_map.insert(r, t);
                }

                true
            }
            (TypeOrVar::Var(r1, _), TypeOrVar::Var(r2, _)) => {
                // union using data structure
                self.unions.union(r1, r2);
                true
            }
        }
    }

    // If error, just return Top
    fn transform_type(
        &mut self,
        t: &Option<TypePos>,
        id_pos: PositionRange,
        adts: &AdtMap,
    ) -> TypeOrVar {
        match t {
            Some(ty) => match &ty.ty {
                Type::Primitve(p) => TypeOrVar::Ty(SType::Primitve(*p)),

                Type::UserType(t) => {
                    // TODO: FOR NOW just use the head. But later on this needs to be changed
                    // to support importing scopes/namespaces.
                    let id = adts.get(&t.name);

                    match id {
                        Some(id) => TypeOrVar::Ty(SType::UserType(*id)),
                        _ => {
                            self.name_errors
                                .push(AnalysisError::TypeNotFound(t.to_string(), ty.pos));
                            TypeOrVar::Ty(SType::Top)
                        }
                    }
                }
            },
            None => self.fresh_type_var(id_pos),
        }
    }

    fn add_fn_locals(
        &mut self,
        params: &Vec<(String, SParamDef)>,
        locals: &LocalsMap,
    ) -> LocalsMap {
        let mut ret = locals.to_owned();

        for p in params {
            ret = ret.insert(p.0.to_string(), (p.1.name, p.1.ty));
        }

        ret
    }

    // will update the fn map
    // function will only ever be transformed once.
    fn transform_fn(
        &mut self,
        fun_name: &String,  // name
        pos: PositionRange, // where the function was found
        locals: &LocalsMap, // locals
        fns: &FnMap,        // fns
        adts: &AdtMap,      // adts
    ) {
        // get id, then def
        let fun_id = *match fns.get(fun_name) {
            Some(id) => id,
            None => {
                self.name_errors
                    .push(AnalysisError::FnNotFoundError(fun_name.clone(), pos));
                return;
            }
        };

        let fun_def = match self.get_fun_def(&fun_id) {
            Some(f) => f,
            None => {
                self.name_errors
                    .push(AnalysisError::FnNotFoundError(fun_name.clone(), pos));
                return;
            }
        };

        // if already transformed, return
        if matches!(&fun_def.body, NSExprPos::S(_)) {
            return;
        }

        let fun_def_owned = self.fun_defs.remove(&fun_id).unwrap();

        let body = match fun_def_owned.body {
            NSExprPos::N(e) => e,
            NSExprPos::S(_) => unreachable!(),
        };

        let locals_ = match fun_def_owned.captured_locals {
            Some(l) => l,
            None => locals.clone(),
        };

        let more_locals = self.add_fn_locals(&fun_def_owned.params, &locals_);

        let body_pos = body.pos;

        // let stripped = self.scan_defs(body, fns.clone(), adts.clone());

        // re-insert dummy definition in case of recursive calls inside the body
        let dummy_expr = SStatExprPos {
            expr: Dummy,
            pos: body_pos,
        };

        let dummy = TmpFunDef {
            name_str: fun_def_owned.name_str,
            name: fun_def_owned.name,
            name_pos: fun_def_owned.name_pos,
            ty: fun_def_owned.ty,
            captured_locals: Some(locals_),
            params: fun_def_owned.params,
            body: NSExprPos::S(dummy_expr),
        };
        self.fun_defs.insert(fun_id, dummy);

        let transformed = self.convert_stat_expr(
            body,
            fun_def_owned.ty,
            &more_locals,
            &LocalsMap::new(),
            &fns,
            &adts,
        );

        // If not transformed correctly, return
        if transformed.is_none() {
            return;
        }

        let transformed_ = transformed.unwrap();

        // retrieve dummy and reuse its relevant data
        let retrieved = self.fun_defs.remove(&fun_id).unwrap();

        // reinsert information from dummy
        let new = TmpFunDef {
            name_str: retrieved.name_str,
            name: retrieved.name,
            name_pos: retrieved.name_pos,
            ty: retrieved.ty,
            params: retrieved.params,
            captured_locals: retrieved.captured_locals,
            body: NSExprPos::S(transformed_.0),
        };

        self.fun_defs.insert(fun_id, new);
    }

    // Adds extra functions and adts to the map in the current scope
    fn scan_defs(&mut self, e: Expr, fns: FnMap, adts: AdtMap) -> (Expr, FnMap, AdtMap) {
        let (fns_, adts_) = self.scan_names(&e, fns, adts);
        (self.scan_defs_rec(e, &fns_, &adts_), fns_, adts_)
    }

    fn scan_names(&mut self, e: &Expr, mut fns: FnMap, mut adts: AdtMap) -> (FnMap, AdtMap) {
        for se in e {
            match &se.expr {
                StatExpr::AdtDefn(defn) => {
                    if adts.contains_key(&defn.name) {
                        // error
                        let id = adts.get(&defn.name).unwrap();
                        let og_pos = self.id_pos_map.get(&id).unwrap();

                        self.name_errors.push(AnalysisError::NameAlreadyUsedError(
                            defn.name.to_string(),
                            defn.name_pos,
                            *og_pos,
                        ));
                    } else {
                        let id = self.fresh_id(defn.name.clone(), defn.name_pos);
                        adts = adts.insert(defn.name.clone(), id);
                    }
                }
                StatExpr::FunDefn(defn) => {
                    if fns.contains_key(&defn.name) {
                        // error
                        let id = fns.get(&defn.name).unwrap();
                        let og_pos = self.id_pos_map.get(&id).unwrap();

                        self.name_errors.push(AnalysisError::NameAlreadyUsedError(
                            defn.name.to_string(),
                            defn.name_pos,
                            *og_pos,
                        ));
                    } else {
                        let id = self.fresh_id(defn.name.clone(), defn.name_pos);
                        fns = fns.insert(defn.name.clone(), id);
                    }
                }
                _ => {}
            }
        }

        (fns, adts)
    }

    fn convert_adt(&mut self, id: Identifier, defn: AdtDef, adts: &AdtMap) -> SAdtDef {
        let mut name_map: HashMap<String, Identifier> = HashMap::new();
        let mut name_pos_map: HashMap<String, PositionRange> = HashMap::new();

        // add universal parameters to set

        let mut s_params: Vec<SParamDef> = Vec::new();
        // rules to be enforced:
        // 1. variants cannot have the same name
        // 2. for any one variant, its parameters combined with the
        //    universal parameters may not clash

        // TODO: should refactor this, a lot of code is copied and pasted

        // 1. scan universal names
        for p in defn.params {
            let maybe_pos = name_pos_map.get(&p.name);
            // name already used
            if maybe_pos.is_some() {
                let n = maybe_pos.unwrap();
                self.name_errors.push(AnalysisError::DuplicateMemberError(
                    p.name.clone(),
                    defn.name.clone(),
                    p.nme_pos,
                    *n,
                ));
            }
            // just continue and see what happens :)

            let id = self.fresh_id(p.name.clone(), p.nme_pos);
            let ty = self.transform_type(&p.ty, p.nme_pos, adts);

            name_map.insert(p.name.clone(), id);
            name_pos_map.insert(p.name.clone(), p.nme_pos);

            s_params.push(SParamDef {
                name: id,
                ty,
                pos: p.nme_pos,
            })
        }

        let mut s_variants: BTreeMap<Identifier, SAdtVariant> = BTreeMap::new();

        let mut variant_name_map: HashMap<String, Identifier> = HashMap::new();
        let mut variant_pos_map: HashMap<String, PositionRange> = HashMap::new();

        // if no variants, create a default one
        if defn.variants.is_empty() {
            let def_id = self.fresh_id("Base".to_string(), defn.name_pos);
            variant_name_map.insert("Base".to_string(), def_id);

            s_variants.insert(
                def_id,
                SAdtVariant {
                    name: def_id,
                    name_pos: defn.name_pos,
                    params: vec![],
                },
            );
        }

        // 2. scan variants, convert them too
        for v in defn.variants {
            let maybe_pos = variant_pos_map.get(&v.name);
            // name already used
            if maybe_pos.is_some() {
                let n = maybe_pos.unwrap();
                self.name_errors.push(AnalysisError::DuplicateVariantError(
                    v.name.clone(),
                    defn.name.clone(),
                    v.name_pos,
                    *n,
                ));
            }

            let id = self.fresh_id(v.name.clone(), v.name_pos);

            variant_name_map.insert(v.name.clone(), id);
            variant_pos_map.insert(v.name.clone(), v.name_pos);

            // convert parameters

            let mut s_variant_params: Vec<SParamDef> = Vec::new();

            let mut variant_int_name_map: HashMap<String, Identifier> = HashMap::new();
            let mut variant_int_pos_map: HashMap<String, PositionRange> = HashMap::new();

            for p in v.params {
                let maybe_pos1 = name_pos_map.get(&p.name);
                let maybe_pos2 = variant_int_pos_map.get(&p.name);
                // name already used
                if maybe_pos1.is_some() {
                    let n = maybe_pos1.unwrap();
                    self.name_errors.push(AnalysisError::DuplicateMemberError(
                        p.name.clone(),
                        defn.name.clone(),
                        p.nme_pos,
                        *n,
                    ));
                } else if maybe_pos2.is_some() {
                    let n = maybe_pos2.unwrap();
                    self.name_errors.push(AnalysisError::DuplicateMemberError(
                        p.name.clone(),
                        defn.name.clone(),
                        p.nme_pos,
                        *n,
                    ));
                }

                let id = self.fresh_id(p.name.clone(), p.nme_pos);
                let ty = self.transform_type(&p.ty, p.nme_pos, adts);

                variant_int_name_map.insert(p.name.clone(), id);
                variant_int_pos_map.insert(p.name.clone(), p.nme_pos);

                s_variant_params.push(SParamDef {
                    name: id,
                    ty,
                    pos: p.nme_pos,
                })
            }

            // create variant
            s_variants.insert(
                id,
                SAdtVariant {
                    name: id,
                    name_pos: v.name_pos,
                    params: s_variant_params,
                },
            );
        }

        SAdtDef {
            name: id,
            name_pos: defn.name_pos,
            params: s_params,
            name_map,
            variant_name_map,
            variants: s_variants,
            wildcard: SPatternPos {
                pat: SPattern::WildcardPattern,
                ty: SType::UserType(id),
                pos: defn.name_pos, // dummy, not used
            },
        }
    }

    // strips away all adt definitions, replaces function definitions with IDs
    fn scan_defs_rec(&mut self, mut expr: Expr, fns: &FnMap, adts: &AdtMap) -> Expr {
        let mut ret: Expr = vec![];

        for e in expr {
            match e.expr {
                StatExpr::AdtDefn(defn) => {
                    let id = *adts.get(&defn.name).unwrap();

                    if !self.adt_defs.contains_key(&id) {
                        let converted = self.convert_adt(id, defn, adts);
                        self.adt_defs.insert(id, converted);
                    }

                    // quick hack, adt definitions have a unit type
                    ret.push(StatExprPos {
                        expr: StatExpr::UnitLit,
                        pos: e.pos,
                    })
                }
                StatExpr::FunDefn(defn) => {
                    let id = *fns.get(&defn.name).unwrap();

                    // if name already exists, this error was already caught before. just ignore
                    if !self.fun_defs.contains_key(&id) {
                        let mut new_params: Vec<(String, SParamDef)> = vec![];
                        let mut names: HashSet<String> = HashSet::new(); // check for duplicate param names

                        for p in defn.params {
                            if names.contains(&p.name) {
                                self.name_errors.push(AnalysisError::DuplicateArgError(
                                    p.name.clone(),
                                    p.nme_pos,
                                ));
                            }

                            let id = self.fresh_id(p.name.clone(), p.nme_pos);
                            names.insert(p.name.clone());
                            new_params.push((
                                p.name,
                                SParamDef {
                                    name: id,
                                    ty: self.transform_type(&p.ty, p.nme_pos, &adts),
                                    pos: p.nme_pos,
                                },
                            ))
                        }

                        let name_pos = defn.name_pos;

                        let nme = defn.name.to_string();

                        let defn = TmpFunDef {
                            name_str: nme.to_string(),
                            name: id,
                            name_pos,
                            ty: self.transform_type(&defn.ty, name_pos, &adts),
                            params: new_params,
                            captured_locals: None,
                            body: NSExprPos::N(*defn.body),
                        };

                        self.fun_defs.insert(id, defn);

                        ret.push(StatExprPos {
                            expr: StatExpr::FunDefId(id, name_pos),
                            pos: e.pos,
                        })
                    }
                }
                _ => ret.push(e),
            }
        }

        ret
    }

    fn find_ctor(
        &mut self,
        qn: &QualifiedName,
        adts: &AdtMap,
        report_error: bool,
    ) -> Option<(&SAdtDef, &SAdtVariant)> {
        // no support for importing scopes yet
        if qn.scopes.len() >= 2 {
            unimplemented!();
        }

        let adt_name = if qn.scopes.len() == 0 {
            (qn.name.clone(), qn.name_pos)
        } else {
            qn.scopes.last().unwrap().clone()
        };

        let ctor_name = if qn.scopes.len() == 0 {
            ("Base".to_string(), qn.name_pos)
        } else {
            (qn.name.clone(), qn.name_pos)
        };

        // resolve name of adt
        let adt_id = *match adts.get(&adt_name.0) {
            Some(id) => id,
            None => {
                if report_error {
                    // error
                    self.name_errors
                        .push(AnalysisError::AdtNotFoundError(adt_name.0, adt_name.1))
                }
                return None;
            }
        };

        let adt_def = self.adt_defs.get(&adt_id).unwrap();

        // resolve ctor
        let ctor_id = *match adt_def.variant_name_map.get(&ctor_name.0) {
            Some(id) => id,
            None => {
                // error

                if report_error {
                    if qn.scopes.len() == 0 {
                        self.name_errors.push(AnalysisError::AdtNoBaseError(
                            adt_name.0,
                            adt_name.1,
                            adt_def.name_pos,
                        ));
                    } else {
                        self.name_errors
                            .push(AnalysisError::AdtVariantNotFoundError(
                                adt_name.0,
                                ctor_name.0,
                                ctor_name.1,
                            ));
                    }
                }
                return None;
            }
        };

        let ctor = adt_def.variants.get(&ctor_id).unwrap();

        Some((adt_def, ctor))
    }

    fn convert_args(
        &mut self,
        args: Vec<StatExprPos>,
        types: &Vec<TypeOrVar>,
        qn: &QualifiedName,
        pos: PositionRange,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
    ) -> Option<Vec<SStatExprPos>> {
        let args_len = types.len();
        let actual_len = args.len();

        // type check args
        let mut transformed_args: Vec<Converted> = Vec::new();

        // type check even if lengths are incompatible, do as much as possible
        // zip will return the longest allowed array
        for (arg, ty) in zip(args, types) {
            // type checking occurs here
            transformed_args.push(self.convert_stat_expr(arg, *ty, prev_locals, locals, fns, adts));
        }

        // check args length correct
        if actual_len != args_len {
            self.name_errors.push(AnalysisError::WrongNoArgsError(
                qn.to_string(),
                args_len,
                actual_len,
                pos,
            ));
            return None;
        }

        // transform options into exprs
        let mut transformed_final: Vec<SStatExprPos> = Vec::new();

        for e_ in transformed_args {
            transformed_final.push(e_?.0)
        }

        Some(transformed_final)
    }

    pub fn convert_top(&mut self, e: Expr) -> Option<SExpr> {
        // scan definitions
        let stripped = self.scan_defs(e, TreeMap::new(), TreeMap::new());
        let pos = match stripped.0.last() {
            Some(e) => e.pos,
            None => PositionRange {
                start: Position { line_no: 0, pos: 0 },
                end: Position { line_no: 0, pos: 0 },
            },
        };

        let ret = self.convert(
            stripped.0,
            TypeOrVar::Ty(SType::Top),
            &TreeMap::new(),
            &TreeMap::new(),
            &stripped.1,
            &stripped.2,
        );

        // transform any remaining functions not yet transformed
        for fn_id in stripped.1.into_iter() {
            self.transform_fn(fn_id.0, pos, &LocalsMap::new(), &stripped.1, &stripped.2)
        }

        // Look for unbound type variables.
        let mut checked: HashSet<u64> = HashSet::new();

        for i in 0..self.unions.size() {
            let rt = self.unions.find_set(i);
            if checked.contains(&rt) {
                continue;
            }

            checked.insert(rt);

            let ty = self.type_map_all.get(&rt).unwrap();

            let t = self.resolve_type(*ty);
            match t {
                TypeOrVar::Ty(_) => (),
                TypeOrVar::Var(_, pos) => {
                    self.type_errors.push(TypeError::TypeNeededError(pos));
                }
            }
        }

        return ret;
    }

    // Converts everything to a float implicitly if at least one expression is a float.
    // Otherwise, conerts them to an integer.
    // If err, return the converted expressoins and their types.

    // Return spec:
    // OK: (e1, e2, is_float, is_top)
    // ERR: e1, e2, t1, t2.

    // this really should be refactored...
    fn convert_maybe_float(
        &mut self,
        e1: StatExprPos,
        e2: StatExprPos,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
        error_on_neq: bool,
    ) -> Result<
        (SStatExprPos, SStatExprPos, bool, bool),
        Option<(SStatExprPos, SStatExprPos, TypeOrVar, TypeOrVar)>,
    > {
        let left_t = self.fresh_type_var(e1.pos);
        let right_t = self.fresh_type_var(e2.pos);

        let e1_p = e1.pos;
        let e2_p = e2.pos;

        let s_e1_ = self.convert_stat_expr(e1, left_t, prev_locals, locals, fns, adts);
        let s_e2_ = self.convert_stat_expr(e2, right_t, prev_locals, locals, fns, adts);

        if s_e1_.is_none() || s_e2_.is_none() {
            return Err(None);
        }

        let s_e1 = s_e1_.unwrap();
        let s_e2 = s_e2_.unwrap();

        let left_r = self.resolve_type(left_t);
        let right_r = self.resolve_type(right_t);

        // if either are top
        if matches!(left_r, TypeOrVar::Ty(SType::Top))
            || matches!(right_r, TypeOrVar::Ty(SType::Top))
        {
            return Ok((s_e1.0, s_e2.0, false, true));
        }

        let mut fail = false;

        // types must be known
        if matches!(left_r, TypeOrVar::Var(_, _)) {
            self.type_errors.push(TypeError::TypeNeededError(e1_p));
            fail = true;
        } else if !matches_float(&left_r) && !matches_int(&left_r) && !matches_bool(&left_r) {
            // both must be ints, floats or bools
            if error_on_neq {
                self.type_errors.push(TypeError::InvalidOperandError(e1_p));
            }

            fail = true;
        }

        if matches!(right_r, TypeOrVar::Var(_, _)) {
            self.type_errors.push(TypeError::TypeNeededError(e2_p));
            fail = true;
        } else if !matches_float(&right_r) && !matches_int(&right_r) && !matches_bool(&right_r) {
            if error_on_neq {
                self.type_errors.push(TypeError::InvalidOperandError(e2_p));
            }
            fail = true;
        }

        if fail {
            return Err(Some((s_e1.0, s_e2.0, left_r, right_r)));
        }

        // remaining case handling
        if matches_float(&left_r) || matches_float(&right_r) {
            let float_prim = TypeOrVar::Ty(SType::Primitve(Prim::Float));
            let e1 = self.add_constraint_pos(s_e1.0, float_prim, left_r).unwrap();
            let e2 = self
                .add_constraint_pos(s_e2.0, float_prim, right_r)
                .unwrap();

            Ok((e1, e2, true, false))
        } else {
            // both are integers
            let int_prim = TypeOrVar::Ty(SType::Primitve(Prim::Int));
            let e1 = self.add_constraint_pos(s_e1.0, int_prim, left_r).unwrap();
            let e2 = self.add_constraint_pos(s_e2.0, int_prim, right_r).unwrap();

            Ok((e1, e2, false, false))
        }
    }

    fn convert_adt_pat(
        &mut self,
        qn: QualifiedName,
        adts: &AdtMap,
        pats: Vec<PatternPos>,
        cur_locals: &LocalsMap,
        pos: PositionRange,
    ) -> Option<(SPatternPos, LocalsMap)> {
        let name = qn.to_string();

        let (adt_def, ctor) = self.find_ctor(&qn, adts, true)?;

        let adt_id = adt_def.name;
        let ctor_id = ctor.name;

        // We allow matching using *all* parameters, including the invariant ones of the ADT,
        // or just the parameters of a certain variant.
        //
        // If we have:
        // adt A(a, b) = VarA(c), VarB(d)
        //
        // then
        // A::VarA(pat)
        // is equivalent to
        // A::VarA(_, _, c)
        // where the first two _ are bound to a and b.
        let p1_len = adt_def.params.len();
        let p2_len = ctor.params.len();

        let adt_ty: Vec<TypeOrVar> = adt_def.params.iter().map(|p| p.ty).collect();
        let ctor_ty: Vec<TypeOrVar> = ctor.params.iter().map(|p| p.ty).collect();

        let mut is_short = false;

        let types = if pats.len() == p1_len + p2_len {
            vec![adt_ty, ctor_ty].concat()
        } else if pats.len() == p2_len {
            is_short = true;
            ctor_ty
        } else {
            self.name_errors.push(AnalysisError::WrongNoArgsError(
                name,
                p2_len,
                pats.len(),
                pos,
            ));
            return None;
        };

        let mut new_pats: Vec<SPatternPos> = vec![];

        // Pad with wildcard patterns
        if is_short {
            for pd in &adt_def.params {
                let ty = match pd.ty {
                    TypeOrVar::Ty(t) => t,
                    TypeOrVar::Var(_, pos) => {
                        self.type_errors.push(TypeError::TypeNeededError(pos));
                        return None;
                    }
                };

                new_pats.push(SPatternPos {
                    pat: SPattern::WildcardPattern,
                    pos,
                    ty,
                })
            }
        }

        let mut more_locals = cur_locals.clone();

        // zip patterns and expected types, and type check
        for (pat, ty) in zip(pats, types) {
            let maybe = self.check_and_bind(adts, pat, ty, &more_locals);

            if maybe.is_none() {
                continue;
            }

            let (s_pat, more) = maybe.unwrap();

            more_locals = more;
            new_pats.push(s_pat);
        }

        Some((
            SPatternPos {
                pat: SPattern::AdtPattern(adt_id, ctor_id, new_pats),
                pos,
                ty: SType::UserType(adt_id),
            },
            more_locals,
        ))
    }

    fn check_and_bind(
        &mut self,
        adts: &AdtMap,
        pat: PatternPos,
        expected: TypeOrVar,
        cur_locals: &LocalsMap,
    ) -> Option<(SPatternPos, LocalsMap)> {
        let ty = match expected {
            TypeOrVar::Ty(t) => t,
            TypeOrVar::Var(_, pos) => {
                self.type_errors.push(TypeError::TypeNeededError(pos));
                return None;
            }
        };

        match pat.pat {
            Pattern::WildcardPattern => Some((
                SPatternPos {
                    pat: SPattern::WildcardPattern,
                    pos: pat.pos,
                    ty,
                },
                cur_locals.clone(),
            )),
            Pattern::IdOrAdtPattern(name) => {
                // pseudo qualified name to check for constructors
                let qn = QualifiedName {
                    scopes: vec![],
                    name: name.clone(),
                    name_pos: pat.pos,
                    members: vec![],
                };

                let opt = self.find_ctor(&qn, adts, false);

                match opt {
                    Some((_, _)) => {
                        // simple case, ADT def with no arguments.
                        self.convert_adt_pat(qn, adts, vec![], cur_locals, pat.pos)
                    }
                    None => {
                        // If local already has name, error
                        if cur_locals.contains_key(&name) {
                            let id = cur_locals.get(&name).unwrap();
                            let og_pos = self.id_pos_map.get(&id.0).unwrap();
                            self.name_errors.push(AnalysisError::DuplicatePatIdError(
                                name.clone(),
                                pat.pos,
                                *og_pos,
                            ))
                        }

                        // is ID otherwise
                        let local = self.fresh_id(name.clone(), pat.pos);
                        Some((
                            SPatternPos {
                                pat: SPattern::IdPattern(local),
                                pos: pat.pos,
                                ty,
                            },
                            cur_locals.insert(name, (local, expected)), // has expected type
                        ))
                    }
                }
            }
            Pattern::IntLiteralPattern(v) => {
                let int_lit = TypeOrVar::Ty(SType::Primitve(Prim::Int));

                self.add_type_constraint(expected, int_lit, pat.pos);

                Some((
                    SPatternPos {
                        pat: SPattern::IntLiteralPattern(v),
                        pos: pat.pos,
                        ty: SType::Primitve(Prim::Int),
                    },
                    cur_locals.clone(),
                ))
            }
            Pattern::FloatLiteralPattern(v) => {
                let lit = TypeOrVar::Ty(SType::Primitve(Prim::Float));

                self.add_type_constraint(expected, lit, pat.pos);

                Some((
                    SPatternPos {
                        pat: SPattern::FloatLiteralPattern(v),
                        pos: pat.pos,
                        ty: SType::Primitve(Prim::Float),
                    },
                    cur_locals.clone(),
                ))
            }
            Pattern::StringLiteralPattern(v) => {
                let lit = TypeOrVar::Ty(SType::Primitve(Prim::String));

                self.add_type_constraint(expected, lit, pat.pos);

                Some((
                    SPatternPos {
                        pat: SPattern::StringLiteralPattern(v.clone()),
                        pos: pat.pos,
                        ty: SType::Primitve(Prim::String),
                    },
                    cur_locals.clone(),
                ))
            }
            Pattern::BoolLiteralPattern(v) => {
                let lit = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                self.add_type_constraint(expected, lit, pat.pos);

                Some((
                    SPatternPos {
                        pat: SPattern::BoolLiteralPattern(v),
                        pos: pat.pos,
                        ty: SType::Primitve(Prim::Bool),
                    },
                    cur_locals.clone(),
                ))
            }
            Pattern::AdtPattern(qn, pats) => {
                self.convert_adt_pat(qn, adts, pats, cur_locals, pat.pos)
            }
        }
    }

    fn get_wildcard<'a>(&'a self, ty: &SType) -> &'a SPatternPos {
        match ty {
            SType::Top => &TOP_WILDCARD,
            SType::Primitve(p) => match p {
                Prim::Int => &INT_WILDCARD,
                Prim::Float => &FLOAT_WILDCARD,
                Prim::String => &STRING_WILDCARD,
                Prim::Bool => &BOOL_WILDCARD,
                Prim::Unit => unreachable!("Unit wildcard requested"),
            },
            SType::UserType(id) => &self.get_adt_def(id).unwrap().wildcard,
        }
    }

    fn specialize<'a>(
        &'a self,
        ctor: &Ctor,
        pat: &'a SPatternPos,
    ) -> Result<Option<Vec<&'a SPatternPos>>, PositionRange> {
        match (ctor, &pat.pat) {
            // Arbitrary vs wildcard/id
            (Ctor::Arbitrary, SPattern::WildcardPattern)
            | (Ctor::Arbitrary, SPattern::IdPattern(_)) => Ok(Some(vec![])),

            // Literal wildcard cases
            (Ctor::BoolCtor(_), SPattern::WildcardPattern)
            | (Ctor::BoolCtor(_), SPattern::IdPattern(_)) => Ok(Some(vec![])),

            (Ctor::BoolCtor(v1), SPattern::BoolLiteralPattern(v2)) if v1 == v2 => Ok(Some(vec![])),

            // Adt wildcard ctor cases. just return wildcards
            (Ctor::AdtCtor(ctor, variant), SPattern::WildcardPattern)
            | (Ctor::AdtCtor(ctor, variant), SPattern::IdPattern(_)) => {
                let adt_def = self.adt_defs.get(ctor).unwrap();
                let var_def = adt_def.variants.get(variant).unwrap();

                let mut ret: Vec<&SPatternPos> = vec![];

                for param in &adt_def.params {
                    let ty = match param.ty {
                        TypeOrVar::Ty(t) => t,
                        TypeOrVar::Var(_, pos) => {
                            return Err(pos);
                        }
                    };
                    ret.push(self.get_wildcard(&ty))
                }

                for param in &var_def.params {
                    let ty = match param.ty {
                        TypeOrVar::Ty(t) => t,
                        TypeOrVar::Var(_, pos) => {
                            return Err(pos);
                        }
                    };
                    ret.push(self.get_wildcard(&ty))
                }

                Ok(Some(ret))
            }

            (Ctor::AdtCtor(ctor, variant), SPattern::AdtPattern(ctor_got, variant_got, pats))
                if *ctor == *ctor_got && *variant == *variant_got =>
            {
                let mut ret: Vec<&SPatternPos> = vec![];

                for p in pats {
                    ret.push(p)
                }

                Ok(Some(ret))
            }

            _ => Ok(None),
        }
    }

    fn specialize_pats<'a>(
        &'a self,
        ctor: &Ctor,
        pats: &Vec<&'a SPatternPos>,
    ) -> Result<Option<Vec<Vec<&'a SPatternPos>>>, PositionRange> {
        let first = match pats.first() {
            Some(v) => v,
            None => return Ok(None),
        };

        let mut ret: Vec<&SPatternPos>;

        match self.specialize(&ctor, &first)? {
            Some(v) => ret = v,
            None => return Ok(None),
        };

        for i in 1..pats.len() {
            ret.push(pats.get(i).unwrap());
        }

        Ok(Some(vec![ret]))
    }

    fn usefulness<'a>(
        &'a self,
        ty: Option<SType>,
        pat_stacks: &'a Vec<Vec<&'a SPatternPos>>,
        q: &'a Vec<&'a SPatternPos>,
    ) -> Result<Vec<Vec<Witness>>, PositionRange> {
        // Base cases

        fn to_witness_vec<'a>(q: &'a Vec<&'a SPatternPos>) -> Vec<Witness> {
            let mut ret: Vec<Witness> = vec![];

            for pat in q {
                ret.push(to_witness(pat))
            }

            ret
        }

        fn to_witness(pat: &SPatternPos) -> Witness {
            match &pat.pat {
                SPattern::WildcardPattern => Witness::Wildcard,
                SPattern::IdPattern(_) => Witness::Wildcard,
                SPattern::IntLiteralPattern(_) => Witness::Int,
                SPattern::FloatLiteralPattern(_) => Witness::Float,
                SPattern::StringLiteralPattern(_) => Witness::String,
                SPattern::BoolLiteralPattern(b) => Witness::Bool(*b),
                SPattern::AdtPattern(id, ctor, pats) => {
                    let mut pats_ref: Vec<&SPatternPos> = vec![];
                    for p in pats {
                        pats_ref.push(&p);
                    }
                    Witness::Adt(*id, *ctor, to_witness_vec(&pats_ref))
                }
            }
        }

        if pat_stacks.len() == 0 {
            return Ok(vec![to_witness_vec(q)]);
        }

        let cols = pat_stacks.first().unwrap().len();
        if cols == 0 {
            // return Ok(pat_stacks.to_vec());
            return Ok(vec![]);
        }

        // type must exist
        let ty = ty.unwrap();

        // Inductive case.

        // (!!) Important trick to make the running time proportional to the number of items in the "pattern tree",
        //      and NOT exponential in the depth/branching factor of the adts.
        //
        // If there is one identifier or wildcard pattern in the first column, we can just pop that from the pat stacks
        // and compute the remaining recursively.

        let has_wildcard = pat_stacks.iter().any(|p| {
            matches!(
                p.first().unwrap().pat,
                SPattern::WildcardPattern | SPattern::IdPattern(_)
            )
        });

        if has_wildcard {
            // Create new pat stacks.
            let mut new_pat_stacks: Vec<Vec<&'a SPatternPos>> = vec![];

            for p in pat_stacks {
                let mut new_stack: Vec<&'a SPatternPos> = vec![];
                for i in 1..p.len() {
                    new_stack.push(p.get(i).unwrap())
                }

                new_pat_stacks.push(new_stack)
            }

            // Create new q
            let mut new_q: Vec<&'a SPatternPos> = vec![];

            for i in 1..q.len() {
                new_q.push(q.get(i).unwrap())
            }

            // Get type

            let next_ty = match new_q.first() {
                Some(pat) => Some(pat.ty),
                None => None,
            };

            // Recurse
            let wits = self.usefulness(next_ty, &new_pat_stacks, &new_q)?;

            let mut ret: Vec<Vec<Witness>> = vec![];

            for mut w in wits {
                w.insert(0, Witness::Wildcard);
                ret.push(w);
            }

            return Ok(ret);
        }

        // (!!) Otherwise, we do the usual checking.

        // Determine all constructors of ty

        // For int, float, and string, we just push an "Arbitrary" constructor.
        //
        // This Arbitrary value is typeless; it just represents any arbitrary value
        // of the required type, which is fine because we assume the pattern type checks
        // (guaranteed by the previous stage).
        //
        // The idea is that nobody can pracitcally write ALL cases for all ints, floats and
        // strings, so we just push an arbitrary value to represent some case not matched.
        let ctors: Vec<Ctor> = match ty {
            SType::Top => vec![],
            SType::Primitve(t) => match t {
                Prim::Int | Prim::Float | Prim::String => vec![Ctor::Arbitrary],
                Prim::Bool => vec![Ctor::BoolCtor(true), Ctor::BoolCtor(false)],
                Prim::Unit => unreachable!(),
            },
            SType::UserType(id) => {
                // get adt def
                let adt_def = self.adt_defs.get(&id).unwrap();

                adt_def
                    .variants
                    .iter()
                    .map(|(_, variant)| Ctor::AdtCtor(id, variant.name))
                    .collect()
            }
        };

        //  For each ctor c,
        //      Compute specialize(c, q_1), ..., specialize(c, q_n)
        //      For each ctor q' in specialize(c, q),
        //           Compute usefuless(specialize(c, q_1), ..., specialize(c, q_n), q')

        let mut ret: Vec<Vec<Witness>> = vec![];

        for c in ctors {
            // Specialize q
            let q_specialized = match self.specialize_pats(&c, q)? {
                Some(q_) => q_,
                None => continue,
            };

            let mut pats_specialized: Vec<Vec<&'a SPatternPos>> = vec![];

            for pat_stack in pat_stacks {
                match self.specialize_pats(&c, pat_stack)? {
                    Some(v) => {
                        for v_ in v {
                            pats_specialized.push(v_)
                        }
                    }
                    None => (),
                }
            }

            for q_ in q_specialized {
                let next_ty = match q_.first() {
                    Some(pat) => Some(pat.ty),
                    None => None,
                };

                let witnesses = self.usefulness(next_ty, &pats_specialized, &q_)?;

                for mut witness in witnesses {
                    // Witness found, undo specialization and insert witness

                    // Specialization involves unpacking the arguments of the first
                    // column and pushing them to the front.
                    //
                    // To undo this, we simply pop the first n items of the witness,
                    // where n is the number of items in the current constructor,
                    // wrap those back into the constructor, then push that ctor
                    // back to the front of the witnesses list.

                    witness.reverse();

                    let first: Witness = match c {
                        // These do not consume any values
                        Ctor::Arbitrary => match ty {
                            SType::Primitve(Prim::Int) => Witness::Int,
                            SType::Primitve(Prim::Float) => Witness::Float,
                            SType::Primitve(Prim::String) => Witness::String,
                            _ => unreachable!(),
                        },
                        Ctor::BoolCtor(b) => Witness::Bool(b),

                        // Determine the length of the parameters, which we call n, then
                        // consume the first n items of `witness`.
                        //
                        // Wrap them in a ctor then push them back to the start of witness.
                        Ctor::AdtCtor(id, variant) => {
                            let adt_def = self.get_adt_def(&id).unwrap();
                            let var_def = adt_def.variants.get(&variant).unwrap();

                            let n = adt_def.params.len() + var_def.params.len();

                            let mut param_wits: Vec<Witness> = vec![];

                            for _ in 0..n {
                                param_wits.push(witness.pop().unwrap());
                            }

                            Witness::Adt(id, variant, param_wits)
                        }
                    };

                    witness.push(first);

                    witness.reverse();

                    ret.push(witness);
                }
            }
        }

        // Ok(witnesses)
        // Ok(res)

        Ok(ret)
    }

    // Algorithm adapted from:
    // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_build/thir/pattern/usefulness/index.html
    // Original paper:
    // http://moscova.inria.fr/~maranget/papers/warn/index.html
    fn get_witnesss(
        &self,
        ty: &TypeOrVar,
        pats: &Vec<&SPatternPos>,
    ) -> Result<Vec<Witness>, PositionRange> {
        let ty = match ty {
            TypeOrVar::Ty(t) => t,
            TypeOrVar::Var(_, pos) => {
                return Err(*pos);
            }
        };

        let mut pat_stacks: Vec<Vec<&SPatternPos>> = vec![];

        for p in pats {
            pat_stacks.push(vec![p]);
        }

        let mut res = self.usefulness(Some(*ty), &pat_stacks, &vec![&self.get_wildcard(ty)])?;

        Ok(res
            .iter_mut()
            .map(|w| match w.pop() {
                Some(w) => w,
                _ => unreachable!("Got witness with zero elements"),
            })
            .collect())
    }

    fn convert(
        &mut self,
        expr: Expr,
        expected: TypeOrVar,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
    ) -> Option<SExpr> {
        let mut ret: SExpr = vec![];

        let mut prev_locals = prev_locals.clone();
        let mut locals = locals.clone();

        let last_idx = expr.len() - 1;

        let mut i = 0;

        for e in expr {
            let ty = if i == last_idx {
                // we only require the final item has the expected type
                expected
            } else {
                TypeOrVar::Ty(SType::Top)
            };

            let converted = self.convert_stat_expr(e, ty, &prev_locals, &locals, fns, adts);

            match converted {
                Some(c) => {
                    match c.1 {
                        Some((p, l)) => {
                            (prev_locals, locals) = (p, l);
                        }
                        None => {}
                    };
                    ret.push(c.0)
                }
                None => {}
            }

            i += 1;
        }

        Some(ret)
    }

    // Return spec:
    // Option<Converted expression, Option<More prev locals, more locals>>
    // Outer option is Some() when conversion successful.
    // Inner option is Some() when new locals were added.
    fn convert_stat_expr(
        &mut self,
        e: StatExprPos,
        expected: TypeOrVar,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
    ) -> Converted {
        let pos = e.pos;

        let mut more: Option<(LocalsMap, LocalsMap)> = None;

        let s_expr: SStatExprPos = match e.expr {
            StatExpr::Nested(e) => {
                // we want a fresh map containing just the functions and adts scanned here
                let stripped = self.scan_defs(e, TreeMap::new(), TreeMap::new());

                // now combine
                let mut fns_combined = fns.clone();
                for f in stripped.1.into_iter() {
                    fns_combined = fns_combined.insert((*f.0).clone(), *f.1)
                }

                // now combine
                let mut adts_combined = adts.clone();
                for f in stripped.2.into_iter() {
                    adts_combined = adts_combined.insert((*f.0).clone(), *f.1)
                }

                let ret = self.convert(
                    stripped.0,
                    expected,
                    &prev_locals,
                    &LocalsMap::new(),
                    &fns_combined,
                    &adts_combined,
                ); // fresh locals

                // if any functions are not converted, convert them. Technically we do not need to convert them,
                // but it's good to give the user more errors :P
                for fn_id in stripped.1.into_iter() {
                    self.transform_fn(fn_id.0, pos, &LocalsMap::new(), &stripped.1, &stripped.2)
                }

                // if the return type is an ADT inside the nested block, return.
                let r = self.resolve_type(expected);

                match r {
                    TypeOrVar::Ty(SType::UserType(v)) => {
                        // If it was discovered in this block. Note that this only contains
                        // outer definitions in this block (does not contain defns in any
                        // nested blocks), but inductively, this guarantees that any returned ADT
                        // is visible from the outside block.
                        let name = self.id_map.get(&v).unwrap().clone();
                        let id = stripped.2.get(&name);
                        match id {
                            Some(id) => {
                                let adt_def = self.adt_defs.get(id).unwrap();
                                self.type_errors.push(TypeError::InvalidBlockRetError(
                                    name,
                                    adt_def.name_pos,
                                    pos,
                                ))
                            }
                            None => (),
                        }
                    }
                    _ => (),
                }

                SStatExprPos {
                    expr: SStatExpr::Nested(ret?),
                    pos,
                }
            }

            StatExpr::FunDefn(_) => SStatExprPos { expr: Dummy, pos },
            StatExpr::Variable(nme) => {
                // not yet implemented
                if !nme.scopes.is_empty() {
                    unimplemented!();
                }

                // 1. Check if in locals map
                // 2. Get local
                let local = match get_local(&nme.name, prev_locals, locals) {
                    Some(l) => l,
                    None => {
                        self.name_errors
                            .push(AnalysisError::LocalNotFoundError(nme.name.to_string(), pos));
                        return None;
                    }
                };

                // Get type
                let mut ty = self.resolve_type(local.1);

                let mut s_members: Vec<Identifier> = vec![];

                // For each xk in  first.x1.x2...xn, resolve type of each xk sequentially

                for (member, pos) in nme.members {
                    match ty {
                        TypeOrVar::Ty(SType::UserType(id)) => {
                            // get adt type
                            let adt_def = self.adt_defs.get(&id).unwrap();
                            // get member id
                            let member_id = *match adt_def.name_map.get(&member) {
                                Some(id) => id,
                                None => {
                                    self.name_errors.push(AnalysisError::NoMemberError(
                                        self.type_to_string(&ty),
                                        member,
                                        pos,
                                    ));
                                    return None;
                                }
                            };

                            // get member defn
                            let member_pd =
                                adt_def.params.iter().find(|p| p.name == member_id).unwrap();

                            // set type to this new member definition
                            ty = member_pd.ty;

                            // push id
                            s_members.push(member_id);
                        }
                        TypeOrVar::Ty(SType::Primitve(_)) => {
                            self.name_errors.push(AnalysisError::NoMemberError(
                                self.type_to_string(&ty),
                                member,
                                pos,
                            ));
                            return None;
                        }
                        TypeOrVar::Ty(SType::Top) => {
                            // ignore
                            return None;
                        }
                        TypeOrVar::Var(_, _) => {
                            self.type_errors.push(TypeError::TypeNeededError(pos));
                            return None;
                        }
                    }
                }

                let e = SStatExpr::Variable(local.0, s_members);

                self.add_constraint(e, expected, ty, pos)?
            }
            StatExpr::Call(qn, args) => {
                // get id, then def
                let fun_id = *match fns.get(&qn.name) {
                    Some(id) => id,
                    None => {
                        self.name_errors
                            .push(AnalysisError::FnNotFoundError(qn.name, pos));
                        return None;
                    }
                };

                let fun_def = match self.get_fun_def(&fun_id) {
                    Some(f) => f,
                    None => {
                        self.name_errors
                            .push(AnalysisError::FnNotFoundError(qn.name, pos));
                        return None;
                    }
                };

                // self.print_type(&self.resolve_type(ret_type));

                let mut types: Vec<TypeOrVar> = vec![];

                for p in &fun_def.params {
                    types.push(p.1.ty);
                }

                let ty_ = fun_def.ty.clone();
                let ret_type = self.resolve_type(ty_);
                // self.print_type(&ret_type);

                let transformed_args =
                    self.convert_args(args, &types, &qn, e.pos, &prev_locals, &locals, fns, adts);

                let e = SStatExpr::Call(fun_id, transformed_args?);
                // add type constraint
                let ret = self.add_constraint(e, expected, ret_type, pos);

                // transform function
                self.transform_fn(&qn.name, pos, &prev_locals, fns, adts);

                // println!("Ret type:");
                // self.print_type(&self.resolve_type(ret_type));
                // println!("First arg type:")
                // self.print_type(&self.resolve_type(func.ty));

                ret?
            }
            StatExpr::Ctor(qn, args) => {
                // NOTE: Adt() actually calls Adt::Base(). We need to handle this.

                // no support for importing scopes yet
                let (adt_def, ctor) = self.find_ctor(&qn, adts, true)?;

                let adt_id = adt_def.name;
                let ctor_id = ctor.name;

                // check args
                let mut types: Vec<TypeOrVar> = vec![];

                // 1. build types
                for p in &adt_def.params {
                    types.push(p.ty);
                }

                for p in &ctor.params {
                    types.push(p.ty);
                }

                // 2. convert args
                let transformed_args =
                    self.convert_args(args, &types, &qn, e.pos, &prev_locals, &locals, fns, adts);

                // 3. check type
                let ctor_type = TypeOrVar::Ty(SType::UserType(adt_id));

                match transformed_args {
                    Some(args) => {
                        let expr = SStatExpr::Ctor(adt_id, ctor_id, args);
                        self.add_constraint(expr, expected, ctor_type, e.pos)?
                    }
                    None => {
                        // add type constraint to help further type checking
                        self.add_type_constraint(expected, ctor_type, e.pos);
                        return None;
                    }
                }
            }
            StatExpr::Ite(cond, if_e, elif_e, else_e) => {
                let bool_prim = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                let cond_conv =
                    self.convert_stat_expr(*cond, bool_prim, prev_locals, locals, fns, adts);

                let if_e_conv =
                    self.convert_stat_expr(*if_e, expected, prev_locals, locals, fns, adts);

                let mut elif_e_conv_: Vec<(Converted, Converted)> = Vec::new();

                for e in elif_e {
                    elif_e_conv_.push((
                        self.convert_stat_expr(*e.0, bool_prim, prev_locals, locals, fns, adts),
                        self.convert_stat_expr(*e.1, expected, prev_locals, locals, fns, adts),
                    ))
                }

                let else_e_conv = match else_e {
                    Some(e) => Some(Box::new(
                        self.convert_stat_expr(*e, expected, prev_locals, locals, fns, adts)?
                            .0,
                    )),
                    None => Some(Box::new(
                        self.convert_stat_expr(
                            StatExprPos {
                                expr: StatExpr::UnitLit,
                                pos,
                            }, // implicit unit literal for else branch
                            expected,
                            prev_locals,
                            locals,
                            fns,
                            adts,
                        )?
                        .0,
                    )),
                };

                // Only check the option values now to maximise the number of errors outputted at once

                let mut elif_e_conv: Vec<(Box<SStatExprPos>, Box<SStatExprPos>)> = Vec::new();

                for e in elif_e_conv_ {
                    elif_e_conv.push((Box::new(e.0?.0), Box::new(e.1?.0)))
                }

                SStatExprPos {
                    expr: SStatExpr::Ite(
                        Box::new(cond_conv?.0),
                        Box::new(if_e_conv?.0),
                        elif_e_conv,
                        else_e_conv,
                    ),
                    pos,
                }
            }
            StatExpr::Match(scrut, cases) => {
                // Find scrut type. Must be known
                let scrut_ty = self.fresh_type_var(scrut.pos);

                let scrut_pos = scrut.pos;

                // Convert.
                let s_scrut =
                    self.convert_stat_expr(*scrut, scrut_ty, prev_locals, locals, fns, adts);

                let ty = self.resolve_type(scrut_ty);

                if is_type_var(&ty) {
                    self.type_errors.push(TypeError::TypeNeededError(scrut_pos));
                }

                let mut success = true;
                let mut s_cases: Vec<SMatchCase> = vec![];

                // for each matchcase, convert the pattern
                for case in cases {
                    // convert
                    let maybe = self.check_and_bind(adts, case.pat, ty, &locals);
                    if maybe.is_none() {
                        success = false;
                        continue;
                    }
                    // evaluate body using new locals
                    let (s_pat, more_locals) = maybe.unwrap();
                    let s_body = self.convert_stat_expr(
                        case.body,
                        expected,
                        prev_locals,
                        &more_locals,
                        fns,
                        adts,
                    );

                    if s_body.is_none() {
                        success = false;
                        continue;
                    }

                    s_cases.push(SMatchCase {
                        pat: s_pat,
                        body: s_body.unwrap().0,
                    });
                }

                if !success {
                    return None;
                }

                let mut pats: Vec<&SPatternPos> = vec![];

                for case in &s_cases {
                    pats.push(&case.pat);
                }

                let witnesses = self.get_witnesss(&ty, &pats);

                match witnesses {
                    Ok(res) => {
                        if !res.is_empty() {
                            self.name_errors.push(AnalysisError::MatchNotExhaustiveErr(
                                res.iter().map(|w| self.witness_to_string(w)).collect(),
                                scrut_pos,
                            ));
                            success = false
                        }
                    }
                    Err(pos) => {
                        self.type_errors.push(TypeError::TypeNeededError(pos));
                        success = false;
                    }
                }

                if success {
                    SStatExprPos {
                        expr: SStatExpr::Match(Box::new(s_scrut?.0), s_cases),
                        pos,
                    }
                } else {
                    return None;
                }
            }
            StatExpr::While(cond, body) => {
                let bool_prim = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                let cond_conv =
                    self.convert_stat_expr(*cond, bool_prim, prev_locals, locals, fns, adts);

                let body_conv = self.convert_stat_expr(
                    *body,
                    TypeOrVar::Ty(SType::Top),
                    prev_locals,
                    locals,
                    fns,
                    adts,
                );

                let e = SStatExpr::While(Box::new(cond_conv?.0), Box::new(body_conv?.0));
                // while expression has type unit
                self.add_constraint(e, expected, TypeOrVar::Ty(SType::Primitve(Prim::Bool)), pos)?
            }
            StatExpr::IntLit(v) => self.add_constraint(
                SStatExpr::IntLit(v),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Int)),
                pos,
            )?,
            StatExpr::FloatLit(v) => self.add_constraint(
                SStatExpr::FloatLit(v),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Float)),
                pos,
            )?,
            StatExpr::StringLit(v) => self.add_constraint(
                SStatExpr::StringLit(v.to_string()),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::String)),
                pos,
            )?,
            StatExpr::BoolLit(v) => self.add_constraint(
                SStatExpr::BoolLit(v),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Bool)),
                pos,
            )?,
            StatExpr::UnitLit => self.add_constraint(
                SStatExpr::UnitLit,
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Unit)),
                pos,
            )?,
            StatExpr::Infix(op, e1, e2) => match op {
                Op::Add | Op::Minus | Op::Times | Op::Divide | Op::Mod => {
                    let converted =
                        self.convert_maybe_float(*e1, *e2, &prev_locals, &locals, fns, adts, true);

                    let float_prim = TypeOrVar::Ty(SType::Primitve(Prim::Float));
                    let int_prim = TypeOrVar::Ty(SType::Primitve(Prim::Int));
                    let top = TypeOrVar::Ty(SType::Top);

                    match converted {
                        Ok(e) => {
                            let expr = Infix(op, Box::new(e.0), Box::new(e.1));
                            // is float
                            if e.2 {
                                self.add_constraint(expr, expected, float_prim, pos)?
                            } else if e.3 {
                                self.add_constraint(expr, expected, top, pos)?
                            } else {
                                self.add_constraint(expr, expected, int_prim, pos)?
                            }
                        }
                        Err(_) => {
                            // self.add_constraint(expected, TypeOrVar::Ty(SType::Top), pos);
                            return None;
                        }
                    }
                }
                Op::Not => unreachable!(),
                Op::Or | Op::And | Op::Lt | Op::Lte | Op::Gt | Op::Gte => {
                    let converted =
                        self.convert_maybe_float(*e1, *e2, &prev_locals, &locals, fns, adts, true);

                    let bool_prim = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                    match converted {
                        Ok(e) => {
                            let top = TypeOrVar::Ty(SType::Top);
                            let expr = Infix(op, Box::new(e.0), Box::new(e.1));
                            if e.3 {
                                self.add_constraint(expr, expected, top, pos)?
                            } else {
                                self.add_constraint(expr, expected, bool_prim, pos)?
                            }
                        }
                        Err(_) => {
                            // self.add_constraint(expected, TypeOrVar::Ty(SType::Top), pos);
                            return None;
                        }
                    }
                }
                Op::Eq | Op::Neq => {
                    let e2_p = e2.pos;

                    let converted =
                        self.convert_maybe_float(*e1, *e2, &prev_locals, &locals, fns, adts, false);

                    let bool_prim = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                    match converted {
                        Ok(e) => {
                            let expr = Infix(op, Box::new(e.0), Box::new(e.1));

                            let top = TypeOrVar::Ty(SType::Top);
                            if e.3 {
                                self.add_constraint(expr, expected, top, pos)?
                            } else {
                                self.add_constraint(expr, expected, bool_prim, pos)?
                            }
                        }
                        Err(Some(e)) => {
                            // both sides must have same type
                            self.add_constraint(
                                Infix(op, Box::new(e.0), Box::new(e.1)),
                                e.2,
                                e.3,
                                e2_p,
                            )?
                        }
                        Err(None) => {
                            // self.add_constraint(expected, TypeOrVar::Ty(SType::Top), pos);
                            return None;
                        }
                    }
                }
            },
            StatExpr::Prefix(op, expr) => {
                let e_pos = expr.pos;

                // type already known for boolean expressions
                let ty = match op {
                    Op::Minus => self.fresh_type_var(e_pos),
                    Op::Not => TypeOrVar::Ty(SType::Primitve(Prim::Bool)),
                    _ => unreachable!(),
                };

                let converted = self.convert_stat_expr(*expr, ty, prev_locals, locals, fns, adts);

                let l_ty_r = self.resolve_type(ty);

                // need to know type of expr
                if is_type_var(&l_ty_r) {
                    self.type_errors.push(TypeError::TypeNeededError(e_pos));
                    return None;
                }

                // check type for minus operation
                if matches!(op, Op::Minus) && !matches_numerical(&l_ty_r) {
                    self.type_errors.push(TypeError::InvalidOperandError(e_pos));
                    return None;
                }

                let expr = Prefix(op, Box::new(converted?.0));

                self.add_constraint(expr, expected, ty, pos)?
            }
            StatExpr::Let(pd, expr) => {
                // Check for name conflicts. Allow variable shadowing
                // If there is a name conflict, we try to continue using the new
                // definition of the variable to minimise errors for the user.

                let maybe_local = locals.get(&pd.name);

                if locals.get(&pd.name).is_some() {
                    let og_pos = self.id_pos_map.get(&maybe_local.unwrap().0).unwrap();

                    self.name_errors.push(AnalysisError::VariableRedefError(
                        pd.name.to_string(),
                        pd.nme_pos,
                        *og_pos,
                    ));
                }

                // get type ID
                let ty = self.transform_type(&pd.ty, pd.nme_pos, &adts);

                // eval body
                let body = self.convert_stat_expr(*expr, ty, prev_locals, locals, fns, adts);

                // get fresh local
                let new_local = self.fresh_id(pd.name.to_string(), pd.nme_pos);

                // add to both maps (prev locals is used to pass to nested scopes for variable shadowing)
                let more_prev_locals = prev_locals.insert(pd.name.to_string(), (new_local, ty));
                let more_locals = locals.insert(pd.name, (new_local, ty));

                more = Some((more_prev_locals, more_locals));

                self.add_type_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Unit)), pos);

                SStatExprPos {
                    expr: SStatExpr::Let(
                        SParamDef {
                            name: new_local,
                            ty: ty,
                            pos: pd.nme_pos,
                        },
                        Box::new(body?.0),
                    ),
                    pos,
                }
            }
            StatExpr::AssignmentOp(op, lhs, rhs) => {
                let l_pos = lhs.pos;

                // LHS must be a variable (for now)
                if !matches!(lhs.expr, StatExpr::Variable(_)) {
                    self.type_errors.push(TypeError::NotAssignableError(l_pos));
                    return None;
                };

                let ty = self.fresh_type_var(l_pos);

                let lhs = self.convert_stat_expr(*lhs, ty, prev_locals, locals, fns, adts);

                let l_ty_r = self.resolve_type(ty);

                // need to know type of LHS
                if is_type_var(&l_ty_r) {
                    self.type_errors.push(TypeError::TypeNeededError(l_pos));
                    return None;
                }

                match op {
                    AssignOp::AddEq
                    | AssignOp::SubEq
                    | AssignOp::TimesEq
                    | AssignOp::DivEq
                    | AssignOp::ModEq => {
                        // must be numeric
                        if !matches_number(&l_ty_r) {
                            self.type_errors.push(TypeError::InvalidOperandError(l_pos));
                            return None;
                        }
                    }
                    AssignOp::OrEq | AssignOp::AndEq => {
                        // must be bool
                        if !matches_bool(&l_ty_r) {
                            self.type_errors.push(TypeError::InvalidOperandError(l_pos));
                            return None;
                        }
                    }
                    AssignOp::Assign => (),
                }

                // LHS and RHS must be the same type, but RHS can implicitly convert.
                let rhs = self.convert_stat_expr(*rhs, l_ty_r, prev_locals, locals, fns, adts);

                let expr = SStatExpr::AssignmentOp(op, Box::new(lhs?.0), Box::new(rhs?.0));

                self.add_constraint(expr, expected, ty, pos)?
            }
            StatExpr::AdtDefn(_) => unreachable!(),
            StatExpr::FunDefId(id, _) => {
                // capture locals

                let retrieved = self.fun_defs.remove(&id).unwrap();

                let new = TmpFunDef {
                    name_str: retrieved.name_str,
                    name: retrieved.name,
                    name_pos: retrieved.name_pos,
                    ty: retrieved.ty,
                    params: retrieved.params,
                    captured_locals: Some(locals.clone()),
                    body: retrieved.body,
                };

                self.fun_defs.insert(id, new);

                self.add_type_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Unit)), pos);

                SStatExprPos { expr: Dummy, pos }
            }
        };

        Some((s_expr, more))
    }
}

pub fn init_analyzer() -> Analyzer {
    Analyzer {
        fun_defs: HashMap::new(),
        adt_defs: HashMap::new(),
        id_map: HashMap::new(),
        id_pos_map: HashMap::new(),
        local_id: 0,
        unions: union_find_int::new(),
        type_map: HashMap::new(),
        type_map_all: HashMap::new(),
        name_errors: Vec::new(),
        type_errors: Vec::new(),
    }
}
