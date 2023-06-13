use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use crate::analysis::symbolic_ast;
use crate::parsing::ast::*;
use crate::parsing::position::*;

use crate::analysis::symbolic_ast::SExpr::*;
use crate::analysis::symbolic_ast::*;

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

// for storing nominal exprs pending conversion
enum NSExprPos {
    N(ExprPos),
    S(SExprPos),
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

    // Useful to have
    id_map: HashMap<Identifier, String>,
    id_pos_map: HashMap<Identifier, PositionRange>,
    local_id: u64,

    // Type analysis part. We use a union-find data structure
    // to compactly store type var equality.
    unions: UnionFindInt,
    type_map: HashMap<Identifier, SType>,
    type_map_all: HashMap<Identifier, TypeOrVar>,

    // Errors, add all of them and report the errors all at once
    pub name_errors: Vec<AnalysisError>,
    pub type_errors: Vec<TypeError>,
}

pub enum TypeError {
    TypeNeededError(PositionRange),
    InvalidOperandError(PositionRange),
    TypeMismatch(String, String, PositionRange), // expected, actual, location
}
pub enum AnalysisError {
    LocalNotFoundError(String, PositionRange),
    FnNotFoundError(String, PositionRange),
    TooManyArgsError(String, PositionRange), // fn name, fn pos, position of excess args
    TooFewArgsError(String, PositionRange),  // fn name, fn pos, position of excess args
    NoMemberError(String, String, PositionRange), // type name, member, pos
    TypeNotFound(String, PositionRange),
    NameAlreadyUsedError(String, PositionRange, PositionRange), // name, offending position, original position
    VariableRedefError(String, PositionRange, PositionRange), // name, offending position, original position
    DuplicateMemberError(String, String, PositionRange, PositionRange), // name, offending position, original position
    DuplicateVariantError(String, String, PositionRange, PositionRange), // name, offending position, original position
    InvalidCtorError(PositionRange),
    AdtNotFoundError(String, PositionRange),
    AdtVariantNotFoundError(String, String, PositionRange), // adt name, adt variant name, position
    AdtNoBaseError(String, PositionRange, PositionRange), // adt name, error position, suggested position to insert Base
}

fn matches_float(ty: TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Ty(SType::Primitve(Prim::Float)))
}
fn matches_int(ty: TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Ty(SType::Primitve(Prim::Int)))
}
fn matches_bool(ty: TypeOrVar) -> bool {
    matches!(ty, TypeOrVar::Ty(SType::Primitve(Prim::Bool)))
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

    fn stype_str(&self, t: &SType) -> String {
        match t {
            SType::Primitve(p) => p.to_string(),
            SType::UserType(id) => self.id_map.get(id).unwrap().to_string(),
            SType::Top => "<Top>".to_string(),
        }
    }

    fn add_constraint_pos(
        &mut self,
        expr: SExprPos,
        expected: TypeOrVar,
        actual: TypeOrVar,
    ) -> Option<SExprPos> {
        self.add_constraint(expr.expr, expected, actual, expr.pos)
    }
    
    // returns converted expression, type of new expression
    fn implicit_convert(&self, expr: SExprPos, expected: TypeOrVar, actual: TypeOrVar) -> (SExprPos, TypeOrVar) {
        use crate::parsing::tokens::Prim::*;

        let pos = expr.pos;

        match (expected, actual) {
            (TypeOrVar::Ty(SType::Primitve(p1)), TypeOrVar::Ty(SType::Primitve(p2))) => {
                let new_expr = match (p1, p2) {
                    (Float, Bool) => BoolToFloat(Box::new(expr)),
                    (Float, Int) => IntToFloat(Box::new(expr)),
                    (Int, Bool) => BoolToInt(Box::new(expr)),
                    (Float, Bool) => FloatToBool(Box::new(expr)),
                    (Int, Bool) => IntToBool(Box::new(expr)),
                    _ => return (expr, actual)
                };
                (SExprPos {
                    expr: new_expr,
                    pos,
                }, expected)
            }
            _ => (expr, actual)
        }
    }

    // Also handles implicit conversions.
    fn add_constraint(
        &mut self,
        expr: SExpr,
        expected: TypeOrVar,
        actual: TypeOrVar,
        pos: PositionRange,
    ) -> Option<SExprPos> {
        // useful imports
        use crate::analysis::symbolic_ast::SType::*;

        // resolve types
        let r_expected = self.resolve_type(expected);
        let r_actual = self.resolve_type(actual);

        let res = self.implicit_convert(SExprPos { expr, pos } , r_expected, r_actual);

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
        let dummy_expr = SExprPos {
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

        let transformed = self.convert(
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
            body: NSExprPos::S(transformed_),
        };

        self.fun_defs.insert(fun_id, new);
    }

    // Adds extra functions and adts to the map in the current scope
    fn scan_defs(&mut self, e: ExprPos, fns: FnMap, adts: AdtMap) -> (ExprPos, FnMap, AdtMap) {
        let (fns_, adts_) = self.scan_names(&e, fns, adts);
        (self.scan_defs_rec(e, &fns_, &adts_), fns_, adts_)
    }

    fn scan_names(&mut self, e: &ExprPos, fns: FnMap, adts: AdtMap) -> (FnMap, AdtMap) {
        match &e.expr {
            Expr::AdtDefn(defn, next) => {
                if adts.contains_key(&defn.name) {
                    // error
                    let id = adts.get(&defn.name).unwrap();
                    let og_pos = self.id_pos_map.get(&id).unwrap();

                    self.name_errors.push(AnalysisError::NameAlreadyUsedError(
                        defn.name.to_string(),
                        defn.name_pos,
                        *og_pos,
                    ));

                    self.scan_names(&next, fns, adts)
                } else {
                    let id = self.fresh_id(defn.name.clone(), defn.name_pos);
                    let more = adts.insert(defn.name.clone(), id);

                    self.scan_names(&next, fns, more)
                }
            }
            Expr::FunDefn(defn, next) => {
                if fns.contains_key(&defn.name) {
                    // error
                    let id = fns.get(&defn.name).unwrap();
                    let og_pos = self.id_pos_map.get(&id).unwrap();

                    self.name_errors.push(AnalysisError::NameAlreadyUsedError(
                        defn.name.to_string(),
                        defn.name_pos,
                        *og_pos,
                    ));

                    self.scan_names(&next, fns, adts)
                } else {
                    let id = self.fresh_id(defn.name.clone(), defn.name_pos);
                    let more = fns.insert(defn.name.clone(), id);

                    self.scan_names(&next, more, adts)
                }
            }
            Expr::Sequence(_, e2) => self.scan_names(&e2, fns, adts),
            Expr::Let(_, _, after) => self.scan_names(&after, fns, adts),
            _ => (fns, adts),
        }
    }

    fn convert_adt(&mut self, defn: AdtDef, adts: &AdtMap) -> SAdtDef {
        let id = self.fresh_id(defn.name.clone(), defn.name_pos);

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

        let mut s_variants: HashMap<Identifier, SAdtVariant> = HashMap::new();

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
        }
    }

    // strips away all adt definitions, replaces function definitions with IDs
    fn scan_defs_rec(&mut self, e: ExprPos, fns: &FnMap, adts: &AdtMap) -> ExprPos {
        match e.expr {
            Expr::AdtDefn(defn, next) => {
                let id = *adts.get(&defn.name).unwrap();

                if !self.adt_defs.contains_key(&id) {
                    let converted = self.convert_adt(defn, adts);
                    self.adt_defs.insert(id, converted);
                }

                self.scan_defs_rec(*next, fns, adts)
            }
            Expr::FunDefn(defn, next) => {
                let id = *fns.get(&defn.name).unwrap();

                // if name already exists, this error was already caught before. just continue
                if self.fun_defs.contains_key(&id) {
                    self.scan_defs_rec(*next, fns, adts)
                } else {
                    let new_params = defn
                        .params
                        .iter()
                        .map(|p| {
                            (
                                p.name.to_string(),
                                SParamDef {
                                    name: self.fresh_id(p.name.to_string(), p.nme_pos),
                                    ty: self.transform_type(&p.ty, p.nme_pos, &adts),
                                    pos: p.nme_pos,
                                },
                            )
                        })
                        .collect();

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

                    let ret = self.scan_defs_rec(*next, fns, adts);

                    ExprPos {
                        expr: Expr::FunDefId(id, name_pos, Box::new(ret)),
                        pos: e.pos,
                    }
                }
            }
            Expr::Sequence(e1, e2) => {
                let ret = self.scan_defs_rec(*e2, fns, adts);
                ExprPos {
                    expr: Expr::Sequence(e1, Box::new(ret)),
                    pos: e.pos,
                }
            }
            Expr::Let(pd, expr, after) => {
                let ret = self.scan_defs_rec(*after, fns, adts);
                ExprPos {
                    expr: Expr::Let(pd, expr, Box::new(ret)),
                    pos: e.pos,
                }
            }
            _ => e,
        }
    }

    fn convert_args(
        &mut self,
        args: Vec<ExprPos>,
        types: &Vec<TypeOrVar>,
        qn: &QualifiedName,
        pos: PositionRange,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
    ) -> Option<Vec<SExprPos>> {
        let args_len = types.len();

        // check args length correct
        if args.len() > args_len {
            self.name_errors
                .push(AnalysisError::TooManyArgsError(qn.name.clone(), pos));
            return None;
        }
        if args.len() < args_len {
            self.name_errors
                .push(AnalysisError::TooFewArgsError(qn.name.clone(), pos));
            return None;
        }

        // type check args
        let mut transformed_args: Vec<Option<SExprPos>> = Vec::new();

        for (arg, ty) in zip(args, types) {
            // type checking occurs here
            transformed_args.push(self.convert(arg, *ty, prev_locals, locals, fns, adts));
        }

        // transform options into exprs
        let mut transformed_final: Vec<SExprPos> = Vec::new();

        for e_ in transformed_args {
            transformed_final.push(e_?)
        }

        Some(transformed_final)
    }

    pub fn convert_top(&mut self, e: ExprPos) -> Option<SExprPos> {
        // scan definitions
        let stripped = self.scan_defs(e, TreeMap::new(), TreeMap::new());
        let pos = stripped.0.pos;
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
    fn convert_maybe_float(
        &mut self,
        e1: ExprPos,
        e2: ExprPos,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
        error_on_neq: bool,
    ) -> Result<(SExprPos, SExprPos, bool, bool), Option<(SExprPos, SExprPos, TypeOrVar, TypeOrVar)>>
    {
        let left_t = self.fresh_type_var(e1.pos);
        let right_t = self.fresh_type_var(e2.pos);

        let e1_p = e1.pos;
        let e2_p = e2.pos;

        let s_e1_ = self.convert(e1, left_t, prev_locals, locals, fns, adts);
        let s_e2_ = self.convert(e2, right_t, prev_locals, locals, fns, adts);

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
            return Ok((s_e1, s_e2, false, true));
        }

        let mut fail = false;

        // types must be known
        if matches!(left_r, TypeOrVar::Var(_, _)) {
            self.type_errors.push(TypeError::TypeNeededError(e1_p));
            fail = true;
        } else if !matches_float(left_r) && !matches_int(left_r) && !matches_bool(left_r) {
            // both must be ints, floats or bools
            if error_on_neq {
                self.type_errors.push(TypeError::InvalidOperandError(e1_p));
            }

            fail = true;
        }

        if matches!(right_r, TypeOrVar::Var(_, _)) {
            self.type_errors.push(TypeError::TypeNeededError(e2_p));
            fail = true;
        } else if !matches_float(right_r) && !matches_int(right_r) && !matches_bool(right_r) {
            if error_on_neq {
                self.type_errors.push(TypeError::InvalidOperandError(e2_p));
            }
            fail = true;
        }

        if fail {
            return Err(Some((s_e1, s_e2, left_r, right_r)));
        }

        if matches_float(left_r) || matches_float(right_r) {
            let float_prim = TypeOrVar::Ty(SType::Primitve(Prim::Float));
            let e1 = self.add_constraint_pos(s_e1, float_prim, left_r).unwrap();
            let e2 = self.add_constraint_pos(s_e2, float_prim, right_r).unwrap();

            Ok((e1, e2, true, false))

            /*
            fn implicit_float(s_e: SExprPos, ty: TypeOrVar, r: TyConstraintRes) -> SExprPos {
                let pos = s_e.pos;

                // implicit conversions
                if matches!(r, TyConstraintRes::ImplicitConv) {
                    if matches_int(ty) {
                        SExprPos {
                            expr: IntToFloat(Box::new(s_e)),
                            pos,
                        }
                    } else {
                        SExprPos {
                            expr: BoolToFloat(Box::new(s_e)),
                            pos,
                        }
                    }
                } else {
                    //
                    s_e
                }
            }
            */
        } else {
            // both are integers
            let int_prim = TypeOrVar::Ty(SType::Primitve(Prim::Int));
            let e1 = self.add_constraint_pos(s_e1, int_prim, left_r).unwrap();
            let e2 = self.add_constraint_pos(s_e2, int_prim, right_r).unwrap();

            /*
            fn implicit_int(s_e: SExprPos, r: TyConstraintRes) -> SExprPos {
                let pos = s_e.pos;

                // implicit conversions
                if matches!(r, TyConstraintRes::ImplicitConv) {
                    SExprPos {
                        expr: BoolToInt(Box::new(s_e)),
                        pos,
                    }
                } else {
                    //
                    s_e
                }
            }
            */

            Ok((e1, e2, false, false))
        }
    }

    fn convert(
        &mut self,
        e: ExprPos,
        expected: TypeOrVar,
        prev_locals: &LocalsMap,
        locals: &LocalsMap,
        fns: &FnMap,
        adts: &AdtMap,
    ) -> Option<SExprPos> {
        pub fn get_local(
            name: &String,
            prev_locals: &LocalsMap,
            locals: &LocalsMap,
        ) -> Option<Local> {
            match locals.get(name) {
                Some(t) => Some(*t),
                None => match prev_locals.get(name) {
                    Some(t) => Some(*t),
                    None => None,
                },
            }
        }

        let pos = e.pos;

        let s_expr: SExprPos = match e.expr {
            Expr::Nested(e) => {
                // we want a fresh map containing just the functions scanned here
                let stripped = self.scan_defs(*e, TreeMap::new(), adts.clone());

                // now combine
                let mut fns_combined = fns.clone();
                for f in stripped.1.into_iter() {
                    fns_combined = fns_combined.insert((*f.0).clone(), *f.1)
                }

                let ret = self.convert(
                    stripped.0,
                    expected,
                    prev_locals,
                    &LocalsMap::new(),
                    &stripped.1,
                    &stripped.2,
                ); // fresh locals

                // if any functions are not converted, convert them. Technically we do not need to convert them,
                // but it's good to give the user more errors :P
                for fn_id in stripped.1.into_iter() {
                    self.transform_fn(fn_id.0, pos, &LocalsMap::new(), &stripped.1, &stripped.2)
                };
                ret?
            }

            Expr::FunDefn(_, after) => {
                self.convert(*after, expected, prev_locals, locals, fns, adts)?
            }
            Expr::Variable(nme) => {
                // not yet implemented
                if !nme.scopes.is_empty() {
                    todo!();
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

                let e = SExpr::Variable(local.0, s_members);

                self.add_constraint(e, expected, ty, pos)?
            }
            Expr::Call(qn, args) => {
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
                    self.convert_args(args, &types, &qn, e.pos, prev_locals, locals, fns, adts);

                let e = SExpr::Call(fun_id, transformed_args?);
                // add type constraint
                let ret = self.add_constraint(e, expected, ret_type, pos);

                // transform function
                self.transform_fn(&qn.name, pos, prev_locals, fns, adts);

                // println!("Ret type:");
                // self.print_type(&self.resolve_type(ret_type));
                // println!("First arg type:")
                // self.print_type(&self.resolve_type(func.ty));

                ret?
            }
            Expr::Ctor(qn, args) => {
                // NOTE: Adt() actually calls Adt::Base(). We need to handle this.

                // no support for importing scopes yet
                if qn.scopes.len() >= 2 {
                    todo!();
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
                        // error
                        self.name_errors
                            .push(AnalysisError::AdtNotFoundError(adt_name.0, adt_name.1));
                        return None;
                    }
                };

                let adt_def = self.adt_defs.get(&adt_id).unwrap();

                // resolve ctor
                let ctor_id = *match adt_def.variant_name_map.get(&ctor_name.0) {
                    Some(id) => id,
                    None => {
                        // error

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
                        return None;
                    }
                };

                let ctor = adt_def.variants.get(&ctor_id).unwrap();

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
                    self.convert_args(args, &types, &qn, e.pos, prev_locals, locals, fns, adts);

                // 3. check type
                let ctor_type = TypeOrVar::Ty(SType::UserType(adt_id));

                let expr = SExpr::Ctor(adt_id, ctor_id, transformed_args?);

                self.add_constraint(expr, expected, ctor_type, e.pos)?
            }
            Expr::Sequence(e1, e2) => {
                let e1 = self.convert(
                    *e1,
                    TypeOrVar::Ty(SType::Top),
                    prev_locals,
                    locals,
                    fns,
                    adts,
                );
                let e2 = self.convert(*e2, expected, prev_locals, locals, fns, adts)?;

                match e1 {
                    Some(e) => SExprPos {
                        expr: SExpr::Sequence(Box::new(e), Box::new(e2)),
                        pos,
                    },
                    None => return None,
                }
            }
            Expr::Ite(cond, if_e, elif_e, else_e) => {
                let bool_prim = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                let cond_conv = self.convert(*cond, bool_prim, prev_locals, locals, fns, adts);

                let if_e_conv = self.convert(*if_e, expected, prev_locals, locals, fns, adts);

                let mut elif_e_conv_: Vec<(Option<SExprPos>, Option<SExprPos>)> = Vec::new();

                for e in elif_e {
                    elif_e_conv_.push((
                        self.convert(*e.0, bool_prim, prev_locals, locals, fns, adts),
                        self.convert(*e.1, expected, prev_locals, locals, fns, adts),
                    ))
                }

                let else_e_conv = match else_e {
                    Some(e) => Some(Box::new(self.convert(
                        *e,
                        expected,
                        prev_locals,
                        locals,
                        fns,
                        adts,
                    )?)),
                    None => None,
                };

                // Only check the option values now to maximise the number of errors outputted at once

                let mut elif_e_conv: Vec<(Box<SExprPos>, Box<SExprPos>)> = Vec::new();

                for e in elif_e_conv_ {
                    elif_e_conv.push((Box::new(e.0?), Box::new(e.1?)))
                }

                SExprPos {
                    expr: SExpr::Ite(
                        Box::new(cond_conv?),
                        Box::new(if_e_conv?),
                        elif_e_conv,
                        else_e_conv,
                    ),
                    pos,
                }
            }
            Expr::Match(_, _) => todo!(),
            Expr::While(cond, body) => {
                let bool_prim = TypeOrVar::Ty(SType::Primitve(Prim::Bool));

                let cond_conv = self.convert(*cond, bool_prim, prev_locals, locals, fns, adts);

                let body_conv = self.convert(
                    *body,
                    TypeOrVar::Ty(SType::Top),
                    prev_locals,
                    locals,
                    fns,
                    adts,
                );

                let e = SExpr::While(Box::new(cond_conv?), Box::new(body_conv?));
                // while expression has type unit
                self.add_constraint(e, expected, TypeOrVar::Ty(SType::Primitve(Prim::Bool)), pos)?
            }
            Expr::IntLit(v) => self.add_constraint(
                SExpr::IntLit(v),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Int)),
                pos,
            )?,
            Expr::FloatLit(v) => self.add_constraint(
                SExpr::FloatLit(v),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Float)),
                pos,
            )?,
            Expr::StringLit(v) => self.add_constraint(
                SExpr::StringLit(v.to_string()),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::String)),
                pos,
            )?,
            Expr::BoolLit(v) => self.add_constraint(
                SExpr::BoolLit(v),
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Bool)),
                pos,
            )?,
            Expr::UnitLit => self.add_constraint(
                SExpr::UnitLit,
                expected,
                TypeOrVar::Ty(SType::Primitve(Prim::Unit)),
                pos,
            )?,
            Expr::Infix(op, e1, e2) => match op {
                Op::Add | Op::Minus | Op::Times | Op::Divide | Op::Mod => {
                    let converted =
                        self.convert_maybe_float(*e1, *e2, prev_locals, locals, fns, adts, true);

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
                Op::Not => todo!(),
                Op::Or | Op::And | Op::Lt | Op::Lte | Op::Gt | Op::Gte => {
                    let converted =
                        self.convert_maybe_float(*e1, *e2, prev_locals, locals, fns, adts, true);

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
                        self.convert_maybe_float(*e1, *e2, prev_locals, locals, fns, adts, false);

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
            Expr::Prefix(_, _) => todo!(),
            Expr::Let(pd, expr, after) => {
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
                let body = self.convert(*expr, ty, prev_locals, locals, fns, adts);

                // get fresh local
                let new_local = self.fresh_id(pd.name.to_string(), pd.nme_pos);

                // add to both maps (prev locals is used to pass to nested scopes for variable shadowing)
                let more_prev_locals = prev_locals.insert(pd.name.to_string(), (new_local, ty));
                let more_locals = locals.insert(pd.name, (new_local, ty));

                let after =
                    self.convert(*after, expected, &more_prev_locals, &more_locals, fns, adts)?;

                SExprPos { expr: SExpr::Let(
                    SParamDef {
                        name: new_local,
                        ty: ty,
                        pos: pd.nme_pos,
                    },
                    Box::new(body?),
                    Box::new(after),
                ), pos }
            }
            Expr::AssignmentOp(_, _, _, _) => todo!(),
            Expr::AdtDefn(_, _) => unreachable!(),
            Expr::FunDefId(id, pos, after) => {
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

                self.convert(*after, expected, prev_locals, locals, fns, adts)?
            }
        };

        Some(s_expr)
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
