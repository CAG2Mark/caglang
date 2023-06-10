use std::collections::HashMap;
use std::collections::HashSet;
use std::iter::zip;

use crate::parsing::ast::Expr::*;
use crate::parsing::ast::*;
use crate::parsing::position::*;

use crate::analysis::symbolic_ast::SExpr::*;
use crate::analysis::symbolic_ast::*;

use crate::parsing::tokens::Prim;
use crate::util::union_find_int;
use crate::util::union_find_int::UnionFindInt;

use immutable_map::map::TreeMap;

type Identifier = u64;
type Local = (Identifier, TypeOrVar);
type LocalsMap = TreeMap<String, Local>;

// for storing nominal exprs pending conversion
enum NSExprPos {
    N(ExprPos),
    S(SExprPos)
}

struct TmpFunDef {
    name_str: String,
    name: Identifier,
    name_pos: PositionRange,
    ty: TypeOrVar, 
    params: Vec<(String, SParamDef)>,
    body: NSExprPos
}

pub struct Analyzer {
    // Name analysis part
    fun_defs: HashMap<Identifier, TmpFunDef>,
    adt_defs: HashMap<Identifier, SAdtDef>,
    nme_map: HashMap<String, Identifier>,
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
    pub type_errors: Vec<TypeError>
}

pub enum TypeError {
    TypeNeededError(PositionRange),
    TypeMismatch(String, String, PositionRange), // expected, actual, location
}
pub enum AnalysisError {
    LocalNotFoundError(String, PositionRange),
    FnNotFoundError(String, PositionRange),
    TooManyArgsError(String, PositionRange), // fn name, fn pos, position of excess args
    TooFewArgsError(String, PositionRange), // fn name, fn pos, position of excess args
    NoMemberError(String, PositionRange),
    TypeNotFound(String, PositionRange),
    VariableRedefError(String, PositionRange, PositionRange) // name, offending position, original position
}

impl Analyzer {
    fn print_type(&self, ty: &TypeOrVar) {
        let msg = match ty {
            TypeOrVar::Ty(t) => match t {
                SType::Top => println!("Top"),
                SType::Primitve(p) => println!("{}", p),
                SType::UserType(t) => println!("{}", self.id_map.get(t).unwrap()),
            },
            TypeOrVar::Var(v, _) => println!("TypeVar({})",v),
        };
    }

    fn get_adt_def(&self, id: &Identifier) -> Option<&SAdtDef> {
        self.adt_defs.get(id)
    }

    fn get_fun_def(&self, id: &Identifier) -> Option<&TmpFunDef> {
        self.fun_defs.get(id)
    }

    fn fresh_id(&mut self, name: String, pos: PositionRange) -> u64 {
        self.id_map.insert(self.local_id, name.to_string());
        self.nme_map.insert(name.to_string(), self.local_id);
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
            },
        }
    }

    fn stype_str(&self, t: &SType) -> String {
        match t {
            SType::Primitve(p) => p.to_string(),
            SType::UserType(id) => self.id_map.get(id).unwrap().to_string(),
            SType::Top => "<Top>".to_string()
        }
    }

    fn add_constraint(&mut self, expected: TypeOrVar, actual: TypeOrVar, pos: PositionRange) {
        // println!("Constraints added:");
        // self.print_type(&expected);
        // self.print_type(&actual);
        // println!("Resolved to:");
        // find roots
        let r_expected = self.resolve_type(expected);
        let r_actual = self.resolve_type(actual);
        // self.print_type(&r_expected);
        // self.print_type(&r_actual);
        // println!("");
        
        match (r_expected, r_actual) {
            (TypeOrVar::Ty(p), TypeOrVar::Ty(q)) =>
                if !self.types_ok(p, q) {
                    self.type_errors.push(TypeError::TypeMismatch(
                        self.stype_str(&p),
                        self.stype_str(&q),
                        pos
                    ))
                },
            (TypeOrVar::Ty(t), TypeOrVar::Var(r, _)) | (TypeOrVar::Var(r, _), TypeOrVar::Ty(t)) => {
                // set root id in map to type
                self.type_map.insert(r, t);   
            }
            (TypeOrVar::Var(r1, _), TypeOrVar::Var(r2, _)) => {
                // union using data structure
                self.unions.union(r1, r2);
                
                // no need to resolve again and check type, already done earlier
                
                /*
                let t1 = self.type_map.get(&r1);
                let t2 = self.type_map.get(&r2);
                // check that they match
                match (t1, t2) {
                    (None, Some(t)) | (Some(t), None) => {
                        // set type of root to t
                        self.type_map.insert(new_root, *t);
                    }
                    (Some(exp), Some(act)) => {
                        // check if OK
                        if !self.types_ok(*exp, *act) {
                            self.type_errors.push(TypeError::TypeMismatch(
                                self.stype_str(exp),
                                self.stype_str(act),
                                pos
                            ));
                        }

                        // set type of root to expected type, 
                        // minimise less desirable error message later on
                        self.type_map.insert(new_root, *exp);
                    }
                    _ => ()
                }
                */
            }
        }
    }

    // If error, just return Top
    fn transform_type(&mut self, t: &Option<TypePos>, id_pos: PositionRange) -> TypeOrVar {
        match t {
            Some(ty) => match &ty.ty {
                Type::Primitve(p) => TypeOrVar::Ty(SType::Primitve(*p)),
            
                Type::UserType(t) => {
                    // TODO: FOR NOW just use the head. But later on this needs to be changed
                    // to support importing scopes/namespaces.
                    let id = self.nme_map.get(&t.first);
                    
                    match id {
                        Some(id) if self.adt_defs.get(&id).is_some() => TypeOrVar::Ty(SType::UserType(*id)),
                        _ => {
                            self.name_errors.push(AnalysisError::TypeNotFound(t.to_string(), ty.pos));
                            TypeOrVar::Ty(SType::Top)
                        }
                    }
                }
            }
            None => self.fresh_type_var(id_pos)
        }
    }

    fn create_fn_locals(&mut self, params: &Vec<(String, SParamDef)>) -> LocalsMap {
        let mut new_locals = LocalsMap::new();

        for p in params {
            new_locals = new_locals.insert(p.0.to_string(), (p.1.name, p.1.ty));
        }

        new_locals
    }

    // will update the fn map
    // function will only ever be transformed once.
    fn transform_fn(&mut self, fun_name: String, pos: PositionRange, locals: &LocalsMap) {
        // get id, then def
        let fun_id = *match self.nme_map.get(&fun_name) {
            Some(id) => id,
            None => {
                self.name_errors.push(AnalysisError::FnNotFoundError(fun_name, pos));
                return;
            }
        };

        let fun_def = match self.get_fun_def(&fun_id) {
            Some(f) => f,
            None => {
                self.name_errors.push(AnalysisError::FnNotFoundError(fun_name, pos));
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

        let more_locals = self.create_fn_locals(&fun_def_owned.params);

        let body_pos = body.pos;

        let stripped = self.scan_defs(body);

        // re-insert dummy definition in case of recursive calls inside the body
        let dummy_expr = SExprPos { expr: Dummy, pos: body_pos };
        
        let dummy = TmpFunDef {
            name_str: fun_def_owned.name_str,
            name: fun_def_owned.name,
            name_pos: fun_def_owned.name_pos,
            ty: fun_def_owned.ty,
            params: fun_def_owned.params,
            body: NSExprPos::S(dummy_expr)
        };
        self.fun_defs.insert(fun_id, dummy);

        let transformed = self.convert(stripped, fun_def_owned.ty, &locals, &more_locals);

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
            body: NSExprPos::S(transformed_)
        };
        
        self.fun_defs.insert(fun_id, new);
    }

    fn scan_defs(&mut self, e: ExprPos) -> ExprPos {
        // TODO: scan names
        self.scan_defs_rec(e)
    }

    // strips away all adt definitions, replaces function definitions with IDs
    fn scan_defs_rec(&mut self, e: ExprPos) -> ExprPos {
        match e.expr {
            Expr::AdtDefn(defn, next) => {
                let id = self.fresh_id(defn.name.to_string(), defn.name_pos);
                todo!();
                self.scan_defs_rec(*next)
            }
            Expr::FunDefn(defn, next) => {
                let id = self.fresh_id(defn.name.to_string(), defn.name_pos);
                
                let new_params = defn.params.iter().map(|p| {
                    (
                        p.name.to_string(),
                        SParamDef {
                            // TODO: fix p.pos
                            name: self.fresh_id(p.name.to_string(), p.nme_pos),
                            ty: self.transform_type(&p.ty, p.nme_pos),
                            pos: p.nme_pos
                        }
                    )
                }).collect();

                let name_pos = defn.name_pos;

                let defn = TmpFunDef {
                    name_str: defn.name.to_string(),
                    name: id,
                    name_pos,
                    ty: self.transform_type(&defn.ty, name_pos),
                    params: new_params,
                    body: NSExprPos::N(*defn.body)
                };

                self.fun_defs.insert(id, defn);

                ExprPos { expr: Expr::FunDefId(id, name_pos, Box::new(self.scan_defs_rec(*next))), pos: e.pos} 
            }
            Expr::Sequence(e1, e2) => ExprPos {
                expr: Expr::Sequence(e1, Box::new(self.scan_defs_rec(*e2))),
                pos: e.pos
            },
            Expr::Let(pd, expr, after) => {
                ExprPos {
                    expr: Expr::Let(pd, expr, Box::new(self.scan_defs_rec(*after))),
                    pos: e.pos
                }
            }
            _ => e
        }
    }

    pub fn convert_top(&mut self, e: ExprPos) -> Option<SExprPos> {
        // scan definitions
        let stripped = self.scan_defs(e);
        let ret = self.convert(stripped, TypeOrVar::Ty(SType::Top), &TreeMap::new(), &TreeMap::new());
        
        // Look for unbound type variables.
        let mut checked : HashSet<u64> = HashSet::new();
        
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
                },
            }
        }

        return ret;
    }

    pub fn convert(&mut self, e: ExprPos, expected: TypeOrVar, prev_locals: &LocalsMap, locals: &LocalsMap) -> Option<SExprPos> {

        pub fn get_local(name: &String, prev_locals: &LocalsMap, locals: &LocalsMap) -> Option<Local> {
            match locals.get(name) {
                Some(t) => Some(*t),
                None => match prev_locals.get(name) {
                    Some(t) => Some(*t),
                    None => None
                }
            }
        }
        
        let pos = e.pos;

        let s_expr: SExpr = match e.expr {
            Expr::Nested(e) => 
                self.convert(*e, expected, prev_locals, locals)?.expr,
            
            Expr::FunDefn(_, after) => {
                self.convert(*after, expected, prev_locals, locals)?.expr
            }
            Expr::Variable(nme) => {
                // 1. Check if in locals map
                // 2. Get local
                let local = match get_local(&nme.first, prev_locals, locals) {
                    Some(l) => l,
                    None => {
                        self.name_errors.push(AnalysisError::LocalNotFoundError(nme.first.to_string(), pos));
                        return None
                    }
                };

                // if ty is in type map, set
                let ty = self.resolve_type(local.1);
                
                match nme.nexts.first() {
                    None => {
                        self.add_constraint(expected, ty, pos); // we know its type, so add the constraint
                        SExpr::Variable(local.0, Vec::new())
                    }
                    Some(next) => 
                        // 3. In case it's accessing a data member, we require that its
                        // type is already inferred.
                        match ty {
                            TypeOrVar::Ty(SType::UserType(id)) => {
                                // Get the adt def.
                                let adt_def = self.get_adt_def(&id).unwrap();
                                // Check if the member exists in the scope.
                                let param_id_ = adt_def.name_map.get(next);

                                match param_id_ {
                                    Some(param_id) => {
                                        // add type constarint, return

                                        let pd = adt_def.params.iter().find(|p| p.name == *param_id).unwrap();
                                        let ty_ = pd.ty;
                                        let param_id_owned = *param_id;

                                        self.add_constraint(expected, ty_, pos);
                                        SExpr::Variable(local.0, vec![param_id_owned])
                                    }
                                    None => {
                                        // error
                                        self.name_errors.push(AnalysisError::NoMemberError(next.to_string(), pos));
                                        return None
                                    }
                                }
                            }
                            TypeOrVar::Ty(SType::Primitve(_)) | TypeOrVar::Ty(SType::Top) => {
                                self.name_errors.push(AnalysisError::NoMemberError(next.to_string(), pos));
                                return None
                            }
                            TypeOrVar::Var(_, pos) => {
                                self.type_errors.push(TypeError::TypeNeededError(pos));
                                return None
                            }
                        }
                }
                
            }
            Expr::Call(qn, args) => {
                 // get id, then def
                let fun_id = *match self.nme_map.get(&qn.first) {
                    Some(id) => id,
                    None => {
                        self.name_errors.push(AnalysisError::FnNotFoundError(qn.first, pos));
                        return None;
                    }
                };

                let fun_def = match self.get_fun_def(&fun_id) {
                    Some(f) => f,
                    None => {
                        self.name_errors.push(AnalysisError::FnNotFoundError(qn.first, pos));
                        return None;
                    }
                };

                let args_len = fun_def.params.len();

                // check args length correct
                if args.len() > args_len {
                    self.name_errors.push(AnalysisError::TooManyArgsError(qn.first, pos));
                    return None;
                }
                if args.len() < args_len {
                    self.name_errors.push(AnalysisError::TooFewArgsError(qn.first, pos));
                    return None;
                }

                // type check args
                let mut transformed_args: Vec<Option<SExprPos>> = Vec::new();

                let types: Vec<TypeOrVar> = fun_def.params.iter().map(|p| p.1.ty).collect();

                let ret_type = fun_def.ty;

                for (arg, ty) in zip(args, types) {
                    // type checking occurs here
                    transformed_args.push(
                        self.convert(arg, ty, prev_locals, locals)
                    );
                }
                
                // transform options into exprs
                let mut transformed_final : Vec<SExprPos> = Vec::new();

                for e_ in transformed_args {
                    transformed_final.push(e_?)
                }

                // add type constraint
                self.add_constraint(expected, ret_type, pos);

                // transform function
                self.transform_fn(qn.first, pos, locals);

                // println!("Ret type:");
                // self.print_type(&self.resolve_type(ret_type));
                // println!("First arg type:")
                // self.print_type(&self.resolve_type(func.ty));

                SExpr::Call(
                    fun_id, transformed_final
                )
            },
            Expr::Ctor(_, _) => todo!(),
            Expr::Sequence(e1, e2) => {
                let e1 = self.convert(*e1, TypeOrVar::Ty(SType::Top), prev_locals, locals);
                let e2 = self.convert(*e2, expected, prev_locals, locals)?;

                match e1 {
                    Some(e) => SExpr::Sequence(Box::new(e), Box::new(e2)),
                    None => return None
                }
            }
            Expr::Ite(_, _, _, _) => todo!(),
            Expr::Match(_, _) => todo!(),
            Expr::While(_, _) => todo!(),
            Expr::IntLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Int)), pos);
                SExpr::IntLit(v)
            }
            Expr::FloatLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Float)), pos);
                SExpr::FloatLit(v)
            }
            Expr::StringLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::String)), pos);
                SExpr::StringLit(v.to_string())
            }
            Expr::BoolLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Bool)), pos);
                SExpr::BoolLit(v)
            }
            Expr::UnitLit => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Unit)), pos);
                SExpr::UnitLit
            }
            Expr::Infix(_, _, _) => todo!(),
            Expr::Prefix(_, _) => todo!(),
            Expr::Let(pd, expr, after) => {
                // Check for name conflicts. Allow variable shadowing
                // If there is a name conflict, we try to continue using the new
                // definition of the variable to minimise errors for the user.
                
                let maybe_local = locals.get(&pd.name);

                if locals.get(&pd.name).is_some() {
                        let og_pos = self.id_pos_map.get(&maybe_local.unwrap().0).unwrap();

                        self.name_errors.push(AnalysisError::VariableRedefError(pd.name.to_string(), pos, *og_pos));
                }

                // get type ID
                let ty = self.transform_type(&pd.ty, pd.nme_pos);

                // eval body
                let body = self.convert(*expr, ty, prev_locals, locals);
                
                // get fresh local
                let new_local = self.fresh_id(pd.name.to_string(), pd.nme_pos);

                let more_locals = locals.insert(pd.name, (new_local, ty));

                let after = self.convert(*after, expected, prev_locals, &more_locals)?;
                
                SExpr::Let(
                    SParamDef {
                        name: new_local,
                        ty: ty,
                        pos: pd.nme_pos
                    },
                    Box::new(body?),
                    Box::new(after)
                )
            }
            Expr::AssignmentOp(_, _, _, _) => todo!(),
            Expr::AdtDefn(_, _) => todo!(),
            Expr::FunDefId(id, pos, after) => {
                self.transform_fn(self.id_map.get(&id).unwrap().to_string(), pos, locals);
                self.convert(*after, expected, prev_locals, locals)?.expr
            },
        };

        Some(SExprPos {
            expr: s_expr,
            pos
        })
    }
}

pub fn init_analyzer() -> Analyzer {
    Analyzer {
        fun_defs: HashMap::new(),
        adt_defs: HashMap::new(),
        nme_map: HashMap::new(),
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