use std::collections::HashMap;

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

pub struct FunSig {
    pub id: Identifier,
    pub params: Vec<SParamDef>,
    pub ret: TypeOrVar
}

pub struct ConstrDef {
    pub id: Identifier,
    pub params: Vec<SParamDef>
}

pub struct AdtSig {
    id: Identifier,
    params: HashMap<Identifier, SParamDef>,
    id_map: HashMap<String, Identifier>,
    variants: HashMap<String, ConstrDef>
}

pub struct SProgram {
    pub funcs: Vec<FunSig>,
    pub main: SExprPos
}

pub struct Analyzer {
    // Name analysis part
    fun_defs: HashMap<Identifier, FunSig>,
    adt_defs: HashMap<Identifier, AdtSig>,
    nme_map: HashMap<String, Identifier>,
    id_map: HashMap<Identifier, String>,
    local_id: u64,

    // Type analysis part. We use a union-find data structure
    // to compactly store type var equality.
    unions: UnionFindInt,
    type_map: HashMap<Identifier, SType>,

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
    NoMemberError(String, PositionRange)
}

impl Analyzer {
    fn get_adt_def(&mut self, id: &Identifier) -> Option<&AdtSig> {
        self.adt_defs.get(id)
    }

    fn fresh_local(&mut self, name: String) -> u64 {
        self.id_map.insert(self.local_id, name.to_string());
        self.nme_map.insert(name.to_string(), self.local_id);

        let ret = self.local_id;
        self.local_id += 1;
        ret
    }

    fn fresh_type_var(&mut self) -> TypeOrVar {
        TypeOrVar::Var(self.unions.fresh_var())
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

    fn stype_str(&self, t: &SType) -> String {
        match t {
            SType::Primitve(p) => p.to_string(),
            SType::UserType(id) => self.id_map.get(id).unwrap().to_string(),
            SType::Top => "<Top>".to_string()
        }
    }

    fn add_constraint(&mut self, expected: TypeOrVar, actual: TypeOrVar, pos: PositionRange) {
        match (expected, actual) {
            (TypeOrVar::Ty(p), TypeOrVar::Ty(q)) =>
                if !self.types_ok(p, q) {
                    self.type_errors.push(TypeError::TypeMismatch(
                        self.stype_str(&p),
                        self.stype_str(&q),
                        pos
                    ))
                },
            (TypeOrVar::Ty(t), TypeOrVar::Var(v)) | (TypeOrVar::Var(v), TypeOrVar::Ty(t)) => {
                // get root
                let rt = self.unions.find_set(v);
                // set root id in map to type
                self.type_map.insert(rt, t);   
            }
            (TypeOrVar::Var(v1), TypeOrVar::Var(v2)) => {
                // get roots
                let r1 = self.unions.find_set(v1);
                let r2 = self.unions.find_set(v2);
                
                // union using data structure
                let new_root = self.unions.union(r1, r2);
                // check that types match
                let t1 = self.type_map.get(&r1);
                let t2 = self.type_map.get(&r2);

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
                            return
                        }

                        // set type of root to expected type, 
                        // minimise less desirable error message later on
                        self.type_map.insert(new_root, *exp);
                    }
                    _ => ()
                }
            }
        }
    }

    fn scan_defs(&mut self, e: &ExprPos) {
        todo!()
    }

    pub fn convert_top(&mut self, e: &ExprPos) -> Option<SExprPos> {
        self.convert(e, TypeOrVar::Ty(SType::Primitve(Prim::Unit)), &TreeMap::new())
    }

    pub fn convert(&mut self, e: &ExprPos, expected: TypeOrVar, locals: &TreeMap<Identifier, TypeOrVar>) -> Option<SExprPos> {
        // self.scan_defs(&e);
        
        let pos = e.pos;

        let s_expr: SExpr = match &e.expr {
            Expr::Nested(e) => 
                self.convert(&*e, expected, locals)?.expr,
            
            Expr::FunDefn(_, after) => {
                self.convert(&*after, expected, locals)?.expr
            }
            Expr::Variable(nme) => {
                // first, get ID
                let var = *match self.nme_map.get(&nme.first) {
                    Some(id) => id,
                    None => {
                        self.name_errors.push(AnalysisError::LocalNotFoundError(nme.first.to_string(), pos));
                        return None
                    }
                };

                // 1. Check if in locals map
                // 2. Get type
                let mut ty = *match locals.get(&var) {
                    Some(ty) => ty,
                    None => {
                        self.name_errors.push(AnalysisError::LocalNotFoundError(nme.first.to_string(), pos));
                        return None
                    }
                };

                // if ty is in type map, set
                ty = match ty {
                    TypeOrVar::Ty(_) => ty,
                    TypeOrVar::Var(v) => match self.type_map.get(&v) {
                        Some(t) => TypeOrVar::Ty(*t),
                        None => ty,
                    },
                };
                
                match nme.nexts.first() {
                    None => {
                        self.add_constraint(expected, ty, pos); // we know its type, so add the constraint
                        SExpr::Variable(var, Vec::new())
                    }
                    Some(next) => 
                        // 3. In case it's accessing a data member, we require that its
                        // type is already inferred.
                        match ty {
                            TypeOrVar::Ty(SType::UserType(id)) => {
                                // Get the adt def.
                                let adt_def = self.get_adt_def(&id).unwrap();
                                // Check if the next item exists in the scope.
                                let param_id_ = adt_def.id_map.get(next);

                                match param_id_ {
                                    Some(param_id) => {
                                        // add type constarint, return

                                        let pd = adt_def.params.get(param_id).unwrap();
                                        let ty_ = pd.ty;
                                        let param_id_owned = *param_id;

                                        self.add_constraint(expected, ty_, pos);
                                        SExpr::Variable(var, vec![param_id_owned])
                                    }
                                    None => {
                                        // error
                                        self.name_errors.push(AnalysisError::NoMemberError(next.to_string(), pos));
                                        return None
                                    }
                                }
                            }
                            TypeOrVar::Ty(SType::Primitve(_)) => {
                                self.name_errors.push(AnalysisError::NoMemberError(next.to_string(), pos));
                                return None
                            }
                            _ => {
                                self.type_errors.push(TypeError::TypeNeededError(pos));
                                return None
                            }
                        }
                }
                
            }
            Expr::Call(_, _) => todo!(),
            Expr::Sequence(e1, e2) => {
                let e1 = self.convert(e1, TypeOrVar::Ty(SType::Top), locals);
                let e2 = self.convert(e2, expected, locals)?;

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
                SExpr::IntLit(*v)
            }
            Expr::FloatLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Float)), pos);
                SExpr::FloatLit(*v)
            }
            Expr::StringLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::String)), pos);
                SExpr::StringLit(v.to_string())
            }
            Expr::BoolLit(v) => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Bool)), pos);
                SExpr::BoolLit(*v)
            }
            Expr::UnitLit => {
                self.add_constraint(expected, TypeOrVar::Ty(SType::Primitve(Prim::Unit)), pos);
                SExpr::UnitLit
            }
            Expr::Infix(_, _, _) => todo!(),
            Expr::Prefix(_, _) => todo!(),
            Expr::Let(pd, expr, after) => {
                // todo!()
                // get type ID
                let ty: TypeOrVar = match &pd.ty {
                    // primitive
                    Some(Type::Primitve(p)) => TypeOrVar::Ty(SType::Primitve(*p)),
                    // user type
                    Some(Type::UserType(name)) => {
                        // get id
                        // TODO: FOR NOW just use the head. But later on this needs to be changed
                        // to support importing scopes/namespaces.

                        let id = self.nme_map.get(&name.first).unwrap();
                        TypeOrVar::Ty(SType::UserType(*id))
                    }
                    None => {
                        self.fresh_type_var()
                    }
                };

                // eval body
                let body = self.convert(&*expr, ty, locals);
                
                // get fresh local
                let new_local = self.fresh_local(pd.name.to_string());

                let more_locals = locals.insert(new_local, ty);

                let after = self.convert(&*after, expected, &more_locals)?;

                
                SExpr::Let(
                    SParamDef {
                        name: new_local,
                        ty: ty,
                        pos: pd.pos
                    },
                    Box::new(body?),
                    Box::new(after)
                )
            }
            Expr::AssignmentOp(_, _, _, _) => todo!(),
            Expr::AdtDefn(_, _) => todo!(),
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
        local_id: 0,
        unions: union_find_int::new(),
        type_map: HashMap::new(),
        name_errors: Vec::new(),
        type_errors: Vec::new(),
    }
}