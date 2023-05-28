use std::{collections::VecDeque, any::Any};
use crate::tokens::TokenPos;
use crate::tokens::*;
use crate::tokens::Token::*;
use crate::ast::*;
use crate::ast::Expr::*;
use crate::ast::Tree::*;

pub enum ParseError {
    UnexpectedToken(String, Vec<String>, Position), // got, expected, pos
    Unfinished(String, Position), // got, pos
    UnexpectedEOF(Vec<String>), // expected
    UnexpectedEOFOther // expected
}

pub struct Parser {
    tokens: VecDeque<TokenPos>
}

fn vecStrToString(v: Vec<&str>) -> Vec<String> {
    v.into_iter().map(|s| s.to_string()).collect()
}

impl Parser {

    fn skip_keyword(&mut self, expected: &str, skip_exprsep: bool) -> Result<(String, Position), ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                Keyword(got) => {
                    if got == expected {
                        Ok((got, tk.pos))
                    } else {
                        Err(ParseError::UnexpectedToken(got, vec![expected.to_string()], tk.pos))
                    }
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_delimiter(&mut self, expected: Vec<&str>, skip_exprsep: bool) -> Result<(String, Position), ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let exp : Vec<String> = vecStrToString(expected);

        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                Delimiter(got) => {
                    if exp.contains(&got) {
                        Ok((got, tk.pos))
                    } else {
                        Err(ParseError::UnexpectedToken(got, exp, tk.pos))
                    }
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), exp, tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(exp))
            }
        }
    }

    fn skip_identifier(&mut self, skip_exprsep: bool) -> Result<(String, Position), ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = IDENT_STR;
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                Identifier(nme) => {
                    Ok((nme, tk.pos))
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_prim_type(&mut self, skip_exprsep: bool) -> Result<(Type, Position), ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = PRIM_STR;
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                PrimType(nme) => {
                    Ok((Type::Primitve(nme), tk.pos))
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_int_literal(&mut self, skip_exprsep: bool) -> Result<TokenPos, ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = INT_LIT_STR;
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                IntLiteral(_) => {
                    Ok(tk)
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_float_literal(&mut self, skip_exprsep: bool) -> Result<TokenPos, ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = FLOAT_LIT_STR;
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                FloatLiteral(_) => {
                    Ok(tk)
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_string_literal(&mut self, skip_exprsep: bool) -> Result<TokenPos, ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = STRING_LIT_STR;
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                StringLiteral(_) => {
                    Ok(tk)
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_bool_literal(&mut self, skip_exprsep: bool) -> Result<TokenPos, ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = BOOL_LIT_STR;
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                BoolLiteral(_) => {
                    Ok(tk)
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_operator(&mut self, expected: &str, skip_exprsep: bool) -> Result<(String, Position), ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                Operator(got) => {
                    if got == expected {
                        Ok((got, tk.pos))
                    } else {
                        Err(ParseError::UnexpectedToken(got, vec![expected.to_string()], tk.pos))
                    }
                }
                _ => Err(ParseError::UnexpectedToken(tk.to_str(), vec![expected.to_string()], tk.pos))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec![expected.to_string()]))
            }
        }
    }

    fn skip_exprsep(&mut self) {
        let front = self.tokens.front();

        match front {
            Some(tk) => match tk.tk {
                ImplicitExprSep => {
                    self.consume(false);
                    self.skip_exprsep()
                }
                _ => ()
            }
            _ => ()
        }
    }

    fn peek_front(&mut self, skip_exprsep: bool) -> Option<&TokenPos> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let front = self.tokens.front();
        match front {
            Some(tk) => Some(tk),
            None => None
        }
    }

    fn peek_front_strict(&mut self, skip_exprsep: bool) -> Result<&TokenPos, ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let front = self.tokens.front();
        match front {
            Some(tk) => Ok(tk),
            None => Err(ParseError::UnexpectedEOFOther)
        }
    }

    fn consume(&mut self, skip_exprsep: bool) {
        if skip_exprsep {
            self.skip_exprsep()
        }

        self.tokens.pop_front();
    }
    

    pub fn parse(&mut self) -> Result<ExprPos, ParseError> {

        let parsed = self.parse_expr()?;

        
        // all tokens should be consumed by now
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => Err(ParseError::Unfinished(tk.to_str(), tk.pos)),
            None => Ok(parsed)
        }
        
    }

    
    // ALTERNATIVES.
    // def id ( paramDef* ) (: type)? = singleExpr
    // singleExpr (; singleExpr?)?
    fn parse_expr(&mut self) -> Result<ExprPos, ParseError> {
        let next = self.peek_front(true);

        match next {
            Some(cur) => {
                let first = match &cur.tk {
                    Keyword(kw) if kw == "def" => {
                        self.parse_fn_def()?
                    }
                    _ => {
                        self.parse_single_expr()?
                    }
                };

                let pos = first.pos;

                // parse (; expr?)?
                match self.peek_front(false) {
                    Some(tk) => match &tk.tk {
                        ExplicitExprSep => {
                            let tk_pos = tk.pos;
                            self.consume(false);

                            match self.parse_maybe_expr()? {
                                Some(second) => Ok(ExprPos {
                                    expr: Sequence(Box::new(first), Box::new(second)),
                                    pos: pos
                                }),
                                None => Ok(ExprPos {
                                    expr: Sequence(Box::new(first), Box::new(ExprPos { expr: UnitLit, pos: tk_pos })),
                                    pos: pos})
                            }
                        }
                        ImplicitExprSep => {
                            self.consume(false);

                            match self.parse_maybe_expr()? {
                                Some(second) => Ok(ExprPos {
                                    expr: Sequence(Box::new(first), Box::new(second)),
                                    pos: pos
                                }),
                                None => Ok(first)
                            }
                        }
                        _ => Ok(first)
                    },
                    None => Ok(first)
                }
            }
            None => Err(ParseError::UnexpectedEOFOther)
        }
    }

    fn parse_maybe_expr(&mut self) -> Result<Option<ExprPos>, ParseError> {
        match self.peek_front(true) {
            Some(tk) => match &tk.tk {
                Delimiter(d) if d == "}" || d == ")" || d == "]" => Ok(None),
                _ => Ok(Some(self.parse_expr()?)),
            }
            None => Ok(None)
        }
    }

    fn parse_fn_def(&mut self) -> Result<ExprPos, ParseError> {
        let first = self.skip_keyword("def", true)?;
        let id = self.skip_identifier(true)?;
        self.skip_delimiter(vec!["("], true)?;

        let params = self.parse_fn_params()?; // also parses the remaining ")"

        let ty : Option<Type> = 
            if self.skip_delimiter(vec!["=", ":"], true)?.0 == ":" {
                let ret = Some(self.parse_type()?);
                self.skip_delimiter(vec!["="], true)?;
                ret
            } else {
                None
            };
        
        let body = self.parse_single_expr()?;

        Ok(ExprPos { expr: Expr::FunDef(id.0, ty, params, Box::new(body)), pos: first.1 })
    }

    fn parse_fn_params(&mut self) -> Result<Vec<ParamDef>, ParseError> {
        let mut ret: Vec<ParamDef> = Vec::new();
        match self.peek_front_strict(true)?.tk {
            Identifier(_) => {
                let mut cond = true;

                while cond {
                    ret.push(self.parse_param_def()?);
                    let next = self.skip_delimiter(vec![")", ","], true)?;
                    cond = next.0 == ",";
                }

                Ok(ret)
            }
            _ => {
                self.consume(true);
                Ok(ret)
            }
        }
    }

    fn parse_param_def(&mut self) -> Result<ParamDef, ParseError> {
        let id = self.skip_identifier(true)?;
        let cur = self.peek_front_strict(true)?;
        match &cur.tk {
            Delimiter(d) if d == ":" => {
                self.consume(true);
                let ty = self.parse_type()?;
                Ok(ParamDef { name: id.0, ty: Some(ty), pos: id.1 })
            }
            _ => Ok(ParamDef { name: id.0, ty: None, pos: id.1 })
        }
    }

    fn parse_type(&mut self) -> Result<Type, ParseError> {
        let ty = self.skip_prim_type(true)?;
        Ok(ty.0)
    }

    fn parse_single_expr(&mut self) -> Result<ExprPos, ParseError> {
        // temporary
        let possible = vec!["if", "match", IDENT_STR, INT_LIT_STR, FLOAT_LIT_STR, BOOL_LIT_STR, STRING_LIT_STR, "{", "("];

        let front = self.peek_front_strict(true)?;
        
        let pos = front.pos;

        match &front.tk {
            // Keyword(_) => todo!(),
            Delimiter(d) if d == "{" => {
                self.consume(true);
                let expr = self.parse_expr()?;
                self.skip_delimiter(vec!["}"], true)?;
                Ok(ExprPos{ expr: Nested(Box::new(expr)), pos: pos })
            }
            Identifier(id) => {
                let ret = Ok(ExprPos { expr: Variable(id.to_owned()), pos: pos });
                self.consume(true);
                ret
            }
            IntLiteral(val) => {
                let ret = Ok(ExprPos { expr: IntLit(*val), pos: pos });
                self.consume(true);
                ret
            }
            FloatLiteral(val) => {
                let ret = Ok(ExprPos { expr: FloatLit(*val), pos: pos });
                self.consume(true);
                ret
            }
            StringLiteral(val) => {
                let ret = Ok(ExprPos { expr: StringLit(val.to_owned()), pos: pos });
                self.consume(true);
                ret
            }
            BoolLiteral(val) => {
                let ret = Ok(ExprPos { expr: BoolLit(*val), pos: pos });
                self.consume(true);
                ret
            }
            // Operator(_) => todo!(),
            _ => Err(ParseError::UnexpectedToken(front.to_str(), vecStrToString(possible), pos))
        }
    }
    
}


pub fn new(tokens: Vec<TokenPos>) -> Parser {
    Parser { tokens: VecDeque::from(tokens) }
}