use std::collections::VecDeque;
use crate::tokens::TokenPos;
use crate::tokens::*;
use crate::tokens::Token::*;
use crate::ast::*;
use crate::ast::Expr::*;
use crate::parsing::pratt_parser::pratt_parse;

pub enum ParseError {
    UnexpectedToken(String, Vec<String>, Position), // got, expected, pos
    Unfinished(String, Position), // got, pos
    UnexpectedEOF(Vec<String>), // expected
    UnexpectedEOFOther // expected
}

pub struct Parser {
    tokens: VecDeque<TokenPos>
}

fn vec_str_to_string(v: Vec<&str>) -> Vec<String> {
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

        let exp : Vec<String> = vec_str_to_string(expected);

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

    fn skip_equals(&mut self, skip_exprsep: bool) -> Result<Position, ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let expected = "=".to_string();
        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                AssignmentOperator(op) if op == "=" => {
                    Ok(tk.pos)
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

    fn skip_assignment_operator(&mut self, skip_exprsep: bool) -> Result<(String, Position), ParseError> {
        if skip_exprsep {
            self.skip_exprsep()
        }

        let front = self.tokens.pop_front();
        match front {
            Some(tk) => match tk.tk {
                AssignmentOperator(got) => {
                    Ok((got, tk.pos))
                }
                _ => Err(ParseError::UnexpectedEOF(vec!["<Assignment Operator>".to_string()]))
            }
            None => {
                Err(ParseError::UnexpectedEOF(vec!["<Assignment Operator>".to_string()]))
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

    fn peek_front(&self, skip_exprsep: bool) -> Option<&TokenPos> {
        let mut idx = 0;

        if skip_exprsep {
            // skip to next token that is not ImplicitExprSep
            while idx < self.tokens.len() && matches!(self.tokens.get(idx).unwrap().tk, ImplicitExprSep) {
                idx += 1;
            }
        }

        let front = self.tokens.get(idx);
        match front {
            Some(tk) => Some(tk),
            None => None
        }
    }

    fn lookahead(&self, cnt: u32, skip_exprsep: bool) -> Option<&TokenPos> {
        let mut idx = 0;

        for _ in 0..cnt {
            if skip_exprsep {
                // skip to next token that is not ImplicitExprSep
                while idx < self.tokens.len() && matches!(self.tokens.get(idx).unwrap().tk, ImplicitExprSep) {
                    idx += 1;
                }
            }
            // skip non-whitespace token
            idx += 1;
        }

        idx -= 1;

        let front = self.tokens.get(idx);
        match front {
            Some(tk) => Some(tk),
            None => None
        }
    }

    fn peek_front_strict(&self, skip_exprsep: bool) -> Result<&TokenPos, ParseError> {
        let mut idx = 0;

        if skip_exprsep {
            // skip to next token that is not ImplicitExprSep
            while idx < self.tokens.len() && matches!(self.tokens.get(idx).unwrap().tk, ImplicitExprSep) {
                idx += 1;
            }
        }

        let front = self.tokens.get(idx);
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
    // x = singleExpr; ?
    // singleExpr (; singleExpr?)?
    fn parse_expr(&mut self) -> Result<ExprPos, ParseError> {
        let cur = self.peek_front_strict(true)?;
        let pos = cur.pos.to_owned();
                
        // position of this expression
        match &cur.tk {
            Keyword(kw) if kw == "def" => {
                let e1 = self.parse_fn_def()?;
                let rest = self.parse_after_exprsep()?;
                match rest {
                    Some(e2) => Ok(ExprPos { expr: Sequence(Box::new(e1), Box::new(e2)), pos }),
                    None => Ok(e1)
                }
            }
            
            Keyword(kw) if kw == "let" => self.parse_let(false),
            
            _ => self.parse_sequence_or_assignment(false, false)
        }
    }

    fn parse_sequence_or_assignment(&mut self, skip_exprsep: bool, single: bool) -> Result<ExprPos, ParseError> {
        let front = self.peek_front_strict(true)?;
        let mut pos = front.pos.to_owned();

        let e1 = self.parse_single_expr(skip_exprsep)?;
        
        let between = self.peek_front(false);

        // quick hack
        let mode;
        let mut op_: String = "".to_string();

        let body = match &between {
            Some(tk) => match &tk.tk {
                AssignmentOperator(op) => {
                    op_ = op.to_string();
                    pos = tk.pos;
                    self.consume(true);
                    let e2 = self.parse_single_expr(skip_exprsep)?;
                    mode = 0;
                    Some(e2)
                }
                _ => {
                    mode = 1;
                    None
                }
            }
            _ => {
                mode = 1;
                None
            }
        };

        let after = if single {
            None
        } else {
            self.parse_after_exprsep()?
        };

        let ret = match after {
            Some(e2) => {
                match mode {
                    0 => ExprPos { expr: AssignmentOp(
                        op_,
                        Box::new(e1), 
                        Box::new(body.unwrap(),),
                        Box::new(e2)), pos },
                    1 => ExprPos { expr: Sequence(Box::new(e1), Box::new(e2)), pos },
                    _ => unreachable!()
                }
            }
            None => {
                match mode {
                    0 => ExprPos { expr: AssignmentOp(
                        op_,
                        Box::new(e1), 
                        Box::new(body.unwrap(),),
                        Box::new(
                            ExprPos { expr: UnitLit, pos }
                        )), pos },
                    1 => e1,
                    _ => unreachable!()
                }
            }
        };

        Ok(ret)
    }

    fn parse_let(&mut self, single: bool) -> Result<ExprPos, ParseError> {
        self.skip_keyword("let", true)?;
        
        let id_pos = self.peek_front_strict(true)?.pos;
        let pd = self.parse_param_def()?;

        let equal_pos = self.skip_equals(true)?;
        let val = self.parse_single_expr(false)?;
        
        let after = if single {
            Some(ExprPos { expr: UnitLit, pos: id_pos })
        } else {
            self.parse_after_exprsep()?
        };

        let ret = match after {
            Some(e2) => ExprPos { expr: Let(pd, Box::new(val), Box::new(e2)), pos: equal_pos },
            None => ExprPos { expr: Let(pd, Box::new(val), Box::new(ExprPos { expr: UnitLit, pos: id_pos })), pos: equal_pos }
        };

        Ok(ret)
    }

    // parse (<ExprSep> expr?)?.
    fn parse_after_exprsep(&mut self) -> Result<Option<ExprPos>, ParseError> {
        let ret = match self.peek_front(false) {
            Some(tk) => match &tk.tk {
                ExplicitExprSep => {
                    let tk_pos = tk.pos;
                    self.consume(false);

                    match self.parse_maybe_expr()? {
                        Some(second) => Some(second),
                        None => Some(ExprPos { expr: UnitLit, pos: tk_pos })
                    }
                }
                ImplicitExprSep => {
                    self.consume(false);

                    match self.parse_maybe_expr()? {
                        Some(second) => Some(second),
                        None => None
                    }
                }
                _ => None
            },
            None => None
        };
        Ok(ret)
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

    fn parse_maybe_single_expr(&mut self, skip_exprsep: bool) -> Result<Option<ExprPos>, ParseError> {
        match self.peek_front(true) {
            Some(tk) => match &tk.tk {
                Delimiter(d) if d == "}" || d == ")" || d == "]" => Ok(None),
                _ => Ok(Some(self.parse_single_expr(skip_exprsep)?)),
            }
            None => Ok(None)
        }
    }

    fn parse_fn_def(&mut self) -> Result<ExprPos, ParseError> {
        let first = self.skip_keyword("def", true)?;
        let id = self.skip_identifier(true)?;
        self.skip_delimiter(vec!["("], true)?;

        let params = self.parse_fn_params()?; 

        self.skip_delimiter(vec![")"], true)?;

        let next = self.peek_front_strict(true)?;
        let ty : Option<Type> = match &next.tk {
            Delimiter(d) if d == ":" => {
                self.consume(true);
                let ret = Some(self.parse_type()?);
                self.skip_equals(true)?;
                Ok(ret)
            }
            AssignmentOperator(op) if op == "=" => {
                self.consume(true);
                Ok(None)
            }
            tk => Err(ParseError::UnexpectedToken(tk.to_str(), vec!["=".to_string(), ":".to_string()], next.pos))
        }?;
        
        let body = self.parse_sequence_or_assignment(false, true)?;

        Ok(ExprPos { expr: Expr::FunDef(id.0, ty, params, Box::new(body)), pos: first.1 })
    }

    fn parse_fn_params(&mut self) -> Result<Vec<ParamDef>, ParseError> {
        let mut ret: Vec<ParamDef> = Vec::new();
        match self.peek_front_strict(true)?.tk {
            Identifier(_) => {
                let mut cond = true;

                while cond {
                    ret.push(self.parse_param_def()?);
                    let next = self.peek_front_strict(true)?;
                    cond = matches!(&next.tk, Delimiter(d) if d == ",");
                    if cond {
                        self.consume(true)
                    }
                }

                Ok(ret)
            }
            _ => Ok(ret)
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

    // "Single expressions" are guaranteed to evaluate to a value (or explicitly a unit literal) and do not contain
    // chained sequences on the outer level.

    // Here, it would just be expressions involving zero or more operators.
    fn parse_single_expr(&mut self, skip_exprsep: bool) -> Result<ExprPos, ParseError> {
        let first = self.parse_simple_expr(skip_exprsep)?;
        let rest = self.parse_more_ops(skip_exprsep)?;

        Ok(pratt_parse(first, 0, &mut VecDeque::from(rest)))
    }
    
    fn parse_more_ops(&mut self, skip_exprsep: bool) -> Result<Vec<(String, Position, ExprPos)>, ParseError> {
        let mut ret: Vec<(String, Position, ExprPos)> = Vec::new();
        
        let mut front = self.peek_front(skip_exprsep);
        
        let mut cond = true;
        while cond {
            match front {
                Some(tk) => {
                    match &tk.tk {
                        Operator(op) => {
                            let op_ = op.to_owned();
                            let pos_ = tk.pos.to_owned();
                            self.consume(true);
                            let next = self.parse_simple_expr(skip_exprsep)?;
                            ret.push((op_.to_string(), pos_, next));
                            front = self.peek_front(skip_exprsep);
                        }
                        _ => cond = false
                    }
                }
                None => {
                    cond = false
                }
            }
        }
        

        Ok(ret)
    }
        

    // Includes match and if else expressions.
    fn parse_simple_expr(&mut self, skip_exprsep: bool) -> Result<ExprPos, ParseError> {
        let front = self.peek_front_strict(true)?;
        
        let pos = front.pos;

        match &front.tk {
            Keyword(kw) if kw == "if" => self.parse_ite_expr(),
            Keyword(kw) if kw == "while" => self.parse_while_expr(),
            Operator(op) if op == "!" || op == "-" => {
                let op_ = op.to_owned();
                self.consume(true);
                let operand = self.parse_atomic_exp(skip_exprsep)?;
                Ok(ExprPos{ expr: Prefix(op_, Box::new(operand)), pos })
            }
            // Operator(_) => todo!(),
            _ => self.parse_atomic_exp(skip_exprsep)
        }
    }

    fn parse_atomic_exp(&mut self, skip_exprsep: bool) -> Result<ExprPos, ParseError> {
        let possible = vec!["if", "match", IDENT_STR, INT_LIT_STR, FLOAT_LIT_STR, BOOL_LIT_STR, STRING_LIT_STR, "{", "("];

        let front = self.peek_front_strict(true)?;
        let pos = front.pos;

        match &front.tk {
            Delimiter(d) if d == "{" => {
                self.consume(true);
                let inner = self.parse_maybe_expr()?;
                self.skip_delimiter(vec!["}"], true)?;

                match inner {
                    Some(expr) => Ok(ExprPos{ expr: Nested(Box::new(expr)), pos: pos }),
                    None => Ok(ExprPos{ expr: UnitLit, pos: pos })
                }
            }
            Delimiter(d) if d == "(" => {
                self.consume(true);
                let inner = self.parse_maybe_single_expr(true)?;
                self.skip_delimiter(vec![")"], true)?;

                match inner {
                    Some(expr) => Ok(expr),
                    None => Ok(ExprPos{ expr: UnitLit, pos: pos })
                }
            }
            Identifier(_) => {
                self.parse_var_or_call(skip_exprsep)
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

            _ => Err(ParseError::UnexpectedToken(front.to_str(), vec_str_to_string(possible), pos))
        }
    }

    fn parse_var_or_call(&mut self, skip_exprsep: bool) -> Result<ExprPos, ParseError> {
        let pos = self.peek_front_strict(true)?.pos.to_owned();

        let qn = self.parse_qualified_name()?;

        let front = self.peek_front(skip_exprsep);
        match &front {
            Some(tk) if matches!(&tk.tk, Delimiter(d) if d == "(") => {
                let args = self.parse_bracketed_exprs()?;
                Ok(ExprPos {
                    expr: Call(qn, args),
                    pos
                })
            }
            _ => Ok(ExprPos { expr: Variable(qn), pos })
        }
    }

    fn parse_bracketed_exprs(&mut self) -> Result<Vec<ExprPos>, ParseError> {
        self.skip_delimiter(vec!["("], true)?;
        let mut ret = Vec::new();
        if matches!(&self.peek_front_strict(true)?.tk, Delimiter(d) if d == ")") {
            self.consume(true);
            return Ok(ret);
        }

        let mut cond = true;
        while cond {
            ret.push(self.parse_single_expr(true)?);
            let next = self.peek_front_strict(true)?;
            cond = matches!(&next.tk, Delimiter(d) if d == ",");
            if cond {
                self.consume(true)
            }
        }

        self.skip_delimiter(vec![")"], true)?;

        Ok(ret)
    }

    fn parse_qualified_name(&mut self) -> Result<QualifiedName, ParseError> {
        let first = self.skip_identifier(true)?.0.to_string();
        
        let mut front = self.peek_front(true);

        let mut nexts : Vec<String> = Vec::new();

        let mut cond = true;

        while cond {
            match &front {
                Some(tk) => match &tk.tk {
                    Delimiter(d) if d == "." => {
                        self.consume(true);
                        let next = self.skip_identifier(true)?.0;

                        nexts.push(next);

                        front = self.peek_front(true)
                    }
                    _ => cond = false
                }
                None => cond = false
            }
        }

        Ok(QualifiedName { first, nexts })
    }
    
    // parse if elif else
    // syntax: if (cond) singleExpr elif (cond) singleExpr .. else singleExpr 
    fn parse_ite_expr(&mut self) -> Result<ExprPos, ParseError> {
        let first = self.skip_keyword("if", true)?;
        // self.skip_delimiter(vec!["("], true)?;
        let cond = self.parse_single_expr(false)?;
        // self.skip_delimiter(vec![")"], true)?;
        let body = self.parse_sequence_or_assignment(false, true)?;

        Ok(
            ExprPos{ expr: Ite(
                Box::new(cond), Box::new(body),
                self.parse_elifs_expr()?,
                self.parse_else_expr()?
            ), pos: first.1 }
        )
    }

    fn parse_while_expr(&mut self) -> Result<ExprPos, ParseError> {
        let first = self.skip_keyword("while", true)?;
        // self.skip_delimiter(vec!["("], true)?;
        let cond = self.parse_single_expr(false)?;
        // self.skip_delimiter(vec![")"], true)?;
        let body = self.parse_sequence_or_assignment(false, true)?;

        Ok(
            ExprPos{ expr: While(
                Box::new(cond), Box::new(body)
            ), pos: first.1 }
        )
    }

    fn parse_elifs_expr(&mut self) -> Result<Vec<(Box<ExprPos>, Box<ExprPos>)>, ParseError> {
        let mut front = self.peek_front(true);

        let mut ret : Vec<(Box<ExprPos>, Box<ExprPos>)> = Vec::new();

        let mut cond = true;

        while cond {
            match &front {
                Some(tk) => match &tk.tk {
                    Keyword(d) if d == "elif" => {
                        self.consume(true);
                        // self.skip_delimiter(vec!["("], true)?;
                        let cond = self.parse_single_expr(false)?;
                        // self.skip_delimiter(vec![")"], true)?;
                        let body = self.parse_sequence_or_assignment(false, true)?;

                        ret.push((Box::new(cond), Box::new(body)));

                        front = self.peek_front(true)
                    }
                    _ => cond = false
                }
                None => cond = false
            }
        }

        Ok(ret)
    }

    fn parse_else_expr(&mut self) -> Result<Option<Box<ExprPos>>, ParseError> {
        let front = self.peek_front(true);

        match &front {
            Some(tk) => match &tk.tk {
                Keyword(d) if d == "else" => {
                    self.consume(true);
                    Ok(Some(Box::new(self.parse_sequence_or_assignment(false, true)?)))
                }
                _ => Ok(None)
            }
            None => Ok(None)
        }
    }
}


pub fn new(tokens: Vec<TokenPos>) -> Parser {
    Parser { tokens: VecDeque::from(tokens) }
}