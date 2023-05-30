use std::collections::VecDeque;

use crate::parsing::ast::*;

use crate::parsing::{ast::ExprPos, tokens::Position};

/*
Prec:
||
&&
==
<, >
<=, >=
+, -
*, /, %
 */
fn get_prec(op: &String) -> (u32, u32) {
    let op_ = op.as_str();

    match op_ {
        "||" => (1, 2),
        "&&" => (3, 4),
        "==" => (5, 6),
        "<" | ">" => (7, 8),
        "<=" | ">=" => (9, 10),
        "+" | "-" => (11, 12),
        "*" | "/" | "%" => (13, 14),
        _ => unreachable!()
    }
}

pub fn pratt_parse(acc: ExprPos, prec: u32, rest: &mut VecDeque<(String, Position, ExprPos)>) -> ExprPos {
    match rest.front() {
        Some((op, _, _)) if get_prec(op).0 > prec => {
            let front = rest.pop_front().unwrap();
            let (op_, pos_, next_) = front;
            
            let rhs = pratt_parse(next_, get_prec(&op_).1, rest);
            let lhs = ExprPos { expr: Expr::Infix(op_, Box::new(acc), Box::new(rhs)), pos: pos_ };

            pratt_parse(lhs, prec, rest)
        }
        _ => acc
    }
}