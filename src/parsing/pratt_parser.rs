use std::collections::VecDeque;

use crate::parsing::ast::*;

use crate::parsing::ast::ExprPos;

use super::position::union_posr;

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

pub fn pratt_parse(acc: ExprPos, prec: u32, rest: &mut VecDeque<(String, ExprPos)>) -> ExprPos {
    match rest.front() {
        Some((op, _)) if get_prec(op).0 > prec => {
            let front = rest.pop_front().unwrap();
            let (op_, next_) = front;

            let p1 = acc.pos.to_owned();
            
            let rhs = pratt_parse(next_, get_prec(&op_).1, rest);
            let p2 = rhs.pos.to_owned();

            let lhs = ExprPos { expr: Expr::Infix(op_, Box::new(acc), Box::new(rhs)), pos: union_posr(p1, p2) };

            pratt_parse(lhs, prec, rest)
        }
        _ => acc
    }
}