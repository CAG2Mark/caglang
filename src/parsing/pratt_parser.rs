use std::collections::VecDeque;

use crate::parsing::ast::*;

use crate::parsing::tokens::Op;

use crate::parsing::ast::StatExprPos;

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
fn get_prec(op: &Op) -> (u32, u32) {
    use crate::parsing::tokens::Op::*;
    match op {
        Or => (1, 2),
        And => (3, 4),
        Eq => (5, 6),
        Lt | Gt => (7, 8),
        Lte | Gte => (9, 10),
        Add | Minus => (11, 12),
        Times | Divide | Mod  => (13, 14),
        _ => unreachable!(),
    }
}

pub fn pratt_parse(acc: StatExprPos, prec: u32, rest: &mut VecDeque<(Op, StatExprPos)>) -> StatExprPos {
    match rest.front() {
        Some((op, _)) if get_prec(op).0 > prec => {
            let front = rest.pop_front().unwrap();
            let (op_, next_) = front;

            let p1 = acc.pos.to_owned();

            let rhs = pratt_parse(next_, get_prec(&op_).1, rest);
            let p2 = rhs.pos.to_owned();

            let lhs = StatExprPos {
                expr: StatExpr::Infix(op_, Box::new(acc), Box::new(rhs)),
                pos: union_posr(p1, p2),
            };

            pratt_parse(lhs, prec, rest)
        }
        _ => acc,
    }
}
