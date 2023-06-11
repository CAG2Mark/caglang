#[derive(Copy, Clone)]
pub struct Position {
    pub line_no: usize,
    pub pos: usize,
}

#[derive(Copy, Clone)]
pub struct PositionRange {
    pub start: Position,
    pub end: Position,
}

pub fn union_pos(start: Position, end: Position) -> PositionRange {
    PositionRange { start, end }
}

pub fn union_pos1(start: Position, p2: PositionRange) -> PositionRange {
    PositionRange { start, end: p2.end }
}

pub fn union_posr(p1: PositionRange, p2: PositionRange) -> PositionRange {
    PositionRange {
        start: p1.start,
        end: p2.end,
    }
}
