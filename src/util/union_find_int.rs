pub struct UnionFindInt {
    arr: Vec<u64>,
    heights: Vec<u64>,
    cur: u64
}

impl UnionFindInt {
    pub fn size(&self) -> u64 {
        self.cur
    } 

    pub fn fresh_var(&mut self) -> u64 {
        let ret = self.cur;
        self.arr.push(self.cur);
        self.heights.push(1);
        self.cur += 1;
        ret
    }

    pub fn find_set(&mut self, mut a: u64) -> u64 {
        if a >= self.cur {
            panic!("Variable out of bounds!")
        }

        while a != self.arr[a as usize] {
            let tmp = a;
            a = self.arr[a as usize];
            // path compress
            self.arr[tmp as usize] = self.arr[a as usize];
        }

        a
    }

    pub fn find_set_imut(&self, mut a: u64) -> u64 {
        if a >= self.cur {
            panic!("Variable out of bounds!")
        }

        while a != self.arr[a as usize] {
            a = self.arr[a as usize];
        }

        a
    }

    pub fn union(&mut self, x: u64, y: u64) -> u64 {
        if x >= self.cur || y >= self.cur {
            panic!("Variable out of bounds!")
        }

        let a = self.find_set(x);
        let b = self.find_set(y);

        let a_h = self.heights[a as usize];
        let b_h = self.heights[b as usize];

        // maintain balance
        // return new root
        if a_h <= b_h {
            if a_h == b_h {
                self.heights[y as usize] = b_h + 1;
            }
            self.arr[a as usize] = b;
            b
        } else {
            self.arr[b as usize] = a;
            a
        }
    }

    pub fn equal(&mut self, x: u64, y: u64) -> bool {
        self.find_set(x) == self.find_set(y)
    }

    pub fn print(&mut self) {
        for i in 0..self.cur {
            println!("{} -> {}", i, self.find_set(i));
        }
    }
}

pub fn new() -> UnionFindInt {
    UnionFindInt {
        arr: Vec::new(),
        heights: Vec::new(),
        cur: 0
    }
}