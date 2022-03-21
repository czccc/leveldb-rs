pub struct Random {
    seed: u32,
}

impl Random {
    pub fn new(seed: u32) -> Self {
        let mut random = Self {
            seed: seed & 0x7FFFFFFF,
        };
        if random.seed == 0 || random.seed == 2147483647 {
            random.seed = 1;
        }
        random
    }
    pub fn next(&mut self) -> u32 {
        const M: u32 = 2147483647;
        const A: u64 = 16807;
        let product: u64 = self.seed as u64 * A;
        self.seed = ((product >> 31) + (product & M as u64)) as u32;
        if self.seed > M {
            self.seed -= M;
        }
        self.seed
    }
    pub fn uniform(&mut self, n: u32) -> u32 {
        self.next() % n
    }
    pub fn one_in(&mut self, n: u32) -> bool {
        (self.next() % n) == 0
    }
    pub fn skewed(&mut self, max_log: u32) -> u32 {
        let tmp = self.uniform(max_log + 1) % 32;
        self.uniform((1 << tmp) as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn random() {
        let mut rand = Random::new(0xdeadbeef);
        for _ in 0..100 {
            rand.next();
            rand.uniform(100);
            rand.one_in(100);
            rand.skewed(100);
        }
    }
}
