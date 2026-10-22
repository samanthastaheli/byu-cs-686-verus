use vstd::prelude::*;
// use vstd::prelude::int;

verus! {
    mod problem_1 {
        use vstd::prelude::*;       
        pub open spec fn count_spec(s: Seq<int>, x: int) -> int
            decreases s.len(),
        {
            // let mut i: int = s.len() as int;
            // let mut count: int = 0;

            // while i > 0 
            //     invariant
            //         i <= s.len() as int,
            //         i >= 0,
            //     decreases i
            // {
            //     if s[i] == x {
            //         count = count + 1;
            //     }
            //     i = i - 1;
            // }
            // count
            if s.len() == 0 {
                0
            } else {
                (if s[0] == x { 1 as int } else { 0 as int }) + count_spec(s.skip(1), x)
            }
        }

        pub fn count_vec(v: Vec<isize>, x: isize) -> (count: usize) 
            // ensures
            //     count as int == count_spec(v@ as int, x),
        {
            let mut i: usize = v.len();
            let mut count: usize = 0;

            while i > 0 
                invariant 
                    i <= v.len(),
                    count as int == count_spec(v@.subrange(i as int, v.len() as int).map(|idx: int, val: isize| val as int), x as int),
                decreases 
                    i,
            {
                i = i - 1;
                if v[i] == x {
                    count = count + 1;
                }
            }
            count
        }

        pub proof fn lemma_count(v: Vec<isize>, x: isize)
            ensures 
                count_vec(v, x) as int == count_spec(v@.map(|idx: int, val: isize| val as int), x as int),
        {
            // assert(count_vec(v, x) == count_spec(v@, x));
        }

    }

    mod problem_2 {

    }

    mod problem_3 {
        
    }

    mod problem_4 {
        
    }

    fn main() {}
} // verus!