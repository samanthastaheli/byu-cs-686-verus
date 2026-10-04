use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish;

verus! {

    mod problem_1 {
        use vstd::prelude::*;
        use vstd::arithmetic::mul::lemma_mul_inequality;

        // 1.1
        pub open spec fn factorial_spec(n: nat) -> nat 
            decreases 
                n
        {
            if n == 0 {
                1
            } else {
                n * factorial_spec((n-1) as nat)
            }
        }

        // 1.2
        pub proof fn test_factorial_n_gte_1() {
            assert(factorial_spec(0) == 1);
            assert(factorial_spec(1) == 1);
            assert(factorial_spec(2) == 2);
        }

        // 1.3 
        pub proof fn lemma_factorial_is_monotonic(i: nat, j:nat) by (nonlinear_arith) // tell remember how to do math
            ensures 
                i <= j ==> factorial_spec(i) <= factorial_spec(j),
            decreases
                j,
        {
            if j == 0 {
            } else {
                lemma_factorial_is_monotonic(i, (j - 1) as nat);
            }
            
        }

        pub proof fn test_i_lt_j_then_factorial_i_will_be_gte_factorial_i() 
        {
            assert_by_compute(factorial_spec(3) >= factorial_spec(2));
        }

        // 1.4
        pub fn factorial_exec(n: usize) -> (result: usize)
            requires
                factorial_spec(n as nat) <= usize::MAX as nat,
            ensures
                factorial_spec(n as nat) == result,
            decreases 
                n
        {
            if n == 0 {
                1
            } else {
                proof {
                lemma_factorial_is_monotonic((n - 1) as nat, n as nat);
                }
                n * factorial_exec((n-1))
            }
        }

        // 1.5
        pub fn factorial_iter(n: usize) -> (result: usize)
            requires
                factorial_spec(n as nat) <= usize::MAX as nat,
            ensures
                factorial_spec(n as nat) == result,
        {
            let mut result: usize = 1;
            let mut i: usize = 0;
            
            while i < n  
                invariant
                    i <= n,
                    factorial_spec(n as nat) <= usize::MAX as nat,
                    result == factorial_spec(i as nat),
                decreases
                    n - i 
            {
                let next: usize= i + 1;

                proof {
                    assert(i < n);
                    lemma_factorial_is_monotonic((i as nat) + 1,n as nat,);
                    assert(factorial_spec((i as nat) + 1) <= factorial_spec(n as nat));
                    assert(factorial_spec((i as nat) + 1) <= usize::MAX as nat);
                    reveal(factorial_spec);
                    assert(factorial_spec(next as nat) == (next as nat) * factorial_spec(i as nat));
                }
                result = result * next;
                i += 1;
            }
            result
        }

        pub fn test_factorial_spec_and_factorial_iter_are_equal() {
            proof {
            assert_by_compute(factorial_spec(2) == 2);
            }

            let result = factorial_iter(2);
            assert(result == 2);
        }
    }

    mod problem_2 {
        use vstd::prelude::*;
        use vstd::arithmetic::mul::lemma_mul_is_commutative;
        use vstd::arithmetic::mul::lemma_mul_is_distributive_add;

        // 2.1: recursive implementation 
        pub open spec fn sum_to_n_spec(n: nat) -> nat 
            decreases 
                n
        {
            if n == 0 {
                0
            } else {
                n + sum_to_n_spec((n-1) as nat)
            }
        }

        // 2.2: prove sum_to_n
        pub proof fn test_sum_to_n_n_gte_1() {
            assert(sum_to_n_spec(0) == 0);
            assert(sum_to_n_spec(1) == 1);
            assert(sum_to_n_spec(2) == 3);
        }

        // 2.3: prove sum_to_n is monotonic 
        pub proof fn lemma_sum_to_n_is_monotonic(i: nat, j:nat) by (nonlinear_arith) // tell remember how to do math
            ensures 
                i <= j ==> sum_to_n_spec(i) <= sum_to_n_spec(j),
            decreases
                j,
        {
            if j == 0 {
            } else {
                lemma_sum_to_n_is_monotonic(i, (j - 1) as nat);
            }
        }

        // 2.4: recursive implementation
        pub fn sum_to_n_exec(n: usize) -> (result: usize)
            requires
                sum_to_n_spec(n as nat) <= usize::MAX as nat,
            ensures
                sum_to_n_spec(n as nat) == result,
            decreases 
                n
        {
            if n == 0 {
                0
            } else {
                proof {
                lemma_sum_to_n_is_monotonic((n - 1) as nat, n as nat);
                }
                n + sum_to_n_exec((n-1))
            }
        }

        // Proofs
        pub proof fn lemma_sum_to_n_is_commutative(n: nat) 
            ensures
                sum_to_n_spec(n) == n * (n + 1) / 2,
            decreases
                n
        {
            if n == 0 {
            } else {
                lemma_sum_to_n_is_commutative((n - 1) as nat);
                assert(sum_to_n_spec(n) == n * (n + 1) / 2) by (nonlinear_arith)
                    requires
                        sum_to_n_spec((n - 1) as nat) == ((n - 1) * n) / 2,
                        sum_to_n_spec(n) == n + sum_to_n_spec((n - 1) as nat),
                        n > 0,
                {};
            }
        }

        pub proof fn lemma_sum_to_n_is_distributive_add(n: nat) 
            ensures
                n * (n - 1) + n + n == n * ((n - 1) + 2),
            decreases
                n
        {
            if n == 0 {
            } else {
                lemma_sum_to_n_is_distributive_add((n - 1) as nat);
                assert(n * (n - 1) + n + n == n * ((n - 1) + 2)) by (nonlinear_arith)
                    requires
                        n > 0,
                {};
            }
        }
    }

    mod problem_3 {
        use vstd::prelude::*;

        // 3.1: recursive implementation 
        pub open spec fn gcd_spec(a: nat, b: nat) -> nat
            decreases b
        {
            if b == 0 {
                a
            } else {
                gcd_spec(b, (a % b) as nat)
            }
        }

        // 3.4: recursive implementation
        pub fn gcd_exec(a: usize, b: usize) -> (result: usize)
            requires
                gcd_spec(a as nat, b as nat) <= usize::MAX as nat,
            ensures
                gcd_spec(a as nat, b as nat) == result,
            decreases 
                b
        {
            if b == 0 {
                a
            } else {
                gcd_exec(b, (a % b) as usize)
            }
        }

        // Proofs
        pub proof fn test_gcd_positive_concrete() {
            assert_by_compute(gcd_spec(8, 2) > 0);
        }

        pub proof fn lemma_gcd_positive(a: nat, b: nat)
            requires
                !(a == 0 && b == 0),
            ensures
                0 < gcd_spec(a, b),
            decreases
                b
        {
            if b == 0 {}
            else {
                lemma_gcd_positive(b, (a % b) as nat);
            }
        }

        use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};
        use vstd::arithmetic::div_mod::lemma_mod_adds;
        use vstd::arithmetic::div_mod::lemma_mod_multiples_basic;
        use vstd::arithmetic::mul::lemma_mul_is_associative;

        proof fn lemma_mod_mul_zero(x: int, q: int, m: int)
            requires
                m > 0,
                x % m == 0,
            ensures
                (x * q) % m == 0,
        {
            lemma_fundamental_div_mod(x, m);
            lemma_mul_is_associative(m, (x / m), q);
            lemma_mod_multiples_basic((x / m) * q, m);
        }

        pub proof fn lemma_gcd_divides(a: nat, b: nat)
            requires
                !(a == 0 && b == 0),
            ensures
                a % gcd_spec(a, b) == 0,
                b % gcd_spec(a, b) == 0,
            decreases
                a, b
        {
            lemma_gcd_positive(a, b);
            if a == 0 {

            } else if b == 0 {

            } else if a > b {
                let g = gcd_spec(a , b) as int;
                lemma_gcd_divides(a % b, b);
                lemma_fundamental_div_mod(a as int, b as int);
                lemma_mod_mul_zero(b as int, (a / b) as int, g);
                lemma_mod_adds(b as int * (a as int / b as int), a as int % b as int, g)
            } else {
                let g = gcd_spec(a , b) as int;
                lemma_gcd_divides(a % b, b);
                lemma_fundamental_div_mod(a as int, b as int);
                lemma_mod_mul_zero(a as int, (b / a) as int, g);
                lemma_mod_adds(a as int * (b as int / a as int), b as int % a as int, g)
            }
        }
    }

    fn main()
    {

    }
} //verus!