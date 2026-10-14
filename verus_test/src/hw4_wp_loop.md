# Homework 4 Weakest Precondition Loops

## Problem 1

### Proof

0: $m0 != 0 \wedge n0 * m0 <= usize::MAX \wedge n0 * m0 == res + n * m0$

1: $m0 != 0 \wedge n0 * m0 <= usize::MAX \wedge n0 * m0 == res + n * m0 \wedge 0 < n$

2: $m0 != 0 \wedge n0 * m0 <= usize::MAX \wedge n0 * m0 == res + n * m0 \wedge res + m0 <= n0 * m0$

for all n, res ==> (2)

3: $m0 != 0 \wedge n0 * m0 <= usize::MAX \wedge n0 * m0 == res + n * m0 \wedge res + m0$

4: $m0 != 0 \wedge n0 * m0 <= usize::MAX \wedge n0 * m0 == (res+m0) + (n-1) * m0 \wedge n - 1$

4: $m0 != 0 \wedge n0 * m0 <= usize::MAX \wedge n0 * m0 == (res+m0) + (n-1) * m0 \wedge n0 * m0 == (res+m0) + (n-1) * m0$

for all n, res ==> (4)


<!-- 1: $n0 * m0 == res + n * m0 \wedge n - 1 \wedge res + m0 \wedge res + m0 <= n0 * m0$ -->



### Code
```rust
pub proof fn lemma_q3(n0: usize, m0: usize, res: usize, n: usize) 
{
    // I (invariant)
    // assert requires implies invariant
    assert((m0 != 0 && n0 * m0 <= usize::MAX) ==> (m0 != 0 && n0 * m0 <= usize::MAX && n0 * m0 == res + n * m0));

    // while loop body preserves I
    assert((0 < n) ==> (m0 != 0 && n0 * m0 <= usize::MAX && n0 * m0 == res + n * m0 && res + m0 <= n0 * m0));
    assert((0 < n) ==> (n0 * m0 == (res + m0) + (n-1) * m0) && ((res+m0) + m0 <= n0 * m0));
    // not looping implies Q
    assert((0 < n) ==> (res == 0));
    // termination
    assert((n > 0));
}
```