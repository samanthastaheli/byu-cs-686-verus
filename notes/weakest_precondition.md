# Weakest Precondition 

*How verus works*

## Hoare Logic

* Hoare triples
  * `{P} s {Q}`
    * `{P}` = precondition
    * `{Q}` = postcondition
    * `s` = statement -> assumes termination 
  * strongest postcondition calculus $\rightarrow$
    * look a precondition to satisfy postcondition 
    * $sp(s,P) \rightarrow Q$
  * weakest precondition calculus $\leftarrow$
    * figure out what weakest precondition needs to be to imply weakest postcondition 
    * $p \rightarrow wp(s,Q)$
    * use to propagate through all the statements ending at precondition (`{P}`)

### WP Rules
1. Termination case: $wp([], Q) = Q$
2. Sequencing rule: $wp([s_0; s_1,], Q) = wp([s_0], wp([s_1], Q)$
3. Assignment rule: $wp([x: = e], Q) = Q[e/x]$ (replace x with e)
4. Assume (Partial Correctness): $wp([assume \ e],Q) = e \wedge Q$
5. Assume (Total Correctness / Standard Logic): $wp([assume \ e],Q) = e \rightarrow Q$
6. Function?Procedure Call: $wp([y = f(x)],Q) = wp([assert \ p_{f}[x/i]; \  assume \ Q_{f}[x/i,y/o], Q)$
7. While Loop (with invariant $I$ and variant/decrease metric $d$): $wp([while \ c \ s \ I \ d], Q) = $
   1. $\wedge I$
   2. $\wedge \forall xs \ c \wedge I \rightarrow wp([s], I)$
   3. $\wedge \forall xs \not c \wedge I \rightarrow Q$
   4. $\wedge \forall xs \ c \wedge I \rightarrow wp([s], d \geq 0)$
   5. $\wedge \forall xs \ c \wedge I \rightarrow wp([t=d;s], t > d)$
8. Conditional (if) rule: $wp([if \ c \ s_r \ s_E], Q) = (c ^ wp([s_T], Q)) V (\not c \wedge wp(s_E],Q)$


### Weakest Precondition Calculus Rules

![](wp_calculus.jpeg)

#### If Statements

```rust
exec fn g(x: isize) -> (r: isize) 
        requires
            x > isize::MIN + 1,
            x < isize::MAX - 1,
            x <= -9 || x >= 9,
        ensures
            r > 9,
            r > x,
    {
        let mut r: isize = x;
        if r < 0 {
            r = -r;
        }
        r = r + 1;

        r
    }
```

Numbers are correlated to lines of code in the above.

![](process_tree.jpeg)

#### While Loop

Rules:

1. assert the invariant at the head of the loop

##### Old While Loop
```rust
let mut m: usize = 0;
        assert(m <= n);
        while m < n 
            invariant 
                m <= n,
            decreases n - m,
        {
            m = m + 1;
        }
```

##### New As If Statement

```rust
25      exec fn h(n: usize) -> (m: usize)
26        requires 
27              n >= 0,
28        ensures 
29            n == m,
30    {
31        let mut m: usize = 0;
32        assert(n >= 0 && m <= n); // assert the invariant at the head of the loop
33        // havoc m
34        assume(n >= 0 && m <= n);
35        if m < n // change while to if
36        {
37            m = m + 1;
38            assert(n >= 0 && m <= n); // end of loop assert the invariant 
39            assume(false); // false -> 0 
40        } 
41        
42        m
```

$w|p (while \ c \ s \ I \ Q) =$

$\wedge I $

$\wedge \forall xs \ c \wedge I \rightarrow wp(s,I)$

$\wedge \forall xs \ \not c \wedge I \rightarrow Q$

$\wedge \forall xs \ c \wedge I \rightarrow wp(s, d \geq 0)$

$\wedge \forall xs \ c \wedge I \rightarrow wp([t'=d;s], t' > d)$


$\lor$


HW3:

use forall in an assert to "write out wp's"