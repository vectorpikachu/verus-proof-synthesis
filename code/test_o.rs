
use vstd::prelude::*;
fn main() {}

verus! {

#[verifier::loop_isolation(false)]

    pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
    {
        let mut i: usize = 0;
        while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            forall |j: int| 0 <= j < i ==> {
                if j as usize % 1 == 0 {
                    a[j as int] == 1
                } else {
                    a[j as int] == 0
                }
            },
        {
            if (i % 1 == 0) {
                a.set(i, 1);
            } else {
                a.set(i, 0);
            }
            i = i + 1;
        }

        i = 0;
        proof {
            assert(sum[0] >= 0); // Added by AI
            assert(sum[0] <= i); // Added by AI
        }
        while (i < N as usize)
        invariant
            i <= N,
            a.len() == N,
            sum.len() == 1,
            N > 0,
            sum[0] <= i,                                // Invariant bounding sum[0]
            forall |j: int| 0 <= j < i ==> {
                if j == 0 {
                    sum[0] == 0
                } else {
                    sum[0] == old(sum)[0] + a[j as int]
                }
            },
            sum[0] >= 0,                                // Lower bound for sum[0]
            forall |j: usize| (0 <= j < N as usize) ==> (a[( j ) as int] >= 0 && a[( j ) as int] <= 1),   // Bounds for a[j]
        {
            proof {
                assert(0 <= sum[0]); // Added by AI
                assert(sum[0] <= i); // Added by AI
                assert(a[(i) as int] >= 0 && a[(i) as int] <= 1); // Added for bounds of a[i]
                assert(0 <= sum[0] + a[(i) as int]); // Lower bound hold
                assert(sum[0] + a[(i) as int] <= N); // Upper bound ensured
            }
            if (i == 0) {
                sum.set(0, 0);
            } else {
                sum.set(0, sum[0] + a[i]);
            }
            i = i + 1;
        }
    }
}

// Score: (0, 2)
// Safe: True