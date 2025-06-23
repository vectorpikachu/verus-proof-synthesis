
use vstd::prelude::*;
fn main() {}

verus!{

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
				0 <= N,
				N > 0,
				i <= N,
				a.len() == N,
				sum.len() == 1,
				forall|k:int| 0 <= k < i ==> (a[k] == 1 || a[k] == 0),
		{
			if (i % 1 == 0) { // This handles each iteration explicitly.
				a.set(i, 1);
			} else {
				a.set(i, 0);
			}
			i = i + 1;
		}

		assert(forall|k:int| 0 <= k < N ==> (a[k] == 1 || a[k] == 0));

		i = 0;
		while (i < N as usize)
			invariant
				0 <= N,
				N > 0,
				i <= N,
				a.len() == N,
				sum.len() == 1,
				(i > 0 ==> sum[0] <= i), // Invariant holds for all iterations except the first one.
				forall|k:int| 0 <= k < a.len() ==> (a[k] == 1 || a[k] == 0), // `a[k]` remains correctly set.
		{
			if (i == 0) {
				sum.set(0, 0); // Special handling during the first iteration.
			} else {
				sum.set(0, sum[0] + a[i]);
			}
			i = i + 1;
		}
	}
}


// Score: (3, 0)
// Safe: True