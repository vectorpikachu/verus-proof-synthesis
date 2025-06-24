use vstd::prelude::*;

fn main() {}

verus!{
spec fn fibo(n: nat) -> nat 
	decreases n
{ 
	if n == 0 { 0 } else if n == 1 { 1 } 
	else { fibo((n - 2) as nat) + fibo((n - 1) as nat) } 
}

proof fn fibo_is_monotonic(i: nat, j: nat)
	requires i <= j,
	ensures fibo(i) <= fibo(j),
    decreases j - i
{  
	if i < 2 && j < 2 {}
	else if i == j {}
	else if i == j - 1 {
		fibo_is_monotonic(i as nat, (j - 1) as nat);
	} else { 
		fibo_is_monotonic(i as nat, (j - 1) as nat);
		fibo_is_monotonic(i as nat, (j - 2) as nat);
	}
}
}
