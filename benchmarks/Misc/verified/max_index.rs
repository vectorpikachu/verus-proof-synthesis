use vstd::prelude::*;
fn main() {}
verus! {

pub fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    requires
        x.len() >= 1,
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        exists|k: int| 0 <= k < x.len() ==> x[max_index as int] == x[k],
{
    let mut max_index = 0;
    let mut i: usize = 1;
    while (i < x.len())
        invariant
            0 <= i <= x.len(),
            0 <= max_index < x.len(),
            forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
    {
        if x[i] > x[max_index] {
            max_index = i;
        }
        assert(forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k]);
        i = i + 1;
    }
    max_index
}

} // verus!