
use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            exists|k: int| 0 <= k < i ==> arr[k] == key ==> true,
            arr.len() == arr.len(),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len()
        invariant
            index <= list1.len(),
            shared.len() <= list1.len(),
            forall|i: int|
                0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                    #[trigger] shared[i],
                )),
            forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
            list1.len() == list1.len(),
            list2.len() == list2.len(),
            shared.len() == shared.len(),
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            shared.push(list1[index]);
        }
        index += 1
    }
    shared
}

} // verus!
