use vstd::prelude::*;

fn main() {
    // Write a function in Rust to check if a string represents an integer or not.

    assert!(!is_integer(&("python".as_bytes().to_vec())));
    assert!(is_integer(&("1".as_bytes().to_vec())));
    assert!(is_integer(&("123".as_bytes().to_vec())));
}

verus! {

spec fn is_digit_sepc(c: u8) -> bool {
    c >= 48 && c <= 57
}

fn is_digit(c: u8) -> (res: bool)
    ensures
        res == is_digit_sepc(c),
{
    c >= 48 && c <= 57
}

fn is_integer(text: &Vec<u8>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < text.len() ==> (#[trigger] is_digit_sepc(text[i]))),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall|i: int| 0 <= i < index ==> (#[trigger] is_digit_sepc(text[i])),
    {
        if (!is_digit(text[index])) {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
