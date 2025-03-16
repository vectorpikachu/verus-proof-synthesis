use vstd::prelude::*;

fn main() {
    // Write a function in Rust  to replace characters in a string.

    assert_eq!(
        replace_chars(&("polygon".as_bytes()), b'y', b'l'),
        "pollgon".as_bytes().to_vec()
    );
    assert_eq!(
        replace_chars(&("character".as_bytes()), b'c', b'a'),
        "aharaater".as_bytes().to_vec()
    );
    assert_eq!(
        replace_chars(&("python".as_bytes()), b'l', b'a'),
        "python".as_bytes().to_vec()
    );
}

verus! {

fn replace_chars(str1: &[u8], old_char: u8, new_char: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == old_char {
                new_char
            } else {
                str1[i]
            }),
{
    let mut result_str = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1@.len(),
            result_str@.len() == index,
            forall|k: int|
                0 <= k < index ==> result_str[k] == (if str1[k] == old_char {
                    new_char
                } else {
                    str1[k]
                }),
    {
        if str1[index] == old_char {
            result_str.push(new_char);
        } else {
            result_str.push(str1[index]);
        }
        index += 1;
    }
    result_str
}

} // verus!
