use vstd::prelude::*;

fn main() {
    // Write a function in Rust that takes in a string and character, replaces blank spaces in the string with the character, and returns the string.

    assert_eq!(
        replace_blanks_with_chars(&("hello people".as_bytes().to_vec()), b'@'),
        "hello@people".as_bytes().to_vec()
    );
    assert_eq!(
        replace_blanks_with_chars(&("python program language".as_bytes().to_vec()), b'$'),
        "python$program$language".as_bytes().to_vec()
    );
    assert_eq!(
        replace_blanks_with_chars(&("blank space".as_bytes().to_vec()), b'-'),
        "blank-space".as_bytes().to_vec()
    );
}

verus! {

fn replace_blanks_with_chars(str1: &Vec<u8>, ch: u8) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if str1[i] == 32 {
                ch
            } else {
                str1[i]
            }),
{
    let mut out_str: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            out_str@.len() == index,
            forall|k: int|
                0 <= k < index ==> out_str[k] == (if str1[k] == 32 {  // 32 is ASCII Space as u8
                    ch
                } else {
                    str1[k]
                }),
    {
        if (str1[index] == 32) {  // 32 is ASCII Space as u8
            out_str.push(ch);
        } else {
            out_str.push(str1[index]);
        }
        index += 1;
    }
    out_str
}

} // verus!
