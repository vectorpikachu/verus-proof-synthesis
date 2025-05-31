# Verus-Bench

This folder contains benchmark tasks for Verus, a formal verification tool.
Its name is `VerusBench`.

Verus-Bench contains in total 150 tasks, which are from four different sources:

- `CloverBench`: 11 tasks from [CloverBench](https://github.com/ChuyueSun/Clover).
  - This suite includes 60 example programs, as might be found in CS textbooks, written and verified in Dafny. The authors of CloverBench also provide the Verus translation for 39 of them. Our manual inspection found that 3 of them cannot be verified by the latest version of Verus, 4 have weaker specifications than their variants already included in the dataset, and 21 can be verified without proof annotations. We add all remaining 11 into Verus-Bench.
- `MBPP-DFY-153`: 78 tasks from [MBPP-DFY-153](https://github.com/Mondego/dafny-synthesis).
  - That dataset contains 153 problems with specifications and verified implementation in/for Dafny, based on the MBPP dataset. Among these 153, 67 of them require no proof annotations to verify; 8 are too difficult to translate due to code features not well supported by Rust/Verus like floating points and string; the remaining 78 are all translated and included in Verus-Bench.
- `Diffy`: 38 tasks from [Diffy](https://figshare.com/articles/code/Diffy_Inductive_Reasoning_of_Array_Programs_using_Difference_Invariants/14509467?file=27797196), a SV-COMP-2021 benchmark suite.
  - Diffy contains 69 programs written in C that were designed to evaluate array and loop related verification. Most tasks in this suite contain multiple loops and hence require good loop-invariant synthesis. 31 tasks here require reasoning about non-linear equations, which is not the focus of Verus system verification. We translated all the remaining 38 tasks from C to Rust.
- `Misc`: 23 tasks from Misc
  - This is a collection of 23 miscellaneous Verus programs that appeared in Verus tutorials or libraries. They include some algorithmic programs, like bubble sort, binary search, fibonacci sequence, and tasks that contain challenging features like nested loops, expressing function post conditions as asserts instead of ensures, etc.

For each source, the `unverified` folder contains the task to be verified, and the `verified` folder contains the task with correct proof annotations.
