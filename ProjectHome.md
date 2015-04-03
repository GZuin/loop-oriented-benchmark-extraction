Most of a program's execution time lies within loops execution. Therefore, loops are an interesting field of research in the context of compiler optimization, leading to multiple academic works. Heuristics to solve the halt problem is an example of such works. However, benchmarks specialized in loops aren't easily found, making testing such heuristics rather troublesome.



A benchmark extractor of C programs is proposed in this work. Utilizing the LLVM compiler and the pass framework, we seek the slicing of real programs in segments of code containing only a loop and the variables which affect its execution. The proposed extractor operates only over a program's bytecodes, keeping the original program's integrity intact.



This project can be divided into two minor projects:

- Slicing a program's bytecodes removing instructions not related to loops.

- A backend translator from low-level bc to high-level c