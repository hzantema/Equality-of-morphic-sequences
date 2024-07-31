
This repository consists of all files for proving equality of morphic sequences, as described in the paper 
"Equality of morphic sequences" by Hans Zantema, available at https://arxiv.org/abs/2407.15721.

It contains the source code of three programs eq.p, eql.p and eqb.p, written in FreePascal. 
Here eq.p is the default and produces the standard proof. The program eql.p does the same, but produces the proof in LaTeX format.
The program eqb.p applies the basic approach as explained in the paper.

Also the Windows executables are available. 

FreePascal is open source, and also provides compilers for other platforms for free.

Apart from the programs several example files are included. 
They may serve as input for the programs, but also contain the output of the programs eq and eqb if they succeed: proofs that the encoded morphic sequences are equal. 
For instance, by running "eq < ex1.txt" a proof is generated that the corresponding morphic sequences are equal, which is also part of the file ex1.txt.
The format of the input is excplained in the above mentioned paper.

The programs and examples have been developed by Hans Zantema in 2024.
