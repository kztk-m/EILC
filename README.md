Embedded ILC
============

This is an implementation of the unembedded EDSL for 
Giarrusso et al.'s cache-transfer style incremental 
calculus. 

The code is used in the experiments in Section 5 of the 
paper "Embedding by Unembedding", which appears in ICFP 2023.

We note here that this version is based on a preliminary 
version of the framework, which has minor differences from 
the one presented in the paper.

To perform the experiments mentioned in the paper, run:

    sh runbench.sh sequence
    
To run the script, we need `stack`: we can install `stack` following the instructions in https://docs.haskellstack.org/en/stable/README/.