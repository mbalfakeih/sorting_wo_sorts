# Sorting without Sorts Benchmarks
This repository contains the benchmark files for the paper "Sorting without Sorts", that is the sortedness and multiset property conjectures of three popular sorting algorithms, namely Insertion Sort, Mergesort and Quicksort. 

To run the benchmarks, we use the Vampire theorem prover branch supporting parameterized sorts and computation induction available at https://github.com/vprover/vampire/tree/rule-induction-sorting. 

Each file contains a comment indicating the strategy that solves the benchmark in a matter of seconds. Note we ran our benchmarks on a dedicated portfolio mode to find these winning strategies. 

Run vampire with the following command: 
    [vampire_executable] --decode [copy strategy from file] [filename.smt2]
