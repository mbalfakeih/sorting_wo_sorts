#!/bin/bash
# This script is to reproduce the results in "Saturating Sorting without Sorts" 2024
# We run every *.smt2 file in the repo in six ways:
# Firstly, we use either the release version of Vampire 4.9 (commit 5ad494e78) or Vampire (commit 1b51a8072), symlinked to vampire and vampire_ind respectively.
# The latter is the most recent version of Vampire before the benchmarks were committed.
# (The benchmarks were commited on August 16th 2023, the Vampire commit is from June 17th 2023).
# Secondly, for each version of vampire we run:
# 1. The strategy defined in the file (These are slightly edited to each have a time limit of 2 minutes, which is larger than the largest time limit)
# 2. The structural induction schedule
# 3. The induction schedule
# If possible, we use the maximum number of cores available on our machine

#Resetting
d=$(git rev-parse --show-toplevel)

mkdir -p "$d"/results/insertionsort/sortedness
mkdir -p "$d"/results/insertionsort/mset
mkdir -p "$d"/results/mergesort/sortedness
mkdir -p "$d"/results/mergesort/mset
mkdir -p "$d"/results/quicksort/sortedness
mkdir -p "$d"/results/quicksort/mset

find "$d"/results/ -name "*.out" -type f -delete


# $1 which vampire to use
# $2 schedule/strategy parameters
# $3 file name
run () {
    if [[ "$2" = *"lrs"* ]] then
       o="strat"
    else
       o=$(echo "$2" | awk '{print $NF}')
    fi
    o="$o.$1"
    echo "Running on $3 with $2 using $1"
    $1 --input_syntax smtlib2 $2 "$d/$3.smt2" > "$d/results/$3.$o.out" 
    echo $(grep "SZS status" "$d/results/$3.$o.out") 
    echo $(grep "error" "$d/results/$3.$o.out")
    printf "\n"
}

# $1 file name
# $2 strategy
run_three () {
    #Strategy

    #Note that mergesort/mset/lemma1 does not define a strategy in its file
    if [[ "$1" != *"mergesort/mset/lemma1"* ]] then
        run "vampire" "--decode $2" $1
        run "vampire_ind" "--decode $2" $1
    fi

    #Structural induction
    run "vampire" "--cores 0 --mode portfolio -sched struct_induction"  $1
    run "vampire_ind" "--cores 0 --mode portfolio -sched struct_induction" $1

    #Induction
    run "vampire" "--cores 0 --mode portfolio -sched induction"  $1
    run "vampire_ind" "--cores 0 --mode portfolio -sched induction" $1
}

for i in $(find . -name "*.smt2"); do
    f="${i//$d}"
    f="${f:1:-5}"
    # Getting strategy from file
    if [[ "$f" != *"mergesort/mset/lemma1"* ]] then
        s=$(cat $i | grep "lrs")
        s=${s:2}
        s="${s%:*}_1200"
        run_three $f $s
    else
        run_three $f "" 
    fi
    done


echo "For more information on individual results, check the results directory"
