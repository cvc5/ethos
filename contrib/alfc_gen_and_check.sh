#!/bin/bash

CVC=cvc5
ETHOS=~/ethos/build/src/ethos

echo "=== Generate with cvc5 $@"
$CVC --dump-proofs --proof-format=cpc $@ > temp.txt
tail -n +2 "temp.txt" > proof.smt2
echo "=== End generate with cvc5"

$ETHOS proof.smt2
