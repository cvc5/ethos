#!/bin/bash

CVC=ajr-cvc5
ALFC=~/alfc/build/src/alfc

echo "=== Generate with cvc5 $@"
$CVC --dump-proofs --proof-format=alf $@ > temp.txt
tail -n +2 "temp.txt" > proof.smt2
echo "=== End generate with cvc5"

$ALFC proof.smt2
