#!/bin/bash

ALFC_SIG_DIR=/space/ajreynol/cvc5-ajr/proofs/alf

gcc -O2 -o drat-trim drat-trim.c
cp drat-trim $ALFC_SIG_DIR/rules/drat/drat-trim
