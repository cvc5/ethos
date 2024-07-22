#!/bin/bash

ETHOS_SIG_DIR=/space/ajreynol/cvc5-ajr/proofs/eo/cpc

gcc -O2 -o drat-trim drat-trim.c
cp drat-trim $ETHOS_SIG_DIR/rules/drat/drat-trim
