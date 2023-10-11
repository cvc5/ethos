#!/usr/bin/env bash

# This reads exactly one function call from stdin, and returns
# true if it is as expected:
# (
# 42
# )

count=0
while read -r line
    do
    if (( count == 0 )) && [[ "$line" == "(" ]]; then
        count=$((count+1))
    elif (( count == 1 )) && [[ "$line" == "42" ]]; then
        count=$((count+1))
    elif (( count == 2 )) && [[ "$line" == ")" ]]; then
        echo "true"
        break
    else
        echo "false"
        break
    fi
done < /dev/stdin

