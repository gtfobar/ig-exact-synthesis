#!/bin/bash

INPUT_DIR="input/$1"
OUTPUT_DIR="results/$1"
let "COMPLEXITY_TO_CHECK=$1 - 1"
TIMEOUT="$2"

for file in $(find ${INPUT_DIR}/*); do
    ./start.sh -i "$file" -c "$COMPLEXITY_TO_CHECK" -d "$OUTPUT_DIR" -t "$TIMEOUT" -j 7
done
