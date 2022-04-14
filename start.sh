#!/bin/bash

OUTPUT_PATH="$1"
PROJECT_DIR="$(pwd)"

if [[ ! -d venv ]]; then
	python3 -m virtualenv venv
fi

source ./venv/bin/activate
python3 -m pip install -U pip
python3 -m pip install -r requirements.txt

if [[ -z "$OUTPUT_PATH" ]]; then
	python3 "$PROJECT_DIR/src/core/mig_synthesis.py"
else
	python3 "$PROJECT_DIR/src/core/mig_synthesis.py" -o "$OUTPUT_PATH"
fi
