#!/bin/bash

PROJECT_DIR="$(pwd)"

source ./venv/bin/activate
python3 "$PROJECT_DIR/src/core/mig_synthesis.py" $@
