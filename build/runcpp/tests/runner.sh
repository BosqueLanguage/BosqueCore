#!/bin/bash

SCRIPT_DIR="$(dirname $0)"

bins=(
    "$SCRIPT_DIR/postree_tests"
    "$SCRIPT_DIR/gc_basic_tests"
)

for bin in "${bins[@]}"; do
	"$bin"
done

