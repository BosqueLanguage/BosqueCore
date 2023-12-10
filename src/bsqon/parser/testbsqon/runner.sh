#!/usr/bin/env bash

set -uo pipefail

# get the directory of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# get the test data directory
TEST_DATA_DIR="$( realpath "$DIR/tests" )"

# get the bsqon executable
BSQON_EXE="$( realpath "$DIR/../../../../build/output/bsqon" )"

# get the metadata generation script
METADATA_GEN_SCRIPT="$( realpath "$DIR/../../../../bin/frontend/generate_metadata.js" )"

echo $DIR
echo $TEST_DATA_DIR

