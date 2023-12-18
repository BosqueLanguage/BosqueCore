#!/usr/bin/env bash

set -uo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

# get the directory of this script
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# get the test data directory
TEST_DATA_DIR="$( realpath "$DIR/tests" )"

# get the bsqon executable
BSQON_EXE="$( realpath "$DIR/../../../../build/output/bsqon" )"

# get the metadata generation script
METADATA_GEN_SCRIPT="$( realpath "$DIR/../../../../bin/frontend/generate_metadata.js" )"

########
# Setup the test directory as needed
TEST_OUTPUT_DIR="$( realpath "$DIR/../../../../build/test" )"
mkdir -p $TEST_OUTPUT_DIR/bsqon

TEST_OUTPUT_BSQON_DIR="$( realpath "$DIR/../../../../build/test/bsqon" )"

TOTAL_TESTS=0
PASSING_TESTS=0
FAILING_TESTS=0

function run_test 
{
    local TEST_FAILED=0

    mkdir -p $TEST_OUTPUT_BSQON_DIR/$1

    node $METADATA_GEN_SCRIPT --outdir $TEST_OUTPUT_BSQON_DIR/$1 $2 >/dev/null
    if [ $? -ne 0 ]; then
        echo "Failed to generate metadata for '$1'"
        TEST_FAILED=1
    fi

    if [ $TEST_FAILED -ne 0 ]; then
        $BSQON_EXE $TEST_OUTPUT_BSQON_DIR/$1/metadata.json $3 < <(echo $4) >$TEST_OUTPUT_BSQON_DIR/$1/output.bsqon
        if [ $? -ne 0 ]; then
            echo "Failed parsing of '$1'"
            TEST_FAILED=1
        fi
    fi

    if [ $TEST_FAILED -ne 0 ]; then
        diff $TEST_OUTPUT_BSQON_DIR/$1/output.bsqon <(echo $5) >$TEST_OUTPUT_BSQON_DIR/$1/result.diff
        if(($? != 0)); then
            echo "Parse output does not match expected '$1'"
            echo "--diff--"
            echo "$(<$TEST_OUTPUT_BSQON_DIR/$1/result.diff)"
            TEST_FAILED=1
        fi
    fi

    #delete the temp files and directory
    rm -f $TEST_OUTPUT_BSQON_DIR/$1/metadata.json $TEST_OUTPUT_BSQON_DIR/$1/output.bsqon $TEST_OUTPUT_BSQON_DIR/$1/result.diff
    rmdir $TEST_OUTPUT_BSQON_DIR/$1

    if [ $TEST_FAILED -eq 1 ]; then
        PASSING_TESTS=$((PASSING_TESTS+1))
        echo -e "Test '$1' ${RED}failed${NC}"
    else
        FAILING_TESTS=$((FAILING_TESTS+1))
        echo -e "Test '$1' ${GREEN}passed${NC}"
    fi
}


function run_test_list
{
    echo $3
    local AARGS TYPE VALUE EXPECTED
    for TEST in $3[@]; do
        TOTAL_TESTS=$((TOTAL_TESTS+1))

        AARGS=${TEST//;/}
        echo $AARGS

        TYPE=${AARGS[0]}
        VALUE=${AARGS[1]}
        EXPECTED=${AARGS[2]}

        echo $TYPE
        echo $VALUE
        echo $EXPECTED

        run_test $1 $2 $TYPE $VALUE $EXPECTED 
    done
}

#run_test "doit" "/home/mark/Desktop/doit/doit.bsqapi" "Int" "5i" "5i"

T_OPTS="Int ; 5i ; 5i # Int ; 3i ; 1i"
echo $T_OPTS

T_OPTS_ARR=(${T_OPTS//#/ })
for i in ${T_OPTS_ARR[@]}; do echo $i; done

run_test_list "doit" "/home/mark/Desktop/doit/doit.bsqapi" $T_OPTS_ARR
