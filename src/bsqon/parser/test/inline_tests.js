"use strict";

const { execFileSync } = require("child_process");
const path = require("path");

const builddir = path.join(__dirname, "../../../../build");
const outexec = path.join(builddir, "output", "bsqon_parser");

let runcount = 0;
let failcount = 0;

function runSucceedingTest(testname, bsqon, output) {
    runcount++;
    process.stdout.write(`    running test ${testname}...`);
    try {
        const result = execFileSync(outexec, { input: bsqon }).toString().trim();
        if(result === output) {
            process.stdout.write(`passed\n`); 
        }
        else {
            process.stdout.write(`test ${testname} failed: expected ${output}, got ${result}\n`);
            failcount++;
        }
    }
    catch(err) {
        console.log(`test ${testname} failed: expected ${output}, got error ${err}`);
        failcount++;
    }
}

function runSucceedingTestGroup(groupname, tests) {
    process.stdout.write(`running test group ${groupname}...\n`);
    for(let i = 0; i < tests.length; ++i) {
        const test = tests[i];
        const testname = test[0];
        const bsqon = test[1];
        const output = test[2];

        runSucceedingTest(testname, bsqon, output);
    }
    process.stdout.write(`done test group ${groupname}\n\n`);
}

function runParseErrorTest(testname, bsqon, output) {
    runcount++;
    process.stdout.write(`    running test ${testname}...`);
    try {
        const result = execFileSync(outexec, { input: bsqon }).toString().trim();
        if(result.startsWith(output)) {
            process.stdout.write(`passed\n`); 
        }
        else {
            process.stdout.write(`test ${testname} failed: expected ${output}, got ${result}\n`);
            failcount++;
        }
    }
    catch(err) {
        console.log(`test ${testname} failed: expected ${output}, got error ${err}`);
        failcount++;
    }
}

function runParseErrorTestGroup(groupname, tests) {
    process.stdout.write(`running (parse error) test group ${groupname}...\n`);
    for(let i = 0; i < tests.length; ++i) {
        const test = tests[i];
        const testname = test[0];
        const bsqon = test[1];
        const output = test[2];

        runParseErrorTest(testname, bsqon, output);
    }
    process.stdout.write(`done test group ${groupname}\n\n`);
}

function runall(alltests) {
    for(let i = 0; i < alltests.length; ++i) {
        const testgroup = alltests[i];
        const groupname = testgroup.name;
        const tests = testgroup.tests;

        if(testgroup.succeed) {
            runSucceedingTestGroup(groupname, tests);
        }
        else {
            runParseErrorTestGroup(groupname, tests);
        }
    }

    process.stdout.write(`ran ${runcount} tests`);
    if (failcount === 0) {
        process.stdout.write(` -- all passed!\n`);
    }
    else {
        process.stdout.write(` -- ${failcount} failed!\n`);
    }
}

const literaltests_numbers = {
    name: "Literal Numeric Parses",
    succeed: true,
    tests: [
        ['none', 'none', 'none'],
        ['true', 'true', 'true'],
        ['false', 'false', 'false'],

        ['0n', '0n', '0n'],
        ['5n', '5n', '5n'],
    
        ['-1i', '-1i', '-1i'],
        ['1i', '1i', '1i'],
        ['+3i', '+3i', '+3i'],

        ['0N', '0N', '0N'],
        ['5N', '5N', '5N'],
    
        ['-1I', '-1I', '-1I'],
        ['1I', '1I', '1I'],
        ['+3I', '+3I', '+3I'],

        ['0R', '0R', '0R'],
        ['-1R', '-1R', '-1R'],
        ['1/1R', '1/1R', '1/1R'],
        ['+3/2R', '+3/2R', '+3/2R'],

        ['-1.0f', '-1.0f', '-1.0f'],
        ['1.0f', '1.0f', '1.0f'],
        ['+0.3f', '+0.3f', '+0.3f'],

        ['-1.0d', '-1.0d', '-1.0d'],
        ['1.0fd', '1.0d', '1.0d'],
        ['+0.3d', '+0.3d', '+0.3d'],

        ['-1', '-1', '-1'],
        ['1', '1', '1'],
        ['+3', '+3', '+3']
    ]
};

const literalerrortests_numbers = {
    name: "Literal Numeric Errors",
    succeed: false,
    tests: [
        ['00n', '00n', 'Leading zero'],
        ['-0n', '-0n', 'Zero cannot be negative'],
        ['-5n', '-5n', 'Cannot have negative natural number'],
    
        ['-01i', '-01i', 'Leading zero'],
        ['01i', '01i', 'Leading zero'],

        ['00N', '00N', 'Leading zero'],
        ['-5N', '-5N', 'Cannot have negative natural number'],
    
        ['01I', '01I', 'Leading zero'],
        ['+03I', '+03I', 'Leading zero'],

        ['01R', '01R', 'Leading zero'],
        ['+03/1R', '+03/1R', 'Leading zero'],
        ['1/0R', '1/0R', 'Zero as divisor'],

        ['-01.0f', '-01.0f', 'Leading zero'],
        ['.0f', '.0f', 'Leading decimal is not allowed'],
        ['00.3f', '00.3f', 'Redundant leading zero is not allowed'],

        ['-01.0d', '-01.0d', 'Leading zero'],
        ['.0d', '.0d', 'Leading decimal is not allowed'],
        ['00.3d', '00.3d', 'Redundant leading zero is not allowed'],

        ['-01', '-01', 'Leading zero'],
        ['01', '01', 'Leading zero'],
        ['00', '00', 'Leading zero'],

        ['-01.0', '-01.0', 'Leading zero'],
        ['00.3', '00.3', 'Redundant leading zero is not allowed']
    ]
};

const literaltests_strings = {
    name: "Literal String-like Parses",
    succeed: true,
    tests: [
        ['"none"', '"none"', '"none"'],
        ['"ok %q;"', '"ok %q;"', '"ok %q;"'],
        ['""', '""', '""'],

        ['ascii{"none"}', 'ascii{"none"}', 'ascii{"none"}'],
        ['ascii{"ok %q;"}', 'ascii{"ok %q;"}', 'ascii{"ok %q;"}'],
        ['ascii{""}', 'ascii{""}', 'ascii{""}']
    ]
};


const literalerrortests_strings = {
    name: "Literal String-like Errors",
    succeed: false,
    tests: [
        ['"ok', '"ok', 'Unclosed String'],

        ['ascii{"ok"', 'ascii{"ok"', 'Unclosed ASCIIString'],
        ['ascii{"ok}', 'ascii{"ok}', 'Unclosed ASCIIString'],
        ['ascii{"ok}"', 'ascii{"ok}"', 'Unclosed ASCIIString'],
    ]
};

runall([
    literaltests_numbers,
    literalerrortests_numbers,
    literaltests_strings,
    literalerrortests_strings
]);
