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

const literaltests = {
    name: "LiteralParses",
    succeed: true,
    tests: [
        ["none", "none", "none"],
        ["true", "true", "true"],
        ["false", "false", "false"],

        ["0n", "0n", "0n"],
        ["5n", "5n", "5n"],
    
        ["-1i", "-1i", "-1i"],
        ["1i", "1i", "1i"],
        ["+3i", "+3i", "+3i"],

        ["0N", "0N", "0N"],
        ["5N", "5N", "5N"],
    
        ["-1I", "-1I", "-1I"],
        ["1I", "1I", "1I"],
        ["+3I", "+3I", "+3I"],

        ["0R", "0R", "0R"],
        ["-1R", "-1R", "-1R"],
        ["1/1R", "1/1R", "1/1R"],
        ["+3/2R", "+3/2R", "+3/2R"],

        ["-1.0f", "-1.0f", "-1.0f"],
        ["1.0ff", "1.0f", "1.0f"],
        ["+0.3f", "+0.3f", "+0.3f"],

        ["-1.0d", "-1.0d", "-1.0d"],
        ["1.0fd", "1.0d", "1.0d"],
        ["+0.3d", "+0.3d", "+0.3d"]
    ]
};

const literalerrortests = {
    name: "LiteralParses",
    succeed: false,
    tests: [
        ["00n", "00n", "Leading zero"],
        ["-0n", "-0n", "Zero cannot be negative"],
        ["-5n", "-5n", "Cannot have negative natural number"],
    
        ["-01i", "-01i", "Leading zero"],
        ["01i", "01i", "Leading zero"],

        ["00N", "00N", "Leading zero"],
        ["-5N", "-5N", "Cannot have negative natural number"],
    
        ["01I", "01I", "Leading zero"],
        ["+03I", "+03I", "Leading zero"]
    ]
};

runall([
    literaltests,
    literalerrortests
]);
