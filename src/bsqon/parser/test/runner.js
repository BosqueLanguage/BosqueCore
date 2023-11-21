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
        if(result.includes(output)) {
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

exports.runall = runall;
