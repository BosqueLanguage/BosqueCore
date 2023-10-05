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

        ['0', '0', '0'],
        ['3', '3', '3']
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

        ['-1', '-1', 'Cannot have sign'],
        ['+1', '+1', 'Cannot have sign'],
        ['01', '01', 'Leading zero'],
        ['00', '00', 'Leading zero'],
    ]
};

const literaltests_strings = {
    name: "Literal String-like Parses",
    succeed: true,
    tests: [
        ['"none"', '"none"', '"none"'],
        ['"ok%quote;"', '"ok%quote;"', '"ok%quote;"'],
        ['""', '""', '""'],
        ['unicode', '"🌵"', '"🌵"'],
        ['multiline', '"abc\ndef"', '"abc\ndef"'],
        ['multiline-set', '"abc\n  \\ def"', '"abc\n def"'],

        ['\'none\'', '\'none\'', '\'none\''],
        ['\'ok%tick;\'', '\'ok%tick;\'', '\'ok%tick;\''],
        ['\'\'', '\'\'', '\'\''],

        ['/none/', '/none/', '/none/'],
        ['/[0-9]+/', '/[0-9]+/', '/[0-9]+/'],
        ['/a b/', '/a b/', '/a b/'],

        ['`file://mark.com`', '`file://mark.com`', '`file://mark.com`'],
        ['`file://mark.com/**`g', '`file://mark.com/**`g', '`file://mark.com/**`g'],
        ['`mark.com`f', '`mark.com`f', '`mark.com`f'],
    ]
};

const literalerrortests_strings = {
    name: "Literal String-like Errors",
    succeed: false,
    tests: [
        ['"ok', '"ok', 'Unclosed String'],
        ['\'ok', '\'ok', 'Unclosed ASCIIString'],

        ['/ok', '/ok', 'Unclosed Regex'],
        ['newline', '/ok\n', 'Newline in Regex'],
        ['`file://mark.com', '`file://mark.com', 'Unclosed Path Item'],
        ['whitespace', '`file:// mark.com`', 'Whitespace in Path Item'],
    ]
};

const literaltests_times = {
    name: "Literal time Parses",
    succeed: true,
    tests: [
        ['DateTime', '2023-10-05T20:06:24@{Lexington, Ky}', '2023-10-05T20:06:24@{Lexington, Ky}'],
        ['UTCDateTime', '2023-10-05T20:06:24', '2023-10-05T20:06:24'],
        ['UTCDateTimeZ', '2023-10-05T20:06:24Z', '2023-10-05T20:06:24Z'],
        ['PlainDate"', '2023-10-05', '2023-10-05'],
        ['PlainTime', '20:06:24', '20:06:24'],
        ['Timestamp', '2023-10-05T20:06:24.000Z', '2023-10-05T20:06:24.000Z'],

        ['TickTime', '52t', '52t'],
        ['LogicalTime', '1l', '1l']
    ]
};

const literalerrortests_times = {
    name: "Literal time Errors",
    succeed: false,
    tests: [
        ['00t', '00t', 'Leading zero'],
        ['01t', '01t', 'Leading zero'],
        ['-5l', '-5l', 'Cannot have sign/negative time'],

        ['00l', '00l', 'Leading zero'],
        ['01l', '01l', 'Leading zero'],
        ['-5l', '-5l', 'Cannot have sign/negative time']
    ]
};

const literaltests_idhash = {
    name: "Literal ID and Hash Parses",
    succeed: true,
    tests: [
        ['bytebuff', '0x[000111f]', '0x[000111f]'],
        ['uuid4', 'uuid4{550e8400-e29b-41d4-a716-446655440000}', 'uuid4{550e8400-e29b-41d4-a716-446655440000}'],
        ['uuid7', 'uuid7{550e8400-e29b-41d4-a716-446655440000}', 'uuid7{550e8400-e29b-41d4-a716-446655440000}'],
        ['sha', 'sha3{a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a}', 'sha3{a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a}']
    ]
};

const literalerrortests_idhash = {
    name: "Literal ID and Hash Errors",
    succeed: false,
    tests: [
        ['bytebuff_value', '0x[000 111f]', 'Invalid buffer contents'],
        ['bytebuff_bracket', '0x[000111f', 'Missing close bracket'],
        ['uuid_value', 'uuid4{550e8400-e29b41d4-a716-446655440000}', 'Invalid UUID value'],
        ['uuid_bracket', 'uuid4{550e8400-e29b41d4-a716-446655440000', 'Missing close bracket'],
        ['uuid_value2', 'uuid7{550e8400-e29b-414P-a716-446655440000}', 'Invalid UUID value'],
        ['sha_value', 'sha3{a7ffc6f8bf1ed76651cX4756a061d662f580ff4de43b49fa82d80a4b80f8434a}', 'Invalid SHA3 value'],
        ['sha_value2', 'sha3{a7ffc6f8bf1ed766X1c4756a061d662f580ff4de43b49fa82d80a4b80f8434a}', 'Invalid SHA3 value'],
        ['sha_bracket', 'sha3{a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a', 'Missing close bracket']
    ]
};

const identifiertests = {
    name: "Name Parses",
    succeed: true,
    tests: [
        ['$src', '$src', '$src'],
        ['bob', 'bob', 'bob'],
        ['foo', 'foo', 'foo'],
        ['_$us', '_$us', '_$us'],
        ['Foo', 'Foo', 'Foo'],
        ['Foo::Bar', 'Foo::Bar', 'Foo::Bar']
    ]
};

const identifiererrortests = {
    name: "Name Errors",
    succeed: false,
    tests: [
        ['foo::bar', 'foo::bar', 'syntax error'],
        ['u$s', 'u$s', 'syntax error']
    ]
};

runall([
    literaltests_numbers,
    literalerrortests_numbers,
    literaltests_strings,
    literalerrortests_strings,
    literaltests_times,
    literalerrortests_times,
    literaltests_idhash,
    literalerrortests_idhash,
    identifiertests,
    identifiererrortests
]);
