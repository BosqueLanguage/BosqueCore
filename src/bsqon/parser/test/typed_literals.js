"use strict";

const { runall } = require("./runner");

const stringoftests = {
    name: "StringOf Parses",
    succeed: true,
    tests: [
        ['"foo"Bar', '"foo"Bar', '"foo"Bar'],
        ['\'foo\'Bar', '\'foo\'Bar', '\'foo\'Bar']
    ]
};

const stringoferrortests = {
    name: "StringOf Errors",
    succeed: false,
    tests: [
        ['"foo"bar', '"foo"bar', 'syntax error']
    ]
};

const typedtests_numbers = {
    name: "Typed Numeric Parses",
    succeed: true,
    tests: [
        ['2i_Foo', '2i_Foo', '2i_Foo'],
        ['2R_Foo', '2R_Foo', '2R_Foo'],
        ['2.0f_Foo<Int>', '2.0f_Foo<Int>', '2.0f_Foo<Int>']
    ]
};

const typederrortests_numbers = {
    name: "Typed Numeric Errors",
    succeed: false,
    tests: [
        ['2iFoo', '2iFoo', 'syntax error'],
        ['2_Foo', '2_Foo', 'Missing numeric specifier']
    ]
};

const typedtests_string = {
    name: "Typed String Parses",
    succeed: true,
    tests: [
        ['"foo"_Bar', '"foo"_Bar', '"foo"_Bar'],
        ['\'foo\'_Bar', '\'foo\'_Bar', '\'foo\'_Bar'],
        ['`file://mark.com`FS', '`file://mark.com`FS', '`file://mark.com`FS'],
        ['g`file://mark.com/**`FS', 'g`file://mark.com/**`FS', 'g`file://mark.com/**`FS'],
        ['f`mark.com`FS', 'f`mark.com`FS', 'f`mark.com`FS'],
    ]
};

const typederrortests_string = {
    name: "Typed String Errors",
    succeed: false,
    tests: [
        ['"x"foo', '"x"foo', 'syntax error'],
    ]
};

const typedtests_misc = {
    name: "Typed Misc Parses",
    succeed: true,
    tests: [
        ['true_Flag', 'true_Flag', 'true_Flag'],
        ['false_Flag', 'false_Flag', 'false_Flag'],
        ['2023-10-05T20:06:24Z_Event', '2023-10-05T20:06:24Z_Event', '2023-10-05T20:06:24Z_Event'],
        ['uuid4{550e8400-e29b-41d4-a716-446655440000}_State', 'uuid4{550e8400-e29b-41d4-a716-446655440000}_State', 'uuid4{550e8400-e29b-41d4-a716-446655440000}_State']
    ]
};

const typederrortests_misc = {
    name: "Typed Misc Errors",
    succeed: false,
    tests: [
        ['none_Flag', 'none_Flag', 'Cannot have a typedecl of none or nothing']
    ]
};


runall([
    stringoftests,
    stringoferrortests,
    typedtests_numbers,
    typederrortests_numbers,
    typedtests_string,
    typederrortests_string,
    typedtests_misc,
    typederrortests_misc
]);
