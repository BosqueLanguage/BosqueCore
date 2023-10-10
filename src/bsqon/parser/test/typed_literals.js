"use strict";

const { runall } = require("./runner");

const stringoftests = {
    name: "StringOf Parses",
    succeed: true,
    tests: [
    ]
};

const stringoferrortests = {
    name: "StringOf Errors",
    succeed: false,
    tests: [
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
        ['2_Foo', '2_Foo', 'missing numeric specifier']
    ]
};

const typedtests_string = {
    name: "Typed String Parses",
    succeed: true,
    tests: [
    ]
};

const typederrortests_string = {
    name: "Typed String Errors",
    succeed: false,
    tests: [
    ]
};

const typedtests_misc = {
    name: "Typed Misc Parses",
    succeed: true,
    tests: [
        ['true_Flag', 'true_Flag', 'true_Flag']
    ]
};

const typederrortests_misc = {
    name: "Typed Misc Errors",
    succeed: false,
    tests: [
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
