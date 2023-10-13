"use strict";

const { runall } = require("./runner");

const brackettests = {
    name: "Bracket Parses",
    succeed: true,
    tests: [
        ['[]', '[]', '[]'],
        ['[1i]', '[1i]', '[1i]'],
        ['[2i, 3n]', '[2i, 3n]', '[2i, 3n]'],
        ['[2i, 3n, true]', '[2i, 3n, true]', '[2i, 3n, true]']
    ]
};

const bracketerrortests = {
    name: "Bracket Errors",
    succeed: false,
    tests: [
        ['[}', '[}', 'syntax error'],
        ['[f=1i]', '[f=1i]', 'syntax error'],
        ['[1i, 0]', '[1i, 0]', '[1i, ^ERROR_EXP^]']
    ]
};

const bracetests = {
    name: "Brace Parses",
    succeed: true,
    tests: [
        ['{}', '{}', '{}'],
        ['{f=1i}', '{f=1i}', '{f=1i}'],
        ['{f=2i, g=3n}', '{f=2i, g=3n}', '{f=2i, g=3n}'],
        ['{f=2i, g=3n, h=true}', '{f=2i, g=3n, h=true}', '{f=2i, g=3n, h=true}'],
        ['{1i}', '{1i}', '{1i}'],
        ['{2i, 3n}', '{2i, 3n}', '{2i, 3n}'],
        ['{2i, 3n, true}', '{2i, 3n, true}', '{2i, 3n, true}'],
        ['{2i, g=3n}', '{2i, g=3n}', '{2i, g=3n}'],
    ]
};

const braceerrortests = {
    name: "Brace Errors",
    succeed: false,
    tests: [
        ['{]', '{]', 'syntax error'],
        ['{f:1i}', '{f:1i}', 'syntax error'],
        ['{:1i}', '{:1i}', 'syntax error'],
        ['{f=1i, g=0}', '{f=1i, g=0}', '{f=1i, g=^ERROR_EXP^}'],
        ['{1i, 0}', '{1i, 0}', '{1i, ^ERROR_EXP^}']
    ]
};

const typedtests = {
    name: "Typed Value Parses",
    succeed: true,
    tests: [
        ['Foo{3i}', 'Foo{3i}', 'Foo{3i}'],
        ['<Foo>{3i}', '<Foo>{3i}', 'Foo{3i}'],
        ['List<Int>{3i}', 'List<Int>{3i}', 'List<Int>{3i}'],
        ['<{f: Int}>{f=3i}', '<{f: Int}>{f=3i}', '<{f: Int}>{f=3i}'],
        ['<[Int, Bool]>[3i, false]', '<[Int, Bool]>[3i, false]', '<[Int, Bool]>[3i, false]'],
        ['List[3i]', 'List[3i]', 'List[3i]'],
        ['List<Int>[3i]', 'List<Int>[3i]', 'List<Int>[3i]'],
        ['<List<Int>>[3i]', '<List<Int>>[3i]', 'List<Int>[3i]'],
    ]
};

const typederrortests = {
    name: "Typed Value Errors",
    succeed: false,
    tests: [
        ['[Int, Bool][3i, false]', '[Int, Bool][3i, false]', 'syntax error'],
        ['<[Int, Bool][3i, false]', '<[Int, Bool][3i, false]', 'syntax error']
    ]
};

const mixedtests = {
    name: "Mixed Value Parses",
    succeed: true,
    tests: [
        ['{f=2i, g=[3n, 0i], h=true}', '{f=2i, g=[3n, 0i], h=true}', '{f=2i, g=[3n, 0i], h=true}'],
        ['[2i, {f=3n, g=0i}, true]', '[2i, {f=3n, g=0i}, true]', '[2i, {f=3n, g=0i}, true]'],
        ['[2i, Foo{3n, g=0i}, true]', '[2i, Foo{3n, g=0i}, true]', '[2i, Foo{3n, g=0i}, true]']
    ]
};

const mixederrortests = {
    name: "Mixed Value Errors",
    succeed: false,
    tests: [
        ['{f=2i, g=[3n, 0], h=true}', '{f=2i, g=[3n, 0], h=true}', '{f=2i, g=[3n, ^ERROR_EXP^], h=true}'],
        ['[2i, {f=3, g=0i}, true]', '[2i, {f=3, g=0i}, true]', '[2i, {f=^ERROR_EXP^, g=0i}, true]']
    ]
};

runall([
    brackettests,
    bracketerrortests,
    bracetests,
    braceerrortests,
    typedtests,
    typederrortests,
    mixedtests,
    mixederrortests
]);
