"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List map basic', function () {
    const testopt = ["stdlib/list/map_project", "map_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected [2, 3, 4]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([2, 3, 4]);
        });
    });
    describe('List{}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
});

describe('List map idx basic', function () {
    const testopt = ["stdlib/list/map_project", "map_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected [1, 3, 5]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([1, 3, 5]);
        });
    });
    describe('List{}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
});

describe('List map new type', function () {
    const testopt = ["stdlib/list/map_project", "map_new_type"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected [1, none, 3]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([["Int", 1], ["None", null], ["Int", 3]]);
        });
    });
    describe('List{}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
});

describe('List project basic', function () {
    const testopt = ["stdlib/list/map_project", "project_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, none, 3}', function () {
        it('expected [1, none, 3]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([["Int", 2], ["None", null], ["Int", 4]]);
        });
    });
    describe('List{}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
    describe('List{1, 4, 2}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [1, 4, 2])).to.includes("Failed precondition");
        });
    });
});

describe('List project boxed', function () {
    const testopt = ["stdlib/list/map_project", "project_boxed"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, none, 3}', function () {
        it('expected ["two", "none", "three"]', function () {
            expect(invokeExecutionOn(jsmain, [["Int", 1], ["None", null], ["Int", 3]])).to.eql(["two", "none", "three"]);
        });
    });
    describe('List{}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
    describe('List{7, none}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [["Int", 7], ["None", null]])).to.includes("Failed precondition");
        });
    });
});

