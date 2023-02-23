"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Set', function () {
    const testopt = ["stdlib/list/set_remove_insert", "set_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 0, 5', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [], 0, 5)).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}, 5, 5', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 5, 5)).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}, 1, 4', function () {
        it('expected List{1, 4, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 1, 4)).to.eql([1, 4, 3]);
        });
    });
    describe('List{1, 2, 3}, 0, 4', function () {
        it('expected List{4, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 0, 4)).to.eql([4, 2, 3]);
        });
    });
});

describe('List Insert', function () {
    const testopt = ["stdlib/list/set_remove_insert", "insert_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 0, 5', function () {
        it('expected List{5}', function () {
            expect(invokeExecutionOn(jsmain, [], 0, 5)).to.eql([5]);
        });
    });
    describe('List{}, 1, 5', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [], 1, 5)).to.includes("Failed precondition");
        });
    });
    describe('List{}, 2, 5', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [], 2, 5)).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}, 5, 5', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 5, 5)).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}, 1, 4', function () {
        it('expected List{1, 4, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 1, 4)).to.eql([1, 4, 2, 3]);
        });
    });
    describe('List{1, 2, 3}, 0, 4', function () {
        it('expected List{4, 1, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 0, 4)).to.eql([4, 1, 2, 3]);
        });
    });
    describe('List{1, 2, 3}, 3, 4', function () {
        it('expected List{1, 2, 3, 4}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 3, 4)).to.eql([1, 2, 3, 4]);
        });
    });
});

describe('List Remove', function () {
    const testopt = ["stdlib/list/set_remove_insert", "remove_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 0', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [], 0)).to.include("Failed precondition");
        });
    });
    describe('List{1, 2, 3}, 5', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 5)).to.includes("Failed precondition");
        });
    });
    describe('List{1, 2, 3}, 1', function () {
        it('expected List{1, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 1)).to.eql([1, 3]);
        });
    });
    describe('List{1, 2, 3}, 0', function () {
        it('expected List{2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 0)).to.eql([2, 3]);
        });
    });
    describe('List{1, 2, 3}, 2', function () {
        it('expected List{1, 2}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 2)).to.eql([1, 2]);
        });
    });
});
