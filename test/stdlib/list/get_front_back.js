"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Front', function () {
    const testopt = ["stdlib/list/get_front_back", "front"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [])).to.includes("error -- Failed precondition List");
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql(1);
        });
    });
});

describe('List Back', function () {
    const testopt = ["stdlib/list/get_front_back", "back"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [])).to.includes("error -- Failed precondition List");
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected 3', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql(3);
        });
    });
});

describe('List Get', function () {
    const testopt = ["stdlib/list/get_front_back", "get"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [], 0)).to.includes("error -- Failed precondition List");
        });
    });
    describe('List{1, 2, 3}, 0', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 0)).to.eql(1);
        });
    });
    describe('List{1, 2, 3}, 1', function () {
        it('expected 2', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 1)).to.eql(2);
        });
    });
    describe('List{1, 2, 3}, 2', function () {
        it('expected 3', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 2)).to.eql(3);
        });
    });
    describe('List{1, 2, 3}, 3', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 3)).to.includes("error -- Failed precondition List");
        });
    });
    describe('List{1, 2, 3}, 100', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 100)).to.includes("error -- Failed precondition List");
        });
    });
});
