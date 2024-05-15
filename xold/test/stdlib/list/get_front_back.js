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
            expect(invokeExecutionOn(jsmain, "List{}")).to.includes("Failed precondition List");
        });
    });
    describe('List{1n, 2n, 3n}', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, "List{1n, 2n, 3n}")).to.eql("1n");
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
            expect(invokeExecutionOn(jsmain, "List{}")).to.includes("Failed precondition List");
        });
    });
    describe('List{1n, 2n, 3n}', function () {
        it('expected 3n', function () {
            expect(invokeExecutionOn(jsmain, "List{1n, 2n, 3n}")).to.eql("3n");
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
            expect(invokeExecutionOn(jsmain, "List{}", "0n")).to.includes("Failed precondition List");
        });
    });
    describe('List{1i, 2i, 3i}, 0n', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "0n")).to.eql("1i");
        });
    });
    describe('List{1i, 2i, 3i}, 1n', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "1n")).to.eql("2i");
        });
    });
    describe('List{1i, 2i, 3i}, 2n', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "2n")).to.eql("3i");
        });
    });
    describe('List{1i, 2i, 3i}, 3n', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "3n")).to.includes("Failed precondition List");
        });
    });
    describe('List{1i, 2i, 3i}, 100n', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "100n")).to.includes("Failed precondition List");
        });
    });
});
