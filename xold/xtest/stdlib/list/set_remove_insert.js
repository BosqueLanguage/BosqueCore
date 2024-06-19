"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Set', function () {
    const testopt = ["stdlib/list/set_remove_insert", "set_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 0n, 5i', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "0n", "5i")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}, 5n, 5i', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "5n", "5i")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}, 1n, 4i', function () {
        it('expected List{1i, 4i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "1n", "4i")).to.eql("List{1i, 4i, 3i}");
        });
    });
    describe('List{1i, 2i, 3i}, 0n, 4i', function () {
        it('expected List{4i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "0n", "4i")).to.eql("List{4i, 2i, 3i}");
        });
    });
});

describe('List Insert', function () {
    const testopt = ["stdlib/list/set_remove_insert", "insert_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 0n, 5i', function () {
        it('expected List{5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "0n", "5i")).to.eql("List{5i}");
        });
    });
    describe('List{}, 1n, 5i', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "1n", "5i")).to.includes("Failed precondition");
        });
    });
    describe('List{}, 2n, 5i', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "2n", "5i")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}, 5n, 5i', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "5n", "5i")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}, 1n, 4i', function () {
        it('expected List{1i, 4i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "1n", "4i")).to.eql("List{1i, 4i, 2i, 3i}");
        });
    });
    describe('List{1i, 2i, 3i}, 0n, 4i', function () {
        it('expected List{4i, 1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "0n", "4i")).to.eql("List{4i, 1i, 2i, 3i}");
        });
    });
    describe('List{1i, 2i, 3i}, 3n, 4i', function () {
        it('expected List{1i, 2i, 3i, 4i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "3n", "4i")).to.eql("List{1i, 2i, 3i, 4i}");
        });
    });
});

describe('List Remove', function () {
    const testopt = ["stdlib/list/set_remove_insert", "remove_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 0n', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "0n")).to.include("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}, 5n', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "5n")).to.includes("Failed precondition");
        });
    });
    describe('List{1i, 2i, 3i}, 1n', function () {
        it('expected List{1i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "1n")).to.eql("List{1i, 3i}");
        });
    });
    describe('List{1i, 2i, 3i}, 0n', function () {
        it('expected List{2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "0n")).to.eql("List{2i, 3i}");
        });
    });
    describe('List{1i, 2i, 3i}, 2n', function () {
        it('expected List{1i, 2i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "2n")).to.eql("List{1i, 2i}");
        });
    });
});
