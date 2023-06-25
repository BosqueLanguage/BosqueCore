"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Append', function () {
    const testopt = ["stdlib/list/append_ops", "append"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "List{}")).to.eql("List{}");
        });
    });
    describe('List{1i, 2i, 3i}, List{}', function () {
        it('expected List{1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "List{}")).to.eql("List{1i, 2i, 3i}");
        });
    });
    describe('List{}, List{4i, 5i}', function () {
        it('expected List{4i, 5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "List{4i, 5i}")).to.eql("List{4i, 5i}");
        });
    });
    describe('List{1i, 2i, 3i}, List{4i, 5i}', function () {
        it('expected List{1i, 2i, 3i, 4i, 5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "List{4i, 5i}")).to.eql("List{1i, 2i, 3i, 4i, 5i}");
        });
    });
});

describe('List Prepend', function () {
    const testopt = ["stdlib/list/append_ops", "prepend"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "List{}")).to.eql("List{}");
        });
    });
    describe('List{1i, 2i, 3i}, List{}', function () {
        it('expected List{1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "List{}")).to.eql("List{1i, 2i, 3i}");
        });
    });
    describe('List{}, List{4i, 5i}', function () {
        it('expected List{4i, 5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "List{4i, 5i}")).to.eql("List{4i, 5i}");
        });
    });
    describe('List{1i, 2i, 3i}, List{4i, 5i}', function () {
        it('expected List{4i, 5i, 1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "List{4i, 5i}")).to.eql("List{4i, 5i, 1i, 2i, 3i}");
        });
    });
});
