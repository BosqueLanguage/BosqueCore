"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List zip basic', function () {
    const testopt = ["stdlib/list/zip_ops", "zip_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{2i, 3i, 4i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql('List{[1i, "one"], [2i, "two"], [3i, "three"]}');
        });
    });
    describe('List{1i, 2i}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i}")).to.includes("Failed precondition");
        });
    });
});

describe('List zipwith basic', function () {
    const testopt = ["stdlib/list/zip_ops", "zipwith_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{1i, 3i, 5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{true, false, true}");
        });
    });
    describe('List{1i, 2i}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i}")).to.includes("Failed precondition");
        });
    });
});
