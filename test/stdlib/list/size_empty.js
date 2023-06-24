"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Size/Empty basic', function () {
    const testopt = ["stdlib/list/size_empty", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected [0n, true]', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("[0n, true]");
        });
    });
    describe('List{1n, 2n, 3n}', function () {
        it('expected [3n, false]', function () {
            expect(invokeExecutionOn(jsmain, "List{1n, 2n, 3n}")).to.eql("[3n, false]");
        });
    });
});

