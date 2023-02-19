"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Size/Empty basic', function () {
    const testopt = ["stdlib/list/size_empty", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}', function () {
        it('expected [0, true]', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([0, true]);
        });
    });
    describe('List{1, 2, 3}', function () {
        it('expected [3, false]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([3, false]);
        });
    });
});

