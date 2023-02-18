"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Assert basic', function () {
    const testopt = ["statement/assert", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process ok', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(true);
        });
    });
    describe('process fail', function () {
        it('expected fail', function () {
            expect(invokeExecutionOn(jsmain, false)).to.includes("error -- Assert");
        });
    });
});

