"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Defer basic', function () {
    const testopt = ["statement/defer", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('defer matches', function () {
        it('expected 5i', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("5i");
        });
    });
});

