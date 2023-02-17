"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Var Assign basic', function () {
    const testopt = ["statement/var_assignment", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process', function () {
        it('expected 3', function () {
            expect(invokeExecutionOn(jsmain)).to.eql(3);
        });
    });
});
