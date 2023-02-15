"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Logical !', function () {
    const testopt = ["expression/logical_not", "notop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('!true', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(false);
        });
    });
    describe('!false', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(true);
        });
    });
});

