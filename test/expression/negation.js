"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Negation', function () {
    const testopt = ["expression/negation", "simpleneg"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Negate 1i, 1.0f, 3/2R, 10I_Foo', function () {
        it('expected [-1i, -1.0f, "-3/2R", -10I_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "1i", "1.0f", "3/2R", "10I_Foo")).to.eql("[-1i, -1.0f, -3/2R, -10I_Foo]");
        });
    });
    describe('Negate -1i, -1.0f, -3/2R, -10I_Foo', function () {
        it('expected [1i, 1.0f, 3/2R, 10I_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "-1i", "-1.0f", "-3/2R", "-10I_Foo")).to.eql("[1i, 1.0f, 3/2R, 10I_Foo]");
        });
    });
    describe('Negate 0i, 0.0f, 0R, 0I_Foo', function () {
        it('expected [0i, 0.0f, 0R, 0I_Foo]', function () {
            expect(invokeExecutionOn(jsmain, "0i", "0.0f", "0R", "0I_Foo")).to.eql("[0i, 0.0f, 0R, 0I_Foo]");
        });
    });
});
