"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Method virtual concept', function () {
    const testopt = ["expression/method_virtual", "calls_concept"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('call Qux', function () {
        it('expected [2i, 4i, 1i, 1i, 2i]', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("[2i, 4i, 1i, 1i, 2i]");
        });
    });
    describe('call Qax', function () {
        it('expected [2i, 4i, 1i, 4i, 2i]', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("[2i, 4i, 1i, 4i, 4i]");
        });
    });
});

describe('Method virtual union', function () {
    const testopt = ["expression/method_virtual", "calls_union"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('call Qux', function () {
        it('expected [2i, 4i, 1i, 1i, 2i]', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("[2i, 4i, 1i, 1i, 2i]");
        });
    });
    describe('call Qax', function () {
        it('expected [2i, 4i, 1i, 4i, 2i]', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("[2i, 4i, 1i, 4i, 4i]");
        });
    });
});



