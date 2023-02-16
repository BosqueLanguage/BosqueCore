"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Binary &&', function () {
    const testopt = ["expression/bin_logic", "andops"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('&& flavors', function () {
        it('expected [true, false, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, false, false]);
        });
    });
});

describe('Binary ||', function () {
    const testopt = ["expression/bin_logic", "orops"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('|| flavors', function () {
        it('expected [true, false, true]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, false, true]);
        });
    });
});

describe('Binary ==>', function () {
    const testopt = ["expression/bin_logic", "implyops"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('==> flavors', function () {
        it('expected [true, false, true]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, false, true]);
        });
    });
});

