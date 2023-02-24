"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('NBody', function () {
    const testopt = ["small_apps/nbody", "nbody"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('init', function () {
        it('expected value', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(-0.16907516382852444);
        });
    });
    describe('process 1', function () {
        it('expected value', function () {
            expect(invokeExecutionOn(jsmain, 1)).to.eql(-0.16907495402506748);
        });
    });
    describe('process 3', function () {
        it('expected value', function () {
            expect(invokeExecutionOn(jsmain, 3)).to.eql(-0.1690745314240226);
        });
    });
});

