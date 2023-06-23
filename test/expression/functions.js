"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Namespace functions', function () {
    const testopt = ["expression/functions", "functions_namespace"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('f(1i, 2i)', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("3i");
        });
    });
    describe('Main::f(1i, 2i)', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("3i");
        });
    });
});

describe('Type functions', function () {
    const testopt = ["expression/functions", "functions_type"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Foo:f(1i, 2i)', function () {
        it('expected -1i', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("-1i");
        });
    });
    describe('Main::f(1i, 2i)', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("3i");
        });
    });
});

