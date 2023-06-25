"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest, cmdStringEscape} = require("../codeproc.js");

describe('Temp constructor', function () {
    const testopt = ["expression/entity_indirect", "temp"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Fahrenheit{32i}', function () {
        it('expected Fahrenheit{32i}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("32i_Fahrenheit");
        });
    });
});

describe('PartID literal constructor', function () {
    const testopt = ["expression/entity_indirect", "pid_literal"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('"ABC-123"_PartID', function () {
        it('expected "ABC-123"_PartID', function () {
            expect(invokeExecutionOn(jsmain)).to.eql('"ABC-123"_PartID');
        });
    });
});

describe('PartID constructor', function () {
    const testopt = ["expression/entity_indirect", "pid"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('PartID{"X-52"} fails', function () {
        it('expected PartID{"X-52"} fails', function () {
            expect(invokeExecutionOn(jsmain, '"X-52"')).to.contain("Assertion failed");
        });
    });
    describe('PartID{"ABC-123"}', function () {
        it('expected PartID{"ABC-123"}', function () {
            expect(invokeExecutionOn(jsmain, '"ABC-123"')).to.eql('"ABC-123"_PartID');
        });
    });
});

describe('BoolOp constructor', function () {
    const testopt = ["expression/entity_indirect", "boolop"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('NotOp{5n LConst{1n, false}}', function () {
        it('expected NotOp{5n, LConst{1n, false}}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("NotOp{5n, LConst{1n, false}}");
        });
    });
});
