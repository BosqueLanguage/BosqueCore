"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Field direct', function () {
    const testopt = ["expression/field_access", "direct"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('v.g', function () {
        it('expected [1i, 3i]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([1, 3]);
        });
    });
});

describe('Field virtual concept', function () {
    const testopt = ["expression/field_access", "virtual_concept"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('vaccess g (1i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(1);
        });
    });
    describe('vaccess g (3i)', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(3);
        });
    });
});


describe('Field virtual union', function () {
    const testopt = ["expression/field_access", "virtual_union"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('vaccess g (1i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(1);
        });
    });
    describe('vaccess g (3i)', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(3);
        });
    });
});


