"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Tuple basic', function () {
    const testopt = ["expression/tuple_access", "access_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('t.0', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(1);
        });
    });
    describe('t.1', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(2);
        });
    });
});

describe('Tuple nested', function () {
    const testopt = ["expression/tuple_access", "access_nested"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('t.0.1', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(2);
        });
    });
    describe('t.1', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(3);
        });
    });
});


describe('Record basic', function () {
    const testopt = ["expression/record_access", "access_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('r.f', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(1);
        });
    });
    describe('r.g', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(2);
        });
    });
});

describe('Record nested', function () {
    const testopt = ["expression/record_access", "access_nested"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('r.f.g', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(2);
        });
    });
    describe('r.q', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(3);
        });
    });
});

