"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Tuple basic', function () {
    const testopt = ["expression/tuple_access", "access_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('t.0', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("1i");
        });
    });
    describe('t.1', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("2i");
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
            expect(invokeExecutionOn(jsmain, "true")).to.eql("2i");
        });
    });
    describe('t.1', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("3i");
        });
    });
});


describe('Record basic', function () {
    const testopt = ["expression/record_access", "access_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('r.f', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("1i");
        });
    });
    describe('r.g', function () {
        it('expected 2i', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("2i");
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
            expect(invokeExecutionOn(jsmain, "true")).to.eql("2i");
        });
    });
    describe('r.q', function () {
        it('expected 3i', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("3i");
        });
    });
});

