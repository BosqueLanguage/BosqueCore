"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Result union', function () {
    const testopt = ["expression/special_constructor", "union_result"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0n)', function () {
        it('expected union none', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("none");
        });
    });
    describe('process(5n)', function () {
        it('expected union 5n', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("5n");
        });
    });
});

describe('Result direct', function () {
    const testopt = ["expression/special_constructor", "direct_result"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0n)', function () {
        it('expected err(none)', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("err(none)");
        });
    });
    describe('process(5n)', function () {
        it('expected ok(5n)', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("ok(5n)");
        });
    });
});

describe('Result coerce', function () {
    const testopt = ["expression/special_constructor", "coerce_result"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0n)', function () {
        it('expected err(none)', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("err(none)");
        });
    });
    describe('process(1n)', function () {
        it('expected ok(true)', function () {
            expect(invokeExecutionOn(jsmain, "1n")).to.eql("ok(true)");
        });
    });
    describe('process(5n)', function () {
        it('expected ok(5n)', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("ok(5n)");
        });
    });
});

describe('Option direct', function () {
    const testopt = ["expression/special_constructor", "direct_option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0n)', function () {
        it('expected nothing', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("nothing");
        });
    });
    describe('process(5n)', function () {
        it('expected something(5n)', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("something(5n)");
        });
    });
});

describe('Option coerce', function () {
    const testopt = ["expression/special_constructor", "coerce_option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0n)', function () {
        it('expected nothing', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("nothing");
        });
    });
    describe('process(1n)', function () {
        it('expected something(true)', function () {
            expect(invokeExecutionOn(jsmain, "1n")).to.eql("something(true)");
        });
    });
    describe('process(5n)', function () {
        it('expected ok(5n)', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("something(5n)");
        });
    });
});
