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
            expect(invokeExecutionOn(jsmain, 0)).to.eql(null);
        });
    });
    describe('process(5n)', function () {
        it('expected union 5n', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(5);
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
            expect(invokeExecutionOn(jsmain, 0)).to.eql(["Result::Err<Nat, None>", null]);
        });
    });
    describe('process(5n)', function () {
        it('expected ok(5n)', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(["Result::Ok<Nat, None>", 5]);
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
            expect(invokeExecutionOn(jsmain, 0)).to.eql(["Result::Err<Bool|Nat, None>", null]);
        });
    });
    describe('process(1n)', function () {
        it('expected ok(true)', function () {
            expect(invokeExecutionOn(jsmain, 1)).to.eql(["Result::Ok<Bool|Nat, None>", ["Bool", true]]);
        });
    });
    describe('process(5n)', function () {
        it('expected ok(5n)', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(["Result::Ok<Bool|Nat, None>", ["Nat", 5]]);
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
            expect(invokeExecutionOn(jsmain, 0)).to.eql(["Nothing", null]);
        });
    });
    describe('process(5n)', function () {
        it('expected something(5n)', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(["Something<Nat>", 5]);
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
            expect(invokeExecutionOn(jsmain, 0)).to.eql(["Nothing", null]);
        });
    });
    describe('process(1n)', function () {
        it('expected something(true)', function () {
            expect(invokeExecutionOn(jsmain, 1)).to.eql(["Something<Bool|Nat>", ["Bool", true]]);
        });
    });
    describe('process(5n)', function () {
        it('expected ok(5n)', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(["Something<Bool|Nat>", ["Nat", 5]]);
        });
    });
});
