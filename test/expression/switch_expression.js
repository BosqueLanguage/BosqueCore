"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Switch Expression basic', function () {
    const testopt = ["expression/switch_expression", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(none)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(0);
        });
    });
    describe('switch(0)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(1);
        });
    });
    describe('switch(7)', function () {
        it('expected 2', function () {
            expect(invokeExecutionOn(jsmain, 7)).to.eql(2);
        });
    });
});

describe('Switch Expression no default', function () {
    const testopt = ["expression/switch_expression", "no_default"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(true)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql(0);
        });
    });
    describe('switch(false)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql(1);
        });
    });
});

describe('Switch Expression infer', function () {
    const testopt = ["expression/switch_expression", "infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(none)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(0);
        });
    });
    describe('switch(5)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(1);
        });
    });
});

describe('Switch Expression binder general', function () {
    const testopt = ["expression/switch_expression", "binder"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(none)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(0);
        });
    });
    describe('switch(5)', function () {
        it('expected 6', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(6);
        });
    });
});


describe('Switch Expression binder option', function () {
    const testopt = ["expression/switch_expression", "binder_option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(nothing)', function () {
        it('expected 0,', function () {
            expect(invokeExecutionOn(jsmain, ["Nothing", null])).to.eql(0);
        });
    });
    describe('switch(something(5))', function () {
        it('expected 6', function () {
            expect(invokeExecutionOn(jsmain, ["Something<Nat>", 5])).to.eql(6);
        });
    });
});
