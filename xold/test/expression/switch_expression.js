"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Switch Expression basic', function () {
    const testopt = ["expression/switch_expression", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(none)', function () {
        it('expected 0i,', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0i");
        });
    });
    describe('switch(0i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("1i");
        });
    });
    describe('switch(7i)', function () {
        it('expected "2i', function () {
            expect(invokeExecutionOn(jsmain, "7i")).to.eql("2i");
        });
    });
});

describe('Switch Expression no default', function () {
    const testopt = ["expression/switch_expression", "no_default"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(true)', function () {
        it('expected 0n,', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql("0n");
        });
    });
    describe('switch(false)', function () {
        it('expected 1n', function () {
            expect(invokeExecutionOn(jsmain, "false")).to.eql("1n");
        });
    });
});

describe('Switch Expression infer', function () {
    const testopt = ["expression/switch_expression", "infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(none)', function () {
        it('expected 0i,', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0i");
        });
    });
    describe('switch(5)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("1i");
        });
    });
});

describe('Switch Expression binder general', function () {
    const testopt = ["expression/switch_expression", "binder"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(none)', function () {
        it('expected 0n,', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0n");
        });
    });
    describe('switch(5)', function () {
        it('expected 6n', function () {
            expect(invokeExecutionOn(jsmain, "5n")).to.eql("6n");
        });
    });
});


describe('Switch Expression binder option', function () {
    const testopt = ["expression/switch_expression", "binder_option"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('switch(nothing)', function () {
        it('expected 0n', function () {
            expect(invokeExecutionOn(jsmain, "nothing")).to.eql("0n");
        });
    });
    describe('switch(something(5))', function () {
        it('expected 6n', function () {
            expect(invokeExecutionOn(jsmain, "something(5n)")).to.eql("6n");
        });
    });
});
