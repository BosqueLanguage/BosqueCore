"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Empty record', function () {
    const testopt = ["expression/record_constructor", "record_empty"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('{}', function () {
        it('expected {}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql({});
        });
    });
});

describe('Three record', function () {
    const testopt = ["expression/record_constructor", "record_3int"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('{f=1, g=2, h=3}', function () {
        it('expected {f=i1, g=2i, h=3i}', function () {
            expect(invokeExecutionOn(jsmain, 2)).to.eql({f:1, g:2, h:3});
        });
    });
    describe('{f=1, g=-1, h=3}', function () {
        it('expected {f=i1, g=-1i, h=3i}', function () {
            expect(invokeExecutionOn(jsmain, -1)).to.eql({f:1, g:-1, h:3});
        });
    });
});

describe('Nested record', function () {
    const testopt = ["expression/record_constructor", "record_nested"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('{f=1, g={h=true}}', function () {
        it('expected {f=i1, g={h=true}}', function () {
            expect(invokeExecutionOn(jsmain, 1)).to.eql({f:1, g:{h:true}});
        });
    });
    describe('{f=-1, g={h=true}}', function () {
        it('expected {f=-1i, g={h=true}}', function () {
            expect(invokeExecutionOn(jsmain, -1)).to.eql({f:-1, g:{h:true}});
        });
    });
});

describe('Infer record', function () {
    const testopt = ["expression/record_constructor", "record_infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process(0)', function () {
        it('expected {f=0, g=none}', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql({f:0, g:null});
        });
    });
    describe('process(5)', function () {
        it('expected {f=5, g=true}', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql({f:5, g:true});
        });
    });
});

