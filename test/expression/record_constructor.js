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
            expect(invokeExecutionOn(jsmain)).to.eql("{}");
        });
    });
});

describe('Three record', function () {
    const testopt = ["expression/record_constructor", "record_3int"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('{f=1i, g=2i, h=3i}', function () {
        it('expected {f=1i, g=2i, h=3i}', function () {
            expect(invokeExecutionOn(jsmain, "2i")).to.eql("{f=1i, g=2i, h=3i}");
        });
    });
    describe('{f=1i, g=-1i, h=3i}', function () {
        it('expected {f=1i, g=-1i, h=3i}', function () {
            expect(invokeExecutionOn(jsmain, "-1i")).to.eql("{f=1i, g=-1i, h=3i}");
        });
    });
});

describe('Nested record', function () {
    const testopt = ["expression/record_constructor", "record_nested"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('{f=1i, g={h=true}}', function () {
        it('expected {f=1i, g={h=true}}', function () {
            expect(invokeExecutionOn(jsmain, "1i")).to.eql("{f=1i, g={h=true}}");
        });
    });
    describe('{f=-1i, g={h=true}}', function () {
        it('expected {f=-1i, g={h=true}}', function () {
            expect(invokeExecutionOn(jsmain, "-1i")).to.eql("{f=-1i, g={h=true}}");
        });
    });
});

describe('Infer record', function () {
    const testopt = ["expression/record_constructor", "record_infer"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('{f=0i, g=none}', function () {
        it('expected {f=0i, g=none}', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("{f=0i, g=none}");
        });
    });
    describe('{f=5i, g=true}', function () {
        it('expected {f=5i, g=true}', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("{f=5i, g=true}");
        });
    });
});

