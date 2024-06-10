"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('None/Nothing/Boolean', function () {
    const testopt = ["expression/literal", "none_nothing_bool"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('main()', function () {
        it('expected [none, nothing, true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[none, nothing, true, false]");
        });
    });
});

describe('Integral', function () {
    const testopt = ["expression/literal", "integrals"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('main()', function () {
        it('expected [0n, 10n, -3i, 0i, 1i, 0N, 10N, -3I, 0I, 1I]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[0n, 10n, -3i, 0i, 1i, 0N, 10N, -3I, 0I, 1I]");
        });
    });
});

describe('Float', function () {
    const testopt = ["expression/literal", "rational_fp"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('main()', function () {
        it('expected [0.0f, 1.1f, -3.01d, 5.0d, 0/2R, 2/1R, 5/2R]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[0.0f, 1.1f, -3.01d, 5.0d, 0R, 2R, 5/2R]");
        });
    });
});

describe('String', function () {
    const testopt = ["expression/literal", "strings"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('main()', function () {
        it('expected ["hello", "", ascii{"hello"}, ascii{""}]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql('["hello", "", ascii{"hello"}, ascii{""}]');
        });
    });
});
