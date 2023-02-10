"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Logical /\\', function () {
    const testopt = ["expression/logical_and_or", "logical_and"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('and flavors', function () {
        it('expected [true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, false]);
        });
    });
});

describe('Logical \\/', function () {
    const testopt = ["expression/logical_and_or", "logical_or"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('or flavors', function () {
        it('expected [true, false]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([true, false]);
        });
    });
});

