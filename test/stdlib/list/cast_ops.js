"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List castType basic', function () {
    const testopt = ["stdlib/list/cast_ops", "cast_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{3i, none, 1i}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, [3, null, 1])).to.includes("error -- cannot convert value");
        });
    });
    describe('List{3i, 2i, 0i}', function () {
        it('expected [3, 2, 0]', function () {
            expect(invokeExecutionOn(jsmain, [3, 2, 0])).to.eql([3, 2, 0]);
        });
    });
});
