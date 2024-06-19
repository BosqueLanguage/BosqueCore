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
            expect(invokeExecutionOn(jsmain, "List{3i, none, 1i}")).to.includes("cannot convert value");
        });
    });
    describe('List{3i, 2i, 0i}', function () {
        it('expected List{3i, 2i, 0i}', function () {
            expect(invokeExecutionOn(jsmain, "List{3i, 2i, 0i}")).to.eql("List{3i, 2i, 0i}");
        });
    });
});
