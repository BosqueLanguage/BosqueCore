"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Contains basic', function () {
    const testopt = ["stdlib/list/contains", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.eql("false");
        });
    });
    describe('List{none, 3i}', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "List{none, 3i}")).to.eql("true");
        });
    });
    describe('List{}', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("false");
        });
    });
});

