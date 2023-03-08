"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Contains basic', function () {
    const testopt = ["stdlib/list/contains", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.eql(false);
        });
    });
    describe('List{none, 3}', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, [null, 3])).to.eql(true);
        });
    });
    describe('List{}', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql(false);
        });
    });
});

