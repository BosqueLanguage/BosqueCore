"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List Append', function () {
    const testopt = ["stdlib/list/append_ops", "append"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, [], [])).to.eql([]);
        });
    });
    describe('List{1, 2, 3}, List{}', function () {
        it('expected List{1, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], [])).to.eql([1, 2, 3]);
        });
    });
    describe('List{}, List{4, 5}', function () {
        it('expected List{4, 5}', function () {
            expect(invokeExecutionOn(jsmain, [], [4, 5])).to.eql([4, 5]);
        });
    });
    describe('List{1, 2, 3}, List{4, 5}', function () {
        it('expected List{1, 2, 3, 4, 5}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], [4, 5])).to.eql([1, 2, 3, 4, 5]);
        });
    });
});

describe('List Prepend', function () {
    const testopt = ["stdlib/list/append_ops", "prepend"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, [], [])).to.eql([]);
        });
    });
    describe('List{1, 2, 3}, List{}', function () {
        it('expected List{1, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], [])).to.eql([1, 2, 3]);
        });
    });
    describe('List{}, List{4, 5}', function () {
        it('expected List{4, 5}', function () {
            expect(invokeExecutionOn(jsmain, [], [4, 5])).to.eql([4, 5]);
        });
    });
    describe('List{1, 2, 3}, List{4, 5}', function () {
        it('expected List{4, 5, 1, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], [4, 5])).to.eql([4, 5, 1, 2, 3]);
        });
    });
});
