"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List pushBack basic', function () {
    const testopt = ["stdlib/list/push_ops", "push_back"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 5', function () {
        it('expected List{5}', function () {
            expect(invokeExecutionOn(jsmain, [], 5)).to.eql([5]);
        });
    });
    describe('List{1, 2, 3}, 5', function () {
        it('expected List{1, 2, 3, 5}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 5)).to.eql([1, 2, 3, 5]);
        });
    });
});

describe('List pushFront basic', function () {
    const testopt = ["stdlib/list/push_ops", "push_front"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 5', function () {
        it('expected List{5}', function () {
            expect(invokeExecutionOn(jsmain, [], 5)).to.eql([5]);
        });
    });
    describe('List{1, 2, 3}, 5', function () {
        it('expected List{5, 1, 2, 3}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3], 5)).to.eql([5, 1, 2, 3]);
        });
    });
});
