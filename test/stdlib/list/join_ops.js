"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List join basic', function () {
    const testopt = ["stdlib/list/join_ops", "join_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected List{[2i, 2i], [3i, 2i], [3i, 3i]}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([[2, 2], [3, 2], [3, 3]]);
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
});

describe('List group basic', function () {
    const testopt = ["stdlib/list/join_ops", "group_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1, 2, 3}', function () {
        it('expected List{[1i, List<Int>{}], [2i, List{2i}], [3i, List{2i, 3i}]}', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 3])).to.eql([[1, []], [2, [2]], [3, [2, 3]]]);
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql([]);
        });
    });
});
