"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List join basic', function () {
    const testopt = ["stdlib/list/join_ops", "join_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{[2i, 2i], [3i, 2i], [3i, 3i]}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{[2i, 2i], [3i, 2i], [3i, 3i]}");
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
});

describe('List group basic', function () {
    const testopt = ["stdlib/list/join_ops", "group_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{[1i, List{}], [2i, List{2i}], [3i, List{2i, 3i}]}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{[1i, List{}], [2i, List{2i}], [3i, List{2i, 3i}]}");
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
});
