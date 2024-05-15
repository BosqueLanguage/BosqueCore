"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List pushBack basic', function () {
    const testopt = ["stdlib/list/push_ops", "push_back"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 5i', function () {
        it('expected List{5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "5i")).to.eql("List{5i}");
        });
    });
    describe('List{1i, 2i, 3i}, 5i', function () {
        it('expected List{1i, 2i, 3i, 5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "5i")).to.eql("List{1i, 2i, 3i, 5i}");
        });
    });
});

describe('List pushFront basic', function () {
    const testopt = ["stdlib/list/push_ops", "push_front"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{}, 5i', function () {
        it('expected List{5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{}", "5i")).to.eql("List{5i}");
        });
    });
    describe('List{1i, 2i, 3i}, 5i', function () {
        it('expected List{5i, 1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}", "5i")).to.eql("List{5i, 1i, 2i, 3i}");
        });
    });
});
