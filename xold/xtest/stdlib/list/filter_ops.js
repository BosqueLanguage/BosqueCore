"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List filter basic', function () {
    const testopt = ["stdlib/list/filter_ops", "filter_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.eql("List{}");
        });
    });
    describe('List{1i, 2i, 0i, 4i}', function () {
        it('expected List{2i, 4i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 0i, 4i}")).to.eql("List{2i, 4i}");
        });
    });
});

describe('List filterIdx basic', function () {
    const testopt = ["stdlib/list/filter_ops", "filter_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0i, 0i, 0i}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{0i, 0i, 0i}")).to.eql("List{}");
        });
    });
    describe('List{1i, 3i, 0i, 4i}', function () {
        it('expected List{3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 3i, 0i, 4i}")).to.eql("List{3i}");
        });
    });
    describe('List{1i, 0i, 0i, 4i}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 0i, 0i, 4i}")).to.eql("List{}");
        });
    });
});

describe('List filterType basic', function () {
    const testopt = ["stdlib/list/filter_ops", "filtertype_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{3i, none, 1i}', function () {
        it('expected List{3i, 1i}', function () {
            expect(invokeExecutionOn(jsmain, "List{3i, none, 1i}")).to.eql("List{3i, 1i}");
        });
    });
    describe('List{3i, 2i, 0i}', function () {
        it('expected List{3i, 2i, 0i}', function () {
            expect(invokeExecutionOn(jsmain, "List{3i, 2i, 0i}")).to.eql("List{3i, 2i, 0i}");
        });
    });
});
