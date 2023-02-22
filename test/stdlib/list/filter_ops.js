"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List filter basic', function () {
    const testopt = ["stdlib/list/filter_ops", "filter_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.eql([]);
        });
    });
    describe('List{1, 2, 0, 4}', function () {
        it('expected [2, 4]', function () {
            expect(invokeExecutionOn(jsmain, [1, 2, 0, 4])).to.eql([2, 4]);
        });
    });
});

describe('List filterIdx basic', function () {
    const testopt = ["stdlib/list/filter_ops", "filter_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{0, 0, 0}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [0, 0, 0])).to.eql([]);
        });
    });
    describe('List{1, 3, 0, 4}', function () {
        it('expected [3]', function () {
            expect(invokeExecutionOn(jsmain, [1, 3, 0, 4])).to.eql([3]);
        });
    });
    describe('List{1, 0, 0, 4}', function () {
        it('expected []', function () {
            expect(invokeExecutionOn(jsmain, [1, 0, 0, 4])).to.eql([]);
        });
    });
});

describe('List filterType basic', function () {
    const testopt = ["stdlib/list/filter_ops", "filtertype_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{3i, none, 1i}', function () {
        it('expected [3, 1]', function () {
            expect(invokeExecutionOn(jsmain, [["Int", 3], ["None", null], ["Int", 1]])).to.eql([3, 1]);
        });
    });
    describe('List{3i, 2i, 0i}', function () {
        it('expected [3, 2, 0]', function () {
            expect(invokeExecutionOn(jsmain, [["Int", 3], ["Int", 2], ["Int", 0]])).to.eql([3, 2, 0]);
        });
    });
});
