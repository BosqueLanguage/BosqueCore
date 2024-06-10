"use strict;"

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../../codeproc.js");

describe('List map basic', function () {
    const testopt = ["stdlib/list/map_project", "map_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{2i, 3i, 4i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{2i, 3i, 4i}");
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
});

describe('List map idx basic', function () {
    const testopt = ["stdlib/list/map_project", "map_idx_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{1i, 3i, 5i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{1i, 3i, 5i}");
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
});

describe('List map new type', function () {
    const testopt = ["stdlib/list/map_project", "map_new_type"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{1i, none, 3i}");
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
});

describe('List project basic', function () {
    const testopt = ["stdlib/list/map_project", "project_basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, 2i, 3i}', function () {
        it('expected List{2i, none, 4i]', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 2i, 3i}")).to.eql("List{2i, none, 4i}");
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
    describe('List{1i, 4i, 2i}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 4i, 2i}")).to.includes("Failed precondition");
        });
    });
});

describe('List project boxed', function () {
    const testopt = ["stdlib/list/map_project", "project_boxed"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List{1i, none, 3i}', function () {
        it('expected List{"two", "none", "three"}', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, none, 3i}")).to.eql('List{"two", "none", "three"}');
        });
    });
    describe('List{}', function () {
        it('expected List{}', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("List{}");
        });
    });
    describe('List{7i, none}', function () {
        it('expected err', function () {
            expect(invokeExecutionOn(jsmain, "List{7i, none}")).to.includes("Failed precondition");
        });
    });
});

