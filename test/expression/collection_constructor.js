"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('List constructor', function () {
    const testopt = ["expression/collection_constructor", "list_constructor"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('List<Int>{}', function () {
        it('expected List<Int>{}', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql("List{}");
        });
    });
    describe('List<Int>{1i, 2i, 3i}', function () {
        it('expected List<Int>{1i, 2i, 3i}', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql("List{1i, 2i, 3i}");
        });
    });
});

describe('Map constructor', function () {
    const testopt = ["expression/collection_constructor", "map_constructor"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Map<Int, String>{}', function () {
        it('expected Map<Int, String>{}', function () {
            expect(invokeExecutionOn(jsmain, true)).to.eql("Map{}");
        });
    });
    describe('Map<Int, String>{1i => "one", 2i => "two"}', function () {
        it('expected Map<Int, String>{1i => "one", 2i => "two"}', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql('Map{1i => "one", 2i => "two"}');
        });
    });
});

describe('Map specific constructor', function () {
    const testopt = ["expression/collection_constructor", "map_constructor_short"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Map<Int, String>{}', function () {
        it('expected error', function () {
            expect(invokeExecutionOn(jsmain, true)).to.contain("Duplicate keys in Map construction");
        });
    });
    describe('Map<Int, String>{1i => "one", 2i => "two"}', function () {
        it('expected Map<Int, String>{1i => "one", 2i => "two"}', function () {
            expect(invokeExecutionOn(jsmain, false)).to.eql('Map{1i => "one", 2i => "two"}');
        });
    });
});

