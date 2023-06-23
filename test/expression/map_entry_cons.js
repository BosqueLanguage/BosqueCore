"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Single MapEntry constructor', function () {
    const testopt = ["expression/map_entry_cons", "from_exps"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('From exps and infer return', function () {
        it('expected [MapEntry<Int, Int>{1i, 2i}, MapEntry<Int, Int|None>{3i, 4i}]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[MapEntry<Int, Int>{1i, 2i}, MapEntry<Int, Int|None>{3i, 4i}]");
        });
    });
});

describe('Collection MapEntry Constructor', function () {
    const testopt = ["expression/map_entry_cons", "from_collection"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('As Collection Entries', function () {
        it('expected Map{1i => "one", 2i => "two"}', function () {
            expect(invokeExecutionOn(jsmain)).to.eql('Map{1i => "one", 2i => "two"}');
        });
    });
});


