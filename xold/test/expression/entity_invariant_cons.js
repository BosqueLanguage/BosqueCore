"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Percentage constructor', function () {
    const testopt = ["expression/entity_invariant", "percentage"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Percentage{101n}', function () {
        it('expected invariant failure', function () {
            expect(invokeExecutionOn(jsmain, "101n_Percentage")).to.contain("Failed invariant");
        });
    });
    describe('Percentage{99n}', function () {
        it('expected 99_Percentage', function () {
            expect(invokeExecutionOn(jsmain, "99n_Percentage")).to.eql("99n_Percentage");
        });
    });
});

describe('Qux constructor', function () {
    const testopt = ["expression/entity_invariant", "qux"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Qux{"", 3i, 10i} fails', function () {
        it('expected invariant fails', function () {
            expect(invokeExecutionOn(jsmain, '""', "3i", "10i")).to.contain("Failed invariant");
        });
    });
    describe('Qux{"bob", 0i, 10i} fails', function () {
        it('expected invariant fails', function () {
            expect(invokeExecutionOn(jsmain, '"bob"', "0i", "10i")).to.contain("Failed invariant");
        });
    });
    describe('Qux{"bob", 4i, 2i} fails', function () {
        it('expected invariant fails', function () {
            expect(invokeExecutionOn(jsmain, '"bob"', "4i", "2i")).to.contain("Failed invariant");
        });
    });
    describe('Qux{"bob", 4i, 10i} ok', function () {
        it('expected Qux{"bob", 4i, 10i}', function () {
            expect(invokeExecutionOn(jsmain, '"bob"', "4i", "10i")).to.eql('Qux{"bob", 4i, 10i}');
        });
    });
});
