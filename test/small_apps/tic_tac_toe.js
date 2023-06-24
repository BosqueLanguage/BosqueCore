"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Tic-Tac-Toe', function () {
    const testopt = ["small_apps/tic_tac_toe", "tic_tac_toe"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process two moves', function () {
        it('expected ok(none)', function () {
            expect(invokeExecutionOn(jsmain, "List{[0n, 0n, PlayerMark::x], [0n, 1n, PlayerMark::o]}")).to.eql("ok(none)");
        });
    });
    describe('process winner', function () {
        it('expected ok(x)', function () {
            expect(invokeExecutionOn(jsmain, "List{[0n, 0n, PlayerMark::x], [0n, 1n, PlayerMark::o], [1n, 0n, PlayerMark::x], [1n, 1n, PlayerMark::o], [2n, 0n, PlayerMark::x]}")).to.eql("ok(PlayerMark::x)");
        });
    });
    describe('process err invalid move', function () {
        it('expected invalid', function () {
            expect(invokeExecutionOn(jsmain, "List{[0n, 0n, PlayerMark::x], [0n, 0n, PlayerMark::o]}")).to.eql('err("Cell is already occupied")');
        });
    });
    describe('process err already won', function () {
        it('expected already won', function () {
            expect(invokeExecutionOn(jsmain, "List{[0n, 0n, PlayerMark::x], [0n, 1n, PlayerMark::o], [1n, 0n, PlayerMark::x], [1n, 1n, PlayerMark::o], [2n, 0n, PlayerMark::x], [0n, 2n, PlayerMark::o]}")).to.eql('err("A player already won")');
        });
    });
});

