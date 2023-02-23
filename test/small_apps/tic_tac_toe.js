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
            expect(invokeExecutionOn(jsmain, [[0, 0, "Main::PlayerMark::x"], [0, 1, "Main::PlayerMark::o"]])).to.eql(["Result::Ok<Main::PlayerMark|None, String>", ["None", null]]);
        });
    });
    describe('process winner', function () {
        it('expected ok(x)', function () {
            expect(invokeExecutionOn(jsmain, [[0, 0, "Main::PlayerMark::x"], [0, 1, "Main::PlayerMark::o"], [1, 0, "Main::PlayerMark::x"], [1, 1, "Main::PlayerMark::o"], [2, 0, "Main::PlayerMark::x"]])).to.eql(["Result::Ok<Main::PlayerMark|None, String>", ["Main::PlayerMark", "Main::PlayerMark::x"]]);
        });
    });
    describe('process err invalid move', function () {
        it('expected invalid', function () {
            expect(invokeExecutionOn(jsmain, [[0, 0, "Main::PlayerMark::x"], [0, 0, "Main::PlayerMark::o"]])).to.eql(["Result::Err<Main::PlayerMark|None, String>", "Cell is already occupied"]);
        });
    });
    describe('process err already won', function () {
        it('expected won', function () {
            expect(invokeExecutionOn(jsmain, [[0, 0, "Main::PlayerMark::x"], [0, 1, "Main::PlayerMark::o"], [1, 0, "Main::PlayerMark::x"], [1, 1, "Main::PlayerMark::o"], [2, 0, "Main::PlayerMark::x"], [0, 2, "Main::PlayerMark::o"]])).to.eql(["Result::Err<Main::PlayerMark|None, String>", "A player already won"]);
        });
    });
});

