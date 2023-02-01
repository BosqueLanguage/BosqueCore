"use strict";

const expect = require("chai").expect;

const path = require("path");
const fsextra = require("fs-extra");
const { json } = require("stream/consumers");
const execFileSync = require("child_process").execFileSync;

const proj_root = path.join(__dirname, "../");
const genbin = path.join(proj_root, "bin/runtimes/javascript/cmd.js")

function generatePaths(testopt) {
    return {
        srcfile: path.join(proj_root, "test/bsqsrc", ...testopt) + ".bsq",
        dstdir: path.join(proj_root, "build/test", ...testopt),
        jsmain: path.join(proj_root, "build/test", ...testopt, "_main_.mjs")
    }
}

function codegen(srcdir, dstdir) {
    fsextra.ensureDirSync(dstdir);
    execFileSync(`node`, [genbin, "--outdir", dstdir, srcdir]);
}

function invokeExecutionOn(jsmain, ...args) {
    const rr = execFileSync(`node`, [jsmain, ...(args.map((vv) => "'" + JSON.stringify(vv) + "'"))]).toString();
    if(rr.startsWith("error -- ")) {
        return rr;
    }
    else {
        return JSON.parse(rr);
    }
}

describe('Readme add2', function () {
    const testopt = ["readme", "add"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { fsextra.removeSync(dstdir); });

    describe('add2(3n, 4n)', function () {
        it('expected 7', function () {
            expect(invokeExecutionOn(jsmain, 3, 4)).to.eql(7);
        });
    });
    describe('add2(3n, 0n)', function () {
        it('expected 3', function () {
            expect(invokeExecutionOn(jsmain, 3, 0)).to.eql(3);
        });
    });
});

describe('Readme allPositive', function () {
    const testopt = ["readme", "allpositive"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { fsextra.removeSync(dstdir); });

    describe('allPositive([1, 3, 4])', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, [1, 3, 4])).to.eql(true);
        });
    });
    describe('allPositive([])', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql(true);
        });
    });
    describe('allPositive([1, -3, 4])', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, [1, -3, 4])).to.eql(false);
        });
    });
});


describe('Readme sign', function () {
    const testopt = ["readme", "sign"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { fsextra.removeSync(dstdir); });

    describe('sign(5)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(1);
        });
    });
    describe('sign(-5)', function () {
        it('expected -1', function () {
            expect(invokeExecutionOn(jsmain, -5)).to.eql(-1);
        });
    });
    describe('sign(0)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(0);
        });
    });
});

describe('Readme nominal generic', function () {
    const testopt = ["readme", "nominal_inv_generic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { fsextra.removeSync(dstdir); });

    describe('GenericGreeting', function () {
        it('expected ["hello world", "hello world"]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql(["hello world", "hello world"]);
        });
    });
});

describe('Readme nominal named', function () {
    const testopt = ["readme", "nominal_inv_named"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { fsextra.removeSync(dstdir); });

    describe('NamedGreeting', function () {
        it('expected "hello bob"', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("hello bob");
        });
    });
});


describe('Readme nominal err', function () {
    const testopt = ["readme", "nominal_inv_err"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { fsextra.removeSync(dstdir); });

    describe('Greeting Err', function () {
        it('expected invariant failure', function () {
            expect(invokeExecutionOn(jsmain)).to.contain("Failed invariant");
        });
    });
});
