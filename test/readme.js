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
    srcfile: path.join(proj_root, "test/bsqsrc", testopt) + ".bsq",
    dstdir: path.join(proj_root, "build/test", testopt),
    jsmain: path.join(proj_root, "build/test", testopt, "Main.mjs")
  }
}

function codegen(srcdir, dstdir) {
  fsextra.ensureDirSync(dstdir);
  execFileSync(`node`, [genbin, "--outdir", dstdir, srcdir]);
}

function invokeExecutionOn(jsmain, ...args) {
  const rr = execFileSync(`node`, [jsmain, ...args]);
  return JSON.parse(rr);
}

describe('Readme Add', function () {
  const testopt = "readme_add";
  const { srcfile, dstdir, jsmain } = generatePaths(testopt);

  before(function () {
    codegen(srcfile, dstdir);
  });

  after(function() {
    //fsextra.removeSync(dstdir);
  });

  describe('main()', function () {
    it('expected 7n', function () {
      expect(invokeExecutionOn(jsmain)).to.eql(7);
    });
  });

/*
  describe('add2(3, 4)', function () {
    it('expected 7n', function (done) {
      expect(invokeExecutionOn(done, 3, 4)).to.eql(7);
    });
  });
*/
});
