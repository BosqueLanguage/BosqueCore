"use strict";

const expect = require("chai").expect;

const path = require("path");
const fsextra = require("fs-extra");
const { json } = require("stream/consumers");
const execFileSync = require("child_process").execFileSync;

const proj_root = path.join(__dirname, "../");
const genbin = path.join(proj_root, "bin/runtimes/javascript/cmd.js")

function codegen(srcdir, dstdir) {
  fsextra.ensureDirSync(dstdir);
  execFileSync(`node`, [genbin, "--output", dstdir, srcdir]);
}

function invokeExecutionOn(jsmain, ...args) {
  const rr = execFileSync(`node`, [jsmain, ...args]);
  return JSON.parse(rr);
}

describe('Readme Add', function () {
  const testopt = "readme_add";
  const srcdir = path.join(proj_root, "test/bsqsrc", testopt) + ".bsq";
  const dstdir = path.join(proj_root, "build", testopt);
  const jsmain = path.join(proj_root, "build", testopt, "Main.js");

  before(function () {
    codegen(srcdir, dstdir);
  });

  after(function() {
    fsextra.removeSync(dstdir);
  });

  describe('main()', function () {
    it('expected 7n', function () {
      expect(invokeExecutionOn(jsmain, "main")).to.eql(7n);
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
