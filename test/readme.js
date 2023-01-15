"use strict";

const expect = require("chai").expect;

const path = require("path");
const fsextra = require("fs-extra");
const execcmd = require("child_process").execFileSync;

const proj_root = path.join(__dirname, "../");
const genbin = path.join(proj_root, "bin/runtimes/javascript/cmd.js")

function codegen(testopt, done) {
  try {
    const srcdir = path.join(proj_root, "test", testopt) + "/*";
    const dstdir = path.join(proj_root, "build", testopt);

    fsextra.ensureDirSync(dstdir);
    execcmd(`node`, [genbin, srcdir]);
  }
  catch (ex) {
    return false;
  }

  return true;
}

function invokeExecutionOn(...args) {
  try {
    const jsmain = path.join(proj_root, "build", testopt, "Main.js");
    execcmd(`node`, [jsmain, ...args]);
  }
  catch (ex) {
    return false;
  }

  return true;
}

describe('Readme', function () {
  describe('add2(3, 4)', function () {
    it('expected pass', function () {

      expect([1, 2, 3]).to.eql([1, -2, 3]);
    });
  });
});
