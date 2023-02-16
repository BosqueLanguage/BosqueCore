"use strict";

const path = require("path");
const fsextra = require("fs-extra");
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

function cmdescape(str) {
    return str.replace(/[&<>'"]/g, 
    tag => ({
        '&': '&amp;',
        '<': '&lt;',
        '>': '&gt;',
        "'": '&#39;',
        '"': '&quot;'
      }[tag]));
}

function invokeExecutionOn(jsmain, ...args) {
    const rr = execFileSync(`node`, [jsmain, ...(args.map((vv) => "'" + cmdescape(JSON.stringify(vv)) + "'"))]).toString();
    if(rr.startsWith("error -- ")) {
        return rr;
    }
    else {
        return JSON.parse(rr);
    }
}

function cleanTest(dstdir) {
    fsextra.removeSync(dstdir);
}

module.exports = {
    generatePaths, codegen, invokeExecutionOn, cleanTest
};
