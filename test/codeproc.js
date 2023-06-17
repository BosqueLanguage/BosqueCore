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
        jsmain: path.join(proj_root, "build/test", ...testopt, "_main.ts")
    }
}

function codegen(srcdir, dstdir) {
    fsextra.ensureDirSync(dstdir);
    execFileSync(`node`, [genbin, "--outdir", dstdir, srcdir]);
}

function cmdescape(str) {
    return str.replace(/[&<>'"\n]/g, 
    tag => ({
        '&': '&amp;',
        '<': '&lt;',
        '>': '&gt;',
        "'": '&#39;',
        '"': '&quot;',
        '\n': '&#10;'
      }[tag]));
}

function invokeExecutionOn(jsmain, ...args) {
    const rr = execFileSync(`deno`, ["run", jsmain, ...(args.map((vv) => "'" + vv + "'"))]).toString();
    if(rr.startsWith("error -- ")) {
        return rr;
    }
    else {
        return JSON.parse(rr);
    }
}

function cleanTest(dstdir) {
    //fsextra.removeSync(dstdir);
}

module.exports = {
    generatePaths, codegen, invokeExecutionOn, cleanTest, cmdescape
};
