"use strict";

const path = require("path");
const fsextra = require("fs-extra");
const {execSync} = require("child_process");

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
    execSync(`node ${genbin} --outdir ${dstdir} ${srcdir}`);
}

function invokeExecutionOnDirect(jsmain, ...args) {
    return execSync(`node ${jsmain}`, {input: args.join(" ") + "\n", timeout: 30000}).toString().trim();
}

const retry = 2;
function invokeExecutionOn(jsmain, ...args) {
    let tries = 0;
    while (tries < retry) {
        try {
            return execSync(`deno run ${jsmain}`, { input: args.join(" ") + "\n", timeout: 30000 }).toString().trim();
        }
        catch (e) {
            tries++;
        }
    }

    return "[--ERROR--]";
}

function cleanTest(dstdir) {
    fsextra.removeSync(dstdir);
}

module.exports = {
    generatePaths, codegen, invokeExecutionOn, cleanTest
};
