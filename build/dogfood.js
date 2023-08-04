"use strict";

const { exec } = require("child_process");
const path = require("path");
const glob = require("glob");

const builddir = __dirname;
const tscdir = path.dirname(__dirname);

let doneemitimpl = false;
let donesmtimpl = false

let haderror = false;

function doneop(iserror, msg) {
    haderror = haderror || iserror;

    process.stdout.write(msg + "\n");
    if(doneemitimpl && donesmtimpl) {
        if(!haderror) {
            process.stdout.write("done!\n");
            process.exit(0);
        }
        else {
            process.stdout.write("error!\n");
            process.exit(1);
        }
    }
}

const srcfile = process.argv[2];
const outfile = path.join("./bsqbin", "ir.bsqon");

const srcdirs = ["./src/transformer/tree_ir/", "./src/transformer/rewriter/", "./src/transformer/solver/", "./src/transformer/solver/smt_emitter/"];
let srcfiles = [];
for(let i = 0; i < srcdirs.length; ++i) {
    srcfiles.push(...glob.sync(path.join(srcdirs[i], "*.bsq")));
}

exec(`node ./bin/runtimes/javascript/cmd.js --namespace=SMTEmit --outdir ./bsqbin ${srcfiles.join(" ")}`, {cwd: tscdir}, (err, stdout, stderr) => {
    donesmtimpl = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done build compiler pass..."); 
});

exec(`node ./bin/runtimes/javascript/emit.js --outfile ${outfile} ${srcfile}`, {cwd: tscdir}, (err, stdout, stderr) => {
    donesmtimpl = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done emit ir..."); 
});