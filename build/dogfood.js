"use strict";

const { exec } = require("child_process");
const path = require("path");

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
const outfile = path.join("./bsqbin", "ir.json");

exec("node ./bin/runtimes/javascript/cmd.js --fileasm --namespace=SMTEmit --outdir ./bsqbin ./src/transformer/tree_ir/*.bsq ./src/transformer/rewriter/*.bsq ./src/transformer/solver/*.bsq ./src/transformer/solver/smt_emitter/*.bsq", {cwd: tscdir}, (err, stdout, stderr) => {
    donesmtimpl = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done build compiler pass..."); 
});

exec(`node ./bin/runtimes/javascript/emit.js --outfile ${outfile} ${srcfile}`, {cwd: tscdir}, (err, stdout, stderr) => {
    donesmtimpl = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done emit ir..."); 
});