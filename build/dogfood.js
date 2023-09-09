"use strict";

const { exec } = require("child_process");
const path = require("path");
const fs = require("fs");
const glob = require("glob");

const builddir = __dirname;
const tscdir = path.dirname(__dirname);

let doneemitimpl = false;
let donesmtimpl = false

let haderror = false;

function unescapeString(str) {
    let ret = "";
    for (let i = 0; i < str.length; i++) {
        if (str[i] === "%") {
            i++;
            if (str[i] === "%") {
                ret += "%";
            }
            else if (str[i] === "n") {
                ret += "\n";
                i++;
            }
            else if (str[i] === "r") {
                ret += "\r";
                i++;
            }
            else if (str[i] === "t") {
                ret += "\t";
                i++;
            }
            else if (str[i] === "b") {
                ret += "`";
                i++;
            }
            else if (str[i] === "q") {
                ret += "\"";
                i++;
            }
            else {
                //should be a u 
                i++;
                const epos = str.indexOf(";", i);
                const hex = str.substring(i, epos);
                ret += String.fromCharCode(parseInt(hex, 16));
                i = epos;
            }
        }
        else {
            ret += str[i];
        }
    }

    return ret;
}

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
const smtfile = path.join("./bsqbin", "doit.smt2");

const srcdirs = ["./src/transformer/tree_ir/", "./src/transformer/rewriter/", "./src/transformer/solver/", "./src/transformer/solver/smt_emitter/"];
let srcfiles = [];
for(let i = 0; i < srcdirs.length; ++i) {
    srcfiles.push(...glob.sync(path.join(srcdirs[i], "*.bsq")));
}

exec(`node ./bin/runtimes/javascript/cmd.js --namespace=SMTEmit --outdir ./bsqbin ${srcfiles.join(" ")}`, {cwd: tscdir}, (err, stdout, stderr) => {
    donesmtimpl = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done build compiler pass..."); 
});

exec(`node ./bin/transformer/solver.js --outfile ${outfile} ${srcfile}`, {cwd: tscdir}, (err, stdout, stderr) => {
    if(err !== null) {
        donesmtimpl = true;
        doneop(true, err + stderr + stdout); 
    }
    else {
        doneop(false, "done emit ir..."); 
        
        exec(`deno run --allow-all ./bsqbin/_main.ts --input=${outfile}`, {cwd: tscdir}, (smterr, smtstdout, smtstderr) => {
            donesmtimpl = true;
            try {
                fs.writeFileSync(smtfile, unescapeString(smtstdout.slice(1, -1)));
            }
            catch(e) {
                smterr = e;
            }

            doneop(smterr !== null, smterr !== null ? smterr + smtstderr + smtstdout : "done emit smt...");
        });
    }
});