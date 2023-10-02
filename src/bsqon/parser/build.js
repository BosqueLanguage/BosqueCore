"use strict";

const fsx = require("fs-extra");
const { exec } = require("child_process");
const path = require("path");

const builddir = path.join(__dirname, "../../../build");
const srcdir = path.join(__dirname, "lb");

const outexec = path.join(builddir, "output");
const outobj = path.join(builddir, "output", "obj");

fsx.ensureDirSync(outexec);
fsx.ensureDirSync(outobj);

let doneyy = false;
let donetest = false;
let doneexport = false;

let haderror = false;

function doneop(iserror, msg) {
    haderror = haderror || iserror;

    process.stdout.write(msg + "\n");
    if(doneyy && donetest && doneexport) {
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

console.log(srcdir);
const mode = process.argv[2] || "debug";

exec(`bison -d${mode === "debug" ? " -Wcex" : ""} bsqon.y && flex bsqon.l`, {cwd: srcdir}, (err, stdout, stderr) => {
    doneyy = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done parser gen..."); 

    exec(`gcc -Og -DEXPORT -o ${outobj}/bsqon.tab.o -c bsqon.tab.c && gcc -Og -DEXPORT -o ${outobj}/lex.yy.o -c lex.yy.c`, {cwd: srcdir}, (oerr, ostdout, ostderr) => {
        donetest = true;
        doneop(oerr !== null, oerr !== null ? oerr + ostderr + ostdout : "done obj file build...");
    });

    exec(`gcc -O1 -g -ggdb -o ${outexec}/bsqon_parser bsqon_ast.c bsqon.tab.c lex.yy.c -lfl`, {cwd: srcdir}, (eerr, estdout, estderr) => {
        doneexport = true;
        doneop(eerr !== null, eerr !== null ? eerr + estderr + estdout : "done test executable...");
    });
});