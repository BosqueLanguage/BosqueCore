"use strict";

const fsx = require("fs-extra");
const { exec } = require("child_process");
const path = require("path");

const builddir = path.join(__dirname, "../../../build");
const bsqonsrcdir = __dirname;
const srcdir = path.join(__dirname, "lb");

const outexec = path.join(builddir, "output");
const outobj = path.join(builddir, "output", "obj");

const bsqon_cpp_files = [
    "../regex/bsqregex.cpp",
    "../info/type_info.cpp", "../info/bsqon.cpp",
    "bsqon_parse.cpp"
];

const bsqon_obj_files = [
    `${outobj}/bsqon.tab.o`, `${outobj}/lex.yy.o`
];

//const cpp_flags = "-fno-omit-frame-pointer -Wall -Wextra -Wuninitialized -Wno-unused-parameter -Werror -std=c++20";
const cpp_flags = "-fno-omit-frame-pointer -std=c++20";
const json_includes = `-I ${path.join(builddir, "include/headers/json")}`;

fsx.ensureDirSync(outexec);
fsx.ensureDirSync(outobj);

let doneyy = false;
let donetest = false;
let doneexport = false;
let donebsqon = false;

let haderror = false;

function doneop(iserror, msg) {
    haderror = haderror || iserror;

    process.stdout.write(msg + "\n");
    if(doneyy && donetest && doneexport && donebsqon) {
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

console.log(bsqonsrcdir);
const mode = process.argv[2] || "default";

exec(`bison -d${mode === "debug" ? " -Wcex" : ""} bsqon.y && flex bsqon.l`, {cwd: srcdir}, (err, stdout, stderr) => {
    doneyy = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done parser gen..."); 

    exec(`gcc -Og -ggdb -DEXPORT -o ${outobj}/bsqon.tab.o -c bsqon.tab.c && gcc -Og -DEXPORT -o ${outobj}/lex.yy.o -c lex.yy.c`, {cwd: srcdir}, (oerr, ostdout, ostderr) => {
        donetest = true;
        doneop(oerr !== null, oerr !== null ? oerr + ostderr + ostdout : "done obj file build...");

        exec(`g++ -Og -ggdb ${cpp_flags} ${json_includes} -o ${outexec}/bsqon ${bsqon_cpp_files.join(" ")} ${bsqon_obj_files.join(" ")} bsqon_main.cpp`, {cwd: bsqonsrcdir}, (berr, bstdout, bstderr) => {
            donebsqon = true;
            doneop(berr !== null, berr !== null ? berr + bstderr + bstdout : "done bsqon main build...");
        });
    });

    exec(`gcc -O1 -g -ggdb ${mode === "debug" ? " -fsanitize=address" : ""} -fno-omit-frame-pointer -o ${outexec}/bsqon_parser bytestring.c bsqon_type_ast.c bsqon_ast.c bsqon.tab.c lex.yy.c -lfl`, {cwd: srcdir}, (eerr, estdout, estderr) => {
        doneexport = true;
        doneop(eerr !== null, eerr !== null ? eerr + estderr + estdout : "done test executable...");
    });
});
