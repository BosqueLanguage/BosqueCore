"use strict";

const path = require("path");
const fsx = require("fs-extra");

const rootsrc = path.join(__dirname, "../", "src");
const rootbin = path.join(__dirname, "../", "bin");

function copyResourceDir(dirfrom, dirto) {
    const srcpath = path.join(rootsrc, dirfrom);
    const dstpath = path.join(rootbin, dirto);

    process.stdout.write(`Copying ${srcpath} to ${dstpath}\n`);
    fsx.ensureDirSync(dstpath);
    fsx.emptyDirSync(dstpath);
    fsx.copySync(srcpath, dstpath);
}


function copyResourceFile(dirfrom, dirto, file) {
    const srcpath = path.join(rootsrc, dirfrom);
    const dstpath = path.join(rootbin, dirto);

    process.stdout.write(`Copying ${srcpath} to ${dstpath}\n`);
    fsx.ensureDirSync(dstpath);
    fsx.emptyDirSync(dstpath);
    fsx.copySync(path.join(srcpath, file), path.join(dstpath, file));
}

process.stdout.write(`Copying resources...\n`);

copyResourceDir("core", "core");
copyResourceDir("runtimes/javascript/runtime", "runtimes/javascript/runtime");

copyResourceFile("frontend/ast/tree_ir", "runtimes/javascript/runtime", "typeinfo.ts");

process.stdout.write(`done!\n`);