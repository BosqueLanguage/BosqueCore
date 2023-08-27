"use strict";

const path = require("path");
const fs = require("fs");

function countLinesInFile(filepath, ext) {
    if(!filepath.endsWith(ext)) {
        return 0;
    }
    else {
        const contents = fs.readFileSync(filepath, "utf8").toString();
        const emptylines = contents.match(/(^[ \t]*\n$)/gm);
        const totallines = contents.match(/(\n)/g);

        const emptycount = emptylines !== null ? (emptylines.length - 1) : 0;
        const linecount = totallines !== null ? (totallines.length - 1) : 0;

        return linecount - emptycount;
    }
}

function countLinesInDir(dir, ext) {
    let total = 0;
    const files = fs.readdirSync(dir);
    for(const file of files) {
        if(file.startsWith(".")) {
            continue;
        }

        const filepath = path.join(dir, file);
        const stat = fs.statSync(filepath);
        if(stat.isDirectory()) {
            total += countLinesInDir(filepath, ext);
        }
        else if(file.endsWith(ext)) {
            total += countLinesInFile(filepath, ext);
        }
    }
    return total;
}

["ts", "bsq", "smt2", "js", "h", "c", "cpp"].forEach((ext) => {
    const total = countLinesInDir(path.join(__dirname, "..", "src"), ext);
    const pad = " ".repeat(5 - ext.length);
    console.log(`Total lines for ${ext}: ${pad}${total}`);
});
