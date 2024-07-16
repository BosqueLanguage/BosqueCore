import { workflowLoadCoreSrc } from '../../src/cmd/workflows.js';
import { Assembly } from '../../src/frontend/assembly.js';
import { CodeFileInfo } from '../../src/frontend/build_decls.js';
import { TypeChecker } from '../../src/frontend/checker.js';
import { Parser } from '../../src/frontend/parser.js';

import assert from "node:assert";

function loadContents(ff: string): Assembly | string {
    const src = workflowLoadCoreSrc();
    if(src === undefined) {
        return "**ERROR**";
    }

    const maintest: CodeFileInfo[]  = [{srcpath: "test", filename: "test", contents: ff}];

    const rr = Parser.parse(src, maintest, ["EXEC_LIBS"]);
    return Array.isArray(rr) ? rr[0].message : rr;
}

function generateExpFunctionContents(exp: string, type: string): string {
    return `declare namespace Main; function main(): ${type} { return ${exp}; }`;
}

function generateFileContents(contents: string): string {
    return `declare namespace Main; ${contents}`;
}

function checkTestExp(exp: string, type: string) {
    const ff = generateExpFunctionContents(exp, type);
    const assembly = loadContents(ff);

    if(typeof(assembly) === "string") {
        assert.fail(assembly);
    }

    const errors = TypeChecker.checkAssembly(assembly);
    if(errors.length > 0) {
        assert.fail(errors.map(e => e.msg).join("\n"));
    }
}

function checkTestExpError(exp: string, type: string, msg: string) {
    const ff = generateExpFunctionContents(exp, type);
    const assembly = loadContents(ff);

    if(typeof(assembly) === "string") {
        assert.fail(assembly);
    }

    const errors = TypeChecker.checkAssembly(assembly);
    assert.equal(errors[0].msg, msg);
}

function generateFunctionContents(ff: string): string {
    return `declare namespace Main; ${ff}`;
}

function checkTestFunction(ff: string) {
    const assembly = loadContents(generateFunctionContents(ff));

    if(typeof(assembly) === "string") {
        assert.fail(assembly);
    }

    const errors = TypeChecker.checkAssembly(assembly);
    if(errors.length > 0) {
        assert.fail(errors.map(e => e.msg).join("\n"));
    }
}

function checkTestFunctionError(ff: string, msg: string) {
    const assembly = loadContents(generateFunctionContents(ff));

    if(typeof(assembly) === "string") {
        assert.fail(assembly);
    }

    const errors = TypeChecker.checkAssembly(assembly);
    assert.equal(errors[0].msg, msg);
}


function checkTestFunctionInFile(code: string) {
    const assembly = loadContents(generateFileContents(code));

    if(typeof(assembly) === "string") {
        assert.fail(assembly);
    }

    const errors = TypeChecker.checkAssembly(assembly);
    if(errors.length > 0) {
        assert.fail(errors.map(e => e.msg).join("\n"));
    }
}

function checkTestFunctionInFileError(code: string, msg: string) {
    const assembly = loadContents(generateFileContents(code));

    if(typeof(assembly) === "string") {
        assert.fail(assembly);
    }

    const errors = TypeChecker.checkAssembly(assembly);
    assert.equal(errors[0].msg, msg);
}

export {
    checkTestExp, checkTestExpError,
    checkTestFunction, checkTestFunctionError,
    checkTestFunctionInFile, checkTestFunctionInFileError
};
