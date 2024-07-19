import { workflowLoadCoreSrc } from '../../src/cmd/workflows.js';
import { Parser } from '../../src/frontend/parser.js';

import assert from "node:assert";

function wsnorm(s: string): string {
    return s.trim().replace(/\s+/g, " ");
}

function parseFunction(ff: string): string {
    const src = workflowLoadCoreSrc();
    if(src === undefined) {
        return "**ERROR**";
    }

    const rr = Parser.test_parseSFunction(src, ["EXEC_LIBS"], ff);
    return wsnorm(Array.isArray(rr) ? rr[0].message : rr);
}

function parseFunctionInFile(code: string): string {
    const src = workflowLoadCoreSrc();
    if(src === undefined) {
        return "**ERROR**";
    }

    const rr = Parser.test_parseSFunctionInFile(src, ["EXEC_LIBS"], code, "main");
    return wsnorm(Array.isArray(rr) ? rr[0].message : rr);
}

function parseFunctionInFilePlus(code: string, ctxcode: string[]): string {
    const src = workflowLoadCoreSrc();
    if(src === undefined) {
        return "**ERROR**";
    }

    const ctxfiles = ctxcode.map((c, i) => {
        return { 
            srcpath: `/src/code_${i}.bsq`, 
            filename: `code_${i}.bsq`, 
            contents: c
        };
    });

    const rr = Parser.test_parseSFunctionInFilePlus(src, ["EXEC_LIBS"], ctxfiles, code, "main");
    return wsnorm(Array.isArray(rr) ? rr[0].message : rr);

}

function generateExpFunction(exp: string, type: string): string {
    return `function main(): ${type} { return ${exp}; }`;
}

function parseTestExp(exp: string, rexp: string | undefined, type: string) {
    const ff = generateExpFunction(exp, type);
    const rff = rexp === undefined ? ff : generateExpFunction(rexp, type);
    assert.equal(parseFunction(ff), wsnorm(rff));
}

function parseTestExpError(exp: string, error: string, type: string) {
    const ff = generateExpFunction(exp, type);
    assert.equal(parseFunction(ff), error);
}

function parseTestFunction(ff: string, rff: string | undefined) {
    assert.equal(parseFunction(ff), wsnorm(rff || ff));
}

function parseTestFunctionError(ff: string, error: string) {
    assert.equal(parseFunction(ff), error);
}

function parseTestFunctionInFile(code: string, rff: string) {
    assert.equal(parseFunctionInFile(code.replace("[FUNC]", rff)), wsnorm(rff));
}

function parseTestFunctionInFileError(code: string, error: string) {
    assert.equal(parseFunctionInFile(code), error);
}

function parseTestFunctionInFilePlus(code: string, rff: string, eres: string | undefined, ...ctxcode: string[]) {
    assert.equal(parseFunctionInFilePlus(code.replace("[FUNC]", rff), ctxcode), wsnorm(eres || rff));
}

function parseTestFunctionInFilePlusError(code: string, error: string, ...ctxcode: string[]) {
    assert.equal(parseFunctionInFilePlus(code, ctxcode), error);
}

export {
    parseTestExp, parseTestExpError,
    parseTestFunction, parseTestFunctionError,
    parseTestFunctionInFile, parseTestFunctionInFileError,
    parseTestFunctionInFilePlus, parseTestFunctionInFilePlusError
};
