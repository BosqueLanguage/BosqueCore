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

function generateExpFunction(exp: string, type: string): string {
    return `function main(): ${type} { return ${exp}; }`;
}

function parseTestExp(exp: string, type: string) {
    const ff = generateExpFunction(exp, type);
    assert.equal(parseFunction(ff), wsnorm(ff));
}

export {
    parseFunction,
    generateExpFunction,
    parseTestExp
};
