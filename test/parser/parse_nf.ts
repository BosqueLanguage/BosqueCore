import { workflowLoadCoreSrc } from '../../src/cmd/workflows.js';
import { Parser } from '../../src/frontend/parser.js';

function wsnorm(s: string): string {
    return s.trim().replace(/\s+/g, " ");
}

function parseExp(contents: string): string {
    const src = workflowLoadCoreSrc();
    if(src === undefined) {
        return "**ERROR**";
    }

    const rr = Parser.test_parseSFunction(src, ["EXEC_LIBS"], contents);
    return wsnorm(Array.isArray(rr) ? rr[0].message : rr);
}

function parseExpOk(contents: string, expected: string): string {
    return parseExp(contents);
}

export {
    parseExp,
    parseExpOk
};
