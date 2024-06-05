import { workflowLoadCoreSrc } from '../../cmd/load_core';
import { Parser } from '../../frontend/parser';

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

function parseExpOk(contents: string, expected: string): boolean {
    return parseExp(contents) === expected;
}

export {
    parseExp,
    parseExpOk
};
