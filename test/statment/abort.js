
const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Abort basic', function () {
    const testopt = ["statement/abort", "basic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('process fail', function () {
        it('expected fail', function () {
            expect(invokeExecutionOn(jsmain, false)).to.includes("error -- Abort");
        });
    });
});

