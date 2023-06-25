const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Namespace constants', function () {
    const testopt = ["expression/constants", "namespace_consts"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('main()', function () {
        it('expected [1i, 3i]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[1i, 3i]");
        });
    });
});
