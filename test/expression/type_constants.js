const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Type constants', function () {
    const testopt = ["expression/constants", "type_consts"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('main()', function () {
        it('expected [1i, 1i, 4i, 1i]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([1, 1, 4, 1]);
        });
    });
});
