"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("./codeproc.js");

describe('Readme add2', function () {
    const testopt = ["readme", "add"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('add2(3n, 4n)', function () {
        it('expected 7', function () {
            expect(invokeExecutionOn(jsmain, 3, 4)).to.eql(7);
        });
    });
    describe('add2(3n, 0n)', function () {
        it('expected 3', function () {
            expect(invokeExecutionOn(jsmain, 3, 0)).to.eql(3);
        });
    });
});

describe('Readme allPositive', function () {
    const testopt = ["readme", "allpositive"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('allPositive([1, 3, 4])', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, [1, 3, 4])).to.eql(true);
        });
    });
    describe('allPositive([])', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, [])).to.eql(true);
        });
    });
    describe('allPositive([1, -3, 4])', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, [1, -3, 4])).to.eql(false);
        });
    });
});


describe('Readme sign', function () {
    const testopt = ["readme", "sign"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('sign(5)', function () {
        it('expected 1', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(1);
        });
    });
    describe('sign(-5)', function () {
        it('expected -1', function () {
            expect(invokeExecutionOn(jsmain, -5)).to.eql(-1);
        });
    });
    describe('sign(0)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(0);
        });
    });
});

describe('Readme nominal generic', function () {
    const testopt = ["readme", "nominal_inv_generic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('GenericGreeting', function () {
        it('expected ["hello world", "hello world"]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql(["hello world", "hello world"]);
        });
    });
});

describe('Readme nominal named', function () {
    const testopt = ["readme", "nominal_inv_named"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('NamedGreeting', function () {
        it('expected "hello bob"', function () {
            expect(invokeExecutionOn(jsmain, "bob")).to.eql("hello bob");
        });
    });
    describe('NamedGreeting Err', function () {
        it('expected invariant failure', function () {
            expect(invokeExecutionOn(jsmain, "")).to.contain("Failed invariant");
        });
    });
});

describe('Readme percentage', function () {
    const testopt = ["readme", "typedecl_percentage"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Percentage 30%', function () {
        it('expected 30', function () {
            expect(invokeExecutionOn(jsmain, 30)).to.eql(30);
        });
    });
    describe('Percentage 101 Err', function () {
        it('expected invariant failure', function () {
            expect(invokeExecutionOn(jsmain, 101)).to.contain("Failed invariant");
        });
    });
});

describe('Readme temp', function () {
    const testopt = ["readme", "typedecl_temp"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('isFrezing 5', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, 5)).to.eql(false);
        });
    });
    describe('isFrezing -5', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, -5)).to.eql(true);
        });
    });
});

describe('Ref Methods', function () {
    const testopt = ["readme", "refcall"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ctrs', function () {
        it('expected [0, 1]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql([0, 1]);
        });
    });
});

describe('Binders & Flow (flowit)', function () {
    const testopt = ["readme", "flowit"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('flowit(none)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, null)).to.eql(0);
        });
    });
    describe('flowit(0)', function () {
        it('expected 10', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(10);
        });
    });
    describe('flowit(7)', function () {
        it('expected 17', function () {
            expect(invokeExecutionOn(jsmain, 7)).to.eql(17);
        });
    });
});

describe('Binders & Flow (restrict)', function () {
    const testopt = ["readme", "restrict"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('restrict(none)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain,  null)).to.eql(0);
        });
    });
    describe('restrict(0)', function () {
        it('expected 10', function () {
            expect(invokeExecutionOn(jsmain, 0)).to.eql(10);
        });
    });
    describe('restrict(7)', function () {
        it('expected 17', function () {
            expect(invokeExecutionOn(jsmain, 7)).to.eql(17);
        });
    });
});

describe('Datatype (evaluate)', function () {
    const testopt = ["readme", "datatype_evaluate"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('evaluate (and)', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, ["Main::AndOp", {
                line: 2, 
                larg: ["Main::LConst", {line: 1, val: true}], 
                rarg: ["Main::LConst", {line: 1, val: false}]
            }]
            )).to.eql(false);
        });
    });
    describe('evaluate (or)', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, ["Main::OrOp", {
                line: 2, 
                larg: ["Main::LConst", {line: 1, val: true}], 
                rarg: ["Main::LConst", {line: 1, val: false}]
            }]
            )).to.eql(true);
        });
    });
});

describe('Union (print)', function () {
    const testopt = ["readme", "union_print"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('print (bool)', function () {
        it('expected "b"', function () {
            expect(invokeExecutionOn(jsmain, ["Bool", true])).to.eql("b");
        });
    });
    describe('print (none)', function () {
        it('expected "n"', function () {
            expect(invokeExecutionOn(jsmain, ["None", null])).to.eql("n");
        });
    });
    describe('print (int)', function () {
        it('expected "i"', function () {
            expect(invokeExecutionOn(jsmain, ["Int", 7])).to.eql("i");
        });
    });
});

describe('Validator (zipcode)', function () {
    const testopt = ["readme", "zipcode"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('accepts (98052)', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "98052")).to.eql(true);
        });
    });
    describe('accepts (1234)', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "1234")).to.eql(false);
        });
    });
});


describe('StringOf (csspt)', function () {
    const testopt = ["readme", "csspt"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('is3pt (3pt)', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "3pt")).to.eql(true);
        });
    });
    describe('is3pt (4pt)', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "4pt")).to.eql(false);
        });
    });
});
