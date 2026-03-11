"use strict";


import { runTestSet } from "../../../bin/test/cpprun/cpprun_nf.js";
import { describe, it } from "node:test";

describe ("CPPExec -- interpolate cstring", () => {
    it("should exec simple interpolate cstring (direct)", function () {
        runTestSet("public function main(s: CString): CString { return Interpolate::cstring($'-${0}-', s); }", [['"x"', "'-x-'"]], []);
        runTestSet("public function main(s: CString): CString { return Interpolate::cstring($'${0}-${1}', s, 'b'); }", [['"x"', "'x-b'"]], []);

        runTestSet("public function main(s: CString): CString { return Interpolate::cstring<CString>($'${0}-${0}', s); }", [['"x"', "'x-x'"]], []);
        runTestSet("public function main(s: CString): CString { return Interpolate::cstring<CString>($'${arg2}-${arg1}', arg1 = s, arg2 = 'b'); }", [['"x"', "'b-x'"]], []);
    });

    it("should exec simple interpolate cstring (var)", function () {
        runTestSet("public function main(s: CString): CString { let fs = $'-${0}-'; return Interpolate::cstring(fs, s); }", [['"x"', "'-x-'"]], []);
        runTestSet("public function main(s: CString): CString { let fs = $'${0}-${1}'; return Interpolate::cstring(fs, s, 'b'); }", [['"x"', "'x-b'"]], []);

        runTestSet("public function main(s: CString): CString { let fs = $'${0}-${0}'; return Interpolate::cstring<CString>(fs, s); }", [['"x"', "'x-x'"]], []);
        runTestSet("public function main(s: CString): CString { let fs = $'${arg2}-${arg1}'; return Interpolate::cstring<CString>(fs, arg1 = s, arg2 = 'b'); }", [['"x"', "'b-x'"]], []);
    });
});

