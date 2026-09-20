"use strict";

import { parseTestFunctionInFile, parseTestFunctionInFileError } from "../../../bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

const taskctx = "public task Main { action start(): APIResult<Int> { return success(3i); } }";