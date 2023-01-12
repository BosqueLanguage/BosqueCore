import * as assert  from "assert";
import { BSQRegex } from "./bsqregex";

class PathValidator {
    readonly scheme: string | undefined;
    readonly userinfo: BSQRegex | undefined;
    readonly host: BSQRegex | undefined;
    readonly port: number | undefined;
    readonly path: {
        prefix: BSQRegex | undefined,
        segments: BSQRegex | undefined,
        suffix: BSQRegex | undefined,
        file: BSQRegex | undefined,
        extension: BSQRegex | undefined
    };
    readonly query: Map<string, BSQRegex> | undefined;
    readonly fragment: BSQRegex | undefined;

    constructor(scheme: string | undefined, userinfo: BSQRegex | undefined, host: BSQRegex | undefined, port: number | undefined,
        path: { prefix: BSQRegex | undefined, segments: BSQRegex | undefined, suffix: BSQRegex | undefined, file: BSQRegex | undefined, extension: BSQRegex | undefined },
        query: Map<string, BSQRegex> | undefined, fragment: BSQRegex | undefined) {
            this.scheme = scheme;
            this.userinfo = userinfo;
            this.host = host;
            this.port = port;
            this.path = path;
            this.query = query;
            this.fragment = fragment;
    }

    acceptsPath(pth: string): boolean {
        assert(false, "NOT IMPLEMENtED -- acceptsPath");
        return false;
    }

    acceptsPathFragment(pth: string): boolean {
        assert(false, "NOT IMPLEMENtED -- acceptsPathFragment");
        return false;
    }

    acceptsPathGlob(pth: string): boolean {
        assert(false, "NOT IMPLEMENtED -- acceptsPathGlob");
        return false;
    }
}

export {
    PathValidator
};