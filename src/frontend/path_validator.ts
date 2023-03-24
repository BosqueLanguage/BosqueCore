import { BSQRegex } from "./bsqregex";

class BSQPathValidator {
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

    jemit(): any {
        return {
            scheme: this.scheme || null,
            userinfo: this.userinfo ? this.userinfo.jemit() : null,
            host: this.host ? this.host.jemit() : null,
            port: this.port || null,
            path: {
                prefix: this.path.prefix ? this.path.prefix.jemit() : null,
                segments: this.path.segments ? this.path.segments.jemit() : null,
                suffix: this.path.suffix ? this.path.suffix.jemit() : null,
                file: this.path.file ? this.path.file.jemit() : null,
                extension: this.path.extension ? this.path.extension.jemit() : null
            },
            query: this.query ? Array.from(this.query.entries()).map((e) => [e[0], e[1].jemit()]) : null,
            fragment: this.fragment ? this.fragment.jemit() : null
        };
    }
    static jparse(obj: any): BSQPathValidator {
        return new BSQPathValidator(
            obj.scheme || undefined,
            obj.userinfo ? BSQRegex.jparse(obj.userinfo) : undefined,
            obj.host ? BSQRegex.jparse(obj.host) : undefined,
            obj.port || undefined,
            {
                prefix: obj.path.prefix ? BSQRegex.jparse(obj.path.prefix) : undefined,
                segments: obj.path.segments ? BSQRegex.jparse(obj.path.segments) : undefined,
                suffix: obj.path.suffix ? BSQRegex.jparse(obj.path.suffix) : undefined,
                file: obj.path.file ? BSQRegex.jparse(obj.path.file) : undefined,
                extension: obj.path.extension ? BSQRegex.jparse(obj.path.extension) : undefined
            },
            obj.query ? new Map(obj.query.map((e: any) => [e[0], BSQRegex.jparse(e[1])])) : undefined,
            obj.fragment ? BSQRegex.jparse(obj.fragment) : undefined
        );
    }

    acceptsPath(pth: string): boolean {
        //TODO: implement
        return false;
    }

    acceptsPathFragment(pth: string): boolean {
        //TODO: implement
        return false;
    }

    acceptsPathGlob(pth: string): boolean {
        //TODO: implement
        return false;
    }
}

export {
    BSQPathValidator
};