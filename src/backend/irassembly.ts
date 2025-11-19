import { IRRegex } from "./irsupport";


class IRAssembly {
    readonly regexps: IRRegex[];

    constructor(regexps: IRRegex[]) {
        this.regexps = regexps;
    }
}

export {
    IRAssembly
};