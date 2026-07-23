# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/BosqueLanguage/BosqueCore/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Health](https://img.shields.io/github/actions/workflow/status/BosqueLanguage/BosqueCore/main.yml?branch=main)](https://github.com/BosqueLanguage/BosqueCore/actions) 


# The Bosque Project

Bosque is a new approach to programming languages, development tooling, and runtime design that is focused on supporting mechanization at scale and establishing a new standard for creating efficient and high-reliability software artifacts. 
- **Quality** -- reliability and correctness should be opt-out, not opt-in, by default. Doing the simple obvious thing should _just work_ and lead to good outcomes.
- **Efficiency** -- software bloat and inefficiency are a major source of cost and complexity in modern systems. Writing simple, clear code, should lead to efficient and predictable systems.
- **Mechanization** -- whenever possible we support mechanization of development tasks. We want humans to focus on the creative \& high-level aspects development and let machines handle the tedious parts.
- **AI Agents & APIs** -- we want to embrace the use of AI agents and APIs as key parts of the development process. Thus, we support these a first-class parts of the programming and software stack.
- **Development should be Fun!** -- the tools and languages we use should make it easy (and fun) to express ideas and solve problems, not get in the way.

# Current Status
We are at a major milestone in the Bosque project -- our 2.0 release! 

Since the first announcement about this project in 2019 we have been focused on a North-Star of eliminating extrinsic complexity from the software stack and engineering process. We are excited to announce that after a lot (and more than I expected) of experimentation and experience we are ready to stabilize the language and core platform for general use in the 2.0 release.

Our #1 priority is to work with the community to start deploying Bosque in the real-world and rapidly address any issues that arise. In addition we plan to invest in building out the ecosystem of tools, libraries, and integrations that will make Bosque a great platform for building high-quality software. This includes the entire gamut of ecosystems from table stakes like LSP support, formal-methods, and workflows for Agentic AI systems!

# Platform Road Map 
The current (approximate) roadmap for the Bosque project is broken down into a series of major components that are being developed in parallel + smaller but high-impact work items. These cover a range of complexity and required skills, from academic level publication results, through non-trivial software engineering lifts, and into smaller tasks that are good starter projects. If you are interested in one of these please find (or open) an issue for more detail.

The current work items are focused on the 2.0 release of the Bosque language and it actively in-progress:
- Core Libraries -- lots of opportunity to build out this to provide a comprehensive set of core libraries for the Bosque language.
- Build out async tasks and runtime support -- including priority scheduling, cancellation, an async I/O microservice host, and production trace recording.
- Visual Studio Code Integration -- The current version is a simple syntax highlighter at the moment next steps are to build out a full LSP server.
- Small Model Verifier -- a symbolic checker with guarantees of the decidability of the presence or absence of small inputs that trigger any runtime failure/assertion/pre/post/invariant condition.
- Provide the [Tecton](https://arxiv.org/abs/2510.19777) test generator as a builtin component to augment the small model verifier and provide a simple way to generate test cases for Bosque programs.

The Bosque project is actively inviting contributors as we move from a research focused into a practically focused project! We want to make this a a great place to learn and contribute to the next era in programming languages, compilers, and runtime systems. Below are some topics that are open for contributions and where help is greatly appreciated, we are happy to help mentor and guide you through the process.

# Some Notable Bosque Features
- **No Spooky Actions at a Distance** -- Bosque code is understandable in isolation and strongly guarantees that the behavior of a program is not dependent on the context in which it is run or dependent on implicit behaviors.
- **Fully Deterministic** -- Core Bosque is fully deterministic, for any input there is only one possible output and any (nondeterministic) environmental interactions are explicitly encapsulated in 'Task' environments.
- **Poke-Yoke Programming** -- These features, along with full memory safety, loop-free programming, typed strings, and type invariants, Bosque makes writing correct programs hard to do wrong. In fact, of the 2024 MITRE Top-10 CWE categories, 3 are impossible and 5 more require explicit opt-outs of safety features to trigger. 
- **No Tradeoff-GC** -- The simplified design of Bosque limits what happen when any given piece of code runs (simplifying reasoning) and also simplifying the runtime. In fact the Bosque compiler leverages this to provide _the first_ no-tradeoooff garbage collector with bounded pauses, starvation freedom, and bounded CPU/Memory overhead!
- **(Being) Made for Observability** -- Bosque is designed to be a distributed deployment ecosystem -- thus assertions, operation auditing, distributed event tracking, and field-issue reproduction and built into the language and runtime. 

# Sample Code

**Functions and arguments:**
```none
public function sub2(x: Int, y: Int): Int {
    return x - y;
}

sub2(4i, 2i)     %% 2i
sub2(y=2i, x=3i) %% 1i

sub2(3i, 4.0f) %% type error -- defined on Int but given Float arg
sub2(3, 4)     %% type error -- un-annotated numeric literals are not supported (for now)
```

**All positive check using rest parameters and lambda:**
```none
public function allPositive(...args: List<Int>): Bool {
    return args.allOf(pred(x) => x >= 0i);
}

allPositive(1i, 3i, 4i)  %% true
allPositive()            %% true
allPositive(1i, 3i, -4i) %% false
```

**Sign (with blocks and assignment):**
```none
public function sign(x: Int): Int {
    if(x == 0i) {
        return 0i;
    }

    var y: Int;
    if(x < 0i) {
        y = -1i;
    }
    else {
        y = 1i;
    }

    return y;
}

sign(5i)    %%  1i
sign(-5i)   %% -1i
```

**Reference and Parameter Passing modes -- Simplify common state management:**
```none
%%Manual threading of state
entity Ctr { 
    field vv: Nat = 0n; 
    method next(): Ctr { 
        return Ctr{ vv = this.vv + 1n }; 
    } 
} 

let ctr = Ctr{}; 
let ctr1 = ctr.next(); 
let ctr2 = ctr1.next(); 

ctr2.vv; %% 2n
```

```none
%%Use ref params and updates to simplify state management (but still functional!)
entity Ctr { 
    field vv: Nat = 0n; 
    ref method next() { 
        ref this[vv = $vv + 1n]; 
    } 
} 

ref ctr = Ctr{}; 
ref ctr.next(); 
ref ctr.next(); 

ctr.vv; %% 2n
```

**Nominal Types with Multi-Inheritance (todo: vcall impl) & Data Invariants:**
```
concept WithName {
    invariant $name !== "";

    field name: String;
}

concept Greeting {
    abstract method sayHello(): String;

    virtual method sayGoodbye(): String {
        return "goodbye";
    }
}

entity GenericGreeting provides Greeting {
    const instance: GenericGreeting = GenericGreeting{};

    override method sayHello(): String {
        return "hello world";
    }
}

entity NamedGreeting provides WithName, Greeting {
    override method sayHello(): String {
        return String::concat("hello", " ", this.name);
    }
}

GenericGreeting{}.sayHello()          %% "hello world"
GenericGreeting::instance.sayHello()  %% "hello world"

NamedGreeting{}.sayHello()           %% type error no value provided for "name" field
NamedGreeting{""}.sayHello()         %% invariant error
NamedGreeting{"bob"}.sayHello()      %% "hello bob"
```

**Type Alias Types**
```
type Fahrenheit = Int;
type Celsius = Int;

type Percentage = Nat & {
    invariant $value <= 100n;
}

32i<Fahrenheit> + 0i<Celsius>  %% type error different numeric types
30n<Percentage>                %% valid percentage
101n<Percentage>               %% invariant error

function isFreezing(temp: Celsius): Bool {
    return temp <= 0i<Celsius>;
}

isFreezing(5.0f)           %% type error not a celsius number
isFreezing(5i<Celsius>)    %% false
isFreezing(-5i<Celsius>)   %% true

```

**Flow and Explicit Type Inference:**
```
function flowit(x: Option<Nat>): Nat {
    %%ITest for none as special
    if(x)@none {
        return 0n;
    }
    else {
        %%ITest allows binder for $x to value of x (with type inference)
        return $x + 10n;
    }
}

flowit(none)      %% 0n
flowit(some(5n))  %% 15n
```

**(Algebraic Data Types)++**
```
datatype BoolOp of
    Const { val: Bool }
    NotOp { arg: BoolOp }
    AndOp { larg: BoolOp, rarg: BoolOp }
    OrOp { larg: BoolOp, rarg: BoolOp }
& {
    recursive method evaluate(): Bool {
        match(this) {
            Const  => { return $this.val; }
            NotOp => { return !$this.arg.evaluate[recursive](); }
            AndOp => { return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive](); }
            OrOp  => { return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive](); }
        }
    } 
}

OrOp{Const{true}, Const{false}}.evaluate[recursive]()            %% true
AndOp{larg=Const{true}, rarg=Const{false}}.evaluate[recursive]() %% false
```

**Validated Strings:**
```
type Zipcode = CString of /[0-9]{5}('-'[0-9]{4})?/c;
type CSSPt = CString of /[0-9]+'pt'/c;

function is3pt(s1: CSSPt): Bool {
    return s1.value === '3pt';
}

'1234'<Zipcode> %% type error (does not match regex)
'3px'<CSSPt>    %% type error (does not match regex)

is3pt('12')               %% type error not a CSSPt
is3pt('98052'<Zipcode>)   %% type error not a CSSPt

is3pt('3pt'<CSSPt>) %% true
is3pt('4pt'<CSSPt>) %% false
```

# Documentation

In progress documentation for the language and standard libraries are on the [Language](docs/overview.md) and [Libraries](docs/overview.md) doc pages respectively. Sample code snippets below provide a quick feel of the language and syntax.

Detailed Documentation, Tutorials, and Technical Information:
* [Language Docs](docs/overview.md)
* [Library Docs](docs/overview.md)
* [Technical Papers](docs/research/papers/publist.md)


# Installing the Bosque Language

In order to install/build the project the following are needed:

- 64 bit Linux Operating System (Ubuntu 24 recommended)
- Version 22+ of [node.js](https://nodejs.org/en/download/)
- Typescript 5.6 (installed as a dev dependency)
- Git 

## Build & Test

```none
npm install && npm test
```

## Running

The current way to work with Bosque source code is through the `bosque` compiler command line tool. After building this tool is available in the `bin/src/cmd/` directory. It is currently very simple with _one_ action which is to take all of the command line arguments and transpile them into C++ sources and a `Makefile` -- using the _unique_ `public function main(args) ...` as the entrypoint and putting the results in the output folder `cppout`. This makefile defaults to a diagnostic build with no optimizations and but can also be built as an optimized build with the `make BUILD=release` option. The resulting executable 'app' is placed in the `cppout` folder.

```none
node bin/src/cmd/bosque.js <source-file.bsq> <source-file.bsq> ...
make -f cppout/Makefile
./cppout/app 'arg1' 'arg2' ...
```

## Visual Studio Code Integration

Basic [Visual Studio Code](https://code.visualstudio.com/) IDE support for the Bosque language (currently limited to syntax and brace highlighting) is available from [this repo](https://github.com/BosqueLanguage/bosque-language-tools). The installation requires manually building and installing as a VSIX package.

## Contribute

This project welcomes community contributions.

* [Submit bugs](https://github.com/BosqueLanguage/BosqueCore/issues) and help us verify fixes.
* [Submit pull requests](https://github.com/BosqueLanguage/BosqueCore/pulls) for bug fixes and features and discuss existing proposals.
* Chat about the [@BosqueLanguage](https://twitter.com/BosqueLanguage) (or [#BosqueLanguage](https://twitter.com/hashtag/BosqueLanguage)) on Twitter.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/).

## License

Code licensed under the [MIT License](LICENSE.txt).
