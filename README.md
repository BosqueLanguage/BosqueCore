# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/BosqueLanguage/BosqueCore/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Health](https://img.shields.io/github/actions/workflow/status/BosqueLanguage/BosqueCore/main.yml?branch=main)](https://github.com/BosqueLanguage/BosqueCore/actions) 


# The Bosque Project

Bosque is a new approach to programming models, development tooling, and runtime design that is focused on supporting mechanization at scale and establishing a new standard for creating high-reliability software artifacts. The foundational design precepts for Bosque are:
1. Design for Tooling & Mechanization -- The entire system should be amenable to automated analysis and transformation. Avoid features or behaviors that inhibit analysis and automation.
2. Total Safety -- Don't just make mistakes hard to make, eliminate them entirely. Whenever possible rule-out entire categories of failures by construction.
3. WYSIWYG -- Humans and AI Agents understand and make assumptions about the semantics (behavior) of the code from the textual representation (syntax). Minimize the presence of implicit or syntactically hidden behaviors. 
4. The Ecosystem is the Language -- Modern development at scale is a collaborative process, both working with partner teams or using 3rd party code, via packages and/or APIs. Create a framework that is designed for componentization, composition, and behavioral guarantees.
5. Reliable Performance at Scale -- At scale worst-case performance behaviors _will_ inevitably occur and are problematic to resolve. Design for low-variance execution and minimize the impacts of worst case behaviors instead of optimizing for the best or average case. 
6. Failure is Always an Option -- Failure is inevitable and mitigation/recovery is a requirement for reliable and scalable systems. Give un-happy path processing first-class support in the language and ensure observability throughout the system.

# Current Status
We are at a major milestone in the Bosque project -- declaring 1.0! 

Now this doesn't mean that Bosque is done, or even that is easily useable, but it does mean that the language is what it is going to be and (bold) engineering teams can write code with some degree of confidence that it will be stable and supported. As part of living this commitment, and moving on to the Bosque 2.0 phase, the goal is to begin implementing the majority of new Bosque code in Bosque itself!

The 2.0 release will be focused on a revised version of the [Small Model Verifier](https://discovery.ucl.ac.uk/id/eprint/10146184/1/finir.pdf), the [AOT compiler/runtime](https://bosquelanguage.github.io/2024/10/01/an-omega-c-runtime.html), along with improving the language for self-hosting the compiler and having a stable language for development in general.

# Platform Road Map 
The current (approximate) roadmap for the Bosque project is broken down into a series of major components that are being developed in parallel + smaller but high-impact work items. These cover a range of complexity and required skills, from academic level publication results, through non-trivial software engineering lifts, and into smaller tasks that are good starter projects. If you are interested in one of these please find (or open) an issue for more detail.

The current work items are focused on the 1.0 release of the Bosque language and it actively in-progress:
- Core Libraries -- not much but lots of opportunity to build out from previous prototype code.
- Visual Studio Code Integration -- Just a simple syntax highlighter at the moment next steps are to build out a full LSP server.
- Small Model Verifier -- a symbolic checker with guarantees of the decidability of the presence or absence of small inputs that trigger any runtime failure/assertion/pre/post/invariant condition.
- A Ω()-time and O(1)-space runtime and AOT compiler -- a runtime that is designed to be performant, low memory, and predictable in its behavior.

## Invitation for Contributors
The Bosque project is actively inviting contributors as we move from a research focused into a practically focused project! We want to make this a a great place to learn and contribute to the next era in programming languages, compilers, and runtime systems. Below are some topics that are open for contributions and where help is greatly appreciated, we are happy to help mentor and guide you through the process.

### Breakout Features
These items are headline features that are large and complex(possibly open research) but will have major impact on the future of software development. They are great for someone, highly-motivated and skilled, looking to make a big impact on the project.

- O(1)-GC -- a garbage collector with constant memory overhead, constant work per allocation, constant collector pauses, and compaction! 
- Versioning and Packaging -- build a well-founded semantics for versioning + ability to verify if changes/version errors. For users the ability to confidently upgrade dependencies (also prep for package manager and testing features).
- Termination and Bounds analysis -- a static analysis that can prove the termination of a function/task/api and the bounds on the resources it consumes.
- Extending StringOf to allow for context-free languages. Create an easy to write and generally expressive CFG language for use in Bosque and enable it for safe strings and general use.
- API-Embodied Meta-Cognitive AI-Agent (AMC-AI) -- a big acronym but big potential! Take the idea of Bosque APIs, which are well suited for synthesis with generative AI, and combine with the verifier to have a _fully-grounded_ and API (tool) using agent that can reliably accomplish user tasks.

### High-Value Enhancements
These items are more defined in scope, and will make a big difference for the project, but still require a substantial level of technical skill and effort.

- LSP Server -- a full language server protocol server for Bosque that provides code completion, diagnostics, and other IDE features.
- API Manager and Broker -- to enable bundling and calling of APIs in a uniform and efficient method. Needs a bit of semantic work + OS and Cloud support.
- Testing framework -- both to run traditional unit-tests, examples, small-model verification, and fuzzing. Also doc-gen from code artifacts.
- Power-Proroguing -- take the idea [here](https://earlbarr.com/publications/prorogue.pdf) and use the capabilities of [BSQON](https://github.com/BosqueLanguage/BSQON/blob/main/docs/publications/bsqon_techreport.pdf) (full-fidelity literals and references) to make it practical -- also maybe have some fun with LLMs!


### Chunckable Work Items
These are well-defined items that can be done in a few hours to a maybe a couple weeks and don't require much (if any) special expertise. They are great for someone looking to get started with the project -- also see good-first-issues.

- Standard Library -- build out the standard library with a focus on the core data structures and algorithms that are needed for general programming tasks.
- Documentation -- write documentation for the language, libraries, and tools. This is a great way to learn the language and help others.
- Tests -- write tests for the language, libraries, and tools. This is a great way to learn the language and help others.
- Shell -- a Bosque shell that can be used standalone or for scripting. Mainly writing a host for tracking tasks and interacting with them + writing some tasks that implement basic shell functionality.
- TTD and Debugger -- time-travel-debugging is actually a pretty simple to implement feature in Bosque. Would be great to have this and a debugger that can use it! Might split this into deterministic replay & debugger as two tasks.

# Documentation

In progress documentation for the language and standard libraries are on the [Language](docs/overview.md) and [Libraries](docs/overview.md) doc pages respectively. Sample code snippets below provide a quick feel of the language and syntax.

Detailed Documentation, Tutorials, and Technical Information:
* [Language Docs](docs/overview.md)
* [Library Docs](docs/overview.md)
* [Technical Papers](docs/research/papers/publist.md)

## Code Snippets

**Functions and arguments:**
```none
public function sub2(x: Int, y: Int): Int {
    return x - y;
}

sub2(4i, 2i)   %%2i
sub2(y=2i, 3i) %%1i

sub2(3i, 4.0f) %%type error -- defined on Int but given Float arg
sub2(3, 4)     %%type error -- un-annotated numeric literals are not supported (for now)
```

**All positive check using rest parameters and lambda:**
```none
public function allPositive(...args: List<Int>): Bool {
    return args.allOf(pred(x) => x >= 0i);
}

allPositive(1i, 3i, 4i)  %%true
allPositive()            %%true
allPositive(1i, 3i, -4i) %%false
```

**Sign (with blocks and assignment):**
```none
public function sign(x: Int): Int {
    var y: Int;

    if(x == 0i) {
        y = 0i;
    }
    else {
        y = if (x > 0i) then 1i else -1i;
    }

    return y;
}

sign(5i)    %%1
sign(-5i)   %%-1
```

**Nominal Types with Multi-Inheritance & Data Invariants:**
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

GenericGreeting{}.sayHello()          %%"hello world"
GenericGreeting::instance.sayHello()  %%"hello world"

NamedGreeting{}.sayHello()           %%type error no value provided for "name" field
NamedGreeting{""}.sayHello()         %%invariant error
NamedGreeting{"bob"}.sayHello()      %%"hello bob"
```

**Type Alias Types**
```
type Fahrenheit = Int;
type Celsius = Int;

type Percentage = Nat & {
    invariant $value <= 100n;
}

32i<Fahrenheit> + 0i<Celsius>  %%type error different numeric types
30n<Percentage>                %%valid percentage
101n<Percentage>               %%invariant error

function isFreezing(temp: Celsius): Bool {
    return temp <= 0i<Celsius>;
}

isFreezing(5.0f)           %%type error not a celsius number
isFreezing(5i<Celsius>)    %%false
isFreezing(-5i<Celsius>)   %%true

```

**Flow and Binders:**
```
function flowit(x: Nat?): Nat {
    %%ITest for none as special
    if(x)@none {
        return 0n;
    }
    else {
        %%ITest allows binder for $x to value of x (with type inference)
        return $x + 10n;
    }
}

function restrict(x: Nat?): Nat {
    if(x)@@none {
        return 0n;
    }
    %%x is a Nat here and type infer

    return x + 10n;
}
```

**(Algebraic Data Types)++ and Union Types**
```
datatype BoolOp using {
    line: Nat
} of
Const { val: Bool }
| NotOp { arg: BoolOp }
| AndOp { larg: BoolOp, rarg: BoolOp }
| OrOp { larg: BoolOp, rarg: BoolOp }
& {
    recursive method evaluate(): Bool {
        match(this)@ {
            Const  => return $this.val;
            | NotOp => return !$this.arg.evaluate[recursive]();
            | AndOp => return $this.larg.evaluate[recursive]() && $this.rarg.evaluate[recursive]();
            | OrOp  => return $this.larg.evaluate[recursive]() || $this.rarg.evaluate[recursive]();
        }
    } 
}

AndOp{2n, Const{1n, true}, Const{1n, false}}.evaluate[recursive]() %%false
OrOp{2n, Const{1n, true}, Const{1n, false}}.evaluate[recursive]()  %%true

function printType(x: Bool | Int | String | None): String {
    return match(x) {
        Bool     => "b"
        | Int    => "i"
        | String => "s"
        | _      => "n"
    };
}

printType(1.0f) %%type error
printType(true) %%"b"
printType(none) %%"n"

```

**Validated Strings:**
```
validator ValidZipcodeUS = /[0-9]{5}("-"[0-9]{4})?/;
validator ValidCSSpt = /[0-9]+"pt"/;

function is3pt(s1: StringOf<ValidCSSpt>): Bool {
    return s1.value() === "3pt";
}

RegexValidator::accepts<ValidZipcodeUS>("98052-0000") %%true
RegexValidator::accepts<ValidZipcodeUS>("1234")       %%false

is3pt("12")              %%type error not a StringOf<CSSpt>
is3pt("98052"(ValidZipcodeUS)) %%type error not a StringOf<CSSpt>

is3pt("3pt"(ValidCSSpt)) %%true
is3pt("4pt"(ValidCSSpt)) %%false
```

# Installing the Bosque Language (Currently Development Only)

In order to install/build the project the following are needed:

- 64 bit Linux Operating System (Ubuntu 22 recommended)
- Version 20+ of [node.js](https://nodejs.org/en/download/) (v20 or higher)
- Typescript (5.3 or higher) -- install with: `npm i typescript -g`
- Git and [git-lfs](https://git-lfs.github.com/) setup

## Build & Test

```none
npm install && npm test
```
The Z3 theorem prover is provided as a binary dependency in the repo via git LFS. To ensure these are present you will need to have [git-lfs](https://git-lfs.github.com/) installed, run `git lfs install` to setup the needed hooks, and pull. 

## Parser & Typechecker

Current work is on spinning up the Parser/Typechecker and some basic LSP support. Key design goals in these systems are simplicity and general efficiency. Fast turnaround times in the developer loop tools are a priority so all features are geared towards a max O(n log n) complexity -- no exponential blowups (or turing completeness) in the type system, a relatively efficient 2 pass parser, and a fast emit to JavaScript.

## Compiler & Runtime

Next open task on the roadmap is a JavaScript runtime and NPM package generator. This will be targeted as a fast turnaround for developer tasks and ease of implementation (+ nice features like supporting a web-playground or REPL). A secondary task is an optimized AOT compiler with the O(1)-GC and and a focus on fast startup, low memory usage, and predictable latency.

## Visual Studio Code Integration

This repository provides basic [Visual Studio Code](https://code.visualstudio.com/) IDE support for the Bosque language (currently limited to syntax and brace highlighting). The installation requires manually copying the full `bosque-language-tools/` folder into your user `.vscode/extensions/` directory and restarting VSCode.

## Contribute

This project welcomes community contributions.

* [Submit bugs](https://github.com/BosqueLanguage/BosqueCore/issues) and help us verify fixes.
* [Submit pull requests](https://github.com/BosqueLanguage/BosqueCore/pulls) for bug fixes and features and discuss existing proposals.
* Chat about the [@BosqueLanguage](https://twitter.com/BosqueLanguage) (or [#BosqueLanguage](https://twitter.com/hashtag/BosqueLanguage)) on Twitter.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/).

## License

Code licensed under the [MIT License](LICENSE.txt).
