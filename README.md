# Bosque Programming Language

[![Licensed under the MIT License](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/BosqueLanguage/BosqueCore/blob/master/LICENSE.txt)
[![PR's Welcome](https://img.shields.io/badge/PRs%20-welcome-brightgreen.svg)](#contribute)
[![Build Health](https://img.shields.io/github/workflow/status/BosqueLanguage/BosqueCore/nodeci)](https://github.com/BosqueLanguage/BosqueCore/actions) 


# The Bosque Project

Bosque is an open-source project developing a new Programming Language and Development Stack. The foundation of this project is the view that mechanization and automated reasoning, along with human and AI agents that leverage them, are the features that will define the next era of software development. The foundation of the Bosque language and stack is a carefully constructed core calculus and computation model that are uniquely amenable to automated reasoning. Building on top of this core calculus the Bosque language, as seen by a developer, is a hybrid of functional programming design, ergonomic block & assignment-based syntax, and a number of new features designed to simplify and support writing high reliability code.

Features in the **_Bosque Programming Language_** include typed strings and paths [TODO], block-syntax [TODO], functor-libs [TODO], dynamic operator multi-dispatch [TODO], ref methods [TODO], explicit-flow typing/binding [TODO], typedecls & datatypes [TODO], task-flows [TODO], and extensive logical assertion integration [TODO]. Logical strutures, like block-syntax, ref methods, and the elimination of loops in favor of functor-libs, allow us to maintain many of the classic benefits of a functionl programming language, with compositional reasoning and immutable state, while providing a familiar and ergonomic block-structured syntax with variable assignment. Data representation features, like typed strings/paths, typedecls, and datatypes, make it simple to express intent and role of a datatype in the application. The logical assertion support features provide builtin mechanisms to specify and check for correct behaviors/values in a program. Finally, the structure of the task-flows, and extensive integration of observability, monitoring, and debugging features in them, are designed to make writing (and maintaing) asynchronous applications, either local or distributed, simple and painless.

The **_Bosque Development Stack_** provides state of the art observability and debugging features (including time-travel debugging) [TODO], a novel symbolic testing framework [TODO], and, with the introduction of APITypes [TODO], a new way to version and validate package behaviors. These features provide a developers with the ability to generate tests for an API before a line of code is even written, test against imported code (or external services) using auto-generated mocks and, check that package updates do not (intentionally or maliciously) change the package behavior, introduce new data outputs, or expose sensitive data to unintended outputs! The testing tools allow for deep analysis of code flows in an appliction and can find compact debuggable inputs that trigger and error or failing test *or* prove that there is no small input that will trigger the error! For any bugs that do make it into the wild the ability to record and then locally replay the exact error accelerates their diagnosis resolution as well as makes _non-repro_ and _intermitent_ issues a thing of the past. 

The **_Bosque Runtime_** is a novel _pathology free_ design that focuses on predictable latency, pauses, and 99th percentile behavior. This starts with a new garbage collector [TODO] that is guaranteed to never need a stop-the-world collection, that only uses live-heap + an additional small constant in memory to run, and supports incremental external defragmentation! Beyond the GC behavior the runtime design excludes pathological regex behavior, dynamic execution bailout overload, and catastrophic amortized operation behaviors such as repeated rehashing (instead using slower but stable log time persistent structures [TODO]). Depending on the application Bosque supports transpilation/compilation to JavaScript [TODO], Morphir [TODO], and an AOT compiler [TODO]. The semantics of the language also open interesting compiler work on eliminating cache conflicts, trusted computation offloading, and compilation for accelerator (e.g. FPGA or dataflow) architectures.

# Documentation

Small samples of code and unique Bosque tooling are below in the [Code Snippets](#Code-Snippets) and [Tooling](#Tooling) sections. Complete documenation for the language and standard libraries are on the [Language](docs/language/overview.md) and [Libraries](docs/libraries/overview.md) doc pages respectively.

Detailed Documentation, Tutorials, and Technical Information:
* [Language Docs](docs/language/overview.md)
* [Library Docs](docs/libraries/overview.md)
* Runtime and GC Docs -- !TODO!
* Checkers -- !TODO!
* [Technical Papers](docs/papers/publist.md)

## Code Snippets

**Add 2 numbers:**
```none
function add2(x: Nat, y: Nat): Nat {
    return x + y;
}

add2(3n, 4n) //7n
add2(3n, 0n) //3n

add2(3i, 4f) //type error -- defined on Nat but given Int and Float args 
add2(3, 4)   //type error -- all numeric literals must have kind specifier
```

**All positive check using rest parameters and lambda:**
```none
function allPositive(args: List<Int>): Bool {
    return args.allOf(fn(x) => x >= 0i);
}

allPositive([1, 3, 4])  //true
allPositive([])         //true
allPositive([1, 3, -4]) //false
```

**Sign (with blocks and assignment):**
```none
function sign(x: Int): Int {
    var y: Int;

    if(x == 0i) {
        y = 0i;
    }
    else {
        y = (x > 0i) ? 1i : -1i;
    }

    return y;
}

sign(5i)    //1
sign(-5i)   //-1
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
        return String::concat("hello ", this.name);
    }
}

GenericGreeting{}.sayHello()          //"hello world"
GenericGreeting::instance.sayHello()  //"hello world"

NamedGreeting{}.sayHello()           //type error no value provided for "name" field
NamedGreeting{""}.sayHello()         //invariant error
NamedGreeting{"bob"}.sayHello()      //"hello bob"
```

**Typedecl Types**
```
typedecl Fahrenheit = Int;
typedecl Celsius = Int;

typedecl Percentage = Nat & {
    invariant $value <= 100n;
}

32i_Fahrenheit + 0i_Celsius //type error different numeric types
30n_Percentage              //valid percentage
101n_Percentage             //invariant error

function isFreezing(temp: Celsius): Bool {
    return temp <= 0i_Celsius;
}

isFreezing(5i)           //type error not a celsius number
isFreezing(5i_Celsius)  //false
isFreezing(-5i_Celsius) //true

```

**Ref Methods:**
```
entity Counter {
    field ctr: Nat;

    function create(): Counter {
        return Counter{0n};
    }

    method ref generateNextID(): Nat {
        let id = this.ctr;
        this = Counter{this.ctr + 1n};

        return id;
    }
} 

var ctr = Counter::create();         //create a Counter 
let id1 = ref ctr.generateNextID(); //id1 is 0 -- ctr is updated
let id2 = ref ctr.generateNextID(); //id2 is 1 -- ctr is updated again
```

**Flow and Binders:**
```
function flowit(x: Nat?): Nat {
    //ITest for none as special
    if none (x) {
        return 0n;
    }
    else {
        //ITest allows binder for $ to value of x (with type inference)
        return $ + 10n;
    }
}

function restrict(x: Nat?): Nat {
    if none (x) {
        return 0n;
    }
    x@<Nat>; //assert that x is a Nat here (error otherwise) and type infer

    return x + 10n;
}
```

**(Algebraic Data Types)++ and Union Types**
```
datatype BoolOp using {
    line: Nat
} of
LConst { val: Bool }
| NotOp { arg: BoolOp }
| AndOp { larg: BoolOp, rarg: BoolOp }
| OrOp { larg: BoolOp, rarg: BoolOp }
& {
    recursive method evaluate(): Bool {
        match(this) {
            LConst  => return $.val;
            | NotOp => return !$.arg.evaluate[recursive]();
            | AndOp => return $.larg.evaluate[recursive]() && $.rarg.evaluate[recursive]();
            | OrOp  => return $.larg.evaluate[recursive]() || $.rarg.evaluate[recursive]();
        }
    } 
}

AndOp{2, LConst{1, true}, LConst{1, false}}.evaluate[recursive]() //false
OrOp{2, LConst{1, true}, LConst{1, false}}.evaluate[recursive]()  //true

function printType(x: Bool | Int | String | None): String {
    return match(x) {
        Bool     => "b"
        | Int    => "i"
        | String => "s"
        | _      => "n"
    };
}

printType(1.0f) //type error
printType(true) //"b"
printType(none) //"n"

```

**Validated Strings:**
```
typedecl ZipcodeUS = /[0-9]{5}(-[0-9]{4})?/;
typedecl CSSpt = /[0-9]+pt/;

function is3pt(s1: StringOf<CSSpt>): Bool {
    return s1.value() === "3pt";
}

ZipcodeUS::accepts("98052-0000") //true
ZipcodeUS::accepts("1234")       //false

is3pt("12")              //type error not a StringOf<CSSpt>
is3pt('98052'_ZipcodeUS) //type error not a StringOf<CSSpt>

is3pt('3pt'_CSSpt) //true
is3pt('4pt'_CSSpt) //false
```

**Tasks:**
```
[TODO]
```

# Installing the Bosque Language (Development)

In order to install/build the project the following are needed:

- 64 bit Operating System
- The LTS version of [node.js](https://nodejs.org/en/download/) ( According to your OS )
- Typescript (install with: `npm i typescript -g`)
- Git and [git-lfs](https://git-lfs.github.com/) setup

## Build & Test

```none
npm install && npm test
```

The Z3 theorem prover is provided as a binary dependency in the repo via git LFS. To ensure these are present you will need to have [git-lfs](https://git-lfs.github.com/) installed, run `git lfs install` to setup the needed hooks, and pull. 

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
