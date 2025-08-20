"use strict";
let _$consts = {};

import { $VRepr, _$softfails, _$supertypes, _$fisSubtype, _$fisNotSubtype, _$fasSubtype, _$fasNotSubtype, _$None, _$not, _$negate, _$add, _$sub, _$mult, _$div, _$bval, _$fkeq, _$fkeqopt, _$fkneq, _$fkneqopt, _$fkless, _$fnumeq, _$fnumless, _$fnumlesseq, _$exhaustive, _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond, _$memoconstval, _$accepts } from "./runtime.mjs";
import { _$setnone_lit, _$parsemap, _$emitmap, _$parseBSQON, _$emitBSQON } from "./bsqon.mjs";

let _$rv = {};

export const CStringOps = {
    "s_empty": (s) => { return s === ""; },
    "s_concat2": (s1, s2) => { return s1 + s2; }
};

export const ListOps = {
    s_list_empty: {
        "<Main::Entry>": (l) => {
            return l.value._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym);
        },
        "<Main::FormatEntry>": (l) => {
            return l.value._$is(ListOps.BBLeaf["<Main::FormatEntry>"].$tsym);
        },
        "<Nat>": (l) => {
            return l.value._$is(ListOps.BBLeaf["<Nat>"].$tsym);
        },
        "<CString>": (l) => {
            return l.value._$is(ListOps.BBLeaf["<CString>"].$tsym);
        }
    },
    s_list_size: {
        "<Main::Entry>": (l) => {
            return ListOps.size["<Main::Entry>"](l.value);
        },
        "<CString>": (l) => {
            return ListOps.size["<CString>"](l.value);
        },
        "<Nat>": (l) => {
            return ListOps.size["<Nat>"](l.value);
        }
    },
    s_list_get: {
        "<Nat>": (l, idx) => {
            return ListOps.get["<Nat>"](l.value, idx);
        },
        "<Main::Entry>": (l, idx) => {
            return ListOps.get["<Main::Entry>"](l.value, idx);
        },
        "<CString>": (l, idx) => {
            return ListOps.get["<CString>"](l.value, idx);
        }
    },
    s_list_set: {
        "<Main::Entry>": (l, idx, v) => {
            return List["<Main::Entry>"].$create(ListOps.set["<Main::Entry>"](l.value, idx, v));
        }
    },
    s_list_push_back: {
        "<Main::Entry>": (l, v) => {
            return List["<Main::Entry>"].$create(ListOps.pushBack["<Main::Entry>"](l.value, v));
        },
        "<CString>": (l, v) => {
            return List["<CString>"].$create(ListOps.pushBack["<CString>"](l.value, v));
        },
        "<Nat>": (l, v) => {
            return List["<Nat>"].$create(ListOps.pushBack["<Nat>"](l.value, v));
        },
        "<Main::FormatEntry>": (l, v) => {
            return List["<Main::FormatEntry>"].$create(ListOps.pushBack["<Main::FormatEntry>"](l.value, v));
        }
    },
    s_list_delete: {
        "<Main::Entry>": (l, idx) => {
            return List["<Main::Entry>"].$create(ListOps.delete["<Main::Entry>"](l.value, idx));
        }
    },
    s_list_create_empty: {
        "<Main::Entry>": () => {
            return List["<Main::Entry>"].$create(ListOps.Tree["<Main::Entry>"].emptyTree());
        },
        "<CString>": () => {
            return List["<CString>"].$create(ListOps.Tree["<CString>"].emptyTree());
        },
        "<Nat>": () => {
            return List["<Nat>"].$create(ListOps.Tree["<Nat>"].emptyTree());
        },
        "<Main::FormatEntry>": () => {
            return List["<Main::FormatEntry>"].$create(ListOps.Tree["<Main::FormatEntry>"].emptyTree());
        }
    },
    s_list_create_1: {
        "<CString>": (v1) => {
            return List["<CString>"].$create(ListOps.Tree["<CString>"].createLeaf(v1));
        }
    },
    s_list_create_2: {
        "<CString>": (v1, v2) => {
            return List["<CString>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), ListOps.Tree["<CString>"].createLeaf(v1), ListOps.Tree["<CString>"].createLeaf(v2)));
        },
        "<Main::FormatEntry>": (v1, v2) => {
            return List["<Main::FormatEntry>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), ListOps.Tree["<Main::FormatEntry>"].createLeaf(v1), ListOps.Tree["<Main::FormatEntry>"].createLeaf(v2)));
        }
    },
    s_list_create_3: {
        "<CString>": (v1, v2, v3) => {
            return List["<CString>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), ListOps.Tree["<CString>"].createLeaf(v1), ListOps.Tree["<CString>"].createNode(ListOps.Color.Red(), ListOps.Tree["<CString>"].createLeaf(v2), ListOps.Tree["<CString>"].createLeaf(v3))));
        },
        "<Main::Entry>": (v1, v2, v3) => {
            return List["<Main::Entry>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), ListOps.Tree["<Main::Entry>"].createLeaf(v1), ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Red(), ListOps.Tree["<Main::Entry>"].createLeaf(v2), ListOps.Tree["<Main::Entry>"].createLeaf(v3))));
        }
    },
    s_list_firstk: {
        "<CString>": (l, k) => {
            return ListOps.s_list_reduce["<CString, List<CString>>"](l, ListOps.s_list_create_empty["<CString>"](), (acc, v) => {  if(ListOps.s_list_size["<CString>"](acc) >= k) {  return acc;  }  else {  return ListOps.s_list_push_back["<CString>"](acc, v);  }  });
        }
    },
    s_list_shiftk: {
        "<CString>": (l, k) => {
            return ListOps.s_list_reduce["<CString, (|List<CString>, Nat|)>"](l, [ListOps.s_list_create_empty["<CString>"](), k], (acc, v) => {  if(acc[1] > 0n) {  return [acc[0], _$sub.Nat(acc[1], 1n)];  }  else {  return [ListOps.s_list_push_back["<CString>"](acc[0], v), 0n];  }  })[0];
        }
    },
    s_list_allof: {
        "<Main::Entry>": (l, p) => {
            return ListOps.Tree["<Main::Entry>"].allof(l.value, p);
        },
        "<Nat>": (l, p) => {
            return ListOps.Tree["<Nat>"].allof(l.value, p);
        }
    },
    s_list_map: {
        "<Main::FormatEntry, Nat>": (l, f) => {
            return List["<Nat>"].$create(ListOps.Tree["<Main::FormatEntry>"].map["<Nat>"](l.value, f));
        }
    },
    s_list_mapidx: {
        "<Main::Entry, Nat>": (l, f) => {
            return List["<Nat>"].$create(ListOps.Tree["<Main::Entry>"].mapidx["<Nat>"](l.value, 0n, f));
        },
        "<CString, CString>": (l, f) => {
            return List["<CString>"].$create(ListOps.Tree["<CString>"].mapidx["<CString>"](l.value, 0n, f));
        }
    },
    s_list_reduce: {
        "<CString, CString>": (l, init, f) => {
            return ListOps.Tree["<CString>"].reduce["<CString>"](l.value, init, f);
        },
        "<CString, List<CString>>": (l, init, f) => {
            return ListOps.Tree["<CString>"].reduce["<List<CString>>"](l.value, init, f);
        },
        "<CString, (|List<CString>, Nat|)>": (l, init, f) => {
            return ListOps.Tree["<CString>"].reduce["<(|List<CString>, Nat|)>"](l.value, init, f);
        },
        "<Main::FormatEntry, (|CString, List<CString>|)>": (l, init, f) => {
            return ListOps.Tree["<Main::FormatEntry>"].reduce["<(|CString, List<CString>|)>"](l.value, init, f);
        }
    },
    s_list_sum: {
        "<Nat>": (l, zero) => {
            return ListOps.Tree["<Nat>"].sum(l.value, zero);
        }
    },
    "redden": (c) => {
        _$assert(_$fkneq.Enum(c, ListOps.Color.NB()), "c !== ListOps::Color#NB @ xcore_list_exec.bsq:438");
        if (_$fkeq.Enum(c, ListOps.Color.BB())) {
            return ListOps.Color.Black();
        }
        else if (_$fkeq.Enum(c, ListOps.Color.Black())) {
            return ListOps.Color.Red();
        }
        else {
            return ListOps.Color.NB();
        }
    },
    balanceHelper_RR_LL: {
        "<Main::Entry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:453"); {
                    return _$None;
                }
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:458"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), lleft.l, lleft.r);
            const nr = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), tleft.r, tright);
            return Some["<ListOps::Node<Main::Entry>>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<CString>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:453"); {
                    return _$None;
                }
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:458"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), lleft.l, lleft.r);
            const nr = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), tleft.r, tright);
            return Some["<ListOps::Node<CString>>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Nat>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:453"); {
                    return _$None;
                }
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:458"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), lleft.l, lleft.r);
            const nr = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), tleft.r, tright);
            return Some["<ListOps::Node<Nat>>"].$create(ListOps.Tree["<Nat>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:453"); {
                    return _$None;
                }
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:458"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), lleft.l, lleft.r);
            const nr = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), tleft.r, tright);
            return Some["<ListOps::Node<Main::FormatEntry>>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.redden(c), nl, nr));
        }
    },
    balanceHelper_RR_LR: {
        "<Main::Entry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:477"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:482"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), tleft.l, lright.l);
            const nr = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<Main::Entry>>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<CString>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:477"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:482"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), tleft.l, lright.l);
            const nr = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<CString>>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Nat>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:477"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:482"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), tleft.l, lright.l);
            const nr = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<Nat>>"].$create(ListOps.Tree["<Nat>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:477"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:482"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tleft.c, ListOps.Color.Red()), _$fkneq.Enum(lright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), tleft.l, lright.l);
            const nr = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<Main::FormatEntry>>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.redden(c), nl, nr));
        }
    },
    balanceHelper_RR_RL: {
        "<Main::Entry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:501"); {
                    return _$None;
                }
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:506"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), rleft.r, tright.r);
            return Some["<ListOps::Node<Main::Entry>>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<CString>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:501"); {
                    return _$None;
                }
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:506"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), rleft.r, tright.r);
            return Some["<ListOps::Node<CString>>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Nat>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:501"); {
                    return _$None;
                }
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:506"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), rleft.r, tright.r);
            return Some["<ListOps::Node<Nat>>"].$create(ListOps.Tree["<Nat>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:501"); {
                    return _$None;
                }
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:506"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rleft.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), rleft.r, tright.r);
            return Some["<ListOps::Node<Main::FormatEntry>>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.redden(c), nl, nr));
        }
    },
    balanceHelper_RR_RR: {
        "<Main::Entry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:525"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:530"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), tleft, tright.l);
            const nr = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), rright.l, rright.r);
            return Some["<ListOps::Node<Main::Entry>>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<CString>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:525"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:530"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), tleft, tright.l);
            const nr = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), rright.l, rright.r);
            return Some["<ListOps::Node<CString>>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Nat>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:525"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:530"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), tleft, tright.l);
            const nr = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), rright.l, rright.r);
            return Some["<ListOps::Node<Nat>>"].$create(ListOps.Tree["<Nat>"].createNode(ListOps.redden(c), nl, nr));
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            if([_$fkneq.Enum(c, ListOps.Color.Black()), _$fkneq.Enum(c, ListOps.Color.BB())].every((ee) => ee)) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:525"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:530"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(tright.c, ListOps.Color.Red()), _$fkneq.Enum(rright.c, ListOps.Color.Red())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), tleft, tright.l);
            const nr = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), rright.l, rright.r);
            return Some["<ListOps::Node<Main::FormatEntry>>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.redden(c), nl, nr));
        }
    },
    balanceHelper_DB_L: {
        "<Main::Entry>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:549"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tleft.c, ListOps.Color.NB())) {
                return _$None;
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:558"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:563"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(lleft.c, ListOps.Color.Black()), _$fkneq.Enum(lright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.balance["<Main::Entry>"](ListOps.Color.Black(), ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Red(), lleft.l, lleft.r), lright.l);
            const nr = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<Main::Entry>>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), nl, nr));
        },
        "<CString>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:549"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tleft.c, ListOps.Color.NB())) {
                return _$None;
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:558"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:563"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(lleft.c, ListOps.Color.Black()), _$fkneq.Enum(lright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.balance["<CString>"](ListOps.Color.Black(), ListOps.Tree["<CString>"].createNode(ListOps.Color.Red(), lleft.l, lleft.r), lright.l);
            const nr = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<CString>>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), nl, nr));
        },
        "<Nat>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:549"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tleft.c, ListOps.Color.NB())) {
                return _$None;
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:558"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:563"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(lleft.c, ListOps.Color.Black()), _$fkneq.Enum(lright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.balance["<Nat>"](ListOps.Color.Black(), ListOps.Tree["<Nat>"].createNode(ListOps.Color.Red(), lleft.l, lleft.r), lright.l);
            const nr = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<Nat>>"].$create(ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), nl, nr));
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tleft = tleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:549"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tleft.c, ListOps.Color.NB())) {
                return _$None;
            }

            const lleft = tleft.l;

            if(lleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $lleft = lleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:558"); {
                    return _$None;
                }
            }

            const lright = tleft.r;

            if(lright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $lright = lright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:563"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(lleft.c, ListOps.Color.Black()), _$fkneq.Enum(lright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.balance["<Main::FormatEntry>"](ListOps.Color.Black(), ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Red(), lleft.l, lleft.r), lright.l);
            const nr = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), lright.r, tright);
            return Some["<ListOps::Node<Main::FormatEntry>>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), nl, nr));
        }
    },
    balanceHelper_DB_R: {
        "<Main::Entry>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:582"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tright.c, ListOps.Color.NB())) {
                return _$None;
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:591"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:596"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(rleft.c, ListOps.Color.Black()), _$fkneq.Enum(rright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.balance["<Main::Entry>"](ListOps.Color.Black(), rleft.r, ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Red(), rright.l, rright.r));
            return Some["<ListOps::Node<Main::Entry>>"].$create(ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), nl, nr));
        },
        "<CString>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:582"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tright.c, ListOps.Color.NB())) {
                return _$None;
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:591"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:596"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(rleft.c, ListOps.Color.Black()), _$fkneq.Enum(rright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.balance["<CString>"](ListOps.Color.Black(), rleft.r, ListOps.Tree["<CString>"].createNode(ListOps.Color.Red(), rright.l, rright.r));
            return Some["<ListOps::Node<CString>>"].$create(ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), nl, nr));
        },
        "<Nat>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:582"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tright.c, ListOps.Color.NB())) {
                return _$None;
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:591"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:596"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(rleft.c, ListOps.Color.Black()), _$fkneq.Enum(rright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.balance["<Nat>"](ListOps.Color.Black(), rleft.r, ListOps.Tree["<Nat>"].createNode(ListOps.Color.Red(), rright.l, rright.r));
            return Some["<ListOps::Node<Nat>>"].$create(ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), nl, nr));
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            if(_$fkneq.Enum(c, ListOps.Color.BB())) {
                return _$None;
            }

            if(tright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tright = tright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:582"); {
                    return _$None;
                }
            }

            if(_$fkneq.Enum(tright.c, ListOps.Color.NB())) {
                return _$None;
            }

            const rleft = tright.l;

            if(rleft._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $rleft = rleft._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:591"); {
                    return _$None;
                }
            }

            const rright = tright.r;

            if(rright._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $rright = rright._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:596"); {
                    return _$None;
                }
            }

            if((![_$fkneq.Enum(rleft.c, ListOps.Color.Black()), _$fkneq.Enum(rright.c, ListOps.Color.Black())].every((ee) => !ee))) {
                return _$None;
            }

            const nl = ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), tleft, rleft.l);
            const nr = ListOps.balance["<Main::FormatEntry>"](ListOps.Color.Black(), rleft.r, ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Red(), rright.l, rright.r));
            return Some["<ListOps::Node<Main::FormatEntry>>"].$create(ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), nl, nr));
        }
    },
    balance: {
        "<Main::Entry>": (c, tleft, tright) => {
            const doubleRedLL = ListOps.balanceHelper_RR_LL["<Main::Entry>"](c, tleft, tright);

            if(doubleRedLL._$isNotNone()) {
                let $doubleRedLL = doubleRedLL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:611"); {
                    return $doubleRedLL;
                }
            }

            const doubleRedLR = ListOps.balanceHelper_RR_LR["<Main::Entry>"](c, tleft, tright);

            if(doubleRedLR._$isNotNone()) {
                let $doubleRedLR = doubleRedLR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:616"); {
                    return $doubleRedLR;
                }
            }

            const doubleRedRL = ListOps.balanceHelper_RR_RL["<Main::Entry>"](c, tleft, tright);

            if(doubleRedRL._$isNotNone()) {
                let $doubleRedRL = doubleRedRL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:621"); {
                    return $doubleRedRL;
                }
            }

            const doubleRedRR = ListOps.balanceHelper_RR_RR["<Main::Entry>"](c, tleft, tright);

            if(doubleRedRR._$isNotNone()) {
                let $doubleRedRR = doubleRedRR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:626"); {
                    return $doubleRedRR;
                }
            }

            const negBlackL = ListOps.balanceHelper_DB_L["<Main::Entry>"](c, tleft, tright);

            if(negBlackL._$isNotNone()) {
                let $negBlackL = negBlackL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:631"); {
                    return $negBlackL;
                }
            }

            const negBlackR = ListOps.balanceHelper_DB_R["<Main::Entry>"](c, tleft, tright);

            if(negBlackR._$isNotNone()) {
                let $negBlackR = negBlackR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:636"); {
                    return $negBlackR;
                }
            }

            return ListOps.Tree["<Main::Entry>"].createNode(c, tleft, tright);
        },
        "<CString>": (c, tleft, tright) => {
            const doubleRedLL = ListOps.balanceHelper_RR_LL["<CString>"](c, tleft, tright);

            if(doubleRedLL._$isNotNone()) {
                let $doubleRedLL = doubleRedLL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:611"); {
                    return $doubleRedLL;
                }
            }

            const doubleRedLR = ListOps.balanceHelper_RR_LR["<CString>"](c, tleft, tright);

            if(doubleRedLR._$isNotNone()) {
                let $doubleRedLR = doubleRedLR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:616"); {
                    return $doubleRedLR;
                }
            }

            const doubleRedRL = ListOps.balanceHelper_RR_RL["<CString>"](c, tleft, tright);

            if(doubleRedRL._$isNotNone()) {
                let $doubleRedRL = doubleRedRL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:621"); {
                    return $doubleRedRL;
                }
            }

            const doubleRedRR = ListOps.balanceHelper_RR_RR["<CString>"](c, tleft, tright);

            if(doubleRedRR._$isNotNone()) {
                let $doubleRedRR = doubleRedRR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:626"); {
                    return $doubleRedRR;
                }
            }

            const negBlackL = ListOps.balanceHelper_DB_L["<CString>"](c, tleft, tright);

            if(negBlackL._$isNotNone()) {
                let $negBlackL = negBlackL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:631"); {
                    return $negBlackL;
                }
            }

            const negBlackR = ListOps.balanceHelper_DB_R["<CString>"](c, tleft, tright);

            if(negBlackR._$isNotNone()) {
                let $negBlackR = negBlackR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:636"); {
                    return $negBlackR;
                }
            }

            return ListOps.Tree["<CString>"].createNode(c, tleft, tright);
        },
        "<Nat>": (c, tleft, tright) => {
            const doubleRedLL = ListOps.balanceHelper_RR_LL["<Nat>"](c, tleft, tright);

            if(doubleRedLL._$isNotNone()) {
                let $doubleRedLL = doubleRedLL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:611"); {
                    return $doubleRedLL;
                }
            }

            const doubleRedLR = ListOps.balanceHelper_RR_LR["<Nat>"](c, tleft, tright);

            if(doubleRedLR._$isNotNone()) {
                let $doubleRedLR = doubleRedLR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:616"); {
                    return $doubleRedLR;
                }
            }

            const doubleRedRL = ListOps.balanceHelper_RR_RL["<Nat>"](c, tleft, tright);

            if(doubleRedRL._$isNotNone()) {
                let $doubleRedRL = doubleRedRL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:621"); {
                    return $doubleRedRL;
                }
            }

            const doubleRedRR = ListOps.balanceHelper_RR_RR["<Nat>"](c, tleft, tright);

            if(doubleRedRR._$isNotNone()) {
                let $doubleRedRR = doubleRedRR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:626"); {
                    return $doubleRedRR;
                }
            }

            const negBlackL = ListOps.balanceHelper_DB_L["<Nat>"](c, tleft, tright);

            if(negBlackL._$isNotNone()) {
                let $negBlackL = negBlackL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:631"); {
                    return $negBlackL;
                }
            }

            const negBlackR = ListOps.balanceHelper_DB_R["<Nat>"](c, tleft, tright);

            if(negBlackR._$isNotNone()) {
                let $negBlackR = negBlackR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:636"); {
                    return $negBlackR;
                }
            }

            return ListOps.Tree["<Nat>"].createNode(c, tleft, tright);
        },
        "<Main::FormatEntry>": (c, tleft, tright) => {
            const doubleRedLL = ListOps.balanceHelper_RR_LL["<Main::FormatEntry>"](c, tleft, tright);

            if(doubleRedLL._$isNotNone()) {
                let $doubleRedLL = doubleRedLL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:611"); {
                    return $doubleRedLL;
                }
            }

            const doubleRedLR = ListOps.balanceHelper_RR_LR["<Main::FormatEntry>"](c, tleft, tright);

            if(doubleRedLR._$isNotNone()) {
                let $doubleRedLR = doubleRedLR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:616"); {
                    return $doubleRedLR;
                }
            }

            const doubleRedRL = ListOps.balanceHelper_RR_RL["<Main::FormatEntry>"](c, tleft, tright);

            if(doubleRedRL._$isNotNone()) {
                let $doubleRedRL = doubleRedRL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:621"); {
                    return $doubleRedRL;
                }
            }

            const doubleRedRR = ListOps.balanceHelper_RR_RR["<Main::FormatEntry>"](c, tleft, tright);

            if(doubleRedRR._$isNotNone()) {
                let $doubleRedRR = doubleRedRR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:626"); {
                    return $doubleRedRR;
                }
            }

            const negBlackL = ListOps.balanceHelper_DB_L["<Main::FormatEntry>"](c, tleft, tright);

            if(negBlackL._$isNotNone()) {
                let $negBlackL = negBlackL._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:631"); {
                    return $negBlackL;
                }
            }

            const negBlackR = ListOps.balanceHelper_DB_R["<Main::FormatEntry>"](c, tleft, tright);

            if(negBlackR._$isNotNone()) {
                let $negBlackR = negBlackR._$asNotNone("expected Some but got None @ xcore_list_exec.bsq:636"); {
                    return $negBlackR;
                }
            }

            return ListOps.Tree["<Main::FormatEntry>"].createNode(c, tleft, tright);
        }
    },
    bubble: {
        "<Main::Entry>": (c, tleft, tright) => {
            if(tleft._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym)) {
                return tright;
            }

            if(tright._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym)) {
                return tleft;
            }

            return ListOps.balance["<Main::Entry>"](c, tleft, tright);
        }
    },
    size: {
        "<CString>": (t) => {
            if (t._$is(ListOps.BBLeaf["<CString>"].$tsym)) { let $t = t; {
                    return 0n;
                }
            }
            else if (t._$is(ListOps.Leaf["<CString>"].$tsym)) { let $t = t; {
                    return 1n;
                }
            }
            else { let $t = t; {
                    return $t.count;
                }
            }
        },
        "<Main::Entry>": (t) => {
            if (t._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym)) { let $t = t; {
                    return 0n;
                }
            }
            else if (t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) { let $t = t; {
                    return 1n;
                }
            }
            else { let $t = t; {
                    return $t.count;
                }
            }
        },
        "<Main::FormatEntry>": (t) => {
            if (t._$is(ListOps.BBLeaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                    return 0n;
                }
            }
            else if (t._$is(ListOps.Leaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                    return 1n;
                }
            }
            else { let $t = t; {
                    return $t.count;
                }
            }
        },
        "<Nat>": (t) => {
            if (t._$is(ListOps.BBLeaf["<Nat>"].$tsym)) { let $t = t; {
                    return 0n;
                }
            }
            else if (t._$is(ListOps.Leaf["<Nat>"].$tsym)) { let $t = t; {
                    return 1n;
                }
            }
            else { let $t = t; {
                    return $t.count;
                }
            }
        }
    },
    get: {
        "<Nat>": (t, idx) => {
            if(t._$is(ListOps.Leaf["<Nat>"].$tsym)) {
                let $t = t._$as(ListOps.Leaf["<Nat>"].$tsym, "expected type ListOps::Leaf<Nat> @ xcore_list_exec.bsq:690"); {
                    return $t.v;
                }
            }
            else {
                let $t = t._$asNot(ListOps.Leaf["<Nat>"].$tsym, "expected different type than ListOps::Leaf<Nat> @ xcore_list_exec.bsq:690"); {
                    const nn = t;
                    const count = ListOps.size["<Nat>"](nn.l);
                    if(idx < count) {
                        return ListOps.get["<Nat>"](nn.l, idx);
                    }
                    else {
                        return ListOps.get["<Nat>"](nn.r, _$sub.Nat(idx, count));
                    }
                }
            }
        },
        "<Main::Entry>": (t, idx) => {
            if(t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) {
                let $t = t._$as(ListOps.Leaf["<Main::Entry>"].$tsym, "expected type ListOps::Leaf<Main::Entry> @ xcore_list_exec.bsq:690"); {
                    return $t.v;
                }
            }
            else {
                let $t = t._$asNot(ListOps.Leaf["<Main::Entry>"].$tsym, "expected different type than ListOps::Leaf<Main::Entry> @ xcore_list_exec.bsq:690"); {
                    const nn = t;
                    const count = ListOps.size["<Main::Entry>"](nn.l);
                    if(idx < count) {
                        return ListOps.get["<Main::Entry>"](nn.l, idx);
                    }
                    else {
                        return ListOps.get["<Main::Entry>"](nn.r, _$sub.Nat(idx, count));
                    }
                }
            }
        },
        "<CString>": (t, idx) => {
            if(t._$is(ListOps.Leaf["<CString>"].$tsym)) {
                let $t = t._$as(ListOps.Leaf["<CString>"].$tsym, "expected type ListOps::Leaf<CString> @ xcore_list_exec.bsq:690"); {
                    return $t.v;
                }
            }
            else {
                let $t = t._$asNot(ListOps.Leaf["<CString>"].$tsym, "expected different type than ListOps::Leaf<CString> @ xcore_list_exec.bsq:690"); {
                    const nn = t;
                    const count = ListOps.size["<CString>"](nn.l);
                    if(idx < count) {
                        return ListOps.get["<CString>"](nn.l, idx);
                    }
                    else {
                        return ListOps.get["<CString>"](nn.r, _$sub.Nat(idx, count));
                    }
                }
            }
        }
    },
    set: {
        "<Main::Entry>": (t, idx, v) => {
            if(t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) {
                let $t = t._$as(ListOps.Leaf["<Main::Entry>"].$tsym, "expected type ListOps::Leaf<Main::Entry> @ xcore_list_exec.bsq:727"); {
                    return ListOps.Tree["<Main::Entry>"].createLeaf(v);
                }
            }
            else {
                let $t = t._$asNot(ListOps.Leaf["<Main::Entry>"].$tsym, "expected different type than ListOps::Leaf<Main::Entry> @ xcore_list_exec.bsq:727"); {
                    const nn = t;
                    const count = ListOps.size["<Main::Entry>"](nn.l);
                    if(idx < count) {
                        return ListOps.Tree["<Main::Entry>"].createNode(nn.c, ListOps.set["<Main::Entry>"](nn.l, idx, v), nn.r);
                    }
                    else {
                        return ListOps.Tree["<Main::Entry>"].createNode(nn.c, nn.l, ListOps.set["<Main::Entry>"](nn.r, _$sub.Nat(idx, count), v));
                    }
                }
            }
        }
    },
    pushBack_helper: {
        "<Main::Entry>": (t, v) => {
            if (t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) { let $t = t; {
                    return ListOps.balance["<Main::Entry>"](ListOps.Color.Red(), $t, ListOps.Tree["<Main::Entry>"].createLeaf(v));
                }
            }
            else {
                _$exhaustive((t._$is(ListOps.Node["<Main::Entry>"].$tsym)), "exhaustive switch @ xcore_list_exec.bsq:744");
                { let $t = t; {
                        const nr = ListOps.pushBack_helper["<Main::Entry>"]($t.r, v);
                        return ListOps.balance["<Main::Entry>"]($t.c, $t.l, nr);
                    }
                }
            }
        },
        "<CString>": (t, v) => {
            if (t._$is(ListOps.Leaf["<CString>"].$tsym)) { let $t = t; {
                    return ListOps.balance["<CString>"](ListOps.Color.Red(), $t, ListOps.Tree["<CString>"].createLeaf(v));
                }
            }
            else {
                _$exhaustive((t._$is(ListOps.Node["<CString>"].$tsym)), "exhaustive switch @ xcore_list_exec.bsq:744");
                { let $t = t; {
                        const nr = ListOps.pushBack_helper["<CString>"]($t.r, v);
                        return ListOps.balance["<CString>"]($t.c, $t.l, nr);
                    }
                }
            }
        },
        "<Nat>": (t, v) => {
            if (t._$is(ListOps.Leaf["<Nat>"].$tsym)) { let $t = t; {
                    return ListOps.balance["<Nat>"](ListOps.Color.Red(), $t, ListOps.Tree["<Nat>"].createLeaf(v));
                }
            }
            else {
                _$exhaustive((t._$is(ListOps.Node["<Nat>"].$tsym)), "exhaustive switch @ xcore_list_exec.bsq:744");
                { let $t = t; {
                        const nr = ListOps.pushBack_helper["<Nat>"]($t.r, v);
                        return ListOps.balance["<Nat>"]($t.c, $t.l, nr);
                    }
                }
            }
        },
        "<Main::FormatEntry>": (t, v) => {
            if (t._$is(ListOps.Leaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                    return ListOps.balance["<Main::FormatEntry>"](ListOps.Color.Red(), $t, ListOps.Tree["<Main::FormatEntry>"].createLeaf(v));
                }
            }
            else {
                _$exhaustive((t._$is(ListOps.Node["<Main::FormatEntry>"].$tsym)), "exhaustive switch @ xcore_list_exec.bsq:744");
                { let $t = t; {
                        const nr = ListOps.pushBack_helper["<Main::FormatEntry>"]($t.r, v);
                        return ListOps.balance["<Main::FormatEntry>"]($t.c, $t.l, nr);
                    }
                }
            }
        }
    },
    pushBack: {
        "<Main::Entry>": (t, v) => {
            if(t._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym)) {
                return ListOps.Tree["<Main::Entry>"].createLeaf(v);
            }

            const tt = ListOps.pushBack_helper["<Main::Entry>"](t, v);
            if(tt._$isNot(ListOps.Node["<Main::Entry>"].$tsym)) {
                let $tt = tt._$asNot(ListOps.Node["<Main::Entry>"].$tsym, "expected different type than ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:759"); {
                    return tt;
                }
            }
            else {
                let $tt = tt._$as(ListOps.Node["<Main::Entry>"].$tsym, "expected type ListOps::Node<Main::Entry> @ xcore_list_exec.bsq:759"); {
                    const nt = _$fkeq.Enum($tt.c, ListOps.Color.Red()) ? ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), $tt.l, $tt.r) : $tt;
                    return nt;
                }
            }
        },
        "<CString>": (t, v) => {
            if(t._$is(ListOps.BBLeaf["<CString>"].$tsym)) {
                return ListOps.Tree["<CString>"].createLeaf(v);
            }

            const tt = ListOps.pushBack_helper["<CString>"](t, v);
            if(tt._$isNot(ListOps.Node["<CString>"].$tsym)) {
                let $tt = tt._$asNot(ListOps.Node["<CString>"].$tsym, "expected different type than ListOps::Node<CString> @ xcore_list_exec.bsq:759"); {
                    return tt;
                }
            }
            else {
                let $tt = tt._$as(ListOps.Node["<CString>"].$tsym, "expected type ListOps::Node<CString> @ xcore_list_exec.bsq:759"); {
                    const nt = _$fkeq.Enum($tt.c, ListOps.Color.Red()) ? ListOps.Tree["<CString>"].createNode(ListOps.Color.Black(), $tt.l, $tt.r) : $tt;
                    return nt;
                }
            }
        },
        "<Nat>": (t, v) => {
            if(t._$is(ListOps.BBLeaf["<Nat>"].$tsym)) {
                return ListOps.Tree["<Nat>"].createLeaf(v);
            }

            const tt = ListOps.pushBack_helper["<Nat>"](t, v);
            if(tt._$isNot(ListOps.Node["<Nat>"].$tsym)) {
                let $tt = tt._$asNot(ListOps.Node["<Nat>"].$tsym, "expected different type than ListOps::Node<Nat> @ xcore_list_exec.bsq:759"); {
                    return tt;
                }
            }
            else {
                let $tt = tt._$as(ListOps.Node["<Nat>"].$tsym, "expected type ListOps::Node<Nat> @ xcore_list_exec.bsq:759"); {
                    const nt = _$fkeq.Enum($tt.c, ListOps.Color.Red()) ? ListOps.Tree["<Nat>"].createNode(ListOps.Color.Black(), $tt.l, $tt.r) : $tt;
                    return nt;
                }
            }
        },
        "<Main::FormatEntry>": (t, v) => {
            if(t._$is(ListOps.BBLeaf["<Main::FormatEntry>"].$tsym)) {
                return ListOps.Tree["<Main::FormatEntry>"].createLeaf(v);
            }

            const tt = ListOps.pushBack_helper["<Main::FormatEntry>"](t, v);
            if(tt._$isNot(ListOps.Node["<Main::FormatEntry>"].$tsym)) {
                let $tt = tt._$asNot(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected different type than ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:759"); {
                    return tt;
                }
            }
            else {
                let $tt = tt._$as(ListOps.Node["<Main::FormatEntry>"].$tsym, "expected type ListOps::Node<Main::FormatEntry> @ xcore_list_exec.bsq:759"); {
                    const nt = _$fkeq.Enum($tt.c, ListOps.Color.Red()) ? ListOps.Tree["<Main::FormatEntry>"].createNode(ListOps.Color.Black(), $tt.l, $tt.r) : $tt;
                    return nt;
                }
            }
        }
    },
    delete_helper: {
        "<Main::Entry>": (t, idx) => {
            if (t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) { let $t = t; {
                    return ListOps.Tree["<Main::Entry>"].emptyTree();
                }
            }
            else {
                _$exhaustive((t._$is(ListOps.Node["<Main::Entry>"].$tsym)), "exhaustive switch @ xcore_list_exec.bsq:836");
                { let $t = t; {
                        const count = ListOps.size["<Main::Entry>"]($t.l);
                        if(idx < count) {
                            const nl = ListOps.delete_helper["<Main::Entry>"]($t.l, idx);
                            return ListOps.bubble["<Main::Entry>"]($t.c, nl, $t.r);
                        }
                        else {
                            const nr = ListOps.delete_helper["<Main::Entry>"]($t.r, _$sub.Nat(idx, count));
                            return ListOps.bubble["<Main::Entry>"]($t.c, $t.l, nr);
                        }
                    }
                }
            }
        }
    },
    delete: {
        "<Main::Entry>": (t, idx) => {
            const nt = ListOps.delete_helper["<Main::Entry>"](t, idx);
            if (nt._$is(ListOps.Node["<Main::Entry>"].$tsym)) { let $nt = nt; {
                    const ntt = _$fkeq.Enum($nt.c, ListOps.Color.Red()) ? ListOps.Tree["<Main::Entry>"].createNode(ListOps.Color.Black(), $nt.l, $nt.r) : nt;
                    return ntt;
                }
            }
            else { let $nt = nt; {
                    return nt;
                }
            }
        }
    },
    Color: Object.create($VRepr, {
        $tsym: { value: Symbol.for("ListOps::Color") },
        _$memomap: { value: {} },
        Red: {value: function() { return _$memoconstval(this._$memomap, "Red", () => Object.create(ListOps.Color, { value: { value: 0n } })); } },
        Black: {value: function() { return _$memoconstval(this._$memomap, "Black", () => Object.create(ListOps.Color, { value: { value: 1n } })); } },
        BB: {value: function() { return _$memoconstval(this._$memomap, "BB", () => Object.create(ListOps.Color, { value: { value: 2n } })); } },
        NB: {value: function() { return _$memoconstval(this._$memomap, "NB", () => Object.create(ListOps.Color, { value: { value: 3n } })); } },
        $parseAPI: { value: (parser) => { parser.checkConsType("ListOps::Color"); const ename = parser.parseEnumNameComponent(); return ListOps.Color[ename](); } },
        $emitAPI: { value: (emitter, value) => { return "ListOps::Color" + "#" + [mm, mm, mm, mm][value.value]; } }
    }),
    Tree: {
        "<CString>": Object.create(Object.prototype, {
            $tsym: { value: Symbol.for("ListOps::Tree<CString>") },
            _$consts: { value: {} },
            emptyTree: { value: function () { return _$memoconstval(this._$consts, "emptyTree", () => ListOps.BBLeaf["<CString>"].$create()); } },
            createLeaf:  { value: (v) => {
                return ListOps.Leaf["<CString>"].$create(v);
            } },
            createNode:  { value: (c, l, r) => {
                return ListOps.Node["<CString>"].$create(c, _$add.Nat(ListOps.size["<CString>"](l), ListOps.size["<CString>"](r)), l, r);
            } },
            mapidx: { value: {
                "<CString>": (t, cidx, f) => {
                    if (t._$is(ListOps.BBLeaf["<CString>"].$tsym)) { let $t = t; {
                            return ListOps.BBLeaf["<CString>"].$create();
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<CString>"].$tsym)) { let $t = t; {
                            return ListOps.Leaf["<CString>"].$create(f($t.v, cidx));
                        }
                    }
                    else { let $t = t; {
                            const nl = ListOps.Tree["<CString>"].mapidx["<CString>"]($t.l, cidx, f);
                            const nr = ListOps.Tree["<CString>"].mapidx["<CString>"]($t.r, _$add.Nat(cidx, ListOps.size["<CString>"]($t.l)), f);
                            return ListOps.Node["<CString>"].$create($t.c, $t.count, nl, nr);
                        }
                    }
                }
            } },
            reduce: { value: {
                "<CString>": (t, acc, f) => {
                    if (t._$is(ListOps.BBLeaf["<CString>"].$tsym)) { let $t = t; {
                            return acc;
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<CString>"].$tsym)) { let $t = t; {
                            return f(acc, $t.v);
                        }
                    }
                    else { let $t = t; {
                            return ListOps.Tree["<CString>"].reduce["<CString>"]($t.r, ListOps.Tree["<CString>"].reduce["<CString>"]($t.l, acc, f), f);
                        }
                    }
                },
                "<List<CString>>": (t, acc, f) => {
                    if (t._$is(ListOps.BBLeaf["<CString>"].$tsym)) { let $t = t; {
                            return acc;
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<CString>"].$tsym)) { let $t = t; {
                            return f(acc, $t.v);
                        }
                    }
                    else { let $t = t; {
                            return ListOps.Tree["<CString>"].reduce["<List<CString>>"]($t.r, ListOps.Tree["<CString>"].reduce["<List<CString>>"]($t.l, acc, f), f);
                        }
                    }
                },
                "<(|List<CString>, Nat|)>": (t, acc, f) => {
                    if (t._$is(ListOps.BBLeaf["<CString>"].$tsym)) { let $t = t; {
                            return acc;
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<CString>"].$tsym)) { let $t = t; {
                            return f(acc, $t.v);
                        }
                    }
                    else { let $t = t; {
                            return ListOps.Tree["<CString>"].reduce["<(|List<CString>, Nat|)>"]($t.r, ListOps.Tree["<CString>"].reduce["<(|List<CString>, Nat|)>"]($t.l, acc, f), f);
                        }
                    }
                }
            } },
            $parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } },
            $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
        }),
        "<Main::Entry>": Object.create(Object.prototype, {
            $tsym: { value: Symbol.for("ListOps::Tree<Main::Entry>") },
            _$consts: { value: {} },
            emptyTree: { value: function () { return _$memoconstval(this._$consts, "emptyTree", () => ListOps.BBLeaf["<Main::Entry>"].$create()); } },
            createLeaf:  { value: (v) => {
                return ListOps.Leaf["<Main::Entry>"].$create(v);
            } },
            createNode:  { value: (c, l, r) => {
                return ListOps.Node["<Main::Entry>"].$create(c, _$add.Nat(ListOps.size["<Main::Entry>"](l), ListOps.size["<Main::Entry>"](r)), l, r);
            } },
            allof:  { value: (t, p) => {
                if (t._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym)) { let $t = t; {
                        return true;
                    }
                }
                else if (t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) { let $t = t; {
                        return p($t.v);
                    }
                }
                else { let $t = t; {
                        const nl = ListOps.Tree["<Main::Entry>"].allof($t.l, p);
                        if(!nl) {
                            return false;
                        }
                        else {
                            const nr = ListOps.Tree["<Main::Entry>"].allof($t.r, p);
                            return nr;
                        }
                    }
                }
            } },
            mapidx: { value: {
                "<Nat>": (t, cidx, f) => {
                    if (t._$is(ListOps.BBLeaf["<Main::Entry>"].$tsym)) { let $t = t; {
                            return ListOps.BBLeaf["<Nat>"].$create();
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<Main::Entry>"].$tsym)) { let $t = t; {
                            return ListOps.Leaf["<Nat>"].$create(f($t.v, cidx));
                        }
                    }
                    else { let $t = t; {
                            const nl = ListOps.Tree["<Main::Entry>"].mapidx["<Nat>"]($t.l, cidx, f);
                            const nr = ListOps.Tree["<Main::Entry>"].mapidx["<Nat>"]($t.r, _$add.Nat(cidx, ListOps.size["<Main::Entry>"]($t.l)), f);
                            return ListOps.Node["<Nat>"].$create($t.c, $t.count, nl, nr);
                        }
                    }
                }
            } },
            $parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } },
            $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
        }),
        "<Main::FormatEntry>": Object.create(Object.prototype, {
            $tsym: { value: Symbol.for("ListOps::Tree<Main::FormatEntry>") },
            _$consts: { value: {} },
            emptyTree: { value: function () { return _$memoconstval(this._$consts, "emptyTree", () => ListOps.BBLeaf["<Main::FormatEntry>"].$create()); } },
            createLeaf:  { value: (v) => {
                return ListOps.Leaf["<Main::FormatEntry>"].$create(v);
            } },
            createNode:  { value: (c, l, r) => {
                return ListOps.Node["<Main::FormatEntry>"].$create(c, _$add.Nat(ListOps.size["<Main::FormatEntry>"](l), ListOps.size["<Main::FormatEntry>"](r)), l, r);
            } },
            map: { value: {
                "<Nat>": (t, f) => {
                    if (t._$is(ListOps.BBLeaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                            return ListOps.BBLeaf["<Nat>"].$create();
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                            return ListOps.Leaf["<Nat>"].$create(f($t.v));
                        }
                    }
                    else { let $t = t; {
                            const nl = ListOps.Tree["<Main::FormatEntry>"].map["<Nat>"]($t.l, f);
                            const nr = ListOps.Tree["<Main::FormatEntry>"].map["<Nat>"]($t.r, f);
                            return ListOps.Node["<Nat>"].$create($t.c, $t.count, nl, nr);
                        }
                    }
                }
            } },
            reduce: { value: {
                "<(|CString, List<CString>|)>": (t, acc, f) => {
                    if (t._$is(ListOps.BBLeaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                            return acc;
                        }
                    }
                    else if (t._$is(ListOps.Leaf["<Main::FormatEntry>"].$tsym)) { let $t = t; {
                            return f(acc, $t.v);
                        }
                    }
                    else { let $t = t; {
                            return ListOps.Tree["<Main::FormatEntry>"].reduce["<(|CString, List<CString>|)>"]($t.r, ListOps.Tree["<Main::FormatEntry>"].reduce["<(|CString, List<CString>|)>"]($t.l, acc, f), f);
                        }
                    }
                }
            } },
            $parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } },
            $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
        }),
        "<Nat>": Object.create(Object.prototype, {
            $tsym: { value: Symbol.for("ListOps::Tree<Nat>") },
            _$consts: { value: {} },
            emptyTree: { value: function () { return _$memoconstval(this._$consts, "emptyTree", () => ListOps.BBLeaf["<Nat>"].$create()); } },
            createLeaf:  { value: (v) => {
                return ListOps.Leaf["<Nat>"].$create(v);
            } },
            createNode:  { value: (c, l, r) => {
                return ListOps.Node["<Nat>"].$create(c, _$add.Nat(ListOps.size["<Nat>"](l), ListOps.size["<Nat>"](r)), l, r);
            } },
            allof:  { value: (t, p) => {
                if (t._$is(ListOps.BBLeaf["<Nat>"].$tsym)) { let $t = t; {
                        return true;
                    }
                }
                else if (t._$is(ListOps.Leaf["<Nat>"].$tsym)) { let $t = t; {
                        return p($t.v);
                    }
                }
                else { let $t = t; {
                        const nl = ListOps.Tree["<Nat>"].allof($t.l, p);
                        if(!nl) {
                            return false;
                        }
                        else {
                            const nr = ListOps.Tree["<Nat>"].allof($t.r, p);
                            return nr;
                        }
                    }
                }
            } },
            sum:  { value: (t, acc) => {
                if (t._$is(ListOps.BBLeaf["<Nat>"].$tsym)) { let $t = t; {
                        return acc;
                    }
                }
                else if (t._$is(ListOps.Leaf["<Nat>"].$tsym)) { let $t = t; {
                        return _$add.Nat(acc, $t.v);
                    }
                }
                else { let $t = t; {
                        return ListOps.Tree["<Nat>"].sum($t.r, ListOps.Tree["<Nat>"].sum($t.l, acc));
                    }
                }
            } },
            $parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } },
            $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
        })
    },
    BBLeaf: {
        "<CString>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::BBLeaf<CString>") },
            $create: { value: () => {
                return Object.create(ListOps.BBLeaf["<CString>"], {  });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.BBLeaf["<CString>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return ""; } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Main::Entry>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::BBLeaf<Main::Entry>") },
            $create: { value: () => {
                return Object.create(ListOps.BBLeaf["<Main::Entry>"], {  });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.BBLeaf["<Main::Entry>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return ""; } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Main::FormatEntry>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::BBLeaf<Main::FormatEntry>") },
            $create: { value: () => {
                return Object.create(ListOps.BBLeaf["<Main::FormatEntry>"], {  });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.BBLeaf["<Main::FormatEntry>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return ""; } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Nat>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::BBLeaf<Nat>") },
            $create: { value: () => {
                return Object.create(ListOps.BBLeaf["<Nat>"], {  });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.BBLeaf["<Nat>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return ""; } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        })
    },
    Leaf: {
        "<CString>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Leaf<CString>") },
            $create: { value: (v) => {
                return Object.create(ListOps.Leaf["<CString>"], { v: { value: v, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Leaf["<CString>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return emitter.emitValue("CString", value.v); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Main::Entry>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Leaf<Main::Entry>") },
            $create: { value: (v) => {
                return Object.create(ListOps.Leaf["<Main::Entry>"], { v: { value: v, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Leaf["<Main::Entry>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return emitter.emitValue("Main::Entry", value.v); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Main::FormatEntry>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Leaf<Main::FormatEntry>") },
            $create: { value: (v) => {
                return Object.create(ListOps.Leaf["<Main::FormatEntry>"], { v: { value: v, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Leaf["<Main::FormatEntry>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return emitter.emitValue("Main::FormatEntry", value.v); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Nat>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Leaf<Nat>") },
            $create: { value: (v) => {
                return Object.create(ListOps.Leaf["<Nat>"], { v: { value: v, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Leaf["<Nat>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return emitter.emitValue("Nat", value.v); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        })
    },
    Node: {
        "<CString>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Node<CString>") },
            $create: { value: (c, count, l, r) => {
                return Object.create(ListOps.Node["<CString>"], { c: { value: c, enumerable: true }, count: { value: count, enumerable: true }, l: { value: l, enumerable: true }, r: { value: r, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Node["<CString>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return [emitter.emitValue("ListOps::Tree<CString>", value.l), emitter.emitValue("ListOps::Tree<CString>", value.r)].filter((vv) => vv !== "").join(", "); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Main::Entry>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Node<Main::Entry>") },
            $create: { value: (c, count, l, r) => {
                return Object.create(ListOps.Node["<Main::Entry>"], { c: { value: c, enumerable: true }, count: { value: count, enumerable: true }, l: { value: l, enumerable: true }, r: { value: r, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Node["<Main::Entry>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return [emitter.emitValue("ListOps::Tree<Main::Entry>", value.l), emitter.emitValue("ListOps::Tree<Main::Entry>", value.r)].filter((vv) => vv !== "").join(", "); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Main::FormatEntry>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Node<Main::FormatEntry>") },
            $create: { value: (c, count, l, r) => {
                return Object.create(ListOps.Node["<Main::FormatEntry>"], { c: { value: c, enumerable: true }, count: { value: count, enumerable: true }, l: { value: l, enumerable: true }, r: { value: r, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Node["<Main::FormatEntry>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return [emitter.emitValue("ListOps::Tree<Main::FormatEntry>", value.l), emitter.emitValue("ListOps::Tree<Main::FormatEntry>", value.r)].filter((vv) => vv !== "").join(", "); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        }),
        "<Nat>": Object.create($VRepr, {
            $tsym: { value: Symbol.for("ListOps::Node<Nat>") },
            $create: { value: (c, count, l, r) => {
                return Object.create(ListOps.Node["<Nat>"], { c: { value: c, enumerable: true }, count: { value: count, enumerable: true }, l: { value: l, enumerable: true }, r: { value: r, enumerable: true } });
            } },
            $update: { value: function(updates) {
                let vobj = {...this, ...updates};
                return Object.assign(Object.create(ListOps.Node["<Nat>"]), vobj);
            } },
            $emitAPI: { value: (emitter, value) => { return [emitter.emitValue("ListOps::Tree<Nat>", value.l), emitter.emitValue("ListOps::Tree<Nat>", value.r)].filter((vv) => vv !== "").join(", "); } },
            $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
        })
    }
};

export const NumericOps = {
    "s_natToCString": (v) => { return v.toString(); }
};

export const Option = {
    "<Main::DatabaseIndex>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<Main::DatabaseIndex>") },
        $create: { value: (value) => {
            return Object.create(Option["<Main::DatabaseIndex>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<Main::DatabaseIndex>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    }),
    "<CString>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<CString>") },
        $create: { value: (value) => {
            return Object.create(Option["<CString>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<CString>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    }),
    "<Nat>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<Nat>") },
        $create: { value: (value) => {
            return Object.create(Option["<Nat>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<Nat>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    }),
    "<ListOps::Node<Main::Entry>>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<ListOps::Node<Main::Entry>>") },
        $create: { value: (value) => {
            return Object.create(Option["<ListOps::Node<Main::Entry>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<ListOps::Node<Main::Entry>>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    }),
    "<ListOps::Node<CString>>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<ListOps::Node<CString>>") },
        $create: { value: (value) => {
            return Object.create(Option["<ListOps::Node<CString>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<ListOps::Node<CString>>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    }),
    "<ListOps::Node<Nat>>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<ListOps::Node<Nat>>") },
        $create: { value: (value) => {
            return Object.create(Option["<ListOps::Node<Nat>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<ListOps::Node<Nat>>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    }),
    "<ListOps::Node<Main::FormatEntry>>": Object.create(Object.prototype, {
        $tsym: { value: Symbol.for("Option<ListOps::Node<Main::FormatEntry>>") },
        $create: { value: (value) => {
            return Object.create(Option["<ListOps::Node<Main::FormatEntry>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { return parser.testAndConsumeIfNone() ? _$None : parser.parseValue("Some<ListOps::Node<Main::FormatEntry>>"); } },
        $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
    })
}

export const None = Object.create(Object.prototype, {
    $tsym: { value: Symbol.for("None") }
});

export const Some = {
    "<Main::DatabaseIndex>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<Main::DatabaseIndex>") },
        $create: { value: (value) => {
            return Object.create(Some["<Main::DatabaseIndex>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<Main::DatabaseIndex>"].$create(parser.parseSingleArg(true, "value", "Main::DatabaseIndex")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<Main::DatabaseIndex>{" + emitter.emitValue("Main::DatabaseIndex", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    }),
    "<CString>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<CString>") },
        $create: { value: (value) => {
            return Object.create(Some["<CString>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<CString>"].$create(parser.parseSingleArg(true, "value", "CString")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<CString>{" + emitter.emitValue("CString", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    }),
    "<Nat>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<Nat>") },
        $create: { value: (value) => {
            return Object.create(Some["<Nat>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<Nat>"].$create(parser.parseSingleArg(true, "value", "Nat")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<Nat>{" + emitter.emitValue("Nat", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    }),
    "<ListOps::Node<Main::Entry>>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<ListOps::Node<Main::Entry>>") },
        $create: { value: (value) => {
            return Object.create(Some["<ListOps::Node<Main::Entry>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<ListOps::Node<Main::Entry>>"].$create(parser.parseSingleArg(true, "value", "ListOps::Node<Main::Entry>")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<ListOps::Node<Main::Entry>>{" + emitter.emitValue("ListOps::Node<Main::Entry>", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    }),
    "<ListOps::Node<CString>>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<ListOps::Node<CString>>") },
        $create: { value: (value) => {
            return Object.create(Some["<ListOps::Node<CString>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<ListOps::Node<CString>>"].$create(parser.parseSingleArg(true, "value", "ListOps::Node<CString>")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<ListOps::Node<CString>>{" + emitter.emitValue("ListOps::Node<CString>", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    }),
    "<ListOps::Node<Nat>>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<ListOps::Node<Nat>>") },
        $create: { value: (value) => {
            return Object.create(Some["<ListOps::Node<Nat>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<ListOps::Node<Nat>>"].$create(parser.parseSingleArg(true, "value", "ListOps::Node<Nat>")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<ListOps::Node<Nat>>{" + emitter.emitValue("ListOps::Node<Nat>", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    }),
    "<ListOps::Node<Main::FormatEntry>>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("Some<ListOps::Node<Main::FormatEntry>>") },
        $create: { value: (value) => {
            return Object.create(Some["<ListOps::Node<Main::FormatEntry>>"], { value: { value: value, enumerable: true } });
        } },
        $parseAPI: { value: (parser) => { parser.checkSpecialCons("some"); return Some["<ListOps::Node<Main::FormatEntry>>"].$create(parser.parseSingleArg(true, "value", "ListOps::Node<Main::FormatEntry>")); } },
        $emitAPI: { value: (emitter, value) => { return "Some<ListOps::Node<Main::FormatEntry>>{" + emitter.emitValue("ListOps::Node<Main::FormatEntry>", value.value) + "}"; } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
    })
}

export const Bool = Object.create(Object.prototype, {
    $tsym: { value: Symbol.for("Bool") }
});

export const Nat = Object.create(Object.prototype, {
    $tsym: { value: Symbol.for("Nat") },
    _$consts: { value: {} },
    zero: { value: function() { return 0n; } },
    one: { value: function() { return 1n; } },
    toCString:  { value: function() {
        let $this$ = this;
        return NumericOps.s_natToCString($this$);
    } }
});

export const CString = Object.create(Object.prototype, {
    $tsym: { value: Symbol.for("CString") },
    concat:  { value: (strs) => {
        if(strs.empty()) {
            return "";
        }
        else {
            return strs.$scall("reduce", "<CString>", "", (acc, s) => { return CStringOps.s_concat2(acc, s); });
        }
    } },
    joinAll:  { value: (sep, strs) => {
        if(strs.empty()) {
            return "";
        }
        else {
            return strs.$scall("reduce", "<CString>", "", (acc, s) => {  if(CString.empty.call(acc)) {  return s;  }  else {  return CStringOps.s_concat2(CStringOps.s_concat2(acc, sep), s);  }  });
        }
    } },
    empty:  { value: function() {
        let $this$ = this;
        return CStringOps.s_empty($this$);
    } }
});

export const List = {
    "<Main::Entry>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("List<Main::Entry>") },
        $create: { value: (value) => {
            return Object.create(List["<Main::Entry>"], { value: { value: value, enumerable: true } });
        } },
        empty:  { value: function() {
            let $this$ = this;
            return ListOps.s_list_empty["<Main::Entry>"]($this$);
        } },
        size:  { value: function() {
            let $this$ = this;
            return ListOps.s_list_size["<Main::Entry>"]($this$);
        } },
        lastIndex:  { value: function() {
            let $this$ = this;
            _$precond(!$this$.empty(), "!this.empty() @ list.bsq:17");

            return _$sub.Nat(ListOps.s_list_size["<Main::Entry>"]($this$), 1n);
        } },
        get:  { value: function(i) {
            let $this$ = this;
            _$precond(i < $this$.size(), "i < this.size() @ list.bsq:45");

            return ListOps.s_list_get["<Main::Entry>"]($this$, i);
        } },
        set:  { value: function(i, v) {
            let $this$ = this;
            _$precond(i < $this$.size(), "i < this.size() @ list.bsq:63");

            return ListOps.s_list_set["<Main::Entry>"]($this$, i, v);
        } },
        pushBack:  { value: function(v) {
            let $this$ = this;
            return ListOps.s_list_push_back["<Main::Entry>"]($this$, v);
        } },
        delete:  { value: function(i) {
            let $this$ = this;
            _$precond(i < $this$.size(), "i < this.size() @ list.bsq:107");

            return ListOps.s_list_delete["<Main::Entry>"]($this$, i);
        } },
        allOf:  { value: function(p) {
            let $this$ = this;
            if(ListOps.s_list_empty["<Main::Entry>"]($this$)) {
                return true;
            }
            else {
                return ListOps.s_list_allof["<Main::Entry>"]($this$, p);
            }
        } },
        mapIdx: { value: {
            "<Nat>": function(f) {
                let $this$ = this;
                if(ListOps.s_list_empty["<Main::Entry>"]($this$)) {
                    return ListOps.s_list_create_empty["<Nat>"]();
                }
                else {
                    return ListOps.s_list_mapidx["<Main::Entry, Nat>"]($this$, f);
                }
            }
        } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } },
        $parseAPI: { value: (parser) => { parser.checkConsType("List<Main::Entry>"); const ee = parser.parseCollectionConsArgs("Main::Entry"); return ee.reduce((acc, v) => { return ListOps.s_list_push_back["<Main::Entry>"](acc, v); }, ListOps.s_list_create_empty["<Main::Entry>"]()); } },
        $emitAPI: { value: (emitter, value) => { return "List<Main::Entry>" + "{" + emitter.emitCollectionEntries("Main::Entry", value.value) + "}"; } }
    }),
    "<CString>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("List<CString>") },
        $create: { value: (value) => {
            return Object.create(List["<CString>"], { value: { value: value, enumerable: true } });
        } },
        empty:  { value: function() {
            let $this$ = this;
            return ListOps.s_list_empty["<CString>"]($this$);
        } },
        size:  { value: function() {
            let $this$ = this;
            return ListOps.s_list_size["<CString>"]($this$);
        } },
        get:  { value: function(i) {
            let $this$ = this;
            _$precond(i < $this$.size(), "i < this.size() @ list.bsq:45");

            return ListOps.s_list_get["<CString>"]($this$, i);
        } },
        firstK:  { value: function(n) {
            let $this$ = this;
            _$precond(n <= $this$.size(), "n <= this.size() @ list.bsq:158");

            if(ListOps.s_list_empty["<CString>"]($this$)) {
                return ListOps.s_list_create_empty["<CString>"]();
            }
            else {
                return ListOps.s_list_firstk["<CString>"]($this$, n);
            }
        } },
        shiftK:  { value: function(n) {
            let $this$ = this;
            _$precond(n <= $this$.size(), "n <= this.size() @ list.bsq:180");

            if(ListOps.s_list_empty["<CString>"]($this$)) {
                return ListOps.s_list_create_empty["<CString>"]();
            }
            else {
                return ListOps.s_list_shiftk["<CString>"]($this$, n);
            }
        } },
        mapIdx: { value: {
            "<CString>": function(f) {
                let $this$ = this;
                if(ListOps.s_list_empty["<CString>"]($this$)) {
                    return ListOps.s_list_create_empty["<CString>"]();
                }
                else {
                    return ListOps.s_list_mapidx["<CString, CString>"]($this$, f);
                }
            }
        } },
        reduce: { value: {
            "<CString>": function(init, f) {
                let $this$ = this;
                if(ListOps.s_list_empty["<CString>"]($this$)) {
                    return init;
                }
                else {
                    return ListOps.s_list_reduce["<CString, CString>"]($this$, init, f);
                }
            }
        } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } },
        $parseAPI: { value: (parser) => { parser.checkConsType("List<CString>"); const ee = parser.parseCollectionConsArgs("CString"); return ee.reduce((acc, v) => { return ListOps.s_list_push_back["<CString>"](acc, v); }, ListOps.s_list_create_empty["<CString>"]()); } },
        $emitAPI: { value: (emitter, value) => { return "List<CString>" + "{" + emitter.emitCollectionEntries("CString", value.value) + "}"; } }
    }),
    "<Nat>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("List<Nat>") },
        $create: { value: (value) => {
            return Object.create(List["<Nat>"], { value: { value: value, enumerable: true } });
        } },
        size:  { value: function() {
            let $this$ = this;
            return ListOps.s_list_size["<Nat>"]($this$);
        } },
        get:  { value: function(i) {
            let $this$ = this;
            _$precond(i < $this$.size(), "i < this.size() @ list.bsq:45");

            return ListOps.s_list_get["<Nat>"]($this$, i);
        } },
        allOf:  { value: function(p) {
            let $this$ = this;
            if(ListOps.s_list_empty["<Nat>"]($this$)) {
                return true;
            }
            else {
                return ListOps.s_list_allof["<Nat>"]($this$, p);
            }
        } },
        sum:  { value: function() {
            let $this$ = this;
            if(ListOps.s_list_empty["<Nat>"]($this$)) {
                return Nat.zero();
            }
            else {
                return ListOps.s_list_sum["<Nat>"]($this$, Nat.zero());
            }
        } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } },
        $parseAPI: { value: (parser) => { parser.checkConsType("List<Nat>"); const ee = parser.parseCollectionConsArgs("Nat"); return ee.reduce((acc, v) => { return ListOps.s_list_push_back["<Nat>"](acc, v); }, ListOps.s_list_create_empty["<Nat>"]()); } },
        $emitAPI: { value: (emitter, value) => { return "List<Nat>" + "{" + emitter.emitCollectionEntries("Nat", value.value) + "}"; } }
    }),
    "<Main::FormatEntry>": Object.create($VRepr, {
        $tsym: { value: Symbol.for("List<Main::FormatEntry>") },
        $create: { value: (value) => {
            return Object.create(List["<Main::FormatEntry>"], { value: { value: value, enumerable: true } });
        } },
        map: { value: {
            "<Nat>": function(f) {
                let $this$ = this;
                if(ListOps.s_list_empty["<Main::FormatEntry>"]($this$)) {
                    return ListOps.s_list_create_empty["<Nat>"]();
                }
                else {
                    return ListOps.s_list_map["<Main::FormatEntry, Nat>"]($this$, f);
                }
            }
        } },
        reduce: { value: {
            "<(|CString, List<CString>|)>": function(init, f) {
                let $this$ = this;
                if(ListOps.s_list_empty["<Main::FormatEntry>"]($this$)) {
                    return init;
                }
                else {
                    return ListOps.s_list_reduce["<Main::FormatEntry, (|CString, List<CString>|)>"]($this$, init, f);
                }
            }
        } },
        $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } },
        $parseAPI: { value: (parser) => { parser.checkConsType("List<Main::FormatEntry>"); const ee = parser.parseCollectionConsArgs("Main::FormatEntry"); return ee.reduce((acc, v) => { return ListOps.s_list_push_back["<Main::FormatEntry>"](acc, v); }, ListOps.s_list_create_empty["<Main::FormatEntry>"]()); } },
        $emitAPI: { value: (emitter, value) => { return "List<Main::FormatEntry>" + "{" + emitter.emitCollectionEntries("Main::FormatEntry", value.value) + "}"; } }
    })
}

//_$supertypes for none is a special case in code (not emitted)
_$supertypes[Symbol.for("Some<Main::DatabaseIndex>")] = [Symbol.for("Option<Main::DatabaseIndex>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Some<CString>")] = [Symbol.for("Option<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Some<Nat>")] = [Symbol.for("Option<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Some<ListOps::Node<Main::Entry>>")] = [Symbol.for("Option<ListOps::Node<Main::Entry>>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Some<ListOps::Node<CString>>")] = [Symbol.for("Option<ListOps::Node<CString>>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Some<ListOps::Node<Nat>>")] = [Symbol.for("Option<ListOps::Node<Nat>>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Some<ListOps::Node<Main::FormatEntry>>")] = [Symbol.for("Option<ListOps::Node<Main::FormatEntry>>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Bool")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Nat")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("CString")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("List<Main::Entry>")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("List<CString>")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("List<Nat>")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("List<Main::FormatEntry>")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Color")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});

_$parsemap["Option<Main::DatabaseIndex>"] = Option["<Main::DatabaseIndex>"].$parseAPI;
_$parsemap["Option<CString>"] = Option["<CString>"].$parseAPI;
_$parsemap["Option<Nat>"] = Option["<Nat>"].$parseAPI;
_$parsemap["Option<ListOps::Node<Main::Entry>>"] = Option["<ListOps::Node<Main::Entry>>"].$parseAPI;
_$parsemap["Option<ListOps::Node<CString>>"] = Option["<ListOps::Node<CString>>"].$parseAPI;
_$parsemap["Option<ListOps::Node<Nat>>"] = Option["<ListOps::Node<Nat>>"].$parseAPI;
_$parsemap["Option<ListOps::Node<Main::FormatEntry>>"] = Option["<ListOps::Node<Main::FormatEntry>>"].$parseAPI;
_$parsemap["Some<Main::DatabaseIndex>"] = Some["<Main::DatabaseIndex>"].$parseAPI;
_$parsemap["Some<CString>"] = Some["<CString>"].$parseAPI;
_$parsemap["Some<Nat>"] = Some["<Nat>"].$parseAPI;
_$parsemap["Some<ListOps::Node<Main::Entry>>"] = Some["<ListOps::Node<Main::Entry>>"].$parseAPI;
_$parsemap["Some<ListOps::Node<CString>>"] = Some["<ListOps::Node<CString>>"].$parseAPI;
_$parsemap["Some<ListOps::Node<Nat>>"] = Some["<ListOps::Node<Nat>>"].$parseAPI;
_$parsemap["Some<ListOps::Node<Main::FormatEntry>>"] = Some["<ListOps::Node<Main::FormatEntry>>"].$parseAPI;
_$parsemap["List<Main::Entry>"] = List["<Main::Entry>"].$parseAPI;
_$parsemap["List<CString>"] = List["<CString>"].$parseAPI;
_$parsemap["List<Nat>"] = List["<Nat>"].$parseAPI;
_$parsemap["List<Main::FormatEntry>"] = List["<Main::FormatEntry>"].$parseAPI;
_$parsemap["(|CString, List<CString>|)"] = (parser) => parser.parseEListArgs("CString", "List<CString>");
_$supertypes[Symbol.for("ListOps::Color")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});

_$emitmap["Option<Main::DatabaseIndex>"] = Option["<Main::DatabaseIndex>"].$emitAPI;
_$emitmap["Option<CString>"] = Option["<CString>"].$emitAPI;
_$emitmap["Option<Nat>"] = Option["<Nat>"].$emitAPI;
_$emitmap["Option<ListOps::Node<Main::Entry>>"] = Option["<ListOps::Node<Main::Entry>>"].$emitAPI;
_$emitmap["Option<ListOps::Node<CString>>"] = Option["<ListOps::Node<CString>>"].$emitAPI;
_$emitmap["Option<ListOps::Node<Nat>>"] = Option["<ListOps::Node<Nat>>"].$emitAPI;
_$emitmap["Option<ListOps::Node<Main::FormatEntry>>"] = Option["<ListOps::Node<Main::FormatEntry>>"].$emitAPI;
_$emitmap["Some<Main::DatabaseIndex>"] = Some["<Main::DatabaseIndex>"].$emitAPI;
_$emitmap["Some<CString>"] = Some["<CString>"].$emitAPI;
_$emitmap["Some<Nat>"] = Some["<Nat>"].$emitAPI;
_$emitmap["Some<ListOps::Node<Main::Entry>>"] = Some["<ListOps::Node<Main::Entry>>"].$emitAPI;
_$emitmap["Some<ListOps::Node<CString>>"] = Some["<ListOps::Node<CString>>"].$emitAPI;
_$emitmap["Some<ListOps::Node<Nat>>"] = Some["<ListOps::Node<Nat>>"].$emitAPI;
_$emitmap["Some<ListOps::Node<Main::FormatEntry>>"] = Some["<ListOps::Node<Main::FormatEntry>>"].$emitAPI;
_$emitmap["List<Main::Entry>"] = List["<Main::Entry>"].$emitAPI;
_$emitmap["List<CString>"] = List["<CString>"].$emitAPI;
_$emitmap["List<Nat>"] = List["<Nat>"].$emitAPI;
_$emitmap["List<Main::FormatEntry>"] = List["<Main::FormatEntry>"].$emitAPI;
_$emitmap["(|CString, List<CString>|)"] = (emitter, value) => "(|" + emitter.emitValue("CString", value[0]) + emitter.emitValue("List<CString>", value[1]) + "|)";
_$supertypes[Symbol.for("ListOps::Color")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::BBLeaf<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Leaf<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<CString>")] = [Symbol.for("ListOps::Tree<CString>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Main::Entry>")] = [Symbol.for("ListOps::Tree<Main::Entry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Main::FormatEntry>")] = [Symbol.for("ListOps::Tree<Main::FormatEntry>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("ListOps::Node<Nat>")] = [Symbol.for("ListOps::Tree<Nat>")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
