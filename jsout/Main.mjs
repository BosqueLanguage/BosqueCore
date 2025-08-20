"use strict";
let _$consts = {};

import { $VRepr, _$softfails, _$supertypes, _$fisSubtype, _$fisNotSubtype, _$fasSubtype, _$fasNotSubtype, _$None, _$not, _$negate, _$add, _$sub, _$mult, _$div, _$bval, _$fkeq, _$fkeqopt, _$fkneq, _$fkneqopt, _$fkless, _$fnumeq, _$fnumless, _$fnumlesseq, _$exhaustive, _$abort, _$assert, _$formatchk, _$invariant, _$validate, _$precond, _$softprecond, _$postcond, _$softpostcond, _$memoconstval, _$accepts } from "./runtime.mjs";
import { _$setnone_lit, _$parsemap, _$emitmap, _$parseBSQON, _$emitBSQON } from "./bsqon.mjs";

import * as $Core from "./Core.mjs";

let _$rv = {};

export function getSampleDB() {
    const entries = $Core.ListOps.s_list_create_3["<Main::Entry>"](Entry.$create($Core.ListOps.s_list_create_3["<CString>"]("Bosque", "Yes", "Hybrid")), Entry.$create($Core.ListOps.s_list_create_3["<CString>"]("C++", "Yes", "Compiled")), Entry.$create($Core.ListOps.s_list_create_3["<CString>"]("JavaScript", "No", "JIT")));
    const format = Format.$create($Core.ListOps.s_list_create_2["<Main::FormatEntry>"](FormatEntry.$create("PL", $Core.ListOps.s_list_create_1["<CString>"]("Name")), FormatEntry.$create("Features", $Core.ListOps.s_list_create_2["<CString>"]("Static Types", "Runtime"))), 3n);
    return Database.$create(_$None, entries, format, _$None, _$None);
}

export function testOpOnSample(op) {
    const db = getSampleDB();
    const [res,  ] = db.processDatabaseOperation(op);
    return res;
}

export const Entry = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::Entry") },
    $create: { value: (items) => {
        return Object.create(Entry, { items: { value: items, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(Entry), vobj);
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::Entry"); return Entry.$create(parser.parseSingleArg(false, "items", "List<CString>")); } },
    $emitAPI: { value: (emitter, value) => { return "Main::Entry{" + emitter.emitValue("List<CString>", value.items) + "}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const FormatEntry = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::FormatEntry") },
    $create: { value: (header, entries) => {
        return Object.create(FormatEntry, { header: { value: header, enumerable: true }, entries: { value: entries, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(FormatEntry), vobj);
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::FormatEntry"); const vals = parser.parseArgListGeneral([["header", "CString"],["entries", "List<CString>"]]); return FormatEntry.$create(...vals); } },
    $emitAPI: { value: (emitter, value) => { return "Main::FormatEntry{" + emitter.emitValue("CString", value.header) + ", " + emitter.emitValue("List<CString>", value.entries) + "}"; } },
    format:  { value: function(values) {
        let $this$ = this;
        const parts = $this$.entries.$scall("mapIdx", "<CString>", (vv, ii) => { return $Core.CString.concat($Core.ListOps.s_list_create_3["<CString>"](vv, ": ", values.get(ii))); });
        const iidt = $Core.CString.joinAll(decodeURI("%0A%20%20"), parts);
        const hdr = $Core.CString.concat($Core.ListOps.s_list_create_2["<CString>"]($this$.header, decodeURI("%0A")));
        return $Core.CString.concat($Core.ListOps.s_list_create_3["<CString>"](hdr, "  ", iidt));
    } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const Format = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::Format") },
    $checkinv_29_646: { value: ($entries, $vcount) => $vcount === $entries.$scall("map", "<Nat>", (ee) => { return ee.entries.size(); }).sum() },
    $create: { value: (entries, vcount) => {
        _$invariant(Format.$checkinv_29_646(entries, vcount), "failed invariant @ db.bsq:29");
        return Object.create(Format, { entries: { value: entries, enumerable: true }, vcount: { value: vcount, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        _$invariant(Format.$checkinv_29_646(vobj.entries, vobj.vcount), "failed invariant @ db.bsq:29");
        return Object.assign(Object.create(Format), vobj);
    } },
    $createAPI: { value: (entries, vcount) => {
        _$invariant(Format.$checkinv_29_646(entries, vcount), "failed invariant @ db.bsq:29");
        return Object.create(Format, { entries: { value: entries, enumerable: true }, vcount: { value: vcount, enumerable: true } });
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::Format"); const vals = parser.parseArgListGeneral([["entries", "List<Main::FormatEntry>"],["vcount", "Nat"]]); return Format.$createAPI(...vals); } },
    $emitAPI: { value: (emitter, value) => { return "Main::Format{" + emitter.emitValue("List<Main::FormatEntry>", value.entries) + ", " + emitter.emitValue("Nat", value.vcount) + "}"; } },
    formatEntry:  { value: function(entry) {
        let $this$ = this;
        const [res,  ] = $this$.entries.$scall("reduce", "<(|CString, List<CString>|)>", ["", entry.items], (acc, fmt) => {  const fargs = acc[1].firstK(fmt.entries.size());  const rrest = acc[1].shiftK(fmt.entries.size());  const formatted = $Core.CString.concat($Core.ListOps.s_list_create_3["<CString>"](acc[0], decodeURI("%0A"), fmt.format(fargs)));  return [formatted, rrest];  });
        return res;
    } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const DatabaseOperation = Object.create(Object.prototype, {
    $tsym: { value: Symbol.for("Main::DatabaseOperation") },
    $parseAPI: { value: (parser) => { return parser.parseValue(parser.peekScopedType()); } },
    $emitAPI: { value: (emitter, value) => { return value.$emitAPI(emitter, value); } }
});

export const NumRecordsOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::NumRecordsOp") },
    $create: { value: () => {
        return Object.create(NumRecordsOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(NumRecordsOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return NumRecordsOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::NumRecordsOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const EndOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::EndOp") },
    $create: { value: () => {
        return Object.create(EndOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(EndOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return EndOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::EndOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const ListOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::ListOp") },
    $create: { value: () => {
        return Object.create(ListOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(ListOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return ListOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::ListOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const GotoRecordOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::GotoRecordOp") },
    $create: { value: (ridx) => {
        return Object.create(GotoRecordOp, { ridx: { value: ridx, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(GotoRecordOp), vobj);
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::GotoRecordOp"); return GotoRecordOp.$create(parser.parseSingleArg(false, "ridx", "Nat")); } },
    $emitAPI: { value: (emitter, value) => { return "Main::GotoRecordOp{" + emitter.emitValue("Nat", value.ridx) + "}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const NextOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::NextOp") },
    $create: { value: () => {
        return Object.create(NextOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(NextOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return NextOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::NextOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const PreviousOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::PreviousOp") },
    $create: { value: () => {
        return Object.create(PreviousOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(PreviousOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return PreviousOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::PreviousOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const StatusOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::StatusOp") },
    $create: { value: () => {
        return Object.create(StatusOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(StatusOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return StatusOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::StatusOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const AddOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::AddOp") },
    $create: { value: (entry) => {
        return Object.create(AddOp, { entry: { value: entry, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(AddOp), vobj);
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::AddOp"); return AddOp.$create(parser.parseSingleArg(false, "entry", "Main::Entry")); } },
    $emitAPI: { value: (emitter, value) => { return "Main::AddOp{" + emitter.emitValue("Main::Entry", value.entry) + "}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const ModifyOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::ModifyOp") },
    $create: { value: (entry) => {
        return Object.create(ModifyOp, { entry: { value: entry, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(ModifyOp), vobj);
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::ModifyOp"); return ModifyOp.$create(parser.parseSingleArg(false, "entry", "Main::Entry")); } },
    $emitAPI: { value: (emitter, value) => { return "Main::ModifyOp{" + emitter.emitValue("Main::Entry", value.entry) + "}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const RemoveOp = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::RemoveOp") },
    $create: { value: () => {
        return Object.create(RemoveOp, {  });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        return Object.assign(Object.create(RemoveOp), vobj);
    } },
    $parseAPI: { value: (parser) => { return RemoveOp.$create(); } },
    $emitAPI: { value: (emitter, value) => { return "Main::RemoveOp{}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const DatabaseIndex = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::DatabaseIndex") },
    $checkinv_62_1466: { value: ($imap, $curr) => $curr < $imap.size() },
    $create: { value: (imap, curr) => {
        _$invariant(DatabaseIndex.$checkinv_62_1466(imap, curr), "failed invariant @ db.bsq:62");
        return Object.create(DatabaseIndex, { imap: { value: imap, enumerable: true }, curr: { value: curr, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        _$invariant(DatabaseIndex.$checkinv_62_1466(vobj.imap, vobj.curr), "failed invariant @ db.bsq:62");
        return Object.assign(Object.create(DatabaseIndex), vobj);
    } },
    $createAPI: { value: (imap, curr) => {
        _$invariant(DatabaseIndex.$checkinv_62_1466(imap, curr), "failed invariant @ db.bsq:62");
        return Object.create(DatabaseIndex, { imap: { value: imap, enumerable: true }, curr: { value: curr, enumerable: true } });
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::DatabaseIndex"); const vals = parser.parseArgListGeneral([["imap", "List<Nat>"],["curr", "Nat"]]); return DatabaseIndex.$createAPI(...vals); } },
    $emitAPI: { value: (emitter, value) => { return "Main::DatabaseIndex{" + emitter.emitValue("List<Nat>", value.imap) + ", " + emitter.emitValue("Nat", value.curr) + "}"; } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

export const Database = Object.create($VRepr, {
    $tsym: { value: Symbol.for("Main::Database") },
    $default$dbname: { value: ($dbname, $entries, $format, $index, $fnum) => _$None },
    $checkinv_96_2331: { value: ($dbname, $entries, $format, $index, $fnum) => Database.indexQuickCheck($index, $entries.size()) },
    $checkinv_96_2331: { value: ($dbname, $entries, $format, $index, $fnum) => $entries.allOf((e) => { return e.items.size() === $format.vcount; }) },
    $checkinv_96_2331: { value: ($dbname, $entries, $format, $index, $fnum) => Database.indexFullCheck($index, $entries.size()) },
    $create: { value: (dbname, entries, format, index, fnum) => {
        let $dbname = dbname, $entries = entries, $format = format, $index = index, $fnum = fnum;
        if(dbname === undefined) { $dbname = dbname = Database.$default$dbname($dbname, $entries, $format, $index, $fnum); }
        _$invariant(Database.$checkinv_96_2331(dbname, entries, format, index, fnum), "failed invariant @ db.bsq:96");
        return Object.create(Database, { dbname: { value: dbname, enumerable: true }, entries: { value: entries, enumerable: true }, format: { value: format, enumerable: true }, index: { value: index, enumerable: true }, fnum: { value: fnum, enumerable: true } });
    } },
    $update: { value: function(updates) {
        let vobj = {...this, ...updates};
        _$invariant(Database.$checkinv_96_2331(vobj.dbname, vobj.entries, vobj.format, vobj.index, vobj.fnum), "failed invariant @ db.bsq:96");
        return Object.assign(Object.create(Database), vobj);
    } },
    $createAPI: { value: (dbname, entries, format, index, fnum) => {
        let $dbname = dbname, $entries = entries, $format = format, $index = index, $fnum = fnum;
        if(dbname === undefined) { $dbname = dbname = Database.$default$dbname($dbname, $entries, $format, $index, $fnum); }
        _$invariant(Database.$checkinv_96_2331(dbname, entries, format, index, fnum), "failed invariant @ db.bsq:96");
        _$validate(Database.$checkinv_96_2331(dbname, entries, format, index, fnum), "failed validation @ db.bsq:96");
        _$validate(Database.$checkinv_96_2331(dbname, entries, format, index, fnum), "failed validation @ db.bsq:96");
        return Object.create(Database, { dbname: { value: dbname, enumerable: true }, entries: { value: entries, enumerable: true }, format: { value: format, enumerable: true }, index: { value: index, enumerable: true }, fnum: { value: fnum, enumerable: true } });
    } },
    $parseAPI: { value: (parser) => { parser.checkConsType("Main::Database"); const vals = parser.parseArgListGeneral([["dbname", "Option<CString>"],["entries", "List<Main::Entry>"],["format", "Main::Format"],["index", "Option<Main::DatabaseIndex>"],["fnum", "Option<Nat>"]]); return Database.$createAPI(...vals); } },
    $emitAPI: { value: (emitter, value) => { return "Main::Database{" + emitter.emitValue("Option<CString>", value.dbname) + ", " + emitter.emitValue("List<Main::Entry>", value.entries) + ", " + emitter.emitValue("Main::Format", value.format) + ", " + emitter.emitValue("Option<Main::DatabaseIndex>", value.index) + ", " + emitter.emitValue("Option<Nat>", value.fnum) + "}"; } },
    indexQuickCheck:  { value: (idx, entrycount) => {
        if(idx._$isNone()) {
            let $idx = idx._$asNone("expected None but got Some @ db.bsq:74"); {
                return true;
            }
        }
        else {
            let $idx = idx._$asNotNone("expected Some but got None @ db.bsq:74"); {
                return ($idx.imap.size() === entrycount) && ($idx.curr < entrycount);
            }
        }
    } },
    indexFullCheck:  { value: (idx, entrycount) => {
        if(idx._$isNone()) {
            let $idx = idx._$asNone("expected None but got Some @ db.bsq:83"); {
                return true;
            }
        }
        else {
            let $idx = idx._$asNotNone("expected Some but got None @ db.bsq:83"); {
                if(($idx.imap.size() !== entrycount) || ($idx.curr >= entrycount)) {
                    return false;
                }
                else {
                    return $idx.imap.allOf((i) => { return i < entrycount; });
                }
            }
        }
    } },
    setIndex:  { value: function(atidx) {
        let $this$ = this;
        const nidx = $this$.entries.$scall("mapIdx", "<Nat>", (e, i) => { return i; });
        const nindex = DatabaseIndex.$create(nidx, atidx);
        return [Database.$create($this$.dbname, $this$.entries, $this$.format, $Core.Some["<Main::DatabaseIndex>"].$create(nindex), $this$.fnum), nindex];
    } },
    ensureIndex:  { value: function(atidx) {
        let $this$ = this;
        if($this$.index._$isNone()) {
            let $tidx = $this$.index._$asNone("expected None but got Some @ db.bsq:109"); {
                if(atidx._$isNone()) {
                    let $atidx = atidx._$asNone("expected None but got Some @ db.bsq:110"); {
                        return $this$.setIndex(0n);
                    }
                }
                else {
                    let $atidx = atidx._$asNotNone("expected Some but got None @ db.bsq:110"); {
                        return $this$.setIndex($atidx);
                    }
                }
            }
        }
        else {
            let $tidx = $this$.index._$asNotNone("expected Some but got None @ db.bsq:109"); {
                if(atidx._$isNone()) {
                    let $atidx = atidx._$asNone("expected None but got Some @ db.bsq:119"); {
                        return [$this$, $tidx];
                    }
                }
                else {
                    let $atidx = atidx._$asNotNone("expected Some but got None @ db.bsq:119"); {
                        const dbidx = DatabaseIndex.$create($tidx.imap, $atidx);
                        return [Database.$create($this$.dbname, $this$.entries, $this$.format, $Core.Some["<Main::DatabaseIndex>"].$create(dbidx), $this$.fnum), dbidx];
                    }
                }
            }
        }
    } },
    setCurr:  { value: function(atIdx) {
        let $this$ = this;
        _$precond($this$.index._$isSome(), "this.index?some @ db.bsq:129");

        return Database.$create($this$.dbname, $this$.entries, $this$.format, $Core.Some["<Main::DatabaseIndex>"].$create(DatabaseIndex.$create($this$.index._$asSome("expected Some but got None @ db.bsq:132").imap, atIdx)), $this$.fnum);
    } },
    printRec:  { value: function() {
        let $this$ = this;
        const [tdb, tidx] = $this$.ensureIndex(_$None);
        const entry = tdb.entries.get(tidx.imap.get(tidx.curr));
        return [tdb.format.formatEntry(entry), tdb];
    } },
    processNumRecords:  { value: function(op) {
        let $this$ = this;
        return $Core.CString.concat($Core.ListOps.s_list_create_2["<CString>"]("Records Count: ", $Core.Nat.toCString.call($this$.entries.size())));
    } },
    processEnd:  { value: function(op) {
        let $this$ = this;
        if($this$.entries.empty()) {
            return ["Empty DB", $this$];
        }
        else {
            const [tdb,  ] = $this$.ensureIndex($Core.Some["<Nat>"].$create($this$.entries.lastIndex()));
            return tdb.printRec();
        }
    } },
    processList:  { value: function(op) {
        let $this$ = this;
        if($this$.entries.empty()) {
            return ["Empty DB", $this$];
        }
        else {
            const [tdb,  ] = $this$.ensureIndex($Core.Some["<Nat>"].$create(0n));
            return tdb.printRec();
        }
    } },
    processGotoRecord:  { value: function(op) {
        let $this$ = this;
        if((0n === op.ridx) || ($this$.entries.size() < op.ridx)) {
            return ["Invalid Record Index", $this$];
        }
        else {
            const [tdb, tidx] = $this$.ensureIndex($Core.Some["<Nat>"].$create(_$sub.Nat(op.ridx, 1n)));
            return tdb.printRec();
        }
    } },
    processNext:  { value: function(op) {
        let $this$ = this;
        const [tdb, tidx] = $this$.ensureIndex(_$None);
        if(tidx.curr >= $this$.entries.lastIndex()) {
            return ["", tdb];
        }
        else {
            const ntdb = tdb.setCurr(_$add.Nat(tidx.curr, 1n));
            return ntdb.printRec();
        }
    } },
    processPrevious:  { value: function(op) {
        let $this$ = this;
        const [tdb, tidx] = $this$.ensureIndex(_$None);
        if(tidx.curr === 0n) {
            return ["", tdb];
        }
        else {
            const ntdb = tdb.setCurr(_$sub.Nat(tidx.curr, 1n));
            return ntdb.printRec();
        }
    } },
    processStatus:  { value: function(op) {
        let $this$ = this;
        const [tdb, tidx] = $this$.ensureIndex(_$None);
        return $Core.CString.concat($Core.ListOps.s_list_create_3["<CString>"]($Core.Nat.toCString.call(tidx.curr), " of ", $Core.Nat.toCString.call($this$.entries.size())));
    } },
    processAdd:  { value: function(op) {
        let $this$ = this;
        _$precond(op.entry.items.size() === $this$.format.vcount, "op.entry.items.size() == this.format.vcount @ db.bsq:206");

        return Database.$create($this$.dbname, $this$.entries.pushBack(op.entry), $this$.format, _$None, _$None);
    } },
    processModify:  { value: function(op) {
        let $this$ = this;
        if($this$.index._$isNone()) {
            let $idx = $this$.index._$asNone("expected None but got Some @ db.bsq:213"); {
                return $this$;
            }
        }
        else {
            let $idx = $this$.index._$asNotNone("expected Some but got None @ db.bsq:213"); {
                return Database.$create($this$.dbname, $this$.entries.set($idx.imap.get($idx.curr), op.entry), $this$.format, $this$.index, _$None);
            }
        }
    } },
    processRemove:  { value: function(op) {
        let $this$ = this;
        if($this$.entries.empty()) {
            return $this$;
        }
        else {
            const [tdb, tidx] = $this$.ensureIndex(_$None);
            return Database.$create($this$.dbname, $this$.entries.delete(tidx.imap.get(tidx.curr)), $this$.format, _$None, _$None);
        }
    } },
    processDatabaseOperation:  { value: function(op) {
        let $this$ = this;
        if (op._$is(NumRecordsOp.$tsym)) { let $op = op; {
                return [$this$.processNumRecords($op), $this$];
            }
        }
        else if (op._$is(EndOp.$tsym)) { let $op = op; {
                return $this$.processEnd($op);
            }
        }
        else if (op._$is(ListOp.$tsym)) { let $op = op; {
                return $this$.processList($op);
            }
        }
        else if (op._$is(GotoRecordOp.$tsym)) { let $op = op; {
                return $this$.processGotoRecord($op);
            }
        }
        else if (op._$is(NextOp.$tsym)) { let $op = op; {
                return $this$.processNext($op);
            }
        }
        else if (op._$is(PreviousOp.$tsym)) { let $op = op; {
                return $this$.processPrevious($op);
            }
        }
        else if (op._$is(StatusOp.$tsym)) { let $op = op; {
                return [$this$.processStatus($op), $this$];
            }
        }
        else if (op._$is(AddOp.$tsym)) { let $op = op; {
                return ["", $this$.processAdd($op)];
            }
        }
        else if (op._$is(ModifyOp.$tsym)) { let $op = op; {
                return ["", $this$.processModify($op)];
            }
        }
        else { let $op = op; {
                return ["", $this$.processRemove($op)];
            }
        }
    } },
    $scall: { value: function(name, tt, ...args) { return this[name][tt].call(this, ...args); } }
});

_$supertypes[Symbol.for("Main::Entry")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::FormatEntry")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::Format")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::NumRecordsOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::EndOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::ListOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::GotoRecordOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::NextOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::PreviousOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::StatusOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::AddOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::ModifyOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::RemoveOp")] = [Symbol.for("Main::DatabaseOperation")].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::DatabaseIndex")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});
_$supertypes[Symbol.for("Main::Database")] = [].reduce((acc, ks) => { acc[ks] = true; return acc; }, {});

_$parsemap["Main::Entry"] = Entry.$parseAPI;
_$parsemap["Main::FormatEntry"] = FormatEntry.$parseAPI;
_$parsemap["Main::Format"] = Format.$parseAPI;
_$parsemap["Main::DatabaseOperation"] = DatabaseOperation.$parseAPI;
_$parsemap["Main::NumRecordsOp"] = NumRecordsOp.$parseAPI;
_$parsemap["Main::EndOp"] = EndOp.$parseAPI;
_$parsemap["Main::ListOp"] = ListOp.$parseAPI;
_$parsemap["Main::GotoRecordOp"] = GotoRecordOp.$parseAPI;
_$parsemap["Main::NextOp"] = NextOp.$parseAPI;
_$parsemap["Main::PreviousOp"] = PreviousOp.$parseAPI;
_$parsemap["Main::StatusOp"] = StatusOp.$parseAPI;
_$parsemap["Main::AddOp"] = AddOp.$parseAPI;
_$parsemap["Main::ModifyOp"] = ModifyOp.$parseAPI;
_$parsemap["Main::RemoveOp"] = RemoveOp.$parseAPI;
_$parsemap["Main::DatabaseIndex"] = DatabaseIndex.$parseAPI;
_$parsemap["Main::Database"] = Database.$parseAPI;
_$parsemap["(|CString, Main::Database|)"] = (parser) => parser.parseEListArgs("CString", "Main::Database");
_$parsemap["(|Main::Database, Main::DatabaseIndex|)"] = (parser) => parser.parseEListArgs("Main::Database", "Main::DatabaseIndex");
_$parsemap["(|CString, List<CString>|)"] = (parser) => parser.parseEListArgs("CString", "List<CString>");

_$emitmap["Main::Entry"] = Entry.$emitAPI;
_$emitmap["Main::FormatEntry"] = FormatEntry.$emitAPI;
_$emitmap["Main::Format"] = Format.$emitAPI;
_$emitmap["Main::DatabaseOperation"] = DatabaseOperation.$emitAPI;
_$emitmap["Main::NumRecordsOp"] = NumRecordsOp.$emitAPI;
_$emitmap["Main::EndOp"] = EndOp.$emitAPI;
_$emitmap["Main::ListOp"] = ListOp.$emitAPI;
_$emitmap["Main::GotoRecordOp"] = GotoRecordOp.$emitAPI;
_$emitmap["Main::NextOp"] = NextOp.$emitAPI;
_$emitmap["Main::PreviousOp"] = PreviousOp.$emitAPI;
_$emitmap["Main::StatusOp"] = StatusOp.$emitAPI;
_$emitmap["Main::AddOp"] = AddOp.$emitAPI;
_$emitmap["Main::ModifyOp"] = ModifyOp.$emitAPI;
_$emitmap["Main::RemoveOp"] = RemoveOp.$emitAPI;
_$emitmap["Main::DatabaseIndex"] = DatabaseIndex.$emitAPI;
_$emitmap["Main::Database"] = Database.$emitAPI;
_$emitmap["(|CString, Main::Database|)"] = (emitter, value) => "(|" + emitter.emitValue("CString", value[0]) + emitter.emitValue("Main::Database", value[1]) + "|)";
_$emitmap["(|Main::Database, Main::DatabaseIndex|)"] = (emitter, value) => "(|" + emitter.emitValue("Main::Database", value[0]) + emitter.emitValue("Main::DatabaseIndex", value[1]) + "|)";
_$emitmap["(|CString, List<CString>|)"] = (emitter, value) => "(|" + emitter.emitValue("CString", value[0]) + emitter.emitValue("List<CString>", value[1]) + "|)";

import { loadConstAndValidateRESystem } from "@bosque/jsbrex";
loadConstAndValidateRESystem([]);
process.stdout.write(`Error -- main function not found in main namespace\n`);