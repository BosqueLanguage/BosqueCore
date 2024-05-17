import {strict as assert} from "assert";
import { TypeSignature } from "./type";

class TypeCheckerRelations {
    refineType(src: TypeSignature, refine: TypeSignature): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        if (oft.isInvalidType() || witht.isInvalidType()) {
            return { tp: undefined, fp: undefined };
        }

        if (oft.typeID === witht.typeID) {
            return { tp: oft, fp: undefined };
        }

        const paths = oft.options.map((opt) => this.splitAtomWithType(opt, witht));
        let tp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.tp));
        let fp = ([] as ResolvedType[]).concat(...paths.map((pp) => pp.fp));

        return {tp: tp.length !== 0 ? this.normalizeUnionList(tp) : undefined, fp: fp.length !== 0 ? this.normalizeUnionList(fp) : undefined};
    }

    private atomSubtypeOf(t1: ResolvedAtomType, t2: ResolvedAtomType): boolean {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.typeID);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.typeID, new Map<string, boolean>());
            memores = this.m_atomSubtypeRelationMemo.get(t1.typeID) as Map<string, boolean>;
        }

        let memoval = memores.get(t2.typeID);
        if (memoval !== undefined) {
            return memoval;
        }

        let res = false;

        if (t1.typeID === t2.typeID) {
            res = true;
        }
        else if (t1 instanceof ResolvedConceptAtomType && t2 instanceof ResolvedConceptAtomType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t2 instanceof ResolvedConceptAtomType) {
            if (t1 instanceof ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleConcept(t1, t2);
            }
            else if (t1 instanceof ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordConcept(t1, t2);
            }
            else {
                //fall-through
            }
        }
        else {
            //fall-through
        }

        memores.set(t2.typeID, res);
        return res;
    }

    isSubtypeOf(t1: TypeSignature, t2: TypeSignature): boolean {
        xxxx;
    }

    typesEqual(t1: TypeSignature, t2: TypeSignature): boolean {
        xxxx;
    }

    typesUniqueAndEqual(t1: TypeSignature, t2: TypeSignature): boolean {
        xxxx;
    }
}

export {
    TypeCheckerRelations
};
