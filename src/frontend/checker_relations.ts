import {strict as assert} from "assert";

import { ErrorTypeSignature, TemplateConstraintScope, TypeSignature } from "./type";

class TypeCheckerRelations {
    getStringOfType(vtype: TypeSignature): TypeSignature {
        //TODO: given a validator type return a StringOf<vtype> type reference
        xxxx;
    }

    getASCIIStringOfType(vtype: TypeSignature): TypeSignature {
        //TODO: given a validator type return a StringOf<vtype> type reference
        xxxx;
    }

    refineType(src: TypeSignature, refine: TypeSignature): { overlap: TypeSignature | undefined, remain: TypeSignature | undefined } {
        //If src is an error then just return error for both
        if(src instanceof ErrorTypeSignature) {
            return { overlap: src, remain: src };
        }

        //If the refinement is indeterminate (an error) then just nop and return src as the option for both
        if(refine instanceof ErrorTypeSignature) {
            return { overlap: src, remain: src };
        }


        //now do the actual cases
        xxxx;
    }

    isSubtypeOf(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert((t1 instanceof ErrorTypeSignature) || (t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        xxxx;
    }

    areSameTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert((t1 instanceof ErrorTypeSignature) || (t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        xxxx;
    }

    isNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    isBooleanType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    isUniqueNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        //check special TNumeric template as well as the specific possibilities
        xxxx;
    }
}

export {
    TypeCheckerRelations
};
