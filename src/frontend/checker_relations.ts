import {strict as assert} from "assert";

import { ErrorTypeSignature, TemplateConstraintScope, TypeSignature } from "./type";

class TypeCheckerRelations {
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

    //Check is t1 is a subtype of t2
    isSubtypeOf(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert((t1 instanceof ErrorTypeSignature) || (t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        xxxx;
    }

    //Check if t1 and t2 are the same type
    areSameTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert((t1 instanceof ErrorTypeSignature) || (t2 instanceof ErrorTypeSignature), "Checking subtypes on errors");

        xxxx;
    }

    //Check if t1 is the type None (exactly)
    isNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t includes None (e.g. None is a subtype of t)
    includesNoneType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t1 is the type Nothing (exactly)
    isNothingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t incudes Nothing (e.g. Nothing is a subtype of t)
    includesNothingType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        xxxx;
    }

    //Check if t is the type Bool (exactly)
    isBooleanType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if t is the type Void (exactly)
    isVoidType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check is this type is unique (i.e. not a union or concept type)
    isUniqueType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is unique and a numeric type of some sort (either primitive number or a typedecl of a numeric type)
    isUniqueNumericType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");
        
        //check special TNumeric template as well as the specific possibilities
        xxxx;
    }

    //Check if this type is a primitive type in Core
    isPrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is a typedecl of some sort
    isTypeDeclType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Get the base primitive type of a typedecl (resolving through typedecls and aliases as needed)
    getTypeDeclBasePrimitiveType(t: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Check if this type is a KeyType (e.g. a subtype of KeyType)
    isKeyType(t: TypeSignature, tconstrain: TemplateConstraintScope): boolean {
        assert(t instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //Compute the upper bound of two types for use in control-flow join types
    joinTypes(t1: TypeSignature, t2: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature {
        assert(t1 instanceof ErrorTypeSignature, "Checking subtypes on errors");
        assert(t2 instanceof ErrorTypeSignature, "Checking subtypes on errors");

        xxxx;
    }

    //If possible resolve a single canonical type for a type -- e.g. not a union and no alias or constraint redirects
    tryResolveSingleCanonicalType(vtype: TypeSignature, tconstrain: TemplateConstraintScope): TypeSignature | undefined {
        xxxx;
    }
}

export {
    TypeCheckerRelations
};
