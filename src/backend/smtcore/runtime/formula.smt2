;;
;;Template file for building SMTLIB models of Bosque code
;;

(declare-datatype @Result (par (T) (
    (@Result-err-trgt)
    (@Result-err-other) 
    (@Result-ok (@Result-value T))
)))

(declare-datatypes (
    (@EList-2 2)
    (@EList-3 3)
    (@EList-4 4)
    ) (
        (par (T1 T2) ((@EList-2-mk (@EList-2-0 T1) (@EList-2-1 T2))) )
        (par (T1 T2 T3) ((@EList-3-mk (@EList-3-0 T1) (@EList-3-1 T2) (@EList-3-2 T3))) )
        (par (T1 T2 T3 T4) ((@EList-4-mk (@EList-4-0 T1) (@EList-4-1 T2) (@EList-4-2 T3) (@EList-4-3 T4))) )
    )
)

;;
;; Primitive datatypes 
;;
(declare-datatype None ((none)))
;;Bool is Bool
(define-sort Nat () Int)
;;Int is Int
(define-sort BigNat () Int)
(define-sort BigInt () Int)
(define-sort Float () Real)
(define-sort CString () String)
;;String is String

;;--ENUM_DECLS--;;
;;--TYPEDECL_DECLS--;;

;;
;; Entity datatypes 
;;
(declare-datatypes (
    ;;--SPECIAL_DECLS--;;
    ;;--COLLECTION_DECLS--;;
    ;;--ENTITY_DECLS--;;
    ;;--DATATYPE_DECLS--;;
    (@Term 0)
    ) (
        ;;--SPECIAL_CONSTRUCTORS--;;
        ;;--COLLECTION_CONSTRUCTORS--;;
        ;;--ENTITY_CONSTRUCTORS--;;
        ;;--DATATYPE_CONSTRUCTORS--;;
        (
            (@Term-mk-None)
            ;;--TYPEDECL_TERM_CONSTRUCTORS--;;
            ;;--SPECIAL_TERM_CONSTRUCTORS--;;
            ;;--ENTITY_TERM_CONSTRUCTORS--;;
            ;;--DATATYPE_TERM_CONSTRUCTORS--;;
        )
    )
)

;;--SUBTYPE_PREDICATES--;;

;;--GLOBAL_DECLS--;;

;;--PRE_FUNCS--;;

;;--FUNCTION_DECLS--;;

;;--GLOBAL_IMPLS--;;

