;;
;;Template file for building SMTLIB models of Bosque code
;;

(declare-datatype @Result (par (T) (
    (@Result-err-trgt)
    (@Result-err-other) 
    (@Result-ok (@Result-value T))
)))

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

;;NLA options
(declare-fun @NLA_I_mult (Int Int) Int)
(declare-fun @NLA_I_div (Int Int) Int)

;;--GLOBAL_DECLS--;;

;;--PRE_FUNCS--;;

;;--FUNCTION_DECLS--;;

;;--GLOBAL_IMPLS--;;

