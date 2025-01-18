;;
;;Template file for building SMTLIB models of Bosque code
;;

;;
;;Bounds on input numeric/string/container sizes -- TODO: in the future let solver set these....
;;
(declare-const _@INPUT_NUMBER_MIN Int) (assert (= _@INPUT_NUMBER_MIN -256))
(declare-const _@INPUT_NUMBER_MAX Int) (assert (= _@INPUT_NUMBER_MAX 256))
(declare-const _@INPUT_STRING_MAX_SIZE Int) (assert (= _@INPUT_STRING_MAX_SIZE 64))
(declare-const _@INPUT_CONTAINER_MAX_SIZE Int) (assert (= _@INPUT_CONTAINER_MAX_SIZE 3))

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
(define-sort Float () Real)
(define-sort CString () String)
;;String is String

;;--ENUM DECLS--;;
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


;;--TYPE_PRIMITIVE_CONCEPT_SUBTYPE--;;
;;--TYPE_CONCEPT_SUBTYPE--;;
;;--TYPE_DATATYPE_SUBTYPE--;;

;;NLA options
(declare-fun @NLA_I_mult (Int Int) Int)
(declare-fun @NLA_I_div (Int Int) Int)

;;--GLOBAL_DECLS--;;

;;--FUNCTION_DECLS--;;

;;--GLOBAL_DEFINITIONS--;;

