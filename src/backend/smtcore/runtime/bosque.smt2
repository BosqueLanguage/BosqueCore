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

;;
;; enum datatypes
;; SAMPLE -- (declare-datatype (EnumType a b c)) 
;;
;;--ENUM DECLS--;;

;;
;; typedecl datatypes 
;;

;;SAMPLE -- (declare-datatype TAType ((TAType-mk p)))

;;
;; typedecl results -- set of type alias results per type alias type
;;

;;
;; Entity datatypes 
;;
(declare-datatypes (
    ;;--ENTITY_DECLS--;;
    (@Term 0)
    ) (
        ;;--ENTITY_CONSTRUCTORS--;;
        (
            (@Term-mk-None)
            ;;--TYPEDECL_TERM_CONSTRUCTORS--;;
            ;;--ENTITY_TERM_CONSTRUCTORS--;;
        )
    )
)

;;NLA options
(declare-fun @NLA_I_mult (Int Int) Int)
(declare-fun @NLA_I_div (Int Int) Int)

;;--TYPE_SUBTYPE--;;

;;--GLOBAL_DECLS--;;

;;--FUNCTION_DECLS--;;

;;--GLOBAL_DEFINITIONS--;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun mmap ((a (Seq Int)) (g (Array Int Bool))) (Seq Bool)
    (seq.map g a))

(declare-const ain (Seq Int))
(assert (= ain (seq.++ (seq.unit 1) (seq.unit 2))))

(declare-const aout (Seq Bool))
(assert (= aout (mmap ain (lambda ((x Int)) (ite (> x 1) true false)))))