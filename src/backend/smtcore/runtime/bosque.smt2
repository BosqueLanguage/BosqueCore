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

;;
;;Error kinds and results that we propagate
;;
(declare-datatype @ResultT (par (T) ((@ResultT-err) (@ResultT-ok (@ResultT-value T)))))
(declare-datatype @ResultO (par (T) ((@ResultO-err) (@ResultO-ok (@ResultO-value T)))))

;;Any is either a @ResultKind-T @ResultKind-O
(declare-datatype @ResultA (par (T) (
    (@ResultA-err-t)
    (@ResultA-err-o) 
    (@ResultA-ok (@ResultA-value T))
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

;;
;; entity results 
;;

;;
;; term results 
;;

(declare-datatype @ResultTrgt-@Term ( (@ResultTrgt-@Term-mk-err) (@ResultTrgt-@Term-mk-ok (@ResultTrgt-@Term-ok @Term)) ))
(define-fun @ResultTrgt-@Term-is-err ((x @ResultTrgt-@Term)) Bool (= x @ResultTrgt-@Term-mk-err))
(define-fun @ResultTrgt-@Term-is-ok ((x @ResultTrgt-@Term)) Bool (not (= x @ResultTrgt-@Term-mk-err)))
(define-fun @ResultTrgt-@Term-get-ok ((x @ResultTrgt-@Term)) @Term (@ResultTrgt-@Term-ok x))

(declare-datatype @ResultOther-@Term ( (@ResultOther-@Term-mk-err) (@ResultOther-@Term-mk-ok (@ResultOther-@Term-ok Nat)) ))
(define-fun @ResultOther-@Term-is-err ((x @ResultOther-@Term)) Bool (= x @ResultOther-@Term-mk-err))
(define-fun @ResultOther-@Term-is-ok ((x @ResultOther-@Term)) Bool (not (= x @ResultOther-@Term-mk-err)))
(define-fun @ResultOther-@Term-get-ok ((x @ResultOther-@Term)) Nat (@ResultOther-@Term-ok x))

(declare-datatype @Result-Term ( (@Result-@Term-mk-err-trgt) (@Result-@Term-mk-err-other) (@Result-@Term-mk-ok (@Result-@Term-ok @Term)) ))
(define-fun @Result-@Term-from-trgt ((x @ResultTrgt-@Term)) @Result-@Term (ite (= x @ResultTrgt-@Term-mk-err) @Result-@Term-mk-err-trgt (@Result-@Term-mk-ok (@ResultTrgt-@Term-get-ok x))))
(define-fun @Result-@Term-from-other ((x @ResultOther-@Term)) @Result-@Term (ite (= x @ResultOther-@Term-mk-err) @Result-@Term-mk-err-other (@Result-@Term-mk-ok (@ResultOther-@Term-get-ok x))))
(define-fun @Result-@Term-is-err ((x @Result-@Term)) Bool (or (= x @Result-@Term-mk-err-trgt) (= x @Result-@Term-mk-err-other)))
(define-fun @Result-@Term-is-ok ((x @Result-@Term)) Bool (and (not (= x @Result-@Term-mk-err-trgt)) (not (= x @Result-@Term-mk-err-other))))
(define-fun @Result-@Term-get-ok ((x @Result-@Term)) @Term (@Result-@Term-ok x))

;;
;; term results per entity (or typedecl) type
;;

;;SAMPLE --
;; (define-fun @Result-@Term-from-Type ((x Type)) @Result-@Term (@Result-@Term-mk-ok (@Term-mk-Type x)))
;; (define-fun @Result-@Term-from-@ResultTrgt-Type ((x Type)) @Result-@Term (ite ....)
;; (define-fun @Result-@Term-from-@ResultOther-Type ((x Type)) @Result-@Term (ite ....)
;; (define-fun @Result-@Term-from-@Result-Type ((x @Result-Type)) @Result-@Term (ite ....)
;;
;; (define-fun @Result-Type-from-Term ((x @Term)) @Result-Type (@Result-Type-mk-ok (@Term-Type-value x)))
;; (define-fun @Result-Type-from-@ResultTrgt-@Term ((x @Term)) @Result-Type (ite ....)
;; (define-fun @Result-Type-from-@ResultOther-@Term ((x @Term)) @Result-Type (ite ....)
;; (define-fun @Result-Type-from-@Result-@Term ((x @Result-@Term)) @Result-Type (ite ....)

TODO: None action!!!!!

;;NLA options
(declare-fun @NLA_I_mult (Int Int) Int)
(declare-fun @NLA_I_div (Int Int) Int)

;;--TYPE_SUBTYPE--;;

;;--GLOBAL_DECLS--;;

;;--UF_DECLS--;;

;;--FUNCTION_DECLS--;;

;;--GLOBAL_DEFINITIONS--;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun mmap ((a (Seq Int)) (g (Array Int Bool))) (Seq Bool)
    (seq.map g a))

(declare-const ain (Seq Int))
(assert (= ain (seq.++ (seq.unit 1) (seq.unit 2))))

(declare-const aout (Seq Bool))
(assert (= aout (mmap ain (lambda ((x Int)) (ite (> x 1) true false)))))