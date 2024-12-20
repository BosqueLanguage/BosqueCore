;;
;;Template file for building SMTLIB models of Bosque code
;;

;;
;;Error kinds and results that we propagate
;;

;;
;;Bounds on input numeric/string/container sizes -- TODO: in the future let solver set these....
;;
(declare-const _@INPUT_NUMBER_MIN Int) (assert (= _@INPUT_NUMBER_MIN -256))
(declare-const _@INPUT_NUMBER_MAX Int) (assert (= _@INPUT_NUMBER_MAX 256))
(declare-const _@INPUT_STRING_MAX_SIZE Int) (assert (= _@INPUT_STRING_MAX_SIZE 64))
(declare-const _@INPUT_CONTAINER_MAX_SIZE Int) (assert (= _@INPUT_CONTAINER_MAX_SIZE 3))

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
;; primitive results 
;;

;;;;Target error result types
(declare-datatype @ResultTrgt-None ( (@ResultTrgt-None-mk-err) (@ResultTrgt-None-mk-ok (@ResultTrgt-None-ok None)) ))
(define-fun @ResultTrgt-None-is-err ((x @ResultTrgt-None)) Bool (= x @ResultTrgt-None-mk-err))
(define-fun @ResultTrgt-None-is-ok ((x @ResultTrgt-None)) Bool (not (= x @ResultTrgt-None-mk-err)))
(define-fun @ResultTrgt-None-get-ok ((x @ResultTrgt-None)) None none)

(declare-datatype @ResultTrgt-Bool ( (@ResultTrgt-Bool-mk-err) (@ResultTrgt-Bool-mk-ok (@ResultTrgt-Bool-ok Bool)) ))
(define-fun @ResultTrgt-Bool-is-err ((x @ResultTrgt-Bool)) Bool (= x @ResultTrgt-Bool-mk-err))
(define-fun @ResultTrgt-Bool-is-ok ((x @ResultTrgt-Bool)) Bool (not (= x @ResultTrgt-Bool-mk-err)))
(define-fun @ResultTrgt-Bool-get-ok ((x @ResultTrgt-Bool)) Bool (@ResultTrgt-Bool-ok x))

(declare-datatype @ResultTrgt-Nat ( (@ResultTrgt-Nat-mk-err) (@ResultTrgt-Nat-mk-ok (@ResultTrgt-Nat-ok Nat)) ))
(define-fun @ResultTrgt-Nat-is-err ((x @ResultTrgt-Nat)) Bool (= x @ResultTrgt-Nat-mk-err))
(define-fun @ResultTrgt-Nat-is-ok ((x @ResultTrgt-Nat)) Bool (not (= x @ResultTrgt-Nat-mk-err)))
(define-fun @ResultTrgt-Nat-get-ok ((x @ResultTrgt-Nat)) Nat (@ResultTrgt-Nat-ok x))

(declare-datatype @ResultTrgt-Int ( (@ResultTrgt-Int-mk-err) (@ResultTrgt-Int-mk-ok (@ResultTrgt-Int-ok Int)) ))
(define-fun @ResultTrgt-Int-is-err ((x @ResultTrgt-Int)) Bool (= x @ResultTrgt-Int-mk-err))
(define-fun @ResultTrgt-Int-is-ok ((x @ResultTrgt-Int)) Bool (not (= x @ResultTrgt-Int-mk-err)))
(define-fun @ResultTrgt-Int-get-ok ((x @ResultTrgt-Int)) Int (@ResultTrgt-Int-ok x))

(declare-datatype @ResultTrgt-Float ( (@ResultTrgt-Float-mk-err) (@ResultTrgt-Float-mk-ok (@ResultTrgt-Float-ok Float)) ))
(define-fun @ResultTrgt-Float-is-err ((x @ResultTrgt-Float)) Bool (= x @ResultTrgt-Float-mk-err))
(define-fun @ResultTrgt-Float-is-ok ((x @ResultTrgt-Float)) Bool (not (= x @ResultTrgt-Float-mk-err)))
(define-fun @ResultTrgt-Float-get-ok ((x @ResultTrgt-Float)) Float (@ResultTrgt-Float-ok x))

(declare-datatype @ResultTrgt-CString ( (@ResultTrgt-CString-mk-err) (@ResultTrgt-CString-mk-ok (@ResultTrgt-CString-ok CString)) ))
(define-fun @ResultTrgt-CString-is-err ((x @ResultTrgt-CString)) Bool (= x @ResultTrgt-CString-mk-err))
(define-fun @ResultTrgt-CString-is-ok ((x @ResultTrgt-CString)) Bool (not (= x @ResultTrgt-CString-mk-err)))
(define-fun @ResultTrgt-CString-get-ok ((x @ResultTrgt-CString)) CString (@ResultTrgt-CString-ok x))

(declare-datatype @ResultTrgt-String ( (@ResultTrgt-String-mk-err) (@ResultTrgt-String-mk-ok (@ResultTrgt-String-ok String)) ))
(define-fun @ResultTrgt-String-is-err ((x @ResultTrgt-String)) Bool (= x @ResultTrgt-String-mk-err))
(define-fun @ResultTrgt-String-is-ok ((x @ResultTrgt-String)) Bool (not (= x @ResultTrgt-String-mk-err)))
(define-fun @ResultTrgt-String-get-ok ((x @ResultTrgt-String)) String (@ResultTrgt-String-ok x))

;;;;Other error result types
(declare-datatype @ResultOther-None ( (@ResultOther-None-mk-err) (@ResultOther-None-mk-ok (@ResultOther-None-ok None)) ))
(define-fun @ResultOther-None-is-err ((x @ResultOther-None)) Bool (= x @ResultOther-None-mk-err))
(define-fun @ResultOther-None-is-ok ((x @ResultOther-None)) Bool (not (= x @ResultOther-None-mk-err)))
(define-fun @ResultOther-None-get-ok ((x @ResultOther-None)) None none)

(declare-datatype @ResultOther-Bool ( (@ResultOther-Bool-mk-err) (@ResultOther-Bool-mk-ok (@ResultOther-Bool-ok Bool)) ))
(define-fun @ResultOther-Bool-is-err ((x @ResultOther-Bool)) Bool (= x @ResultOther-Bool-mk-err))
(define-fun @ResultOther-Bool-is-ok ((x @ResultOther-Bool)) Bool (not (= x @ResultOther-Bool-mk-err)))
(define-fun @ResultOther-Bool-get-ok ((x @ResultOther-Bool)) Bool (@ResultOther-Bool-ok x))

(declare-datatype @ResultOther-Nat ( (@ResultOther-Nat-mk-err) (@ResultOther-Nat-mk-ok (@ResultOther-Nat-ok Nat)) ))
(define-fun @ResultOther-Nat-is-err ((x @ResultOther-Nat)) Bool (= x @ResultOther-Nat-mk-err))
(define-fun @ResultOther-Nat-is-ok ((x @ResultOther-Nat)) Bool (not (= x @ResultOther-Nat-mk-err)))
(define-fun @ResultOther-Nat-get-ok ((x @ResultOther-Nat)) Nat (@ResultOther-Nat-ok x))

(declare-datatype @ResultOther-Int ( (@ResultOther-Int-mk-err) (@ResultOther-Int-mk-ok (@ResultOther-Int-ok Int)) ))
(define-fun @ResultOther-Int-is-err ((x @ResultOther-Int)) Bool (= x @ResultOther-Int-mk-err))
(define-fun @ResultOther-Int-is-ok ((x @ResultOther-Int)) Bool (not (= x @ResultOther-Int-mk-err)))
(define-fun @ResultOther-Int-get-ok ((x @ResultOther-Int)) Int (@ResultOther-Int-ok x))

(declare-datatype @ResultOther-Float ( (@ResultOther-Float-mk-err) (@ResultOther-Float-mk-ok (@ResultOther-Float-ok Float)) ))
(define-fun @ResultOther-Float-is-err ((x @ResultOther-Float)) Bool (= x @ResultOther-Float-mk-err))
(define-fun @ResultOther-Float-is-ok ((x @ResultOther-Float)) Bool (not (= x @ResultOther-Float-mk-err)))
(define-fun @ResultOther-Float-get-ok ((x @ResultOther-Float)) Float (@ResultOther-Float-ok x))

(declare-datatype @ResultOther-CString ( (@ResultOther-CString-mk-err) (@ResultOther-CString-mk-ok (@ResultOther-CString-ok CString)) ))
(define-fun @ResultOther-CString-is-err ((x @ResultOther-CString)) Bool (= x @ResultOther-CString-mk-err))
(define-fun @ResultOther-CString-is-ok ((x @ResultOther-CString)) Bool (not (= x @ResultOther-CString-mk-err)))
(define-fun @ResultOther-CString-get-ok ((x @ResultOther-CString)) CString (@ResultOther-CString-ok x))

(declare-datatype @ResultOther-String ( (@ResultOther-String-mk-err) (@ResultOther-String-mk-ok (@ResultOther-String-ok String)) ))
(define-fun @ResultOther-String-is-err ((x @ResultOther-String)) Bool (= x @ResultOther-String-mk-err))
(define-fun @ResultOther-String-is-ok ((x @ResultOther-String)) Bool (not (= x @ResultOther-String-mk-err)))
(define-fun @ResultOther-String-get-ok ((x @ResultOther-String)) String (@ResultOther-String-ok x))

;;;;General error result types
(declare-datatype @Result-None ( (@Result-None-mk-err-trgt) (@Result-None-mk-err-other) (@Result-None-mk-ok (@Result-None-ok None)) ))
(define-fun @Result-None-from-trgt ((x @ResultTrgt-None)) @Result-None (ite (= x @ResultTrgt-None-mk-err) @Result-None-mk-err-trgt (@Result-None-mk-ok (@ResultTrgt-None-get-ok x))))
(define-fun @Result-None-from-other ((x @ResultOther-None)) @Result-None (ite (= x @ResultOther-None-mk-err) @Result-None-mk-err-other (@Result-None-mk-ok (@ResultOther-None-get-ok x))))
(define-fun @Result-None-is-err ((x @Result-None)) Bool (or (= x @Result-None-mk-err-trgt) (= x @Result-None-mk-err-other)))
(define-fun @Result-None-is-ok ((x @Result-None)) Bool (and (not (= x @Result-None-mk-err-trgt)) (not (= x @Result-None-mk-err-other))))
(define-fun @Result-None-get-ok ((x @Result-None)) None (@Result-None-ok x))

(declare-datatype @Result-Bool ( (@Result-Bool-mk-err-trgt) (@Result-Bool-mk-err-other) (@Result-Bool-mk-ok (@Result-Bool-ok Bool)) ))
(define-fun @Result-Bool-from-trgt ((x @ResultTrgt-Bool)) @Result-Bool (ite (= x @ResultTrgt-Bool-mk-err) @Result-Bool-mk-err-trgt (@Result-Bool-mk-ok (@ResultTrgt-Bool-get-ok x))))
(define-fun @Result-Bool-from-other ((x @ResultOther-Bool)) @Result-Bool (ite (= x @ResultOther-Bool-mk-err) @Result-Bool-mk-err-other (@Result-Bool-mk-ok (@ResultOther-Bool-get-ok x))))
(define-fun @Result-Bool-is-err ((x @Result-Bool)) Bool (or (= x @Result-Bool-mk-err-trgt) (= x @Result-Bool-mk-err-other)))
(define-fun @Result-Bool-is-ok ((x @Result-Bool)) Bool (and (not (= x @Result-Bool-mk-err-trgt)) (not (= x @Result-Bool-mk-err-other))))
(define-fun @Result-Bool-get-ok ((x @Result-Bool)) Bool (@Result-Bool-ok x))

(declare-datatype @Result-Nat ( (@Result-Nat-mk-err-trgt) (@Result-Nat-mk-err-other) (@Result-Nat-mk-ok (@Result-Nat-ok Nat)) ))
(define-fun @Result-Nat-from-trgt ((x @ResultTrgt-Nat)) @Result-Nat (ite (= x @ResultTrgt-Nat-mk-err) @Result-Nat-mk-err-trgt (@Result-Nat-mk-ok (@ResultTrgt-Nat-get-ok x))))
(define-fun @Result-Nat-from-other ((x @ResultOther-Nat)) @Result-Nat (ite (= x @ResultOther-Nat-mk-err) @Result-Nat-mk-err-other (@Result-Nat-mk-ok (@ResultOther-Nat-get-ok x))))
(define-fun @Result-Nat-is-err ((x @Result-Nat)) Bool (or (= x @Result-Nat-mk-err-trgt) (= x @Result-Nat-mk-err-other)))
(define-fun @Result-Nat-is-ok ((x @Result-Nat)) Bool (and (not (= x @Result-Nat-mk-err-trgt)) (not (= x @Result-Nat-mk-err-other))))
(define-fun @Result-Nat-get-ok ((x @Result-Nat)) Nat (@Result-Nat-ok x))

(declare-datatype @Result-Int ( (@Result-Int-mk-err-trgt) (@Result-Int-mk-err-other) (@Result-Int-mk-ok (@Result-Int-ok Int)) ))
(define-fun @Result-Int-from-trgt ((x @ResultTrgt-Int)) @Result-Int (ite (= x @ResultTrgt-Int-mk-err) @Result-Int-mk-err-trgt (@Result-Int-mk-ok (@ResultTrgt-Int-get-ok x))))
(define-fun @Result-Int-from-other ((x @ResultOther-Int)) @Result-Int (ite (= x @ResultOther-Int-mk-err) @Result-Int-mk-err-other (@Result-Int-mk-ok (@ResultOther-Int-get-ok x))))
(define-fun @Result-Int-is-err ((x @Result-Int)) Bool (or (= x @Result-Int-mk-err-trgt) (= x @Result-Int-mk-err-other)))
(define-fun @Result-Int-is-ok ((x @Result-Int)) Bool (and (not (= x @Result-Int-mk-err-trgt)) (not (= x @Result-Int-mk-err-other))))
(define-fun @Result-Int-get-ok ((x @Result-Int)) Int (@Result-Int-ok x))

(declare-datatype @Result-Float ( (@Result-Float-mk-err-trgt) (@Result-Float-mk-err-other) (@Result-Float-mk-ok (@Result-Float-ok Float)) ))
(define-fun @Result-Float-from-trgt ((x @ResultTrgt-Float)) @Result-Float (ite (= x @ResultTrgt-Float-mk-err) @Result-Float-mk-err-trgt (@Result-Float-mk-ok (@ResultTrgt-Float-get-ok x))))
(define-fun @Result-Float-from-other ((x @ResultOther-Float)) @Result-Float (ite (= x @ResultOther-Float-mk-err) @Result-Float-mk-err-other (@Result-Float-mk-ok (@ResultOther-Float-get-ok x))))
(define-fun @Result-Float-is-err ((x @Result-Float)) Bool (or (= x @Result-Float-mk-err-trgt) (= x @Result-Float-mk-err-other)))
(define-fun @Result-Float-is-ok ((x @Result-Float)) Bool (and (not (= x @Result-Float-mk-err-trgt)) (not (= x @Result-Float-mk-err-other))))
(define-fun @Result-Float-get-ok ((x @Result-Float)) Float (@Result-Float-ok x))

(declare-datatype @Result-CString ( (@Result-CString-mk-err-trgt) (@Result-CString-mk-err-other) (@Result-CString-mk-ok (@Result-CString-ok CString)) ))
(define-fun @Result-CString-from-trgt ((x @ResultTrgt-CString)) @Result-CString (ite (= x @ResultTrgt-CString-mk-err) @Result-CString-mk-err-trgt (@Result-CString-mk-ok (@ResultTrgt-CString-get-ok x))))
(define-fun @Result-CString-from-other ((x @ResultOther-CString)) @Result-CString (ite (= x @ResultOther-CString-mk-err) @Result-CString-mk-err-other (@Result-CString-mk-ok (@ResultOther-CString-get-ok x))))
(define-fun @Result-CString-is-err ((x @Result-CString)) Bool (or (= x @Result-CString-mk-err-trgt) (= x @Result-CString-mk-err-other)))
(define-fun @Result-CString-is-ok ((x @Result-CString)) Bool (and (not (= x @Result-CString-mk-err-trgt)) (not (= x @Result-CString-mk-err-other))))
(define-fun @Result-CString-get-ok ((x @Result-CString)) CString (@Result-CString-ok x))

(declare-datatype @Result-String ( (@Result-String-mk-err-trgt) (@Result-String-mk-err-other) (@Result-String-mk-ok (@Result-String-ok String)) ))
(define-fun @Result-String-from-trgt ((x @ResultTrgt-String)) @Result-String (ite (= x @ResultTrgt-String-mk-err) @Result-String-mk-err-trgt (@Result-String-mk-ok (@ResultTrgt-String-get-ok x))))
(define-fun @Result-String-from-other ((x @ResultOther-String)) @Result-String (ite (= x @ResultOther-String-mk-err) @Result-String-mk-err-other (@Result-String-mk-ok (@ResultOther-String-get-ok x))))
(define-fun @Result-String-is-err ((x @Result-String)) Bool (or (= x @Result-String-mk-err-trgt) (= x @Result-String-mk-err-other)))
(define-fun @Result-String-is-ok ((x @Result-String)) Bool (and (not (= x @Result-String-mk-err-trgt)) (not (= x @Result-String-mk-err-other))))
(define-fun @Result-String-get-ok ((x @Result-String)) String (@Result-String-ok x))

;;
;; enum datatypes 
;;

;;SAMPLE -- (declare-datatypes () ((EnumType a b c)))

;;
;; enum results -- set of enum results per enum type
;;

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