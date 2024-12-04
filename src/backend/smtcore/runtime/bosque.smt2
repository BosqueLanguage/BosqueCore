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
(define-datatype Nat () Int)
;;Int is Int
(define-datatype BigNat () Int)
(define-datatype BigInt () Int)
(define-datatype Float () Real)
(define-datatype CString () String)
;;String is String


;;
;; primitive results 
;;
(declare-datatype @ResultTrgt-None ( (@ResultTrgt-None-mk-err) (@ResultTrgt-None-mk-ok (@ResultTrgt-None-value None)) ))
(define-fun @ResultTrgt-None-is-err ((x @ResultTrgt-None)) Bool (_ is @ResultTrgt-None-mk-err x))

(declare-datatype @ResultOther ( par ( T )
    ( 
        (@ResultOther-mk-err)
        (@ResultOther-mk-ok (@ResultOther-value T)) 
    )
))

(declare-datatype @Result ( par ( T )
    ( 
        (some (value T)) 
    )
))

;;
;; typedecl datatypes 
;;
(declare-datatype T ())

;;
;; typedecl results 
;;

;;
;; Entity datatypes 
;;
(declare-datatypes (
    (@ResultT-None 0)
    (@ResultT-Nothing 0)
    (@ResultT-Bool 0)
    (@ResultT-Int 0)
    (@ResultT-Nat 0)
    (@ResultT-BigInt 0)
    (@ResultT-BigNat 0)
    (@ResultT-Float 0)
    (@ResultT-Decimal 0)
    (@ResultT-Rational 0)
    (@ResultT-String 0)
    (@ResultT-ASCIIString 0)
    (@ResultT-ByteBuffer 0)
    (@ResultT-DateTime 0)
    (@ResultT-UTCDateTime 0)
    (@ResultT-PlainDate 0)
    (@ResultT-PlainTime 0)
    (@ResultT-TickTime 0)
    (@ResultT-LogicalTime 0)
    (@ResultT-ISOTimeStamp 0)
    (@ResultT-UUIDv4 0)
    (@ResultT-UUIDv7 0)
    (@ResultT-SHAContentHash 0)
    (@ResultT-Regex 0)
    ;;--RESULT_T_DECLS--;;
    ) (
        ( (@ResultT-mk-ok-None (@ResultT-None-val None)) (@ResultT-mk-err-None (@ResultT-None-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Nothing (@ResultT-Nothing-val Nothing)) (@ResultT-mk-err-Nothing (@ResultT-Nothing-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Bool (@ResultT-Bool-val Bool)) (@ResultT-mk-err-Bool (@ResultT-Bool-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Int (@ResultT-Int-val Int)) (@ResultT-mk-err-Int (@ResultT-Int-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Nat (@ResultT-Nat-val Int)) (@ResultT-mk-err-Nat (@ResultT-Nat-err @ErrorKind)) )
        ( (@ResultT-mk-ok-BigInt (@ResultT-BigInt-val Int)) (@ResultT-mk-err-BigInt (@ResultT-BigInt-err @ErrorKind)) )
        ( (@ResultT-mk-ok-BigNat (@ResultT-BigNat-val Int)) (@ResultT-mk-err-BigNat (@ResultT-BigNat-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Float (@ResultT-Float-val @Float)) (@ResultT-mk-err-Float (@ResultT-Float-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Decimal (@ResultT-Decimal-val @Decimal)) (@ResultT-mk-err-Decimal (@ResultT-Decimal-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Rational (@ResultT-Rational-val @Rational)) (@ResultT-mk-err-Rational (@ResultT-Rational-err @ErrorKind)) )
        ( (@ResultT-mk-ok-String (@ResultT-String-val String)) (@ResultT-mk-err-String (@ResultT-String-err @ErrorKind)) )
        ( (@ResultT-mk-ok-ASCIIString (@ResultT-ASCIIString-val String)) (@ResultT-mk-err-ASCIIString (@ResultT-ASCIIString-err @ErrorKind)) )
        ( (@ResultT-mk-ok-ByteBuffer (@ResultT-ByteBuffer-val (Seq (_ BitVec 8)))) (@ResultT-mk-err-ByteBuffer (@ResultT-ByteBuffer-err @ErrorKind)) )
        ( (@ResultT-mk-ok-DateTime (@ResultT-DateTime-val @IdealDateTime)) (@ResultT-mk-err-DateTime (@ResultT-DateTime-err @ErrorKind)) )
        ( (@ResultT-mk-ok-UTCDateTime (@ResultT-UTCDateTime-val @IdealDateTime)) (@ResultT-mk-err-UTCDateTime (@ResultT-UTCDateTime-err @ErrorKind)) )
        ( (@ResultT-mk-ok-PlainDate (@ResultT-PlainDate-val @IdealDateTime)) (@ResultT-mk-err-PlainDate (@ResultT-PlainDate-err @ErrorKind)) )
        ( (@ResultT-mk-ok-PlainTime (@ResultT-PlainTime-val @IdealDateTime)) (@ResultT-mk-err-PlainTime (@ResultT-PlainTime-err @ErrorKind)) )
        ( (@ResultT-mk-ok-TickTime (@ResultT-TickTime-val Int)) (@ResultT-mk-err-TickTime (@ResultT-TickTime-err @ErrorKind)) )
        ( (@ResultT-mk-ok-LogicalTime (@ResultT-LogicalTime-val Int)) (@ResultT-mk-err-LogicalTime (@ResultT-LogicalTime-err @ErrorKind)) )
        ( (@ResultT-mk-ok-ISOTimeStamp (@ResultT-ISOTimeStamp-val @IdealDateTime)) (@ResultT-mk-err-ISOTimeStamp (@ResultT-ISOTimeStamp-err @ErrorKind)) )
        ( (@ResultT-mk-ok-UUIDv4 (@ResultT-UUIDv4-val String)) (@ResultT-mk-err-UUIDv4 (@ResultT-UUIDv4-err @ErrorKind)) )
        ( (@ResultT-mk-ok-UUIDv7 (@ResultT-UUIDv7-val String)) (@ResultT-mk-err-UUIDv7 (@ResultT-UUIDv7-err @ErrorKind)) )
        ( (@ResultT-mk-ok-SHAContentHash (@ResultT-SHAContentHash-val (_ BitVec 16))) (@ResultT-mk-err-SHAContentHash (@ResultT-SHAContentHash-err @ErrorKind)) )
        ( (@ResultT-mk-ok-Regex (@ResultT-Regex-val String)) (@ResultT-mk-err-Regex (@ResultT-Regex-err @ErrorKind)) )
        ;;--RESULT_T_CONSTRUCTORS--;;
    )
)

(declare-datatype @Term 
    (
        (@Term-mk-None)
        (@Term-mk-Bool (@Term-Bool Bool))
        (@Term-mk-Nat (@Term-Nat Nat))
        (@Term-mk-Int (@Term-Int Int))
        (@Term-mk-BigNat (@Term-BigNat BigNat))
        (@Term-mk-BigInt (@Term-BigInt BigInt))
        (@Term-mk-Float (@Term-Float Float))
        (@Term-mk-CString (@Term-CString CString))
        (@Term-mk-String (@Term-String String))
        ;;--TYPE_CONSTRUCTORS--;;
    )
)

;;Checked arith operations
(define-fun @Nat_checked_trgt_sub ((x Int) (y Int)) @ResultT-Nat 
    (ite (<= y x) (@ResultT-mk-ok-Nat (- x y)) (@ResultT-mk-err-Nat @error-target))
)

(define-fun @Nat_checked_sub ((x Int) (y Int)) @ResultO-Nat
    (ite (<= y x) (@ResultO-mk-ok-Nat (- x y)) (@ResultO-mk-err-Nat @error-other))
)

(define-fun @BigNat_checked_trgt_sub ((x Int) (y Int)) @ResultT-BigNat 
    (ite (<= y x) (@ResultT-mk-ok-BigNat (- x y)) (@ResultT-mk-err-BigNat @error-target))
)

(define-fun @BigNat_checked_sub ((x Int) (y Int)) @ResultO-BigNat 
    (ite (<= y x) (@ResultO-mk-ok-BigNat (- x y)) (@ResultO-mk-err-BigNat @error-other))
)

(define-fun @Nat_checked_trgt_div ((x Int) (y Int)) @ResultT-Nat 
    (ite (= y 0) (@ResultT-mk-err-Nat @error-target) (@ResultT-mk-ok-Nat (@Nat_div x y)))
)

(define-fun @Nat_checked_div ((x Int) (y Int)) @ResultO-Nat 
    (ite (= y 0) (@ResultO-mk-err-Nat @error-other) (@ResultO-mk-ok-Nat (@Nat_div x y)))
)

(define-fun @BigNat_checked_trgt_div ((x Int) (y Int)) @ResultT-BigNat 
    (ite (= y 0) (@ResultT-mk-err-BigNat @error-target) (@ResultT-mk-ok-BigNat (@BigNat_div x y)))
)

(define-fun @BigNat_checked_div ((x Int) (y Int)) @ResultO-BigNat 
    (ite (= y 0) (@ResultO-mk-err-BigNat @error-other) (@ResultO-mk-ok-BigNat (@BigNat_div x y)))
)

(define-fun @Int_checked_trgt_div ((x Int) (y Int)) @ResultT-Int 
    (ite (= y 0) (@ResultT-mk-err-Int @error-target) (@ResultT-mk-ok-Int (@Int_div x y)))
)

(define-fun @Int_checked_div ((x Int) (y Int)) @ResultO-Int 
    (ite (= y 0) (@ResultO-mk-err-Int @error-other) (@ResultO-mk-ok-Int (@Int_div x y)))
)

(define-fun @BigInt_checked_trgt_div ((x Int) (y Int)) @ResultT-BigInt 
    (ite (= y 0) (@ResultT-mk-err-BigInt @error-target) (@ResultT-mk-ok-BigInt (@BigInt_div x y)))
)

(define-fun @BigInt_checked_div ((x Int) (y Int)) @ResultO-BigInt 
    (ite (= y 0) (@ResultO-mk-err-BigInt @error-other) (@ResultO-mk-ok-BigInt (@BigInt_div x y)))
)

;;NLA options
(declare-fun @Nat_mult (Int Int) Int)
(declare-fun @Nat_div (Int Int) Int)

(declare-fun @Int_mult (Int Int) Int)
(declare-fun @Int_div (Int Int) Int)

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