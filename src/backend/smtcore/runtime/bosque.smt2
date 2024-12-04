;;
;;Template file for building SMTLIB models of Bosque code
;;

;;
;;Error kinds that we propagate in results
;;;
(declare-sort @ErrorKind)
(declare-const @error-target @ErrorKind)
(declare-const @error-other @ErrorKind)

;;Make sure they are all different values
(assert (distinct @error-target @error-other))

;;Bounds on input numeric/string/container sizes -- TODO: in the future let solver set these....
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

(declare-datatype _@Some ( par ( T )
    ( (some (value T)) )
))

;;
;; Primitive datatypes 
;;
(declare-datatypes (
    (None 0)
    ; Bool -> Bool
    ; Int -> Int
    ; Nat -> Int
    ; BigInt -> Int
    ; BigNat -> Int
    ; Float -> @Float 
    ; CString -> String
    ; String -> String
    ; Regex -> String
    ;;--OO_DECLS--;;
    ) (
        ( (none) ) 
        ;;--OO_CONSTRUCTORS--;;
    )
)

(declare-datatypes (T) ((@ResultO (mk-pair (first T1) (second T2)))))

(declare-datatype @Term 
    (
        (@Term-mk-None)
        (@Term-mk-Bool (@Term-Bool Bool))
        (@Term-mk-Int (@Term-Int Int))
        (@Term-mk-Nat (@Term-Nat Int))
        (@Term-mk-BigInt (@Term-BigInt Int))
        (@Term-mk-BigNat (@Term-BigNat Int))
        (@Term-mk-Float (@Term-Float @Float))
        (@Term-mk-CString (@Term-CString String))
        (@Term-mk-String (@Term-String String))
        ;;--TYPE_CONSTRUCTORS--;;
    )
)

;;
;; ResultO datatypes 
;;
(declare-datatypes (
    (@ResultO-None 0)
    (@ResultO-Nothing 0)
    (@ResultO-Bool 0)
    (@ResultO-Int 0)
    (@ResultO-Nat 0)
    (@ResultO-BigInt 0)
    (@ResultO-BigNat 0)
    (@ResultO-Float 0)
    (@ResultO-Decimal 0)
    (@ResultO-Rational 0)
    (@ResultO-String 0)
    (@ResultO-ASCIIString 0)
    (@ResultO-ByteBuffer 0)
    (@ResultO-DateTime 0)
    (@ResultO-UTCDateTime 0)
    (@ResultO-PlainDate 0)
    (@ResultO-PlainTime 0)
    (@ResultO-TickTime 0)
    (@ResultO-LogicalTime 0)
    (@ResultO-ISOTimeStamp 0)
    (@ResultO-UUIDv4 0)
    (@ResultO-UUIDv7 0)
    (@ResultO-SHAContentHash 0)
    (@ResultO-Regex 0)
    ;;--RESULT_O_DECLS--;;
    ) (
        ( (@ResultO-mk-ok-None (@ResultO-None-val None)) (@ResultO-mk-err-None (@ResultO-None-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Nothing (@ResultO-Nothing-val Nothing)) (@ResultO-mk-err-Nothing (@ResultO-Nothing-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Bool (@ResultO-Bool-val Bool)) (@ResultO-mk-err-Bool (@ResultO-Bool-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Int (@ResultO-Int-val Int)) (@ResultO-mk-err-Int (@ResultO-Int-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Nat (@ResultO-Nat-val Int)) (@ResultO-mk-err-Nat (@ResultO-Nat-err @ErrorKind)) )
        ( (@ResultO-mk-ok-BigInt (@ResultO-BigInt-val Int)) (@ResultO-mk-err-BigInt (@ResultO-BigInt-err @ErrorKind)) )
        ( (@ResultO-mk-ok-BigNat (@ResultO-BigNat-val Int)) (@ResultO-mk-err-BigNat (@ResultO-BigNat-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Float (@ResultO-Float-val @Float)) (@ResultO-mk-err-Float (@ResultO-Float-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Decimal (@ResultO-Decimal-val @Decimal)) (@ResultO-mk-err-Decimal (@ResultO-Decimal-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Rational (@ResultO-Rational-val @Rational)) (@ResultO-mk-err-Rational (@ResultO-Rational-err @ErrorKind)) )
        ( (@ResultO-mk-ok-String (@ResultO-String-val String)) (@ResultO-mk-err-String (@ResultO-String-err @ErrorKind)) )
        ( (@ResultO-mk-ok-ASCIIString (@ResultO-ASCIIString-val String)) (@ResultO-mk-err-ASCIIString (@ResultO-ASCIIString-err @ErrorKind)) )
        ( (@ResultO-mk-ok-ByteBuffer (@ResultO-ByteBuffer-val (Seq (_ BitVec 8)))) (@ResultO-mk-err-ByteBuffer (@ResultO-ByteBuffer-err @ErrorKind)) )
        ( (@ResultO-mk-ok-DateTime (@ResultO-DateTime-val @IdealDateTime)) (@ResultO-mk-err-DateTime (@ResultO-DateTime-err @ErrorKind)) )
        ( (@ResultO-mk-ok-UTCDateTime (@ResultO-UTCDateTime-val @IdealDateTime)) (@ResultO-mk-err-UTCDateTime (@ResultO-UTCDateTime-err @ErrorKind)) )
        ( (@ResultO-mk-ok-PlainDate (@ResultO-PlainDate-val @IdealDateTime)) (@ResultO-mk-err-PlainDate (@ResultO-PlainDate-err @ErrorKind)) )
        ( (@ResultO-mk-ok-PlainTime (@ResultO-PlainTime-val @IdealDateTime)) (@ResultO-mk-err-PlainTime (@ResultO-PlainTime-err @ErrorKind)) )
        ( (@ResultO-mk-ok-TickTime (@ResultO-TickTime-val Int)) (@ResultO-mk-err-TickTime (@ResultO-TickTime-err @ErrorKind)) )
        ( (@ResultO-mk-ok-LogicalTime (@ResultO-LogicalTime-val Int)) (@ResultO-mk-err-LogicalTime (@ResultO-LogicalTime-err @ErrorKind)) )
        ( (@ResultO-mk-ok-ISOTimeStamp (@ResultO-ISOTimeStamp-val @IdealDateTime)) (@ResultO-mk-err-ISOTimeStamp (@ResultO-ISOTimeStamp-err @ErrorKind)) )
        ( (@ResultO-mk-ok-UUIDv4 (@ResultO-UUIDv4-val String)) (@ResultO-mk-err-UUIDv4 (@ResultO-UUIDv4-err @ErrorKind)) )
        ( (@ResultO-mk-ok-UUIDv7 (@ResultO-UUIDv7-val String)) (@ResultO-mk-err-UUIDv7 (@ResultO-UUIDv7-err @ErrorKind)) )
        ( (@ResultO-mk-ok-SHAContentHash (@ResultO-SHAContentHash-val (_ BitVec 16))) (@ResultO-mk-err-SHAContentHash (@ResultO-SHAContentHash-err @ErrorKind)) )
        ( (@ResultO-mk-ok-Regex (@ResultO-Regex-val String)) (@ResultO-mk-err-Regex (@ResultO-Regex-err @ErrorKind)) )
        ;;--RESULT_O_CONSTRUCTORS--;;
    )
)

;;
;; ResultT datatypes 
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
