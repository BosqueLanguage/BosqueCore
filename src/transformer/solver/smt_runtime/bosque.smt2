;;
;;Template file for building SMTLIB models of Bosque code
;;

;;;;;
;;Utilities
;;;;;

;;
;;Error kinds that we propagate in results
;;;
(declare-sort @ErrorKind)
(declare-const @error-target @ErrorKind)
(declare-const @error-other @ErrorKind)
(declare-const @error-resource @ErrorKind)

;;Make sure they are all different values
(assert (distinct @error-target @error-other @error-resource))

;;@Result datatypes
(declare-datatypes 
    (
        (@ResultT 1)
        (@ResultO 1)
    ) 
    (
        (par (T) (
            (@ResultT-mk-err (@ResultT-error @ErrorKind))
            (@ResultT-mk-ok (@ResultT-value T))
        ))
        (par (T) (
            (@ResultO-mk-err (@ResulO-error @ErrorKind))
            (@ResultO-mk-ok (@ResultO-value T))
        ))
    )
)

;;
;;Support for numerics
;;

(declare-sort @Float)
(declare-sort @Decimal)
(declare-sort @Rational)

(declare-fun @Float_uninterp (String) @Float)
(declare-fun @Decimal_uninterp (String) @Decimal)
(declare-fun @Rational_uninterp (String) @Rational)

(declare-const @Float_0 @Float) (assert (= @Float_0 (@Float_uninterp "0.0")))
(declare-const @Decimal_0 @Decimal) (assert (= @Decimal_0 (@Decimal_uninterp "0.0")))
(declare-const @Rational_0 @Rational) (assert (= @Rational_0 (@Rational_uninterp "0")))

;;TODO: maybe want to have template for all FP constants and declare distinct

(declare-fun @Float_negate (@Float) @Float)
(declare-fun @Float_add (@Float @Float) @Float)
(declare-fun @Float_sub (@Float @Float) @Float)
(declare-fun @Float_mult (@Float @Float) @Float)
(declare-fun @Float_div (@Float @Float) @Float)

(declare-fun @Decimal_unary (@Decimal) @Decimal)
(declare-fun @Decimal_add (@Decimal @Decimal) @Decimal)
(declare-fun @Decimal_sub (@Decimal @Decimal) @Decimal)
(declare-fun @Decimal_mult (@Decimal @Decimal) @Decimal)
(declare-fun @Decimal_div (@Decimal @Decimal) @Decimal)

(declare-fun @Rational_unary (@Rational) @Rational)
(declare-fun @Rational_add (@Rational @Rational) @Rational)
(declare-fun @Rational_sub (@Rational @Rational) @Rational)
(declare-fun @Rational_mult (@Rational @Rational) @Rational)
(declare-fun @Rational_div (@Rational @Rational) @Rational)

(define-fun @Float_lteq ((x @Float) (y @Float)) Bool ((_ linear-order 0) x y))
(define-fun @Float_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Float_lteq x y)))

(define-fun @Decimal_lteq ((x @Decimal) (y @Decimal)) Bool ((_ linear-order 0) x y))
(define-fun @Decimal_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Decimal_lteq x y)))

(define-fun @Rational_lteq ((x @Rational) (y @Rational)) Bool ((_ linear-order 0) x y))
(define-fun @Rational_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Rational_lteq x y)))

;;NLA options
(declare-fun @Nat_mult (@Nat @Nat) @Nat)
(declare-fun @Nat_div (@Nat @Nat) @Nat)

(declare-fun @Int_mult (@Int @Int) @Int)
(declare-fun @Int_div (@Int @Int) @Int)

(declare-fun @BigNat_mult (@BigNat @BigNat) @BigNat)
(declare-fun @BigNat_div (@BigNat @BigNat) @BigNat)

(declare-fun @BigInt_mult (@BigInt @BigInt) @BigInt)
(declare-fun @BigInt_div (@BigInt @BigInt) @BigInt)

;;Checked arith operations

(define-fun @Nat_checked_trgt_sub ((x Int) (y Int)) (@ResultT Int) 
    (ite (<= y x) (@ResultT-mk-ok (- x y)) (@ResultT-mk-err @error-target))
)

(define-fun @Nat_checked_sub ((x Int) (y Int)) (@ResultO Int) 
    (ite (<= y x) (@ResultO-mk-ok (- x y)) (@ResultO-mk-err @error-target))
)

(define-fun @BigNat_checked_trgt_sub ((x Int) (y Int)) (@ResultT Int) 
    (ite (<= y x) (@ResultT-mk-ok (- x y)) (@ResultT-mk-err @error-target))
)

(define-fun @BigNat_checked_sub ((x Int) (y Int)) (@ResultO Int) 
    (ite (<= y x) (@ResultO-mk-ok (- x y)) (@ResultO-mk-err @error-target))
)

(define-fun @Nat_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@Nat_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @Nat_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@Nat_div x y)) (@ResultO-mk-err @error-target))
)

(define-fun @BigNat_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@BigNat_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @BigNat_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@BigNat_div x y)) (@ResultO-mk-err @error-target))
)

(define-fun @Int_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@Int_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @Int_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@Int_div x y)) (@ResultO-mk-err @error-target))
)

(define-fun @BigInt_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@BigInt_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @BigInt_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@BigInt_div x y)) (@ResultO-mk-err @error-target))
)

;;
;; Primitive datatypes 
;;
(declare-datatypes (
    (@None 0)
    (@Nothing 0)
    ;;STRUCTURAL_DECLS;;
    ;;OO_DECLS;;
    ; Bool -> Bool
    ; Int -> Int
    ; Nat -> Int
    ; BigInt -> Int
    ; BigNat -> Int
    ; Float -> @Float 
    ; Decimal -> @Decimal
    ; Rational -> @Rational
    ; String -> String
    ; ByteBuffer -> @ByteBuffer
    ; DateTime -> @DateTime
    ; UTCDateTime -> @UTCDateTime
    ; PlainDate -> @PlainDate
    ; PlainTime -> @PlainTime
    ; TickTime -> Int
    ; LogicalTime -> Int
    ; ISOTimeStamp -> @ISOTimeStamp
    ; UUID4 -> String
    ; UUID7 -> String
    ; SHAContentHash -> String
    ; LatLongCoordinate -> @LatLongCoordinate
    ) (
        ( (@none) ) 
        ( (@nothing) )
        ;;STRUCTURAL_CONSTRUCTORS;;
        ;;OO_CONSTRUCTORS;;
    )
)