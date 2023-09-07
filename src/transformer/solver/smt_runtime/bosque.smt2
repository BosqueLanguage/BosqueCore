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
(declare-const @error-validate @ErrorKind)

;;Make sure they are all different values
(assert (distinct @error-target @error-other @error-resource @error-validate))

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


;;@INT_MIN, @INT_MAX, @NAT_MAX, @SLEN_MAX, @BLEN_MAX, @CSIZE_MAX
;;--V_MIN_MAX--;;

;;
;;Type tag decls and orders
;;
(declare-sort @KeyTypeTag)
(declare-const @KeyTypeTag-NA @KeyTypeTag)
(declare-const @KeyTypeTag-None @KeyTypeTag)
(declare-const @KeyTypeTag-Bool @KeyTypeTag)
(declare-const @KeyTypeTag-Nat @KeyTypeTag)
(declare-const @KeyTypeTag-Int @KeyTypeTag)
(declare-const @KeyTypeTag-BigNat @KeyTypeTag)
(declare-const @KeyTypeTag-BigInt @KeyTypeTag)
(declare-const @KeyTypeTag-String @KeyTypeTag)
(declare-const @KeyTypeTag-ASCIIString @KeyTypeTag)
(declare-const @KeyTypeTag-UTCDateTime @KeyTypeTag)
(declare-const @KeyTypeTag-PlainDate @KeyTypeTag)
(declare-const @KeyTypeTag-PlainTime @KeyTypeTag)
(declare-const @KeyTypeTag-TickTime @KeyTypeTag)
(declare-const @KeyTypeTag-LogicalTime @KeyTypeTag)
(declare-const @KeyTypeTag-ISOTimeStamp @KeyTypeTag)
(declare-const @KeyTypeTag-UUIDv4 @KeyTypeTag)
(declare-const @KeyTypeTag-UUIDv7 @KeyTypeTag)
(declare-const @KeyTypeTag-SHAContentHash @KeyTypeTag)
;;--KEY_TYPE_TAG_DECLS--;;

(assert 
    (distinct 
        @KeyTypeTag-NA
        @KeyTypeTag-None @KeyTypeTag-Bool 
        @KeyTypeTag-Nat @KeyTypeTag-Int @KeyTypeTag-BigNat @KeyTypeTag-BigInt 
        @KeyTypeTag-String @KeyTypeTag-ASCIIString
        @KeyTypeTag-UTCDateTime @KeyTypeTag-PlainDate @KeyTypeTag-PlainTime @KeyTypeTag-TickTime @KeyTypeTag-LogicalTime @KeyTypeTag-ISOTimeStamp 
        @KeyTypeTag-UUIDv4 @KeyTypeTag-UUIDv7 @KeyTypeTag-SHAContentHash
        ;;--KEY_TYPE_TAG_DISTINCTS--;;
    )
)

(define-fun @key_type_sort_order ((x @KeyTypeTag) (y @KeyTypeTag)) Bool ((_ linear-order 0) x y))
(assert (@key_type_sort_order @KeyTypeTag-None @KeyTypeTag-Bool))
(assert (@key_type_sort_order @KeyTypeTag-Bool @KeyTypeTag-Nat))
(assert (@key_type_sort_order @KeyTypeTag-Nat @KeyTypeTag-Int))
(assert (@key_type_sort_order @KeyTypeTag-Int @KeyTypeTag-BigNat))
(assert (@key_type_sort_order @KeyTypeTag-BigNat @KeyTypeTag-BigInt))
(assert (@key_type_sort_order @KeyTypeTag-BigInt @KeyTypeTag-String))
(assert (@Key_type_sort_order @KeyTypeTag-String @KeyTypeTag-ASCIIString))
(assert (@key_type_sort_order @KeyTypeTag-ASCIIString @KeyTypeTag-UTCDateTime))
(assert (@key_type_sort_order @KeyTypeTag-UTCDateTime @KeyTypeTag-PlainDate))
(assert (@key_type_sort_order @KeyTypeTag-PlainDate @KeyTypeTag-PlainTime))
(assert (@key_type_sort_order @KeyTypeTag-PlainTime @KeyTypeTag-TickTime))
(assert (@key_type_sort_order @KeyTypeTag-TickTime @KeyTypeTag-LogicalTime))
(assert (@key_type_sort_order @KeyTypeTag-LogicalTime @KeyTypeTag-ISOTimeStamp))
(assert (@key_type_sort_order @KeyTypeTag-ISOTimeStamp @KeyTypeTag-UUIDv4))
(assert (@key_type_sort_order @KeyTypeTag-UUIDv4 @KeyTypeTag-UUIDv7))
(assert (@key_type_sort_order @KeyTypeTag-UUIDv7 @KeyTypeTag-SHAContentHash))
;;--KEY_TYPE_TAG_SORT--;;

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

(define-fun @Float_lteq ((x @Float) (y @Float)) Bool ((_ linear-order 1) x y))
(define-fun @Float_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Float_lteq x y)))

(define-fun @Decimal_lteq ((x @Decimal) (y @Decimal)) Bool ((_ linear-order 2) x y))
(define-fun @Decimal_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Decimal_lteq x y)))

(define-fun @Rational_lteq ((x @Rational) (y @Rational)) Bool ((_ linear-order 3) x y))
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
    (ite (<= y x) (@ResultO-mk-ok (- x y)) (@ResultO-mk-err @error-other))
)

(define-fun @BigNat_checked_trgt_sub ((x Int) (y Int)) (@ResultT Int) 
    (ite (<= y x) (@ResultT-mk-ok (- x y)) (@ResultT-mk-err @error-target))
)

(define-fun @BigNat_checked_sub ((x Int) (y Int)) (@ResultO Int) 
    (ite (<= y x) (@ResultO-mk-ok (- x y)) (@ResultO-mk-err @error-other))
)

(define-fun @Nat_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@Nat_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @Nat_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@Nat_div x y)) (@ResultO-mk-err @error-other))
)

(define-fun @BigNat_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@BigNat_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @BigNat_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@BigNat_div x y)) (@ResultO-mk-err @error-other))
)

(define-fun @Int_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@Int_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @Int_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@Int_div x y)) (@ResultO-mk-err @error-other))
)

(define-fun @BigInt_checked_trgt_div ((x Int) (y Int)) (@ResultT Int) 
    (ite (= y 0) (@ResultT-mk-ok (@BigInt_div x y)) (@ResultT-mk-err @error-target))
)

(define-fun @BigInt_checked_div ((x Int) (y Int)) (@ResultO Int) 
    (ite (= y 0) (@ResultO-mk-ok (@BigInt_div x y)) (@ResultO-mk-err @error-other))
)

(declare-datatype @IdealDateTime 
    (
        (@IdealDateTime-mk (@IdealDateTime-year Int) (@IdealDateTime-month Int) (@IdealDateTime-day Int) (@IdealDateTime-hour Int) (@IdealDateTime-min Int) (@IdealDateTime-sec Int) (@IdealDateTime-msec Int) (@IdealDateTime-tzdata String))
    )
)

(declare-const @IdealDateTime-UTC String)
(assert (= @IdealDateTime-UTC "UTC"))

(define-fun @IdealDateTime_less ((k1 @IdealDateTime ) (k2 @IdealDateTime)) Bool
    (ite (not (= (@IdealDateTime-year k1) (@IdealDateTime-year k2)))
        (< (@IdealDateTime-year k1) (@IdealDateTime-year k2))
        (ite (not (= (@IdealDateTime-month k1) (@IdealDateTime-month k2)))
            (< (@IdealDateTime-month k1) (@IdealDateTime-month k2))
            (ite (not (= (@IdealDateTime-day k1) (@IdealDateTime-day k2)))
                (< (@IdealDateTime-day k1) (@IdealDateTime-day k2))
                (ite (not (= (@IdealDateTime-hour k1) (@IdealDateTime-hour k2)))
                    (< (@IdealDateTime-hour k1) (@IdealDateTime-hour k2))
                    (ite (not (= (@IdealDateTime-min k1) (@IdealDateTime-min k2)))
                        (< (@IdealDateTime-min k1) (@IdealDateTime-min k2))
                        (ite (not (= (@IdealDateTime-sec k1) (@IdealDateTime-sec k2)))
                            (< (@IdealDateTime-sec k1) (@IdealDateTime-sec k2))
                            (ite (not (= (@IdealDateTime-msec k1) (@IdealDateTime-msec k2)))
                                (< (@IdealDateTime-msec k1) (@IdealDateTime-msec k2))
                                (< (@IdealDateTime-tzdata k1) (@IdealDateTime-tzdata k2))
                            )
                        )
                    )
                )
            )
        )
    )
)

;;
;; Primitive datatypes 
;;
(declare-datatypes (
    (None 0)
    (Nothing 0)
    ; Bool -> Bool
    ; Int -> Int
    ; Nat -> Int
    ; BigInt -> Int
    ; BigNat -> Int
    ; Float -> @Float 
    ; Decimal -> @Decimal
    ; Rational -> @Rational
    ; String -> String
    ; ASCIIString -> String
    ; (Seq (_ BitVec 8))
    ; DateTime -> @IdealDateTime 
    ; UTCDateTime -> @IdealDateTime 
    ; PlainDate -> @IdealDateTime 
    ; PlainTime -> @IdealDateTime 
    ; TickTime -> Int
    ; LogicalTime -> Int
    ; ISOTimeStamp -> @IdealDateTime 
    ; UUIDv4 -> String
    ; UUIDv7 -> String
    ; SHAContentHash -> (_ BitVec 16)
    (LatLongCoordinate 0)
    ; Regex -> String
    ;;--OO_DECLS--;;
    ) (
        ( (none) ) 
        ( (nothing) )
        ( (LatLongCoordinate@mk (LatLongCoordinate-lat @Float) (LatLongCoordinate-long @Float)) )
        ;;--OO_CONSTRUCTORS--;;
    )
)

(declare-datatype @BoxedKeyValue
    (
        (@BoxedKeyValue-mk-NA)
        (@BoxedKeyValue-mk-None)
        (@BoxedKeyValue-mk-Bool (@BoxedKeyValue-Bool Bool))
        (@BoxedKeyValue-mk-Int (@BoxedKeyValue-Int Int))
        (@BoxedKeyValue-mk-String (@BoxedKeyValue-String String))
        (@BoxedKeyValue-mk-SHAContentHash (@BoxedKeyValue-SHAContentHash (_ BitVec 16)))
        (@BoxedKeyValue-mk-IdealDateTime (@BoxedKeyValue-IdealDateTime @IdealDateTime))
    )
)

(declare-datatype @BoxedKey 
    (
        (@BoxedKey-mk-NA)
        (@BoxedKey-mk-of (@BoxedKey-tag @KeyTypeTag) (@BoxedKey-value @BoxedKeyValue))
    )
)
(define-fun @BoxedKey-get-tag ((k @BoxedKey)) @KeyTypeTag (ite ((_ is @BoxedKey-mk-of) k) (@BoxedKey-tag k) @KeyTypeTag-NA))
(define-fun @BoxedKey-get-value ((k @BoxedKey)) @BoxedKeyValue (ite ((_ is @BoxedKey-mk-of) k) (@BoxedKey-value k) @BoxedKeyValue-mk-NA))

(declare-datatype @BoxedData 
    (
        (@BoxedData-mk-None)
        (@BoxedData-mk-Nothing)
        (@BoxedData-mk-Bool (@BoxedData-Bool Bool))
        (@BoxedData-mk-Int (@BoxedData-Int Int))
        (@BoxedData-mk-Nat (@BoxedData-Nat Int))
        (@BoxedData-mk-BigInt (@BoxedData-BigInt Int))
        (@BoxedData-mk-BigNat (@BoxedData-BigNat Int))
        (@BoxedData-mk-Float (@BoxedData-Float @Float))
        (@BoxedData-mk-Decimal (@BoxedData-Decimal @Decimal))
        (@BoxedData-mk-Rational (@BoxedData-Rational @Rational))
        (@BoxedData-mk-String (@BoxedData-String String))
        (@BoxedData-mk-ASCIIString (@BoxedData-ASCIIString String))
        (@BoxedData-mk-ByteBuffer (@BoxedData-ByteBuffer (Seq (_ BitVec 8))))
        (@BoxedData-mk-DateTime (@BoxedData-DateTime @IdealDateTime))
        (@BoxedData-mk-UTCDateTime (@BoxedData-UTCDateTime @IdealDateTime))
        (@BoxedData-mk-PlainDate (@BoxedData-PlainDate @IdealDateTime))
        (@BoxedData-mk-PlainTime (@BoxedData-PlainTime @IdealDateTime))
        (@BoxedData-mk-TickTime (@BoxedData-TickTime Int))
        (@BoxedData-mk-LogicalTime (@BoxedData-LogicalTime Int))
        (@BoxedData-mk-ISOTimeStamp (@BoxedData-ISOTimeStamp @IdealDateTime))
        (@BoxedData-mk-UUIDv4 (@BoxedData-UUIDv4 String))
        (@BoxedData-mk-UUIDv7 (@BoxedData-UUIDv7 String))
        (@BoxedData-mk-SHAContentHash (@BoxedData-SHAContentHash (_ BitVec 16)))
        (@BoxedData-mk-LatLongCoordinate (@BoxedData-LatLongCoordinate @LatLongCoordinate))
        (@BoxedData-mk-Regex (@BoxedData-Regex String))
        ;;--TYPE_BOX_CONSTRUCTORS--;;
    )
)

;;
;; Boxed datatypes 
;;
(declare-datatype @Term
    (
        (@Term-mk (@Term-data @BoxedData) (@Term-key @BoxedKey))
    )
)

(define-fun @Term-box-None ((v None)) @Term (@Term-mk @BoxedData-mk-None (@BoxedKey-mk-of @KeyTypeTag-None @BoxedKeyValue-mk-None)))
(define-fun @Term-box-Nothing ((v Nothing)) @Term (@Term-mk @BoxedData-mk-Nothing @BoxedKey-mk-NA))
(define-fun @Term-box-Bool ((v Bool)) @Term (@Term-mk (@BoxedData-mk-Bool v) (@BoxedKey-mk-of @KeyTypeTag-Bool (@BoxedKeyValue-mk-Bool v))))
(define-fun @Term-box-Int ((v Int)) @Term (@Term-mk (@BoxedData-mk-Int v) (@BoxedKey-mk-of @KeyTypeTag-Int (@BoxedKeyValue-mk-Int v))))
(define-fun @Term-box-Nat ((v Int)) @Term (@Term-mk (@BoxedData-mk-Nat v) (@BoxedKey-mk-of @KeyTypeTag-Nat (@BoxedKeyValue-mk-Int v))))
(define-fun @Term-box-BigInt ((v Int)) @Term (@Term-mk (@BoxedData-mk-BigInt v) (@BoxedKey-mk-of @KeyTypeTag-BigInt (@BoxedKeyValue-mk-Int v))))
(define-fun @Term-box-BigNat ((v Int)) @Term (@Term-mk (@BoxedData-mk-BigNat v) (@BoxedKey-mk-of @KeyTypeTag-BigNat (@BoxedKeyValue-mk-Int v))))
(define-fun @Term-box-Float ((v @Float)) @Term (@Term-mk (@BoxedData-mk-Float v) @BoxedKey-mk-NA))
(define-fun @Term-box-Decimal ((v @Decimal)) @Term (@Term-mk (@BoxedData-mk-Decimal v) @BoxedKey-mk-NA))
(define-fun @Term-box-Rational ((v @Rational)) @Term (@Term-mk (@BoxedData-mk-Rational v) @BoxedKey-mk-NA))
(define-fun @Term-box-String ((v String)) @Term (@Term-mk (@BoxedData-mk-String v) (@BoxedKey-mk-of @KeyTypeTag-String (@BoxedKeyValue-mk-String v))))
(define-fun @Term-box-ASCIIString ((v String)) @Term (@Term-mk (@BoxedData-mk-ASCIIString v) (@BoxedKey-mk-of @KeyTypeTag-ASCIIString (@BoxedKeyValue-mk-String v))))
(define-fun @Term-box-ByteBuffer ((v (Seq (_ BitVec 8)))) @Term (@Term-mk (@BoxedData-mk-ByteBuffer v) @BoxedKey-mk-NA))
(define-fun @Term-box-DateTime ((v @IdealDateTime)) @Term (@Term-mk (@BoxedData-mk-DateTime v) @BoxedKey-mk-NA))
(define-fun @Term-box-UTCDateTime ((v @IdealDateTime)) @Term (@Term-mk (@BoxedData-mk-UTCDateTime v) (@BoxedKey-mk-of @KeyTypeTag-UTCDateTime (@BoxedKeyValue-mk-IdealDateTime v))))
(define-fun @Term-box-PlainDate ((v @IdealDateTime)) @Term (@Term-mk (@BoxedData-mk-PlainDate v) (@BoxedKey-mk-of @KeyTypeTag-PlainDate (@BoxedKeyValue-mk-IdealDateTime v))))
(define-fun @Term-box-PlainTime ((v @IdealDateTime)) @Term (@Term-mk (@BoxedData-mk-PlainTime v) (@BoxedKey-mk-of @KeyTypeTag-PlainTime (@BoxedKeyValue-mk-IdealDateTime v))))
(define-fun @Term-box-TickTime ((v Int)) @Term (@Term-mk (@BoxedData-mk-TickTime v) (@BoxedKey-mk-of @KeyTypeTag-TickTime (@BoxedKeyValue-mk-Int v))))
(define-fun @Term-box-LogicalTime ((v Int)) @Term (@Term-mk (@BoxedData-mk-LogicalTime v) (@BoxedKey-mk-of @KeyTypeTag-LogicalTime (@BoxedKeyValue-mk-Int v))))
(define-fun @Term-box-ISOTimeStamp ((v @IdealDateTime)) @Term (@Term-mk (@BoxedData-mk-ISOTimeStamp v) (@BoxedKey-mk-of @KeyTypeTag-ISOTimeStamp (@BoxedKeyValue-mk-IdealDateTime v))))
(define-fun @Term-box-UUIDv4 ((v String)) @Term (@Term-mk (@BoxedData-mk-UUIDv4 v) (@BoxedKey-mk-of @KeyTypeTag-UUIDv4 (@BoxedKeyValue-mk-String v))))
(define-fun @Term-box-UUIDv7 ((v String)) @Term (@Term-mk (@BoxedData-mk-UUIDv7 v) (@BoxedKey-mk-of @KeyTypeTag-UUIDv7 (@BoxedKeyValue-mk-String v))))
(define-fun @Term-box-SHAContentHash ((v (_ BitVec 16))) @Term (@Term-mk (@BoxedData-mk-SHAContentHash v) (@BoxedKey-mk-of @KeyTypeTag-SHAContentHash (@BoxedKeyValue-mk-SHAContentHash v))))
(define-fun @Term-box-LatLongCoordinate ((v LatLongCoordinate)) @Term (@Term-mk (@BoxedData-mk-LatLongCoordinate v) @BoxedKey-mk-NA))
(define-fun @Term-box-Regex ((v String)) @Term (@Term-mk (@BoxedData-mk-Regex v) @BoxedKey-mk-NA))
;;--TERM_BOX_CONSTRUCTORS--;;

(define-fun @Term-unbox-None ((t @Term)) None none)
(define-fun @Term-unbox-Nothing ((t @Term)) Nothing nothing)
(define-fun @Term-unbox-Bool ((t @Term)) Bool (@BoxedData-Bool (@Term-data t)))
(define-fun @Term-unbox-Int ((t @Term)) Int (@BoxedData-Int (@Term-data t)))
(define-fun @Term-unbox-Nat ((t @Term)) Int (@BoxedData-Nat (@Term-data t)))
(define-fun @Term-unbox-BigInt ((t @Term)) Int (@BoxedData-BigInt (@Term-data t)))
(define-fun @Term-unbox-BigNat ((t @Term)) Int (@BoxedData-BigNat (@Term-data t)))
(define-fun @Term-unbox-Float ((t @Term)) @Float (@BoxedData-Float (@Term-data t)))
(define-fun @Term-unbox-Decimal ((t @Term)) @Decimal (@BoxedData-Decimal (@Term-data t)))
(define-fun @Term-unbox-Rational ((t @Term)) @Rational (@BoxedData-Rational (@Term-data t)))
(define-fun @Term-unbox-String ((t @Term)) String (@BoxedData-String (@Term-data t)))
(define-fun @Term-unbox-ASCIIString ((t @Term)) String (@BoxedData-ASCIIString (@Term-data t)))
(define-fun @Term-unbox-ByteBuffer ((t @Term)) (Seq (_ BitVec 8)) (@BoxedData-ByteBuffer (@Term-data t)))
(define-fun @Term-unbox-DateTime ((t @Term)) @IdealDateTime (@BoxedData-DateTime (@Term-data t)))
(define-fun @Term-unbox-UTCDateTime ((t @Term)) @IdealDateTime (@BoxedData-UTCDateTime (@Term-data t)))
(define-fun @Term-unbox-PlainDate ((t @Term)) @IdealDateTime (@BoxedData-PlainDate (@Term-data t)))
(define-fun @Term-unbox-PlainTime ((t @Term)) @IdealDateTime (@BoxedData-PlainTime (@Term-data t)))
(define-fun @Term-unbox-TickTime ((t @Term)) Int (@BoxedData-TickTime (@Term-data t)))
(define-fun @Term-unbox-LogicalTime ((t @Term)) Int (@BoxedData-LogicalTime (@Term-data t)))
(define-fun @Term-unbox-ISOTimeStamp ((t @Term)) @IdealDateTime (@BoxedData-ISOTimeStamp (@Term-data t)))
(define-fun @Term-unbox-UUIDv4 ((t @Term)) String (@BoxedData-UUIDv4 (@Term-data t)))
(define-fun @Term-unbox-UUIDv7 ((t @Term)) String (@BoxedData-UUIDv7 (@Term-data t)))
(define-fun @Term-unbox-SHAContentHash ((t @Term)) (_ BitVec 16) (@BoxedData-SHAContentHash (@Term-data t)))
(define-fun @Term-unbox-LatLongCoordinate ((t @Term)) LatLongCoordinate (@BoxedData-LatLongCoordinate (@Term-data t)))
(define-fun @Term-unbox-Regex ((t @Term)) String (@BoxedData-Regex (@Term-data t)))
;;--TERM_BOX_UNBOXERS--;;

(define-fun @keyless ((k1 @Term) (k2 @Term)) Bool 
    (let ((tk1 (@BoxedKey-get-tag (@Term-key k1))) (tk2 (@BoxedKey-get-tag (@Term-key k2))))
    (ite (not (= tk1 tk2))
        (@key_type_sort_order tk1 tk2)
        (let ((vv1 (@BoxedKey-get-value (@Term-key k1))) (vv2 (@BoxedKey-get-value (@Term-key k2))))
        (ite (and (= vv1 @BoxedKeyValue-mk-none) (= vv2 @BoxedKeyValue-mk-none))
            false
            (ite (and ((_ is @BoxedKeyValue-mk-Bool) vv1) ((_ is @BoxedKeyValue-mk-Bool) vv2))
                (and (not (@BoxedKeyValue-Bool vv1)) (@BoxedKeyValue-Bool vv2))
                (ite (and ((_ is @BoxedKeyValue-mk-Int) vv1) ((_ is @BoxedKeyValue-mk-Int) vv2))
                    (< (@BoxedKeyValue-Int vv1) (@BoxedKeyValue-Int vv2))
                    (ite (and ((_ is @BoxedKeyValue-mk-String) vv1) ((_ is @BoxedKeyValue-mk-String) vv2))
                        (str.< (@BoxedKeyValue-String vv1) (@BoxedKeyValue-String vv2))
                        (ite (and ((_ is @BoxedKeyValue-mk-SHAContentHash) vv1) ((_ is @BoxedKeyValue-mk-SHAContentHash) vv2))
                            (bvult (@BoxedKeyValue-SHAContentHash vv1) (@BoxedKeyValue-SHAContentHash vv2))
                            (ite (and ((_ is @BoxedKeyValue-mk-IdealDateTime) vv1) ((_ is @BoxedKeyValue-mk-IdealDateTime) vv2))
                                (@IdealDateTime_less (@BoxedKey-IdealDateTime vv1) (@BoxedKey-IdealDateTime vv2)) 
                                false
                            )
                        )
                    )
                )
            )
        ))
    ))
)

;;--TYPE_SUBTYPE--;;


;;
;; Value extraction and binding
;;

(declare-fun @Bool_UFCons_API ((Seq Int)) Bool)
(declare-fun @Nat_UFCons_API ((Seq Int)) Int)
(declare-fun @Int_UFCons_API ((Seq Int)) Int)
(declare-fun @BigInt_UFCons_API ((Seq Int)) Int)
(declare-fun @BigNat_UFCons_API ((Seq Int)) Int)
(declare-fun @Float_UFCons_API ((Seq Int)) @Float)
(declare-fun @Decimal_UFCons_API ((Seq Int)) @Decimal)
(declare-fun @Rational_UFCons_API ((Seq Int)) @Rational)
(declare-fun @String_UFCons_API ((Seq Int)) String)
(declare-fun @ASCIIString_UFCons_API ((Seq Int)) String)
(declare-fun @ByteBuffer_UFCons_API ((Seq Int)) (Seq (_ BitVec 8)))
(declare-fun @IdealDateYear_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateMonth_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateDay_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateHour_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateMinute_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateSecond_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateMillis_UFCons_API ((Seq Int)) Int)
(declare-fun @IdealDateTZName_UFCons_API ((Seq Int)) String)
(declare-fun @TickTime_UFCons_API ((Seq Int)) Int)
(declare-fun @LogicalTime_UFCons_API ((Seq Int)) Int)
(declare-fun @UUIDv4_UFCons_API ((Seq Int)) String)
(declare-fun @UUIDv7_UFCons_API ((Seq Int)) String)
(declare-fun @SHAContentHash_UFCons_API ((Seq Int)) (_ BitVec 16))
(declare-fun @Latitude_UFCons_API ((Seq Int)) @Float)
(declare-fun @Longitude_UFCons_API ((Seq Int)) @Float)
(declare-fun @ContainerSize_UFCons_API ((Seq Int)) Int)
(declare-fun @Enum_UFCons_API ((Seq Int)) Int)
(declare-fun @TypeChoice_UFCons_API ((Seq Int)) Int)

(define-fun @entrypoint_cons_None ((ctx (Seq Int))) (@ResultO None)
    (@ResultO-mk-ok none)
)

(define-fun @entrypoint_cons_Nothing ((ctx (Seq Int))) (@ResultO Nothing)
    (@ResultO-mk-ok nothing)
)

(define-fun @entrypoint_cons_Bool ((ctx (Seq Int))) (@ResultO Bool)
    (@ResultO-mk-ok (@Bool_UFCons_API ctx))
)

(define-fun @entrypoint_cons_Nat ((ctx (Seq Int))) (@ResultO Int)
    (let ((iv (@Nat_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv @INT_MAX))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_Int ((ctx (Seq Int))) (@ResultO Int)
    (let ((iv (@Int_UFCons_API ctx)))
    (ite (and (<= @INT_MIN iv) (<= iv @INT_MAX))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_BigNat ((ctx (Seq Int))) (@ResultO Int)
    (let ((iv (@BigNat_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_BigInt ((ctx (Seq Int))) (@ResultO Int)
    (let ((iv (@BigInt_UFCons_API ctx)))
    (ite (and (<= (+ @INT_MIN @INT_MIN) iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_Float ((ctx (Seq Int))) (@ResultO @Float)
    (@ResultO-mk-ok (@Float_UFCons_API ctx))
)

(define-fun @entrypoint_cons_Decimal ((ctx (Seq Int))) (@ResultO @Decimal)
    (@ResultO-mk-ok (@Decimal_UFCons_API ctx))
)

(define-fun @entrypoint_cons_Rational ((ctx (Seq Int))) (@ResultO @Rational)
    (@ResultO-mk-ok (@Rational_UFCons_API ctx))
)

(define-fun _@@cons_String_entrypoint ((ctx (Seq Int))) (@ResultO String)
    (let ((sv (@String_UFCons_API ctx)))
    (ite (<= (str.len sv) @SLEN_MAX)
        (@ResultO-mk-ok sv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_ByteBuffer ((ctx (Seq Int))) (@ResultO (Seq (_ BitVec 8)))
    (let ((compress (@Enum_UFCons_API (seq.++ ctx (seq.unit 0)))) (format (@Enum_UFCons_API (seq.++ ctx (seq.unit 1)))) (buff (@ByteBuffer_UFCons_API ctx)))
    (ite (and (< compress 2) (< format 4) (<= (seq.len buff) @BLEN_MAX))
        (@ResultO-mk-ok (@ByteBuffer-mk buff compress format))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @isLeapYear ((y Int)) Bool
    (ite (or (= y 1900) (= y 2100) (= y 2200))
        false
        (= (mod y 4) 0)
    )
)

(define-fun @check_DayInMonth ((d Int) (m Int) (y Int)) Bool
    (ite (= m 1)
        (ite (@isLeapYear y) (<= d 29) (<= d 28))
        (ite (or (= m 3) (= m 5) (= m 8) (= m 10)) (<= d 30) (<= d 31))
    )
)

(define-fun @istzname ((tzname String)) Bool
    (str.in.re tzname ((_ re.loop 3 3) (re.range "A" "Z")))
)

(define-fun @entrypoint_cons_DateTime ((ctx (Seq Int))) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)) (hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)) (tzinfo (@IdealDateTZName_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 59) (<= 0 millis) (<= millis 999) (@istzname tzinfo))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh mm ss millis tzinfo))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_UTCDateTime ((ctx (Seq Int))) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)) (hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 59) (<= 0 millis) (<= millis 999))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh mm ss millis @IdealDateTime-UTC))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_PlainDate ((ctx (Seq Int))) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh 0 0 0 @IdealDateTime-UTC))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_PlainTime ((ctx (Seq Int))) (@ResultO @IdealDateTime)
    (let ((hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)))
    (ite (and (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 59) (<= 0 millis) (<= millis 999))
        (@ResultO-mk-ok (@IdealDateTime-mk 0 0 0 hh mm ss millis @IdealDateTime-UTC))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_TickTime ((ctx (Seq Int))) (@ResultO Int)
    (let ((iv (@TickTime_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_LogicalTime ((ctx (Seq Int))) (@ResultO Int)
    (let ((iv (@LogicalTime_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_ISOTimeStamp ((ctx (Seq Int))) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)) (hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)) (tzinfo (@IdealDateTZName_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 60) (<= 0 millis) (<= millis 999) (@istzname tzinfo))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh mm ss millis tzinfo))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @isUUIDFormat ((uuid String)) Bool
    (str.in.re uuid 
        (re.++
            (re.loop (re.union (re.range "0" "9") (re.range "A" "F")) 8 8)
            (str.to.re "-")
            (re.loop (re.union (re.range "0" "9") (re.range "A" "F")) 4 4)
            (str.to.re "-")
            (re.loop (re.union (re.range "0" "9") (re.range "A" "F")) 4 4)
            (str.to.re "-")
            (re.loop (re.union (re.range "0" "9") (re.range "A" "F")) 4 4)
            (str.to.re "-")
            (re.loop (re.union (re.range "0" "9") (re.range "A" "F")) 12 12)
        )
    )
)

(define-fun @entrypoint_cons_UUIDv4 ((ctx (Seq Int))) (@ResultO String)
    (let ((uuv (@UUIDv4_UFCons_API ctx)))
    (ite @isUUIDFormat(uuv)
        (@ResultO-mk-ok uuv)
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_UUIDv7 ((ctx (Seq Int))) (@ResultO String)
    (let ((uuv (@UUIDv7_UFCons_API ctx)))
    (ite @isUUIDFormat(uuv)
        (@ResultO-mk-ok uuv)
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_ContentHash ((ctx (Seq Int))) (@ResultO (_ BitVec 16))
    (@ResultO-mk-ok (@SHAContentHash_UFCons_API ctx))
)

(define-fun @entrypoint_cons_LatLongCoordinate ((ctx (Seq Int))) (@ResultO (@Tuple2 Float Float))
    (let ((lat (@Latitude_UFCons_API ctx)) (long (@Longitude_UFCons_API ctx)))
    (ite (and (<= -90.0 lat) (<= lat 90.0) (< -180.0 long) (<= long 180.0))
        (@ResultO-mk-ok (@Tuple2 lat long))
        (@ResultO-mk-err @error-validate)
    ))
)

;;--GLOBAL_DECLS--;;

;;--UF_DECLS--;;

;;--FUNCTION_DECLS--;;

;;--GLOBAL_DEFINITIONS--;;

;;--IO_CONSTRUCTOR_EXTRACTOR_DEFINITIONS--;;