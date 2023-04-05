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
;;Type tag decls and orders
;;
(declare-sort @TypeTag)
(declare-const @TypeTag-None @TypeTag)
(declare-const @TypeTag-Nothing @TypeTag)
(declare-const @TypeTag-Bool @TypeTag)
(declare-const @TypeTag-Nat @TypeTag)
(declare-const @TypeTag-Int @TypeTag)
(declare-const @TypeTag-BigNat @TypeTag)
(declare-const @TypeTag-BigInt @TypeTag)
(declare-const @TypeTag-Float @TypeTag)
(declare-const @TypeTag-Decimal @TypeTag)
(declare-const @TypeTag-Rational @TypeTag)
(declare-const @TypeTag-String @TypeTag)
(declare-const @TypeTag-ASCIIString @TypeTag)
(declare-const @TypeTag-ByteBuffer @TypeTag)
(declare-const @TypeTag-DateTime @TypeTag)
(declare-const @TypeTag-UTCDateTime @TypeTag)
(declare-const @TypeTag-PlainDate @TypeTag)
(declare-const @TypeTag-PlainTime @TypeTag)
(declare-const @TypeTag-TickTime @TypeTag)
(declare-const @TypeTag-LogicalTime @TypeTag)
(declare-const @TypeTag-ISOTimeStamp @TypeTag)
(declare-const @TypeTag-UUID4 @TypeTag)
(declare-const @TypeTag-UUID7 @TypeTag)
(declare-const @TypeTag-SHAContentHash @TypeTag)
(declare-const @TypeTag-LatLongCoordinate @TypeTag)
(declare-const @TypeTag-Regex @TypeTag)
;;--TYPE_TAG_DECLS--;;


(assert (distinct 
@TypeTag-None @TypeTag-Nothing @TypeTag-Bool @TypeTag-Nat @TypeTag-Int @TypeTag-BigNat @TypeTag-BigInt @TypeTag-Float @TypeTag-Decimal @TypeTag-Rational @TypeTag-String @TypeTag-ASCIIString
@TypeTag-ByteBuffer @TypeTag-DateTime @TypeTag-UTCDateTime @TypeTag-PlainDate @TypeTag-PlainTime @TypeTag-TickTime @TypeTag-LogicalTime @TypeTag-ISOTimeStamp @TypeTag-UUID4 @TypeTag-UUID7 @TypeTag-SHAContentHash @TypeTag-LatLongCoordinate @TypeTag-Regex
;;--TYPE_TAG_DISTINCTS--;;
))

(define-fun @key_type_sort_order ((x @TypeTag) (y @TypeTag)) Bool ((_ linear-order 0) x y))
(assert (@key_type_sort_order @TypeTag-None @TypeTag-Bool))
(assert (@key_type_sort_order @TypeTag-Bool @TypeTag-Nat))
(assert (@key_type_sort_order @TypeTag-Nat @TypeTag-Int))
(assert (@key_type_sort_order @TypeTag-Int @TypeTag-BigNat))
(assert (@key_type_sort_order @TypeTag-BigNat @TypeTag-BigInt))
(assert (@key_type_sort_order @TypeTag-BigInt @TypeTag-String))
(assert (@Key_type_sort_order @TypeTag-String @TypeTag-ASCIIString))
(assert (@key_type_sort_order @TypeTag-ASCIIString @TypeTag-UTCDateTime))
(assert (@key_type_sort_order @TypeTag-UTCDateTime @TypeTag-PlainDate))
(assert (@key_type_sort_order @TypeTag-PlainDate @TypeTag-PlainTime))
(assert (@key_type_sort_order @TypeTag-PlainTime @TypeTag-TickTime))
(assert (@key_type_sort_order @TypeTag-TickTime @TypeTag-LogicalTime))
(assert (@key_type_sort_order @TypeTag-LogicalTime @TypeTag-ISOTimeStamp))
(assert (@key_type_sort_order @TypeTag-ISOTimeStamp @TypeTag-UUID4))
(assert (@key_type_sort_order @TypeTag-UUID4 @TypeTag-UUID7))
(assert (@key_type_sort_order @TypeTag-UUID7 @TypeTag-SHAContentHash))
;;--KEY_TYPE_TAG_SORT--;;

(define-fun @subtypeof ((x @TypeTag) (y @TypeTag)) Bool ((_ partial-order 1) x y))
;;--TYPE_TAG_SUBTYPE--;;

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

(define-fun @Float_lteq ((x @Float) (y @Float)) Bool ((_ linear-order 2) x y))
(define-fun @Float_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Float_lteq x y)))

(define-fun @Decimal_lteq ((x @Decimal) (y @Decimal)) Bool ((_ linear-order 3) x y))
(define-fun @Decimal_lt ((x @Float) (y @Float)) Bool (and (not (= x y)) (@Decimal_lteq x y)))

(define-fun @Rational_lteq ((x @Rational) (y @Rational)) Bool ((_ linear-order 4) x y))
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
;;@Structural datatypes
;;
(declare-datatypes 
    (
        (@Tuple0 0)
        (@Tuple1 1)
        (@Tuple2 2)
        (@Tuple3 3)
        ;;TODO: more tuples here when needed
    ) 
    (
        (par () ( (@Tuple0-mk) ))
        (par (T0) ( (@Tuple1-mk (@Tuple1-0 T0)) ))
        (par (T0 T1) ( (@Tuple2-mk (@Tuple2-0 T0) (Tuple2-1 T1)) ))
        (par (T0 T1 T2) ( (@Tuple3-mk (@Tuple3-0 T0) (Tuple3-1 T1) (Tuple3-2 T2)) ))
        ;;TODO: more tuples here when needed
    )
)
(declare-datatypes 
    (
        (@Record0 0)
        (@Record1 1)
        (@Record2 2)
        (@Record3 3)
        ;;TODO: more records here when needed
    ) 
    (
        (par () ( (@Record0-mk) ))
        (par (T0) ( (@Record1-mk (@Record1-0 T0)) ))
        (par (T0 T1) ( (@Record2-mk (@Record2-0 T0) (Record2-1 T1)) ))
        (par (T0 T1 T2) ( (@Record3-mk (@Record3-0 T0) (Record3-1 T1) (Record3-2 T2)) ))
        ;;TODO: more records here when needed
    )
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
    (@None 0)
    (@Nothing 0)
    ;;--OO_DECLS--;;
    ; Bool -> Bool
    ; Int -> Int
    ; Nat -> Int
    ; BigInt -> Int
    ; BigNat -> Int
    ; Float -> @Float 
    ; Decimal -> @Decimal
    ; Rational -> @Rational
    ; String -> String
    (@ByteBuffer 0)
    ; DateTime -> @IdealDateTime 
    ; UTCDateTime -> @IdealDateTime 
    ; PlainDate -> @IdealDateTime 
    ; PlainTime -> @IdealDateTime 
    ; TickTime -> Int
    ; LogicalTime -> Int
    ; ISOTimeStamp -> @IdealDateTime 
    ; UUID4 -> String
    ; UUID7 -> String
    ; SHAContentHash -> (_ BitVec 16)
    ; LatLongCoordinate -> (@Tuple2 Float Float)
    ; Regex -> String
    ) (
        ( (@none) ) 
        ( (@nothing) )
        ( (@bytebuffer-mk (@ByteBuffer-compress Int) (@ByteBuffer-format Int) (@ByteBuffer-bytes (Seq (_ BitVec 8)))) )
        ;;--OO_CONSTRUCTORS--;;
    )
)

(declare-datatype @BoxedKey 
    (
        (@BoxedKey-mk-NA)
        (@BoxedKey-mk-none)
        (@BoxedKey-mk-Bool (@BoxedKey-Bool Bool))
        (@BoxedKey-mk-Int (@BoxedKey-Int Int))
        (@BoxedKey-mk-String (@BoxedKey-String String))
        (@BoxedKey-mk-SHA (@BoxedKey-SHA (_ BitVec 16)))
        (@BoxedKey-mk-IdealDateTime (@BoxedKey-IdealDateTime @IdealDateTime))
    )
)

(declare-datatype @BoxedData 
    (
        (@BoxedData-mk-none)
        (@BoxedData-mk-nothing)
        ;;--TYPE_BOX_CONSTRUCTORS--;;
    )
)

;;
;; Boxed datatypes 
;;
(declare-datatype @Term
    (
        (@Term-mk (@Term-tag @TypeTag) (@Term-data @BoxedData) (@Term-key @BoxedKey))
    )
)

(declare-const @Term-none @Term)
(assert (= @Term-none (@Term-mk @TypeTag-None @BoxedData-mk-none @BoxedKey-mk-none)))

(declare-const @Term-nothing @Term)
(assert (= @Term-nothing (@Term-mk @TypeTag-Nothing @BoxedData-mk-nothing @BoxedKey-mk-NA)))

(define-fun @boxkey ((tag @TypeTag) (data @BoxedData) (key @BoxedKey)) @Term 
    (@Term-mk tag data key)
)

(define-fun @box ((tag @TypeTag) (data @BoxedData)) @Term 
    (@Term-mk tag data @BoxedKey-mk-NA)
)

(define-fun @keyless ((k1 @Term) (k2 @Term)) Bool 
    (let ((tt1 (@Term-tag k1)) (tt2 @Term-tag k2))
    (ite (not (= ttv1 ttv2))
        (key_type_sort_order ttv1 ttv2)
        (let ((vv1 (@Term-key k1)) (vv2 (@Term-key k2)))
        (ite (and ((_ is @BoxedKey-mk-none) vv1) ((_ is @BoxedKey-mk-none) vv2))
            false
            (ite (and ((_ is @BoxedKey-mk-Bool) vv1) ((_ is @BoxedKey-mk-Bool) vv2))
                    (and (not (@BoxedKey-Bool vv1)) (@BoxedKey-Bool vv2))
                (ite (and ((_ is @BoxedKey-mk-Int) vv1) ((_ is @BoxedKey-mk-Int) vv2))
                    (< (@BoxedKey-Int vv1) (@BoxedKey-Int vv2))
                    (ite (and ((_ is @BoxedKey-mk-String) vv1) ((_ is @BoxedKey-mk-String) vv2))
                        (str.< (bsqkey_nat_value vv1) (bsqkey_nat_value vv2))
                        (ite (and ((_ is @BoxedKey-mk-SHA) vv1) ((_ is @BoxedKey-mk-SHA) vv2))
                            (bvult (@BoxedKey-SHA vv1) (@BoxedKey-SHA vv2))
                            (@IdealDateTime_less (@BoxedKey-IdealDateTime vv1) (@BoxedKey-IdealDateTime vv2)) 
                        )
                    )
                )
            )
        ))
    ))
)

;;
;; Value extraction and binding
;;

(define-sort @HavocSequence () (Seq Int))

(declare-fun @Bool_UFCons_API (@HavocSequence) Bool)
(declare-fun @Nat_UFCons_API (@HavocSequence) Int)
(declare-fun @Int_UFCons_API (@HavocSequence) Int)
(declare-fun @BigInt_UFCons_API (@HavocSequence) Int)
(declare-fun @BigNat_UFCons_API (@HavocSequence) Int)
(declare-fun @Float_UFCons_API (@HavocSequence) @Float)
(declare-fun @Decimal_UFCons_API (@HavocSequence) @Decimal)
(declare-fun @Rational_UFCons_API (@HavocSequence) @Rational)
(declare-fun @String_UFCons_API (@HavocSequence) String)
(declare-fun @ASCIIString_UFCons_API (@HavocSequence) String)
(declare-fun @ByteBuffer_UFCons_API (@HavocSequence) (Seq (_ BitVec 8)))
(declare-fun @IdealDateYear_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateMonth_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateDay_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateHour_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateMinute_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateSecond_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateMillis_UFCons_API (@HavocSequence) Int)
(declare-fun @IdealDateTZName_UFCons_API (@HavocSequence) String)
(declare-fun @TickTime_UFCons_API (@HavocSequence) Int)
(declare-fun @LogicalTime_UFCons_API (@HavocSequence) Int)
(declare-fun @UUID4_UFCons_API (@HavocSequence) String)
(declare-fun @UUID7_UFCons_API (@HavocSequence) String)
(declare-fun @SHAContentHash_UFCons_API (@HavocSequence) (_ BitVec 16))
(declare-fun @Latitude_UFCons_API (@HavocSequence) @Float)
(declare-fun @Longitude_UFCons_API (@HavocSequence) @Float)
(declare-fun @ContainerSize_UFCons_API (@HavocSequence) Int)
(declare-fun @Enum_UFCons_API (@HavocSequence) Int)
(declare-fun @TypeChoice_UFCons_API (@HavocSequence) Int)

(define-fun @entrypoint_cons_None ((ctx @HavocSequence)) (@ResultO @None)
    (@ResultO-mk-ok @none)
)

(define-fun @entrypoint_cons_Nothing ((ctx @HavocSequence)) (@ResultO @Nothing)
    (@ResultO-mk-ok @nothing)
)

;;@INT_MIN, @INT_MAX, @NAT_MAX, @SLEN_MAX, @BLEN_MAX, @CSIZE_MAX
;;V_MIN_MAX;;

(define-fun @entrypoint_cons_Bool ((ctx @HavocSequence)) (@ResultO Bool)
    (@ResultO-mk-ok (@Bool_UFCons_API ctx))
)

(define-fun @entrypoint_cons_Nat ((ctx @HavocSequence)) (@ResultO Int)
    (let ((iv (@Nat_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv @INT_MAX))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_Int ((ctx @HavocSequence)) (@ResultO Int)
    (let ((iv (@Int_UFCons_API ctx)))
    (ite (and (<= @INT_MIN iv) (<= iv @INT_MAX))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_BigNat ((ctx @HavocSequence)) (@ResultO Int)
    (let ((iv (@BigNat_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_BigInt ((ctx @HavocSequence)) (@ResultO Int)
    (let ((iv (@BigInt_UFCons_API ctx)))
    (ite (and (<= (+ @INT_MIN @INT_MIN) iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_Float ((ctx @HavocSequence)) (@ResultO @Float)
    (@ResultO-mk-ok (@Float_UFCons_API ctx))
)

(define-fun @entrypoint_cons_Decimal ((ctx @HavocSequence)) (@ResultO @Decimal)
    (@ResultO-mk-ok (@Decimal_UFCons_API ctx))
)

(define-fun @entrypoint_cons_Rational ((ctx @HavocSequence)) (@ResultO @Rational)
    (@ResultO-mk-ok (@Rational_UFCons_API ctx))
)

(define-fun _@@cons_String_entrypoint ((ctx @HavocSequence)) (@ResultO String)
    (let ((sv (@String_UFCons_API ctx)))
    (ite (<= (str.len sv) @SLEN_MAX)
        (@ResultO-mk-ok sv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_ByteBuffer ((ctx @HavocSequence)) (@ResultO (Seq (_ BitVec 8)))
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

(define-fun @entrypoint_cons_DateTime ((ctx @HavocSequence)) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)) (hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)) (tzinfo (@IdealDateTZName_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 59) (<= 0 millis) (<= millis 999) (@istzname tzinfo))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh mm ss millis tzinfo))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_UTCDateTime ((ctx @HavocSequence)) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)) (hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 59) (<= 0 millis) (<= millis 999))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh mm ss millis @IdealDateTime-UTC))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_PlainDate ((ctx @HavocSequence)) (@ResultO @IdealDateTime)
    (let ((y (@IdealDateYear_UFCons_API ctx)) (m (@IdealDateMonth_UFCons_API ctx)) (d (@IdealDateDay_UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@check_DayInMonth d m y))
        (@ResultO-mk-ok (@IdealDateTime-mk y m d hh 0 0 0 @IdealDateTime-UTC))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_PlainTime ((ctx @HavocSequence)) (@ResultO @IdealDateTime)
    (let ((hh (@IdealDateHour_UFCons_API ctx)) (mm (@IdealDateMinute_UFCons_API ctx)) (ss (@IdealDateSecond_UFCons_API ctx)) (millis (@IdealDateMillis_UFCons_API ctx)))
    (ite (and (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 59) (<= 0 millis) (<= millis 999))
        (@ResultO-mk-ok (@IdealDateTime-mk 0 0 0 hh mm ss millis @IdealDateTime-UTC))
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_TickTime ((ctx @HavocSequence)) (@ResultO Int)
    (let ((iv (@TickTime_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_LogicalTime ((ctx @HavocSequence)) (@ResultO Int)
    (let ((iv (@LogicalTime_UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @INT_MAX @INT_MAX)))
        (@ResultO-mk-ok iv)
        (@ResultO-mk-err @error-validate) 
    ))
)

(define-fun @entrypoint_cons_ISOTimeStamp ((ctx @HavocSequence)) (@ResultO @IdealDateTime)
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

(define-fun @entrypoint_cons_UUID4 ((ctx @HavocSequence)) (@ResultO String)
    (let ((uuv (@UUID4_UFCons_API ctx)))
    (ite @isUUIDFormat(uuv)
        (@ResultO-mk-ok uuv)
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_UUID7 ((ctx @HavocSequence)) (@ResultO String)
    (let ((uuv (@UUID7_UFCons_API ctx)))
    (ite @isUUIDFormat(uuv)
        (@ResultO-mk-ok uuv)
        (@ResultO-mk-err @error-validate)
    ))
)

(define-fun @entrypoint_cons_ContentHash ((ctx @HavocSequence)) (@ResultO (_ BitVec 16))
    (@ResultO-mk-ok (@SHAContentHash_UFCons_API ctx))
)

(define-fun @entrypoint_cons_LatLongCoordinate ((ctx @HavocSequence)) (@ResultO (@Tuple2 Float Float))
    (let ((lat (@Latitude_UFCons_API ctx)) (long (@Longitude_UFCons_API ctx)))
    (ite (and (<= -90.0 lat) (<= lat 90.0) (< -180.0 long) (<= long 180.0))
        (@ResultO-mk-ok (@Tuple2 lat long))
        (@ResultO-mk-err @error-validate)
    ))
)

;;GLOBAL_DECLS;;

;;UF_DECLS;;

;;FUNCTION_DECLS;;

;;GLOBAL_DEFINITIONS;;
