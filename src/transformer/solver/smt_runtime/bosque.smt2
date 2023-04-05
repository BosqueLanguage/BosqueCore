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
    (@IdealDateTime-mk (@IdealDateTime-year Int) (@IdealDateTime-month Int) (@IdealDateTime-day Int) (@IdealDateTime-hour Int) (@IdealDateTime-min Int) (@IdealDateTime-sec Int) (@IdealDateTime-msec Int) (BDateTime@tzdata BString))
  )
)

(declare-const @IdealDateTime-UTC String)
(assert (= @IdealDateTime-UTC "UTC"))

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
    ; ByteBuffer -> (Seq (_ BitVec 8))
    ; DateTime -> @IdealDateTime 
    ; UTCDateTime -> @IdealDateTime 
    ; PlainDate -> @IdealDateTime 
    ; PlainTime -> @IdealDateTime 
    ; TickTime -> Int
    ; LogicalTime -> Int
    ; ISOTimeStamp -> @IdealDateTime 
    ; UUID4 -> String
    ; UUID7 -> String
    ; SHAContentHash -> String
    ; LatLongCoordinate -> (@Tuple2 Float Float)
    ; Regex -> String
    ) (
        ( (@none) ) 
        ( (@nothing) )
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
    (@BoxedKey-mk-IdealDateTime (@BoxedKey-IdealDateTime @IdealDateTime ))
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
    (@Term-mk (@TypeTag tag) (@Term-data @BoxedData) (@Term-key @BoxedKey))
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
    (let ((tt (BKey_oftype k1)) (ttv1 (TypeTag_OrdinalOf (BKey_type k1))) (ttv2 (TypeTag_OrdinalOf (BKey_type k2))))
    (ite (not (= ttv1 ttv2))
      (< ttv1 ttv2)
      (let ((vv1 (BKey_value k1)) (vv2 (BKey_value k2)))
        (ite (= tt TypeTag_None)
          false
          (ite (= tt TypeTag_Bool)
            (Bool@less (bsqkey_bool_value vv1) (bsqkey_bool_value vv2))
            (ite (= tt TypeTag_Int) 
              (BInt@less (bsqkey_int_value vv1) (bsqkey_int_value vv2))
              (ite (= tt TypeTag_Nat) 
                (BNat@less (bsqkey_nat_value vv1) (bsqkey_nat_value vv2))
                (ite (= tt TypeTag_BigInt)
                  (BBigInt@less (bsqkey_bigint_value vv1) (bsqkey_bigint_value vv2))
                  (ite (= tt TypeTag_BigNat)
                    (BBigNat@less (bsqkey_bignat_value vv1) (bsqkey_bignat_value vv2))
                    (ite (= tt TypeTag_String)
                      (BString@less (bsqkey_string_value vv1) (bsqkey_string_value vv2))
                      (ite (= tt TypeTag_UTCDateTime)
                        (BUTCDateTime@less (bsqkey_utcdatetime_value vv1) (bsqkey_utcdatetime_value vv2)) 
                        (ite (= tt TypeTag_CalendarDate)
)


;;
;; Value extraction and binding
;;

(define-sort HavocSequence () (Seq Int))

(declare-fun BBool@UFCons_API (HavocSequence) Bool)
(declare-fun BInt@UFCons_API (HavocSequence) BInt)
(declare-fun BNat@UFCons_API (HavocSequence) BNat)
(declare-fun BBigInt@UFCons_API (HavocSequence) BBigInt)
(declare-fun BBigNat@UFCons_API (HavocSequence) BBigNat)
(declare-fun BFloat@UFCons_API (HavocSequence) BFloat)
(declare-fun BDecimal@UFCons_API (HavocSequence) BDecimal)
(declare-fun BRational@UFCons_API (HavocSequence) BRational)
(declare-fun BString@UFCons_API (HavocSequence) BString)
(declare-fun BByteBuffer@UFCons_API (HavocSequence) (Seq (_ BitVec 8)))
(declare-fun BDateYear@UFCons_API (HavocSequence) BNat)
(declare-fun BDateMonth@UFCons_API (HavocSequence) BNat)
(declare-fun BDateDay@UFCons_API (HavocSequence) BNat)
(declare-fun BDateHour@UFCons_API (HavocSequence) BNat)
(declare-fun BDateMinute@UFCons_API (HavocSequence) BNat)
(declare-fun BDateSecond@UFCons_API (HavocSequence) BNat)
(declare-fun BDateMillis@UFCons_API (HavocSequence) BNat)
(declare-fun BDateTZName@UFCons_API (HavocSequence) BString)
(declare-fun BTickTime@UFCons_API (HavocSequence) BTickTime)
(declare-fun BLogicalTime@UFCons_API (HavocSequence) BLogicalTime)
(declare-fun BUUID4@UFCons_API (HavocSequence) BUUID4)
(declare-fun BUUID7@UFCons_API (HavocSequence) BUUID7)
(declare-fun BSHAContentHash@UFCons_API (HavocSequence) BSHAContentHash)
(declare-fun BLatitude@UFCons_API (HavocSequence) BFloat)
(declare-fun BLongitude@UFCons_API (HavocSequence) BFloat)
(declare-fun ContainerSize@UFCons_API (HavocSequence) BNat)
(declare-fun BEnum@UFCons_API (HavocSequence) BNat)
(declare-fun UnionChoice@UFCons_API (HavocSequence) BNat)

(define-fun _@@cons_None_entrypoint ((ctx HavocSequence)) $Result_bsq_none
  ($Result_bsq_none@success bsq_none@literal)
)

(define-fun _@@cons_Nothing_entrypoint ((ctx HavocSequence)) $Result_bsq_nothing
  ($Result_bsq_nothing@success bsq_nothing@literal)
)

;;@BINTMIN, @BINTMAX, @BNATMAX, @SLENMAX, @BLENMAX
;;V_MIN_MAX;;

(define-fun _@@cons_Bool_entrypoint ((ctx HavocSequence)) $Result_Bool
  ($Result_Bool@success (BBool@UFCons_API ctx))
)

(define-fun _@@cons_Int_entrypoint ((ctx HavocSequence)) $Result_BInt
  (let ((iv (BInt@UFCons_API ctx)))
    (ite (and (<= @BINTMIN iv) (<= iv @BINTMAX))
      ($Result_BInt@success iv)
      ($Result_BInt@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_Nat_entrypoint ((ctx HavocSequence)) $Result_BNat
  (let ((iv (BNat@UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv @BNATMAX))
      ($Result_BNat@success iv)
      ($Result_BNat@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_BigInt_entrypoint ((ctx HavocSequence)) $Result_BBigInt
  (let ((iv (BBigInt@UFCons_API ctx)))
    (ite (and (<= (+ @BINTMIN @BINTMIN) iv) (<= iv (+ @BINTMAX @BINTMAX)))
      ($Result_BBigInt@success iv)
      ($Result_BBigInt@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_BigNat_entrypoint ((ctx HavocSequence)) $Result_BBigNat
  (let ((iv (BBigNat@UFCons_API ctx)))
    (ite (and (<= 0 iv) (<= iv (+ @BNATMAX @BNATMAX)))
      ($Result_BBigNat@success iv)
      ($Result_BBigNat@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_Float_entrypoint ((ctx HavocSequence)) $Result_BFloat
  ($Result_BFloat@success (BFloat@UFCons_API ctx))
)

(define-fun _@@cons_Decimal_entrypoint ((ctx HavocSequence)) $Result_BDecimal
  ($Result_BDecimal@success (BDecimal@UFCons_API ctx))
)

(define-fun _@@cons_Rational_entrypoint ((ctx HavocSequence)) $Result_BRational
  ($Result_BRational@success (BRational@UFCons_API ctx))
)

(define-fun _@@cons_String_entrypoint ((ctx HavocSequence)) $Result_BString
  (let ((sv (BString@UFCons_API ctx)))
    (ite (<= (str.len sv) @SLENMAX)
      ($Result_BString@success sv)
      ($Result_BString@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_ByteBuffer_entrypoint ((ctx HavocSequence)) $Result_BByteBuffer
  (let ((compress (BNat@UFCons_API (seq.++ ctx (seq.unit 0)))) (format (BNat@UFCons_API (seq.++ ctx (seq.unit 1)))) (buff (BByteBuffer@UFCons_API (seq.++ ctx (seq.unit 2)))))
    (ite (and (< compress 2) (< format 4) (<= (seq.len buff) @BLENMAX))
      ($Result_BByteBuffer@success (BByteBuffer@cons buff compress format))
      ($Result_BByteBuffer@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun @@isLeapYear ((y Int)) Bool
  (ite (or (= y 1900) (= y 2100) (= y 2200))
    false
    (= (mod y 4) 0)
  )
)

(define-fun @@check_DayInMonth ((d Int) (m Int) (y Int)) Bool
  (ite (= m 1)
    (ite (@@isLeapYear y)
      (<= d 29)
      (<= d 28)
    )
    (ite (or (= m 3) (= m 5) (= m 8) (= m 10))
      (<= d 30)
      (<= d 31)
    )
  )
)

(define-fun _@@cons_DateTime_entrypoint ((ctx HavocSequence)) $Result_BDateTime
  (let ((y (BDateYear@UFCons_API ctx)) (m (BDateMonth@UFCons_API ctx)) (d (BDateDay@UFCons_API ctx)) (hh (BDateHour@UFCons_API ctx)) (mm (BDateMinute@UFCons_API ctx)) (tzo (BDateTZName@UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (or (= tzo "UTC") (= tzo "PST") (= tzo "MST") (= tzo "CEST")))
      ($Result_BDateTime@success (BDateTime@cons y m d hh mm tzo))
      ($Result_BDateTime@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_UTCDateTime_entrypoint ((ctx HavocSequence)) $Result_BUTCDateTime
  (let ((y (BDateYear@UFCons_API ctx)) (m (BDateMonth@UFCons_API ctx)) (d (BDateDay@UFCons_API ctx)) (hh (BDateHour@UFCons_API ctx)) (mm (BDateMinute@UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59))
      ($Result_BUTCDateTime@success (BUTCDateTime@cons y m d hh mm))
      ($Result_BUTCDateTime@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_CalendarDate_entrypoint ((ctx HavocSequence)) $Result_BCalendarDate
  (let ((y (BDateYear@UFCons_API ctx)) (m (BDateMonth@UFCons_API ctx)) (d (BDateDay@UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@@check_DayInMonth d m y))
      ($Result_BCalendarDate@success (BCalendarDate@cons y m d))
      ($Result_BCalendarDate@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_TickTime_entrypoint ((ctx HavocSequence)) $Result_BTickTime
  (let ((tv (BTickTime@UFCons_API ctx)))
    (ite (and (<= 0 tv) (<= tv 1048576))
      ($Result_BTickTime@success tv)
      ($Result_BTickTime@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_LogicalTime_entrypoint ((ctx HavocSequence)) $Result_BLogicalTime
  (let ((lv (BLogicalTime@UFCons_API ctx)))
    (ite (and (<= 0 lv) (<= lv 64))
      ($Result_BLogicalTime@success lv)
      ($Result_BLogicalTime@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_ISOTimeStamp_entrypoint ((ctx HavocSequence)) $Result_BISOTimeStamp
  (let ((y (BDateYear@UFCons_API ctx)) (m (BDateMonth@UFCons_API ctx)) (d (BDateDay@UFCons_API ctx)) (hh (BDateHour@UFCons_API ctx)) (mm (BDateMinute@UFCons_API ctx)) (ss (BDateSecond@UFCons_API ctx)) (millis (BDateMillis@UFCons_API ctx)))
    (ite (and (<= 1900 y) (<= y 2200) (<= 0 m) (<= m 11) (<= 1 d) (@@check_DayInMonth d m y) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (<= 0 ss) (<= ss 60) (<= 0 millis) (<= millis 999))
      ($Result_BISOTimeStamp@success (BISOTimeStamp@cons y m d hh mm ss millis))
      ($Result_BISOTimeStamp@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_UUID4_entrypoint ((ctx HavocSequence)) $Result_BUUID4
  (let ((uuv (BUUID4@UFCons_API ctx)))
    (ite (str.in.re uuv (re.loop (re.union (re.range "0" "9") (re.range "a" "f")) 32 32))
      ($Result_BUUID4@success uuv)
      ($Result_BUUID4@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_UUID7_entrypoint ((ctx HavocSequence)) $Result_BUUID7
  (let ((uuv (BUUID7@UFCons_API ctx)))
    (ite (str.in.re uuv (re.loop (re.union (re.range "0" "9") (re.range "a" "f")) 32 32))
      ($Result_BUUID7@success uuv)
      ($Result_BUUID7@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_ContentHash_entrypoint ((ctx HavocSequence)) $Result_BSHAContentHash
  ($Result_BSHAContentHash@success (BSHAContentHash@UFCons_API ctx))
)

(define-fun _@@cons_LatLongCoordinate_entrypoint ((ctx HavocSequence)) $Result_BLatLongCoordinate
  (let ((lat (BLatitude@UFCons_API ctx)) (long (BLongitude@UFCons_API ctx)))
    (ite (and (<= -90.0 lat) (<= lat 90.0) (< -180.0 long) (<= long 180.0))
      ($Result_BLatLongCoordinate@success (BLatLongCoordinate@cons lat long))
      ($Result_BLatLongCoordinate@error ErrorID_AssumeCheck) 
    )
  )
)
