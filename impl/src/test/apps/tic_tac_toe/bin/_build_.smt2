(set-logic ALL)

;;
;; Type Tags
;;

(declare-datatypes (
      (TypeTag 0)
    ) (
    ( 
      (TypeTag_$Invalid)
      (TypeTag_BigInt)
      (TypeTag_BigNat)
      (TypeTag_Bool)
      (TypeTag_BufferCompression)
      (TypeTag_BufferFormat)
      (TypeTag_ByteBuffer)
      (TypeTag_CalendarDate)
      (TypeTag_DateTime)
      (TypeTag_Decimal)
      (TypeTag_Float)
      (TypeTag_HavocSequence)
      (TypeTag_ISOTimeStamp)
      (TypeTag_Int)
      (TypeTag_LatLongCoordinate)
      (TypeTag_ListOps)
      (TypeTag_List_Bool_)
      (TypeTag_List_List_Main..PlayerMark__)
      (TypeTag_List_Main..PlayerMark_)
      (TypeTag_LogicalTime)
      (TypeTag_Main..Board)
      (TypeTag_Main..BoardPostion)
      (TypeTag_Main..PlayerMark)
      (TypeTag_Nat)
      (TypeTag_None)
      (TypeTag_Nothing)
      (TypeTag_Rational)
      (TypeTag_Regex)
      (TypeTag_RelativeTime)
      (TypeTag_SHAContentHash)
      (TypeTag_ShaContentHash)
      (TypeTag_String)
      (TypeTag_TickTime)
      (TypeTag_UTCDateTime)
      (TypeTag_UUID4)
      (TypeTag_UUID7)
      (TypeTag__cells._List_List_Main..PlayerMark___)
    )
))

(declare-fun TypeTag_OrdinalOf (TypeTag) Int)
(assert (= (TypeTag_OrdinalOf TypeTag_BigInt) 0))
(assert (= (TypeTag_OrdinalOf TypeTag_BigNat) 1))
(assert (= (TypeTag_OrdinalOf TypeTag_Bool) 2))
(assert (= (TypeTag_OrdinalOf TypeTag_BufferCompression) 3))
(assert (= (TypeTag_OrdinalOf TypeTag_BufferFormat) 4))
(assert (= (TypeTag_OrdinalOf TypeTag_CalendarDate) 5))
(assert (= (TypeTag_OrdinalOf TypeTag_ISOTimeStamp) 6))
(assert (= (TypeTag_OrdinalOf TypeTag_Int) 7))
(assert (= (TypeTag_OrdinalOf TypeTag_LogicalTime) 8))
(assert (= (TypeTag_OrdinalOf TypeTag_Main..PlayerMark) 9))
(assert (= (TypeTag_OrdinalOf TypeTag_Nat) 10))
(assert (= (TypeTag_OrdinalOf TypeTag_None) 11))
(assert (= (TypeTag_OrdinalOf TypeTag_RelativeTime) 12))
(assert (= (TypeTag_OrdinalOf TypeTag_SHAContentHash) 13))
(assert (= (TypeTag_OrdinalOf TypeTag_ShaContentHash) 14))
(assert (= (TypeTag_OrdinalOf TypeTag_String) 15))
(assert (= (TypeTag_OrdinalOf TypeTag_TickTime) 16))
(assert (= (TypeTag_OrdinalOf TypeTag_UTCDateTime) 17))
(assert (= (TypeTag_OrdinalOf TypeTag_UUID4) 18))
(assert (= (TypeTag_OrdinalOf TypeTag_UUID7) 19))

(declare-datatypes (
      (AbstractTypeTag 0)
    ) (
    ( 
      (AbstractTypeTag_$Invalid)
      ;;NO DATA;;
    )
))

(declare-datatypes (
      (TupleIndexTag 0)
    ) (
    ( 
      (TupleIndexTag_$Invalid)
      ;;NO DATA;;
    )
))

(declare-datatypes (
      (RecordPropertyTag 0)
    ) (
    ( 
      (RecordPropertyTag_$Invalid)
      ;;RecordPropertyTag;;
    )
))

(declare-fun SubtypeOf@ (TypeTag AbstractTypeTag) Bool)
;;NO DATA;;

(declare-fun HasIndex@ (TypeTag TupleIndexTag) Bool)
;;NO DATA;;

(declare-fun HasProperty@ (TypeTag RecordPropertyTag) Bool)
;;NO DATA;;

(declare-const Real@zero Real)
(assert (= Real@zero 0.0))

(declare-const Real@one Real)
(assert (= Real@one 1.0))

(define-sort BInt () Int)
(define-sort BNat () Int)
(define-sort BBigInt () Int)
(define-sort BBigNat () Int)
(define-sort BFloat () Real)
(define-sort BDecimal () Real)
(define-sort BRational () Real)
(define-sort BString () String)
(define-sort BTickTime () Int)
(define-sort BLogicalTime () Int)
(define-sort BUUID4 () String)
(define-sort BUUID7 () String)
(define-sort BSHAContentHash () Int)

;;TODO Hash + HashInvert and axioms

(declare-datatype BByteBuffer 
  (
    (BByteBuffer@cons (BByteBuffer@bytes (Seq (_ BitVec 8))) (BByteBuffer@format BNat) (BByteBuffer@compress BNat))
  )
)

(declare-datatype BDateTime 
  (
    (BDateTime@cons (BDateTime@year BNat) (BDateTime@month BNat) (BDateTime@day BNat) (BDateTime@hour BNat) (BDateTime@min BNat) (BDateTime@tzdata BString))
  )
)

(declare-datatype BUTCDateTime 
  (
    (BUTCDateTime@cons (BUTCDateTime@year BNat) (BUTCDateTime@month BNat) (BUTCDateTime@day BNat) (BUTCDateTime@hour BNat) (BUTCDateTime@min BNat))
  )
)

(declare-datatype BCalendarDate 
  (
    (BCalendarDate@cons (BCalendarDate@year BNat) (BCalendarDate@month BNat) (BCalendarDate@day BNat))
  )
)

(declare-datatype BRelativeTime 
  (
    (BRelativeTime@cons (BRelativeTime@hour BNat) (BRelativeTime@min BNat))
  )
)

(declare-datatype BISOTimeStamp 
  (
    (BISOTimeStamp@cons (BISOTimeStamp@year BNat) (BISOTimeStamp@month BNat) (BISOTimeStamp@day BNat) (BISOTimeStamp@hour BNat) (BISOTimeStamp@min BNat) (BISOTimeStamp@sec BNat) (BISOTimeStamp@millis BNat))
  )
)

(declare-datatype BLatLongCoordinate 
  (
    (BLatLongCoordinate@cons (BLatLongCoordinate@lat Real) (BLatLongCoordinate@long Real))
  )
)

(declare-const BInt@zero BInt) (assert (= BInt@zero 0))
(declare-const BInt@one BInt) (assert (= BInt@one 1))

(declare-const BNat@zero BNat) (assert (= BNat@zero 0))
(declare-const BNat@one BNat) (assert (= BNat@one 1))

(declare-const BBigInt@zero BBigInt) (assert (= BBigInt@zero 0))
(declare-const BBigInt@one BBigInt) (assert (= BBigInt@one 1))

(declare-const BBigNat@zero BBigNat) (assert (= BBigNat@zero 0))
(declare-const BBigNat@one BBigNat) (assert (= BBigNat@one 1))

(declare-const BFloat@zero BFloat) (assert (= BFloat@zero Real@zero))
(declare-const BFloat@one BFloat) (assert (= BFloat@one Real@one))

(declare-const BDecimal@zero BDecimal) (assert (= BDecimal@zero Real@zero))
(declare-const BDecimal@one BDecimal) (assert (= BDecimal@one Real@one))

(declare-const BRational@zero BRational) (assert (= BRational@zero Real@zero))
(declare-const BRational@one BRational) (assert (= BRational@one Real@one))

(define-sort HavocSequence () (Seq Int))

;;
;; Primitive datatypes 
;;
(declare-datatypes (
      (bsq_none 0)
      (bsq_nothing 0)
      ; Bool -> Bool
      ; Int -> Int
      ; Nat -> Int
      ; BigInt -> Int
      ; BigNat -> Int
      ; Float -> Real 
      ; Decimal -> Real
      ; Rational -> Real
      ; String -> String | (Seq (_ BitVec 8))
      ; ByteBuffer -> BByteBuffer
      ; DateTime -> BDateTime
      ; UTCDateTime -> BUTCDateTime
      ; CalendarDate -> BCalendarDate
      ; RelativeTime -> BRelativeTime
      ; TickTime -> Int
      ; LogicalTime -> Int
      ; ISOTimeStamp -> BISOTimeStamp
      ; UUID4 -> BUUID4
      ; UUID7 -> BUUID7
      ; SHAContentHash -> (_ BitVec 16)
      ; LatLongCoordinate -> BLatLongCoordinate
    ) (
      ( (bsq_none@literal) ) 
      ( (bsq_nothing@literal) )
))

(define-sort BufferCompression () BNat)
(define-sort BufferFormat () BNat)
(define-sort Main..PlayerMark () BNat)

;;
;; KeyType Concept datatypes
;;
(declare-datatypes (
      (bsq_keyobject 0)
      (BKey 0)
    ) (
    (
      (bsqkey_none@literal)
      (bsqkey_bool@box (bsqkey_bool_value Bool))
      (bsqkey_int@box (bsqkey_int_value BInt))
      (bsqkey_nat@box (bsqkey_nat_value BNat))
      (bsqkey_bigint@box (bsqkey_bigint_value BBigInt))
      (bsqkey_bignat@box (bsqkey_bignat_value BBigNat))
      (bsqkey_string@box (bsqkey_string_value BString))
      (bsqkey_utcdatetime@box (bsqkey_utcdatetime_value BUTCDateTime))
      (bsqkey_calendardate@box (bsqkey_calendardate_value BCalendarDate))
      (bsqkey_relativetime@box (bsqkey_relativetime_value BRelativeTime))
      (bsqkey_ticktime@box (bsqkey_ticktime_value BTickTime))
      (bsqkey_logicaltime@box (bsqkey_logicaltime_value BLogicalTime))
      (bsqkey_isotimestamp@box (bsqkey_isotimestamp_value BISOTimeStamp))
      (bsqkey_uuid4@box (bsqkey_uuid4_value BUUID4))
      (bsqkey_uuid7@box (bsqkey_uuid7_value BUUID7))
      (bsqkey_shacontenthash@box (bsqkey_shacontenthash_value BSHAContentHash))
      (BufferCompression@box (bsqkey_BufferCompression_value BufferCompression))
      (BufferFormat@box (bsqkey_BufferFormat_value BufferFormat))
      (Main..PlayerMark@box (bsqkey_Main..PlayerMark_value Main..PlayerMark))
    )
    ( (BKey@box (BKey_type TypeTag) (BKey_oftype TypeTag) (BKey_value bsq_keyobject)) )
))

(declare-const BKey@none BKey)
(assert (= BKey@none (BKey@box TypeTag_None TypeTag_None bsqkey_none@literal)))

(define-fun bsq_none@less ((k1 bsq_none) (k2 bsq_none)) Bool
  false
)

(define-fun Bool@less ((k1 Bool) (k2 Bool)) Bool
  (and (not k1) k2)
)

(define-fun BInt@less ((k1 BInt) (k2 BInt)) Bool
  (< k1 k2)
)

(define-fun BNat@less ((k1 BNat) (k2 BNat)) Bool
  (< k1 k2)
)

(define-fun BBigInt@less ((k1 BBigInt) (k2 BBigInt)) Bool
  (< k1 k2)
)

(define-fun BBigNat@less ((k1 BBigNat) (k2 BBigNat)) Bool
  (< k1 k2)
)

(define-fun BString@less ((k1 BString) (k2 BString)) Bool
  (str.< k1 k2)
)

(define-fun BUTCDateTime@less ((k1 BUTCDateTime) (k2 BUTCDateTime)) Bool
  (ite (not (= (BUTCDateTime@year k1) (BUTCDateTime@year k2)))
    (< (BUTCDateTime@year k1) (BUTCDateTime@year k2))
    (ite (not (= (BUTCDateTime@month k1) (BUTCDateTime@month k2)))
      (< (BUTCDateTime@month k1) (BUTCDateTime@month k2))
      (ite (not (= (BUTCDateTime@day k1) (BUTCDateTime@day k2)))
        (< (BUTCDateTime@day k1) (BUTCDateTime@day k2))
        (ite (not (= (BUTCDateTime@hour k1) (BUTCDateTime@hour k2)))
          (< (BUTCDateTime@hour k1) (BUTCDateTime@hour k2))
          (< (BUTCDateTime@min k1) (BUTCDateTime@min k2))
        )
      )
    )
  )
)

(define-fun BCalendarDate@less ((k1 BCalendarDate) (k2 BCalendarDate)) Bool
  (ite (not (= (BCalendarDate@year k1) (BCalendarDate@year k2)))
    (< (BCalendarDate@year k1) (BCalendarDate@year k2))
    (ite (not (= (BCalendarDate@month k1) (BCalendarDate@month k2)))
      (< (BCalendarDate@month k1) (BCalendarDate@month k2))
      (< (BCalendarDate@day k1) (BCalendarDate@day k2))
    )
  )
)

(define-fun BRelativeTime@less ((k1 BRelativeTime) (k2 BRelativeTime)) Bool
  (ite (not (= (BRelativeTime@hour k1) (BRelativeTime@hour k2)))
    (< (BRelativeTime@hour k1) (BRelativeTime@hour k2))
    (< (BRelativeTime@min k1) (BRelativeTime@min k2))
  )
)

(define-fun BTickTime@less ((k1 BTickTime) (k2 BTickTime)) Bool
  (< k1 k2)
)

(define-fun BLogicalTime@less ((k1 BLogicalTime) (k2 BLogicalTime)) Bool
  (< k1 k2)
)

(define-fun BISOTimeStamp@less ((k1 BISOTimeStamp) (k2 BISOTimeStamp)) Bool
  (ite (not (= (BISOTimeStamp@year k1) (BISOTimeStamp@year k2)))
    (< (BISOTimeStamp@year k1) (BISOTimeStamp@year k2))
    (ite (not (= (BISOTimeStamp@month k1) (BISOTimeStamp@month k2)))
      (< (BISOTimeStamp@month k1) (BISOTimeStamp@month k2))
      (ite (not (= (BISOTimeStamp@day k1) (BISOTimeStamp@day k2)))
        (< (BISOTimeStamp@day k1) (BISOTimeStamp@day k2))
        (ite (not (= (BISOTimeStamp@hour k1) (BISOTimeStamp@hour k2)))
          (< (BISOTimeStamp@hour k1) (BISOTimeStamp@hour k2))
          (ite (not (= (BISOTimeStamp@min k1) (BISOTimeStamp@min k2)))
            (< (BISOTimeStamp@min k1) (BISOTimeStamp@min k2))
            (ite (not (= (BISOTimeStamp@sec k1) (BISOTimeStamp@sec k2)))
              (< (BISOTimeStamp@sec k1) (BISOTimeStamp@sec k2))
              (< (BISOTimeStamp@millis k1) (BISOTimeStamp@millis k2))
            )
          )
        )
      )
    )
  )
)

(define-fun BUUID4@less ((k1 BUUID4) (k2 BUUID4)) Bool
  (str.< k1 k2)
)

(define-fun BUUID7@less ((k1 BUUID7) (k2 BUUID7)) Bool
  (str.< k1 k2)
)

(define-fun BSHAContentHash@less ((k1 BSHAContentHash) (k2 BSHAContentHash)) Bool
  (< k1 k2)
)

(define-fun BKey@less ((k1 BKey) (k2 BKey)) Bool
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
                          (BCalendarDate@less (bsqkey_calendardate_value vv1) (bsqkey_calendardate_value vv2))
                          (ite (= tt TypeTag_RelativeTime)
                            (BRelativeTime@less (bsqkey_relativetime_value vv1) (bsqkey_relativetime_value vv2))
                            (ite (= tt TypeTag_TickTime)
                              (BTickTime@less (bsqkey_ticktime_value vv1) (bsqkey_ticktime_value vv2))
                              (ite (= tt TypeTag_LogicalTime)
                                (BLogicalTime@less (bsqkey_logicaltime_value vv1) (bsqkey_logicaltime_value vv2))
                                (ite (= tt TypeTag_ISOTimeStamp)
                                  (BISOTimeStamp@less (bsqkey_isotimestamp_value vv1) (bsqkey_isotimestamp_value vv2))
                                  (ite (= tt TypeTag_UUID4)
                                    (BUUID4@less (bsqkey_uuid4_value vv1) (bsqkey_uuid4_value vv2))
                                    (ite (= tt TypeTag_UUID7)
                                      (BUUID7@less (bsqkey_uuid7_value vv1) (bsqkey_uuid7_value vv2))
                                      (BSHAContentHash@less (bsqkey_shacontenthash_value vv1) (bsqkey_shacontenthash_value vv2))
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

;;
;; Any Concept datatypes
;;
(declare-datatypes (
    (bsq_regex 0)
    ;;NO DATA;;
    (_cells._List_List_Main..PlayerMark___ 0)
    (ListOps 0)
    (Main..Board 0)
    (Main..BoardPostion 0)
    (List_Bool_ 0)
    (List_List_Main..PlayerMark__ 0)
    (List_Main..PlayerMark_ 0)
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ;;NO DATA;;
    ( (_cells._List_List_Main..PlayerMark___@cons (_cells._List_List_Main..PlayerMark___@_cells List_List_Main..PlayerMark__)) )
    ( (ListOps@cons ) )
    ( (Main..Board@cons (Main..Board@_cells List_List_Main..PlayerMark__)) )
    ( (Main..BoardPostion@cons (Main..BoardPostion@_rowpos BNat) (Main..BoardPostion@_colpos BNat)) )
    ( (List_Bool_@cons (List_Bool__seq (Seq Bool))) )
    ( (List_List_Main..PlayerMark__@cons (List_List_Main..PlayerMark___seq (Seq List_Main..PlayerMark_))) )
    ( (List_Main..PlayerMark_@cons (List_Main..PlayerMark__seq (Seq Main..PlayerMark))) )
    (
      (bsqobject_nothing@literal)
      (bsqobject_float@box (bsqobject_float_value BFloat))
      (bsqobject_decimal@box (bsqobject_decimal_value BDecimal))
      (bsqobject_rational@box (bsqobject_rational_value BRational))
      (bsqobject_bytebuffer@box (bsqobject_bytebuffer_value BByteBuffer))
      (bsqobject_datetime@box (bsqobject_datetime_value BDateTime))
      (bsqobject_regex@box (bsqobject_regex_value bsq_regex))
      ;;NO DATA;;
      (_cells._List_List_Main..PlayerMark___@box (bsqobject__cells._List_List_Main..PlayerMark____value _cells._List_List_Main..PlayerMark___))
      (ListOps@box (bsqobject_ListOps_value ListOps))
      (Main..Board@box (bsqobject_Main..Board_value Main..Board))
      (Main..BoardPostion@box (bsqobject_Main..BoardPostion_value Main..BoardPostion))
      (List_Bool_@box (bsqobject_List_Bool__value List_Bool_))
      (List_List_Main..PlayerMark__@box (bsqobject_List_List_Main..PlayerMark___value List_List_Main..PlayerMark__))
      (List_Main..PlayerMark_@box (bsqobject_List_Main..PlayerMark__value List_Main..PlayerMark_))
    )
    ( 
      (BTerm@termbox (BTerm_termtype TypeTag) (BTerm_termvalue bsq_object))
      (BTerm@keybox (BTerm_keyvalue BKey)) 
    )
))

(declare-const BTerm@none BTerm)
(assert (= BTerm@none (BTerm@keybox BKey@none)))

(declare-const BTerm@nothing BTerm)
(assert (= BTerm@nothing (BTerm@termbox TypeTag_Nothing bsqobject_nothing@literal)))

;;
;;Define utility functions
;;
(define-fun GetTypeTag@BKey ((t BKey)) TypeTag
  (BKey_type t)
)

(define-fun GetTypeTag@BTerm ((t BTerm)) TypeTag
  (ite ((_ is BTerm@termbox) t) (BTerm_termtype t) (BKey_type (BTerm_keyvalue t)))
)

;;
;; Ephemeral datatypes
;;
(declare-datatypes (
    (elistnull 0)
    ;;NO DATA;;
    ) (
    ( (elistnull@cons) )
    ;;NO DATA;;
))

(declare-datatypes (
      (ErrorID 0)
    ) (
    ( 
      (ErrorID_AssumeCheck)
      (ErrorID_Target)
    )
))

(declare-datatypes (
      ($Result__cells._List_List_Main..PlayerMark___ 0)
      ($Result_BTerm 0)
      ($Result_BBigInt 0)
      ($Result_BBigNat 0)
      ($Result_Bool 0)
      ($Result_BufferCompression 0)
      ($Result_BufferFormat 0)
      ($Result_BByteBuffer 0)
      ($Result_BCalendarDate 0)
      ($Result_BDateTime 0)
      ($Result_BDecimal 0)
      ($Result_BFloat 0)
      ($Result_HavocSequence 0)
      ($Result_BInt 0)
      ($Result_BISOTimeStamp 0)
      ($Result_BKey 0)
      ($Result_BLatLongCoordinate 0)
      ($Result_List_Bool_ 0)
      ($Result_List_List_Main..PlayerMark__ 0)
      ($Result_List_Main..PlayerMark_ 0)
      ($Result_ListOps 0)
      ($Result_BLogicalTime 0)
      ($Result_Main..Board 0)
      ($Result_Main..BoardPostion 0)
      ($Result_Main..PlayerMark 0)
      ($Result_BNat 0)
      ($Result_bsq_none 0)
      ($Result_bsq_nothing 0)
      ($Result_BRational 0)
      ($Result_bsq_regex 0)
      ($Result_BRelativeTime 0)
      ($Result_BSHAContentHash 0)
      ($Result_BString 0)
      ($Result_BTickTime 0)
      ($Result_BUTCDateTime 0)
      ($Result_BUUID4 0)
      ($Result_BUUID7 0)
      ;;NO DATA;;
    ) (
    ( ($Result__cells._List_List_Main..PlayerMark___@success ($Result__cells._List_List_Main..PlayerMark___@success_value _cells._List_List_Main..PlayerMark___)) ($Result__cells._List_List_Main..PlayerMark___@error ($Result__cells._List_List_Main..PlayerMark___@error_value ErrorID)) )
    ( ($Result_BTerm@success ($Result_BTerm@success_value BTerm)) ($Result_BTerm@error ($Result_BTerm@error_value ErrorID)) )
    ( ($Result_BBigInt@success ($Result_BBigInt@success_value BBigInt)) ($Result_BBigInt@error ($Result_BBigInt@error_value ErrorID)) )
    ( ($Result_BBigNat@success ($Result_BBigNat@success_value BBigNat)) ($Result_BBigNat@error ($Result_BBigNat@error_value ErrorID)) )
    ( ($Result_Bool@success ($Result_Bool@success_value Bool)) ($Result_Bool@error ($Result_Bool@error_value ErrorID)) )
    ( ($Result_BufferCompression@success ($Result_BufferCompression@success_value BufferCompression)) ($Result_BufferCompression@error ($Result_BufferCompression@error_value ErrorID)) )
    ( ($Result_BufferFormat@success ($Result_BufferFormat@success_value BufferFormat)) ($Result_BufferFormat@error ($Result_BufferFormat@error_value ErrorID)) )
    ( ($Result_BByteBuffer@success ($Result_BByteBuffer@success_value BByteBuffer)) ($Result_BByteBuffer@error ($Result_BByteBuffer@error_value ErrorID)) )
    ( ($Result_BCalendarDate@success ($Result_BCalendarDate@success_value BCalendarDate)) ($Result_BCalendarDate@error ($Result_BCalendarDate@error_value ErrorID)) )
    ( ($Result_BDateTime@success ($Result_BDateTime@success_value BDateTime)) ($Result_BDateTime@error ($Result_BDateTime@error_value ErrorID)) )
    ( ($Result_BDecimal@success ($Result_BDecimal@success_value BDecimal)) ($Result_BDecimal@error ($Result_BDecimal@error_value ErrorID)) )
    ( ($Result_BFloat@success ($Result_BFloat@success_value BFloat)) ($Result_BFloat@error ($Result_BFloat@error_value ErrorID)) )
    ( ($Result_HavocSequence@success ($Result_HavocSequence@success_value HavocSequence)) ($Result_HavocSequence@error ($Result_HavocSequence@error_value ErrorID)) )
    ( ($Result_BInt@success ($Result_BInt@success_value BInt)) ($Result_BInt@error ($Result_BInt@error_value ErrorID)) )
    ( ($Result_BISOTimeStamp@success ($Result_BISOTimeStamp@success_value BISOTimeStamp)) ($Result_BISOTimeStamp@error ($Result_BISOTimeStamp@error_value ErrorID)) )
    ( ($Result_BKey@success ($Result_BKey@success_value BKey)) ($Result_BKey@error ($Result_BKey@error_value ErrorID)) )
    ( ($Result_BLatLongCoordinate@success ($Result_BLatLongCoordinate@success_value BLatLongCoordinate)) ($Result_BLatLongCoordinate@error ($Result_BLatLongCoordinate@error_value ErrorID)) )
    ( ($Result_List_Bool_@success ($Result_List_Bool_@success_value List_Bool_)) ($Result_List_Bool_@error ($Result_List_Bool_@error_value ErrorID)) )
    ( ($Result_List_List_Main..PlayerMark__@success ($Result_List_List_Main..PlayerMark__@success_value List_List_Main..PlayerMark__)) ($Result_List_List_Main..PlayerMark__@error ($Result_List_List_Main..PlayerMark__@error_value ErrorID)) )
    ( ($Result_List_Main..PlayerMark_@success ($Result_List_Main..PlayerMark_@success_value List_Main..PlayerMark_)) ($Result_List_Main..PlayerMark_@error ($Result_List_Main..PlayerMark_@error_value ErrorID)) )
    ( ($Result_ListOps@success ($Result_ListOps@success_value ListOps)) ($Result_ListOps@error ($Result_ListOps@error_value ErrorID)) )
    ( ($Result_BLogicalTime@success ($Result_BLogicalTime@success_value BLogicalTime)) ($Result_BLogicalTime@error ($Result_BLogicalTime@error_value ErrorID)) )
    ( ($Result_Main..Board@success ($Result_Main..Board@success_value Main..Board)) ($Result_Main..Board@error ($Result_Main..Board@error_value ErrorID)) )
    ( ($Result_Main..BoardPostion@success ($Result_Main..BoardPostion@success_value Main..BoardPostion)) ($Result_Main..BoardPostion@error ($Result_Main..BoardPostion@error_value ErrorID)) )
    ( ($Result_Main..PlayerMark@success ($Result_Main..PlayerMark@success_value Main..PlayerMark)) ($Result_Main..PlayerMark@error ($Result_Main..PlayerMark@error_value ErrorID)) )
    ( ($Result_BNat@success ($Result_BNat@success_value BNat)) ($Result_BNat@error ($Result_BNat@error_value ErrorID)) )
    ( ($Result_bsq_none@success ($Result_bsq_none@success_value bsq_none)) ($Result_bsq_none@error ($Result_bsq_none@error_value ErrorID)) )
    ( ($Result_bsq_nothing@success ($Result_bsq_nothing@success_value bsq_nothing)) ($Result_bsq_nothing@error ($Result_bsq_nothing@error_value ErrorID)) )
    ( ($Result_BRational@success ($Result_BRational@success_value BRational)) ($Result_BRational@error ($Result_BRational@error_value ErrorID)) )
    ( ($Result_bsq_regex@success ($Result_bsq_regex@success_value bsq_regex)) ($Result_bsq_regex@error ($Result_bsq_regex@error_value ErrorID)) )
    ( ($Result_BRelativeTime@success ($Result_BRelativeTime@success_value BRelativeTime)) ($Result_BRelativeTime@error ($Result_BRelativeTime@error_value ErrorID)) )
    ( ($Result_BSHAContentHash@success ($Result_BSHAContentHash@success_value BSHAContentHash)) ($Result_BSHAContentHash@error ($Result_BSHAContentHash@error_value ErrorID)) )
    ( ($Result_BString@success ($Result_BString@success_value BString)) ($Result_BString@error ($Result_BString@error_value ErrorID)) )
    ( ($Result_BTickTime@success ($Result_BTickTime@success_value BTickTime)) ($Result_BTickTime@error ($Result_BTickTime@error_value ErrorID)) )
    ( ($Result_BUTCDateTime@success ($Result_BUTCDateTime@success_value BUTCDateTime)) ($Result_BUTCDateTime@error ($Result_BUTCDateTime@error_value ErrorID)) )
    ( ($Result_BUUID4@success ($Result_BUUID4@success_value BUUID4)) ($Result_BUUID4@error ($Result_BUUID4@error_value ErrorID)) )
    ( ($Result_BUUID7@success ($Result_BUUID7@success_value BUUID7)) ($Result_BUUID7@error ($Result_BUUID7@error_value ErrorID)) )
    ;;NO DATA;;
))

;;
;;Free constructors for entrypoint initialization
;;
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
(declare-fun UnionChoice@UFCons_API (HavocSequence) BNat)

(define-fun _@@cons_None_entrypoint ((ctx HavocSequence)) $Result_bsq_none
  ($Result_bsq_none@success bsq_none@literal)
)

(define-fun _@@cons_Nothing_entrypoint ((ctx HavocSequence)) $Result_bsq_nothing
  ($Result_bsq_nothing@success bsq_nothing@literal)
)

;;@BINTMIN, @BINTMAX, @BNATMAX, @SLENMAX, @BLENMAX
(declare-const @BINTMIN Int) (assert (= @BINTMIN -32768))
(declare-const @BINTMAX Int) (assert (= @BINTMAX 32767))
(declare-const @BNATMAX Int) (assert (= @BNATMAX 65535))
(declare-const @SLENMAX Int) (assert (= @SLENMAX 48))
(declare-const @BLENMAX Int) (assert (= @BLENMAX 32))
(declare-const @CONTAINERMAX Int) (assert (= @CONTAINERMAX 3))

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

(define-fun _@@cons_RelativeTime_entrypoint ((ctx HavocSequence)) $Result_BRelativeTime
  (let ((hh (BDateHour@UFCons_API (seq.++ ctx (seq.unit 3)))) (mm (BDateMinute@UFCons_API (seq.++ ctx (seq.unit 4)))))
    (ite (and (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59))
      ($Result_BRelativeTime@success (BRelativeTime@cons hh mm))
      ($Result_BRelativeTime@error ErrorID_AssumeCheck) 
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
  (let ((lat (BFloat@UFCons_API (seq.++ ctx (seq.unit 0)))) (long (BFloat@UFCons_API (seq.++ ctx (seq.unit 1)))))
    (ite (and (<= -90.0 lat) (<= lat 90.0) (< -180.0 long) (<= long 180.0))
      ($Result_BLatLongCoordinate@success (BLatLongCoordinate@cons lat long))
      ($Result_BLatLongCoordinate@error ErrorID_AssumeCheck) 
    )
  )
)

(declare-fun @@SortedIntSeq@@Create (Int Int Int) (Seq Int))

(define-fun @@CheckIntSeqLen ((s (Seq Int)) (len Int)) Bool
  (= (seq.len s) len)
)

(define-fun @@CheckIntSeqSorted ((s (Seq Int)) (start Int) (len Int)) Bool
  (forall ((i Int)) (=> (and (<= 0 i) (< i len)) (= (seq.nth s i) (+ start i))))
)

(declare-const List_Bool_@@empty List_Bool_) (assert (= List_Bool_@@empty (List_Bool_@cons (as seq.empty (Seq Bool)))))
(declare-const List_List_Main..PlayerMark__@@empty List_List_Main..PlayerMark__) (assert (= List_List_Main..PlayerMark__@@empty (List_List_Main..PlayerMark__@cons (as seq.empty (Seq List_Main..PlayerMark_)))))
(declare-const List_Main..PlayerMark_@@empty List_Main..PlayerMark_) (assert (= List_Main..PlayerMark_@@empty (List_Main..PlayerMark_@cons (as seq.empty (Seq Main..PlayerMark)))))
(declare-const Main..BoardPostion..r0c0 Main..BoardPostion)
(declare-const Main..BoardPostion..r0c1 Main..BoardPostion)
(declare-const Main..BoardPostion..r0c2 Main..BoardPostion)
(declare-const Main..BoardPostion..r1c0 Main..BoardPostion)
(declare-const Main..BoardPostion..r1c1 Main..BoardPostion)
(declare-const Main..BoardPostion..r1c2 Main..BoardPostion)
(declare-const Main..BoardPostion..r2c0 Main..BoardPostion)
(declare-const Main..BoardPostion..r2c1 Main..BoardPostion)
(declare-const Main..BoardPostion..r2c2 Main..BoardPostion)
(declare-const Main..PlayerMark..empty Main..PlayerMark)
(declare-const Main..PlayerMark..o Main..PlayerMark)
(declare-const Main..PlayerMark..x Main..PlayerMark)

;;NO DATA;;

(define-fun $ListSingletonCons_3_List_Main..PlayerMark_ ((arg0 Main..PlayerMark) (arg1 Main..PlayerMark) (arg2 Main..PlayerMark)) List_Main..PlayerMark_
(List_Main..PlayerMark_@cons (seq.++ (seq.unit arg0) (seq.unit arg1) (seq.unit arg2)))
)

(define-fun $ListSingletonCons_3_List_List_Main..PlayerMark__ ((arg0 List_Main..PlayerMark_) (arg1 List_Main..PlayerMark_) (arg2 List_Main..PlayerMark_)) List_List_Main..PlayerMark__
(List_List_Main..PlayerMark__@cons (seq.++ (seq.unit arg0) (seq.unit arg1) (seq.unit arg2)))
)

(define-fun Main..Board..create4 () _cells._List_List_Main..PlayerMark___
(let ((@tmp_2 ($ListSingletonCons_3_List_Main..PlayerMark_ Main..PlayerMark..x Main..PlayerMark..x Main..PlayerMark..empty)))
    (let ((@tmp_6 ($ListSingletonCons_3_List_Main..PlayerMark_ Main..PlayerMark..o Main..PlayerMark..o Main..PlayerMark..empty)))
      (let ((@tmp_10 ($ListSingletonCons_3_List_Main..PlayerMark_ Main..PlayerMark..empty Main..PlayerMark..empty Main..PlayerMark..empty)))
        (let ((@tmp_1 ($ListSingletonCons_3_List_List_Main..PlayerMark__ @tmp_2 @tmp_6 @tmp_10)))
          (let ((@tmp_0 (_cells._List_List_Main..PlayerMark___@cons @tmp_1)))
            (let (($__ir_ret__ @tmp_0))
              (let (($return $__ir_ret__))
                $return
              )
            )
          )
        )
      )
    )
  )
)

(define-fun ListOps..s_list_empty_T_List_Main..PlayerMark__ ((l List_List_Main..PlayerMark__)) Bool
(= l List_List_Main..PlayerMark__@@empty)
)

(define-fun ListOps..s_list_size_T_List_Main..PlayerMark__ ((l List_List_Main..PlayerMark__)) BNat
(seq.len (List_List_Main..PlayerMark___seq l))
)

(define-fun List_List_Main..PlayerMark__..size_T_List_Main..PlayerMark__ ((this List_List_Main..PlayerMark__)) BNat
(let ((@tmp_0 (ListOps..s_list_empty_T_List_Main..PlayerMark__ this)))
    (ite @tmp_0
      (let (($__ir_ret__$1 0))
        (let (($__ir_ret__$2 $__ir_ret__$1))
          (let (($return $__ir_ret__$2))
            $return
          )
        )
      )
      (let ((@tmp_3 (ListOps..s_list_size_T_List_Main..PlayerMark__ this)))
        (let (($__ir_ret__ @tmp_3))
          (let (($__ir_ret__$2 $__ir_ret__))
            (let (($return $__ir_ret__$2))
              $return
            )
          )
        )
      )
    )
  )
)

(define-fun tictactoe.bsq_k14_invariant@0..45@1342..invariant@0 (($cells List_List_Main..PlayerMark__)) Bool
(let ((@tmp_3 (List_List_Main..PlayerMark__..size_T_List_Main..PlayerMark__ $cells)))
    (let ((@tmp_0 (= @tmp_3 3)))
      (let (($__ir_ret__ @tmp_0))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun ListOps..s_list_get_T_List_Main..PlayerMark__ ((l List_List_Main..PlayerMark__) (idx BNat)) List_Main..PlayerMark_
(seq.nth (List_List_Main..PlayerMark___seq l) idx)
)

(define-fun ListOps..s_list_empty_T_Main..PlayerMark_ ((l List_Main..PlayerMark_)) Bool
(= l List_Main..PlayerMark_@@empty)
)

(define-fun ListOps..s_list_size_T_Main..PlayerMark_ ((l List_Main..PlayerMark_)) BNat
(seq.len (List_Main..PlayerMark__seq l))
)

(define-fun List_Main..PlayerMark_..size_T_Main..PlayerMark_ ((this List_Main..PlayerMark_)) BNat
(let ((@tmp_0 (ListOps..s_list_empty_T_Main..PlayerMark_ this)))
    (ite @tmp_0
      (let (($__ir_ret__$1 0))
        (let (($__ir_ret__$2 $__ir_ret__$1))
          (let (($return $__ir_ret__$2))
            $return
          )
        )
      )
      (let ((@tmp_3 (ListOps..s_list_size_T_Main..PlayerMark_ this)))
        (let (($__ir_ret__ @tmp_3))
          (let (($__ir_ret__$2 $__ir_ret__))
            (let (($return $__ir_ret__$2))
              $return
            )
          )
        )
      )
    )
  )
)

(define-fun pred--tictactoe.bsq_k14..46@1399 ((row List_Main..PlayerMark_)) Bool
(let ((@tmp_3 (List_Main..PlayerMark_..size_T_Main..PlayerMark_ row)))
    (let ((@tmp_0 (= @tmp_3 3)))
      (let (($__ir_ret__ @tmp_0))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun $ListSingletonCons_1_List_Bool_ ((arg0 Bool)) List_Bool_
(List_Bool_@cons (seq.++ (seq.unit arg0)))
)

(define-fun $ListSingletonCons_2_List_Bool_ ((arg0 Bool) (arg1 Bool)) List_Bool_
(List_Bool_@cons (seq.++ (seq.unit arg0) (seq.unit arg1)))
)

(define-fun $ListSingletonCons_3_List_Bool_ ((arg0 Bool) (arg1 Bool) (arg2 Bool)) List_Bool_
(List_Bool_@cons (seq.++ (seq.unit arg0) (seq.unit arg1) (seq.unit arg2)))
)

(define-fun $ListSingletonCons_4_List_Bool_ ((arg0 Bool) (arg1 Bool) (arg2 Bool) (arg3 Bool)) List_Bool_
(List_Bool_@cons (seq.++ (seq.unit arg0) (seq.unit arg1) (seq.unit arg2) (seq.unit arg3)))
)

(define-fun ListOps..s_list_map_pred_c4_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ ((l List_List_Main..PlayerMark__) (count BNat)) List_Bool_
(let ((@tmp_1 (ListOps..s_list_get_T_List_Main..PlayerMark__ l 0)))
    (let ((@tmp_0 (pred--tictactoe.bsq_k14..46@1399 @tmp_1)))
      (let ((p0 @tmp_0))
        (let ((@tmp_4 (= count 1)))
          (ite @tmp_4
            (let ((@tmp_7 ($ListSingletonCons_1_List_Bool_ p0)))
              (let (($__ir_ret__$3 @tmp_7))
                (let (($__ir_ret__$4 $__ir_ret__$3))
                  (let (($return $__ir_ret__$4))
                    $return
                  )
                )
              )
            )
            (let ((@tmp_10 (ListOps..s_list_get_T_List_Main..PlayerMark__ l 1)))
              (let ((@tmp_9 (pred--tictactoe.bsq_k14..46@1399 @tmp_10)))
                (let ((p1 @tmp_9))
                  (let ((@tmp_13 (= count 2)))
                    (ite @tmp_13
                      (let ((@tmp_16 ($ListSingletonCons_2_List_Bool_ p0 p1)))
                        (let (($__ir_ret__$2 @tmp_16))
                          (let (($__ir_ret__$4 $__ir_ret__$2))
                            (let (($return $__ir_ret__$4))
                              $return
                            )
                          )
                        )
                      )
                      (let ((@tmp_20 (ListOps..s_list_get_T_List_Main..PlayerMark__ l 2)))
                        (let ((@tmp_19 (pred--tictactoe.bsq_k14..46@1399 @tmp_20)))
                          (let ((p2 @tmp_19))
                            (let ((@tmp_23 (= count 3)))
                              (ite @tmp_23
                                (let ((@tmp_26 ($ListSingletonCons_3_List_Bool_ p0 p1 p2)))
                                  (let (($__ir_ret__$1 @tmp_26))
                                    (let (($__ir_ret__$4 $__ir_ret__$1))
                                      (let (($return $__ir_ret__$4))
                                        $return
                                      )
                                    )
                                  )
                                )
                                (let ((@tmp_31 (ListOps..s_list_get_T_List_Main..PlayerMark__ l 3)))
                                  (let ((@tmp_30 (pred--tictactoe.bsq_k14..46@1399 @tmp_31)))
                                    (let ((p3 @tmp_30))
                                      (let ((@tmp_34 ($ListSingletonCons_4_List_Bool_ p0 p1 p2 @tmp_30)))
                                        (let (($__ir_ret__ @tmp_34))
                                          (let (($__ir_ret__$4 $__ir_ret__))
                                            (let (($return $__ir_ret__$4))
                                              $return
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun ListOps..s_list_slice_end_T_List_Main..PlayerMark__ ((l List_List_Main..PlayerMark__) (idx BNat)) List_List_Main..PlayerMark__
(List_List_Main..PlayerMark__@cons (seq.extract (List_List_Main..PlayerMark___seq l) 0 idx))
)

(define-fun ListOps..s_list_slice_front_T_List_Main..PlayerMark__ ((l List_List_Main..PlayerMark__) (idx BNat)) List_List_Main..PlayerMark__
(List_List_Main..PlayerMark__@cons (seq.extract (List_List_Main..PlayerMark___seq l) idx (- (seq.len (List_List_Main..PlayerMark___seq (List_List_Main..PlayerMark___seq l))) idx)))
)

(define-fun ListOps..s_list_append_T_Bool_ ((l List_Bool_) (r List_Bool_)) List_Bool_
(List_Bool_@cons (seq.++ (List_Bool__seq l) (List_Bool__seq r)))
)

(define-fun ListOps..s_list_map_pred_c8_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ ((l List_List_Main..PlayerMark__) (count BNat)) $Result_List_Bool_
(let ((@tmp_0 (<= count 4)))
    (ite @tmp_0
      (let ((@tmp_3 (ListOps..s_list_map_pred_c4_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ l count)))
        (let (($__ir_ret__$1 @tmp_3))
          (let (($__ir_ret__$2 $__ir_ret__$1))
            (let (($return $__ir_ret__$2))
              ($Result_List_Bool_@success $return)
            )
          )
        )
      )
      (let ((@tmp_7 (ListOps..s_list_slice_end_T_List_Main..PlayerMark__ l 4)))
        (let ((ll @tmp_7))
          (let ((@tmp_10 (ListOps..s_list_map_pred_c4_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ @tmp_7 4)))
            (let ((resl @tmp_10))
              (let ((@tmp_14 (ListOps..s_list_slice_front_T_List_Main..PlayerMark__ l 4)))
                (let ((lr @tmp_14))
                  (let ((_@tmpvar@9 (ite (< 4 count) ($Result_BNat@error ErrorID_AssumeCheck) ($Result_BNat@success (- count 4)))))
                    (ite ((_ is $Result_BNat@error) _@tmpvar@9)
                      ($Result_List_Bool_@error ($Result_BNat@error_value _@tmpvar@9))
                      (let ((@tmp_19 ($Result_BNat@success_value _@tmpvar@9)))
                        (let ((@tmp_17 (ListOps..s_list_map_pred_c4_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ @tmp_14 @tmp_19)))
                          (let ((resr @tmp_17))
                            (let ((@tmp_23 (ListOps..s_list_append_T_Bool_ @tmp_10 @tmp_17)))
                              (let (($__ir_ret__ @tmp_23))
                                (let (($__ir_ret__$2 $__ir_ret__))
                                  (let (($return $__ir_ret__$2))
                                    ($Result_List_Bool_@success $return)
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun ListOps..s_list_map_pred_c16_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ ((l List_List_Main..PlayerMark__) (count BNat)) $Result_List_Bool_
(let ((@tmp_0 (<= count 8)))
    (ite @tmp_0
      (let ((_@tmpvar@10 (ListOps..s_list_map_pred_c8_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ l count)))
        (ite ((_ is $Result_List_Bool_@error) _@tmpvar@10)
          _@tmpvar@10
          (let ((@tmp_3 ($Result_List_Bool_@success_value _@tmpvar@10)))
            (let (($__ir_ret__$1 @tmp_3))
              (let (($__ir_ret__$2 $__ir_ret__$1))
                (let (($return $__ir_ret__$2))
                  ($Result_List_Bool_@success $return)
                )
              )
            )
          )
        )
      )
      (let ((@tmp_7 (ListOps..s_list_slice_end_T_List_Main..PlayerMark__ l 8)))
        (let ((ll @tmp_7))
          (let ((_@tmpvar@13 (ListOps..s_list_map_pred_c8_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ @tmp_7 8)))
            (ite ((_ is $Result_List_Bool_@error) _@tmpvar@13)
              _@tmpvar@13
              (let ((@tmp_10 ($Result_List_Bool_@success_value _@tmpvar@13)))
                (let ((resl @tmp_10))
                  (let ((@tmp_14 (ListOps..s_list_slice_front_T_List_Main..PlayerMark__ l 8)))
                    (let ((lr @tmp_14))
                      (let ((_@tmpvar@12 (ite (< 8 count) ($Result_BNat@error ErrorID_AssumeCheck) ($Result_BNat@success (- count 8)))))
                        (ite ((_ is $Result_BNat@error) _@tmpvar@12)
                          ($Result_List_Bool_@error ($Result_BNat@error_value _@tmpvar@12))
                          (let ((@tmp_19 ($Result_BNat@success_value _@tmpvar@12)))
                            (let ((_@tmpvar@11 (ListOps..s_list_map_pred_c8_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ @tmp_14 @tmp_19)))
                              (ite ((_ is $Result_List_Bool_@error) _@tmpvar@11)
                                _@tmpvar@11
                                (let ((@tmp_17 ($Result_List_Bool_@success_value _@tmpvar@11)))
                                  (let ((resr @tmp_17))
                                    (let ((@tmp_23 (ListOps..s_list_append_T_Bool_ @tmp_10 @tmp_17)))
                                      (let (($__ir_ret__ @tmp_23))
                                        (let (($__ir_ret__$2 $__ir_ret__))
                                          (let (($return $__ir_ret__$2))
                                            ($Result_List_Bool_@success $return)
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun ListOps..s_list_map_pred_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ ((l List_List_Main..PlayerMark__)) $Result_List_Bool_
(let ((@tmp_0 (ListOps..s_list_size_T_List_Main..PlayerMark__ l)))
    (let ((count @tmp_0))
      (let ((@tmp_2 (<= @tmp_0 4)))
        (ite @tmp_2
          (let ((@tmp_5 (ListOps..s_list_map_pred_c4_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ l count)))
            (let (($__ir_ret__$1 @tmp_5))
              (let (($__ir_ret__$2 $__ir_ret__$1))
                (let (($return $__ir_ret__$2))
                  ($Result_List_Bool_@success $return)
                )
              )
            )
          )
          (let ((_@tmpvar@14 (ListOps..s_list_map_pred_c16_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ l count)))
            (ite ((_ is $Result_List_Bool_@error) _@tmpvar@14)
              _@tmpvar@14
              (let ((@tmp_9 ($Result_List_Bool_@success_value _@tmpvar@14)))
                (let (($__ir_ret__ @tmp_9))
                  (let (($__ir_ret__$2 $__ir_ret__))
                    (let (($return $__ir_ret__$2))
                      ($Result_List_Bool_@success $return)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun ListOps..s_list_all_true ((l List_Bool_)) Bool
(not (seq.contains (List_Bool__seq l) (seq.unit false)))
)

(define-fun List_List_Main..PlayerMark__..allOf_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ ((this List_List_Main..PlayerMark__)) $Result_Bool
(let ((@tmp_0 (ListOps..s_list_empty_T_List_Main..PlayerMark__ this)))
    (ite @tmp_0
      (let (($__ir_ret__$1 true))
        (let (($__ir_ret__$2 $__ir_ret__$1))
          (let (($return $__ir_ret__$2))
            ($Result_Bool@success $return)
          )
        )
      )
      (let ((_@tmpvar@15 (ListOps..s_list_map_pred_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ this)))
        (ite ((_ is $Result_List_Bool_@error) _@tmpvar@15)
          ($Result_Bool@error ($Result_List_Bool_@error_value _@tmpvar@15))
          (let ((@tmp_3 ($Result_List_Bool_@success_value _@tmpvar@15)))
            (let ((mask @tmp_3))
              (let ((@tmp_6 (ListOps..s_list_all_true @tmp_3)))
                (let (($__ir_ret__ @tmp_6))
                  (let (($__ir_ret__$2 $__ir_ret__))
                    (let (($return $__ir_ret__$2))
                      ($Result_Bool@success $return)
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun tictactoe.bsq_k14_invariant@1..46@1382..invariant@1 (($cells List_List_Main..PlayerMark__)) $Result_Bool
(let ((_@tmpvar@16 (List_List_Main..PlayerMark__..allOf_T_List_Main..PlayerMark___pred--tictactoe.bsq_k14..46@1399_ $cells)))
    (ite ((_ is $Result_Bool@error) _@tmpvar@16)
      _@tmpvar@16
      (let ((@tmp_2 ($Result_Bool@success_value _@tmpvar@16)))
        (let (($__ir_ret__ @tmp_2))
          (let (($return $__ir_ret__))
            ($Result_Bool@success $return)
          )
        )
      )
    )
  )
)

(define-fun Main..Board..@@constructor (($cells List_List_Main..PlayerMark__)) $Result_Main..Board
(let ((@tmp_0 (tictactoe.bsq_k14_invariant@0..45@1342..invariant@0 $cells)))
    (ite @tmp_0
      (let ((_@tmpvar@17 (tictactoe.bsq_k14_invariant@1..46@1382..invariant@1 $cells)))
        (ite ((_ is $Result_Bool@error) _@tmpvar@17)
          ($Result_Main..Board@error ($Result_Bool@error_value _@tmpvar@17))
          (let ((@tmp_1 ($Result_Bool@success_value _@tmpvar@17)))
            (ite @tmp_1
              (let (($__ir_ret__ (Main..Board@cons $cells)))
                (let (($return $__ir_ret__))
                  ($Result_Main..Board@success $return)
                )
              )
              ($Result_Main..Board@error ErrorID_AssumeCheck)
            )
          )
        )
      )
      ($Result_Main..Board@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun tictactoe.bsq_k14_invariant@0..25@676..invariant@0 (($rowpos BNat)) Bool
(let ((@tmp_0 (< $rowpos 3)))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun tictactoe.bsq_k14_invariant@1..26@704..invariant@1 (($colpos BNat)) Bool
(let ((@tmp_0 (< $colpos 3)))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun Main..BoardPostion..@@constructor (($rowpos BNat) ($colpos BNat)) $Result_Main..BoardPostion
(let ((@tmp_0 (tictactoe.bsq_k14_invariant@0..25@676..invariant@0 $rowpos)))
    (ite @tmp_0
      (let ((@tmp_1 (tictactoe.bsq_k14_invariant@1..26@704..invariant@1 $colpos)))
        (ite @tmp_1
          (let (($__ir_ret__ (Main..BoardPostion@cons $rowpos $colpos)))
            (let (($return $__ir_ret__))
              ($Result_Main..BoardPostion@success $return)
            )
          )
          ($Result_Main..BoardPostion@error ErrorID_AssumeCheck)
        )
      )
      ($Result_Main..BoardPostion@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun list.bsq_k1_pre@0..182@5266..pre@0_T_List_Main..PlayerMark__ ((this List_List_Main..PlayerMark__) (i BNat)) Bool
(let ((@tmp_2 (ListOps..s_list_size_T_List_Main..PlayerMark__ this)))
    (let ((@tmp_0 (< i @tmp_2)))
      (let (($__ir_ret__ @tmp_0))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun List_List_Main..PlayerMark__..get_T_List_Main..PlayerMark__ ((this List_List_Main..PlayerMark__) (i BNat)) $Result_List_Main..PlayerMark_
(let ((@tmp_0 (list.bsq_k1_pre@0..182@5266..pre@0_T_List_Main..PlayerMark__ this i)))
    (ite @tmp_0
      (let ((@tmp_1 (ListOps..s_list_get_T_List_Main..PlayerMark__ this i)))
        (let (($__ir_ret__ @tmp_1))
          (let (($return $__ir_ret__))
            ($Result_List_Main..PlayerMark_@success $return)
          )
        )
      )
      ($Result_List_Main..PlayerMark_@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun list.bsq_k1_pre@0..182@5266..pre@0_T_Main..PlayerMark_ ((this List_Main..PlayerMark_) (i BNat)) Bool
(let ((@tmp_2 (ListOps..s_list_size_T_Main..PlayerMark_ this)))
    (let ((@tmp_0 (< i @tmp_2)))
      (let (($__ir_ret__ @tmp_0))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun ListOps..s_list_get_T_Main..PlayerMark_ ((l List_Main..PlayerMark_) (idx BNat)) Main..PlayerMark
(seq.nth (List_Main..PlayerMark__seq l) idx)
)

(define-fun List_Main..PlayerMark_..get_T_Main..PlayerMark_ ((this List_Main..PlayerMark_) (i BNat)) $Result_Main..PlayerMark
(let ((@tmp_0 (list.bsq_k1_pre@0..182@5266..pre@0_T_Main..PlayerMark_ this i)))
    (ite @tmp_0
      (let ((@tmp_1 (ListOps..s_list_get_T_Main..PlayerMark_ this i)))
        (let (($__ir_ret__ @tmp_1))
          (let (($return $__ir_ret__))
            ($Result_Main..PlayerMark@success $return)
          )
        )
      )
      ($Result_Main..PlayerMark@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..Board..isCellEmpty ((this Main..Board) (c Main..BoardPostion)) $Result_Bool
(let ((@tmp_3 (Main..Board@_cells this)))
    (let ((@tmp_7 (Main..BoardPostion@_rowpos c)))
      (let ((_@tmpvar@19 (List_List_Main..PlayerMark__..get_T_List_Main..PlayerMark__ @tmp_3 @tmp_7)))
        (ite ((_ is $Result_List_Main..PlayerMark_@error) _@tmpvar@19)
          ($Result_Bool@error ($Result_List_Main..PlayerMark_@error_value _@tmpvar@19))
          (let ((@tmp_4 ($Result_List_Main..PlayerMark_@success_value _@tmpvar@19)))
            (let ((@tmp_11 (Main..BoardPostion@_colpos c)))
              (let ((_@tmpvar@18 (List_Main..PlayerMark_..get_T_Main..PlayerMark_ @tmp_4 @tmp_11)))
                (ite ((_ is $Result_Main..PlayerMark@error) _@tmpvar@18)
                  ($Result_Bool@error ($Result_Main..PlayerMark@error_value _@tmpvar@18))
                  (let ((@tmp_8 ($Result_Main..PlayerMark@success_value _@tmpvar@18)))
                    (let ((@tmp_0 (= @tmp_8 Main..PlayerMark..empty)))
                      (let (($__ir_ret__ @tmp_0))
                        (let (($return $__ir_ret__))
                          ($Result_Bool@success $return)
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun tictactoe.bsq_k14_pre@0..78@2532..pre@0 ((this Main..Board) (c Main..BoardPostion) (mark Main..PlayerMark)) $Result_Bool
(let ((_@tmpvar@20 (Main..Board..isCellEmpty this c)))
    (ite ((_ is $Result_Bool@error) _@tmpvar@20)
      _@tmpvar@20
      (let ((@tmp_2 ($Result_Bool@success_value _@tmpvar@20)))
        (let (($__ir_ret__ @tmp_2))
          (let (($return $__ir_ret__))
            ($Result_Bool@success $return)
          )
        )
      )
    )
  )
)

(define-fun list.bsq_k1_pre@0..2735@85479..pre@0_T_Main..PlayerMark_ ((this List_Main..PlayerMark_) (i BNat) (v Main..PlayerMark)) Bool
(let ((@tmp_2 (ListOps..s_list_size_T_Main..PlayerMark_ this)))
    (let ((@tmp_0 (< i @tmp_2)))
      (let (($__ir_ret__ @tmp_0))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun ListOps..s_list_set_T_Main..PlayerMark_ ((l List_Main..PlayerMark_) (idx BNat) (v Main..PlayerMark)) List_Main..PlayerMark_
(let ((sval (List_Main..PlayerMark__seq l)))
    (List_Main..PlayerMark_@cons (seq.++ (seq.extract sval 0 idx) (seq.unit v) (seq.extract sval (+ idx 1) (- (seq.len (List_Main..PlayerMark__seq l)) (+ idx 1)))))
  )
)

(define-fun List_Main..PlayerMark_..set_T_Main..PlayerMark_ ((this List_Main..PlayerMark_) (i BNat) (v Main..PlayerMark)) $Result_List_Main..PlayerMark_
(let ((@tmp_0 (list.bsq_k1_pre@0..2735@85479..pre@0_T_Main..PlayerMark_ this i v)))
    (ite @tmp_0
      (let ((@tmp_1 (ListOps..s_list_set_T_Main..PlayerMark_ this i v)))
        (let (($__ir_ret__ @tmp_1))
          (let (($return $__ir_ret__))
            ($Result_List_Main..PlayerMark_@success $return)
          )
        )
      )
      ($Result_List_Main..PlayerMark_@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun list.bsq_k1_pre@0..2735@85479..pre@0_T_List_Main..PlayerMark__ ((this List_List_Main..PlayerMark__) (i BNat) (v List_Main..PlayerMark_)) Bool
(let ((@tmp_2 (ListOps..s_list_size_T_List_Main..PlayerMark__ this)))
    (let ((@tmp_0 (< i @tmp_2)))
      (let (($__ir_ret__ @tmp_0))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun ListOps..s_list_set_T_List_Main..PlayerMark__ ((l List_List_Main..PlayerMark__) (idx BNat) (v List_Main..PlayerMark_)) List_List_Main..PlayerMark__
(let ((sval (List_List_Main..PlayerMark___seq l)))
    (List_List_Main..PlayerMark__@cons (seq.++ (seq.extract sval 0 idx) (seq.unit v) (seq.extract sval (+ idx 1) (- (seq.len (List_List_Main..PlayerMark___seq l)) (+ idx 1)))))
  )
)

(define-fun List_List_Main..PlayerMark__..set_T_List_Main..PlayerMark__ ((this List_List_Main..PlayerMark__) (i BNat) (v List_Main..PlayerMark_)) $Result_List_List_Main..PlayerMark__
(let ((@tmp_0 (list.bsq_k1_pre@0..2735@85479..pre@0_T_List_Main..PlayerMark__ this i v)))
    (ite @tmp_0
      (let ((@tmp_1 (ListOps..s_list_set_T_List_Main..PlayerMark__ this i v)))
        (let (($__ir_ret__ @tmp_1))
          (let (($return $__ir_ret__))
            ($Result_List_List_Main..PlayerMark__@success $return)
          )
        )
      )
      ($Result_List_List_Main..PlayerMark__@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..Board..setCellMark ((this Main..Board) (c Main..BoardPostion) (mark Main..PlayerMark)) $Result_Main..Board
(let ((_@tmpvar@25 (tictactoe.bsq_k14_pre@0..78@2532..pre@0 this c mark)))
    (ite ((_ is $Result_Bool@error) _@tmpvar@25)
      ($Result_Main..Board@error ($Result_Bool@error_value _@tmpvar@25))
      (let ((@tmp_0 ($Result_Bool@success_value _@tmpvar@25)))
        (ite @tmp_0
          (let ((@tmp_3 (Main..Board@_cells this)))
            (let ((@tmp_7 (Main..BoardPostion@_rowpos c)))
              (let ((_@tmpvar@24 (List_List_Main..PlayerMark__..get_T_List_Main..PlayerMark__ @tmp_3 @tmp_7)))
                (ite ((_ is $Result_List_Main..PlayerMark_@error) _@tmpvar@24)
                  ($Result_Main..Board@error ($Result_List_Main..PlayerMark_@error_value _@tmpvar@24))
                  (let ((@tmp_4 ($Result_List_Main..PlayerMark_@success_value _@tmpvar@24)))
                    (let ((@tmp_11 (Main..BoardPostion@_colpos c)))
                      (let ((_@tmpvar@23 (List_Main..PlayerMark_..set_T_Main..PlayerMark_ @tmp_4 @tmp_11 mark)))
                        (ite ((_ is $Result_List_Main..PlayerMark_@error) _@tmpvar@23)
                          ($Result_Main..Board@error ($Result_List_Main..PlayerMark_@error_value _@tmpvar@23))
                          (let ((@tmp_8 ($Result_List_Main..PlayerMark_@success_value _@tmpvar@23)))
                            (let ((newrow @tmp_8))
                              (let ((@tmp_17 (Main..Board@_cells this)))
                                (let (($cells_@2706 @tmp_17))
                                  (let ((@tmp_22 (Main..BoardPostion@_rowpos c)))
                                    (let ((_@tmpvar@22 (List_List_Main..PlayerMark__..set_T_List_Main..PlayerMark__ @tmp_17 @tmp_22 @tmp_8)))
                                      (ite ((_ is $Result_List_List_Main..PlayerMark__@error) _@tmpvar@22)
                                        ($Result_Main..Board@error ($Result_List_List_Main..PlayerMark__@error_value _@tmpvar@22))
                                        (let ((@tmp_19 ($Result_List_List_Main..PlayerMark__@success_value _@tmpvar@22)))
                                          (let ((_@tmpvar@21 (Main..Board..@@constructor @tmp_19)))
                                            (ite ((_ is $Result_Main..Board@error) _@tmpvar@21)
                                              _@tmpvar@21
                                              (let ((@tmp_15 ($Result_Main..Board@success_value _@tmpvar@21)))
                                                (let (($__ir_ret__ @tmp_15))
                                                  (let (($return $__ir_ret__))
                                                    ($Result_Main..Board@success $return)
                                                  )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
          ($Result_Main..Board@error ErrorID_AssumeCheck)
        )
      )
    )
  )
)

(define-fun Main..Board..getCellMark ((this Main..Board) (c Main..BoardPostion)) $Result_Main..PlayerMark
(let ((@tmp_2 (Main..Board@_cells this)))
    (let ((@tmp_6 (Main..BoardPostion@_rowpos c)))
      (let ((_@tmpvar@27 (List_List_Main..PlayerMark__..get_T_List_Main..PlayerMark__ @tmp_2 @tmp_6)))
        (ite ((_ is $Result_List_Main..PlayerMark_@error) _@tmpvar@27)
          ($Result_Main..PlayerMark@error ($Result_List_Main..PlayerMark_@error_value _@tmpvar@27))
          (let ((@tmp_3 ($Result_List_Main..PlayerMark_@success_value _@tmpvar@27)))
            (let ((@tmp_10 (Main..BoardPostion@_colpos c)))
              (let ((_@tmpvar@26 (List_Main..PlayerMark_..get_T_Main..PlayerMark_ @tmp_3 @tmp_10)))
                (ite ((_ is $Result_Main..PlayerMark@error) _@tmpvar@26)
                  _@tmpvar@26
                  (let ((@tmp_7 ($Result_Main..PlayerMark@success_value _@tmpvar@26)))
                    (let (($__ir_ret__ @tmp_7))
                      (let (($return $__ir_ret__))
                        ($Result_Main..PlayerMark@success $return)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun __i__Main..Board..check3$Llogic_and_done_3 ((@tmp_0 Bool)) Bool
(let (($__ir_ret__ @tmp_0))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun __i__Main..Board..check3$Llogic_and_done_5 ((@tmp_7 Bool)) Bool
(let ((@tmp_0 @tmp_7))
    (let (($__ir_ret__ (__i__Main..Board..check3$Llogic_and_done_3 @tmp_0)))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun Main..Board..check3 ((this Main..Board) (c1 Main..BoardPostion) (c2 Main..BoardPostion) (c3 Main..BoardPostion) (player Main..PlayerMark)) $Result_Bool
(let ((_@tmpvar@30 (Main..Board..getCellMark this c1)))
    (ite ((_ is $Result_Main..PlayerMark@error) _@tmpvar@30)
      ($Result_Bool@error ($Result_Main..PlayerMark@error_value _@tmpvar@30))
      (let ((@tmp_4 ($Result_Main..PlayerMark@success_value _@tmpvar@30)))
        (let ((@tmp_1 (= @tmp_4 player)))
          (let ((@tmp_0 @tmp_1))
            (ite @tmp_1
              (let ((_@tmpvar@29 (Main..Board..getCellMark this c2)))
                (ite ((_ is $Result_Main..PlayerMark@error) _@tmpvar@29)
                  ($Result_Bool@error ($Result_Main..PlayerMark@error_value _@tmpvar@29))
                  (let ((@tmp_11 ($Result_Main..PlayerMark@success_value _@tmpvar@29)))
                    (let ((@tmp_8 (= @tmp_11 player)))
                      (let ((@tmp_7 @tmp_8))
                        (ite @tmp_8
                          (let ((_@tmpvar@28 (Main..Board..getCellMark this c3)))
                            (ite ((_ is $Result_Main..PlayerMark@error) _@tmpvar@28)
                              ($Result_Bool@error ($Result_Main..PlayerMark@error_value _@tmpvar@28))
                              (let ((@tmp_17 ($Result_Main..PlayerMark@success_value _@tmpvar@28)))
                                (let ((@tmp_14 (= @tmp_17 player)))
                                  (let ((@tmp_7$1 @tmp_14))
                                    (let (($__ir_ret__$2 (__i__Main..Board..check3$Llogic_and_done_5 @tmp_7$1)))
                                      (let (($__ir_ret__$3 $__ir_ret__$2))
                                        (let (($return $__ir_ret__$3))
                                          ($Result_Bool@success $return)
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                          (let (($__ir_ret__$1 (__i__Main..Board..check3$Llogic_and_done_5 @tmp_7)))
                            (let (($__ir_ret__$3 $__ir_ret__$1))
                              (let (($return $__ir_ret__$3))
                                ($Result_Bool@success $return)
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
              (let (($__ir_ret__ (__i__Main..Board..check3$Llogic_and_done_3 @tmp_0)))
                (let (($__ir_ret__$3 $__ir_ret__))
                  (let (($return $__ir_ret__$3))
                    ($Result_Bool@success $return)
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun __i__Main..Board..checkWinner$Llogic_or_done_18 ((@tmp_48 Bool)) Bool
(ite @tmp_48
    (let (($__ir_ret__$1 true))
      (let (($__ir_ret__$2 $__ir_ret__$1))
        (let (($return $__ir_ret__$2))
          $return
        )
      )
    )
    (let (($__ir_ret__ false))
      (let (($__ir_ret__$2 $__ir_ret__))
        (let (($return $__ir_ret__$2))
          $return
        )
      )
    )
  )
)

(define-fun __i__Main..Board..checkWinner$Llogic_or_done_11 ((@tmp_24 Bool) (player Main..PlayerMark) (this Main..Board)) $Result_Bool
(ite @tmp_24
    (let (($__ir_ret__$2 true))
      (let (($__ir_ret__$3 $__ir_ret__$2))
        (let (($return $__ir_ret__$3))
          ($Result_Bool@success $return)
        )
      )
    )
    (let ((_@tmpvar@32 (Main..Board..check3 this Main..BoardPostion..r0c0 Main..BoardPostion..r1c1 Main..BoardPostion..r2c2 player)))
      (ite ((_ is $Result_Bool@error) _@tmpvar@32)
        _@tmpvar@32
        (let ((@tmp_51 ($Result_Bool@success_value _@tmpvar@32)))
          (let ((@tmp_48 @tmp_51))
            (ite @tmp_51
              (let (($__ir_ret__$1 (__i__Main..Board..checkWinner$Llogic_or_done_18 @tmp_48)))
                (let (($__ir_ret__$3 $__ir_ret__$1))
                  (let (($return $__ir_ret__$3))
                    ($Result_Bool@success $return)
                  )
                )
              )
              (let ((_@tmpvar@31 (Main..Board..check3 this Main..BoardPostion..r0c2 Main..BoardPostion..r1c1 Main..BoardPostion..r2c0 player)))
                (ite ((_ is $Result_Bool@error) _@tmpvar@31)
                  _@tmpvar@31
                  (let ((@tmp_58 ($Result_Bool@success_value _@tmpvar@31)))
                    (let ((@tmp_48$1 @tmp_58))
                      (let (($__ir_ret__ (__i__Main..Board..checkWinner$Llogic_or_done_18 @tmp_48$1)))
                        (let (($__ir_ret__$3 $__ir_ret__))
                          (let (($return $__ir_ret__$3))
                            ($Result_Bool@success $return)
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun __i__Main..Board..checkWinner$Llogic_or_done_13 ((@tmp_32 Bool) (player Main..PlayerMark) (this Main..Board)) $Result_Bool
(let ((@tmp_24 @tmp_32))
    (let ((_@tmpvar@33 (__i__Main..Board..checkWinner$Llogic_or_done_11 @tmp_24 player this)))
      (ite ((_ is $Result_Bool@error) _@tmpvar@33)
        _@tmpvar@33
        (let (($__ir_ret__ ($Result_Bool@success_value _@tmpvar@33)))
          (let (($return $__ir_ret__))
            ($Result_Bool@success $return)
          )
        )
      )
    )
  )
)

(define-fun __i__Main..Board..checkWinner$Llogic_or_done_4 ((@tmp_0 Bool) (player Main..PlayerMark) (this Main..Board)) $Result_Bool
(ite @tmp_0
    (let (($__ir_ret__$3 true))
      (let (($__ir_ret__$4 $__ir_ret__$3))
        (let (($return $__ir_ret__$4))
          ($Result_Bool@success $return)
        )
      )
    )
    (let ((_@tmpvar@39 (Main..Board..check3 this Main..BoardPostion..r0c0 Main..BoardPostion..r1c0 Main..BoardPostion..r2c0 player)))
      (ite ((_ is $Result_Bool@error) _@tmpvar@39)
        _@tmpvar@39
        (let ((@tmp_27 ($Result_Bool@success_value _@tmpvar@39)))
          (let ((@tmp_24 @tmp_27))
            (ite @tmp_27
              (let ((_@tmpvar@38 (__i__Main..Board..checkWinner$Llogic_or_done_11 @tmp_24 player this)))
                (ite ((_ is $Result_Bool@error) _@tmpvar@38)
                  _@tmpvar@38
                  (let (($__ir_ret__$2 ($Result_Bool@success_value _@tmpvar@38)))
                    (let (($__ir_ret__$4 $__ir_ret__$2))
                      (let (($return $__ir_ret__$4))
                        ($Result_Bool@success $return)
                      )
                    )
                  )
                )
              )
              (let ((_@tmpvar@37 (Main..Board..check3 this Main..BoardPostion..r0c1 Main..BoardPostion..r1c1 Main..BoardPostion..r2c1 player)))
                (ite ((_ is $Result_Bool@error) _@tmpvar@37)
                  _@tmpvar@37
                  (let ((@tmp_35 ($Result_Bool@success_value _@tmpvar@37)))
                    (let ((@tmp_32 @tmp_35))
                      (ite @tmp_35
                        (let ((_@tmpvar@36 (__i__Main..Board..checkWinner$Llogic_or_done_13 @tmp_32 player this)))
                          (ite ((_ is $Result_Bool@error) _@tmpvar@36)
                            _@tmpvar@36
                            (let (($__ir_ret__$1 ($Result_Bool@success_value _@tmpvar@36)))
                              (let (($__ir_ret__$4 $__ir_ret__$1))
                                (let (($return $__ir_ret__$4))
                                  ($Result_Bool@success $return)
                                )
                              )
                            )
                          )
                        )
                        (let ((_@tmpvar@35 (Main..Board..check3 this Main..BoardPostion..r0c2 Main..BoardPostion..r1c2 Main..BoardPostion..r2c2 player)))
                          (ite ((_ is $Result_Bool@error) _@tmpvar@35)
                            _@tmpvar@35
                            (let ((@tmp_42 ($Result_Bool@success_value _@tmpvar@35)))
                              (let ((@tmp_32$1 @tmp_42))
                                (let ((_@tmpvar@34 (__i__Main..Board..checkWinner$Llogic_or_done_13 @tmp_32$1 player this)))
                                  (ite ((_ is $Result_Bool@error) _@tmpvar@34)
                                    _@tmpvar@34
                                    (let (($__ir_ret__ ($Result_Bool@success_value _@tmpvar@34)))
                                      (let (($__ir_ret__$4 $__ir_ret__))
                                        (let (($return $__ir_ret__$4))
                                          ($Result_Bool@success $return)
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun __i__Main..Board..checkWinner$Llogic_or_done_6 ((@tmp_8 Bool) (player Main..PlayerMark) (this Main..Board)) $Result_Bool
(let ((@tmp_0 @tmp_8))
    (let ((_@tmpvar@40 (__i__Main..Board..checkWinner$Llogic_or_done_4 @tmp_0 player this)))
      (ite ((_ is $Result_Bool@error) _@tmpvar@40)
        _@tmpvar@40
        (let (($__ir_ret__ ($Result_Bool@success_value _@tmpvar@40)))
          (let (($return $__ir_ret__))
            ($Result_Bool@success $return)
          )
        )
      )
    )
  )
)

(define-fun Main..Board..checkWinner ((this Main..Board) (player Main..PlayerMark)) $Result_Bool
(let ((_@tmpvar@46 (Main..Board..check3 this Main..BoardPostion..r0c0 Main..BoardPostion..r0c1 Main..BoardPostion..r0c2 player)))
    (ite ((_ is $Result_Bool@error) _@tmpvar@46)
      _@tmpvar@46
      (let ((@tmp_3 ($Result_Bool@success_value _@tmpvar@46)))
        (let ((@tmp_0 @tmp_3))
          (ite @tmp_3
            (let ((_@tmpvar@43 (__i__Main..Board..checkWinner$Llogic_or_done_4 @tmp_0 player this)))
              (ite ((_ is $Result_Bool@error) _@tmpvar@43)
                _@tmpvar@43
                (let (($__ir_ret__$2 ($Result_Bool@success_value _@tmpvar@43)))
                  (let (($__ir_ret__$3 $__ir_ret__$2))
                    (let (($return $__ir_ret__$3))
                      ($Result_Bool@success $return)
                    )
                  )
                )
              )
            )
            (let ((_@tmpvar@45 (Main..Board..check3 this Main..BoardPostion..r1c0 Main..BoardPostion..r1c1 Main..BoardPostion..r1c2 player)))
              (ite ((_ is $Result_Bool@error) _@tmpvar@45)
                _@tmpvar@45
                (let ((@tmp_11 ($Result_Bool@success_value _@tmpvar@45)))
                  (let ((@tmp_8 @tmp_11))
                    (ite @tmp_11
                      (let ((_@tmpvar@44 (__i__Main..Board..checkWinner$Llogic_or_done_6 @tmp_8 player this)))
                        (ite ((_ is $Result_Bool@error) _@tmpvar@44)
                          _@tmpvar@44
                          (let (($__ir_ret__$1 ($Result_Bool@success_value _@tmpvar@44)))
                            (let (($__ir_ret__$3 $__ir_ret__$1))
                              (let (($return $__ir_ret__$3))
                                ($Result_Bool@success $return)
                              )
                            )
                          )
                        )
                      )
                      (let ((_@tmpvar@42 (Main..Board..check3 this Main..BoardPostion..r2c0 Main..BoardPostion..r2c1 Main..BoardPostion..r2c2 player)))
                        (ite ((_ is $Result_Bool@error) _@tmpvar@42)
                          _@tmpvar@42
                          (let ((@tmp_18 ($Result_Bool@success_value _@tmpvar@42)))
                            (let ((@tmp_8$1 @tmp_18))
                              (let ((_@tmpvar@41 (__i__Main..Board..checkWinner$Llogic_or_done_6 @tmp_8$1 player this)))
                                (ite ((_ is $Result_Bool@error) _@tmpvar@41)
                                  _@tmpvar@41
                                  (let (($__ir_ret__ ($Result_Bool@success_value _@tmpvar@41)))
                                    (let (($__ir_ret__$3 $__ir_ret__))
                                      (let (($return $__ir_ret__$3))
                                        ($Result_Bool@success $return)
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun Main..main () $Result_Bool
(let ((@tmp_1 Main..Board..create4))
    (let ((@tmp_2 (_cells._List_List_Main..PlayerMark___@_cells @tmp_1)))
      (let ((_@tmpvar@50 (Main..Board..@@constructor @tmp_2)))
        (ite ((_ is $Result_Main..Board@error) _@tmpvar@50)
          ($Result_Bool@error ($Result_Main..Board@error_value _@tmpvar@50))
          (let ((@tmp_0 ($Result_Main..Board@success_value _@tmpvar@50)))
            (let ((bb @tmp_0))
              (let ((_@tmpvar@49 (Main..BoardPostion..@@constructor 1 0)))
                (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@49)
                  ($Result_Bool@error ($Result_Main..BoardPostion@error_value _@tmpvar@49))
                  (let ((@tmp_6 ($Result_Main..BoardPostion@success_value _@tmpvar@49)))
                    (let ((_@tmpvar@48 (Main..Board..setCellMark @tmp_0 @tmp_6 Main..PlayerMark..x)))
                      (ite ((_ is $Result_Main..Board@error) _@tmpvar@48)
                        ($Result_Bool@error ($Result_Main..Board@error_value _@tmpvar@48))
                        (let ((@tmp_5 ($Result_Main..Board@success_value _@tmpvar@48)))
                          (let ((nb @tmp_5))
                            (let ((_@tmpvar@47 (Main..Board..checkWinner @tmp_5 Main..PlayerMark..x)))
                              (ite ((_ is $Result_Bool@error) _@tmpvar@47)
                                _@tmpvar@47
                                (let ((@tmp_13 ($Result_Bool@success_value _@tmpvar@47)))
                                  (let ((@tmp_10 (not @tmp_13)))
                                    (let (($__ir_ret__ @tmp_10))
                                      (let (($return $__ir_ret__))
                                        ($Result_Bool@success $return)
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..28@762..r0c0 () $Result_Main..BoardPostion
(let ((_@tmpvar@0 (Main..BoardPostion..@@constructor 0 0)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@0)
      _@tmpvar@0
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@0)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..29@813..r0c1 () $Result_Main..BoardPostion
(let ((_@tmpvar@1 (Main..BoardPostion..@@constructor 0 1)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@1)
      _@tmpvar@1
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@1)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..30@864..r0c2 () $Result_Main..BoardPostion
(let ((_@tmpvar@2 (Main..BoardPostion..@@constructor 0 2)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@2)
      _@tmpvar@2
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@2)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..32@920..r1c0 () $Result_Main..BoardPostion
(let ((_@tmpvar@3 (Main..BoardPostion..@@constructor 1 0)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@3)
      _@tmpvar@3
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@3)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..33@971..r1c1 () $Result_Main..BoardPostion
(let ((_@tmpvar@4 (Main..BoardPostion..@@constructor 1 1)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@4)
      _@tmpvar@4
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@4)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..34@1022..r1c2 () $Result_Main..BoardPostion
(let ((_@tmpvar@5 (Main..BoardPostion..@@constructor 1 2)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@5)
      _@tmpvar@5
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@5)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..36@1074..r2c0 () $Result_Main..BoardPostion
(let ((_@tmpvar@6 (Main..BoardPostion..@@constructor 2 0)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@6)
      _@tmpvar@6
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@6)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..37@1125..r2c1 () $Result_Main..BoardPostion
(let ((_@tmpvar@7 (Main..BoardPostion..@@constructor 2 1)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@7)
      _@tmpvar@7
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@7)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..38@1176..r2c2 () $Result_Main..BoardPostion
(let ((_@tmpvar@8 (Main..BoardPostion..@@constructor 2 2)))
    (ite ((_ is $Result_Main..BoardPostion@error) _@tmpvar@8)
      _@tmpvar@8
      (let ((@tmp_0 ($Result_Main..BoardPostion@success_value _@tmpvar@8)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            ($Result_Main..BoardPostion@success $return)
          )
        )
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..8@385..empty () Main..PlayerMark
(let ((@tmp_0 0))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..8@385..o () Main..PlayerMark
(let ((@tmp_0 2))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun constexp_tictactoe.bsq_k14_constexp..8@385..x () Main..PlayerMark
(let ((@tmp_0 1))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..28@762..r0c0)) (assert (= Main..BoardPostion..r0c0 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..28@762..r0c0)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..29@813..r0c1)) (assert (= Main..BoardPostion..r0c1 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..29@813..r0c1)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..30@864..r0c2)) (assert (= Main..BoardPostion..r0c2 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..30@864..r0c2)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..32@920..r1c0)) (assert (= Main..BoardPostion..r1c0 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..32@920..r1c0)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..33@971..r1c1)) (assert (= Main..BoardPostion..r1c1 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..33@971..r1c1)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..34@1022..r1c2)) (assert (= Main..BoardPostion..r1c2 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..34@1022..r1c2)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..36@1074..r2c0)) (assert (= Main..BoardPostion..r2c0 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..36@1074..r2c0)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..37@1125..r2c1)) (assert (= Main..BoardPostion..r2c1 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..37@1125..r2c1)))
(assert ((_ is $Result_Main..BoardPostion@success) constexp_tictactoe.bsq_k14_constexp..38@1176..r2c2)) (assert (= Main..BoardPostion..r2c2 ($Result_Main..BoardPostion@success_value constexp_tictactoe.bsq_k14_constexp..38@1176..r2c2)))
(assert (= Main..PlayerMark..empty constexp_tictactoe.bsq_k14_constexp..8@385..empty))
(assert (= Main..PlayerMark..o constexp_tictactoe.bsq_k14_constexp..8@385..o))
(assert (= Main..PlayerMark..x constexp_tictactoe.bsq_k14_constexp..8@385..x))

(declare-const _@smtres@ $Result_Bool)
(assert (= _@smtres@ Main..main))
(assert ((_ is $Result_Bool@success) _@smtres@))
(assert (not ($Result_Bool@success_value _@smtres@)))
