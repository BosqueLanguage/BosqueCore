;;-------------------------------------------------------------------------------------------------------
;; Copyright (C) Microsoft. All rights reserved.
;; Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
;;-------------------------------------------------------------------------------------------------------

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
      (TypeTag_ContentHash)
      (TypeTag_DateTime)
      (TypeTag_Decimal)
      (TypeTag_Float)
      (TypeTag_HavocSequence)
      (TypeTag_Int)
      (TypeTag_ListOps)
      (TypeTag_List_Main..BuyResponse_)
      (TypeTag_List_Main..Quantity_)
      (TypeTag_List_Main..RejectReason_)
      (TypeTag_List_Main..Violations_)
      (TypeTag_LogicalTime)
      (TypeTag_Main..BuyAccepted)
      (TypeTag_Main..BuyInvalid)
      (TypeTag_Main..BuyRejected)
      (TypeTag_Main..BuyRequest)
      (TypeTag_Main..InvalidPrice)
      (TypeTag_Main..InvalidQuantity)
      (TypeTag_Main..Limit)
      (TypeTag_Main..Market)
      (TypeTag_Main..Price)
      (TypeTag_Main..Quantity)
      (TypeTag_Main..RejectReason)
      (TypeTag_Main..SellAccepted)
      (TypeTag_Main..SellRequest)
      (TypeTag_Nat)
      (TypeTag_None)
      (TypeTag_Nothing)
      (TypeTag_Rational)
      (TypeTag_Regex)
      (TypeTag_String)
      (TypeTag_TickTime)
      (TypeTag_UUID)
    )
))

(declare-fun TypeTag_OrdinalOf (TypeTag) Int)
(assert (= (TypeTag_OrdinalOf TypeTag_BigInt) 0))
(assert (= (TypeTag_OrdinalOf TypeTag_BigNat) 1))
(assert (= (TypeTag_OrdinalOf TypeTag_Bool) 2))
(assert (= (TypeTag_OrdinalOf TypeTag_BufferCompression) 3))
(assert (= (TypeTag_OrdinalOf TypeTag_BufferFormat) 4))
(assert (= (TypeTag_OrdinalOf TypeTag_ContentHash) 5))
(assert (= (TypeTag_OrdinalOf TypeTag_DateTime) 6))
(assert (= (TypeTag_OrdinalOf TypeTag_Int) 7))
(assert (= (TypeTag_OrdinalOf TypeTag_LogicalTime) 8))
(assert (= (TypeTag_OrdinalOf TypeTag_Main..Quantity) 9))
(assert (= (TypeTag_OrdinalOf TypeTag_Main..RejectReason) 10))
(assert (= (TypeTag_OrdinalOf TypeTag_Nat) 11))
(assert (= (TypeTag_OrdinalOf TypeTag_None) 12))
(assert (= (TypeTag_OrdinalOf TypeTag_String) 13))
(assert (= (TypeTag_OrdinalOf TypeTag_UUID) 14))

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
(define-sort BUUID () (Seq (_ BitVec 8)))
(define-sort BContentHash () (_ BitVec 16))

;;TODO BHashable and Hash + HashInvert and axioms

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
      ; TickTime -> Int
      ; LogicalTime -> Int
      ; UUID -> BUUID
      ; ContentHash -> (_ BitVec 16)
    ) (
      ( (bsq_none@literal) ) 
      ( (bsq_nothing@literal) )
))

(define-sort BufferCompression () BNat)
(define-sort BufferFormat () BNat)
(define-sort Main..Quantity () BNat)
(define-sort Main..RejectReason () BNat)
(define-sort Main..Price () BDecimal)

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
      (bsqkey_logicaltime@box (bsqkey_logicaltime_value BLogicalTime))
      (bsqkey_uuid@box (bsqkey_uuid_value BUUID))
      (bsqkey_contenthash@box (bsqkey_contenthash_value BContentHash))
      (BufferCompression@box (bsqkey_BufferCompression_value BufferCompression))
      (BufferFormat@box (bsqkey_BufferFormat_value BufferFormat))
      (Main..Quantity@box (bsqkey_Main..Quantity_value Main..Quantity))
      (Main..RejectReason@box (bsqkey_Main..RejectReason_value Main..RejectReason))
      (Main..Price@box (bsqobject_Main..Price_value Main..Price))
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

(define-fun BLogicalTime@less ((k1 BLogicalTime) (k2 BLogicalTime)) Bool
  (< k1 k2)
)

(define-fun BUUID@less ((k1 BUUID) (k2 BUUID)) Bool
  ;;TODO: fix this
  true
)

(define-fun BContentHash@less ((k1 BContentHash) (k2 BContentHash)) Bool
  (bvult k1 k2)
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
                      (ite (= tt TypeTag_LogicalTime)
                        (BLogicalTime@less (bsqkey_logicaltime_value vv1) (bsqkey_logicaltime_value vv2))
                        (ite (= tt TypeTag_UUID)
                          (BUUID@less (bsqkey_uuid_value vv1) (bsqkey_uuid_value vv2))
                          (BContentHash@less (bsqkey_contenthash_value vv1) (bsqkey_contenthash_value vv2))
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
    ;;NO DATA;;
    (ListOps 0)
    (Main..BuyAccepted 0)
    (Main..BuyInvalid 0)
    (Main..BuyRejected 0)
    (Main..BuyRequest 0)
    (Main..InvalidPrice 0)
    (Main..InvalidQuantity 0)
    (Main..Limit 0)
    (Main..Market 0)
    (Main..SellAccepted 0)
    (Main..SellRequest 0)
    (List_Main..BuyResponse_ 0)
    (List_Main..Quantity_ 0)
    (List_Main..RejectReason_ 0)
    (List_Main..Violations_ 0)
    (bsq_object 0)
    (BTerm 0)
    ) (
    ( (bsq_regex@cons (bsq_regex_value Int)) )
    ;;NO DATA;;
    ;;NO DATA;;
    ( (ListOps@cons ) )
    ( (Main..BuyAccepted@cons (Main..BuyAccepted@_id BString) (Main..BuyAccepted@_product BString) (Main..BuyAccepted@_price Main..Price) (Main..BuyAccepted@_quantity Main..Quantity)) )
    ( (Main..BuyInvalid@cons (Main..BuyInvalid@_id BString) (Main..BuyInvalid@_violations List_Main..Violations_)) )
    ( (Main..BuyRejected@cons (Main..BuyRejected@_id BString) (Main..BuyRejected@_reasons List_Main..RejectReason_)) )
    ( (Main..BuyRequest@cons (Main..BuyRequest@_id BString) (Main..BuyRequest@_requestPrice BTerm) (Main..BuyRequest@_quantity Main..Quantity) (Main..BuyRequest@_product BString)) )
    ( (Main..InvalidPrice@cons (Main..InvalidPrice@_price Main..Price)) )
    ( (Main..InvalidQuantity@cons (Main..InvalidQuantity@_quantity Main..Quantity)) )
    ( (Main..Limit@cons (Main..Limit@_price Main..Price)) )
    ( (Main..Market@cons ) )
    ( (Main..SellAccepted@cons (Main..SellAccepted@_id BString) (Main..SellAccepted@_price Main..Price)) )
    ( (Main..SellRequest@cons (Main..SellRequest@_id BString) (Main..SellRequest@_requestPrice BTerm) (Main..SellRequest@_dealId BString)) )
    ( (List_Main..BuyResponse_@cons (List_Main..BuyResponse__seq (Seq BTerm))) )
    ( (List_Main..Quantity_@cons (List_Main..Quantity__seq (Seq Main..Quantity))) )
    ( (List_Main..RejectReason_@cons (List_Main..RejectReason__seq (Seq Main..RejectReason))) )
    ( (List_Main..Violations_@cons (List_Main..Violations__seq (Seq BTerm))) )
    (
      (bsqobject_nothing@literal)
      (bsqobject_float@box (bsqobject_float_value BFloat))
      (bsqobject_decimal@box (bsqobject_decimal_value BDecimal))
      (bsqobject_rational@box (bsqobject_rational_value BRational))
      (bsqobject_bytebuffer@box (bsqobject_bytebuffer_value BByteBuffer))
      (bsqobject_datetime@box (bsqobject_datetime_value BDateTime))
      (bsqobject_ticktime@box (bsqobject_ticktime_value BTickTime))
      (bsqobject_regex@box (bsqobject_regex_value bsq_regex))
      ;;NO DATA;;
      ;;NO DATA;;
      (ListOps@box (bsqobject_ListOps_value ListOps))
      (Main..BuyAccepted@box (bsqobject_Main..BuyAccepted_value Main..BuyAccepted))
      (Main..BuyInvalid@box (bsqobject_Main..BuyInvalid_value Main..BuyInvalid))
      (Main..BuyRejected@box (bsqobject_Main..BuyRejected_value Main..BuyRejected))
      (Main..BuyRequest@box (bsqobject_Main..BuyRequest_value Main..BuyRequest))
      (Main..InvalidPrice@box (bsqobject_Main..InvalidPrice_value Main..InvalidPrice))
      (Main..InvalidQuantity@box (bsqobject_Main..InvalidQuantity_value Main..InvalidQuantity))
      (Main..Limit@box (bsqobject_Main..Limit_value Main..Limit))
      (Main..Market@box (bsqobject_Main..Market_value Main..Market))
      (Main..SellAccepted@box (bsqobject_Main..SellAccepted_value Main..SellAccepted))
      (Main..SellRequest@box (bsqobject_Main..SellRequest_value Main..SellRequest))
      (List_Main..BuyResponse_@box (bsqobject_List_Main..BuyResponse__value List_Main..BuyResponse_))
      (List_Main..Quantity_@box (bsqobject_List_Main..Quantity__value List_Main..Quantity_))
      (List_Main..RejectReason_@box (bsqobject_List_Main..RejectReason__value List_Main..RejectReason_))
      (List_Main..Violations_@box (bsqobject_List_Main..Violations__value List_Main..Violations_))
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
    (__Main..Price__ 0)
    ) (
    ( (elistnull@cons) )
    ( (__Main..Price__@cons (__Main..Price__@_0 Main..Price)) )
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
      ($Result___Main..Price__ 0)
      ($Result_BTerm 0)
      ($Result_BBigInt 0)
      ($Result_BBigNat 0)
      ($Result_Bool 0)
      ($Result_BufferCompression 0)
      ($Result_BufferFormat 0)
      ($Result_BByteBuffer 0)
      ($Result_BContentHash 0)
      ($Result_BDateTime 0)
      ($Result_BDecimal 0)
      ($Result_BFloat 0)
      ($Result_HavocSequence 0)
      ($Result_BInt 0)
      ($Result_BKey 0)
      ($Result_List_Main..BuyResponse_ 0)
      ($Result_List_Main..Quantity_ 0)
      ($Result_List_Main..RejectReason_ 0)
      ($Result_List_Main..Violations_ 0)
      ($Result_ListOps 0)
      ($Result_BLogicalTime 0)
      ($Result_Main..BuyAccepted 0)
      ($Result_Main..BuyInvalid 0)
      ($Result_Main..BuyRejected 0)
      ($Result_Main..BuyRequest 0)
      ($Result_Main..InvalidPrice 0)
      ($Result_Main..InvalidQuantity 0)
      ($Result_Main..Limit 0)
      ($Result_Main..Market 0)
      ($Result_Main..Price 0)
      ($Result_Main..Quantity 0)
      ($Result_Main..RejectReason 0)
      ($Result_Main..SellAccepted 0)
      ($Result_Main..SellRequest 0)
      ($Result_BNat 0)
      ($Result_bsq_none 0)
      ($Result_bsq_nothing 0)
      ($Result_BRational 0)
      ($Result_bsq_regex 0)
      ($Result_BString 0)
      ($Result_BTickTime 0)
      ($Result_BUUID 0)
      ;;NO DATA;;
    ) (
    ( ($Result___Main..Price__@success ($Result___Main..Price__@success_value __Main..Price__)) ($Result___Main..Price__@error ($Result___Main..Price__@error_value ErrorID)) )
    ( ($Result_BTerm@success ($Result_BTerm@success_value BTerm)) ($Result_BTerm@error ($Result_BTerm@error_value ErrorID)) )
    ( ($Result_BBigInt@success ($Result_BBigInt@success_value BBigInt)) ($Result_BBigInt@error ($Result_BBigInt@error_value ErrorID)) )
    ( ($Result_BBigNat@success ($Result_BBigNat@success_value BBigNat)) ($Result_BBigNat@error ($Result_BBigNat@error_value ErrorID)) )
    ( ($Result_Bool@success ($Result_Bool@success_value Bool)) ($Result_Bool@error ($Result_Bool@error_value ErrorID)) )
    ( ($Result_BufferCompression@success ($Result_BufferCompression@success_value BufferCompression)) ($Result_BufferCompression@error ($Result_BufferCompression@error_value ErrorID)) )
    ( ($Result_BufferFormat@success ($Result_BufferFormat@success_value BufferFormat)) ($Result_BufferFormat@error ($Result_BufferFormat@error_value ErrorID)) )
    ( ($Result_BByteBuffer@success ($Result_BByteBuffer@success_value BByteBuffer)) ($Result_BByteBuffer@error ($Result_BByteBuffer@error_value ErrorID)) )
    ( ($Result_BContentHash@success ($Result_BContentHash@success_value BContentHash)) ($Result_BContentHash@error ($Result_BContentHash@error_value ErrorID)) )
    ( ($Result_BDateTime@success ($Result_BDateTime@success_value BDateTime)) ($Result_BDateTime@error ($Result_BDateTime@error_value ErrorID)) )
    ( ($Result_BDecimal@success ($Result_BDecimal@success_value BDecimal)) ($Result_BDecimal@error ($Result_BDecimal@error_value ErrorID)) )
    ( ($Result_BFloat@success ($Result_BFloat@success_value BFloat)) ($Result_BFloat@error ($Result_BFloat@error_value ErrorID)) )
    ( ($Result_HavocSequence@success ($Result_HavocSequence@success_value HavocSequence)) ($Result_HavocSequence@error ($Result_HavocSequence@error_value ErrorID)) )
    ( ($Result_BInt@success ($Result_BInt@success_value BInt)) ($Result_BInt@error ($Result_BInt@error_value ErrorID)) )
    ( ($Result_BKey@success ($Result_BKey@success_value BKey)) ($Result_BKey@error ($Result_BKey@error_value ErrorID)) )
    ( ($Result_List_Main..BuyResponse_@success ($Result_List_Main..BuyResponse_@success_value List_Main..BuyResponse_)) ($Result_List_Main..BuyResponse_@error ($Result_List_Main..BuyResponse_@error_value ErrorID)) )
    ( ($Result_List_Main..Quantity_@success ($Result_List_Main..Quantity_@success_value List_Main..Quantity_)) ($Result_List_Main..Quantity_@error ($Result_List_Main..Quantity_@error_value ErrorID)) )
    ( ($Result_List_Main..RejectReason_@success ($Result_List_Main..RejectReason_@success_value List_Main..RejectReason_)) ($Result_List_Main..RejectReason_@error ($Result_List_Main..RejectReason_@error_value ErrorID)) )
    ( ($Result_List_Main..Violations_@success ($Result_List_Main..Violations_@success_value List_Main..Violations_)) ($Result_List_Main..Violations_@error ($Result_List_Main..Violations_@error_value ErrorID)) )
    ( ($Result_ListOps@success ($Result_ListOps@success_value ListOps)) ($Result_ListOps@error ($Result_ListOps@error_value ErrorID)) )
    ( ($Result_BLogicalTime@success ($Result_BLogicalTime@success_value BLogicalTime)) ($Result_BLogicalTime@error ($Result_BLogicalTime@error_value ErrorID)) )
    ( ($Result_Main..BuyAccepted@success ($Result_Main..BuyAccepted@success_value Main..BuyAccepted)) ($Result_Main..BuyAccepted@error ($Result_Main..BuyAccepted@error_value ErrorID)) )
    ( ($Result_Main..BuyInvalid@success ($Result_Main..BuyInvalid@success_value Main..BuyInvalid)) ($Result_Main..BuyInvalid@error ($Result_Main..BuyInvalid@error_value ErrorID)) )
    ( ($Result_Main..BuyRejected@success ($Result_Main..BuyRejected@success_value Main..BuyRejected)) ($Result_Main..BuyRejected@error ($Result_Main..BuyRejected@error_value ErrorID)) )
    ( ($Result_Main..BuyRequest@success ($Result_Main..BuyRequest@success_value Main..BuyRequest)) ($Result_Main..BuyRequest@error ($Result_Main..BuyRequest@error_value ErrorID)) )
    ( ($Result_Main..InvalidPrice@success ($Result_Main..InvalidPrice@success_value Main..InvalidPrice)) ($Result_Main..InvalidPrice@error ($Result_Main..InvalidPrice@error_value ErrorID)) )
    ( ($Result_Main..InvalidQuantity@success ($Result_Main..InvalidQuantity@success_value Main..InvalidQuantity)) ($Result_Main..InvalidQuantity@error ($Result_Main..InvalidQuantity@error_value ErrorID)) )
    ( ($Result_Main..Limit@success ($Result_Main..Limit@success_value Main..Limit)) ($Result_Main..Limit@error ($Result_Main..Limit@error_value ErrorID)) )
    ( ($Result_Main..Market@success ($Result_Main..Market@success_value Main..Market)) ($Result_Main..Market@error ($Result_Main..Market@error_value ErrorID)) )
    ( ($Result_Main..Price@success ($Result_Main..Price@success_value Main..Price)) ($Result_Main..Price@error ($Result_Main..Price@error_value ErrorID)) )
    ( ($Result_Main..Quantity@success ($Result_Main..Quantity@success_value Main..Quantity)) ($Result_Main..Quantity@error ($Result_Main..Quantity@error_value ErrorID)) )
    ( ($Result_Main..RejectReason@success ($Result_Main..RejectReason@success_value Main..RejectReason)) ($Result_Main..RejectReason@error ($Result_Main..RejectReason@error_value ErrorID)) )
    ( ($Result_Main..SellAccepted@success ($Result_Main..SellAccepted@success_value Main..SellAccepted)) ($Result_Main..SellAccepted@error ($Result_Main..SellAccepted@error_value ErrorID)) )
    ( ($Result_Main..SellRequest@success ($Result_Main..SellRequest@success_value Main..SellRequest)) ($Result_Main..SellRequest@error ($Result_Main..SellRequest@error_value ErrorID)) )
    ( ($Result_BNat@success ($Result_BNat@success_value BNat)) ($Result_BNat@error ($Result_BNat@error_value ErrorID)) )
    ( ($Result_bsq_none@success ($Result_bsq_none@success_value bsq_none)) ($Result_bsq_none@error ($Result_bsq_none@error_value ErrorID)) )
    ( ($Result_bsq_nothing@success ($Result_bsq_nothing@success_value bsq_nothing)) ($Result_bsq_nothing@error ($Result_bsq_nothing@error_value ErrorID)) )
    ( ($Result_BRational@success ($Result_BRational@success_value BRational)) ($Result_BRational@error ($Result_BRational@error_value ErrorID)) )
    ( ($Result_bsq_regex@success ($Result_bsq_regex@success_value bsq_regex)) ($Result_bsq_regex@error ($Result_bsq_regex@error_value ErrorID)) )
    ( ($Result_BString@success ($Result_BString@success_value BString)) ($Result_BString@error ($Result_BString@error_value ErrorID)) )
    ( ($Result_BTickTime@success ($Result_BTickTime@success_value BTickTime)) ($Result_BTickTime@error ($Result_BTickTime@error_value ErrorID)) )
    ( ($Result_BUUID@success ($Result_BUUID@success_value BUUID)) ($Result_BUUID@error ($Result_BUUID@error_value ErrorID)) )
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
(declare-fun BTickTime@UFCons_API (HavocSequence) BTickTime)
(declare-fun BLogicalTime@UFCons_API (HavocSequence) BLogicalTime)
(declare-fun BUUID@UFCons_API (HavocSequence) BUUID)
(declare-fun BContentHash@UFCons_API (HavocSequence) BContentHash)

(declare-fun ContainerSize@UFCons_API (HavocSequence) BNat)
(declare-fun UnionChoice@UFCons_API (HavocSequence) BNat)

(define-fun _@@cons_None_entrypoint ((ctx HavocSequence)) $Result_bsq_none
  ($Result_bsq_none@success bsq_none@literal)
)

(define-fun _@@cons_Nothing_entrypoint ((ctx HavocSequence)) $Result_bsq_nothing
  ($Result_bsq_nothing@success bsq_nothing@literal)
)

;;@BINTMIN, @BINTMAX, @SLENMAX, @BLENMAX
(declare-const @BINTMIN Int) (assert (= @BINTMIN -255))
(declare-const @BINTMAX Int) (assert (= @BINTMAX 256))
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
    (ite (and (<= 0 iv) (<= iv @BINTMAX))
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
    (ite (and (<= 0 iv) (<= iv (+ @BINTMAX @BINTMAX)))
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

(define-fun _@@cons_DateTime_entrypoint ((ctx HavocSequence)) $Result_BDateTime
  (let ((tctx (seq.++ ctx (seq.unit 0))))
    (let ((y (BDateYear@UFCons_API (seq.++ tctx (seq.unit 0)))) (m (BDateMonth@UFCons_API (seq.++ tctx (seq.unit 1)))) (d (BDateDay@UFCons_API (seq.++ tctx (seq.unit 2)))) (hh (BDateHour@UFCons_API (seq.++ tctx (seq.unit 3)))) (mm (BDateMinute@UFCons_API (seq.++ tctx (seq.unit 4)))) (tzo (BString@UFCons_API (seq.++ ctx (seq.unit 1)))))
      (ite (and (<= 0 y) (<= y 300) (<= 0 m) (<= m 11) (<= 1 d) (<= d 31) (<= 0 hh) (<= hh 23) (<= 0 mm) (<= mm 59) (or (= tzo "UTC") (= tzo "PST") (= tzo "MST") (= tzo "CEST")))
        ($Result_BDateTime@success (BDateTime@cons y m d hh mm tzo))
        ($Result_BDateTime@error ErrorID_AssumeCheck) 
      )
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

(define-fun _@@cons_UUID_entrypoint ((ctx HavocSequence)) $Result_BUUID
  (let ((uuv (BUUID@UFCons_API ctx)))
    (ite (= (seq.len uuv) 16)
      ($Result_BUUID@success uuv)
      ($Result_BUUID@error ErrorID_AssumeCheck) 
    )
  )
)

(define-fun _@@cons_ContentHash_entrypoint ((ctx HavocSequence)) $Result_BContentHash
  ($Result_BContentHash@success (BContentHash@UFCons_API ctx))
)

(declare-const List_Main..BuyResponse_@@empty List_Main..BuyResponse_) (assert (= List_Main..BuyResponse_@@empty (List_Main..BuyResponse_@cons (as seq.empty (Seq BTerm)))))
(declare-const List_Main..Quantity_@@empty List_Main..Quantity_) (assert (= List_Main..Quantity_@@empty (List_Main..Quantity_@cons (as seq.empty (Seq Main..Quantity)))))
(declare-const List_Main..RejectReason_@@empty List_Main..RejectReason_) (assert (= List_Main..RejectReason_@@empty (List_Main..RejectReason_@cons (as seq.empty (Seq Main..RejectReason)))))
(declare-const List_Main..Violations_@@empty List_Main..Violations_) (assert (= List_Main..Violations_@@empty (List_Main..Violations_@cons (as seq.empty (Seq BTerm)))))
(declare-const Main..Quantity..zero Main..Quantity)
(declare-const Main..RejectReason..disagreeablePrice Main..RejectReason)
(declare-const Main..RejectReason..insufficientInventory Main..RejectReason)

;;NO DATA;;

(define-fun ListOps..s_list_empty_T_Main..BuyResponse_ ((l List_Main..BuyResponse_)) Bool
(= l List_Main..BuyResponse_@@empty)
)

(define-fun fn--order.bsq_k14..126@3463$Lswitchexp_done_3 ((@tmp_0 Main..Quantity)) Main..Quantity
(let (($__ir_ret__ @tmp_0))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun fn--order.bsq_k14..126@3463 ((response BTerm)) Main..Quantity
(let (($match_@3477 response))
    (let ((@tmp_2 ((_ is Main..BuyAccepted@box) (BTerm_termvalue response))))
      (ite @tmp_2
        (let ((@tmp_5 (Main..BuyAccepted@_quantity (bsqobject_Main..BuyAccepted_value (BTerm_termvalue response)))))
          (let ((@tmp_0$1 @tmp_5))
            (let (($__ir_ret__$1 (fn--order.bsq_k14..126@3463$Lswitchexp_done_3 @tmp_0$1)))
              (let (($__ir_ret__$2 $__ir_ret__$1))
                (let (($return $__ir_ret__$2))
                  $return
                )
              )
            )
          )
        )
        (let ((@tmp_0 0))
          (let (($__ir_ret__ (fn--order.bsq_k14..126@3463$Lswitchexp_done_3 @tmp_0)))
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
)

(define-fun ListOps..s_list_map_fn_T_Main..BuyResponse__U_Main..Quantity__fn--order.bsq_k14..126@3463_ ((l List_Main..BuyResponse_)) List_Main..Quantity_
(List_Main..Quantity_@cons (seq.map (lambda ((@@x BTerm)) (fn--order.bsq_k14..126@3463 @@x)) (List_Main..BuyResponse__seq l)))
)

(define-fun List_Main..BuyResponse_..map_T_Main..BuyResponse__U_Main..Quantity__fn--order.bsq_k14..126@3463_ ((this List_Main..BuyResponse_)) List_Main..Quantity_
(let ((@tmp_0 (ListOps..s_list_empty_T_Main..BuyResponse_ this)))
    (ite @tmp_0
      (let ((@tmp_2 List_Main..Quantity_@@empty))
        (let (($__ir_ret__$1 @tmp_2))
          (let (($__ir_ret__$2 $__ir_ret__$1))
            (let (($return $__ir_ret__$2))
              $return
            )
          )
        )
      )
      (let ((@tmp_3 (ListOps..s_list_map_fn_T_Main..BuyResponse__U_Main..Quantity__fn--order.bsq_k14..126@3463_ this)))
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

(define-fun ListOps..s_list_empty_T_Main..Quantity_ ((l List_Main..Quantity_)) Bool
(= l List_Main..Quantity_@@empty)
)

(define-fun ListOps..s_list_size_T_Main..Quantity_ ((l List_Main..Quantity_)) BNat
(seq.len (List_Main..Quantity__seq l))
)

(define-fun ListOps..s_list_get_front_T_Main..Quantity_ ((l List_Main..Quantity_)) Main..Quantity
(seq.nth (List_Main..Quantity__seq l) 0)
)

(define-fun ListOps..s_blockingfailure_T_Main..Quantity_ () $Result_Main..Quantity
($Result_Main..Quantity@error ErrorID_AssumeCheck)
)

(define-fun List_Main..Quantity_..sum_T_Main..Quantity_ ((this List_Main..Quantity_)) $Result_Main..Quantity
(let ((@tmp_0 (ListOps..s_list_empty_T_Main..Quantity_ this)))
    (ite @tmp_0
      (let (($__ir_ret__$2 Main..Quantity..zero))
        (let (($__ir_ret__$3 $__ir_ret__$2))
          (let (($return $__ir_ret__$3))
            ($Result_Main..Quantity@success $return)
          )
        )
      )
      (let ((@tmp_4 (ListOps..s_list_size_T_Main..Quantity_ this)))
        (let ((@tmp_3 (= @tmp_4 1)))
          (ite @tmp_3
            (let ((@tmp_7 (ListOps..s_list_get_front_T_Main..Quantity_ this)))
              (let (($__ir_ret__$1 @tmp_7))
                (let (($__ir_ret__$3 $__ir_ret__$1))
                  (let (($return $__ir_ret__$3))
                    ($Result_Main..Quantity@success $return)
                  )
                )
              )
            )
            (let ((_@tmpvar@0 ListOps..s_blockingfailure_T_Main..Quantity_))
              (ite ((_ is $Result_Main..Quantity@error) _@tmpvar@0)
                _@tmpvar@0
                (let ((@tmp_9 ($Result_Main..Quantity@success_value _@tmpvar@0)))
                  (let (($__ir_ret__ @tmp_9))
                    (let (($__ir_ret__$3 $__ir_ret__))
                      (let (($return $__ir_ret__$3))
                        ($Result_Main..Quantity@success $return)
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

(define-fun Core..__infix__Main..Quantity__Main..Quantity_ ((l Main..Quantity) (r Main..Quantity)) Bool
(let ((@tmp_3 l))
    (let ((@tmp_6 r))
      (let ((@tmp_0 (< @tmp_3 @tmp_6)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            $return
          )
        )
      )
    )
  )
)

(define-fun __i__Main..availability$Lselect_done_3 ((@tmp_5 Main..Quantity)) Main..Quantity
(let (($__ir_ret__ @tmp_5))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun Core..-_infix__Main..Quantity__Main..Quantity_ ((l Main..Quantity) (r Main..Quantity)) $Result_Main..Quantity
(let ((@tmp_4 l))
    (let ((@tmp_7 r))
      (let ((_@tmpvar@1 (ite (< @tmp_7 @tmp_4) ($Result_BNat@error ErrorID_AssumeCheck) ($Result_BNat@success (- @tmp_4 @tmp_7)))))
        (ite ((_ is $Result_BNat@error) _@tmpvar@1)
          ($Result_Main..Quantity@error ($Result_BNat@error_value _@tmpvar@1))
          (let ((@tmp_1 ($Result_BNat@success_value _@tmpvar@1)))
            (let ((@tmp_0 @tmp_1))
              (let (($__ir_ret__ @tmp_0))
                (let (($return $__ir_ret__))
                  ($Result_Main..Quantity@success $return)
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun Main..availability ((startOfDayPosition Main..Quantity) (buys List_Main..BuyResponse_)) $Result_Main..Quantity
(let ((@tmp_2 (List_Main..BuyResponse_..map_T_Main..BuyResponse__U_Main..Quantity__fn--order.bsq_k14..126@3463_ buys)))
    (let ((_@tmpvar@3 (List_Main..Quantity_..sum_T_Main..Quantity_ @tmp_2)))
      (ite ((_ is $Result_Main..Quantity@error) _@tmpvar@3)
        _@tmpvar@3
        (let ((@tmp_4 ($Result_Main..Quantity@success_value _@tmpvar@3)))
          (let ((sumOfBuys @tmp_4))
            (let ((@tmp_6 (Core..__infix__Main..Quantity__Main..Quantity_ @tmp_4 startOfDayPosition)))
              (ite @tmp_6
                (let ((@tmp_5$1 0))
                  (let (($__ir_ret__$1 (__i__Main..availability$Lselect_done_3 @tmp_5$1)))
                    (let (($__ir_ret__$2 $__ir_ret__$1))
                      (let (($return $__ir_ret__$2))
                        ($Result_Main..Quantity@success $return)
                      )
                    )
                  )
                )
                (let ((_@tmpvar@2 (Core..-_infix__Main..Quantity__Main..Quantity_ startOfDayPosition sumOfBuys)))
                  (ite ((_ is $Result_Main..Quantity@error) _@tmpvar@2)
                    _@tmpvar@2
                    (let ((@tmp_10 ($Result_Main..Quantity@success_value _@tmpvar@2)))
                      (let ((@tmp_5 @tmp_10))
                        (let (($__ir_ret__ (__i__Main..availability$Lselect_done_3 @tmp_5)))
                          (let (($__ir_ret__$2 $__ir_ret__))
                            (let (($return $__ir_ret__$2))
                              ($Result_Main..Quantity@success $return)
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

(define-fun Core..___infix__Main..Quantity__Main..Quantity_ ((l Main..Quantity) (r Main..Quantity)) Bool
(let ((@tmp_3 l))
    (let ((@tmp_6 r))
      (let ((@tmp_0 (<= @tmp_3 @tmp_6)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            $return
          )
        )
      )
    )
  )
)

(define-fun $ListSingletonCons_1_List_Main..Violations_ ((arg0 BTerm)) List_Main..Violations_
(List_Main..Violations_@cons (seq.++ (seq.unit arg0)))
)

(define-fun ListOps..s_list_empty_T_Main..Violations_ ((l List_Main..Violations_)) Bool
(= l List_Main..Violations_@@empty)
)

(define-fun ListOps..s_list_append_T_Main..Violations_ ((l List_Main..Violations_) (r List_Main..Violations_)) List_Main..Violations_
(List_Main..Violations_@cons (seq.++ (List_Main..Violations__seq l) (List_Main..Violations__seq r)))
)

(define-fun List_Main..Violations_..append_T_Main..Violations_ ((this List_Main..Violations_) (l List_Main..Violations_)) List_Main..Violations_
(let ((@tmp_1 (ListOps..s_list_empty_T_Main..Violations_ this)))
    (let ((@tmp_3 (ListOps..s_list_empty_T_Main..Violations_ l)))
      (let ((@tmp_0 (and @tmp_1 @tmp_3)))
        (ite @tmp_0
          (let ((@tmp_5 List_Main..Violations_@@empty))
            (let (($__ir_ret__$3 @tmp_5))
              (let (($__ir_ret__$4 $__ir_ret__$3))
                (let (($return $__ir_ret__$4))
                  $return
                )
              )
            )
          )
          (let ((@tmp_6 (ListOps..s_list_empty_T_Main..Violations_ this)))
            (ite @tmp_6
              (let (($__ir_ret__$2 l))
                (let (($__ir_ret__$4 $__ir_ret__$2))
                  (let (($return $__ir_ret__$4))
                    $return
                  )
                )
              )
              (let ((@tmp_9 (ListOps..s_list_empty_T_Main..Violations_ l)))
                (ite @tmp_9
                  (let (($__ir_ret__$1 this))
                    (let (($__ir_ret__$4 $__ir_ret__$1))
                      (let (($return $__ir_ret__$4))
                        $return
                      )
                    )
                  )
                  (let ((@tmp_12 (ListOps..s_list_append_T_Main..Violations_ this l)))
                    (let (($__ir_ret__ @tmp_12))
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

(define-fun __i__Main..validateRequest$Lifexp_done_11 ((@tmp_17 List_Main..Violations_) (priceCheck List_Main..Violations_)) List_Main..Violations_
(let ((quantityCheck @tmp_17))
    (let ((@tmp_32 (List_Main..Violations_..append_T_Main..Violations_ priceCheck @tmp_17)))
      (let (($__ir_ret__ @tmp_32))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun __i__Main..validateRequest$Lswitchexp_done_3 ((@tmp_0 List_Main..Violations_) (request Main..BuyRequest)) List_Main..Violations_
(let ((priceCheck @tmp_0))
    (let ((@tmp_21 (Main..BuyRequest@_quantity request)))
      (let ((@tmp_18 (Core..___infix__Main..Quantity__Main..Quantity_ @tmp_21 0)))
        (ite @tmp_18
          (let ((@tmp_27 (Main..BuyRequest@_quantity request)))
            (let ((@tmp_24 (Main..InvalidQuantity@cons @tmp_27)))
              (let ((@tmp_28 (BTerm@termbox TypeTag_Main..InvalidQuantity (Main..InvalidQuantity@box @tmp_24))))
                (let ((@tmp_23 ($ListSingletonCons_1_List_Main..Violations_ @tmp_28)))
                  (let ((@tmp_17$1 @tmp_23))
                    (let (($__ir_ret__$1 (__i__Main..validateRequest$Lifexp_done_11 @tmp_17$1 priceCheck)))
                      (let (($__ir_ret__$2 $__ir_ret__$1))
                        (let (($return $__ir_ret__$2))
                          $return
                        )
                      )
                    )
                  )
                )
              )
            )
          )
          (let ((@tmp_29 List_Main..Violations_@@empty))
            (let ((@tmp_17 @tmp_29))
              (let (($__ir_ret__ (__i__Main..validateRequest$Lifexp_done_11 @tmp_17 priceCheck)))
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
    )
  )
)

(define-fun $EntityProject_Main..Limit@_price_ ((arg Main..Limit)) __Main..Price__
(__Main..Price__@cons (Main..Limit@_price arg))
)

(define-fun Core..__infix__Main..Price__Main..Price_ ((l Main..Price) (r Main..Price)) Bool
(let ((@tmp_3 l))
    (let ((@tmp_6 r))
      (let ((@tmp_0 (< @tmp_3 @tmp_6)))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            $return
          )
        )
      )
    )
  )
)

(define-fun __i__Main..validateRequest$Lifexp_done_8 ((@tmp_8 List_Main..Violations_) (request Main..BuyRequest)) List_Main..Violations_
(let ((@tmp_0 @tmp_8))
    (let (($__ir_ret__ (__i__Main..validateRequest$Lswitchexp_done_3 @tmp_0 request)))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun Main..validateRequest ((request Main..BuyRequest)) List_Main..Violations_
(let ((@tmp_3 (Main..BuyRequest@_requestPrice request)))
    (let (($match_@1196 @tmp_3))
      (let ((@tmp_4 ((_ is Main..Market@box) (BTerm_termvalue @tmp_3))))
        (ite @tmp_4
          (let ((@tmp_5 List_Main..Violations_@@empty))
            (let ((@tmp_0 @tmp_5))
              (let (($__ir_ret__$2 (__i__Main..validateRequest$Lswitchexp_done_3 @tmp_0 request)))
                (let (($__ir_ret__$3 $__ir_ret__$2))
                  (let (($return $__ir_ret__$3))
                    $return
                  )
                )
              )
            )
          )
          (let ((@tmp_6 true))
            (let ((@tmp_7 ($EntityProject_Main..Limit@_price_ (bsqobject_Main..Limit_value (BTerm_termvalue $match_@1196)))))
              (let ((p (__Main..Price__@_0 @tmp_7)))
                (let ((@tmp_9 (Core..__infix__Main..Price__Main..Price_ p BDecimal@zero)))
                  (ite @tmp_9
                    (let ((@tmp_13 (Main..InvalidPrice@cons p)))
                      (let ((@tmp_15 (BTerm@termbox TypeTag_Main..InvalidPrice (Main..InvalidPrice@box @tmp_13))))
                        (let ((@tmp_12 ($ListSingletonCons_1_List_Main..Violations_ @tmp_15)))
                          (let ((@tmp_8$1 @tmp_12))
                            (let (($__ir_ret__$1 (__i__Main..validateRequest$Lifexp_done_8 @tmp_8$1 request)))
                              (let (($__ir_ret__$3 $__ir_ret__$1))
                                (let (($return $__ir_ret__$3))
                                  $return
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                    (let ((@tmp_16 List_Main..Violations_@@empty))
                      (let ((@tmp_8 @tmp_16))
                        (let (($__ir_ret__ (__i__Main..validateRequest$Lifexp_done_8 @tmp_8 request)))
                          (let (($__ir_ret__$3 $__ir_ret__))
                            (let (($return $__ir_ret__$3))
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

(define-fun $ListSingletonCons_1_List_Main..RejectReason_ ((arg0 Main..RejectReason)) List_Main..RejectReason_
(List_Main..RejectReason_@cons (seq.++ (seq.unit arg0)))
)

(define-fun Main..lockinPrice ((requestPrice BTerm) (marketPrice Main..Price)) Main..Price
(let (($match_@1820 requestPrice))
    (let ((@tmp_1 ((_ is Main..Market@box) (BTerm_termvalue requestPrice))))
      (ite @tmp_1
        (let (($__ir_ret__$1 marketPrice))
          (let (($__ir_ret__$2 $__ir_ret__$1))
            (let (($return $__ir_ret__$2))
              $return
            )
          )
        )
        (let ((@tmp_3 true))
          (let ((@tmp_4 ($EntityProject_Main..Limit@_price_ (bsqobject_Main..Limit_value (BTerm_termvalue $match_@1820)))))
            (let ((p (__Main..Price__@_0 @tmp_4)))
              (let (($__ir_ret__ p))
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
    )
  )
)

(define-fun Core..*_infix__Main..Price__Decimal_ ((l Main..Price) (r BDecimal)) Main..Price
(let ((@tmp_4 l))
    (let ((@tmp_1 (* @tmp_4 r)))
      (let ((@tmp_0 @tmp_1))
        (let (($__ir_ret__ @tmp_0))
          (let (($return $__ir_ret__))
            $return
          )
        )
      )
    )
  )
)

(define-fun ListOps..s_list_empty_T_Main..RejectReason_ ((l List_Main..RejectReason_)) Bool
(= l List_Main..RejectReason_@@empty)
)

(define-fun ListOps..s_list_append_T_Main..RejectReason_ ((l List_Main..RejectReason_) (r List_Main..RejectReason_)) List_Main..RejectReason_
(List_Main..RejectReason_@cons (seq.++ (List_Main..RejectReason__seq l) (List_Main..RejectReason__seq r)))
)

(define-fun List_Main..RejectReason_..append_T_Main..RejectReason_ ((this List_Main..RejectReason_) (l List_Main..RejectReason_)) List_Main..RejectReason_
(let ((@tmp_1 (ListOps..s_list_empty_T_Main..RejectReason_ this)))
    (let ((@tmp_3 (ListOps..s_list_empty_T_Main..RejectReason_ l)))
      (let ((@tmp_0 (and @tmp_1 @tmp_3)))
        (ite @tmp_0
          (let ((@tmp_5 List_Main..RejectReason_@@empty))
            (let (($__ir_ret__$3 @tmp_5))
              (let (($__ir_ret__$4 $__ir_ret__$3))
                (let (($return $__ir_ret__$4))
                  $return
                )
              )
            )
          )
          (let ((@tmp_6 (ListOps..s_list_empty_T_Main..RejectReason_ this)))
            (ite @tmp_6
              (let (($__ir_ret__$2 l))
                (let (($__ir_ret__$4 $__ir_ret__$2))
                  (let (($return $__ir_ret__$4))
                    $return
                  )
                )
              )
              (let ((@tmp_9 (ListOps..s_list_empty_T_Main..RejectReason_ l)))
                (ite @tmp_9
                  (let (($__ir_ret__$1 this))
                    (let (($__ir_ret__$4 $__ir_ret__$1))
                      (let (($return $__ir_ret__$4))
                        $return
                      )
                    )
                  )
                  (let ((@tmp_12 (ListOps..s_list_append_T_Main..RejectReason_ this l)))
                    (let (($__ir_ret__ @tmp_12))
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

(define-fun __i__Main..acceptability$Lifexp_done_6 ((@tmp_9 List_Main..RejectReason_) (availabilityCheck List_Main..RejectReason_)) List_Main..RejectReason_
(let ((priceCheck @tmp_9))
    (let ((@tmp_24 (List_Main..RejectReason_..append_T_Main..RejectReason_ availabilityCheck @tmp_9)))
      (let (($__ir_ret__ @tmp_24))
        (let (($return $__ir_ret__))
          $return
        )
      )
    )
  )
)

(define-fun __i__Main..acceptability$Lifexp_done_3 ((@tmp_0 List_Main..RejectReason_) (marketPrice Main..Price) (request Main..BuyRequest)) List_Main..RejectReason_
(let ((availabilityCheck @tmp_0))
    (let ((@tmp_14 (Main..BuyRequest@_requestPrice request)))
      (let ((@tmp_11 (Main..lockinPrice @tmp_14 marketPrice)))
        (let ((@tmp_16 (Core..*_infix__Main..Price__Decimal_ marketPrice 0.9)))
          (let ((@tmp_10 (Core..__infix__Main..Price__Main..Price_ @tmp_11 @tmp_16)))
            (ite @tmp_10
              (let ((@tmp_19 ($ListSingletonCons_1_List_Main..RejectReason_ Main..RejectReason..disagreeablePrice)))
                (let ((@tmp_9$1 @tmp_19))
                  (let (($__ir_ret__$1 (__i__Main..acceptability$Lifexp_done_6 @tmp_9$1 availabilityCheck)))
                    (let (($__ir_ret__$2 $__ir_ret__$1))
                      (let (($return $__ir_ret__$2))
                        $return
                      )
                    )
                  )
                )
              )
              (let ((@tmp_21 List_Main..RejectReason_@@empty))
                (let ((@tmp_9 @tmp_21))
                  (let (($__ir_ret__ (__i__Main..acceptability$Lifexp_done_6 @tmp_9 availabilityCheck)))
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
        )
      )
    )
  )
)

(define-fun Main..acceptability ((request Main..BuyRequest) (marketPrice Main..Price) (availableInventory Main..Quantity)) List_Main..RejectReason_
(let ((@tmp_5 (Main..BuyRequest@_quantity request)))
    (let ((@tmp_1 (Core..__infix__Main..Quantity__Main..Quantity_ availableInventory @tmp_5)))
      (ite @tmp_1
        (let ((@tmp_6 ($ListSingletonCons_1_List_Main..RejectReason_ Main..RejectReason..insufficientInventory)))
          (let ((@tmp_0$1 @tmp_6))
            (let (($__ir_ret__$1 (__i__Main..acceptability$Lifexp_done_3 @tmp_0$1 marketPrice request)))
              (let (($__ir_ret__$2 $__ir_ret__$1))
                (let (($return $__ir_ret__$2))
                  $return
                )
              )
            )
          )
        )
        (let ((@tmp_8 List_Main..RejectReason_@@empty))
          (let ((@tmp_0 @tmp_8))
            (let (($__ir_ret__ (__i__Main..acceptability$Lifexp_done_3 @tmp_0 marketPrice request)))
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
  )
)

(define-fun List_Main..Violations_..empty_T_Main..Violations_ ((this List_Main..Violations_)) Bool
(let ((@tmp_0 (ListOps..s_list_empty_T_Main..Violations_ this)))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun List_Main..RejectReason_..empty_T_Main..RejectReason_ ((this List_Main..RejectReason_)) Bool
(let ((@tmp_0 (ListOps..s_list_empty_T_Main..RejectReason_ this)))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun Main..processBuy ((request Main..BuyRequest) (marketPrice Main..Price) (availableInventory Main..Quantity)) BTerm
(let ((@tmp_0 (Main..validateRequest request)))
    (let ((violations @tmp_0))
      (let ((@tmp_2 (Main..acceptability request marketPrice availableInventory)))
        (let ((rejections @tmp_2))
          (let ((@tmp_9 (Main..BuyRequest@_requestPrice request)))
            (let ((@tmp_6 (Main..lockinPrice @tmp_9 marketPrice)))
              (let ((lockPrice @tmp_6))
                (let ((@tmp_14 (List_Main..Violations_..empty_T_Main..Violations_ @tmp_0)))
                  (let ((@tmp_11 (not @tmp_14)))
                    (ite @tmp_11
                      (let ((@tmp_18 (Main..BuyRequest@_id request)))
                        (let ((@tmp_15 (Main..BuyInvalid@cons @tmp_18 violations)))
                          (let ((@tmp_20 (BTerm@termbox TypeTag_Main..BuyInvalid (Main..BuyInvalid@box @tmp_15))))
                            (let (($__ir_ret__$2 @tmp_20))
                              (let (($__ir_ret__$3 $__ir_ret__$2))
                                (let (($return $__ir_ret__$3))
                                  $return
                                )
                              )
                            )
                          )
                        )
                      )
                      (let ((@tmp_24 (List_Main..RejectReason_..empty_T_Main..RejectReason_ rejections)))
                        (let ((@tmp_21 (not @tmp_24)))
                          (ite @tmp_21
                            (let ((@tmp_28 (Main..BuyRequest@_id request)))
                              (let ((@tmp_25 (Main..BuyRejected@cons @tmp_28 rejections)))
                                (let ((@tmp_30 (BTerm@termbox TypeTag_Main..BuyRejected (Main..BuyRejected@box @tmp_25))))
                                  (let (($__ir_ret__$1 @tmp_30))
                                    (let (($__ir_ret__$3 $__ir_ret__$1))
                                      (let (($return $__ir_ret__$3))
                                        $return
                                      )
                                    )
                                  )
                                )
                              )
                            )
                            (let ((@tmp_34 (Main..BuyRequest@_id request)))
                              (let ((@tmp_37 (Main..BuyRequest@_product request)))
                                (let ((@tmp_41 (Main..BuyRequest@_quantity request)))
                                  (let ((@tmp_31 (Main..BuyAccepted@cons @tmp_34 @tmp_37 lockPrice @tmp_41)))
                                    (let ((@tmp_42 (BTerm@termbox TypeTag_Main..BuyAccepted (Main..BuyAccepted@box @tmp_31))))
                                      (let (($__ir_ret__ @tmp_42))
                                        (let (($__ir_ret__$3 $__ir_ret__))
                                          (let (($return $__ir_ret__$3))
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

(define-fun Main..processSell ((request Main..SellRequest) (marketPrice Main..Price)) BTerm
(let ((@tmp_3 (Main..SellRequest@_requestPrice request)))
    (let ((@tmp_0 (Main..lockinPrice @tmp_3 marketPrice)))
      (let ((lockPrice @tmp_0))
        (let ((@tmp_8 (Main..SellRequest@_id request)))
          (let ((@tmp_5 (Main..SellAccepted@cons @tmp_8 @tmp_0)))
            (let ((@tmp_10 (BTerm@termbox TypeTag_Main..SellAccepted (Main..SellAccepted@box @tmp_5))))
              (let (($__ir_ret__ @tmp_10))
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
)

(define-fun Main..main ((request BTerm) (marketPrice Main..Price) (startOfDayPosition Main..Quantity) (responses List_Main..BuyResponse_)) $Result_BTerm
(let ((@tmp_2 ((_ is Main..BuyRequest@box) (BTerm_termvalue request))))
    (ite @tmp_2
      (let ((_@tmpvar@4 (Main..availability startOfDayPosition responses)))
        (ite ((_ is $Result_Main..Quantity@error) _@tmpvar@4)
          ($Result_BTerm@error ($Result_Main..Quantity@error_value _@tmpvar@4))
          (let ((@tmp_3 ($Result_Main..Quantity@success_value _@tmpvar@4)))
            (let ((availableInventory @tmp_3))
              (let ((@tmp_10 (bsqobject_Main..BuyRequest_value (BTerm_termvalue request))))
                (let ((@tmp_6 (Main..processBuy @tmp_10 marketPrice @tmp_3)))
                  (let ((@tmp_11 @tmp_6))
                    (let (($__ir_ret__$1 @tmp_11))
                      (let (($__ir_ret__$2 $__ir_ret__$1))
                        (let (($return $__ir_ret__$2))
                          ($Result_BTerm@success $return)
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
      (let ((@tmp_15 (bsqobject_Main..SellRequest_value (BTerm_termvalue request))))
        (let ((@tmp_12 (Main..processSell @tmp_15 marketPrice)))
          (let ((@tmp_16 @tmp_12))
            (let (($__ir_ret__ @tmp_16))
              (let (($__ir_ret__$2 $__ir_ret__))
                (let (($return $__ir_ret__$2))
                  ($Result_BTerm@success $return)
                )
              )
            )
          )
        )
      )
    )
  )
)

(define-fun _@@cons_Main..Price_entrypoint ((path HavocSequence)) $Result_Main..Price
(let ((vv (_@@cons_Decimal_entrypoint path)))
    (ite ((_ is $Result_BDecimal@success) vv)
      ($Result_Main..Price@success ($Result_BDecimal@success_value vv))
      ($Result_Main..Price@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..Limit..@@constructor (($price Main..Price)) Main..Limit
(let (($__ir_ret__ (Main..Limit@cons $price)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..Limit_entrypoint ((path HavocSequence)) $Result_Main..Limit
(let ((_@tmpvar@6 (_@@cons_Main..Price_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))))
    (ite (and ((_ is $Result_Main..Price@success) _@tmpvar@6) true)
      ($Result_Main..Limit@success (Main..Limit..@@constructor ($Result_Main..Price@success_value _@tmpvar@6)))
      ($Result_Main..Limit@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..Market..@@constructor () Main..Market
(let (($__ir_ret__ Main..Market@cons))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..Market_entrypoint ((path HavocSequence)) $Result_Main..Market
(let ()
    (ite true
      ($Result_Main..Market@success Main..Market..@@constructor)
      ($Result_Main..Market@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_Main..OrderPrice_entrypoint ((path HavocSequence)) $Result_BTerm
(let ((cc (UnionChoice@UFCons_API path)))
    (ite (= cc 0)
      (let ((_@tmpvar@8 (_@@cons_Main..Limit_entrypoint (seq.++ path (seq.unit 0)))))
        (ite ((_ is $Result_Main..Limit@success) _@tmpvar@8)
          ($Result_BTerm@success (BTerm@termbox TypeTag_Main..Limit (Main..Limit@box ($Result_Main..Limit@success_value _@tmpvar@8))))
          ($Result_BTerm@error ErrorID_AssumeCheck)
        )
      )
      (ite (= cc 1)
        (let ((_@tmpvar@7 (_@@cons_Main..Market_entrypoint (seq.++ path (seq.unit 1)))))
          (ite ((_ is $Result_Main..Market@success) _@tmpvar@7)
            ($Result_BTerm@success (BTerm@termbox TypeTag_Main..Market (Main..Market@box ($Result_Main..Market@success_value _@tmpvar@7))))
            ($Result_BTerm@error ErrorID_AssumeCheck)
          )
        )
        ($Result_BTerm@error ErrorID_AssumeCheck)
      )
    )
  )
)

(define-fun _@@cons_Main..Quantity_entrypoint ((path HavocSequence)) $Result_Main..Quantity
(let ((vv (_@@cons_Nat_entrypoint path)))
    (ite ((_ is $Result_BNat@success) vv)
      ($Result_Main..Quantity@success ($Result_BNat@success_value vv))
      ($Result_Main..Quantity@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..BuyRequest..@@constructor (($id BString) ($requestPrice BTerm) ($quantity Main..Quantity) ($product BString)) Main..BuyRequest
(let (($__ir_ret__ (Main..BuyRequest@cons $id $requestPrice $quantity $product)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..BuyRequest_entrypoint ((path HavocSequence)) $Result_Main..BuyRequest
(let ((_@tmpvar@5 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))) (_@tmpvar@9 (_@@cons_Main..OrderPrice_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 1)))) (_@tmpvar@10 (_@@cons_Main..Quantity_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 2)))) (_@tmpvar@11 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 3)))))
    (ite (and ((_ is $Result_BString@success) _@tmpvar@5) ((_ is $Result_BTerm@success) _@tmpvar@9) ((_ is $Result_Main..Quantity@success) _@tmpvar@10) ((_ is $Result_BString@success) _@tmpvar@11) true)
      ($Result_Main..BuyRequest@success (Main..BuyRequest..@@constructor ($Result_BString@success_value _@tmpvar@5) ($Result_BTerm@success_value _@tmpvar@9) ($Result_Main..Quantity@success_value _@tmpvar@10) ($Result_BString@success_value _@tmpvar@11)))
      ($Result_Main..BuyRequest@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..SellRequest..@@constructor (($id BString) ($requestPrice BTerm) ($dealId BString)) Main..SellRequest
(let (($__ir_ret__ (Main..SellRequest@cons $id $requestPrice $dealId)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..SellRequest_entrypoint ((path HavocSequence)) $Result_Main..SellRequest
(let ((_@tmpvar@12 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))) (_@tmpvar@13 (_@@cons_Main..OrderPrice_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 1)))) (_@tmpvar@14 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 2)))))
    (ite (and ((_ is $Result_BString@success) _@tmpvar@12) ((_ is $Result_BTerm@success) _@tmpvar@13) ((_ is $Result_BString@success) _@tmpvar@14) true)
      ($Result_Main..SellRequest@success (Main..SellRequest..@@constructor ($Result_BString@success_value _@tmpvar@12) ($Result_BTerm@success_value _@tmpvar@13) ($Result_BString@success_value _@tmpvar@14)))
      ($Result_Main..SellRequest@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_Main..Request_entrypoint ((path HavocSequence)) $Result_BTerm
(let ((cc (UnionChoice@UFCons_API path)))
    (ite (= cc 0)
      (let ((_@tmpvar@16 (_@@cons_Main..BuyRequest_entrypoint (seq.++ path (seq.unit 0)))))
        (ite ((_ is $Result_Main..BuyRequest@success) _@tmpvar@16)
          ($Result_BTerm@success (BTerm@termbox TypeTag_Main..BuyRequest (Main..BuyRequest@box ($Result_Main..BuyRequest@success_value _@tmpvar@16))))
          ($Result_BTerm@error ErrorID_AssumeCheck)
        )
      )
      (ite (= cc 1)
        (let ((_@tmpvar@15 (_@@cons_Main..SellRequest_entrypoint (seq.++ path (seq.unit 1)))))
          (ite ((_ is $Result_Main..SellRequest@success) _@tmpvar@15)
            ($Result_BTerm@success (BTerm@termbox TypeTag_Main..SellRequest (Main..SellRequest@box ($Result_Main..SellRequest@success_value _@tmpvar@15))))
            ($Result_BTerm@error ErrorID_AssumeCheck)
          )
        )
        ($Result_BTerm@error ErrorID_AssumeCheck)
      )
    )
  )
)

(define-fun Main..BuyAccepted..@@constructor (($id BString) ($product BString) ($price Main..Price) ($quantity Main..Quantity)) Main..BuyAccepted
(let (($__ir_ret__ (Main..BuyAccepted@cons $id $product $price $quantity)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..BuyAccepted_entrypoint ((path HavocSequence)) $Result_Main..BuyAccepted
(let ((_@tmpvar@17 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))) (_@tmpvar@18 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 1)))) (_@tmpvar@19 (_@@cons_Main..Price_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 2)))) (_@tmpvar@20 (_@@cons_Main..Quantity_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 3)))))
    (ite (and ((_ is $Result_BString@success) _@tmpvar@17) ((_ is $Result_BString@success) _@tmpvar@18) ((_ is $Result_Main..Price@success) _@tmpvar@19) ((_ is $Result_Main..Quantity@success) _@tmpvar@20) true)
      ($Result_Main..BuyAccepted@success (Main..BuyAccepted..@@constructor ($Result_BString@success_value _@tmpvar@17) ($Result_BString@success_value _@tmpvar@18) ($Result_Main..Price@success_value _@tmpvar@19) ($Result_Main..Quantity@success_value _@tmpvar@20)))
      ($Result_Main..BuyAccepted@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..InvalidPrice..@@constructor (($price Main..Price)) Main..InvalidPrice
(let (($__ir_ret__ (Main..InvalidPrice@cons $price)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..InvalidPrice_entrypoint ((path HavocSequence)) $Result_Main..InvalidPrice
(let ((_@tmpvar@22 (_@@cons_Main..Price_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))))
    (ite (and ((_ is $Result_Main..Price@success) _@tmpvar@22) true)
      ($Result_Main..InvalidPrice@success (Main..InvalidPrice..@@constructor ($Result_Main..Price@success_value _@tmpvar@22)))
      ($Result_Main..InvalidPrice@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun Main..InvalidQuantity..@@constructor (($quantity Main..Quantity)) Main..InvalidQuantity
(let (($__ir_ret__ (Main..InvalidQuantity@cons $quantity)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..InvalidQuantity_entrypoint ((path HavocSequence)) $Result_Main..InvalidQuantity
(let ((_@tmpvar@23 (_@@cons_Main..Quantity_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))))
    (ite (and ((_ is $Result_Main..Quantity@success) _@tmpvar@23) true)
      ($Result_Main..InvalidQuantity@success (Main..InvalidQuantity..@@constructor ($Result_Main..Quantity@success_value _@tmpvar@23)))
      ($Result_Main..InvalidQuantity@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_Main..Violations_entrypoint ((path HavocSequence)) $Result_BTerm
(let ((cc (UnionChoice@UFCons_API path)))
    (ite (= cc 0)
      (let ((_@tmpvar@25 (_@@cons_Main..InvalidPrice_entrypoint (seq.++ path (seq.unit 0)))))
        (ite ((_ is $Result_Main..InvalidPrice@success) _@tmpvar@25)
          ($Result_BTerm@success (BTerm@termbox TypeTag_Main..InvalidPrice (Main..InvalidPrice@box ($Result_Main..InvalidPrice@success_value _@tmpvar@25))))
          ($Result_BTerm@error ErrorID_AssumeCheck)
        )
      )
      (ite (= cc 1)
        (let ((_@tmpvar@24 (_@@cons_Main..InvalidQuantity_entrypoint (seq.++ path (seq.unit 1)))))
          (ite ((_ is $Result_Main..InvalidQuantity@success) _@tmpvar@24)
            ($Result_BTerm@success (BTerm@termbox TypeTag_Main..InvalidQuantity (Main..InvalidQuantity@box ($Result_Main..InvalidQuantity@success_value _@tmpvar@24))))
            ($Result_BTerm@error ErrorID_AssumeCheck)
          )
        )
        ($Result_BTerm@error ErrorID_AssumeCheck)
      )
    )
  )
)

(define-fun _@@cons_List_Main..Violations__entrypoint ((path HavocSequence)) $Result_List_Main..Violations_
(let ((len (ContainerSize@UFCons_API path)))
    (ite (or (< len 0) (< @CONTAINERMAX len))
      ($Result_List_Main..Violations_@error ErrorID_AssumeCheck)
      (ite (= len 0)
        ($Result_List_Main..Violations_@success List_Main..Violations_@@empty)
        (let ((carg_0 (_@@cons_Main..Violations_entrypoint (seq.++ path (seq.unit 0)))))
          (ite ((_ is $Result_BTerm@error) carg_0)
            ($Result_List_Main..Violations_@error ErrorID_AssumeCheck)
            (ite (= len 1)
              ($Result_List_Main..Violations_@success (List_Main..Violations_@cons (seq.++ (seq.unit ($Result_BTerm@success_value carg_0)))))
              (let ((carg_1 (_@@cons_Main..Violations_entrypoint (seq.++ path (seq.unit 1)))))
                (ite ((_ is $Result_BTerm@error) carg_1)
                  ($Result_List_Main..Violations_@error ErrorID_AssumeCheck)
                  (ite (= len 2)
                    ($Result_List_Main..Violations_@success (List_Main..Violations_@cons (seq.++ (seq.unit ($Result_BTerm@success_value carg_0)) (seq.unit ($Result_BTerm@success_value carg_1)))))
                    (let ((carg_2 (_@@cons_Main..Violations_entrypoint (seq.++ path (seq.unit 2)))))
                      (ite ((_ is $Result_BTerm@error) carg_2)
                        ($Result_List_Main..Violations_@error ErrorID_AssumeCheck)
                        ($Result_List_Main..Violations_@success (List_Main..Violations_@cons (seq.++ (seq.unit ($Result_BTerm@success_value carg_0)) (seq.unit ($Result_BTerm@success_value carg_1)) (seq.unit ($Result_BTerm@success_value carg_2)))))
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

(define-fun Main..BuyInvalid..@@constructor (($id BString) ($violations List_Main..Violations_)) Main..BuyInvalid
(let (($__ir_ret__ (Main..BuyInvalid@cons $id $violations)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..BuyInvalid_entrypoint ((path HavocSequence)) $Result_Main..BuyInvalid
(let ((_@tmpvar@21 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))) (_@tmpvar@26 (_@@cons_List_Main..Violations__entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 1)))))
    (ite (and ((_ is $Result_BString@success) _@tmpvar@21) ((_ is $Result_List_Main..Violations_@success) _@tmpvar@26) true)
      ($Result_Main..BuyInvalid@success (Main..BuyInvalid..@@constructor ($Result_BString@success_value _@tmpvar@21) ($Result_List_Main..Violations_@success_value _@tmpvar@26)))
      ($Result_Main..BuyInvalid@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_Main..RejectReason_entrypoint ((path HavocSequence)) $Result_Main..RejectReason
(let ((vv (BNat@UFCons_API path)))
    (ite (and (<= 0 vv) (< vv 2))
      ($Result_Main..RejectReason@success vv)
      ($Result_Main..RejectReason@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_List_Main..RejectReason__entrypoint ((path HavocSequence)) $Result_List_Main..RejectReason_
(let ((len (ContainerSize@UFCons_API path)))
    (ite (or (< len 0) (< @CONTAINERMAX len))
      ($Result_List_Main..RejectReason_@error ErrorID_AssumeCheck)
      (ite (= len 0)
        ($Result_List_Main..RejectReason_@success List_Main..RejectReason_@@empty)
        (let ((carg_0 (_@@cons_Main..RejectReason_entrypoint (seq.++ path (seq.unit 0)))))
          (ite ((_ is $Result_Main..RejectReason@error) carg_0)
            ($Result_List_Main..RejectReason_@error ErrorID_AssumeCheck)
            (ite (= len 1)
              ($Result_List_Main..RejectReason_@success (List_Main..RejectReason_@cons (seq.++ (seq.unit ($Result_Main..RejectReason@success_value carg_0)))))
              (let ((carg_1 (_@@cons_Main..RejectReason_entrypoint (seq.++ path (seq.unit 1)))))
                (ite ((_ is $Result_Main..RejectReason@error) carg_1)
                  ($Result_List_Main..RejectReason_@error ErrorID_AssumeCheck)
                  (ite (= len 2)
                    ($Result_List_Main..RejectReason_@success (List_Main..RejectReason_@cons (seq.++ (seq.unit ($Result_Main..RejectReason@success_value carg_0)) (seq.unit ($Result_Main..RejectReason@success_value carg_1)))))
                    (let ((carg_2 (_@@cons_Main..RejectReason_entrypoint (seq.++ path (seq.unit 2)))))
                      (ite ((_ is $Result_Main..RejectReason@error) carg_2)
                        ($Result_List_Main..RejectReason_@error ErrorID_AssumeCheck)
                        ($Result_List_Main..RejectReason_@success (List_Main..RejectReason_@cons (seq.++ (seq.unit ($Result_Main..RejectReason@success_value carg_0)) (seq.unit ($Result_Main..RejectReason@success_value carg_1)) (seq.unit ($Result_Main..RejectReason@success_value carg_2)))))
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

(define-fun Main..BuyRejected..@@constructor (($id BString) ($reasons List_Main..RejectReason_)) Main..BuyRejected
(let (($__ir_ret__ (Main..BuyRejected@cons $id $reasons)))
    (let (($return $__ir_ret__))
      $return
    )
  )
)

(define-fun _@@cons_Main..BuyRejected_entrypoint ((path HavocSequence)) $Result_Main..BuyRejected
(let ((_@tmpvar@27 (_@@cons_String_entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 0)))) (_@tmpvar@28 (_@@cons_List_Main..RejectReason__entrypoint (seq.++ (seq.++ path (seq.unit 0)) (seq.unit 1)))))
    (ite (and ((_ is $Result_BString@success) _@tmpvar@27) ((_ is $Result_List_Main..RejectReason_@success) _@tmpvar@28) true)
      ($Result_Main..BuyRejected@success (Main..BuyRejected..@@constructor ($Result_BString@success_value _@tmpvar@27) ($Result_List_Main..RejectReason_@success_value _@tmpvar@28)))
      ($Result_Main..BuyRejected@error ErrorID_AssumeCheck)
    )
  )
)

(define-fun _@@cons_Main..BuyResponse_entrypoint ((path HavocSequence)) $Result_BTerm
(let ((cc (UnionChoice@UFCons_API path)))
    (ite (= cc 0)
      (let ((_@tmpvar@31 (_@@cons_Main..BuyAccepted_entrypoint (seq.++ path (seq.unit 0)))))
        (ite ((_ is $Result_Main..BuyAccepted@success) _@tmpvar@31)
          ($Result_BTerm@success (BTerm@termbox TypeTag_Main..BuyAccepted (Main..BuyAccepted@box ($Result_Main..BuyAccepted@success_value _@tmpvar@31))))
          ($Result_BTerm@error ErrorID_AssumeCheck)
        )
      )
      (ite (= cc 1)
        (let ((_@tmpvar@30 (_@@cons_Main..BuyInvalid_entrypoint (seq.++ path (seq.unit 1)))))
          (ite ((_ is $Result_Main..BuyInvalid@success) _@tmpvar@30)
            ($Result_BTerm@success (BTerm@termbox TypeTag_Main..BuyInvalid (Main..BuyInvalid@box ($Result_Main..BuyInvalid@success_value _@tmpvar@30))))
            ($Result_BTerm@error ErrorID_AssumeCheck)
          )
        )
        (ite (= cc 2)
          (let ((_@tmpvar@29 (_@@cons_Main..BuyRejected_entrypoint (seq.++ path (seq.unit 2)))))
            (ite ((_ is $Result_Main..BuyRejected@success) _@tmpvar@29)
              ($Result_BTerm@success (BTerm@termbox TypeTag_Main..BuyRejected (Main..BuyRejected@box ($Result_Main..BuyRejected@success_value _@tmpvar@29))))
              ($Result_BTerm@error ErrorID_AssumeCheck)
            )
          )
          ($Result_BTerm@error ErrorID_AssumeCheck)
        )
      )
    )
  )
)

(define-fun _@@cons_List_Main..BuyResponse__entrypoint ((path HavocSequence)) $Result_List_Main..BuyResponse_
(let ((len (ContainerSize@UFCons_API path)))
    (ite (or (< len 0) (< @CONTAINERMAX len))
      ($Result_List_Main..BuyResponse_@error ErrorID_AssumeCheck)
      (ite (= len 0)
        ($Result_List_Main..BuyResponse_@success List_Main..BuyResponse_@@empty)
        (let ((carg_0 (_@@cons_Main..BuyResponse_entrypoint (seq.++ path (seq.unit 0)))))
          (ite ((_ is $Result_BTerm@error) carg_0)
            ($Result_List_Main..BuyResponse_@error ErrorID_AssumeCheck)
            (ite (= len 1)
              ($Result_List_Main..BuyResponse_@success (List_Main..BuyResponse_@cons (seq.++ (seq.unit ($Result_BTerm@success_value carg_0)))))
              (let ((carg_1 (_@@cons_Main..BuyResponse_entrypoint (seq.++ path (seq.unit 1)))))
                (ite ((_ is $Result_BTerm@error) carg_1)
                  ($Result_List_Main..BuyResponse_@error ErrorID_AssumeCheck)
                  (ite (= len 2)
                    ($Result_List_Main..BuyResponse_@success (List_Main..BuyResponse_@cons (seq.++ (seq.unit ($Result_BTerm@success_value carg_0)) (seq.unit ($Result_BTerm@success_value carg_1)))))
                    (let ((carg_2 (_@@cons_Main..BuyResponse_entrypoint (seq.++ path (seq.unit 2)))))
                      (ite ((_ is $Result_BTerm@error) carg_2)
                        ($Result_List_Main..BuyResponse_@error ErrorID_AssumeCheck)
                        ($Result_List_Main..BuyResponse_@success (List_Main..BuyResponse_@cons (seq.++ (seq.unit ($Result_BTerm@success_value carg_0)) (seq.unit ($Result_BTerm@success_value carg_1)) (seq.unit ($Result_BTerm@success_value carg_2)))))
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

(define-fun constexp_order.bsq_k14_constexp..5@59..zero () Main..Quantity
(let ((@tmp_0 0))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun constexp_order.bsq_k14_constexp..29@520..disagreeablePrice () Main..RejectReason
(let ((@tmp_0 1))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(define-fun constexp_order.bsq_k14_constexp..29@520..insufficientInventory () Main..RejectReason
(let ((@tmp_0 0))
    (let (($__ir_ret__ @tmp_0))
      (let (($return $__ir_ret__))
        $return
      )
    )
  )
)

(assert (= Main..Quantity..zero constexp_order.bsq_k14_constexp..5@59..zero))
(assert (= Main..RejectReason..disagreeablePrice constexp_order.bsq_k14_constexp..29@520..disagreeablePrice))
(assert (= Main..RejectReason..insufficientInventory constexp_order.bsq_k14_constexp..29@520..insufficientInventory))

(declare-const request $Result_BTerm)
(assert (= request (_@@cons_Main..Request_entrypoint (seq.++ (seq.unit 0) (seq.unit 0)))))
(assert ((_ is $Result_BTerm@success) request))
(declare-const marketPrice $Result_Main..Price)
(assert (= marketPrice (_@@cons_Main..Price_entrypoint (seq.++ (seq.unit 0) (seq.unit 1)))))
(assert ((_ is $Result_Main..Price@success) marketPrice))
(declare-const startOfDayPosition $Result_Main..Quantity)
(assert (= startOfDayPosition (_@@cons_Main..Quantity_entrypoint (seq.++ (seq.unit 0) (seq.unit 2)))))
(assert ((_ is $Result_Main..Quantity@success) startOfDayPosition))
(declare-const responses $Result_List_Main..BuyResponse_)
(assert (= responses (_@@cons_List_Main..BuyResponse__entrypoint (seq.++ (seq.unit 0) (seq.unit 3)))))
(assert ((_ is $Result_List_Main..BuyResponse_@success) responses))
(declare-const _@smtres@ $Result_BTerm)
(assert (= _@smtres@ (Main..main ($Result_BTerm@success_value request) ($Result_Main..Price@success_value marketPrice) ($Result_Main..Quantity@success_value startOfDayPosition) ($Result_List_Main..BuyResponse_@success_value responses))))
(assert ((_ is $Result_BTerm@success) _@smtres@))
(assert [Not a Bool Result])
