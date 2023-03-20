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

(declare-fun @Float_unary (@Float) @Float)
(declare-fun @Decimal_unary (@Decimal) @Decimal)
(declare-fun @Rational_unary (@Rational) @Rational)

(declare-fun @Float_binary (@Float @Float) @Float)
(declare-fun @Decimal_binary (@Decimal @Decimal) @Decimal)
(declare-fun @Rational_bainry (@Rational @Rational) @Rational)

;;
;; Primitive datatypes 
;;
(declare-datatypes (
      (@None 0)
      (@Nothing 0)
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
      ; UUID4 -> @UUID4
      ; UUID7 -> @UUID7
      ; SHAContentHash -> (_ BitVec 16)
      ; LatLongCoordinate -> @LatLongCoordinate
    ) (
      ( (@none) ) 
      ( (@nothing) )
))
