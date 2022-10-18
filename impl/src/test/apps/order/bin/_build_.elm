
module BSQMain exposing (..)

import Regex exposing(..)

type TypeTag = 
    TypeTag_Invalid
    | TypeTag_BigInt
    | TypeTag_BigNat
    | TypeTag_Bool
    | TypeTag_BufferCompression
    | TypeTag_BufferFormat
    | TypeTag_ByteBuffer
    | TypeTag_CalendarDate
    | TypeTag_DateTime
    | TypeTag_Decimal
    | TypeTag_Float
    | TypeTag_ISOTimeStamp
    | TypeTag_Int
    | TypeTag_LatLongCoordinate
    | TypeTag_ListOps
    | TypeTag_List_Main__BuyResponse_
    | TypeTag_List_Main__Quantity_
    | TypeTag_List_Main__RejectReason_
    | TypeTag_List_Main__Violations_
    | TypeTag_LogicalTime
    | TypeTag_Main__BuyAccepted
    | TypeTag_Main__BuyInvalid
    | TypeTag_Main__BuyRejected
    | TypeTag_Main__BuyRequest
    | TypeTag_Main__InvalidPrice
    | TypeTag_Main__InvalidQuantity
    | TypeTag_Main__Limit
    | TypeTag_Main__Market
    | TypeTag_Main__Price
    | TypeTag_Main__Quantity
    | TypeTag_Main__RejectReason
    | TypeTag_Main__SellAccepted
    | TypeTag_Main__SellRequest
    | TypeTag_Nat
    | TypeTag_None
    | TypeTag_Nothing
    | TypeTag_Rational
    | TypeTag_Regex
    | TypeTag_RelativeTime
    | TypeTag_SHAContentHash
    | TypeTag_ShaContentHash
    | TypeTag_String
    | TypeTag_TickTime
    | TypeTag_UTCDateTime
    | TypeTag_UUID4
    | TypeTag_UUID7

ordinalOf : TypeTag -> Int
ordinalOf tt = 
    case tt of 
        TypeTag_BigInt -> 
            0
        TypeTag_BigNat -> 
            1
        TypeTag_Bool -> 
            2
        TypeTag_BufferCompression -> 
            3
        TypeTag_BufferFormat -> 
            4
        TypeTag_CalendarDate -> 
            5
        TypeTag_ISOTimeStamp -> 
            6
        TypeTag_Int -> 
            7
        TypeTag_LogicalTime -> 
            8
        TypeTag_Main__Quantity -> 
            9
        TypeTag_Main__RejectReason -> 
            10
        TypeTag_Nat -> 
            11
        TypeTag_None -> 
            12
        TypeTag_RelativeTime -> 
            13
        TypeTag_SHAContentHash -> 
            14
        TypeTag_ShaContentHash -> 
            15
        TypeTag_String -> 
            16
        TypeTag_TickTime -> 
            17
        TypeTag_UTCDateTime -> 
            18
        TypeTag_UUID4 -> 
            19
        TypeTag_UUID7 -> 
            20
        _ -> 
            -1

type AbstractTypeTag = 
    AbstractTypeTag_Invalid
--NO DATA--

type TupleIndexTag = 
    TupleIndexTag_Invalid
--NO DATA--

type RecordPropertyTag = 
    RecordPropertyTag_Invalid
--NO DATA--

subtypeOf : TypeTag -> AbstractTypeTag -> Bool
subtypeOf tt oftype = 
    case (tt, oftype) of 
--NO DATA--
        _ -> 
            False

hasIndex : TypeTag -> TupleIndexTag -> Bool
hasIndex tt oftype = 
    case (tt, oftype) of 
--NO DATA--
        _ -> 
            False

hasProperty : TypeTag -> RecordPropertyTag -> Bool
hasProperty tt oftype = 
    case (tt, oftype) of 
--NO DATA--
        _ -> 
            False

real_zero : Float
real_zero = 0.0

real_one : Float
real_one = 1.0

type alias BInt = 
    Int

type alias BNat = 
    Int

type alias BBigInt = 
    Int

type alias BBigNat = 
    Int

type alias BFloat = 
    Float

type alias BDecimal = 
    Float

type alias BRational = 
    Float

type alias BString = 
    String

type alias BTickTime = 
    Int

type alias BLogicalTime = 
    Int

type alias BUUID4 = 
    String

type alias BUUID7 = 
    String

type alias BSHAContentHash = 
    String

type alias BByteBuffer = 
    {
        format: Int,
        compress: Int,
        data: List Int
    }

bbytebuffer_cons : Int -> Int -> List Int -> BByteBuffer
bbytebuffer_cons f c d = 
    {format = f, compress = c, data = d}

type alias BDateTime = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int,
        tzdata: String
    }

bdatetime_cons : Int -> Int -> Int -> Int -> Int -> String -> BDateTime
bdatetime_cons yy mm dd h m tz = 
    {year = yy, month = mm, day = dd, hour = h, min = m, tzdata = tz}

type alias BUTCDateTime = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int
    }

butcdatetime_cons : Int -> Int -> Int -> Int -> Int -> BUTCDateTime
butcdatetime_cons yy mm dd h m = 
    {year = yy, month = mm, day = dd, hour = h, min = m}

type alias BCalendarDate = 
    {
        year: Int,
        month: Int,
        day: Int
    }

bcalendardate_cons : Int -> Int -> Int -> BCalendarDate
bcalendardate_cons yy mm dd = 
    {year = yy, month = mm, day = dd}

type alias BRelativeTime = 
    {
        hour: Int,
        min: Int
    }

brelativetime_cons : Int -> Int -> BRelativeTime
brelativetime_cons h m = 
    {hour = h, min = m}

type alias BISOTimeStamp = 
    {
        year: Int,
        month: Int,
        day: Int,
        hour: Int,
        min: Int,
        sec: Int,
        millis: Int
    }

bisotimestamp_cons : Int -> Int -> Int -> Int -> Int -> Int -> Int -> BISOTimeStamp
bisotimestamp_cons yy mm dd h m s ms= 
    {year = yy, month = mm, day = dd, hour = h, min = m, sec = s, millis = ms}

type alias BLatLongCoordinate = 
    {
        lat: Float,
        long: Float
    }

blatlongcoordinate_cons : Float -> Float -> BLatLongCoordinate
blatlongcoordinate_cons latv longv = 
    {lat = latv, long = longv}

bInt_zero : BInt
bInt_zero = 
    0

bInt_one : BInt
bInt_one = 
    1

bNat_zero : BNat
bNat_zero = 
    0

bNat_one : BNat
bNat_one = 
    1

bBigInt_zero : BBigInt
bBigInt_zero = 
    0

bBigInt_one : BBigInt
bBigInt_one = 
    1

bBigNat_zero : BBigNat
bBigNat_zero = 
    0

bBigNat_one : BBigNat
bBigNat_one = 
    1

bFloat_zero : BFloat
bFloat_zero = 
    0.0

bFloat_one : BFloat
bFloat_one = 
    1.0

bDecimal_zero : BDecimal
bDecimal_zero = 
    0.0

bDecimal_one : BDecimal
bDecimal_one = 
    1.0

bRational_zero : BRational
bRational_zero = 
    0.0

bRational_one : BRational
bRational_one = 
    1.0

type alias BNone = Int

bsqnone_literal : BNone
bsqnone_literal = 
    0

type alias BNothing = Int

bsqnothing_literal : BNothing
bsqnothing_literal = 
    0

bsqnone_less : BNone -> BNone -> Bool
bsqnone_less _ _ = 
    False

type alias BufferCompression = BNat
type alias BufferFormat = BNat
type alias Main__Quantity = BNat
type alias Main__RejectReason = BNat
type alias Main__Price = BDecimal

bool_less : Bool -> Bool -> Bool
bool_less k1 k2 = 
    (not k1) && k2

bint_less : BInt -> BInt -> Bool
bint_less k1 k2 = 
    k1 < k2

bnat_less : BNat -> BNat -> Bool
bnat_less k1 k2 = 
    k1 < k2

bbigint_less : BBigInt -> BBigInt -> Bool
bbigint_less k1 k2 = 
    k1 < k2

bbignat_less : BBigNat -> BBigNat -> Bool
bbignat_less k1 k2 = 
    k1 < k2

bstring_less : BString -> BString -> Bool
bstring_less k1 k2 = 
    k1 < k2

butcdatetime_less : BUTCDateTime -> BUTCDateTime -> Bool
butcdatetime_less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            if k1.day /= k2.day then
                k1.day < k2.day else
                if k1.hour /= k2.hour then
                    k1.hour < k2.hour else
                    k1.min < k2.min

bcalendardate_less : BCalendarDate -> BCalendarDate -> Bool
bcalendardate_less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            k1.day < k2.day

brelativetime_less : BRelativeTime -> BRelativeTime -> Bool
brelativetime_less k1 k2 = 
    if k1.hour /= k2.hour then
        k1.hour < k2.hour else
        k1.min < k2.min

bticktime_less : BTickTime -> BTickTime -> Bool
bticktime_less k1 k2 = 
    k1 < k2

blogicaltime_less : BLogicalTime -> BLogicalTime -> Bool
blogicaltime_less k1 k2 = 
    k1 < k2

bisotimestamp_less : BISOTimeStamp -> BISOTimeStamp -> Bool
bisotimestamp_less k1 k2 = 
    if k1.year /= k2.year then
        k1.year < k2.year else
        if k1.month /= k2.month then 
            k1.month < k2.month else
            if k1.day /= k2.day then
                k1.day < k2.day else
                if k1.hour /= k2.hour then
                    k1.hour < k2.hour else
                    if k1.min /= k2.min then
                    k1.min < k2.min else
                    if k1.sec /= k2.sec then
                        k1.sec < k2.sec else
                        k1.millis < k2.millis

buuid4_less : BUUID4 -> BUUID4 -> Bool
buuid4_less k1 k2 = 
    k1 < k2
    
buuid7_less : BUUID7 -> BUUID7 -> Bool
buuid7_less k1 k2 = 
    k1 < k2
    
bshacontenthashtime_less : BSHAContentHash -> BSHAContentHash -> Bool
bshacontenthashtime_less k1 k2 = 
    k1 < k2

bsqbnone_default : BNone
bsqbnone_default = 
    0

bsqbnothing_default : BNothing
bsqbnothing_default = 
    0

bsqbool_default : Bool
bsqbool_default = 
    False

bsqbint_default : BInt 
bsqbint_default = 
    0

bsqbnat_default : BNat
bsqbnat_default = 
    0

bsqbbigint_default : BBigInt 
bsqbbigint_default = 
    0

bsqbbignat_default : BBigNat
bsqbbignat_default = 
    0

bsqbfloat_default : BFloat
bsqbfloat_default = 
    0.0

bsqbdecimal_default : BDecimal
bsqbdecimal_default = 
    0.0

bsqbrational_default : BRational
bsqbrational_default = 
    0.0

bsqbstring_default : BString
bsqbstring_default = 
    ""

bsqbticktime_default : BTickTime
bsqbticktime_default = 
    0

bsqblogicaltime_default : BLogicalTime
bsqblogicaltime_default = 
    0

bsqbuuid4_default : BUUID4
bsqbuuid4_default = 
    "0x0"

bsqbuuid7_default : BUUID7
bsqbuuid7_default = 
    "0x0"

bsqbshacontenthash_default : BSHAContentHash
bsqbshacontenthash_default = 
    "0x0"

bsqbbytebuffer_default : BByteBuffer
bsqbbytebuffer_default = 
    {format = 0, compress = 0, data = []}

bsqbdatetime_default : BDateTime
bsqbdatetime_default = 
    {
        year = 0,
        month = 0,
        day = 0,
        hour = 0,
        min = 0,
        tzdata = "UTC"
    }

bsqbutcdatetime_default : BUTCDateTime
bsqbutcdatetime_default =  
    {
        year = 0,
        month = 0,
        day = 0,
        hour = 0,
        min = 0
    }

bsqbcalendardate_default : BCalendarDate
bsqbcalendardate_default = 
    {
        year = 0,
        month = 0,
        day = 0
    }

bsqbrelativetime_default : BRelativeTime
bsqbrelativetime_default = 
    {
        hour = 0,
        min = 0
    }

bsqbisotimestamp_default : BISOTimeStamp
bsqbisotimestamp_default = 
    {
        year = 0,
        month = 0,
        day = 0,
        hour = 0,
        min = 0,
        sec = 0,
        millis = 0
    }

bsqblatlongcoordinate_default : BLatLongCoordinate
bsqblatlongcoordinate_default = 
    {
        lat = 0.0,
        long = 0.0
    }

type BKeyObject = 
    BKeyInvalid
    | BKeyNone_box
    | BKeyBool_box Bool
    | BKeyBInt_box BInt
    | BKeyBNat_box BNat
    | BKeyBBigInt_box BBigInt
    | BKeyBBigNat_box BBigNat
    | BKeyBString_box BString
    | BKeyBUTCDateTime_box BUTCDateTime
    | BKeyBCalendarDate_box BCalendarDate
    | BKeyBRelativeTime_box BRelativeTime
    | BKeyBTickTime_box BTickTime
    | BKeyBLogicalTime_box BLogicalTime
    | BKeyBISOTimeStamp_box BISOTimeStamp
    | BKeyBUUID4_box BUUID4
    | BKeyBUUID7_box BUUID7
    | BKeyBSHAContentHash_box BSHAContentHash
    | BufferCompression_box BufferCompression
    | BufferFormat_box BufferFormat
    | Main__Quantity_box Main__Quantity
    | Main__RejectReason_box Main__RejectReason

unbox_BKeyBool : BKeyObject -> Bool
unbox_BKeyBool k =
    case k of 
        BKeyBool_box b -> 
            b
        _ -> 
            False

unbox_BKeyBInt : BKeyObject -> BInt
unbox_BKeyBInt k =
    case k of 
        BKeyBInt_box i -> 
            i
        _ -> 
            0

unbox_BKeyBNat : BKeyObject -> BNat
unbox_BKeyBNat k =
    case k of 
        BKeyBNat_box n -> 
            n
        _ -> 
            0

unbox_BKeyBBigInt : BKeyObject -> BBigInt
unbox_BKeyBBigInt k =
    case k of 
        BKeyBBigInt_box i -> 
            i
        _ -> 
            0

unbox_BKeyBBigNat : BKeyObject -> BBigNat
unbox_BKeyBBigNat k =
    case k of 
        BKeyBBigNat_box n -> 
            n
        _ -> 
            0

unbox_BKeyBString : BKeyObject -> BString
unbox_BKeyBString k =
    case k of 
        BKeyBString_box s -> 
            s
        _ -> 
            ""

unbox_BKeyBUTCDateTime : BKeyObject -> BUTCDateTime
unbox_BKeyBUTCDateTime k =
    case k of 
        BKeyBUTCDateTime_box t -> 
            t
        _ -> 
            bsqbutcdatetime_default


unbox_BKeyBCalendarDate : BKeyObject -> BCalendarDate
unbox_BKeyBCalendarDate k =
    case k of 
        BKeyBCalendarDate_box t -> 
            t
        _ -> 
            bsqbcalendardate_default

unbox_BKeyBRelativeTime : BKeyObject -> BRelativeTime
unbox_BKeyBRelativeTime k =
    case k of 
        BKeyBRelativeTime_box t -> 
            t
        _ -> 
            bsqbrelativetime_default

unbox_BKeyBTickTime : BKeyObject -> BTickTime
unbox_BKeyBTickTime k =
    case k of 
        BKeyBTickTime_box t -> 
            t
        _ -> 
            bsqbticktime_default

unbox_BKeyBLogicalTime : BKeyObject -> BLogicalTime
unbox_BKeyBLogicalTime k =
    case k of 
        BKeyBLogicalTime_box t -> 
            t
        _ -> 
            bsqblogicaltime_default

unbox_BKeyBISOTimeStamp : BKeyObject -> BISOTimeStamp
unbox_BKeyBISOTimeStamp k =
    case k of 
        BKeyBISOTimeStamp_box t -> 
            t
        _ -> 
            bsqbisotimestamp_default


unbox_BKeyBUUID4 : BKeyObject -> BUUID4
unbox_BKeyBUUID4 k =
    case k of 
        BKeyBUUID4_box u -> 
            u
        _ -> 
            bsqbuuid4_default

unbox_BKeyBUUID7 : BKeyObject -> BUUID7
unbox_BKeyBUUID7 k =
    case k of 
        BKeyBUUID7_box u -> 
            u
        _ -> 
            bsqbuuid7_default

unbox_BKeyBSHAContentHash : BKeyObject -> BSHAContentHash
unbox_BKeyBSHAContentHash k =
    case k of 
        BKeyBSHAContentHash_box h -> 
            h
        _ -> 
            bsqbshacontenthash_default

unbox_BKeyBufferCompression : BKeyObject -> BufferCompression
unbox_BKeyBufferCompression k = 
    case k of
        BKeyBNat_box v -> 
            v
        _ -> 
            bsqbuffercompression_default
unbox_BKeyBufferFormat : BKeyObject -> BufferFormat
unbox_BKeyBufferFormat k = 
    case k of
        BKeyBNat_box v -> 
            v
        _ -> 
            bsqbufferformat_default
unbox_BKeyMain__Quantity : BKeyObject -> Main__Quantity
unbox_BKeyMain__Quantity k = 
    case k of
        BKeyBNat_box v -> 
            v
        _ -> 
            bsqmain__quantity_default
unbox_BKeyMain__RejectReason : BKeyObject -> Main__RejectReason
unbox_BKeyMain__RejectReason k = 
    case k of
        BKeyBNat_box v -> 
            v
        _ -> 
            bsqmain__rejectreason_default

bsqbuffercompression_default : BufferCompression
bsqbuffercompression_default = 
    bsqbnat_default
bsqbufferformat_default : BufferFormat
bsqbufferformat_default = 
    bsqbnat_default
bsqmain__quantity_default : Main__Quantity
bsqmain__quantity_default = 
    bsqbnat_default
bsqmain__rejectreason_default : Main__RejectReason
bsqmain__rejectreason_default = 
    bsqbnat_default

type BKey = 
    BKey TypeTag BKeyObject

bkey_extract_value : BKey -> BKeyObject
bkey_extract_value k = 
    let (BKey _ obj) = k in obj

bkey_none : BKey
bkey_none = 
    BKey TypeTag_None BKeyNone_box

bsqbkey_default : BKey
bsqbkey_default = 
    bkey_none
        
bkey_less : BKey -> BKey -> Bool
bkey_less k1 k2 = 
    let (BKey tag1 obj1) = k1 in
    let (BKey tag2 obj2) = k2 in
    if tag1 /= tag2 then
        (ordinalOf tag1) < (ordinalOf tag2) else
        case obj1 of
            BKeyNone_box -> 
                False
            BKeyBool_box b1 -> 
                case obj2 of 
                    BKeyBool_box b2 -> 
                        bool_less b1 b2
                    _ -> 
                        False
            BKeyBInt_box i1 -> 
                case obj2 of 
                    BKeyBInt_box i2 -> 
                        bint_less i1 i2
                    _ -> 
                        False
            BKeyBNat_box n1 -> 
                case obj2 of 
                    BKeyBNat_box n2 -> 
                        bnat_less n1 n2
                    _ -> 
                        False
            BKeyBBigInt_box i1 -> 
                case obj2 of 
                    BKeyBBigInt_box i2 -> 
                        bbigint_less i1 i2
                    _ -> 
                        False
            BKeyBBigNat_box n1 -> 
                case obj2 of 
                    BKeyBBigNat_box n2 -> 
                        bbignat_less n1 n2
                    _ -> 
                        False
            BKeyBString_box s1 -> 
                case obj2 of 
                    BKeyBString_box s2 -> 
                        bstring_less s1 s2
                    _ -> 
                        False
            BKeyBUTCDateTime_box d1 -> 
                case obj2 of 
                    BKeyBUTCDateTime_box d2 -> 
                        butcdatetime_less d1 d2
                    _ -> 
                        False
            BKeyBCalendarDate_box d1 -> 
                case obj2 of 
                    BKeyBCalendarDate_box d2 -> 
                        bcalendardate_less d1 d2
                    _ -> 
                        False
            BKeyBRelativeTime_box t1 -> 
                case obj2 of 
                    BKeyBRelativeTime_box t2 -> 
                        brelativetime_less t1 t2
                    _ -> 
                        False
            BKeyBTickTime_box t1 -> 
                case obj2 of 
                    BKeyBTickTime_box t2 -> 
                        bticktime_less t1 t2
                    _ -> 
                        False
            BKeyBLogicalTime_box t1 -> 
                case obj2 of 
                    BKeyBLogicalTime_box t2 -> 
                        blogicaltime_less t1 t2
                    _ -> 
                        False
            BKeyBISOTimeStamp_box t1 -> 
                case obj2 of 
                    BKeyBISOTimeStamp_box t2 -> 
                        bisotimestamp_less t1 t2
                    _ -> 
                        False
            BKeyBUUID4_box id1 -> 
                case obj2 of 
                    BKeyBUUID4_box id2 -> 
                        buuid4_less id1 id2
                    _ -> 
                        False
            BKeyBUUID7_box id1 -> 
                case obj2 of 
                    BKeyBUUID7_box id2 -> 
                        buuid7_less id1 id2
                    _ -> 
                        False
            BKeyBSHAContentHash_box h1 -> 
                case obj2 of 
                    BKeyBSHAContentHash_box h2 -> 
                        bshacontenthashtime_less h1 h2
                    _ -> 
                        False
            _ -> 
                False

--NO DATA--
--NO DATA--
type alias List_Main__BuyResponse_ = List BTerm
type alias List_Main__Quantity_ = List Main__Quantity
type alias List_Main__RejectReason_ = List Main__RejectReason
type alias List_Main__Violations_ = List BTerm
type alias ListOps = {}
ccListOps : ListOps
ccListOps = {}
type alias Main__BuyAccepted = {main__buyaccepted_id: BString, main__buyaccepted_product: BString, main__buyaccepted_price: Main__Price, main__buyaccepted_quantity: Main__Quantity}
ccMain__BuyAccepted : BString -> BString -> Main__Price -> Main__Quantity -> Main__BuyAccepted
ccMain__BuyAccepted arg_main__buyaccepted_id arg_main__buyaccepted_product arg_main__buyaccepted_price arg_main__buyaccepted_quantity = {main__buyaccepted_id = arg_main__buyaccepted_id, main__buyaccepted_product = arg_main__buyaccepted_product, main__buyaccepted_price = arg_main__buyaccepted_price, main__buyaccepted_quantity = arg_main__buyaccepted_quantity}
type alias Main__BuyInvalid = {main__buyinvalid_id: BString, main__buyinvalid_violations: List_Main__Violations_}
ccMain__BuyInvalid : BString -> List_Main__Violations_ -> Main__BuyInvalid
ccMain__BuyInvalid arg_main__buyinvalid_id arg_main__buyinvalid_violations = {main__buyinvalid_id = arg_main__buyinvalid_id, main__buyinvalid_violations = arg_main__buyinvalid_violations}
type alias Main__BuyRejected = {main__buyrejected_id: BString, main__buyrejected_reasons: List_Main__RejectReason_}
ccMain__BuyRejected : BString -> List_Main__RejectReason_ -> Main__BuyRejected
ccMain__BuyRejected arg_main__buyrejected_id arg_main__buyrejected_reasons = {main__buyrejected_id = arg_main__buyrejected_id, main__buyrejected_reasons = arg_main__buyrejected_reasons}
type alias Main__BuyRequest = {main__buyrequest_id: BString, main__buyrequest_requestPrice: BTerm, main__buyrequest_quantity: Main__Quantity, main__buyrequest_product: BString}
ccMain__BuyRequest : BString -> BTerm -> Main__Quantity -> BString -> Main__BuyRequest
ccMain__BuyRequest arg_main__buyrequest_id arg_main__buyrequest_requestPrice arg_main__buyrequest_quantity arg_main__buyrequest_product = {main__buyrequest_id = arg_main__buyrequest_id, main__buyrequest_requestPrice = arg_main__buyrequest_requestPrice, main__buyrequest_quantity = arg_main__buyrequest_quantity, main__buyrequest_product = arg_main__buyrequest_product}
type alias Main__InvalidPrice = {main__invalidprice_price: Main__Price}
ccMain__InvalidPrice : Main__Price -> Main__InvalidPrice
ccMain__InvalidPrice arg_main__invalidprice_price = {main__invalidprice_price = arg_main__invalidprice_price}
type alias Main__InvalidQuantity = {main__invalidquantity_quantity: Main__Quantity}
ccMain__InvalidQuantity : Main__Quantity -> Main__InvalidQuantity
ccMain__InvalidQuantity arg_main__invalidquantity_quantity = {main__invalidquantity_quantity = arg_main__invalidquantity_quantity}
type alias Main__Limit = {main__limit_price: Main__Price}
ccMain__Limit : Main__Price -> Main__Limit
ccMain__Limit arg_main__limit_price = {main__limit_price = arg_main__limit_price}
type alias Main__Market = {}
ccMain__Market : Main__Market
ccMain__Market = {}
type alias Main__SellAccepted = {main__sellaccepted_id: BString, main__sellaccepted_price: Main__Price}
ccMain__SellAccepted : BString -> Main__Price -> Main__SellAccepted
ccMain__SellAccepted arg_main__sellaccepted_id arg_main__sellaccepted_price = {main__sellaccepted_id = arg_main__sellaccepted_id, main__sellaccepted_price = arg_main__sellaccepted_price}
type alias Main__SellRequest = {main__sellrequest_id: BString, main__sellrequest_requestPrice: BTerm, main__sellrequest_dealId: BString}
ccMain__SellRequest : BString -> BTerm -> BString -> Main__SellRequest
ccMain__SellRequest arg_main__sellrequest_id arg_main__sellrequest_requestPrice arg_main__sellrequest_dealId = {main__sellrequest_id = arg_main__sellrequest_id, main__sellrequest_requestPrice = arg_main__sellrequest_requestPrice, main__sellrequest_dealId = arg_main__sellrequest_dealId}

type BObject = 
    BObjectBNothing_box
    | BObjectBFloat_box BFloat
    | BObjectBDecimal_box BDecimal
    | BObjectBRational_box BRational
    | BObjectBByteBuffer_box BByteBuffer
    | BObjectBDateTime_box BDateTime
    | BObjectBLatLongCoordinate_box BLatLongCoordinate
    | BObjectRegex_box Regex.Regex
--NO DATA--
--NO DATA--
    | List_Main__BuyResponse__box List_Main__BuyResponse_
    | List_Main__Quantity__box List_Main__Quantity_
    | List_Main__RejectReason__box List_Main__RejectReason_
    | List_Main__Violations__box List_Main__Violations_
    | ListOps_box ListOps
    | Main__BuyAccepted_box Main__BuyAccepted
    | Main__BuyInvalid_box Main__BuyInvalid
    | Main__BuyRejected_box Main__BuyRejected
    | Main__BuyRequest_box Main__BuyRequest
    | Main__InvalidPrice_box Main__InvalidPrice
    | Main__InvalidQuantity_box Main__InvalidQuantity
    | Main__Limit_box Main__Limit
    | Main__Market_box Main__Market
    | Main__SellAccepted_box Main__SellAccepted
    | Main__SellRequest_box Main__SellRequest

unbox_BObjectBFloat : BObject -> BFloat
unbox_BObjectBFloat k =
    case k of 
        BObjectBFloat_box f -> 
            f
        _ -> 
            bsqbfloat_default

unbox_BObjectBDecimal : BObject -> BDecimal
unbox_BObjectBDecimal k =
    case k of 
        BObjectBDecimal_box d -> 
            d
        _ -> 
            bsqbdecimal_default

unbox_BObjectBRational : BObject -> BRational
unbox_BObjectBRational k =
    case k of 
        BObjectBRational_box f -> 
            f
        _ -> 
            bsqbrational_default

unbox_BObjectByteBuffer : BObject -> BByteBuffer
unbox_BObjectByteBuffer k =
    case k of 
        BObjectBByteBuffer_box b -> 
            b
        _ -> 
            bsqbbytebuffer_default

unbox_BObjectBDateTime : BObject -> BDateTime
unbox_BObjectBDateTime k =
    case k of 
        BObjectBDateTime_box t -> 
            t
        _ -> 
            bsqbdatetime_default

unbox_BObjectBLatLongCoordinate : BObject -> BLatLongCoordinate
unbox_BObjectBLatLongCoordinate k =
    case k of 
        BObjectBLatLongCoordinate_box t -> 
            t
        _ -> 
            bsqblatlongcoordinate_default

unbox_BObjectRegex : BObject -> Regex.Regex
unbox_BObjectRegex k =
    case k of 
        BObjectRegex_box f -> 
            f
        _ -> 
            Regex.never

bsqmain__price_default : Main__Price
bsqmain__price_default = 
    bsqbdecimal_default
bsqlist_main__buyresponse__default : List_Main__BuyResponse_
bsqlist_main__buyresponse__default = 
    []
bsqlist_main__quantity__default : List_Main__Quantity_
bsqlist_main__quantity__default = 
    []
bsqlist_main__rejectreason__default : List_Main__RejectReason_
bsqlist_main__rejectreason__default = 
    []
bsqlist_main__violations__default : List_Main__Violations_
bsqlist_main__violations__default = 
    []
bsqlistops_default : ListOps
bsqlistops_default = 
    {}
bsqmain__buyaccepted_default : Main__BuyAccepted
bsqmain__buyaccepted_default = 
    {main__buyaccepted_id = bsqbstring_default, main__buyaccepted_product = bsqbstring_default, main__buyaccepted_price = bsqmain__price_default, main__buyaccepted_quantity = bsqmain__quantity_default}
bsqmain__buyinvalid_default : Main__BuyInvalid
bsqmain__buyinvalid_default = 
    {main__buyinvalid_id = bsqbstring_default, main__buyinvalid_violations = bsqlist_main__violations__default}
bsqmain__buyrejected_default : Main__BuyRejected
bsqmain__buyrejected_default = 
    {main__buyrejected_id = bsqbstring_default, main__buyrejected_reasons = bsqlist_main__rejectreason__default}
bsqmain__buyrequest_default : Main__BuyRequest
bsqmain__buyrequest_default = 
    {main__buyrequest_id = bsqbstring_default, main__buyrequest_requestPrice = bsqbterm_default, main__buyrequest_quantity = bsqmain__quantity_default, main__buyrequest_product = bsqbstring_default}
bsqmain__invalidprice_default : Main__InvalidPrice
bsqmain__invalidprice_default = 
    {main__invalidprice_price = bsqmain__price_default}
bsqmain__invalidquantity_default : Main__InvalidQuantity
bsqmain__invalidquantity_default = 
    {main__invalidquantity_quantity = bsqmain__quantity_default}
bsqmain__limit_default : Main__Limit
bsqmain__limit_default = 
    {main__limit_price = bsqmain__price_default}
bsqmain__market_default : Main__Market
bsqmain__market_default = 
    {}
bsqmain__sellaccepted_default : Main__SellAccepted
bsqmain__sellaccepted_default = 
    {main__sellaccepted_id = bsqbstring_default, main__sellaccepted_price = bsqmain__price_default}
bsqmain__sellrequest_default : Main__SellRequest
bsqmain__sellrequest_default = 
    {main__sellrequest_id = bsqbstring_default, main__sellrequest_requestPrice = bsqbterm_default, main__sellrequest_dealId = bsqbstring_default}

unbox_BObjectList_Main__BuyResponse_ : BObject -> List_Main__BuyResponse_
unbox_BObjectList_Main__BuyResponse_ t = 
    case t of
        List_Main__BuyResponse__box v -> 
            v
        _ -> 
            bsqlist_main__buyresponse__default
unbox_BObjectList_Main__Quantity_ : BObject -> List_Main__Quantity_
unbox_BObjectList_Main__Quantity_ t = 
    case t of
        List_Main__Quantity__box v -> 
            v
        _ -> 
            bsqlist_main__quantity__default
unbox_BObjectList_Main__RejectReason_ : BObject -> List_Main__RejectReason_
unbox_BObjectList_Main__RejectReason_ t = 
    case t of
        List_Main__RejectReason__box v -> 
            v
        _ -> 
            bsqlist_main__rejectreason__default
unbox_BObjectList_Main__Violations_ : BObject -> List_Main__Violations_
unbox_BObjectList_Main__Violations_ t = 
    case t of
        List_Main__Violations__box v -> 
            v
        _ -> 
            bsqlist_main__violations__default
unbox_BObjectListOps : BObject -> ListOps
unbox_BObjectListOps t = 
    case t of
        ListOps_box v -> 
            v
        _ -> 
            bsqlistops_default
unbox_BObjectMain__BuyAccepted : BObject -> Main__BuyAccepted
unbox_BObjectMain__BuyAccepted t = 
    case t of
        Main__BuyAccepted_box v -> 
            v
        _ -> 
            bsqmain__buyaccepted_default
unbox_BObjectMain__BuyInvalid : BObject -> Main__BuyInvalid
unbox_BObjectMain__BuyInvalid t = 
    case t of
        Main__BuyInvalid_box v -> 
            v
        _ -> 
            bsqmain__buyinvalid_default
unbox_BObjectMain__BuyRejected : BObject -> Main__BuyRejected
unbox_BObjectMain__BuyRejected t = 
    case t of
        Main__BuyRejected_box v -> 
            v
        _ -> 
            bsqmain__buyrejected_default
unbox_BObjectMain__BuyRequest : BObject -> Main__BuyRequest
unbox_BObjectMain__BuyRequest t = 
    case t of
        Main__BuyRequest_box v -> 
            v
        _ -> 
            bsqmain__buyrequest_default
unbox_BObjectMain__InvalidPrice : BObject -> Main__InvalidPrice
unbox_BObjectMain__InvalidPrice t = 
    case t of
        Main__InvalidPrice_box v -> 
            v
        _ -> 
            bsqmain__invalidprice_default
unbox_BObjectMain__InvalidQuantity : BObject -> Main__InvalidQuantity
unbox_BObjectMain__InvalidQuantity t = 
    case t of
        Main__InvalidQuantity_box v -> 
            v
        _ -> 
            bsqmain__invalidquantity_default
unbox_BObjectMain__Limit : BObject -> Main__Limit
unbox_BObjectMain__Limit t = 
    case t of
        Main__Limit_box v -> 
            v
        _ -> 
            bsqmain__limit_default
unbox_BObjectMain__Market : BObject -> Main__Market
unbox_BObjectMain__Market t = 
    case t of
        Main__Market_box v -> 
            v
        _ -> 
            bsqmain__market_default
unbox_BObjectMain__SellAccepted : BObject -> Main__SellAccepted
unbox_BObjectMain__SellAccepted t = 
    case t of
        Main__SellAccepted_box v -> 
            v
        _ -> 
            bsqmain__sellaccepted_default
unbox_BObjectMain__SellRequest : BObject -> Main__SellRequest
unbox_BObjectMain__SellRequest t = 
    case t of
        Main__SellRequest_box v -> 
            v
        _ -> 
            bsqmain__sellrequest_default

type BTerm = 
    BKeyObject BKey
    | BTermObject TypeTag BObject

bterm_none : BTerm
bterm_none = 
    BKeyObject bkey_none

bterm_nothing : BTerm
bterm_nothing = 
    BTermObject TypeTag_Nothing BObjectBNothing_box

bsqbterm_default : BTerm
bsqbterm_default = 
    bterm_nothing

getTypeTag_BKey : BKey -> TypeTag
getTypeTag_BKey t =
    let (BKey tag _) = t in tag

getTypeTag_BTerm : BTerm -> TypeTag
getTypeTag_BTerm t = 
    case t of 
        BKeyObject kk -> 
            getTypeTag_BKey kk
        BTermObject tag _ ->
            tag

getTermObj_BKey : BTerm -> BKey
getTermObj_BKey t =
    case t of 
        BKeyObject obj ->
            obj
        _ -> 
            bkey_none

getTermObj_BTerm : BTerm -> BObject
getTermObj_BTerm t = 
    case t of 
        BTermObject _ obj ->
            obj
        _ -> 
            BObjectBNothing_box

isBKeyNone : BKey -> Bool
isBKeyNone k = 
    getTypeTag_BKey k == TypeTag_None

isBTermNone : BTerm -> Bool
isBTermNone t = 
    getTypeTag_BTerm t == TypeTag_None

isBTermNothing : BTerm -> Bool
isBTermNothing t = 
    getTypeTag_BTerm t == TypeTag_Nothing

isBKeySome : BKey -> Bool
isBKeySome k = 
    getTypeTag_BKey k /= TypeTag_None

isBTermSome : BTerm -> Bool
isBTermSome t = 
    getTypeTag_BTerm t /= TypeTag_None

isBTermSomething : BTerm -> Bool
isBTermSomething t = 
    getTypeTag_BTerm t /= TypeTag_Nothing

type alias MapEntry k v = 
    {
        key: k,
        val: v
    }

result_is_success : (Result String a) -> Bool
result_is_success r = 
    case r of 
        Ok _ ->
            True
        _ -> 
            False

result_is_error : (Result String a) -> Bool
result_is_error r = 
    case r of 
        Err _ ->
            True
        _ -> 
            False

result_success_get_value : (Result String a) -> a -> a
result_success_get_value r d = 
    case r of 
        Ok v -> 
            v
        _ -> 
            d

result_error_get_value : (Result String a) -> String
result_error_get_value r = 
    case r of 
        Err e -> 
            e
        _ -> 
            "[NO ERROR INFO]"

list_head_w_default : (List a) -> a -> a
list_head_w_default l d =  
    case l of 
        [] ->
            d
        h :: _ ->
            h

type alias ReduceIdxInfo a =
    {
        index: Int,
        vv: a
    }

result_reduce : b -> (b -> a -> b) -> (List (Result String a)) -> (Result String b)
result_reduce acc f l = 
    case l of 
        [] ->
            Ok acc
        h :: t ->
            case h of 
                Err e -> 
                    Err e
                Ok v -> 
                    result_reduce (f acc v) f t

result_map_map : (List (Result String a)) -> (Result String (List a))
result_map_map l = 
    case l of 
        [] ->
            Ok []
        h :: t ->
            case h of 
                Err msg -> 
                    Err msg
                Ok v -> 
                    let tl = result_map_map t in
                    case tl of 
                        Err tlmsg -> 
                            Err tlmsg 
                        Ok tll ->
                            Ok (v :: tll)
            
type alias Q__Main__Price__ = {q__main__price___0: Main__Price}
ccQ__Main__Price__ : Main__Price -> Q__Main__Price__
ccQ__Main__Price__ arg_q__main__price___0 = {q__main__price___0 = arg_q__main__price___0}

--NO DATA--

main__Quantity__zero : Main__Quantity
main__Quantity__zero = 
    constexp_order_bsq_k18_constexp__5_59__zero
main__RejectReason__disagreeablePrice : Main__RejectReason
main__RejectReason__disagreeablePrice = 
    constexp_order_bsq_k18_constexp__29_520__disagreeablePrice
main__RejectReason__insufficientInventory : Main__RejectReason
main__RejectReason__insufficientInventory = 
    constexp_order_bsq_k18_constexp__29_520__insufficientInventory

listOps__s_list_empty_T_Main__BuyResponse_ : List_Main__BuyResponse_ -> Bool
listOps__s_list_empty_T_Main__BuyResponse_ l = 
    (List.isEmpty l)

fn__order_bsq_k18__126_3461_T_Main__BuyResponse___Lswitchexp_done_3 : Main__Quantity -> Main__Quantity
fn__order_bsq_k18__126_3461_T_Main__BuyResponse___Lswitchexp_done_3 q_tmp_0 = 
    let q___ir_ret__ = q_tmp_0 in
        let q__return = q___ir_ret__ in
            q__return

fn__order_bsq_k18__126_3461_T_Main__BuyResponse_ : BTerm -> Main__Quantity
fn__order_bsq_k18__126_3461_T_Main__BuyResponse_ response = 
    let q_match__3475 = response in
        let q_tmp_2 = ((getTypeTag_BTerm response) == TypeTag_Main__BuyAccepted) in
            if q_tmp_2 then
                let q_tmp_5 = (unbox_BObjectMain__BuyAccepted (getTermObj_BTerm response)).main__buyaccepted_quantity in
                    let q_tmp_0_1 = q_tmp_5 in
                        let q___ir_ret___1 = (fn__order_bsq_k18__126_3461_T_Main__BuyResponse___Lswitchexp_done_3 q_tmp_0_1) in
                            let q___ir_ret___2 = q___ir_ret___1 in
                                let q__return = q___ir_ret___2 in
                                    q__return
            else
                let q_tmp_0 = 0 in
                    let q___ir_ret__ = (fn__order_bsq_k18__126_3461_T_Main__BuyResponse___Lswitchexp_done_3 q_tmp_0) in
                        let q___ir_ret___2 = q___ir_ret__ in
                            let q__return = q___ir_ret___2 in
                                q__return

listOps__s_list_map_fn_T_Main__BuyResponse__U_Main__Quantity__fn__order_bsq_k18__126_3461_T_Main__BuyResponse__ : List_Main__BuyResponse_ -> List_Main__Quantity_
listOps__s_list_map_fn_T_Main__BuyResponse__U_Main__Quantity__fn__order_bsq_k18__126_3461_T_Main__BuyResponse__ l = 
    (List.map (\x__ -> (fn__order_bsq_k18__126_3461_T_Main__BuyResponse_ x__)) l)

list_Main__BuyResponse___map_T_Main__BuyResponse__U_Main__Quantity__fn__order_bsq_k18__126_3461_T_Main__BuyResponse__ : List_Main__BuyResponse_ -> List_Main__Quantity_
list_Main__BuyResponse___map_T_Main__BuyResponse__U_Main__Quantity__fn__order_bsq_k18__126_3461_T_Main__BuyResponse__ this = 
    let q_tmp_0 = (listOps__s_list_empty_T_Main__BuyResponse_ this) in
        if q_tmp_0 then
            let q_tmp_2 = [] in
                let q___ir_ret___1 = q_tmp_2 in
                    let q___ir_ret___2 = q___ir_ret___1 in
                        let q__return = q___ir_ret___2 in
                            q__return
        else
            let q_tmp_3 = (listOps__s_list_map_fn_T_Main__BuyResponse__U_Main__Quantity__fn__order_bsq_k18__126_3461_T_Main__BuyResponse__ this) in
                let q___ir_ret__ = q_tmp_3 in
                    let q___ir_ret___2 = q___ir_ret__ in
                        let q__return = q___ir_ret___2 in
                            q__return

listOps__s_list_empty_T_Main__Quantity_ : List_Main__Quantity_ -> Bool
listOps__s_list_empty_T_Main__Quantity_ l = 
    (List.isEmpty l)

listOps__s_list_front_T_Main__Quantity_ : List_Main__Quantity_ -> Main__Quantity
listOps__s_list_front_T_Main__Quantity_ l = 
    (list_head_w_default l bsqmain__quantity_default)

listOps__s_list_pop_front_T_Main__Quantity_ : List_Main__Quantity_ -> List_Main__Quantity_
listOps__s_list_pop_front_T_Main__Quantity_ l = 
    (List.drop 1 l)

core____infix__Main__Quantity__Main__Quantity___1 : Main__Quantity -> Main__Quantity -> Main__Quantity
core____infix__Main__Quantity__Main__Quantity___1 l r = 
    let q_tmp_4 = l in
        let q_tmp_7 = r in
            let q_tmp_1 = (q_tmp_4 + q_tmp_7) in
                let q_tmp_0 = q_tmp_1 in
                    let q___ir_ret__ = q_tmp_0 in
                        let q__return = q___ir_ret__ in
                            q__return

fn__list_bsq_k1__881_25568_T_Main__Quantity_ : Main__Quantity -> Main__Quantity -> Main__Quantity
fn__list_bsq_k1__881_25568_T_Main__Quantity_ a b = 
    let q_tmp_0 = (core____infix__Main__Quantity__Main__Quantity___1 a b) in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

listOps__s_list_reduce_T_Main__Quantity__U_Main__Quantity__fn__list_bsq_k1__881_25568_T_Main__Quantity__ : List_Main__Quantity_ -> Main__Quantity -> Main__Quantity
listOps__s_list_reduce_T_Main__Quantity__U_Main__Quantity__fn__list_bsq_k1__881_25568_T_Main__Quantity__ l iv = 
    (List.foldl (\acc__ x__ -> (fn__list_bsq_k1__881_25568_T_Main__Quantity_ acc__ x__)) iv l)

list_Main__Quantity___sum_T_Main__Quantity_ : List_Main__Quantity_ -> Main__Quantity
list_Main__Quantity___sum_T_Main__Quantity_ this = 
    let q_tmp_0 = (listOps__s_list_empty_T_Main__Quantity_ this) in
        if q_tmp_0 then
            let q___ir_ret___2 = main__Quantity__zero in
                let q___ir_ret___3 = q___ir_ret___2 in
                    let q__return = q___ir_ret___3 in
                        q__return
        else
            let q_tmp_3 = (listOps__s_list_front_T_Main__Quantity_ this) in
                let iv = q_tmp_3 in
                    let q_tmp_5 = (listOps__s_list_pop_front_T_Main__Quantity_ this) in
                        let tl = q_tmp_5 in
                            let q_tmp_7 = (listOps__s_list_empty_T_Main__Quantity_ q_tmp_5) in
                                if q_tmp_7 then
                                    let q___ir_ret___1 = iv in
                                        let q___ir_ret___3 = q___ir_ret___1 in
                                            let q__return = q___ir_ret___3 in
                                                q__return
                                else
                                    let q_tmp_10 = (listOps__s_list_reduce_T_Main__Quantity__U_Main__Quantity__fn__list_bsq_k1__881_25568_T_Main__Quantity__ tl iv) in
                                        let q___ir_ret__ = q_tmp_10 in
                                            let q___ir_ret___3 = q___ir_ret__ in
                                                let q__return = q___ir_ret___3 in
                                                    q__return

core____infix__Main__Quantity__Main__Quantity_ : Main__Quantity -> Main__Quantity -> Bool
core____infix__Main__Quantity__Main__Quantity_ l r = 
    let q_tmp_3 = l in
        let q_tmp_6 = r in
            let q_tmp_0 = (q_tmp_3 < q_tmp_6) in
                let q___ir_ret__ = q_tmp_0 in
                    let q__return = q___ir_ret__ in
                        q__return

q__i__Main__availability__Lselect_done_3 : Main__Quantity -> Main__Quantity
q__i__Main__availability__Lselect_done_3 q_tmp_5 = 
    let q___ir_ret__ = q_tmp_5 in
        let q__return = q___ir_ret__ in
            q__return

core____infix__Main__Quantity__Main__Quantity___0 : Main__Quantity -> Main__Quantity -> Result String Main__Quantity
core____infix__Main__Quantity__Main__Quantity___0 l r = 
    let q_tmp_4 = l in
        let q_tmp_7 = r in
            let tmp_var_0 = (if (q_tmp_7 < q_tmp_4) then (Err "order.bsq::5") else (Ok (q_tmp_4 - q_tmp_7))) in
                if (result_is_error tmp_var_0) then
                    (Err (result_error_get_value tmp_var_0))
                else
                    let q_tmp_1 = (result_success_get_value tmp_var_0 bsqbnat_default) in
                        let q_tmp_0 = q_tmp_1 in
                            let q___ir_ret__ = q_tmp_0 in
                                let q__return = q___ir_ret__ in
                                    (Ok q__return)

main__availability : Main__Quantity -> List_Main__BuyResponse_ -> Result String Main__Quantity
main__availability startOfDayPosition buys = 
    let q_tmp_2 = (list_Main__BuyResponse___map_T_Main__BuyResponse__U_Main__Quantity__fn__order_bsq_k18__126_3461_T_Main__BuyResponse__ buys) in
        let q_tmp_4 = (list_Main__Quantity___sum_T_Main__Quantity_ q_tmp_2) in
            let sumOfBuys = q_tmp_4 in
                let q_tmp_6 = (core____infix__Main__Quantity__Main__Quantity_ q_tmp_4 startOfDayPosition) in
                    if q_tmp_6 then
                        let q_tmp_5_1 = 0 in
                            let q___ir_ret___1 = (q__i__Main__availability__Lselect_done_3 q_tmp_5_1) in
                                let q___ir_ret___2 = q___ir_ret___1 in
                                    let q__return = q___ir_ret___2 in
                                        (Ok q__return)
                    else
                        let tmp_var_1 = (core____infix__Main__Quantity__Main__Quantity___0 startOfDayPosition sumOfBuys) in
                            if (result_is_error tmp_var_1) then
                                tmp_var_1
                            else
                                let q_tmp_10 = (result_success_get_value tmp_var_1 bsqmain__quantity_default) in
                                    let q_tmp_5 = q_tmp_10 in
                                        let q___ir_ret__ = (q__i__Main__availability__Lselect_done_3 q_tmp_5) in
                                            let q___ir_ret___2 = q___ir_ret__ in
                                                let q__return = q___ir_ret___2 in
                                                    (Ok q__return)

core_____infix__Main__Quantity__Main__Quantity_ : Main__Quantity -> Main__Quantity -> Bool
core_____infix__Main__Quantity__Main__Quantity_ l r = 
    let q_tmp_3 = l in
        let q_tmp_6 = r in
            let q_tmp_0 = (q_tmp_3 <= q_tmp_6) in
                let q___ir_ret__ = q_tmp_0 in
                    let q__return = q___ir_ret__ in
                        q__return

listOps__s_list_empty_T_Main__Violations_ : List_Main__Violations_ -> Bool
listOps__s_list_empty_T_Main__Violations_ l = 
    (List.isEmpty l)

listOps__s_list_append_T_Main__Violations_ : List_Main__Violations_ -> List_Main__Violations_ -> List_Main__Violations_
listOps__s_list_append_T_Main__Violations_ ll rr = 
    (List.append ll rr)

list_Main__Violations___s_append_helper_T_Main__Violations_ : List_Main__Violations_ -> List_Main__Violations_ -> List_Main__Violations_
list_Main__Violations___s_append_helper_T_Main__Violations_ l1 l2 = 
    let q_tmp_1 = (listOps__s_list_empty_T_Main__Violations_ l1) in
        let q_tmp_3 = (listOps__s_list_empty_T_Main__Violations_ l2) in
            let q_tmp_0 = (q_tmp_1 && q_tmp_3) in
                if q_tmp_0 then
                    let q_tmp_5 = [] in
                        let q___ir_ret___3 = q_tmp_5 in
                            let q___ir_ret___4 = q___ir_ret___3 in
                                let q__return = q___ir_ret___4 in
                                    q__return
                else
                    let q_tmp_6 = (listOps__s_list_empty_T_Main__Violations_ l1) in
                        if q_tmp_6 then
                            let q___ir_ret___2 = l2 in
                                let q___ir_ret___4 = q___ir_ret___2 in
                                    let q__return = q___ir_ret___4 in
                                        q__return
                        else
                            let q_tmp_9 = (listOps__s_list_empty_T_Main__Violations_ l2) in
                                if q_tmp_9 then
                                    let q___ir_ret___1 = l1 in
                                        let q___ir_ret___4 = q___ir_ret___1 in
                                            let q__return = q___ir_ret___4 in
                                                q__return
                                else
                                    let q_tmp_12 = (listOps__s_list_append_T_Main__Violations_ l1 l2) in
                                        let q___ir_ret__ = q_tmp_12 in
                                            let q___ir_ret___4 = q___ir_ret__ in
                                                let q__return = q___ir_ret___4 in
                                                    q__return

list_Main__Violations___append_T_Main__Violations_ : List_Main__Violations_ -> List_Main__Violations_ -> List_Main__Violations_
list_Main__Violations___append_T_Main__Violations_ this l = 
    let q_tmp_0 = (list_Main__Violations___s_append_helper_T_Main__Violations_ this l) in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

q__i__Main__validateRequest__Lifexp_done_11 : List_Main__Violations_ -> List_Main__Violations_ -> List_Main__Violations_
q__i__Main__validateRequest__Lifexp_done_11 q_tmp_17 priceCheck = 
    let quantityCheck = q_tmp_17 in
        let q_tmp_32 = (list_Main__Violations___append_T_Main__Violations_ priceCheck q_tmp_17) in
            let q___ir_ret__ = q_tmp_32 in
                let q__return = q___ir_ret__ in
                    q__return

q__i__Main__validateRequest__Lswitchexp_done_3 : List_Main__Violations_ -> Main__BuyRequest -> List_Main__Violations_
q__i__Main__validateRequest__Lswitchexp_done_3 q_tmp_0 request = 
    let priceCheck = q_tmp_0 in
        let q_tmp_21 = request.main__buyrequest_quantity in
            let q_tmp_18 = (core_____infix__Main__Quantity__Main__Quantity_ q_tmp_21 0) in
                if q_tmp_18 then
                    let q_tmp_27 = request.main__buyrequest_quantity in
                        let q_tmp_24 = (ccMain__InvalidQuantity q_tmp_27) in
                            let q_tmp_28 = (BTermObject TypeTag_Main__InvalidQuantity (Main__InvalidQuantity_box q_tmp_24)) in
                                let q_tmp_23 = [q_tmp_28] in
                                    let q_tmp_17_1 = q_tmp_23 in
                                        let q___ir_ret___1 = (q__i__Main__validateRequest__Lifexp_done_11 q_tmp_17_1 priceCheck) in
                                            let q___ir_ret___2 = q___ir_ret___1 in
                                                let q__return = q___ir_ret___2 in
                                                    q__return
                else
                    let q_tmp_29 = [] in
                        let q_tmp_17 = q_tmp_29 in
                            let q___ir_ret__ = (q__i__Main__validateRequest__Lifexp_done_11 q_tmp_17 priceCheck) in
                                let q___ir_ret___2 = q___ir_ret__ in
                                    let q__return = q___ir_ret___2 in
                                        q__return

core____infix__Main__Price__Main__Price_ : Main__Price -> Main__Price -> Bool
core____infix__Main__Price__Main__Price_ l r = 
    let q_tmp_3 = l in
        let q_tmp_6 = r in
            let q_tmp_0 = (q_tmp_3 < q_tmp_6) in
                let q___ir_ret__ = q_tmp_0 in
                    let q__return = q___ir_ret__ in
                        q__return

q__i__Main__validateRequest__Lifexp_done_8 : List_Main__Violations_ -> Main__BuyRequest -> List_Main__Violations_
q__i__Main__validateRequest__Lifexp_done_8 q_tmp_8 request = 
    let q_tmp_0 = q_tmp_8 in
        let q___ir_ret__ = (q__i__Main__validateRequest__Lswitchexp_done_3 q_tmp_0 request) in
            let q__return = q___ir_ret__ in
                q__return

main__validateRequest : Main__BuyRequest -> List_Main__Violations_
main__validateRequest request = 
    let q_tmp_3 = request.main__buyrequest_requestPrice in
        let q_match__1196 = q_tmp_3 in
            let q_tmp_4 = ((getTypeTag_BTerm q_tmp_3) == TypeTag_Main__Market) in
                if q_tmp_4 then
                    let q_tmp_5 = [] in
                        let q_tmp_0 = q_tmp_5 in
                            let q___ir_ret___2 = (q__i__Main__validateRequest__Lswitchexp_done_3 q_tmp_0 request) in
                                let q___ir_ret___3 = q___ir_ret___2 in
                                    let q__return = q___ir_ret___3 in
                                        q__return
                else
                    let q_tmp_6 = True in
                        let q_tmp_7 = (ccQ__Main__Price__ (unbox_BObjectMain__Limit (getTermObj_BTerm q_match__1196)).main__limit_price) in
                            let p = q_tmp_7.q__main__price___0 in
                                let q_tmp_9 = (core____infix__Main__Price__Main__Price_ p bDecimal_zero) in
                                    if q_tmp_9 then
                                        let q_tmp_13 = (ccMain__InvalidPrice p) in
                                            let q_tmp_15 = (BTermObject TypeTag_Main__InvalidPrice (Main__InvalidPrice_box q_tmp_13)) in
                                                let q_tmp_12 = [q_tmp_15] in
                                                    let q_tmp_8_1 = q_tmp_12 in
                                                        let q___ir_ret___1 = (q__i__Main__validateRequest__Lifexp_done_8 q_tmp_8_1 request) in
                                                            let q___ir_ret___3 = q___ir_ret___1 in
                                                                let q__return = q___ir_ret___3 in
                                                                    q__return
                                    else
                                        let q_tmp_16 = [] in
                                            let q_tmp_8 = q_tmp_16 in
                                                let q___ir_ret__ = (q__i__Main__validateRequest__Lifexp_done_8 q_tmp_8 request) in
                                                    let q___ir_ret___3 = q___ir_ret__ in
                                                        let q__return = q___ir_ret___3 in
                                                            q__return

main__lockinPrice : BTerm -> Main__Price -> Main__Price
main__lockinPrice requestPrice marketPrice = 
    let q_match__1818 = requestPrice in
        let q_tmp_1 = ((getTypeTag_BTerm requestPrice) == TypeTag_Main__Market) in
            if q_tmp_1 then
                let q___ir_ret___1 = marketPrice in
                    let q___ir_ret___2 = q___ir_ret___1 in
                        let q__return = q___ir_ret___2 in
                            q__return
            else
                let q_tmp_3 = True in
                    let q_tmp_4 = (ccQ__Main__Price__ (unbox_BObjectMain__Limit (getTermObj_BTerm q_match__1818)).main__limit_price) in
                        let p = q_tmp_4.q__main__price___0 in
                            let q___ir_ret__ = p in
                                let q___ir_ret___2 = q___ir_ret__ in
                                    let q__return = q___ir_ret___2 in
                                        q__return

core____infix__Main__Price__Decimal_ : Main__Price -> BDecimal -> Main__Price
core____infix__Main__Price__Decimal_ l r = 
    let q_tmp_4 = l in
        let q_tmp_1 = (q_tmp_4 * r) in
            let q_tmp_0 = q_tmp_1 in
                let q___ir_ret__ = q_tmp_0 in
                    let q__return = q___ir_ret__ in
                        q__return

listOps__s_list_empty_T_Main__RejectReason_ : List_Main__RejectReason_ -> Bool
listOps__s_list_empty_T_Main__RejectReason_ l = 
    (List.isEmpty l)

listOps__s_list_append_T_Main__RejectReason_ : List_Main__RejectReason_ -> List_Main__RejectReason_ -> List_Main__RejectReason_
listOps__s_list_append_T_Main__RejectReason_ ll rr = 
    (List.append ll rr)

list_Main__RejectReason___s_append_helper_T_Main__RejectReason_ : List_Main__RejectReason_ -> List_Main__RejectReason_ -> List_Main__RejectReason_
list_Main__RejectReason___s_append_helper_T_Main__RejectReason_ l1 l2 = 
    let q_tmp_1 = (listOps__s_list_empty_T_Main__RejectReason_ l1) in
        let q_tmp_3 = (listOps__s_list_empty_T_Main__RejectReason_ l2) in
            let q_tmp_0 = (q_tmp_1 && q_tmp_3) in
                if q_tmp_0 then
                    let q_tmp_5 = [] in
                        let q___ir_ret___3 = q_tmp_5 in
                            let q___ir_ret___4 = q___ir_ret___3 in
                                let q__return = q___ir_ret___4 in
                                    q__return
                else
                    let q_tmp_6 = (listOps__s_list_empty_T_Main__RejectReason_ l1) in
                        if q_tmp_6 then
                            let q___ir_ret___2 = l2 in
                                let q___ir_ret___4 = q___ir_ret___2 in
                                    let q__return = q___ir_ret___4 in
                                        q__return
                        else
                            let q_tmp_9 = (listOps__s_list_empty_T_Main__RejectReason_ l2) in
                                if q_tmp_9 then
                                    let q___ir_ret___1 = l1 in
                                        let q___ir_ret___4 = q___ir_ret___1 in
                                            let q__return = q___ir_ret___4 in
                                                q__return
                                else
                                    let q_tmp_12 = (listOps__s_list_append_T_Main__RejectReason_ l1 l2) in
                                        let q___ir_ret__ = q_tmp_12 in
                                            let q___ir_ret___4 = q___ir_ret__ in
                                                let q__return = q___ir_ret___4 in
                                                    q__return

list_Main__RejectReason___append_T_Main__RejectReason_ : List_Main__RejectReason_ -> List_Main__RejectReason_ -> List_Main__RejectReason_
list_Main__RejectReason___append_T_Main__RejectReason_ this l = 
    let q_tmp_0 = (list_Main__RejectReason___s_append_helper_T_Main__RejectReason_ this l) in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

q__i__Main__acceptability__Lifexp_done_6 : List_Main__RejectReason_ -> List_Main__RejectReason_ -> List_Main__RejectReason_
q__i__Main__acceptability__Lifexp_done_6 q_tmp_9 availabilityCheck = 
    let priceCheck = q_tmp_9 in
        let q_tmp_24 = (list_Main__RejectReason___append_T_Main__RejectReason_ availabilityCheck q_tmp_9) in
            let q___ir_ret__ = q_tmp_24 in
                let q__return = q___ir_ret__ in
                    q__return

q__i__Main__acceptability__Lifexp_done_3 : List_Main__RejectReason_ -> Main__Price -> Main__BuyRequest -> List_Main__RejectReason_
q__i__Main__acceptability__Lifexp_done_3 q_tmp_0 marketPrice request = 
    let availabilityCheck = q_tmp_0 in
        let q_tmp_14 = request.main__buyrequest_requestPrice in
            let q_tmp_11 = (main__lockinPrice q_tmp_14 marketPrice) in
                let q_tmp_16 = (core____infix__Main__Price__Decimal_ marketPrice 0.9) in
                    let q_tmp_10 = (core____infix__Main__Price__Main__Price_ q_tmp_11 q_tmp_16) in
                        if q_tmp_10 then
                            let q_tmp_19 = [main__RejectReason__disagreeablePrice] in
                                let q_tmp_9_1 = q_tmp_19 in
                                    let q___ir_ret___1 = (q__i__Main__acceptability__Lifexp_done_6 q_tmp_9_1 availabilityCheck) in
                                        let q___ir_ret___2 = q___ir_ret___1 in
                                            let q__return = q___ir_ret___2 in
                                                q__return
                        else
                            let q_tmp_21 = [] in
                                let q_tmp_9 = q_tmp_21 in
                                    let q___ir_ret__ = (q__i__Main__acceptability__Lifexp_done_6 q_tmp_9 availabilityCheck) in
                                        let q___ir_ret___2 = q___ir_ret__ in
                                            let q__return = q___ir_ret___2 in
                                                q__return

main__acceptability : Main__BuyRequest -> Main__Price -> Main__Quantity -> List_Main__RejectReason_
main__acceptability request marketPrice availableInventory = 
    let q_tmp_5 = request.main__buyrequest_quantity in
        let q_tmp_1 = (core____infix__Main__Quantity__Main__Quantity_ availableInventory q_tmp_5) in
            if q_tmp_1 then
                let q_tmp_6 = [main__RejectReason__insufficientInventory] in
                    let q_tmp_0_1 = q_tmp_6 in
                        let q___ir_ret___1 = (q__i__Main__acceptability__Lifexp_done_3 q_tmp_0_1 marketPrice request) in
                            let q___ir_ret___2 = q___ir_ret___1 in
                                let q__return = q___ir_ret___2 in
                                    q__return
            else
                let q_tmp_8 = [] in
                    let q_tmp_0 = q_tmp_8 in
                        let q___ir_ret__ = (q__i__Main__acceptability__Lifexp_done_3 q_tmp_0 marketPrice request) in
                            let q___ir_ret___2 = q___ir_ret__ in
                                let q__return = q___ir_ret___2 in
                                    q__return

list_Main__Violations___empty_T_Main__Violations_ : List_Main__Violations_ -> Bool
list_Main__Violations___empty_T_Main__Violations_ this = 
    let q_tmp_0 = (listOps__s_list_empty_T_Main__Violations_ this) in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

list_Main__RejectReason___empty_T_Main__RejectReason_ : List_Main__RejectReason_ -> Bool
list_Main__RejectReason___empty_T_Main__RejectReason_ this = 
    let q_tmp_0 = (listOps__s_list_empty_T_Main__RejectReason_ this) in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

main__processBuy : Main__BuyRequest -> Main__Price -> Main__Quantity -> BTerm
main__processBuy request marketPrice availableInventory = 
    let q_tmp_0 = (main__validateRequest request) in
        let violations = q_tmp_0 in
            let q_tmp_2 = (main__acceptability request marketPrice availableInventory) in
                let rejections = q_tmp_2 in
                    let q_tmp_9 = request.main__buyrequest_requestPrice in
                        let q_tmp_6 = (main__lockinPrice q_tmp_9 marketPrice) in
                            let lockPrice = q_tmp_6 in
                                let q_tmp_14 = (list_Main__Violations___empty_T_Main__Violations_ q_tmp_0) in
                                    let q_tmp_11 = (not q_tmp_14) in
                                        if q_tmp_11 then
                                            let q_tmp_18 = request.main__buyrequest_id in
                                                let q_tmp_15 = (ccMain__BuyInvalid q_tmp_18 violations) in
                                                    let q_tmp_20 = (BTermObject TypeTag_Main__BuyInvalid (Main__BuyInvalid_box q_tmp_15)) in
                                                        let q___ir_ret___2 = q_tmp_20 in
                                                            let q___ir_ret___3 = q___ir_ret___2 in
                                                                let q__return = q___ir_ret___3 in
                                                                    q__return
                                        else
                                            let q_tmp_24 = (list_Main__RejectReason___empty_T_Main__RejectReason_ rejections) in
                                                let q_tmp_21 = (not q_tmp_24) in
                                                    if q_tmp_21 then
                                                        let q_tmp_28 = request.main__buyrequest_id in
                                                            let q_tmp_25 = (ccMain__BuyRejected q_tmp_28 rejections) in
                                                                let q_tmp_30 = (BTermObject TypeTag_Main__BuyRejected (Main__BuyRejected_box q_tmp_25)) in
                                                                    let q___ir_ret___1 = q_tmp_30 in
                                                                        let q___ir_ret___3 = q___ir_ret___1 in
                                                                            let q__return = q___ir_ret___3 in
                                                                                q__return
                                                    else
                                                        let q_tmp_34 = request.main__buyrequest_id in
                                                            let q_tmp_37 = request.main__buyrequest_product in
                                                                let q_tmp_41 = request.main__buyrequest_quantity in
                                                                    let q_tmp_31 = (ccMain__BuyAccepted q_tmp_34 q_tmp_37 lockPrice q_tmp_41) in
                                                                        let q_tmp_42 = (BTermObject TypeTag_Main__BuyAccepted (Main__BuyAccepted_box q_tmp_31)) in
                                                                            let q___ir_ret__ = q_tmp_42 in
                                                                                let q___ir_ret___3 = q___ir_ret__ in
                                                                                    let q__return = q___ir_ret___3 in
                                                                                        q__return

main__processSell : Main__SellRequest -> Main__Price -> BTerm
main__processSell request marketPrice = 
    let q_tmp_3 = request.main__sellrequest_requestPrice in
        let q_tmp_0 = (main__lockinPrice q_tmp_3 marketPrice) in
            let lockPrice = q_tmp_0 in
                let q_tmp_8 = request.main__sellrequest_id in
                    let q_tmp_5 = (ccMain__SellAccepted q_tmp_8 q_tmp_0) in
                        let q_tmp_10 = (BTermObject TypeTag_Main__SellAccepted (Main__SellAccepted_box q_tmp_5)) in
                            let q___ir_ret__ = q_tmp_10 in
                                let q__return = q___ir_ret__ in
                                    q__return

main__main : BTerm -> Main__Price -> Main__Quantity -> List_Main__BuyResponse_ -> Result String BTerm
main__main request marketPrice startOfDayPosition responses = 
    let q_tmp_2 = ((getTypeTag_BTerm request) == TypeTag_Main__BuyRequest) in
        if q_tmp_2 then
            let tmp_var_2 = (main__availability startOfDayPosition responses) in
                if (result_is_error tmp_var_2) then
                    (Err (result_error_get_value tmp_var_2))
                else
                    let q_tmp_3 = (result_success_get_value tmp_var_2 bsqmain__quantity_default) in
                        let availableInventory = q_tmp_3 in
                            let q_tmp_10 = (unbox_BObjectMain__BuyRequest (getTermObj_BTerm request)) in
                                let q_tmp_6 = (main__processBuy q_tmp_10 marketPrice q_tmp_3) in
                                    let q_tmp_11 = q_tmp_6 in
                                        let q___ir_ret___1 = q_tmp_11 in
                                            let q___ir_ret___2 = q___ir_ret___1 in
                                                let q__return = q___ir_ret___2 in
                                                    (Ok q__return)
        else
            let q_tmp_15 = (unbox_BObjectMain__SellRequest (getTermObj_BTerm request)) in
                let q_tmp_12 = (main__processSell q_tmp_15 marketPrice) in
                    let q_tmp_16 = q_tmp_12 in
                        let q___ir_ret__ = q_tmp_16 in
                            let q___ir_ret___2 = q___ir_ret__ in
                                let q__return = q___ir_ret___2 in
                                    (Ok q__return)

main__elm_main : Bool
main__elm_main = 
    let q_tmp_2 = ccMain__Market in
        let q_tmp_5 = (BTermObject TypeTag_Main__Market (Main__Market_box q_tmp_2)) in
            let q_tmp_0 = (ccMain__BuyRequest "rq1" q_tmp_5 5 "apples") in
                let request = q_tmp_0 in
                    let marketPrice = 10.0 in
                        let availableInventory = 100 in
                            let q_tmp_8 = (main__processBuy q_tmp_0 10.0 100) in
                                let res = q_tmp_8 in
                                    let q_tmp_14 = ((getTypeTag_BTerm q_tmp_8) == TypeTag_Main__BuyRejected) in
                                        let q___ir_ret__ = q_tmp_14 in
                                            let q__return = q___ir_ret__ in
                                                q__return

constexp_order_bsq_k18_constexp__5_59__zero : Main__Quantity
constexp_order_bsq_k18_constexp__5_59__zero = 
    let q_tmp_0 = 0 in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

constexp_order_bsq_k18_constexp__29_520__disagreeablePrice : Main__RejectReason
constexp_order_bsq_k18_constexp__29_520__disagreeablePrice = 
    let q_tmp_0 = 1 in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

constexp_order_bsq_k18_constexp__29_520__insufficientInventory : Main__RejectReason
constexp_order_bsq_k18_constexp__29_520__insufficientInventory = 
    let q_tmp_0 = 0 in
        let q___ir_ret__ = q_tmp_0 in
            let q__return = q___ir_ret__ in
                q__return

