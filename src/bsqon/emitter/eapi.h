
#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"

namespace BSQON
{
    template <typename ValueRepr, typename State>
    class EmitManager
    {
    public:
        EmitManager() {;}
        virtual ~EmitManager() {;}

        virtual std::optional<bool> extractBoolImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<uint64_t> extractNatImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<int64_t> extractIntImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::string> extractBigNatImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::string> extractBigIntImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::string> extractFloatImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::string> extractDecimalImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::pair<std::string, uint64_t>> extractRationalImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::string> extractStringImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::pair<std::vector<uint8_t>, std::pair<uint8_t, uint8_t>>> extractByteBufferImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<APIDateTime> extractDateTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<APIUTCDateTime> extractUTCDateTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<APICalendarDate> extractCalendarDateImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<uint64_t> extractTickTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<uint64_t> extractLogicalTimeImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<APIISOTimeStamp> extractISOTimeStampImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::vector<uint8_t>> extractUUID4Impl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::vector<uint8_t>> extractUUID7Impl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::vector<uint8_t>> extractSHAContentHashImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<std::pair<float, float>> extractLatLongCoordinateImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        
        virtual std::optional<uint64_t> extractEnumImpl(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

        virtual ValueRepr extractValueForTupleIndex(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
        virtual ValueRepr extractValueForRecordProperty(const APIModule* apimodule, const IType* itype, ValueRepr value, std::string pname, State& ctx) = 0;
        virtual ValueRepr extractValueForEntityField(const APIModule* apimodule, const IType* itype, ValueRepr value, std::pair<std::string, std::string> fnamefkey, State& ctx) = 0;

        virtual void prepareExtractContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual std::optional<size_t> extractLengthForContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual ValueRepr extractValueForContainer_T(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
        virtual std::pair<ValueRepr, ValueRepr> extractValueForContainer_KV(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
        virtual void completeExtractContainer(const APIModule* apimodule, const IType* itype, State& ctx) = 0;

        virtual std::optional<size_t> extractUnionChoice(const APIModule* apimodule, const IType* itype, const std::vector<const IType*>& opttypes, ValueRepr intoloc, State& ctx) = 0;
        virtual ValueRepr extractUnionValue(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t uchoice, State& ctx) = 0;
    };
}
