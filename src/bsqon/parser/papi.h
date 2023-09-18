
#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"

namespace BSQON
{
    template <typename ValueRepr, typename State>
    class ParseManager
    {
    public:
        ParseManager() {;}
        virtual ~ParseManager() {;}

        virtual bool checkInvokeOk(const std::string& checkinvoke, ValueRepr value, State& ctx) = 0;

        virtual void parseNone(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual void parseNothing(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;
        virtual void parseBool(const APIModule* apimodule, const IType* itype, bool b, ValueRepr value, State& ctx) = 0;
        virtual void parseNat(const APIModule* apimodule, const IType* itype, uint64_t n, ValueRepr value, State& ctx) = 0;
        virtual void parseInt(const APIModule* apimodule, const IType* itype, int64_t i, ValueRepr value, State& ctx) = 0;
        virtual void parseBigNat(const APIModule* apimodule, const IType* itype, std::string n, ValueRepr value, State& ctx) = 0;
        virtual void parseBigInt(const APIModule* apimodule, const IType* itype, std::string i, ValueRepr value, State& ctx) = 0;
        virtual void parseFloat(const APIModule* apimodule, const IType* itype, std::string f, ValueRepr value, State& ctx) = 0;
        virtual void parseDecimal(const APIModule* apimodule, const IType* itype, std::string d, ValueRepr value, State& ctx) = 0;
        virtual void parseRational(const APIModule* apimodule, const IType* itype, std::string n, uint64_t d, ValueRepr value, State& ctx) = 0;
        virtual void parseString(const APIModule* apimodule, const IType* itype, std::string s, ValueRepr value, State& ctx) = 0;
        virtual void parseByteBuffer(const APIModule* apimodule, const IType* itype, uint8_t compress, uint8_t format, std::vector<uint8_t>& data, ValueRepr value, State& ctx) = 0;
        virtual void parseDateTime(const APIModule* apimodule, const IType* itype, APIDateTime t, ValueRepr value, State& ctx) = 0;
        virtual void parseUTCDateTime(const APIModule* apimodule, const IType* itype, APIUTCDateTime t, ValueRepr value, State& ctx) = 0;
        virtual void parsePlainDate(const APIModule* apimodule, const IType* itype, APICalendarDate t, ValueRepr value, State& ctx) = 0;
        virtual void parsePlainTime(const APIModule* apimodule, const IType* itype, APICalendarDate t, ValueRepr value, State& ctx) = 0;
        virtual bool parseTickTime(const APIModule* apimodule, const IType* itype, uint64_t t, ValueRepr value, State& ctx) = 0;
        virtual bool parseLogicalTime(const APIModule* apimodule, const IType* itype, uint64_t j, ValueRepr value, State& ctx) = 0;
        virtual bool parseISOTimeStamp(const APIModule* apimodule, const IType* itype, APIISOTimeStamp t, ValueRepr value, State& ctx) = 0;
        virtual bool parseUUID4(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, ValueRepr value, State& ctx) = 0;
        virtual bool parseUUID7(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, ValueRepr value, State& ctx) = 0;
        virtual bool parseSHAContentHash(const APIModule* apimodule, const IType* itype, std::vector<uint8_t> v, ValueRepr value, State& ctx) = 0;
        virtual bool parseLatLongCoordinate(const APIModule* apimodule, const IType* itype, float latitude, float longitude, ValueRepr value, State& ctx) = 0;

        virtual bool parseEnumImpl(const APIModule* apimodule, const IType* itype, uint64_t n, ValueRepr value, State& ctx) = 0;

        virtual void prepareParseTuple(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
        virtual ValueRepr getValueForTupleIndex(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
        virtual void completeParseTuple(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

        virtual void prepareParseRecord(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
        virtual ValueRepr getValueForRecordProperty(const APIModule* apimodule, const IType* itype, ValueRepr value, std::string pname, State& ctx) = 0;
        virtual void completeParseRecord(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

        virtual void prepareParseContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t count, State& ctx) = 0;
        virtual ValueRepr getValueForContainerElementParse_T(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
        virtual std::pair<ValueRepr, ValueRepr> getValueForContainerElementParse_KV(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t i, State& ctx) = 0;
        virtual void completeParseContainer(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

        virtual void prepareParseEntity(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
        virtual void prepareParseEntityMask(const APIModule* apimodule, const IType* itype, State& ctx) = 0;
        virtual ValueRepr getValueForEntityField(const APIModule* apimodule, const IType* itype, ValueRepr value, std::pair<std::string, std::string> fnamefkey, State& ctx) = 0;
        virtual void completeParseEntity(const APIModule* apimodule, const IType* itype, ValueRepr value, State& ctx) = 0;

        virtual void setMaskFlag(const APIModule* apimodule, ValueRepr flagloc, size_t i, bool flag, State& ctx) = 0;

        virtual ValueRepr parseUnionChoice(const APIModule* apimodule, const IType* itype, ValueRepr value, size_t pick, const IType* picktype, State& ctx) = 0;
    };
}
