#pragma once

#include "../common.h"

#include "bsqtype.h"
#include "uuids.h"

namespace ᐸRuntimeᐳ
{
    enum class XAPIInfoTag : uint64_t
    {
        Clear = 0,
        Timeout = 1,
        Cancelled = 2,
        AccessDenied = 3
    };

    class XAPIResultData
    {
    public:
        XUUIDv7 correlationid;
        XUUIDv4 infoid;

        const char* tag; //Type::id format to correlate ad-hoc
        XAPIInfoTag tagid;
    };
    static_assert(sizeof(XAPIResultData) == 48, "Need to update values in compiler");

    template <typename T>
    class XAPIResultEntityValue
    {
    public:
        XAPIResultData data;
        T value;
    };

    template <typename T>
    class XAPIResult
    {
    public:
        TypeInfo* typeinfo;
        XAPIResultRepr<T> repr;
    };
}
