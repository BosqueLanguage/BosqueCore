#include "uuids.h"

#include "boost/uuid/uuid.hpp"
#include "boost/uuid/uuid_io.hpp"
#include "boost/uuid/uuid_generators.hpp"

namespace ᐸRuntimeᐳ
{
    ///////////////////////////////
    //UUIDv4
    ///////////////////////////////

    void jsonParseToBSQ_UUIDv4(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected a string for UUIDv4");

        std::string uuid_str = j.get<std::string>();
        boost::uuids::uuid uuid;
        auto [ec, ptr] = boost::uuids::from_chars(uuid_str.data(), uuid_str.data() + uuid_str.size(), uuid);

        *(boost::uuids::uuid*)resptr = uuid;
    }

    void parseToBSQ_UUIDv4(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        assert(false); //TODO UUIDv4
    }

    json bsqToJSON_UUIDv4(const TypeInfo* tinfo, const void* valptr)
    {
        assert(false); //TODO UUIDv4
    }
    
    void bsqToBAPI_UUIDv4(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        assert(false); //TODO UUIDv4
    }

    void displayValue_UUIDv4(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        assert(false); //TODO UUIDv4
    }

    ///////////////////////////////
    //UUIDv7
    ///////////////////////////////

    void jsonParseToBSQ_UUIDv7(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        assert(false); //TODO UUIDv7
    }

    void parseToBSQ_UUIDv7(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        assert(false); //TODO UUIDv7
    }

    json bsqToJSON_UUIDv7(const TypeInfo* tinfo, const void* valptr)
    {
        assert(false); //TODO UUIDv7
    }

    void bsqToBAPI_UUIDv7(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        assert(false); //TODO UUIDv7
    }

    void displayValue_UUIDv7(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        assert(false); //TODO UUIDv7
    }
}
