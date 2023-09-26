#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>
#include <ctime>
#include <cstdio>

#include <codecvt>

#include <string>
#include <regex>
#include <optional>

#include <vector>
#include <list>
#include <set>
#include <map>

#include "json.hpp"
typedef nlohmann::json json;

namespace BSQON
{
    //
    //TODO: wstring is not that great for unicode -- at some point we need to switch to UTF8 etc.
    //
    typedef std::u32string UnicodeString;
    typedef std::basic_regex<char32_t> UnicodeRegex;

    typedef uint32_t CharCode;
    typedef size_t StateID;

    class CharCodeIterator
    {
    public:
        const UnicodeString sstr;
        int64_t curr;

        CharCodeIterator(UnicodeString& sstr) : sstr(sstr), curr(0) {;}
        
        bool valid() const
        {
            return this->curr != (int64_t)this->sstr.size();
        }

        void advance()
        {
            this->curr++;
        }

        CharCode get() const
        {
            return this->sstr.at(this->curr);
        }
    };

    struct DateTime
    {
        uint16_t year;   // Year since 1900
        uint8_t month;   // 0-11
        uint8_t day;     // 1-31
        uint8_t hour;    // 0-23
        uint8_t min;     // 0-59
        uint8_t sec;     // 0-60

        char* tzdata; //timezone name as spec in tzdata database
    };

    struct UTCDateTime
    {
        uint16_t year;   // Year since 1900
        uint8_t month;   // 0-11
        uint8_t day;     // 1-31
        uint8_t hour;    // 0-23
        uint8_t min;     // 0-59
        uint8_t sec;     // 0-60
    };

    struct PlainDate
    {
        uint16_t year;   // Year since 1900
        uint8_t month;   // 0-11
        uint8_t day;     // 1-31
    };

    struct PlainTime
    {
        uint8_t hour;    // 0-23
        uint8_t min;     // 0-59
        uint8_t sec;     // 0-60
    };

    struct ISOTimeStamp
    {
        uint16_t year;   // Year since 1900
        uint8_t month;   // 0-11
        uint8_t day;     // 1-31
        uint8_t hour;    // 0-23
        uint8_t min;     // 0-59
        uint8_t sec;     // 0-60
        uint16_t millis; // 0-999
    };

    using TextPosition = int64_t;
}

