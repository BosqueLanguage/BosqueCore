#include "lexer.h"

#define BSQON_LEXER_RE_MODE std::regex_constants::nosubs | std::regex_constants::optimize | std::regex_constants::basic
#define BSQON_LEXER_SUBS_RE_MODE std::regex_constants::optimize | std::regex_constants::basic

namespace BSQON
{
    ParseError ParseError::createUnclosedMultiLineComment(TextPosition spos, TextPosition epos) {
        return ParseError(U"Unclosed multi-line comment", spos, epos);
    }

    ParseError ParseError::createUnclosedPath(TextPosition spos, TextPosition epos) {
        return ParseError(U"Unclosed Path", spos, epos);
    }

    ParseError ParseError::createUnclosedString(TextPosition spos, TextPosition epos) {
        return ParseError(U"Unclosed String", spos, epos);
    }

    ParseError ParseError::createUnclosedRegex(TextPosition spos, TextPosition epos) {
        return ParseError(U"Unclosed Regex", spos, epos);
    }

    ParseError ParseError::createUnknownToken(TextPosition spos, TextPosition epos) {
        return ParseError(U"Unknown Token", spos, epos);
    }

    LexerToken LexerToken::singletonInvalidToken = LexerToken(TokenKind::TOKEN_INVALID, nullptr, 0, 0, 0, 0);
    LexerToken LexerToken::singletonEOFToken = LexerToken(TokenKind::TOKEN_EOF, nullptr, 0, 0, 0, 0);

    UnicodeRegex LexerRegex::whitespaceRe = UnicodeRegex(U"^\\s+", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::commentStartRe = UnicodeRegex(U"^(//)|(/\\*)", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::commentMultilineEndRe = UnicodeRegex(U"\\*/", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::bytebuffRe = UnicodeRegex(U"^0x\\[[A-Z0-9]*\\]", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::bytebuffCheckRe = UnicodeRegex(U"^[A-Z0-9]*$", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::fullTimeRe = UnicodeRegex(U"^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})(\\[[a-zA-Z0-9/ _-]+\\]|Z)", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::fullTimeUTCRe = UnicodeRegex(U"^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::dateOnlyRe = UnicodeRegex(U"^([0-9]{4})-([0-9]{2})-([0-9]{2})", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::timeOnlyRe = UnicodeRegex(U"^([0-9]{2}):([0-9]{2}):([0-9]{2})", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::tickTimeRe = UnicodeRegex(U"&(0|([1-9][0-9]*))t");
    UnicodeRegex LexerRegex::logicalTimeRe = UnicodeRegex(U"^(0|([1-9][0-9]*))l");
    UnicodeRegex LexerRegex::timestampRe = UnicodeRegex(U"^([0-9]{4})-([0-9]{2})-([0-9]{2})T([0-9]{2}):([0-9]{2}):([0-9]{2})\\.([0-9]{3})Z$", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::uuidRe = UnicodeRegex(U"^uuid(4|7)\\{[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}\\}", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::shahashRe = UnicodeRegex(U"^sha3\\{[a-z0-9]{128}\\}", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::pathStartRe = UnicodeRegex(U"^(path|fragment|glob)\\[");
    UnicodeRegex LexerRegex::pathEndRe = UnicodeRegex(U"\\}", BSQON_LEXER_RE_MODE);; 

    UnicodeRegex LexerRegex::intRe = UnicodeRegex(U"^[+-]?((0)|([1-9][0-9]*))i", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::natRe = UnicodeRegex(U"^((0)|([1-9][0-9]*))n", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::floatRe = UnicodeRegex(U"^([+-]?[0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?f", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::decimalRe = UnicodeRegex(U"^([+-]?[0-9]+\\.[0-9]+)([eE][-+]?[0-9]+)?d", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::bigintRe = UnicodeRegex(U"^((0)|(-?[1-9][0-9]*))I", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::bignatRe = UnicodeRegex(U"^((0)|([1-9][0-9]*))N", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::rationalRe = UnicodeRegex(U"^((0|-?[1-9][0-9]*)|(0|-?[1-9][0-9]*)/([1-9][0-9]*))R", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::intNumberinoRe = UnicodeRegex(U"^[+-]?((0)|([1-9][0-9]*))", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::intExponentNumberinoRe = UnicodeRegex(U"^[+-]?((0)|([1-9][0-9]*))([eE][-+]?[0-9]+)", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::floatNumberinoRe = UnicodeRegex(U"^[+-]?([0-9]*\\.[0-9]+)([eE][-+]?[0-9]+)?", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::stringStartRe = UnicodeRegex(U"^\"", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::asciistringStartRe = UnicodeRegex(U"^ascii\\{\"", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::regexStartRe = UnicodeRegex(U"^regex\\{\"", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::bracketBSQONRe = UnicodeRegex(U"^[()<>{}\\[\\]]", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::symbolBSQONRe = UnicodeRegex(U"^[.:,&|!=>@]+", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::keywordBSQONRe = UnicodeRegex(U"^(none|some|true|false|nothing|something|ok|err|in|let)", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::bracketJSONRe = UnicodeRegex(U"^[{}\\[\\]]", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::symbolJSONRe = UnicodeRegex(U"^[:,]+", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::keywordJSONRe = UnicodeRegex(U"^null|true|false)", BSQON_LEXER_RE_MODE);

    UnicodeRegex LexerRegex::nameSrcRe = UnicodeRegex(U"\\$src");
    UnicodeRegex LexerRegex::nameRefRe = UnicodeRegex(U"#[a-z]|[a-z_][a-zA-Z0-9_]+");

    UnicodeRegex LexerRegex::typeNameRe = UnicodeRegex(U"[A-Z]([a-zA-Z0-9_])+(::[A-Z]([a-zA-Z0-9_])+)*", BSQON_LEXER_RE_MODE);
    UnicodeRegex LexerRegex::propertyNameRE = UnicodeRegex(U"[a-z]|[a-z_][a-zA-Z0-9_]*");
    UnicodeRegex LexerRegex::specialUnderscoreRE = UnicodeRegex(U"_", BSQON_LEXER_RE_MODE);

    std::set<UnicodeString> LexerRegex::coretypes = {
        U"None", U"Bool", U"Int", U"Nat", U"BigInt", U"BigNat", U"Rational", U"Float", U"Decimal", U"String", U"ASCIIString",
        U"ByteBuffer", U"DateTime", U"UTCDateTime", U"PlainDate", U"PlainTime", U"TickTime", U"LogicalTime", U"ISOTimeStamp", U"UUIDv4", U"UUIDv7", U"SHAContentHash", 
        U"LatLongCoordinate", U"Regex", U"Nothing"
    };

    std::optional<uint16_t> LexerDateExtract::extractDateTimeYear(const std::string& str) 
    {
        auto year = std::stoul(str.c_str());
        return ((1900u <= year) & (year <= 2200u)) ? std::make_optional<uint16_t>(year) : std::nullopt; 
    }

    std::optional<uint8_t> LexerDateExtract::extractDateTimeMonth(const std::string& str)
    {
        auto month = std::stoul(str.c_str() + 5);
        return ((0u <= month) & (month <= 11u)) ? std::make_optional<uint8_t>(month) : std::nullopt;
    }

    std::optional<uint8_t> LexerDateExtract::extractDateTimeDay(const std::string& str) 
    {
        auto year = std::stoul(str.c_str());
        auto month = std::stoul(str.c_str() + 5);
        auto day = std::stoul(str.c_str() + 8);
    
        if(month != 1) {
            auto mday = ((month == 3u) | (month == 5u) | (month == 8u) | (month == 10u)) ? 30u : 31u;
            return day <= mday ? std::make_optional<uint8_t>(day) : std::nullopt;
        }
        else {
            bool isleapyear = !((year == 1900u) | (year == 2100u) | (year == 2200u)) & (year % 4u == 0u);
            auto mday = isleapyear ? 29u : 28u;
            return day <= mday ? std::make_optional<uint8_t>(day) : std::nullopt;
        }
    }

    std::optional<uint8_t> LexerDateExtract::extractDateTimeHour(const std::string& str)
    {
        auto hour = std::stoul(str.c_str() + 11);
        return ((0u <= hour) & (hour <= 23u)) ? std::make_optional<uint8_t>(hour) : std::nullopt;
    }

    std::optional<uint8_t> LexerDateExtract::extractDateTimeMinute(const std::string& str) 
    {
        auto minute = std::stoul(str.c_str() + 14);
        return ((0u <= minute) & (minute <= 59u)) ? std::make_optional<uint8_t>(minute) : std::nullopt;
    }

    std::optional<uint8_t> LexerDateExtract::extractDateTimeSecond(const std::string& str)
    {
        auto second = std::stoul(str.c_str() + 17);
        return ((0u <= second) & (second <= 60u)) ? std::make_optional<uint8_t>(second) : std::nullopt;
    }

    std::optional<uint16_t> LexerDateExtract::extractDateTimeMillis(const std::string& str)
    {
        auto millis = std::stoul(str.c_str() + 20);
        return ((0u <= millis) & (millis <= 999u)) ? std::make_optional<uint16_t>(millis) : std::nullopt;
    }

    std::optional<char*> LexerDateExtract::extractDateTimeTZ(const std::string& str, std::set<std::string>& tzvalues) 
    {
        auto tzinfo_start = str.c_str() + 20;
        if(*tzinfo_start == 'Z') {
            return std::make_optional<char*>("UTC");
        }
        else {
            auto tzinfo_end = std::find(tzinfo_start, str.c_str() + str.length() - 1, ']');
            std::string tzinfo(tzinfo_start, tzinfo_end);
    
            auto ii = tzvalues.insert(tzinfo);
            return std::make_optional<char*>(const_cast<char*>(ii.first->c_str()));
        }
    }

    std::optional<DateTime> LexerDateExtract::extractDateTime(UnicodeString::iterator spos, UnicodeString::iterator epos, std::set<std::string>& tzvalues)
    {
        UnicodeString estr(spos, epos);
        std::string asciidate = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(estr);

        auto year = LexerDateExtract::extractDateTimeYear(asciidate);
        auto month = LexerDateExtract::extractDateTimeMonth(asciidate);
        auto day = LexerDateExtract::extractDateTimeDay(asciidate);
        auto hour = LexerDateExtract::extractDateTimeHour(asciidate);
        auto minute = LexerDateExtract::extractDateTimeMinute(asciidate);
        auto second = LexerDateExtract::extractDateTimeSecond(asciidate);
        auto tz = LexerDateExtract::extractDateTimeTZ(asciidate, tzvalues);
        if(!(year.has_value() & month.has_value() & day.has_value() & hour.has_value() & minute.has_value() & second.has_value() & tz.has_value())) {
            return std::nullopt;
        }

        return std::make_optional(DateTime(year.value(), month.value(), day.value(), hour.value(), minute.value(), second.value(), tz.value()));
    }

    std::optional<UTCDateTime> LexerDateExtract::extractUTCDateTime(UnicodeString::iterator spos, UnicodeString::iterator epos)
    {
        UnicodeString estr(spos, epos);
        std::string asciidate = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(estr);

        auto year = LexerDateExtract::extractDateTimeYear(asciidate);
        auto month = LexerDateExtract::extractDateTimeMonth(asciidate);
        auto day = LexerDateExtract::extractDateTimeDay(asciidate);
        auto hour = LexerDateExtract::extractDateTimeHour(asciidate);
        auto minute = LexerDateExtract::extractDateTimeMinute(asciidate);
        auto second = LexerDateExtract::extractDateTimeSecond(asciidate);
        if(!(year.has_value() & month.has_value() & day.has_value() & hour.has_value() & minute.has_value() & second.has_value())) {
            return std::nullopt;
        }

        return std::make_optional(UTCDateTime(year.value(), month.value(), day.value(), hour.value(), minute.value(), second.value()));
    }

    std::optional<PlainDate> LexerDateExtract::extractDate(UnicodeString::iterator spos, UnicodeString::iterator epos)
    {
        UnicodeString estr(spos, epos);
        std::string asciidate = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(estr) + "T00:00:00";

        auto year = LexerDateExtract::extractDateTimeYear(asciidate);
        auto month = LexerDateExtract::extractDateTimeMonth(asciidate);
        auto day = LexerDateExtract::extractDateTimeDay(asciidate);
        if(!(year.has_value() & month.has_value() & day.has_value())) {
            return std::nullopt;
        }

        return std::make_optional(PlainDate(year.value(), month.value(), day.value()));
    }

    std::optional<PlainTime> LexerDateExtract::extractTime(UnicodeString::iterator spos, UnicodeString::iterator epos)
    {
        UnicodeString estr(spos, epos);
        std::string asciidate = "0000-00-00T" + std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(estr);

        auto hour = LexerDateExtract::extractDateTimeHour(asciidate);
        auto minute = LexerDateExtract::extractDateTimeMinute(asciidate);
        auto second = LexerDateExtract::extractDateTimeSecond(asciidate);
        if(!(hour.has_value() & minute.has_value() & second.has_value())) {
            return std::nullopt;
        }

        return std::make_optional(PlainTime(hour.value(), minute.value(), second.value()));
    }

    std::optional<ISOTimeStamp> LexerDateExtract::extractISOTimeStamp(UnicodeString::iterator spos, UnicodeString::iterator epos)
    {
        UnicodeString estr(spos, epos);
        std::string asciidate = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.to_bytes(estr);

        auto year = LexerDateExtract::extractDateTimeYear(asciidate);
        auto month = LexerDateExtract::extractDateTimeMonth(asciidate);
        auto day = LexerDateExtract::extractDateTimeDay(asciidate);
        auto hour = LexerDateExtract::extractDateTimeHour(asciidate);
        auto minute = LexerDateExtract::extractDateTimeMinute(asciidate);
        auto second = LexerDateExtract::extractDateTimeSecond(asciidate);
        auto millis = LexerDateExtract::extractDateTimeMillis(asciidate);
        if(!(year.has_value() & month.has_value() & day.has_value() & hour.has_value() & minute.has_value() & second.has_value() & millis.has_value())) {
            return std::nullopt;
        }

        return std::make_optional(ISOTimeStamp(year.value(), month.value(), day.value(), hour.value(), minute.value(), second.value(), millis.value()));
    }
}
