#pragma once

#include "../common.h"
#include "../regex/bsqregex.h"

#include "lexer.h"
#include "../info/type_info.h"

namespace BSQON
{
    class ParseError
    {
    public:
        UnicodeString message;
        std::optional<Type*> expectedTypeInfo;
        std::optional<std::vector<UnicodeString>> completionsOptions;

        TextPosition spos;
        TextPosition epos;

        ParseError() = default;
        ParseError(const ParseError& other) = default;
        ParseError(ParseError&& other) = default;

        ParseError& operator=(const ParseError& other) = default;
        ParseError& operator=(ParseError&& other) = default;

        ParseError(UnicodeString message, TextPosition spos, TextPosition epos) : message(message), spos(spos), epos(epos) {;}

        void addExpectedTypeInfo(Type* tinfo)
        {
            this->expectedTypeInfo = tinfo;
        }

        void addCompletionOption(std::vector<UnicodeString> options)
        {
            this->completionsOptions = options;
        }

        static ParseError createUnclosedMultiLineComment(TextPosition spos, TextPosition epos);
        static ParseError createUnclosedPath(TextPosition spos, TextPosition epos);
        static ParseError createUnclosedString(TextPosition spos, TextPosition epos);
        static ParseError createUnclosedRegex(TextPosition spos, TextPosition epos);
        static ParseError createUnknownToken(TextPosition spos, TextPosition epos);

        static ParseError createExpectedMissing(UnicodeString expected, TextPosition spos, TextPosition epos);
        static ParseError createExpectedButGot(UnicodeString expected, const LexerToken& tk, TextPosition spos, TextPosition epos);
    };

    enum class TokenKind 
    {
        TOKEN_INVALID = 0x0,
        TOKEN_EOF,
        TOKEN_UNKNOWN, 

        TOKEN_NULL,
        TOKEN_NONE,
        TOKEN_SOME,
        TOKEN_NOTHING,
        TOKEN_TYPE,
        TOKEN_SOMETHING,
        TOKEN_OK,
        TOKEN_ERR,

        TOKEN_LBRACE,
        TOKEN_RBRACE,
        TOKEN_LBRACKET,
        TOKEN_RBRACKET,
        TOKEN_LPAREN,
        TOKEN_RPAREN,
        TOKEN_LANGLE,
        TOKEN_RANGLE,
        TOKEN_COLON,
        TOKEN_COLON_COLON,
        TOKEN_COMMA,
        TOKEN_AMP,
        TOKEN_BAR,
        TOKEN_BANG,
        TOKEN_ENTRY,
        TOKEN_LDOTS,
        TOKEN_EQUALS,
        TOKEN_LET,
        TOKEN_IN,
        TOKEN_SRC,
        TOKEN_REFERENCE,
        TOKEN_DOT,
        TOKEN_AT,

        TOKEN_TRUE, 
        TOKEN_FALSE,
        TOKEN_NAT,
        TOKEN_INT,
        TOKEN_BIG_NAT,
        TOKEN_BIG_INT,
        TOKEN_FLOAT,
        TOKEN_DECIMAL,
        TOKEN_RATIONAL,
        TOKEN_STRING,
        TOKEN_ASCII_STRING,
        TOKEN_BYTE_BUFFER,
        TOKEN_REGEX,
        TOKEN_DATE_TIME,
        TOKEN_UTC_DATE_TIME,
        TOKEN_PLAIN_DATE,
        TOKEN_PLAIN_TIME,
        TOKEN_TICK_TIME,
        TOKEN_LOGICAL_TIME,
        TOKEN_TIMESTAMP,
        TOKEN_UUID,
        TOKEN_SHA_HASH,
        TOKEN_PATH_ITEM,
        TOKEN_PROPERTY,
        TOKEN_UNDERSCORE
    };

    class LexerToken
    {
    public:
        TokenKind kind;

        UnicodeString* input;
        int64_t spos;
        int64_t epos;

        LexerToken() = default;
        LexerToken(const LexerToken& other) = default;
        LexerToken(LexerToken&& other) = default;

        LexerToken& operator=(const LexerToken& other) = default;
        LexerToken& operator=(LexerToken&& other) = default;

        LexerToken(TokenKind kind, UnicodeString* input, int64_t spos, int64_t epos) : kind(kind), input(input), spos(spos), epos(epos) {;}

        bool isValid() const {
            return this->kind != TokenKind::TOKEN_INVALID;
        }

        bool isUnknownToken() const {
            return this->kind == TokenKind::TOKEN_UNKNOWN;
        }

        UnicodeString::iterator tokenBegin() const {
            return this->input->begin() + this->spos;
        }

        UnicodeString::iterator tokenEnd() const {
            return this->input->begin() + this->epos;
        }

        static LexerToken singletonInvalidToken;
        static LexerToken singletonEOFToken;

        UnicodeString convertToPrintable() const;
    };

    class LexerRegex
    {
    public:
        static UnicodeRegex whitespaceRe;
        static UnicodeRegex commentStartRe;
        static UnicodeRegex commentMultilineEndRe;

        static UnicodeRegex bytebuffRe;
        static UnicodeRegex bytebuffCheckRe;

        static UnicodeRegex fullTimeRe;
        static UnicodeRegex fullTimeUTCRe;
        static UnicodeRegex dateOnlyRe;
        static UnicodeRegex timeOnlyRe;

        static UnicodeRegex tickTimeRe;
        static UnicodeRegex logicalTimeRe;
        static UnicodeRegex timestampRe;

        static UnicodeRegex uuidRe;
        static UnicodeRegex shahashRe;

        static UnicodeRegex pathStartRe;
        static UnicodeRegex pathEndRe; 

        static UnicodeRegex intRe;
        static UnicodeRegex natRe;

        static UnicodeRegex floatRe;
        static UnicodeRegex decimalRe;

        static UnicodeRegex bigintRe;
        static UnicodeRegex bignatRe;
        static UnicodeRegex rationalRe;

        static UnicodeRegex intNumberinoRe;
        static UnicodeRegex intExponentNumberinoRe;
        static UnicodeRegex floatNumberinoRe;

        static UnicodeRegex stringStartRe;
        static UnicodeRegex asciistringStartRe;
        static UnicodeRegex regexStartRe;

        static UnicodeRegex bracketBSQONRe;
        static UnicodeRegex symbolBSQONRe;
        static UnicodeRegex keywordBSQONRe;
        
        static UnicodeRegex bracketJSONRe;
        static UnicodeRegex symbolJSONRe;
        static UnicodeRegex keywordJSONRe;

        static UnicodeRegex nameSrcRe;
        static UnicodeRegex nameRefRe;

        static UnicodeRegex typeNameRe;
        static UnicodeRegex propertyNameRE;
        static UnicodeRegex specialUnderscoreRE;

        static std::set<UnicodeString> coretypes;
    };

    class LexerDateExtract
    {
    public:
        static std::optional<uint16_t> extractDateTimeYear(const std::string& str);
        static std::optional<uint8_t> extractDateTimeMonth(const std::string& str);
        static std::optional<uint8_t> extractDateTimeDay(const std::string& str);
        static std::optional<uint8_t> extractDateTimeHour(const std::string& str);
        static std::optional<uint8_t> extractDateTimeMinute(const std::string& str);
        static std::optional<uint8_t> extractDateTimeSecond(const std::string& str);
        static std::optional<uint16_t> extractDateTimeMillis(const std::string& str);
        static std::optional<char*> extractDateTimeTZ(const std::string& str, std::set<std::string>& tzvalues);

        static std::optional<DateTime> extractDateTime(UnicodeString::iterator spos, UnicodeString::iterator epos, std::set<std::string>& tzvalues);
        static std::optional<UTCDateTime> extractUTCDateTime(UnicodeString::iterator spos, UnicodeString::iterator epos);
        static std::optional<PlainDate> extractDate(UnicodeString::iterator spos, UnicodeString::iterator epos);
        static std::optional<PlainTime> extractTime(UnicodeString::iterator spos, UnicodeString::iterator epos);
        static std::optional<ISOTimeStamp> extractISOTimeStamp(UnicodeString::iterator spos, UnicodeString::iterator epos);
    };

    enum class ParseFormat
    {
        PARSE_MODE_BSQON = 0x0,
        PARSE_MODE_JSON
    };

    enum class ParseMode
    {
        PARSE_OUTPUT = 0x0,
        PARSE_SUGGEST
    };

    class Lexer 
    {
    public:
        UnicodeString::iterator m_cpos;
        LexerToken m_lastToken;

        const bool m_parse_bsqon;
        const bool m_parse_suggest;

        UnicodeString m_input;
        std::vector<ParseError> m_errors;

        Lexer(UnicodeString input, bool parse_bsqon, bool parse_suggest) : m_cpos(input.begin()), m_lastToken(), m_parse_bsqon(parse_bsqon), m_parse_suggest(parse_suggest), m_input(input), m_errors() {;}

    private:
        inline bool chkRegexMatch(const UnicodeRegex& re, UnicodeString::iterator& spos, UnicodeString::iterator& epos)
        {
            std::match_results<UnicodeString::iterator> m;
            bool mok = std::regex_search(this->m_cpos, this->m_input.end(), m, re);
            if(!mok) {
                return false;
            }
            else {
                spos = m[0].first;
                epos = m[0].second;
            
                return true;
            }
        }

        static void computeWSMoveExplicit(UnicodeString::iterator spos, UnicodeString::iterator epos, int64_t& line, int64_t col)
        {
            while(spos != epos) {
                if(*spos == '\n') {
                    line++;
                    col = 0;
                }
                else if(*spos == '\t') {
                    col += 4;
                }
                else {
                    col++;
                }

                spos++;
            }
        }

        template<unsigned int N>
        inline static bool chkConstantMatch(UnicodeString::iterator spos, UnicodeString::iterator epos, const char32_t (&cc)[N])
        {
            return std::equal(spos, epos, cc, cc + N - 1);
        }

        inline void setToken(TokenKind kind, UnicodeString::iterator spos, UnicodeString::iterator epos) 
        {
            this->m_cpos = epos;
            this->m_lastToken = LexerToken(kind, &this->m_input, spos - this->m_input.begin(), epos - this->m_input.begin());
        }

        UnicodeString::iterator scanStringContents(UnicodeString::iterator spos)
        {
            UnicodeString::iterator epos = this->m_input.end();

            if(this->m_parse_bsqon) {
                return std::find(spos, epos, U'"');
            }
            else {
                while(spos != epos) {
                    auto c = *spos;
                    if(c == U'"') {
                        break;
                    }

                    spos++;
                    if((spos != epos) & (c == U'\\')) {
                        auto escc = *spos;
                        if(escc != U'u') {
                            spos++;
                        }
                        else {
                            //TODO: if one of these is a " then we will skip it and swallow stuff 
                            //      -- the input is invalid anyway so no problem there but error reporting could be better
                            spos += std::min<ptrdiff_t>(5, std::distance(spos, epos));
                        }
                    }
                }

                return spos;
            }
        }

    public:
        TextPosition toTextPos(UnicodeString::iterator ii)
        {
            return std::distance(this->m_input.begin(), ii);
        }

        TextPosition tokenStartToTextPos(const LexerToken& tk)
        {
            return this->toTextPos(tk.tokenBegin());
        }

        TextPosition tokenEndToTextPos(const LexerToken& tk)
        {
            return this->toTextPos(tk.tokenEnd());
        }

        bool lexWS() 
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::whitespaceRe, spos, epos)) {
                this->m_cpos = epos;
            }
            else {
                return false;
            }
        }

        bool lexComment() {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::commentStartRe, spos, epos)) {
                if(chkConstantMatch(spos, epos, U"//")) {
                    epos = std::find(spos, this->m_input.end(), '\n');

                    this->m_cpos = epos;
                    return true;
                }
                else {
                    epos = std::search(spos, this->m_input.end(), LexerRegex::commentMultilineEndRe);

                    if(epos != this->m_input.end()) {
                        epos += 2;
                    }
                    else {    
                        this->m_errors.push_back(ParseError::createUnclosedMultiLineComment(this->toTextPos(spos), this->toTextPos(epos)));
                    }
                    
                    this->m_cpos = epos;
                    return true;
                }
            }
            else {
                return false;
            }
        }

        bool lexBytebuff()
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::bytebuffRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_BYTE_BUFFER, spos, epos);
                return true;
            }
            else {
                return false;
            }
        }

        bool lexTimeInfo()
        {
            UnicodeString::iterator spos, epos;

            if(this->chkRegexMatch(LexerRegex::fullTimeRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_DATE_TIME, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::fullTimeUTCRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_UTC_DATE_TIME, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::dateOnlyRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_PLAIN_DATE, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::timeOnlyRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_PLAIN_TIME, spos, epos);
                return true;
            }

            return false;
        }

        bool lexLogicalTime() 
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::logicalTimeRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_LOGICAL_TIME, spos, epos);
                return true;
            }
            else {
                return false;
            }
        }

        bool lexTickTime()
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::tickTimeRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_TICK_TIME, spos, epos);
                return true;
            }
            else {
                return false;
            }
        }

        bool lexTimestamp()
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::timestampRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_TIMESTAMP, spos, epos);
                return true;
            }
            else {
                return false;
            }
        }

        bool lexUUID()
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::uuidRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_UUID, spos, epos);
                return true;
            }
            else {
                return false;
            }
        }

        bool lexSHACode() 
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::shahashRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_SHA_HASH, spos, epos);
                return true;
            }
            else {
                return false;
            }
        }

        bool lexPath()
        {
            UnicodeString::iterator spos, epos;
            if(this->chkRegexMatch(LexerRegex::pathStartRe, spos, epos)) {
                epos = std::search(epos, this->m_input.end(), LexerRegex::pathEndRe);
                auto nlpos = std::find(epos, this->m_input.end(), '\n');

                if(epos != this->m_input.end() && (nlpos == this->m_input.end() || epos < nlpos)) {
                    epos += 1;
                    this->setToken(TokenKind::TOKEN_PATH_ITEM, spos, epos);
                }
                else {    
                    this->m_errors.push_back(ParseError::createUnclosedPath(this->toTextPos(spos), this->toTextPos(epos)));

                    //recover to end of line
                    epos = nlpos;
                    this->setToken(TokenKind::TOKEN_UNKNOWN, spos, epos);
                }
                    
                return true;
            }
            else {
                return false;
            }
        }

        bool lexNumber() 
        {
            UnicodeString::iterator spos, epos;

            if (this->m_parse_bsqon) {
                if(this->chkRegexMatch(LexerRegex::rationalRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_RATIONAL, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::decimalRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_DECIMAL, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::floatRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_FLOAT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::bignatRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_BIG_NAT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::bigintRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_BIG_INT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::natRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_NAT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::intRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_INT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::intNumberinoRe, spos, epos) && *spos != U'+' && *spos != U'-') {
                    this->setToken(TokenKind::TOKEN_NAT, spos, epos);
                    return true;
                }
            }
            else {
                if(this->chkRegexMatch(LexerRegex::floatNumberinoRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_FLOAT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::intExponentNumberinoRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_FLOAT, spos, epos);
                    return true;
                }

                if(this->chkRegexMatch(LexerRegex::intNumberinoRe, spos, epos)) {
                    this->setToken(TokenKind::TOKEN_INT, spos, epos);
                    return true;
                }
            }
    
            return false;
        }

        bool lexString() {
            UnicodeString::iterator spos, epos;

            if(this->chkRegexMatch(LexerRegex::stringStartRe, spos, epos)) {
                epos = this->scanStringContents(epos);

                if(chkConstantMatch(epos, this->m_input.end(), U"\"")) {
                    epos += 1;
                    this->setToken(TokenKind::TOKEN_STRING, spos, epos);
                }
                else {    
                    this->m_errors.push_back(ParseError::createUnclosedString(this->toTextPos(spos), this->toTextPos(epos)));
                    this->setToken(TokenKind::TOKEN_UNKNOWN, spos, epos);
                }
                    
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::asciistringStartRe, spos, epos)) {
                epos = this->scanStringContents(epos);

                if(chkConstantMatch(epos, this->m_input.end(), U"\"}")) {
                    epos += 2;
                    this->setToken(TokenKind::TOKEN_ASCII_STRING, spos, epos);
                }
                else {    
                    this->m_errors.push_back(ParseError::createUnclosedString(this->toTextPos(spos), this->toTextPos(epos)));
                    this->setToken(TokenKind::TOKEN_UNKNOWN, spos, epos);
                }
                    
                return true;
            }
    
            return false;
        }

        bool lexRegex() 
        {
            UnicodeString::iterator spos, epos;

            if(this->chkRegexMatch(LexerRegex::regexStartRe, spos, epos)) {
                epos = this->scanStringContents(epos);

                if(chkConstantMatch(epos, this->m_input.end(), U"\"}")) {
                    epos += 2;
                    this->setToken(TokenKind::TOKEN_REGEX, spos, epos);
                }
                else {    
                    this->m_errors.push_back(ParseError::createUnclosedString(this->toTextPos(spos), this->toTextPos(epos)));
                    this->setToken(TokenKind::TOKEN_UNKNOWN, spos, epos);
                }
                    
                return true;
            }

            return false;
        }

        bool lexSymbol(bool nokeyword) 
        {
            UnicodeString::iterator spos, epos;
            if(this->m_parse_bsqon) {
                if(this->chkRegexMatch(LexerRegex::bracketBSQONRe, spos, epos)) {
                    if(*spos == U'{') {
                        this->setToken(TokenKind::TOKEN_LBRACE, spos, epos);
                        return true;
                    }
                    else if(*spos == U'}') {
                        this->setToken(TokenKind::TOKEN_RBRACE, spos, epos);
                        return true;
                    }
                    else if(*spos == U'[') {
                        this->setToken(TokenKind::TOKEN_LBRACKET, spos, epos);
                        return true;
                    }
                    else if(*spos == U']') {
                        this->setToken(TokenKind::TOKEN_RBRACKET, spos, epos);
                        return true;
                    }
                    else if(*spos == U'(') {
                        this->setToken(TokenKind::TOKEN_LPAREN, spos, epos);
                        return true;
                    }
                    else if(*spos == U')') {
                        this->setToken(TokenKind::TOKEN_LPAREN, spos, epos);
                        return true;
                    }
                    else if(*spos == U'<') {
                        this->setToken(TokenKind::TOKEN_LANGLE, spos, epos);
                        return true;
                    }
                    else {
                        assert(*spos == U'>');
                        this->setToken(TokenKind::TOKEN_RANGLE, spos, epos);
                        return true;
                    }
                }

                if(this->chkRegexMatch(LexerRegex::symbolBSQONRe, spos, epos)) {
                    if(*spos == U',') {
                        this->setToken(TokenKind::TOKEN_COMMA, spos, epos);
                        return true;
                    }
                    else if(*spos == U'&') {
                        this->setToken(TokenKind::TOKEN_AMP, spos, epos);
                        return true;
                    }
                    else if(*spos == U'|') {
                        this->setToken(TokenKind::TOKEN_BAR, spos, epos);
                        return true;
                    }
                    else if(*spos == U'!') {
                        this->setToken(TokenKind::TOKEN_BANG, spos, epos);
                        return true;
                    }
                    else if(*spos == U'@') {
                        this->setToken(TokenKind::TOKEN_AT, spos, epos);
                        return true;
                    }
                    else if(*spos == U':') {
                        if(this->chkConstantMatch(spos, epos, U"::")) {
                            this->setToken(TokenKind::TOKEN_COLON_COLON, spos, epos);
                            return true;
                        }
                        else {
                            this->setToken(TokenKind::TOKEN_COLON, spos, epos);
                            return true;
                        }
                    }
                    else if(*spos == U'=') {
                        if(this->chkConstantMatch(spos, epos, U"=>")) {
                            this->setToken(TokenKind::TOKEN_LDOTS, spos, epos);
                            return true;
                        }
                        else {
                            this->setToken(TokenKind::TOKEN_DOT, spos, epos);
                            return true;
                        }
                    }
                    else {
                        assert(*spos == U'.');
                        if(this->chkConstantMatch(spos, epos, U"...")) {
                            this->setToken(TokenKind::TOKEN_LDOTS, spos, epos);
                            return true;
                        }
                        else {
                            this->setToken(TokenKind::TOKEN_DOT, spos, epos);
                            return true;
                        }
                    }
                }

                if(!nokeyword && this->chkRegexMatch(LexerRegex::keywordBSQONRe, spos, epos)) {
                    if(this->chkConstantMatch(spos, epos, U"true")) {
                        this->setToken(TokenKind::TOKEN_TRUE, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"false")) {
                        this->setToken(TokenKind::TOKEN_FALSE, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"nothing")) {
                        this->setToken(TokenKind::TOKEN_NOTHING, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"something")) {
                        this->setToken(TokenKind::TOKEN_SOMETHING, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"none")) {
                        this->setToken(TokenKind::TOKEN_NONE, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"some")) {
                        this->setToken(TokenKind::TOKEN_SOME, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"ok")) {
                        this->setToken(TokenKind::TOKEN_OK, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"err")) {
                        this->setToken(TokenKind::TOKEN_ERR, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"in")) {
                        this->setToken(TokenKind::TOKEN_IN, spos, epos);
                        return true;
                    }
                    else {
                        assert(this->chkConstantMatch(spos, epos, U"let"));
                        this->setToken(TokenKind::TOKEN_LET, spos, epos);
                        return true;
                    }
                }
            }
            else {
                if(this->chkRegexMatch(LexerRegex::bracketBSQONRe, spos, epos)) {
                    if(*spos == U'{') {
                        this->setToken(TokenKind::TOKEN_LBRACE, spos, epos);
                        return true;
                    }
                    else if(*spos == U'}') {
                        this->setToken(TokenKind::TOKEN_RBRACE, spos, epos);
                        return true;
                    }
                    else if(*spos == U'[') {
                        this->setToken(TokenKind::TOKEN_LBRACKET, spos, epos);
                        return true;
                    }
                    else {
                        assert(*spos == U']');
                        this->setToken(TokenKind::TOKEN_RBRACKET, spos, epos);
                        return true;
                    }
                }

                if(this->chkRegexMatch(LexerRegex::symbolBSQONRe, spos, epos)) {
                    if(*spos == U',') {
                        this->setToken(TokenKind::TOKEN_COMMA, spos, epos);
                        return true;
                    }
                    else {
                        this->setToken(TokenKind::TOKEN_COLON, spos, epos);
                        return true;
                    }
                }

                if(!nokeyword && this->chkRegexMatch(LexerRegex::keywordBSQONRe, spos, epos)) {
                    if(this->chkConstantMatch(spos, epos, U"true")) {
                        this->setToken(TokenKind::TOKEN_TRUE, spos, epos);
                        return true;
                    }
                    else if(this->chkConstantMatch(spos, epos, U"false")) {
                        this->setToken(TokenKind::TOKEN_FALSE, spos, epos);
                        return true;
                    }
                    else {
                        this->setToken(TokenKind::TOKEN_NULL, spos, epos);
                        return true;
                    }
                }
            }

            return false;
        }

        bool lexName() {
            UnicodeString::iterator spos, epos;

            if(this->chkRegexMatch(LexerRegex::nameSrcRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_SRC, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::nameRefRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_REFERENCE, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::typeNameRe, spos, epos)) {
                this->setToken(TokenKind::TOKEN_TYPE, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::propertyNameRE, spos, epos)) {
                this->setToken(TokenKind::TOKEN_PROPERTY, spos, epos);
                return true;
            }

            if(this->chkRegexMatch(LexerRegex::specialUnderscoreRE, spos, epos)) {
                this->setToken(TokenKind::TOKEN_UNDERSCORE, spos, epos);
                return true;
            }
    
            return false;
        }

        bool peekTokenDoWork() {
            if (this->m_lastToken.isValid()) {
                return true;
            }

            while (this->lexWS() || this->lexComment()) {
                ; //eat the token
            }   

            return this->lexBytebuff() || this->lexTimeInfo() || this->lexLogicalTime() || this->lexTickTime() || this->lexTimestamp() ||
                this->lexUUID() || this->lexSHACode() || this->lexPath() ||
                this->lexNumber() || this->lexString() || this->lexRegex() ||
                this->lexSymbol(false) || this->lexName();
        }

        LexerToken peekToken() 
        {
            while (!this->peekTokenDoWork()) {
                if(this->m_cpos == this->m_input.end()) {
                    this->m_lastToken = LexerToken::singletonEOFToken;
                    return this->m_lastToken;
                }

                //save first unparseable position, now try to find a token boundary -- whitespace, a symbol, or a comment
                auto spos = this->m_cpos;
                while(!this->lexWS() && !this->lexComment() && !this->lexSymbol(true)) {
                    this->m_cpos++;
                }

                this->m_errors.push_back(ParseError::createUnknownToken(this->toTextPos(spos), this->toTextPos(this->m_cpos)));
            }

            return this->m_lastToken;
        }

        LexerToken popToken() {
            auto tt = this->peekToken();
        
            this->m_lastToken = LexerToken::singletonInvalidToken;
            return tt;
        }

        inline bool testToken(TokenKind tkind) {
            return this->peekToken().kind == tkind;
        }

        inline bool testAndConsumeToken(TokenKind tkind) {
            if(this->peekToken().kind != tkind) {
                return false;
            }

            this->m_lastToken = LexerToken::singletonInvalidToken;
            return true;
        }

/*
        bool testTokens(...tkinds: string[]) {
        const opos = this.m_cpos;
        const olt = this.m_lastToken;

        for (let i = 0; i < tkinds.length; ++i) {
            if (this.testToken(tkinds[i])) {
                this.popToken();
            }
            else {
                this.m_cpos = opos;
                this.m_lastToken = olt;

                return false;
            }
        }

        this.m_cpos = opos;
        this.m_lastToken = olt;
        return true;
    }

        void testTokenWValue(tk: {kind: TokenKind, value: string}): boolean {
        return this.peekToken() !== undefined && this.peekToken()!.kind === tk.kind && this.peekToken()!.value === tk.value;
    }

        void testTokensWValue(...tks: {kind: TokenKind, value: string}[]): boolean {
        const opos = this.m_cpos;
        const olt = this.m_lastToken;

        for (let i = 0; i < tks.length; ++i) {
            if (!this.testTokenWValue(tks[i])) {
                this.m_cpos = opos;
                this.m_lastToken = olt;

                return false;
            }
        }

        this.m_cpos = opos;
        this.m_lastToken = olt;
        return true;
    }

    bool expectToken(tkind: string) {
        this.raiseErrorIf(!this.testToken(tkind), `Expected token ${tkind} but got ${this.peekToken()?.value ?? "[Unknown]"}`);
    }

    bool expectTokenAndPop(tkind: string): {kind: string, value: string} {
        this.expectToken(tkind);
        return this.popToken() as {kind: string, value: string};
    }
*/
    };
}
