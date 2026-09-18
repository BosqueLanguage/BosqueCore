#include "strings.h"

namespace ᐸRuntimeᐳ
{
    thread_local GCAllocator<PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeLeaf_CString_allocator(&g_typeinfo_PosRBTreeLeaf_CString);
    thread_local GCAllocator<PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>> PosRBTreeNode_CString_allocator(&g_typeinfo_PosRBTreeNode_CString);

    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::s_leaftypeinfo = &g_typeinfo_PosRBTreeLeaf_CString;
    template<> thread_local GCAllocator<PosRBTreeLeaf<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>>* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::s_leafallocator = &PosRBTreeLeaf_CString_allocator;
    template<> const TypeInfo* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::s_nodetypeinfo = &g_typeinfo_PosRBTreeNode_CString;
    template<> thread_local GCAllocator<PosRBTreeNode<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE>>* PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::s_nodeallocator = &PosRBTreeNode_CString_allocator;

    thread_local GCAllocator<PosRBTreeLeaf<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeLeaf_String_allocator(&g_typeinfo_PosRBTreeLeaf_String);
    thread_local GCAllocator<PosRBTreeNode<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>> PosRBTreeNode_String_allocator(&g_typeinfo_PosRBTreeNode_String);

    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::s_leaftypeinfo = &g_typeinfo_PosRBTreeLeaf_String;
    template<> thread_local GCAllocator<PosRBTreeLeaf<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>>* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::s_leafallocator = &PosRBTreeLeaf_String_allocator;
    template<> const TypeInfo* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::s_nodetypeinfo = &g_typeinfo_PosRBTreeNode_String;
    template<> thread_local GCAllocator<PosRBTreeNode<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE>>* PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::s_nodeallocator = &PosRBTreeNode_String_allocator;


    size_t writeMustEscapeCCharValue(char value, std::array<char, 64>& numbuf)
    {
        auto ii = std::find_if(s_escape_names_char_simple.begin(), s_escape_names_char_simple.end(), [value](const std::pair<uint8_t, std::pair<size_t, const char*>>& p) { 
            return p.first == (uint8_t)value; 
        });
            
        if(ii != s_escape_names_char_simple.end()) {
            return (size_t)std::snprintf(numbuf.data(), numbuf.size(), "%s", ii->second.second);
        }
        else {
            return (size_t)std::snprintf(numbuf.data(), numbuf.size(), "%%x%x;", (uint8_t)value);
        }
    }

    size_t writeMustEscapeUnicodeCharValue(char32_t value, std::array<char, 64>& numbuf)
    {
        auto ii = std::find_if(s_escape_names_unicode.begin(), s_escape_names_unicode.end(), [value](const std::pair<uint32_t, std::pair<size_t, const char*>>& p) { 
            return p.first == (uint32_t)value; 
        });
            
        if(ii != s_escape_names_unicode.end()) {
            return (size_t)std::snprintf(numbuf.data(), numbuf.size(), "%s", ii->second.second);
        }
        else {
            return (size_t)std::snprintf(numbuf.data(), numbuf.size(), "%%x%x;", (uint32_t)value);
        }
    }

    ///////////////////////////////
    //CString
    ///////////////////////////////

    void jsonParseToBSQ_CString(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected JSON string for CString");

        std::string sstr = j.get<std::string>();
        size_t jlen = sstr.size();
        CStringStreamingBuilder builder{};
        for(size_t i = 0; i < jlen; ++i)
        {
            bsq_validate(isLegalCChar(static_cast<uint8_t>(sstr[i])), "JSON -> BSQ", 0, nullptr, "Invalid CChar literal");
            builder.appendChar(sstr[i]);
        }

        *((XCString*)resptr) = XCString{builder.finalize()};
    }

    void parseToBSQ_CString(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        if(lexer->getCurrentTokenType() != BAPITokenType::LiteralCString) {
            bsq_validate(lexer->allowSloppyStrings && lexer->getCurrentTokenType() == BAPITokenType::LiteralString, "Parse -> BSQ", 0, nullptr, "Expected a CString or String token");
        }
     
        size_t tlen = lexer->getCurrentTokenDataSize();
        if(tlen == 2) {
            *((XCString*)resptr) = XCString{};
        }
        else {
            //eat opening '
            size_t cpos = 1; 
            IOBufferIterator ii = lexer->getCurrentTokenIterator();
            ++ii;

            CStringStreamingBuilder builder{};
            while(cpos < tlen - 1) { //ignore the closing '
                uint8_t cbyte = *ii;
                
                char output = 0;
                if(cbyte != '%') {
                    bsq_validate(isLegalCChar(cbyte), "Parse -> BSQ", 0, nullptr, "Invalid CChar literal");

                    output = cbyte; //just a simple char
                    cpos++;
                    ++ii;
                }
                else {
                    std::array<uint8_t, 64> inbuff{}; 
                    size_t bytecount = 0;

                    while(bytecount < 64 && cpos < tlen - 1) {
                        uint8_t bb = *ii;
                        inbuff[bytecount++] = bb;
                        cpos++;
                        ++ii;

                        if(bb == ';') {
                            break;
                        }
                    }
                    bsq_validate(inbuff[bytecount - 1] == ';', "Parse -> BSQ", 0, nullptr, "Encoded CChar literal missing terminating ';'");

                    bool charok = processEncodedCChar(inbuff, bytecount, output);
                    bsq_validate(charok, "Parse -> BSQ", 0, nullptr, "Invalid CChar literal");
                }

                builder.appendChar(output);
            }

            *((XCString*)resptr) = XCString{builder.finalize()}; 
        }

        lexer->consume();
    }

    json bsqToJSON_CString(const TypeInfo* tinfo, const void* valptr)
    {
        XCString v = *(XCString*)valptr;

        json j = std::string(v.begin(), v.end());
        return j;
    }

    void bsqToBAPI_CString(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XCString v = *(XCString*)valptr;
        std::array<char, 64> numbuf{};

        builder->appendChar('\'');
        for(auto iter = v.begin(); iter != v.end(); ++iter) {
            char c = *iter;
            if(!isMustEscapeCChar(c)) {
                builder->appendChar(c);
            }
            else {
                size_t written = writeMustEscapeCCharValue(c, numbuf);
                builder->appendConstString(numbuf.data(), written);
            }
        }
        builder->appendChar('\'');
    }

    void displayValue_CString(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XCString v = *(XCString*)valptr;
        std::array<char, 64> numbuf{};

        os << getDisplayIndent(indent) << '\'';
        for(auto iter = v.begin(); iter != v.end(); ++iter) {
            char c = *iter;
            if(!isMustEscapeCChar(c)) {
                os << c;
            }
            else {
                size_t written = writeMustEscapeCCharValue(c, numbuf);
                os << std::string(numbuf.data(), written);
            }
        }
        os << '\'';
    }

    ///////////////////////////////
    //String
    ///////////////////////////////

    void jsonParseToBSQ_String(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        bsq_validate(j.is_string(), "JSON -> BSQ", 0, nullptr, "Expected JSON string for String");

        std::string sstr = j.get<std::string>();
        size_t jlen = sstr.size();
        StringStreamingBuilder builder{};
        for(size_t i = 0; i < jlen; ++i)
        {
            if(isSingleByteEncoding(static_cast<uint8_t>(sstr[i]))) {
                builder.appendChar(sstr[i]);
            }
            else {
                size_t mbsize = multibyteCharCount(static_cast<uint8_t>(sstr[i]));
                bsq_validate(i + mbsize <= jlen, "JSON -> BSQ", 0, nullptr, "Invalid multibyte sequence in JSON string");

                std::array<uint8_t, 4> mbseq{};
                for(size_t j = 0; j < mbsize; j++) {
                    mbseq[j] = static_cast<uint8_t>(sstr[i + j]);
                }

                char32_t cchar = multibyteToUChar(mbseq, mbsize);
                bsq_validate(isLegalUnicodeChar(cchar), "JSON -> BSQ", 0, nullptr, "Invalid Unicode character in JSON string");

                builder.appendChar(cchar);
                i += mbsize - 1;
            }
        }

        *((XString*)resptr) = XString{builder.finalize()};
    }

    void parseToBSQ_String(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        if(lexer->getCurrentTokenType() != BAPITokenType::LiteralString) {
            bsq_validate(lexer->allowSloppyStrings && lexer->getCurrentTokenType() == BAPITokenType::LiteralCString, "Parse -> BSQ", 0, nullptr, "Expected a CString or String token");
        }
     
        size_t tlen = lexer->getCurrentTokenDataSize();
        if(tlen == 2) {
            *((XString*)resptr) = XString{};
        }
        else {
            //eat opening "
            size_t cpos = 1; 
            IOBufferIterator ii = lexer->getCurrentTokenIterator();
            ++ii;

            StringStreamingBuilder builder{};
            while(cpos < tlen - 1) { //ignore the closing "
                uint8_t cbyte = *ii;
                
                char32_t output = 0;
                if(cbyte != '%') {
                    if(isSingleByteEncoding(cbyte)) {
                        output = static_cast<char32_t>(cbyte);
                        cpos++;
                        ++ii;
                    }
                    else {
                        size_t mbsize = multibyteCharCount(cbyte);
                        bsq_validate(cpos + mbsize <= tlen, "Parse -> BSQ", 0, nullptr, "Invalid multibyte sequence in BAPI string");

                        std::array<uint8_t, 4> mbseq{};
                        for(size_t j = 0; j < mbsize; j++) {
                            mbseq[j] = *ii;
                            cpos++;
                            ++ii;
                        }

                        output = multibyteToUChar(mbseq, mbsize);
                        bsq_validate(isLegalUnicodeChar(output), "Parse -> BSQ", 0, nullptr, "Invalid Unicode character in BAPI string");
                    }
                }
                else {
                    std::array<uint8_t, 64> inbuff{}; 
                    size_t bytecount = 0;

                    while(bytecount < 64 && cpos < tlen - 1) {
                        uint8_t bb = *ii;
                        inbuff[bytecount++] = bb;
                        cpos++;
                        ++ii;

                        if(bb == ';') {
                            break;
                        }
                    }
                    bsq_validate(inbuff[bytecount - 1] == ';', "Parse -> BSQ", 0, nullptr, "Encoded UnicodeChar literal missing terminating ';'");

                    bool charok = processEncodedUnicodeChar(inbuff, bytecount, output);
                    bsq_validate(charok, "Parse -> BSQ", 0, nullptr, "Invalid UnicodeChar literal");
                }

                builder.appendChar(output);
            }

            *((XString*)resptr) = XString{builder.finalize()}; 
        }

        lexer->consume();
    }        

    json bsqToJSON_String(const TypeInfo* tinfo, const void* valptr)
    {
        XString v = *(XString*)valptr;
        std::array<char, 64> numbuf{};

        std::string jstr;
        jstr.reserve(((XString*)valptr)->size());

        for(XStringIterator it = v.begin(); it != v.end(); ++it) {
            char32_t cchar = *it;
            if(isSingleByteEncoding(cchar)) {
                jstr.push_back(static_cast<char>(cchar));
            }
            else {
                std::array<uint8_t, 64> outbuff;
                size_t bytes = ucharToMultiByteEncoding(cchar, outbuff);

                for(size_t i = 0; i < bytes; i++) {
                    jstr.push_back((char)outbuff[i]);
                }
            }
        }

        json j = std::string(jstr.begin(), jstr.end());
        return j;
    }

    void bsqToBAPI_String(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        XString v = *(XString*)valptr;
        std::array<char, 64> numbuf{};

        builder->appendChar('"');

        for(XStringIterator it = v.begin(); it != v.end(); ++it) {
            char32_t cchar = *it;

            if(isSingleByteEncoding(cchar)) {
                if(!isMustEscapeUnicodeChar(cchar)) {
                    builder->appendByte(cchar);
                }
                else {
                    size_t written = writeMustEscapeUnicodeCharValue(cchar, numbuf);
                    builder->appendConstString(numbuf.data(), written);
                }
            }
            else {
                std::array<uint8_t, 64> outbuff;
                size_t bytes = ucharToMultiByteEncoding(cchar, outbuff);

                for(size_t i = 0; i < bytes; i++) {
                    builder->appendByte(outbuff[i]);
                }
            }
        }
        builder->appendChar('"');
    }

    void displayValue_String(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        XString v = *(XString*)valptr;
        std::array<char, 64> numbuf{};

        os << getDisplayIndent(indent) << "\"";
        for(XStringIterator it = v.begin(); it != v.end(); ++it) {
            char32_t cchar = *it;
            if(isSingleByteEncoding(cchar)) {
                if(!isMustEscapeUnicodeChar(cchar)) {
                    os << static_cast<char>(cchar);
                }
                else {
                    size_t written = writeMustEscapeUnicodeCharValue(cchar, numbuf);
                    os << std::string(numbuf.data(), written);
                }
            }
            else {
                std::array<uint8_t, 64> outbuff;
                size_t bytes = ucharToMultiByteEncoding(cchar, outbuff);

                for(size_t i = 0; i < bytes; i++) {
                    os << (char)outbuff[i];
                }
            }
        }
        os << "\"";
    }

    ///////////////////////////////////////////

    XCString XCString::natToCString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llin", (long long int)value);
        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::intToCString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llii", (long long int)value);
        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::chkNatToCString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliN", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkNat values
        }

        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::chkIntToCString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliI", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkInt values
        }

        return XCString::mk(numbuf, static_cast<size_t>(written));
    }

    XCString XCString::floatToCString(double value) {
        char numbuf[64];
        int written = 0;
        
        if(std::floor(value) != value) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lgf", value);
        }
        else {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lg.0f", value);
        }

        return XCString::mk(numbuf, static_cast<size_t>(written));
    }


    ///////////////////////////////////////////

    XBool XCString::startsWith(const XCString& prefix) const
    {
        if(prefix.empty()) {
            return XTRUE;
        }

        if(prefix.size() > this->size()) {
            return XFALSE;
        }

        auto ii = this->begin();
        auto jj = prefix.begin();
        while(jj != prefix.end()) {
            if(*ii != *jj) {
                return XFALSE;
            }
            ++ii;
            ++jj;
        }

        return XTRUE;
    }

    XBool XCString::startsWith(const boost::regex& prefix) const
    {
        bool match = boost::regex_search(this->begin(), this->end(), prefix, boost::match_continuous);
        return XBool{match};
    }

    XBool XCString::startsWith(XCChar prefix) const
    {
        auto ii = this->begin();
        if(ii == this->end()) {
            return XFALSE;
        }

        return XBool{*ii == (char)prefix.value};
    }

    XBool XCString::endsWith(const XCString& suffix) const
    {
        if(suffix.empty()) {
            return XTRUE;
        }

        if(suffix.size() > this->size()) {
            return XFALSE;
        }

        auto ii = this->end();
        auto jj = suffix.end();

        while(jj != suffix.begin()) {
            --ii;
            --jj;
            if(*ii != *jj) {
                return XFALSE;
            }
        }

        return XTRUE;
    }

    XBool XCString::endsWith(const boost::regex& suffix) const
    {
        assert(false); //TODO: Not implemented -- regex for endsWith
    }

    XBool XCString::endsWith(XCChar suffix) const
    {
        auto ii = this->end();
        if(ii == this->begin()) {
            return XFALSE;
        }

        --ii;
        return XBool{*ii == (char)suffix.value};
    }

    XByteBuffer XCString::toByteBuffer(const XCString& cstr)
    {
        if(cstr.empty()) {
            return XByteBuffer{};
        }
        else {
            ByteBufferStreamingBuilder builder{};
            std::array<char, 64> numbuf{};

            for(auto iter = cstr.begin(); iter != cstr.end(); ++iter) {
                builder.appendByte((uint8_t)(*iter));
            }

            return builder.finalize();
        }
    }

    XBool XCString::fromByteBuffer(const XByteBuffer& buffer, XCString& result)
    {
        if(buffer.bytes() == 0) {
            result = XCString{};
            return XTRUE;
        }
        else {
            CStringStreamingBuilder builder{};
            if(buffer.isInline()) {
                const uint8_t* inlinebytes = buffer.inlinedata();

                for(auto ii = inlinebytes; ii != inlinebytes + buffer.bytes(); ++ii) {
                    uint8_t byte = *ii;
                    if(!isLegalCChar(byte)) {
                        return XFALSE;
                    }

                    builder.appendChar((char)byte);
                }
            }
            else {
                for(auto ii = buffer.begin(); ii != buffer.end(); ++ii) {
                    uint8_t byte = *ii;

                    if(!isLegalCChar(byte)) {
                        return XFALSE;
                    }
                    builder.appendChar((char)byte);
                }
            }

            result = XCString{builder.finalize()};
            return XTRUE;
        }
    }

    XCString XCString::append(XCString other) const
    {
        assert(!this->ucstr.empty());
        assert(!other.ucstr.empty());

        if(this->ucstr.isInline() && other.ucstr.isInline()) {
            if(this->ucstr.inlinecstr.data[0] + other.ucstr.inlinecstr.data[0] <= CStrRootInlineContent::CSTR_MAX_SIZE) {
                return XCString{CStrRootInlineContent{this->ucstr.inlinecstr, other.ucstr.inlinecstr}};
            }
            else {
                static_assert(CStrRootInlineContent::CSTR_MAX_SIZE * 2 <= CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, "If this changes then we need more complex logic like in list append");
                
                return XCString{CStrRootTreeContent{PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::mkinitial_append(this->ucstr.inlinecstr.data.begin() + 1, this->ucstr.inlinecstr.data.begin() + 1 + this->ucstr.inlinecstr.data[0], (const char*)other.ucstr.inlinecstr.data.begin() + 1, (const char*)other.ucstr.inlinecstr.data.begin() + 1 + other.ucstr.inlinecstr.data[0])}};
            }
        }
        else {
            PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING> lnode{};
            if(this->ucstr.isInline()) {
                lnode = PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::mkinitial(this->ucstr.inlinecstr.data.begin() + 1, this->ucstr.inlinecstr.data.begin() + 1 + this->ucstr.inlinecstr.data[0]);
            }
            else {
                lnode = this->ucstr.treecstr.postree;
            }

            PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING> rnode{};
            if(other.ucstr.isInline()) {
                rnode = PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::mkinitial(other.ucstr.inlinecstr.data.begin() + 1, other.ucstr.inlinecstr.data.begin() + 1 + other.ucstr.inlinecstr.data[0]);
            }
            else {
                rnode = other.ucstr.treecstr.postree;
            }

            return XCString{CStrRootTreeContent{PosRBTree<char, CStrRootTreeContent::CSTR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_CSTRING>::append(lnode, rnode)}};
        }
    }

    XCString XCString::trim(XBool front, XBool back) const
    {
        if(this->empty()) {
            return XCString{};
        }

        auto start = this->begin();
        auto end = this->end();

        if((bool)front) {
            while(start != end && isTrimableWhitespace(*start)) {
                ++start;
            }
        }

        if(start == end) {
            return XCString{};
        }

        if((bool)back) {
            --end;
            while(start != end && isTrimableWhitespace(*end)) {
                --end;
            }

            if(!isTrimableWhitespace(*end)) {
                ++end;
            }
        }

        if(start == end) {
            return XCString{};
        }

        if(start == this->begin() && end == this->end()) {
            return *this;
        }
        else {
            //TODO: this is expensive -- we want to 1) keep track of deleted whitespace and subtract here 2) implement an string split/slice so this is at least log time (NOT O(N))
            return XCString::mk(start, end, std::distance(start, end));
        }
    }

    void jsonParseToBSQ_FCString(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        assert(false); // Not Implemented: jsonParseToBSQ_FCString
    }

    void parseToBSQ_FCString(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        assert(false); // Not Implemented: parseToBSQ_FCString
    }

    json bsqToJSON_FCString(const TypeInfo* tinfo, const void* valptr)
    {
        assert(false); // Not Implemented: bsqToJSON_FCString
    }

    void bsqToBAPI_FCString(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        assert(false); // Not Implemented: bsqToBAPI_FCString
    }

    void displayValue_FCString(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        assert(false); // Not Implemented: displayValue_FCString
    }

    void jsonParseToBSQ_CRegex(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        assert(false); // Not Implemented: jsonParseToBSQ_CRegex
    }

    void parseToBSQ_CRegex(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        assert(false); // Not Implemented: parseToBSQ_CRegex
    }
    
    json bsqToJSON_CRegex(const TypeInfo* tinfo, const void* valptr)
    {
        assert(false); // Not Implemented: bsqToJSON_CRegex
    }

    void bsqToBAPI_CRegex(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        assert(false); // Not Implemented: bsqToBAPI_CRegex
    }
    
    void displayValue_CRegex(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        assert(false); // Not Implemented: displayValue_CRegex
    }

    XString XString::natToString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llin", (long long int)value);

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::intToString(int64_t value) {
        char numbuf[64];
        int written = std::snprintf(numbuf, sizeof(numbuf), "%llii", (long long int)value);

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::chkNatToString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliN", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkNat values
        }

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::chkIntToString(__int128_t value) {
        char numbuf[64];
        int written = 0;

        if(value <= (__int128_t)std::numeric_limits<int64_t>::max()) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%lliI", (long long int)value);
        }
        else {
            assert(false); // Not Implemented: format for very large ChkInt values
        }

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XString XString::floatToString(double value) {
        char numbuf[64];
        int written = 0;
        
        if(std::floor(value) != value) {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lgf", value);
        }
        else {
            written = std::snprintf(numbuf, sizeof(numbuf), "%.12lg.0f", value);
        }

        char32_t numbuf32[64];
        std::transform(numbuf, numbuf + written, numbuf32, [](char c) { return static_cast<char32_t>(c); });
        return XString::mk(numbuf32, static_cast<size_t>(written));
    }

    XBool XString::startsWith(const XString& prefix) const
    {
        if(prefix.empty()) {
            return XTRUE;
        }

        if(prefix.size() > this->size()) {
            return XFALSE;
        }

        auto ii = this->begin();
        auto jj = prefix.begin();
        while(jj != prefix.end()) {
            if(*ii != *jj) {
                return XFALSE;
            }
            ++ii;
            ++jj;
        }

        return XTRUE;
    }

    XBool XString::startsWith(const boost::u32regex& prefix) const
    {
        bool match = boost::u32regex_search(this->begin(), this->end(), prefix, boost::match_continuous);
        return XBool{match};
    }

    XBool XString::startsWith(XUnicodeChar prefix) const
    {
        auto ii = this->begin();
        if(ii == this->end()) {
            return XFALSE;
        }

        return XBool{*ii == prefix.value};
    }

    XBool XString::endsWith(const XString& suffix) const
    {
        if(suffix.empty()) {
            return XTRUE;
        }

        if(suffix.size() > this->size()) {
            return XFALSE;
        }

        auto ii = this->end();
        auto jj = suffix.end();
        while(jj != suffix.begin()) {
            --ii;
            --jj;
            if(*ii != *jj) {
                return XFALSE;
            }
        }

        return XTRUE;
    }

    XBool XString::endsWith(const boost::u32regex& suffix) const
    {
        assert(false); //TODO: Not implemented -- regex for endsWith
    }

    XBool XString::endsWith(XUnicodeChar suffix) const
    {
        auto ii = this->end();
        if(ii == this->begin()) {
            return XFALSE;
        }

        --ii;
        return XBool{*ii == suffix.value};
    }

    XString XString::fromCString(const XCString& cstr)
    {
        if(cstr.empty()) {
            return XString{};
        }
        else {
            StringStreamingBuilder builder{};
            for(auto ii = cstr.begin(); ii != cstr.end(); ++ii) {
                builder.appendChar(*ii);
            }

            return builder.finalize();
        }
    }

    XBool XString::toCString(const XString& str, XCString& cstr)
    {
        if(str.empty()) {
            cstr = XCString{};
            return XTRUE;
        }
        else {
            CStringStreamingBuilder builder{};
            for(auto ii = str.begin(); ii != str.end(); ++ii) {
                char32_t cc = *ii;

                if(cc > 127 || !isLegalCChar((uint8_t)cc)) {
                    return XFALSE;
                }

                builder.appendChar((char)cc);
            }

            cstr = builder.finalize();
            return XTRUE;
        }
    }

    XByteBuffer XString::toByteBuffer(const XString& str)
    {
        if(str.empty()) {
            return XByteBuffer{};
        }
        else {
            ByteBufferStreamingBuilder builder{};
            for(auto ii = str.begin(); ii != str.end(); ++ii) {
                char32_t cc = *ii;
                if(isSingleByteEncoding(cc)) {
                    builder.appendByte((uint8_t)cc);
                }
                else {
                    std::array<uint8_t, 64> outbuff;
                    size_t bytes = ucharToMultiByteEncoding(cc, outbuff);

                    for(size_t i = 0; i < bytes; i++) {
                        builder.appendByte(outbuff[i]);
                    }
                }
            }

            return builder.finalize();
        }
    }

    XBool XString::fromByteBuffer(const XByteBuffer& buffer, XString& result)
    {
        if(buffer.bytes() == 0) {
            result = XString{};
            return XTRUE;
        }
        else {
            StringStreamingBuilder builder{};
            if(buffer.isInline()) {
                const uint8_t* inlinebytes = buffer.inlinedata();
                const uint8_t* cpos = inlinebytes;

                while(cpos != inlinebytes + buffer.bytes()) {
                    uint8_t cbyte = *cpos;

                    if(isSingleByteEncoding(cbyte)) {
                        builder.appendChar((char)cbyte);
                        ++cpos;
                    }
                    else {
                        size_t mbsize = multibyteCharCount(cbyte);
                        std::array<uint8_t, 4> mbseq{};
                        
                        for(size_t j = 0; j < mbsize; j++) {
                            if(cpos == inlinebytes + buffer.bytes()) {
                                return XFALSE;
                            }

                            mbseq[j] = *cpos;
                            ++cpos;
                        }

                        char32_t output = multibyteToUChar(mbseq, mbsize);
                        if(!isLegalUnicodeChar(output)) {
                            return XFALSE;
                        }

                        builder.appendChar(output);
                    }
                }
            }
            else {
                auto cpos = buffer.begin();

                while(cpos != buffer.end()) {
                    uint8_t cbyte = *cpos;

                    if(isSingleByteEncoding(cbyte)) {
                        builder.appendChar((char)cbyte);
                        ++cpos;
                    }
                    else {
                        size_t mbsize = multibyteCharCount(cbyte);
                        std::array<uint8_t, 4> mbseq{};
                        
                        for(size_t j = 0; j < mbsize; j++) {
                            if(cpos == buffer.end()) {
                                return XFALSE;
                            }

                            mbseq[j] = *cpos;
                            ++cpos;
                        }

                        char32_t output = multibyteToUChar(mbseq, mbsize);
                        if(!isLegalUnicodeChar(output)) {
                            return XFALSE;
                        }

                        builder.appendChar(output);
                    }
                }
            }

            result = XString{builder.finalize()};
            return XTRUE;
        }
    }

    XString XString::append(XString other) const
    {
        assert(!this->ustr.empty());
        assert(!other.ustr.empty());

        if(this->ustr.isInline() && other.ustr.isInline()) {
            if(this->ustr.inlinestr.data[0] + other.ustr.inlinestr.data[0] <= StrRootInlineContent::STR_MAX_SIZE) {
                return XString{StrRootInlineContent{this->ustr.inlinestr, other.ustr.inlinestr}};
            }
            else {
                static_assert(StrRootInlineContent::STR_MAX_SIZE * 2 <= StrRootTreeContent::STR_MAX_LEAF_SIZE, "If this changes then we need more complex logic like in list append");
                
                return XString{StrRootTreeContent{PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::mkinitial_append(this->ustr.inlinestr.data.begin() + 1, this->ustr.inlinestr.data.begin() + 1 + this->ustr.inlinestr.data[0], (const char32_t*)other.ustr.inlinestr.data.begin() + 1, (const char32_t*)other.ustr.inlinestr.data.begin() + 1 + other.ustr.inlinestr.data[0])}};
            }
        }
        else {
            PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING> lnode{};
            if(this->ustr.isInline()) {
                lnode = PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::mkinitial(this->ustr.inlinestr.data.begin() + 1, this->ustr.inlinestr.data.begin() + 1 + this->ustr.inlinestr.data[0]);
            }
            else {
                lnode = this->ustr.treestr.postree;
            }

            PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING> rnode{};
            if(other.ustr.isInline()) {
                rnode = PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::mkinitial(other.ustr.inlinestr.data.begin() + 1, other.ustr.inlinestr.data.begin() + 1 + other.ustr.inlinestr.data[0]);
            }
            else {
                rnode = other.ustr.treestr.postree;
            }

            return XString{StrRootTreeContent{PosRBTree<char32_t, StrRootTreeContent::STR_MAX_LEAF_SIZE, WELL_KNOWN_TYPE_ID_STRING>::append(lnode, rnode)}};
        }
    }

    XString XString::trim(XBool front, XBool back) const
    {
        if(this->empty()) {
            return XString{};
        }

        auto start = this->begin();
        auto end = this->end();

        if((bool)front) {
            while(start != end && isTrimableWhitespace(*start)) {
                ++start;
            }
        }

        if(start == end) {
            return XString{};
        }

        if((bool)back) {
            --end;
            while(start != end && isTrimableWhitespace(*end)) {
                --end;
            }

            if(!isTrimableWhitespace(*end)) {
                ++end;
            }
        }

        if(start == end) {
            return XString{};
        }

        if(start == this->begin() && end == this->end()) {
            return *this;
        }
        else {
            //TODO: this is expensive -- we want to 1) keep track of deleted whitespace and subtract here 2) implement an string split/slice so this is at least log time (NOT O(N))
            return XString::mk(start, end, std::distance(start, end));
        }
    }

    void jsonParseToBSQ_FString(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        assert(false); // Not Implemented: jsonParseToBSQ_FString
    }

    void parseToBSQ_FString(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        assert(false); // Not Implemented: parseToBSQ_FString
    }

    json bsqToJSON_FString(const TypeInfo* tinfo, const void* valptr)
    {
        assert(false); // Not Implemented: bsqToJSON_FString
    }

    void bsqToBAPI_FString(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        assert(false); // Not Implemented: bsqToBAPI_FString
    }

    void displayValue_FString(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        assert(false); // Not Implemented: displayValue_FString
    }

    void jsonParseToBSQ_Regex(const TypeInfo* tinfo, const json& j, void* resptr)
    {
        assert(false); // Not Implemented: jsonParseToBSQ_Regex
    }

    void parseToBSQ_Regex(const TypeInfo* tinfo, BAPILexer* lexer, void* resptr)
    {
        assert(false); // Not Implemented: parseToBSQ_Regex
    }

    json bsqToJSON_Regex(const TypeInfo* tinfo, const void* valptr)
    {
        assert(false); // Not Implemented: bsqToJSON_Regex
    }

    void bsqToBAPI_Regex(const TypeInfo* tinfo, const void* valptr, BSQStreamingBuilder* builder)
    {
        assert(false); // Not Implemented: bsqToBAPI_Regex
    }

    void displayValue_Regex(const TypeInfo* tinfo, const void* valptr, std::ostream& os, std::optional<std::string> indent)
    {
        assert(false); // Not Implemented: displayValue_Regex
    }
}
