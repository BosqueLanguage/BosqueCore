#include "taskinfo.h"

namespace ᐸRuntimeᐳ
{
    void TaskInfo::bapiParseIntoBSQ(bool sloppyinputs, const std::list<uint8_t*>& iobuffs, size_t totalbytes, uint32_t bsqid, void* outvalue)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(bsqid);

        BAPILexer lexer(IOBufferIterator::initializeBegin(iobuffs.cbegin(), totalbytes), IOBufferIterator::initializeEnd(iobuffs.cend(), totalbytes), sloppyinputs);
        lexer.initialize();
        
        ofinfo->opdispatch.parseToBSQFp(ofinfo, &lexer, outvalue);

        bool allconsumed = lexer.allInputConsumed();
        bsq_validate(allconsumed, "BAPI -> BSQ", 0, nullptr, "Not all input was consumed during BAPI -> BSQ parsing");
    }

    size_t TaskInfo::bsqEmitIntoBAPI(bool allowsensitive, uint32_t bsqid, const void* value, std::list<uint8_t*>& iobuffs)
    {
        const TypeInfo* ofinfo = TypeInfo::getTypeInfoForID(bsqid);

        IOBufferStreamingBuilder builder(allowsensitive);
        ofinfo->opdispatch.bsqToBAPIFp(ofinfo, value, &builder);

        return builder.finalize(iobuffs);
    }
}
