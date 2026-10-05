#include "taskinfo.h"

namespace ᐸRuntimeᐳ
{
    boost::uuids::random_generator g_task_uuidv4_id_generator{};
        
    XUUIDv4 TaskInfo::generateFreshTaskId()
    {
        auto id = g_task_uuidv4_id_generator();
        return XUUIDv4::from_bytes(id.data);
    }

    void TaskInfoRepr::loadEnvVars(std::initializer_list<const char*> reqvars)
    {
        for(auto iter = reqvars.begin(); iter != reqvars.end(); ++iter)
        {
            const char* ename = *iter;
            const char* evalue = std::getenv(ename);

            bsq_validate(evalue != nullptr, "Environment variable not found", 0, nullptr, ename);

            std::string sname(ename);
            std::string svalue(evalue);

            this->environment.setStartupEntry(std::move(sname), &g_typeinfo_CString, std::move(svalue));
        }
    }

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
