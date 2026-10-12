#include "taskinfo.h"

namespace ᐸRuntimeᐳ
{
    //TODO: this should be a 7 when we update the version of boost
    boost::uuids::random_generator g_task_uuidv4_id_generator{};
        
    TaskInfoWorkItemArgs::TaskInfoWorkItemArgs(std::initializer_list<std::tuple<void*, const TypeInfo*>> args) : argc(args.size()), argv(nullptr), types(nullptr), data(nullptr)
    {
        size_t datasize = 0;
        for(auto iter = args.begin(); iter != args.end(); ++iter) {
            auto tinfo = std::get<1>(*iter);
            datasize += (tinfo->tag == LayoutTag::Ref) ? sizeof(void*) : tinfo->bytesize;
        }

        this->argv = (void**)malloc(sizeof(void*) * argc);
        this->types = (const TypeInfo**)malloc(sizeof(const TypeInfo*) * argc);
        this->data = (uint8_t*)malloc(datasize);

        size_t slotpos = 0;
        for(auto iter = args.begin(); iter != args.end(); ++iter) {
            auto tinfo = std::get<1>(*iter);
            this->types[iter - args.begin()] = tinfo;
            this->argv[iter - args.begin()] = std::get<0>(*iter);

            if(tinfo->tag == LayoutTag::Ref) {
                ((void**)this->data)[slotpos] = std::get<0>(*iter);
                slotpos++;
            }
            else {
                size_t csize = tinfo->bytesize;
                memcpy(((void**)this->data) + slotpos, std::get<0>(*iter), csize);
                slotpos += csize;
            }
        }
    }

    TaskInfoWorkItemArgs::~TaskInfoWorkItemArgs()
    {
        free(this->argv);
        free(this->types);
        free(this->data);
    }

    XUUIDv4 TaskInfo::generateFreshTaskId()
    {
        auto id = g_task_uuidv4_id_generator();
        return XUUIDv4::from_bytes(id.data);
    }

    void TaskInfo::loadEnvVars(std::initializer_list<const char*> reqvars)
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
