#include "taskinfo.h"

namespace ᐸRuntimeᐳ
{
    boost::uuids::time_generator_v7 g_task_uuidv7_id_generator{};
        
    TaskInfoWorkItemData::TaskInfoWorkItemData(std::initializer_list<std::pair<void*, const TypeInfo*>> args) : argc(args.size()), argv(nullptr), types(nullptr), data(nullptr)
    {
        size_t datasize = 0;
        for(auto iter = args.begin(); iter != args.end(); ++iter) {
            datasize += iter->second->dynamicReprSize();
        }

        this->argv = (void**)malloc(sizeof(void*) * argc);
        this->types = (const TypeInfo**)malloc(sizeof(const TypeInfo*) * argc);
        this->data = (uint8_t*)malloc(datasize);

        size_t datapos = 0;
        size_t cpos = 0;
        for(auto iter = args.begin(); iter != args.end(); ++iter) {
            this->types[cpos] = iter->second;
            this->argv[cpos] = iter->first;
            iter->second->dynamicReprCopy(this->data + datapos, iter->first);

            datapos += iter->second->dynamicReprSize();
            cpos++;
        }
    }

    TaskInfoWorkItemData::~TaskInfoWorkItemData()
    {
        free(this->argv);
        free(this->types);
        free(this->data);
    }

    TaskInfoWorkItemData::TaskInfoWorkItemData(TaskInfoWorkItemData&& other) : argc(other.argc), argv(other.argv), types(other.types), data(other.data)
    {
        other.argc = 0;
        other.argv = nullptr;
        other.types = nullptr;
        other.data = nullptr;
    }

    TaskInfoWorkItemData& TaskInfoWorkItemData::operator=(TaskInfoWorkItemData&& other)
    {
        if(this != &other)
        {
            free(this->argv);
            free(this->types);
            free(this->data);

            this->argc = other.argc;
            this->argv = other.argv;
            this->types = other.types;
            this->data = other.data;

            other.argc = 0;
            other.argv = nullptr;
            other.types = nullptr;
            other.data = nullptr;
        }
        
        return *this;
    }

    XUUIDv7 TaskInfo::generateFreshTaskId()
    {
        auto id = g_task_uuidv7_id_generator();
        return XUUIDv7::from_bytes(id.data);
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

    void TaskInfo::startStdExec()
    {
        //atomic transitions here!!!!
        assert(this->tstatus == TaskInfoRunStatus::Pending);
        xxxx;

        this->runStdExec();
    }

    void TaskInfo::startIOExec()
    {
        xxxx;
    }

    void TaskInfo::runStdExec()
    {
        xxxx;
    }

    void TaskInfo::runOnCompletionExec()
    {
        assert(false); //TODO
    }

    void TaskInfo::runOnCancelledExec()
    {
        assert(false); //TODO
    }

    void TaskInfo::runOnErrorExec()
    {
        assert(false); //TODO
    }
}
