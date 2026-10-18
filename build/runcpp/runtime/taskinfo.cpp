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
        {
            std::lock_guard<std::mutex> guard(this->state_guard);

            assert(this->tstatus == TaskInfoRunStatus::Pending);
            this->tstatus = TaskInfoRunStatus::Running;
        }
        
        this->runStdExec();
    }

    void TaskInfo::startIOExec()
    {
        std::lock_guard<std::mutex> guard(this->state_guard);

        assert(this->tstatus == TaskInfoRunStatus::Pending);
        this->tstatus = TaskInfoRunStatus::Running;

        this->iofp(this);
    }

    void TaskInfo::runStdExec()
    {
        while(true) {
            //check if this has status changed to something other than Running and dispatch accordingly
            const TaskInfoRunStatus currentStatus = this->tstatus;
            if(this->workitem.isActionSafepoint) {
                if(currentStatus == TaskInfoRunStatus::Canceled || currentStatus == TaskInfoRunStatus::Error) {
                    break;
                }
            }

            //run the next step of the standard execution
            auto [flag, nextop] = this->workitem.continuefp(&this->workitem.argvals, &this->workitem.retvals);
            if(flag == TaskInfoWorkItemEarlyReturnFlag::Return) {
                xxxx; //TODO: we need a pending action workitem call stack to pop from here
            }

            if(flag != TaskInfoWorkItemEarlyReturnFlag::None) {
                assert(false); //TODO: handle special continue/return cases
            }

            //update the task status based on the execution result
            this->workitem.argvals = std::move(this->workitem.retvals);
            this->workitem.continuefp = (TaskInfoWorkItemWorkFp)nextop;
        }

        //dispatch based on the final status of the task
        assert(false); 
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
