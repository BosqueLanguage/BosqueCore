#pragma once

#include "../common.h"

#include "../core/bsqtype.h"
#include "../core/uuids.h"
#include "../core/strings.h"

namespace ᐸRuntimeᐳ
{
    //
    //TODO: we are making the env be only holding std::string keys/values for now -- later make them CString and any value 
    //      need to make the GC aware of this at root walk time
    //

    class TaskEnvironmentEntry
    {
    public:
        //Make sure to put key and value in special roots list for GC
        std::string key;

        const TypeInfo* typeinfo;
        std::string value;

        constexpr TaskEnvironmentEntry() : key(), typeinfo(nullptr), value() {}
        constexpr TaskEnvironmentEntry(const std::string& k, const TypeInfo* ti, const std::string& v) : key(k), typeinfo(ti), value(v) {}
        constexpr TaskEnvironmentEntry(const TaskEnvironmentEntry& other) = default;
    };

    class TaskEnvironment
    {
    public:
        std::list<TaskEnvironmentEntry> tenv;

        TaskEnvironment() : tenv() {}
        TaskEnvironment(const TaskEnvironment& other) = default;

        std::string toByteBuffer(const XCString& cstr)
        {
            std::string res{};
            res.reserve(cstr.size());

            for(auto iter = cstr.begin(); iter != cstr.end(); ++iter) {
                res.push_back((char)(*iter));
            }

            return res;
        }

        bool has(const XCString& key)
        {
            auto kkey = this->toByteBuffer(key);
            return std::find_if(this->tenv.begin(), this->tenv.end(), [&](const TaskEnvironmentEntry& entry) {
                return entry.key == kkey;
            }) != this->tenv.end();
        }

        void setEntry(const XCString& key, const TypeInfo* typeinfo, const XCString& value)
        {
            auto kkey = this->toByteBuffer(key);
            auto vvalue = this->toByteBuffer(value);

            this->tenv.emplace_front(kkey, typeinfo, vvalue);
        }

        void setStartupEntry(const std::string&& key, const TypeInfo* typeinfo, const std::string&& value)
        {
            this->tenv.emplace_front(std::move(key), typeinfo, std::move(value));
        }

        std::list<TaskEnvironmentEntry>::iterator get(const XCString& key)
        {
            auto kkey = this->toByteBuffer(key);
            return std::find_if(this->tenv.begin(), this->tenv.end(), [&](const TaskEnvironmentEntry& entry) {
                return entry.key == kkey;
            });
        }
    };

    class TaskPriority
    {
    public:
        uint64_t level;
        const char* description;

        constexpr TaskPriority() : level(50), description("standard") {}
        constexpr TaskPriority(uint64_t lvl, const char* desc) : level(lvl), description(desc) {}
        constexpr TaskPriority(const TaskPriority& other) = default;

        friend constexpr bool operator<(const TaskPriority &lhs, const TaskPriority &rhs) { return lhs.level < rhs.level; }
        friend constexpr bool operator==(const TaskPriority &lhs, const TaskPriority &rhs) { return lhs.level == rhs.level; }
        friend constexpr bool operator>(const TaskPriority &lhs, const TaskPriority &rhs) { return rhs.level < lhs.level; }
        friend constexpr bool operator!=(const TaskPriority &lhs, const TaskPriority &rhs) { return !(lhs.level == rhs.level); }
        friend constexpr bool operator<=(const TaskPriority &lhs, const TaskPriority &rhs) { return !(lhs.level > rhs.level); }
        friend constexpr bool operator>=(const TaskPriority &lhs, const TaskPriority &rhs) { return !(lhs.level < rhs.level); } 
    
        
        constexpr static TaskPriority pimmediate() { return TaskPriority(100, "immediate"); }
        constexpr static TaskPriority ppriority() { return TaskPriority(80, "priority"); }
        constexpr static TaskPriority pstandard() { return TaskPriority(50, "standard"); }
        constexpr static TaskPriority plongrun() { return TaskPriority(30, "longrun"); }
        constexpr static TaskPriority pbackground() { return TaskPriority(10, "background"); }
        constexpr static TaskPriority poptional() { return TaskPriority(0, "optional"); }
    };

    class TaskInfoWorkItemData
    {
    public:
        size_t argc;
        void** argv;
        const TypeInfo** types;
        uint8_t* data;

        TaskInfoWorkItemData() : argc(0), argv(nullptr), types(nullptr), data(nullptr) {}
        TaskInfoWorkItemData(const TaskInfoWorkItemData& other) = delete;
        TaskInfoWorkItemData(TaskInfoWorkItemData&& other);
        
        TaskInfoWorkItemData(std::initializer_list<std::pair<void*, const TypeInfo*>> args);
        ~TaskInfoWorkItemData();

        TaskInfoWorkItemData& operator=(const TaskInfoWorkItemData& other) = delete;
        TaskInfoWorkItemData& operator=(TaskInfoWorkItemData&& other);
    };

    enum class TaskInfoWorkItemEarlyReturnFlag
    {
        None,     // If this work item should continue without any special handling
        Blocked,  // If the work item blocked on a child task (and this will be resumed later when it clears)
        Yield,    // If the work item yielded and we are going to move to completion
        Continue  // If the work item continued and we are going to dispatch on the new action
    };

    using TaskInfoWorkItemWorkFp = TaskInfoWorkItemEarlyReturnFlag(*)(TaskInfoWorkItemData*, TaskInfoWorkItemData*, TaskInfoWorkItemWorkFp*);

    class TaskInfoWorkItem
    {
    public:
        TaskInfoWorkItemData argvals;
        TaskInfoWorkItemData retvals;

        TaskInfoWorkItemWorkFp continuefp;

        TaskInfoWorkItem() = default;
        TaskInfoWorkItem(TaskInfoWorkItemWorkFp nextop, std::initializer_list<std::pair<void*, const TypeInfo*>> args) : argvals(args), retvals(), continuefp(nextop) {}
        ~TaskInfoWorkItem() = default;
    };

    enum class TaskInfoRunStatus
    {
        Pending, //This task has been created but not yet started -- can canceled trivially (as if it never existed) or run
        Running, //This task is currently running some work items (maybe io_uring IO)
        Canceled, //This task has been canceled but the cancelation has not been initiated yet
        Error, //This task has encountered an error but the handled has not been initiated yet
        RunningCompleteOp, //This task is running the completion operation
        RunningCanceledOp, //This task is running the cancelation operation
        RunningErroredOp, //This task is running the error handling operation
        Finished //This task has finished all work and is complete
    };

    //Info on if this task is hitting io_uring (true/false) and if so what IO resource it uses (so we can ballance IO scheduling if needed -- for now just hit it hard)
    enum class TaskIOInfo
    {
        CPU_ONLY, //This task is not performing any IO now
        //TODO: loopback ??
        LOCAL_STORAGE, //This task is performing IO on the local drive
        LOCAL_NETWORK_STORAGE, //This task is performing IO on a network drive (local network or datacenter)
        LOCAL_NETWORK_DB, //This task is performing IO on a DB (local network or datacenter)
        //TODO: remote storage and DB??
        HTTP //This task is performing IO via remote http
    };

    /**
     * A TaskInfo represents the a full logical task within the runtime system -- corresponding to a Task run, a API invoke, or an Agent invoke. It has a UUID to uniquely identify it and causally link it to parent/children.
     * Then we are going to run individual items of work associated with this task until it is complete.
     **/
    class TaskInfo
    {
    private:
        static void bapiParseIntoBSQ(bool sloppyinputs, const std::list<uint8_t*>& iobuffs, size_t totalbytes, uint32_t bsqid, void* outvalue);
        static size_t bsqEmitIntoBAPI(bool allowsensitive, uint32_t bsqid, const void* value, std::list<uint8_t*>& iobuffs);

    public:
        using RunIOFp = void(*)(TaskInfo*);
        using TaskInfoCompletionFp = void(*)(TaskInfo*);

        boost::uuids::random_generator uuidv4_generator;
        XUUIDv7 taskid;

        TaskPriority priority;
        TaskEnvironment environment;

        const TaskInfo* parent;
        std::list<TaskInfo*> children;

        TaskInfoRunStatus tstatus;
        TaskIOInfo iostatus;
        TaskInfoWorkItem workitem;
        RunIOFp iofp;
        TaskInfoCompletionFp completionfp;

        std::jmp_buf* error_handler;
        std::optional<ErrorInfo> pending_error;

        std::mutex state_guard; //TODO: in the future maybe we can make this atomic and CAS for better performance

        TaskInfo() : uuidv4_generator(), taskid(XUUIDv7::nil()), priority(), environment(), parent(nullptr), children(), tstatus(TaskInfoRunStatus::Pending), iostatus(TaskIOInfo::CPU_ONLY), workitem(), iofp(nullptr), completionfp(nullptr), error_handler(nullptr), pending_error(), state_guard() {}
        TaskInfo(const XUUIDv7& tId, const TaskInfo* pTask, TaskPriority prio, TaskInfoCompletionFp compfp, std::initializer_list<std::pair<void*, const TypeInfo*>> args) : taskid(tId), priority(prio), environment(), parent(pTask), children(), tstatus(TaskInfoRunStatus::Pending), iostatus(TaskIOInfo::CPU_ONLY), workitem(), iofp(nullptr), completionfp(compfp), error_handler(nullptr), pending_error(), state_guard() {}
        TaskInfo(const XUUIDv7& tId, const TaskInfo* pTask, TaskPriority prio, TaskInfoCompletionFp compfp, TaskIOInfo ioinfo, RunIOFp iofp, std::initializer_list<std::pair<void*, const TypeInfo*>> args) : taskid(tId), priority(prio), environment(), parent(pTask), children(), tstatus(TaskInfoRunStatus::Pending), iostatus(ioinfo), workitem(), iofp(iofp), completionfp(compfp), error_handler(nullptr), pending_error(), state_guard() {}
        ~TaskInfo() = default;

        //Generate UUID for a task
        static XUUIDv7 generateFreshTaskId();

        void loadEnvVars(std::initializer_list<const char*> reqvars);

        //Generating user requested UUID values
        XUUIDv4 generateUUIDv4()
        {
            auto uuid = this->uuidv4_generator();
            return XUUIDv4::from_bytes(uuid.data);
        }

        template<typename T>
        static void bapiParseIntoBSQ(bool relaxedparse, const std::list<uint8_t*>& iobuffs, size_t totalbytes, uint32_t bsqid, T& outvalue)
        {
            return bapiParseIntoBSQ(relaxedparse, iobuffs, totalbytes, bsqid, static_cast<void*>(&outvalue));
        }

        template<typename T>
        static size_t bsqEmitIntoBAPI(bool allowsensitive, uint32_t bsqid, const T& value, std::list<uint8_t*>& iobuffs)
        {
            return bsqEmitIntoBAPI(allowsensitive, bsqid, static_cast<const void*>(&value), iobuffs);
        }

        void startStdExec();
        void startIOExec();

        void runStdExec();

        void runOnCompletionExec();
        void runOnCancelledExec();
        void runOnErrorExec();
    };
}
