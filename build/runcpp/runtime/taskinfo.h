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

    class TaskInfoWorkItemArgs
    {
    public:
        size_t argc;
        void** argv;
        const TypeInfo** types;
        uint8_t* data;

        TaskInfoWorkItemArgs() : argc(0), argv(nullptr), types(nullptr), data(nullptr) {}
        TaskInfoWorkItemArgs(const TaskInfoWorkItemArgs& other) : argc(other.argc), argv(other.argv), types(other.types), data(other.data) {}
        
        TaskInfoWorkItemArgs(std::initializer_list<std::tuple<void*, const TypeInfo*>> args);
        ~TaskInfoWorkItemArgs();
    };

    class TaskInfoWorkItemResults
    {
    public:
        size_t argc;
        void** argv;
        const TypeInfo** types;
        uint8_t* data;

        TaskInfoWorkItemResults() : argc(0), argv(nullptr), types(nullptr), data(nullptr) {}
        TaskInfoWorkItemResults(const TaskInfoWorkItemResults& other) : argc(other.argc), argv(other.argv), types(other.types), data(other.data) {}
        
        TaskInfoWorkItemResults(size_t argc, std::initializer_list<std::tuple<void*, const TypeInfo*>> args) : argc(argc), argv(nullptr), types(nullptr), data(data) {}
        
        ~TaskInfoWorkItemResults() {}
    };

    class TaskInfoWorkItem
    {
    public:
        
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
        boost::uuids::random_generator uuidv4_generator;
        XUUIDv4 taskid; //TODO: this should be a 7 when we update the version of boost

        TaskPriority priority;
        TaskEnvironment environment;

        const TaskInfo* parent;
        std::list<TaskInfo*> children;

        std::jmp_buf* error_handler;
        std::optional<ErrorInfo> pending_error;

        TaskInfo() : uuidv4_generator(), taskid(XUUIDv4::nil()), priority(), environment(), parent(nullptr), error_handler(nullptr), pending_error() {}
        TaskInfo(const XUUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : taskid(tId), priority(prio), environment(), parent(pTask), error_handler(nullptr), pending_error() {}

        //Generate UUID for a task
        static XUUIDv4 generateFreshTaskId();

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
    };
}
