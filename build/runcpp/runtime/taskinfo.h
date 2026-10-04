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

        const TypeInfo* typeinfo; //typeinfo of U
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

    class TaskInfo
    {
    private:
        static void bapiParseIntoBSQ(bool sloppyinputs, const std::list<uint8_t*>& iobuffs, size_t totalbytes, uint32_t bsqid, void* outvalue);
        static size_t bsqEmitIntoBAPI(bool allowsensitive, uint32_t bsqid, const void* value, std::list<uint8_t*>& iobuffs);

    public:
        boost::uuids::random_generator uuidv4_generator;
        XUUIDv4 taskid;

        const TaskInfo* parent;
        TaskPriority priority;

        std::jmp_buf error_handler;
        std::optional<ErrorInfo> pending_error;

        TaskInfo() : uuidv4_generator(), taskid(XUUIDv4::nil()), parent(nullptr), priority(), error_handler(), pending_error() {}
        TaskInfo(const XUUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : taskid(tId), parent(pTask), priority(prio), error_handler(), pending_error() {}

        //Generate UUID for a task
        static XUUIDv4 generateFreshTaskId();

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

    class TaskInfoRepr : public TaskInfo
    {
    public:        
        TaskEnvironment environment;

        TaskInfoRepr(const XUUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : TaskInfo(tId, pTask, prio), environment() {}

        void loadEnvVars(std::initializer_list<const char*> reqvars);

        static TaskInfoRepr* asRepr(TaskInfo* current_task)
        {
            return static_cast<TaskInfoRepr*>(current_task);
        }
    };
}
