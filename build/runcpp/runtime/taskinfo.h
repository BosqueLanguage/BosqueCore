#pragma once

#include "../common.h"

#include "../core/bsqtype.h"
#include "../core/uuids.h"
#include "../core/strings.h"

namespace ᐸRuntimeᐳ
{
    template<ConceptUnionRepr U>
    class TaskEnvironmentEntry
    {
    public:
        //Make sure to put key and value in special roots list for GC
        CString key;

        const TypeInfoBase* typeinfo; //typeinfo of U
        U value;

        constexpr TaskEnvironmentEntry() : key(), typeinfo(nullptr), value(nullptr) {}
        constexpr TaskEnvironmentEntry(const CString& k, const TypeInfoBase* ti, const U& u) : key(k), typeinfo(ti), value(u) {}
        constexpr TaskEnvironmentEntry(const TaskEnvironmentEntry& other) = default;
    };

    template<ConceptUnionRepr U>
    class TaskEnvironment
    {
    public:
        std::list<TaskEnvironmentEntry<U>> tenv;

        TaskEnvironment() : tenv() {}
        TaskEnvironment(const TaskEnvironment& other) = default;

        bool has(const CString& key)
        {
            return std::find(this->tenv.begin(), this->tenv.end(), key) != this->tenv.end();
        }

        void setEntry(const CString& key, const TypeInfoBase* typeinfo, const U& value)
        {
            this->tenv.emplace_front(key, typeinfo, value);
        }

        std::list<TaskEnvironmentEntry<U>>::iterator get(const CString& key)
        {
            return std::find(this->tenv.begin(), this->tenv.end(), key);
        }
    };

    class TaskPriority
    {
    public:
        uint64_t level;
        const char* description;

        constexpr TaskPriority() : level(0), description("Normal") {}
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
        constexpr static TaskPriority pstd() { return TaskPriority(50, "std"); }
        constexpr static TaskPriority plongrun() { return TaskPriority(30, "longrun"); }
        constexpr static TaskPriority pbackground() { return TaskPriority(10, "background"); }
        constexpr static TaskPriority poptional() { return TaskPriority(0, "optional"); }
    };

    class TaskInfo
    {
    public:
        UUIDv4 taskid;
        const TaskInfo* parent;
        TaskPriority priority;

        std::jmp_buf error_handler;
        std::optional<ErrorInfo> pending_error;

        TaskInfo() : taskid(), parent(nullptr), priority(), error_handler(), pending_error() {}
        TaskInfo(const UUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : taskid(tId), parent(pTask), priority(prio), error_handler(), pending_error() {}
    };

    template<ConceptUnionRepr U> //U must be a union of all possible types stored in the environment
    class TaskInfoRepr : public TaskInfo
    {
    public:        
        TaskEnvironment<U> environment;

        TaskInfoRepr() : TaskInfo(), environment() {}
        TaskInfoRepr(const UUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : TaskInfo(tId, pTask, prio), environment() {}

        TaskInfoRepr* asRepr(TaskInfo* current_task)
        {
            return static_cast<TaskInfoRepr<U>*>(current_task);
        }
    };
}
