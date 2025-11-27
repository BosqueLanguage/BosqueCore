#pragma once

#include "../common.h"
#include "../bsqtype.h"
#include "../core/uuids.h"
#include "../core/strings.h"

//
//TODO: need to add support for GC to load the implicit roots from the task info
//

namespace ᐸRuntimeᐳ
{
    template<ConceptUnionRepr U>
    class TaskEnvironmentEntry
    {
    public:
        CString key;

        const TypeInfoBase* typeinfo; //typeinfo of U
        U value;

        constexpr TaskEnvironmentEntry() noexcept : key(), typeinfo(nullptr), value(nullptr) {}
        constexpr TaskEnvironmentEntry(const CString& k, const TypeInfoBase* ti, const U& u) noexcept : key(k), typeinfo(ti), value(v) {}
        constexpr TaskEnvironmentEntry(const TaskEnvironmentEntry& other) noexcept = default;
    };

    template<ConceptUnionRepr U>
    class TaskEnvironment
    {
    public:
        std::list<TaskEnvironmentEntry<U>> tenv;

        TaskEnvironment() noexcept : tenv() {}
        TaskEnvironment(const TaskEnvironment& other) noexcept = default;

        bool has(const CString& key) noexcept
        {
            return std::find(this->tenv.begin(), this->tenv.end(), key) != this->tenv.end();
        }

        void setEntry(const CString& key, const TypeInfoBase* typeinfo, void* value) noexcept
        {
            this->tenv.emplace_front(key, typeinfo, value);
        }

        std::list<TaskEnvironmentEntry<U>>::iterator get(const CString& key) noexcept
        {
            return std::find(this->tenv.begin(), this->tenv.end(), key);
        }
    };

    class TaskPriority
    {
    public:
        uint64_t level;
        const char* description;

        constexpr TaskPriority() noexcept : level(0), description("Normal") {}
        constexpr TaskPriority(uint64_t lvl, const char* desc) noexcept : level(lvl), description(desc) {}
        constexpr TaskPriority(const TaskPriority& other) noexcept = default;

        friend constexpr bool operator<(const TaskPriority &lhs, const TaskPriority &rhs) noexcept { return lhs.level < rhs.level; }
        friend constexpr bool operator==(const TaskPriority &lhs, const TaskPriority &rhs) noexcept { return lhs.level == rhs.level; }
        friend constexpr bool operator>(const TaskPriority &lhs, const TaskPriority &rhs) noexcept { return rhs.level < lhs.level; }
        friend constexpr bool operator!=(const TaskPriority &lhs, const TaskPriority &rhs) noexcept { return !(lhs.level == rhs.level); }
        friend constexpr bool operator<=(const TaskPriority &lhs, const TaskPriority &rhs) noexcept { return !(lhs.level > rhs.level); }
        friend constexpr bool operator>=(const TaskPriority &lhs, const TaskPriority &rhs) noexcept { return !(lhs.level < rhs.level); } 
    
        
        constexpr static TaskPriority pimmediate() noexcept { return TaskPriority(100, "immediate"); }
        constexpr static TaskPriority ppriority() noexcept { return TaskPriority(80, "priority"); }
        constexpr static TaskPriority pstd() noexcept { return TaskPriority(50, "std"); }
        constexpr static TaskPriority plongrun() noexcept { return TaskPriority(30, "longrun"); }
        constexpr static TaskPriority pbackground() noexcept { return TaskPriority(10, "background"); }
        constexpr static TaskPriority poptional() noexcept { return TaskPriority(0, "optional"); }
    };

    class TaskInfo
    {
    public:
        UUIDv4 taskid;
        const TaskInfo* parent;
        TaskPriority priority;

        std::jmp_buf error_handler;
        std::optional<ErrorInfo> pending_error;

        TaskInfo() noexcept : taskid(), parent(nullptr), priority(), error_handler(), pending_error() {}
        TaskInfo(const UUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) noexcept : taskid(tId), parent(pTask), priority(prio), error_handler(), pending_error() {}
    };

    template<ConceptUnionRepr U> //U must be a union of all possible types stored in the environment
    class TaskInfoRepr : public TaskInfo
    {
    public:        
        TaskEnvironment<U> environment;

        TaskInfoRepr() noexcept : TaskInfo(), environment() {}
        TaskInfoRepr(const UUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) noexcept : TaskInfo(tId, pTask, prio), environment() {}

        TaskInfoRepr* asRepr(TaskInfo* current_task) noexcept
        {
            return static_cast<TaskInfoRepr<U>*>(current_task);
        }
    };
}
