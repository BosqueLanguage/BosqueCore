#pragma once

#include "../common.h"

#include "../core/bsqtype.h"
#include "../core/uuids.h"
#include "../core/strings.h"

#include "./bsqir/parser.h"
#include "./bsqir/emit.h"

namespace ᐸRuntimeᐳ
{
    template<ConceptUnionRepr U>
    class TaskEnvironmentEntry
    {
    public:
        //Make sure to put key and value in special roots list for GC
        XCString key;

        const TypeInfo* typeinfo; //typeinfo of U
        U value;

        constexpr TaskEnvironmentEntry() : key(), typeinfo(nullptr), value(nullptr) {}
        constexpr TaskEnvironmentEntry(const XCString& k, const TypeInfo* ti, const U& u) : key(k), typeinfo(ti), value(u) {}
        constexpr TaskEnvironmentEntry(const TaskEnvironmentEntry& other) = default;
    };

    template<ConceptUnionRepr U>
    class TaskEnvironment
    {
    public:
        std::list<TaskEnvironmentEntry<U>> tenv;

        TaskEnvironment() : tenv() {}
        TaskEnvironment(const TaskEnvironment& other) = default;

        bool has(const XCString& key)
        {
            return std::find(this->tenv.begin(), this->tenv.end(), key) != this->tenv.end();
        }

        void setEntry(const XCString& key, const TypeInfo* typeinfo, const U& value)
        {
            this->tenv.emplace_front(key, typeinfo, value);
        }

        std::list<TaskEnvironmentEntry<U>>::iterator get(const XCString& key)
        {
            return std::find(this->tenv.begin(), this->tenv.end(), key);
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
    public:
        XUUIDv4 taskid;

        const TaskInfo* parent;
        TaskPriority priority;

        BSQONParser bsqparser;
        BSQONEmitter bsqemitter;

        std::jmp_buf error_handler;
        std::optional<ErrorInfo> pending_error;

        TaskInfo() : taskid(), parent(nullptr), priority(), bsqparser(), bsqemitter(), error_handler(), pending_error() {}
        TaskInfo(const XUUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : taskid(tId), parent(pTask), priority(prio), bsqparser(), bsqemitter(), error_handler(), pending_error() {}
    };

    template<ConceptUnionRepr U> //U must be a union of all possible types stored in the environment
    class TaskInfoRepr : public TaskInfo
    {
    public:        
        TaskEnvironment<U> environment;

        TaskInfoRepr() : TaskInfo(), environment() {}
        TaskInfoRepr(const XUUIDv4& tId, const TaskInfo* pTask, TaskPriority prio) : TaskInfo(tId, pTask, prio), environment() {}

        TaskInfoRepr* asRepr(TaskInfo* current_task)
        {
            return static_cast<TaskInfoRepr<U>*>(current_task);
        }
    };
}
