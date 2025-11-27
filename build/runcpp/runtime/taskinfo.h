#pragma once

#include "../common.h"
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

        const TypeInfoBase* typeinfo;
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

        void setEntry(const CString& key, const TypeInfoBase* typeinfo, void* value) noexcept
        {
            this->tenv.emplace_back(key, typeinfo, value);
        }

        std::list<TaskEnvironmentEntry<U>>::iterator tryGetEntry(const CString& key) noexcept
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
    
        constexpr static TaskPriority lnormal() noexcept { return TaskPriority(50, "normal"); }
        //TODO all the levels here
    };

    template<ConceptUnionRepr U> //U must be a union of all possible types stored in the environment
    class TaskInfo
    {
    public:
        const boost::uuids::uuid taskid;
        const TaskInfo* parent; //null for a root task
        TaskPriority priority;

        TaskInfo() noexcept : taskid(boost::uuids::nil_uuid()), parent(nullptr), priority() {}
        TaskInfo(const boost::uuids::uuid& tId, const TaskInfo* pTask, TaskPriority prio) noexcept : taskid(tId), parent(pTask), priority(prio) {}
    
        generate uuidv4() noexcept
        {
            static boost::uuids::random_generator uuidgen;
            return uuidgen();
        }
    };
}
