#pragma once

#include "../common.h"
#include "../core/strings.h"

//
//TODO: need to add support for GC to load the implicit roots from the task info
//

namespace ᐸTaskRuntimeᐳ
{
    class TaskEnvironmentEntry
    {
    public:
        Core::CString key;

        const Core::ᐸRuntimeᐳ::TypeInfoBase* typeinfo;
        void* value; //Env creation is scoped so we can just store a pointer to the value on the stack/heap here

        constexpr TaskEnvironmentEntry() noexcept : key(), typeinfo(nullptr), value(nullptr) {}
        constexpr TaskEnvironmentEntry(const Core::CString& k, const Core::ᐸRuntimeᐳ::TypeInfoBase* ti, void* v) noexcept : key(k), typeinfo(ti), value(v) {}
        constexpr TaskEnvironmentEntry(const TaskEnvironmentEntry& other) noexcept = default;
    };

    class TaskEnvironment
    {
    public:
        std::list<TaskEnvironmentEntry> tenv;

        TaskEnvironment() noexcept : tenv() {}
        TaskEnvironment(const TaskEnvironment& other) noexcept = default;

        void setEntry(const Core::CString& key, const Core::ᐸRuntimeᐳ::TypeInfoBase* typeinfo, void* value) noexcept
        {
            this->tenv.emplace_back(key, typeinfo, value);
        }

        xxxx;
    };

    class TaskInfo
    {
    public:
        uint64_t taskId;
        TaskInfo* parentTask; //null for a root task
        uint32_t priority;
        uint32_t state;

        constexpr TaskInfo() noexcept : taskId(0), parentTask(nullptr), priority(0), state(0) {}
        constexpr TaskInfo(uint64_t tId, TaskInfo* pTask, uint32_t prio, uint32_t st) noexcept : taskId(tId), parentTask(pTask), priority(prio), state(st) {}
        constexpr TaskInfo(const TaskInfo &other) noexcept = default;
    };
}
