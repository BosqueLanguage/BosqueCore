#include "common.h"
#include "runtime/taskinfo.h"

namespace ᐸRuntimeᐳ
{
    thread_local BosqueThreadLocalInfo tl_bosque_info;

    void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message)
    {
        ᐸRuntimeᐳ::tl_bosque_info.current_task->pending_error = { file, line, kerror, tag, message }; 
        std::longjmp(ᐸRuntimeᐳ::tl_bosque_info.current_task->error_handler, 11);
    }
}
