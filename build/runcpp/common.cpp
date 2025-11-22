#include "common.h"

namespace Core
{
    namespace ᐸRuntimeᐳ
    {
        thread_local ThreadLocalInfo tl_info;

        void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message)
        {
            ᐸRuntimeᐳ::tl_info.pending_error = { file, line, kerror, tag, message }; 
            std::longjmp(ᐸRuntimeᐳ::tl_info.error_handler.back(), 11);
        }
    }
}
