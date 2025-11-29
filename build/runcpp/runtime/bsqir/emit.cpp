#include "emit.h"


namespace ᐸRuntimeᐳ
{
    void BSQEmitBufferMgr::prepForEmit()
    {
        this->cpos = nullptr;
        this->epos = nullptr;
        this->bytes = 0;
        this->indentlevel = 0;
        this->buffers.clear();
    }
        
        void write(char c);
        void write(const char* str);
        void writef(const char* fmt, ...);

        std::list<BSQIOBuffer> completeEmit();
}