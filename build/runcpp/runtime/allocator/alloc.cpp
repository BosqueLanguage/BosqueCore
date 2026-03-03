#include "../../common.h"
#include "alloc.h"

namespace ᐸRuntimeᐳ
{
    thread_local AllocatorThreadLocalInfo tl_alloc_info;
    AllocatorGlobalInfo g_alloc_info;

    AllocatorThreadLocalInfo::~AllocatorThreadLocalInfo()
    {
        this->cleanup();
    }

    void AllocatorThreadLocalInfo::initialize(void** caller_rbp, void (*_collectfp)(), const std::map<uint32_t, GCAllocatorImpl*>& gcallocs)
    {
        this->collectfp = _collectfp;
        this->gcallocs = gcallocs;
    }
	
    void AllocatorThreadLocalInfo::cleanup()
    {
        for(auto iter = this->gcallocs.begin(); iter != this->gcallocs.end(); iter++) {
            iter->second->cleanup();
        }
    
        this->gcallocs.clear();
    }

    void collect()
    {
        ;
    }
}
