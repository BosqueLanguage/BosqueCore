#include "emit.hpp"

//CODE

// Prevents longjmp clobbering rbp in the gc
int wrap_setjmp() 
{
    if(setjmp(__CoreCpp::info.error_handler)) { 
        // We may want to pass in some source info here and perhaps expression causing failure
        std::cout << "Assertion failed! Or perhaps over/underflow?" << std::endl;
        g_decs_prcsr.stop();
        return EXIT_FAILURE;
    }

    // Calling our emitted main is hardcoded for now
    __CoreCpp::MainType ret = Main::main();
    std::cout << __CoreCpp::to_string(ret) << std::endl;

    // Ensure decs thread stops waiting
    g_decs_prcsr.stop();

    return 0;
}

int main() 
{
#ifdef BSQ_GC_TESTING
    gtl_info.initializeGC(allocs, sizeof(allocs) / sizeof(allocs[0]), true 
		, collect);
#else
    gtl_info.initializeGC(allocs, sizeof(allocs) / sizeof(allocs[0]), false 
		, collect);
#endif
    
	return wrap_setjmp();
}
