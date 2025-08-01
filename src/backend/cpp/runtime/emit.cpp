#include "emit.hpp"

//CODE

// Prevents longjmp clobbering rbp in the gc
int wrap_setjmp() {
    if(setjmp(__CoreCpp::info.error_handler)) { 
        // We may want to pass in some source info here and perhaps expression causing failure
        std::cout << "Assertion failed! Or perhaps over/underflow?" << std::endl;
        return EXIT_FAILURE;
    }

    gtl_info.initializeGC<sizeof(allocs) / sizeof(allocs[0])>(allocs);

    // Calling our emitted main is hardcoded for now
    __CoreCpp::MainType ret = Main::main();
    std::cout << __CoreCpp::to_string(ret) << std::endl;

    return 0;
}

int main() {
    INIT_LOCKS();   
    InitBSQMemoryTheadLocalInfo();

    return wrap_setjmp();
}
