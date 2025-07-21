int main() {
    if(setjmp(__CoreCpp::info.error_handler)) { 
        // We may want to pass in some source info here and perhaps expression causing failure
        std::cout << "Assertion failed! Or perhaps over/underflow?" << std::endl;
        return EXIT_FAILURE;
    }
    
    std::cout << Main::main() << std::endl;

    return 0;
}