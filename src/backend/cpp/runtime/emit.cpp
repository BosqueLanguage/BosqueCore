int main() {
    if(setjmp(__CoreCpp::info.error_handler)) {
        std::cout << "Over/underflow detected!" << std::endl;
        return EXIT_FAILURE;
    }

    // Calling our emitted main is hardcoded for now
    __CoreCpp::MainType ret = Main::__main();
    std::cout << __CoreCpp::to_string(ret) << std::endl;

    return 0;
}