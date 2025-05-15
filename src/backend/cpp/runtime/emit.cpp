int main() {
    if(setjmp(__CoreCpp::info.error_handler)) {
        std::cout << "Over/underflow detected!" << std::endl;
        return EXIT_FAILURE;
    }

    // Calling our emitted main is hardcoded for now
    Main::main();

    // We may want some way to convert what Main::main spits out into 
    // a string and write to cout

    return 0;
}