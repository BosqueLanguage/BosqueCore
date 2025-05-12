int main() {
    // Calling our emitted main is hardcoded for now
    auto bsq_main = Main::main();
    std::cout << bsq_main.get() << std::endl;

    return 0;
}