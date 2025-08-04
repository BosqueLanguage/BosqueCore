#define verifyTest() do{ collect(); 𝐚𝐬𝐬𝐞𝐫𝐭(gtl_info.total_live_bytes == 0); }while(0)

__CoreCpp::Int wideTreeTest_1()
{
    [[maybe_unused]] Main::WideTree t = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::WideTree tt = Main::makeTree(1_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}

__CoreCpp::Int wideTreeTest_2()
{
    [[maybe_unused]] Main::WideTree t = Main::makeTree(2_n, 0_n);
    [[maybe_unused]] Main::WideTree tt = Main::makeTree(2_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}

__CoreCpp::Int wideTreeTestMulti_1()
{
    [[maybe_unused]] Main::WideTree t1 = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::WideTree t2 = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::WideTree t3 = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::WideTree t4 = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::WideTree t5 = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::WideTree t6 = Main::makeTree(1_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}

__CoreCpp::Int wideTreeTestMulti_2()
{
    [[maybe_unused]] Main::WideTree t1 = Main::makeTree(2_n, 0_n);
    [[maybe_unused]] Main::WideTree t2 = Main::makeTree(2_n, 0_n);
    [[maybe_unused]] Main::WideTree t3 = Main::makeTree(2_n, 0_n);
    [[maybe_unused]] Main::WideTree t4 = Main::makeTree(2_n, 0_n);
    [[maybe_unused]] Main::WideTree t5 = Main::makeTree(2_n, 0_n);
    [[maybe_unused]] Main::WideTree t6 = Main::makeTree(2_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}