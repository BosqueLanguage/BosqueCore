#define verifyTest() do{ collect(); 𝐚𝐬𝐬𝐞𝐫𝐭(gtl_info.total_live_bytes == 0); }while(0)

__CoreCpp::Int basicTreeTest_1()
{
    [[maybe_unused]] Main::BasicTree t = Main::makeTree(1_n, 0_n);
    [[maybe_unused]] Main::BasicTree tt = Main::makeTree(1_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}

__CoreCpp::Int basicTreeTest_3()
{
    [[maybe_unused]] Main::BasicTree t = Main::makeTree(3_n, 0_n);
    [[maybe_unused]] Main::BasicTree tt = Main::makeTree(3_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}

__CoreCpp::Int basicTreeTest_6()
{
    [[maybe_unused]] Main::BasicTree t = Main::makeTree(6_n, 0_n);
    [[maybe_unused]] Main::BasicTree tt = Main::makeTree(6_n, 0_n);

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.total_live_bytes);

    return 1_i;
}
