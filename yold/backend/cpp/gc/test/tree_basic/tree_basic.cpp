#define verifyTest() do{ collect(); 𝐚𝐬𝐬𝐞𝐫𝐭(gtl_info.mstats.total_live_bytes == 0); }while(0)

__CoreCpp::Int basicTreeTest_1()
{
    garray[0] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(1_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int basicTreeTest_3()
{
    garray[0] = Main::accessNode(Main::makeTree(3_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(3_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int basicTreeTest_6()
{
    garray[0] = Main::accessNode(Main::makeTree(6_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(6_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int basicTreeTestMulti_1()
{
    garray[0] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[2] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[3] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[4] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[5] = Main::accessNode(Main::makeTree(1_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;
    garray[2] = nullptr;
    garray[3] = nullptr;
    garray[4] = nullptr;
    garray[5] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int basicTreeTestMulti_3()
{
    garray[0] = Main::accessNode(Main::makeTree(3_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(3_n, 0_n));
    garray[2] = Main::accessNode(Main::makeTree(3_n, 0_n));
    garray[3] = Main::accessNode(Main::makeTree(3_n, 0_n));
    garray[4] = Main::accessNode(Main::makeTree(3_n, 0_n));
    garray[5] = Main::accessNode(Main::makeTree(3_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;
    garray[2] = nullptr;
    garray[3] = nullptr;
    garray[4] = nullptr;
    garray[5] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int basicTreeTestMulti_6()
{
    garray[0] = Main::accessNode(Main::makeTree(6_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(6_n, 0_n));
    garray[2] = Main::accessNode(Main::makeTree(6_n, 0_n));
    garray[3] = Main::accessNode(Main::makeTree(6_n, 0_n));
    garray[4] = Main::accessNode(Main::makeTree(6_n, 0_n));
    garray[5] = Main::accessNode(Main::makeTree(6_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;
    garray[2] = nullptr;
    garray[3] = nullptr;
    garray[4] = nullptr;
    garray[5] = nullptr;

    verifyTest();

    return 1_i;
}

// Wide tree tests with Main:: namespace
__CoreCpp::Int wideTreeTest_1()
{
    garray[0] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(1_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int wideTreeTest_2()
{
    garray[0] = Main::accessNode(Main::makeTree(2_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(2_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int wideTreeTestMulti_1()
{
    garray[0] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[2] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[3] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[4] = Main::accessNode(Main::makeTree(1_n, 0_n));
    garray[5] = Main::accessNode(Main::makeTree(1_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();
    
    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;
    garray[2] = nullptr;
    garray[3] = nullptr;
    garray[4] = nullptr;
    garray[5] = nullptr;

    verifyTest();

    return 1_i;
}

__CoreCpp::Int wideTreeTestMulti_2()
{
    garray[0] = Main::accessNode(Main::makeTree(2_n, 0_n));
    garray[1] = Main::accessNode(Main::makeTree(2_n, 0_n));
    garray[2] = Main::accessNode(Main::makeTree(2_n, 0_n));
    garray[3] = Main::accessNode(Main::makeTree(2_n, 0_n));
    garray[4] = Main::accessNode(Main::makeTree(2_n, 0_n));
    garray[5] = Main::accessNode(Main::makeTree(2_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.mstats.total_live_bytes;
    collect();
    
    𝐚𝐬𝐬𝐞𝐫𝐭(init_bytes == gtl_info.mstats.total_live_bytes && gtl_info.mstats.total_live_bytes != 0);

    garray[0] = nullptr;
    garray[1] = nullptr;
    garray[2] = nullptr;
    garray[3] = nullptr;
    garray[4] = nullptr;
    garray[5] = nullptr;

    verifyTest();

    return 1_i;
}