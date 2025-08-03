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

__CoreCpp::Int dropChildWideTreeTest()
{
    Main::Node* n = Main::accessNode(Main::makeTree(2_n, 0_n));

    collect();
    uint64_t init_bytes = gtl_info.total_live_bytes;

    n->n1 = WideTreeᘏdeadTree();
    n->n3 = WideTreeᘏdeadTree();
    n->n5 = WideTreeᘏdeadTree();
    n->n7 = WideTreeᘏdeadTree();
    n->n9 = WideTreeᘏdeadTree();
    n->n11 = WideTreeᘏdeadTree();

    uint64_t subtree_size = NodeType.type_size * 6;
    uint64_t expected_size = init_bytes - subtree_size;

    collect();

    𝐚𝐬𝐬𝐞𝐫𝐭(expected_size == gtl_info.total_live_bytes);

    return 1_i;
}