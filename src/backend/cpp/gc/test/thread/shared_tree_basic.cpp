#include <thread>

#define verifyTest(THD) \
do { \
	THD.join(); \
	collect(); \
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes == 0); \
}while(0)

__CoreCpp::Int sharedBasicTreeTest_1()
{
	void* root0 = Main::accessNode(Main::makeTree(1_n, 0_n));
	void* root1 = Main::accessNode(Main::makeTree(1_n, 0_n));
	gtl_info.thd_testing_data[0] = root0;
	gtl_info.thd_testing_data[1] = root1;
	collect();

	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes > 0);

	std::thread thd = std::thread([root0, root1]() {
		gtl_info.thd_testing_data[0] = root0;
		gtl_info.thd_testing_data[1] = root1;
    	initializeGC<sizeof(allocs) / sizeof(allocs[0])>(allocs, gtl_info);
		
		collect();

		MetaData* m0 = GC_GET_META_DATA_ADDR(root0);
		MetaData* m1 = GC_GET_META_DATA_ADDR(root1);
		𝐚𝐬𝐬𝐞𝐫𝐭(GC_THREAD_COUNT(m0) == 2 && GC_THREAD_COUNT(m1) == 2);

		// roots dropped during BSQMemoryTheadLocalInfo destruction
	});

	gtl_info.thd_testing_data[0] = nullptr;
	gtl_info.thd_testing_data[1] = nullptr;

	verifyTest(thd);

	return 1_i;
}
