#include <thread>

#define verifyTest(THD) \
do { \
	THD.join(); \
	collect(); \
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes == 0); \
}while(0)

// roots dropped during BSQMemoryTheadLocalInfo destruction
template<size_t N>
static void threadTest(void* testroots[N], size_t nthds) noexcept
{
	for(size_t i = 0; i < N; i++) {
		gtl_info.thd_testing_data[i] = testroots[i];
	} 

	// NOTE we may be interested in forcing a collection when init gc
	initializeGC<sizeof(allocs) / sizeof(allocs[0])>(allocs, gtl_info, collect);

	for(size_t i = 0; i < N; i++) {
		MetaData* m = GC_GET_META_DATA_ADDR(testroots[i]);
		𝐚𝐬𝐬𝐞𝐫𝐭(static_cast<size_t>(GC_THREAD_COUNT(m)) == nthds);
	}
}

__CoreCpp::Int sharedBasicTreeTest_1()
{	
	const size_t nroots = 2, nthds = 2;
	void* roots[nroots] = { 
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n))
	};
	gtl_info.insertThreadTestData<nroots>(roots);

	collect();
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes > 0);

	std::thread thd = std::thread([troots = roots]() {
		threadTest<nroots>(troots, nthds);	
	});

	gtl_info.clearThreadTestData();
	verifyTest(thd);

	return 1_i;
}
