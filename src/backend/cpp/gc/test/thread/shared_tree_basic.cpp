#include <thread>

#define verifyTest(THD) \
do { \
	THD.join(); \
	collect(); \
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes == 0); \
}while(0)

// this assumes we are only testing with two live threads, may be interesting
// to try spawning some more and see if things still work
template<size_t N>
static void threadTest(void* roots[N], size_t nthds) noexcept
{
	for(size_t i = 0; i < N; i++) {
		gtl_info.thd_testing_data[i] = roots[i];
	}
    	
	initializeGC<sizeof(allocs) / sizeof(allocs[0])>(allocs, gtl_info);
	collect();

	for(size_t i = 0; i < N; i++) {
		MetaData* m = GC_GET_META_DATA_ADDR(roots[i]);
		𝐚𝐬𝐬𝐞𝐫𝐭(static_cast<size_t>(GC_THREAD_COUNT(m)) == nthds);
	}
}

// would be interesting to add these as methods to a new type we use for 
// the thread data stuff
template <size_t N>
static void insert(void* roots[N]) noexcept
{
	static_assert(N < static_cast<size_t>(NUM_THREAD_TESTING_ROOTS));	
	for(size_t i = 0; i < N; i++) {
		gtl_info.thd_testing_data[i] = roots[i];
	}
}

static constexpr void clear() noexcept
{
	for(unsigned i = 0; i < NUM_THREAD_TESTING_ROOTS; i++) {
		gtl_info.thd_testing_data[i] = nullptr;	
	}
}

// roots dropped during BSQMemoryTheadLocalInfo destruction

__CoreCpp::Int sharedBasicTreeTest_1()
{	
	const size_t nroots = 2, nthds = 2;
	void* roots[nroots] = { 
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n))
	};
	insert<nroots>(roots);

	collect();
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes > 0);

	std::thread thd = std::thread([troots = roots]() {
		threadTest<nroots>(troots, nthds);	
	});

	clear();
	verifyTest(thd);

	return 1_i;
}
