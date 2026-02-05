#include <thread>
#include <mutex>
#include <condition_variable>

std::mutex g_mtx;
std::condition_variable g_cv;
bool g_pause = true;	

// roots dropped during BSQMemoryTheadLocalInfo destruction
template<size_t N>
static void threadTest(void* testroots[N], size_t nthds) noexcept
{
	for(size_t i = 0; i < N; i++) {
		MetaData* m = GC_GET_META_DATA_ADDR(testroots[i]);
		𝐚𝐬𝐬𝐞𝐫𝐭(static_cast<size_t>(GC_THREAD_COUNT(m)) == nthds && GC_IS_ALLOCATED(m));
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

	// just so things are clear it might be goo if we call init gc here instead
	// of from the actual cpp main

	gtl_info.collectfp();
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes > 0);

	std::thread thd = std::thread([troots = roots]() {
		for(size_t i = 0; i < nroots; i++) {
			gtl_info.thd_testing_data[i] = troots[i];
		} 
		initializeGC<sizeof(allocs) / sizeof(allocs[0])>(allocs, gtl_info, collect);

		threadTest<nroots>(troots, nthds);
	
		std::unique_lock lk(g_mtx);
		g_pause = false;
		lk.unlock();
		g_cv.notify_one();

		lk.lock();
		g_cv.wait(lk, []{ return g_pause; });

		// main thread dropped the roots, make sure no one died
		threadTest<nroots>(troots, nthds - 1);
	});

	std::unique_lock lk(g_mtx);
	g_cv.wait(lk, []{ return !g_pause; });

	gtl_info.clearThreadTestData();
	gtl_info.collectfp();
	g_pause = true;
	lk.unlock();
	g_cv.notify_one();

	thd.join();
	gtl_info.collectfp();
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes == 0);
	
	return 1_i;
}
