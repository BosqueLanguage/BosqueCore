template <size_t N>
static void runThreadTest(size_t nthds, void* roots[N])
{	
	gtl_info.insertThreadTestData<N>(roots);
	gtl_info.collectfp();
	𝐚𝐬𝐬𝐞𝐫𝐭(g_memstats.total_live_bytes > 0);

	std::thread thd = std::thread([troots = roots, nthds]() {
		for(size_t i = 0; i < N; i++) {
			gtl_info.thd_testing_data[i] = troots[i];
		} 
		initializeGC<sizeof(allocs) / sizeof(allocs[0])>(allocs, gtl_info, collect);

		threadTest<N>(troots, nthds);
	
		std::unique_lock lk(g_mtx);
		g_pause = false;
		lk.unlock();
		g_cv.notify_one();

		lk.lock();
		g_cv.wait(lk, []{ return g_pause; });

		// main thread dropped the roots, make sure no one died
		threadTest<N>(troots, nthds - 1);
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
}

__CoreCpp::Int sharedBasicTreeTest_1()
{	
	const size_t nroots = 2, nthds = 2;
	void* roots[nroots] = { 
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n))
	};
	runThreadTest<nroots>(nthds, roots);

	return 1_i;
}

__CoreCpp::Int sharedBasicTreeTest_6()
{	
	const size_t nroots = 2, nthds = 2;
	void* roots[nroots] = { 
		Main::accessNode(Main::makeTree(6_n, 0_n)),
		Main::accessNode(Main::makeTree(6_n, 0_n))
	};
	runThreadTest<nroots>(nthds, roots);

	return 1_i;
}

__CoreCpp::Int sharedBasicTreeTestMulti_1()
{	
	const size_t nroots = 6, nthds = 2;
	void* roots[nroots] = { 
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n)),
		Main::accessNode(Main::makeTree(1_n, 0_n))
	};
	runThreadTest<nroots>(nthds, roots);

	return 1_i;
}

__CoreCpp::Int sharedBasicTreeTestMulti_6()
{	
	const size_t nroots = 6, nthds = 2;
	void* roots[nroots] = { 
		Main::accessNode(Main::makeTree(6_n, 0_n)),
		Main::accessNode(Main::makeTree(6_n, 0_n)),
		Main::accessNode(Main::makeTree(6_n, 0_n)),
		Main::accessNode(Main::makeTree(6_n, 0_n)),
		Main::accessNode(Main::makeTree(6_n, 0_n)),
		Main::accessNode(Main::makeTree(6_n, 0_n))
	};
	runThreadTest<nroots>(nthds, roots);

	return 1_i;
}
