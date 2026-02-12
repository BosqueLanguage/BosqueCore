template <size_t NROOTS, size_t NSURVIVE>
static void runThreadTest(size_t nthds, void* roots[NROOTS], 
	void* survive[NSURVIVE])
{	
	gtl_info.insertThreadTestData<NROOTS>(roots);
	gtl_info.collectfp();
	𝐚𝐬𝐬𝐞𝐫𝐭(gtl_info.memstats.total_live_bytes > 0);

	std::thread thd = std::thread([troots = survive]() {
		gtl_info.insertThreadTestData<NSURVIVE>(troots);
		gtl_info.initializeGC(allocs, sizeof(allocs) / sizeof(allocs[0]), collect);

		// newly found roots on this thread, so one thd count
		threadTest<NSURVIVE>(troots, 1);
	
		std::unique_lock lk(g_mtx);
		g_pause = false;
		lk.unlock();
		g_cv.notify_one();

		lk.lock();
		g_cv.wait(lk, []{ return g_pause; });

		// main thread dropped its roots, make sure no one died
		threadTest<NSURVIVE>(troots, 1);
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
	𝐚𝐬𝐬𝐞𝐫𝐭(gtl_info.memstats.total_live_bytes == 0);
}

__CoreCpp::Int wideSubtreeTest_2()
{	
	using namespace Main;	

	const size_t nroots = 2, nsurvive = 12, nthds = 2;
	void* roots[nroots] = { 
		accessNode(makeTree(2_n, 0_n)),
		accessNode(makeTree(2_n, 0_n))
	};

	// updates all children to old space
	gtl_info.insertThreadTestData<nroots>(roots);
	gtl_info.collectfp();

	void* survive[nsurvive] = {
		accessNode(static_cast<Node*>(roots[0])->n2),
		accessNode(static_cast<Node*>(roots[0])->n4),
		accessNode(static_cast<Node*>(roots[0])->n6),
		accessNode(static_cast<Node*>(roots[0])->n8),
		accessNode(static_cast<Node*>(roots[0])->n10),
		accessNode(static_cast<Node*>(roots[0])->n12),
		accessNode(static_cast<Node*>(roots[1])->n2),
		accessNode(static_cast<Node*>(roots[1])->n4),
		accessNode(static_cast<Node*>(roots[1])->n6),
		accessNode(static_cast<Node*>(roots[1])->n8),
		accessNode(static_cast<Node*>(roots[1])->n10),
		accessNode(static_cast<Node*>(roots[1])->n12)
	};

	runThreadTest<nroots, nsurvive>(nthds, roots, survive);

	return 1_i;
}

__CoreCpp::Int wideSubtreeTestMulti_2()
{	
	using namespace Main;	

	const size_t nroots = 6, nsurvive = 12, nthds = 2;
	void* roots[nroots] = { 
		accessNode(makeTree(2_n, 0_n)),
		accessNode(makeTree(2_n, 0_n)),
		accessNode(makeTree(2_n, 0_n)),
		accessNode(makeTree(2_n, 0_n)),
		accessNode(makeTree(2_n, 0_n)),
		accessNode(makeTree(2_n, 0_n))
	};

	// updates all children to old space
	gtl_info.insertThreadTestData<nroots>(roots);
	gtl_info.collectfp();
	
	void* survive[nsurvive] = {
		accessNode(static_cast<Node*>(roots[0])->n6),
		accessNode(static_cast<Node*>(roots[0])->n12),
		accessNode(static_cast<Node*>(roots[1])->n6),
		accessNode(static_cast<Node*>(roots[1])->n12),
		accessNode(static_cast<Node*>(roots[2])->n6),
		accessNode(static_cast<Node*>(roots[2])->n12),
		accessNode(static_cast<Node*>(roots[3])->n6),
		accessNode(static_cast<Node*>(roots[3])->n12),
		accessNode(static_cast<Node*>(roots[4])->n6),
		accessNode(static_cast<Node*>(roots[4])->n12),
		accessNode(static_cast<Node*>(roots[5])->n6),
		accessNode(static_cast<Node*>(roots[5])->n12)
	};

	runThreadTest<nroots, nsurvive>(nthds, roots, survive);

	return 1_i;
}
