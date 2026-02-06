#include <thread>
#include <mutex>
#include <condition_variable>

std::mutex g_mtx;
std::condition_variable g_cv;
bool g_pause = true;	

template <size_t N>
static void threadTest(void* testroots[N], size_t nthds) noexcept
{
	for(size_t i = 0; i < N; i++) {
		MetaData* m = GC_GET_META_DATA_ADDR(testroots[i]);
		𝐚𝐬𝐬𝐞𝐫𝐭(static_cast<size_t>(GC_THREAD_COUNT(m)) == nthds && GC_IS_ALLOCATED(m));
	}
}
