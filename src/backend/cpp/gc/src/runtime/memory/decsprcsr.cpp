#include "decsprcsr.h"

#include "threadinfo.h"

DecsProcessor g_decs_prcsr;

void DecsProcessor::mergePendingDecs(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
	ArrayList<void*>& decs = this->pending[tinfo.tl_id];
	if(!decs.isInitialized()) {
		decs.initialize();	
	}

	while(!tinfo.decs_batch.isEmpty()) {
		void* obj = tinfo.decs_batch.pop_front();	
		decs.push_back(obj);
	}
}

void DecsProcessor::mergeDecdPages(BSQMemoryTheadLocalInfo& tinfo) noexcept
{
	ArrayList<PageInfo*>& pages = this->decd_pages[tinfo.tl_id];

	while(!pages.isEmpty()) {
		PageInfo* p = pages.pop_front();
		this->tryUpdateDecdPages(p);	
	}
}

void DecsProcessor::process()
{
	// TODO: tmp hack to ensure memstats gets initialized for the decs thread
	// for the sake of properly dumping global memstats
	UPDATE_TOTAL_PAGES(gtl_info.memstats, +=, 0);

	while(this->st != State::Stopping) {
		{	
			std::unique_lock lk(this->mtx);	
			this->changeStateFromWorker(State::Paused);
			this->cv.wait(lk, [this]
				{ return this->st != State::Paused; }
			);
		}	
		
		for(size_t i = 0; i < MAX_THREADS; i++) {
			ArrayList<void*>& cur_pending = this->pending[i];
			ArrayList<PageInfo*>& cur_decd_pages = this->decd_pages[i];	
			if(!cur_decd_pages.isInitialized()) {
				cur_decd_pages.initialize();	
			}

			while(!cur_pending.isEmpty()) {
				if(this->st != State::Running) {
					break;
				}

				void* obj = cur_pending.pop_front();
				this->processDecfp(obj, cur_pending, cur_decd_pages);
			}
		}				
	}
	this->changeStateFromWorker(State::Stopped);
}
