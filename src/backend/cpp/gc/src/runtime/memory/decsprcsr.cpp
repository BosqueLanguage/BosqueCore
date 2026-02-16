#include "decsprcsr.h"

#include "threadinfo.h"

DecsProcessor g_decs_prcsr;

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

		while(!this->pending.isEmpty()) {
			if(this->st != State::Running) {
				break;
			}

			void* obj = this->pending.pop_front();
			this->processDecfp(obj, this->pending, this->decd_pages);
		}
	}
	this->changeStateFromWorker(State::Stopped);
}
