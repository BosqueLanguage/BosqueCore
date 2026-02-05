#include "decsprcsr.h"

DecsProcessor g_decs_prcsr;

void DecsProcessor::process()
{
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
