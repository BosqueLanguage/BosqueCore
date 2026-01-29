#include "decsprcsr.h"

DecsProcessor g_decs_prcsr;

void DecsProcessor::process()
{
	std::unique_lock lk(this->mtx);
	while(true) {
		this->cv.wait(lk, [this]
			{ return this->st != State::Paused; }
		);

		if(this->st == State::Stopping) {
			this->changeStateFromWorker(State::Stopped);
			return ;
		}

		while(!this->pending.isEmpty()) {
			if(this->st != State::Running) {
				break;
			}

			void* obj = this->pending.pop_front();
			this->processDecfp(obj, this->pending, this->decd_pages);
		}
		
		this->changeStateFromWorker(State::Paused);
	}
}
