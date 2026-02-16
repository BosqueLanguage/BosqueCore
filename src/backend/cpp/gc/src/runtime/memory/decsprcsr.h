#pragma once

#include "../common.h"
#include "allocator.h"
#include "../support/arraylist.h"

#include <mutex>
#include <condition_variable>
#include <thread>
#include <iostream>

// Used for processing RC decrements on a separate thread
// -- utilized to help clean up heavy rc dec loads after we have freed enough
//    memory to ensure no allocators could be outran
struct DecsProcessor {
    std::mutex mtx;
    std::condition_variable cv;
    std::thread thd;    

    void (*processDecfp)(void*, ArrayList<void*>&, ArrayList<PageInfo*>&) noexcept;
	void (*tryUpdateDecdPages)(PageInfo*) noexcept;	
	ArrayList<void*> pending[MAX_THREADS];	
	ArrayList<PageInfo*> decd_pages[MAX_THREADS];

    enum class State {
        Running,
        Pausing,
        Paused,
        Stopping,
        Stopped
    };
    State st;

    DecsProcessor(): 
		mtx(), cv(), thd(), processDecfp(nullptr), tryUpdateDecdPages(nullptr)
		, pending(), decd_pages(), st(State::Paused)
	{
        GlobalThreadAllocInfo::s_thread_counter++;
		this->thd = std::thread([this] { this->process(); });
	}

    void changeStateFromMain(State nst, State ack)
    {
        std::unique_lock lk(this->mtx);
        this->st = nst;
		lk.unlock();
        this->cv.notify_one();
		lk.lock();
        this->cv.wait(lk, [this, ack]{ return this->st == ack; });
    }

    void changeStateFromWorker(State nst)
    {
        this->st = nst;
        this->cv.notify_one();
    }

    void pause()
    {
		{
			std::unique_lock lk(this->mtx);	
			if(this->st == State::Paused || this->st == State::Stopped) {
				return ;
			}
		}
        
        this->changeStateFromMain(State::Pausing, State::Paused);
    }

    void resume()
    {
		std::unique_lock lk(this->mtx);
		if(this->st == State::Stopped) {
			return ;	
		}

        this->st = State::Running;
		lk.unlock(); 
		this->cv.notify_one();
    }

    void stop()
    {
        this->pause(); // Ensure we are waiting
        this->changeStateFromMain(State::Stopping, State::Stopped);

        this->thd.join();
        if(this->thd.joinable()) {
            std::cerr << "Thread did not finish joining!\n";
            std::abort();
        }
    }

	// Merge pending decs from tinfo onto appropriate entry in `this->pending`
	// corresponding to tinfos thread id
	void mergePendingDecs(BSQMemoryTheadLocalInfo& tinfo) noexcept;
	
	// Merge pages with newly dead objects (from rc decrements) onto tinfos
	// `decd_pages` list
	void mergeDecdPages(BSQMemoryTheadLocalInfo& tinfo) noexcept;

	void process();
};
extern DecsProcessor g_decs_prcsr;
