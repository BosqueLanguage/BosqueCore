#pragma once

#include "../common.h"
#include "allocator.h"
#include "../support/arraylist.h"

#include <mutex>
#include <condition_variable>
#include <thread>

// Used for processing RC decrements on a separate thread
// -- utilized to help clean up heavy rc dec loads after we have freed enough
//    memory to ensure no allocators could be outran
struct DecsProcessor {
    std::mutex mtx;
    std::condition_variable cv;
    std::thread thd;    

    void (*processDecfp)(void*, ArrayList<void*>&, ArrayList<PageInfo*>&);
	ArrayList<void*> pending;	
	ArrayList<PageInfo*> decd_pages;

    enum class State {
        Running,
        Pausing,
        Paused,
        Stopping,
        Stopped
    };
    State st;

    DecsProcessor(): 
		mtx(), cv(), thd(), processDecfp(nullptr), pending(), decd_pages(), 
		st(State::Paused)
	{
	    this->pending.initialize();
		this->decd_pages.initialize();
        GlobalThreadAllocInfo::s_thread_counter++;
		this->thd = std::thread([this] { this->process(); });
	}

    void changeStateFromMain(State nst, State ack)
    {
        std::unique_lock lk(this->mtx);
        this->st = nst;
        this->cv.notify_one();
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
			if(this->st == State::Paused) {
				return ;
			}
		}
        
        this->changeStateFromMain(State::Pausing, State::Paused);
    }

    void resume()
    {
		std::unique_lock lk(this->mtx);
        this->st = State::Running;
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

        GlobalThreadAllocInfo::s_thread_counter--;
    }

	void mergeDecdPages(ArrayList<PageInfo*>& dst)
	{
		while(!this->decd_pages.isEmpty()) {
			PageInfo* p = this->decd_pages.pop_front();
			dst.push_back(p);
		}
	}

	void process();
};
extern DecsProcessor g_decs_prcsr;
