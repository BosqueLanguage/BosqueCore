#include "hole.h"

#include "taskinfo.h"
#include "./allocator/alloc.h"

namespace ᐸRuntimeᐳ 
{
    HoleBodyContextManager g_hole_body_contexts;
    
    bool HoleBodyContextManager::trySingleStdInRead(const TypeInfo* ofinfo, void* outvalue)
    {
        size_t obytes = 0;
        std::list<uint8_t*> iobb;
        iobb.push_back(g_alloc_info.io_buffer_alloc());
    
        char c; 
        std::cin.get(c);
        while(c != ';' && c != EOF) {
            (iobb.back())[obytes++] = static_cast<uint8_t>(c);
            std::cin.get(c);
        }

        BAPILexer lexer(IOBufferIterator::initializeBegin(iobb.cbegin(), obytes), IOBufferIterator::initializeEnd(iobb.cend(), obytes), true);
        lexer.initialize();
        
        bool allconsumed = false;
        if (setjmp(*tl_bosque_info.current_task->error_handler) > 0) {
            std::cout << "Error occurred while trying to process input -- retrying" << std::endl;
            return false;
        }
        else {
            ofinfo->opdispatch.parseToBSQFp(ofinfo, &lexer, outvalue);
            allconsumed = lexer.allInputConsumed();
        }

        while(!iobb.empty()) {
            g_alloc_info.io_buffer_free(iobb.back());
            iobb.pop_back();
        }
        
        if(c == EOF) {
            std::cout << "Input closed -- exiting..." << std::endl;
            exit(1);
        }

        return allconsumed;
    }

    HoleBodyContext* HoleBodyContextManager::getHoleContextForID(size_t holeid)
    {
        auto ii = std::find_if(this->contexts.begin(), this->contexts.end(), [holeid](const HoleBodyContext& hb) {
            return hb.holeid == holeid;
        });

        if(ii == this->contexts.end()) {
            return nullptr;
        }
        else {
            return &(*ii);
        }
    }

    void HoleBodyContextManager::addHoleContextForID(size_t holeid, const HoleBodyContext& ctx)
    {
        this->contexts.push_back(ctx);
    }

    void HoleBodyContextManager::completeViaCommandLinePrompt(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result)
    {        
        std::cout << "Hit hole definition of invoke: " << ctx->invokename << " need result for the input" << std::endl;
        
        if(ctx->argtypes.empty()) {
            std::cout << "[ ]";
        }
        else {
            IOBufferStreamingBuilder builder(true);

            for(size_t j = 0; j < args.size(); ++j) {
                ctx->argtypes[j]->opdispatch.bsqToBAPIFp(ctx->argtypes[j], args[j], &builder);
                std::cout << args[j];
            }
            
            std::list<uint8_t*> oibb; 
            size_t obytes = builder.finalize(oibb);

            std::cout << "[ ";
            //TODO assume chars are all printable for now
            size_t ii = 0; auto biter = oibb.begin();
            while(biter != oibb.end()) {
                for(size_t jj = 0; jj < std::min(ᐸRuntimeᐳ::MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE, obytes - ii); ++jj) {
                    std::cout << (char)(*biter)[jj];
                }
                ii += std::min(ᐸRuntimeᐳ::MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE, obytes - ii);
                biter++;
            }
            std::cout << " ]";
        }

        //TODO: check for memoized match here

        std::jmp_buf env;
        std::jmp_buf* origenv = tl_bosque_info.current_task->error_handler;
        tl_bosque_info.current_task->error_handler = &env;
        bool done = false;
        while(!done)
        {
            done = trySingleStdInRead(ctx->resulttype, result);
        }

        tl_bosque_info.current_task->error_handler = origenv;
    }

    void HoleBodyContextManager::completeViaLLMValueGeneration(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result)
    {
        assert(false); //completeViaLLMValueGeneration not yet implemented
    }

    std::string HoleBodyContextManager::completeViaLLMVCodeGeneration(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result)
    {
        assert(false); //completeViaLLMVCodeGeneration not yet implemented
    }

    void HoleBodyContextManager::loadHoleExamples(size_t holeid, std::istream& in)
    {
        assert(false); //loadHoleExamples not yet implemented
    }
    
    void HoleBodyContextManager::emitHoleExample(size_t holeid, std::ostream& out)
    {
        //TODO: we are assuming a single thread here but later we need a global list of all threads and then over that too
        auto ctx = this->getHoleContextForID(holeid);
        assert(ctx != nullptr);

        for(auto iter = ctx->examples.cbegin(); iter != ctx->examples.cend(); ++iter) {
            if(ctx->argtypes.empty()) {
                out << "[ ]";
            }
            else {
                out << "[ ";
                for(size_t j = 0; j < iter->first.size(); ++j) {
                    out << iter->first[j];

                }
                out << " ]";
            }

            out << " => " << iter->second << std::endl;
        }
    }

    void HoleBodyContextManager::emitAllBodyHolesToStdOut()
    {
        for(auto iter = this->contexts.cbegin(); iter != this->contexts.cend(); ++iter) {
            std::cout << "Example IO pairs for: " << iter->invokename << std::endl;
            emitHoleExample(iter->holeid, std::cout);

            std::cout << std::endl;
        }
    }
}
