#include "hole.h"

#include "taskinfo.h"
#include "./allocator/alloc.h"

//For now we are going to run this through boost -- later want IO unified with other http and io_uring
#include <boost/asio.hpp>
#include <boost/beast.hpp>
#include <boost/beast/ssl.hpp>

namespace ᐸRuntimeᐳ 
{
    json makeAIHoleRequest(const std::string& sysprompt, const std::string& userprompt, json schema) 
    {
        //
        //TODO: this is very hacked together and needs some care
        //

        boost::beast::error_code ec;
        std::string host = "api.openai.com";
        std::string target = "/v1/chat/completions";

        boost::asio::io_context ioc;
        boost::asio::ssl::context ctx{boost::asio::ssl::context::tlsv12_client};
        boost::beast::ssl_stream<boost::beast::tcp_stream> stream{ioc, ctx};

        boost::asio::ip::tcp::resolver resolver(ioc);
        auto const results = resolver.resolve(host, "443");
        boost::beast::get_lowest_layer(stream).connect(results, ec);
        if(ec) {
            std::cerr << "Error during connection: " << ec.message() << std::endl;
            assert(false);
        }

        if (!SSL_set_tlsext_host_name(stream.native_handle(), host.c_str())) {
            boost::system::error_code ec{static_cast<int>(::ERR_get_error()), boost::asio::error::get_ssl_category()};
            assert(false);
        }

        stream.handshake(boost::asio::ssl::stream_base::client, ec);
        if(ec) {
            std::cerr << "Error during SSL handshake: " << ec.message() << std::endl;
            assert(false);
        }

        boost::beast::http::request<boost::beast::http::string_body> req{boost::beast::http::verb::post, target, 11}; // HTTP 1.1
        req.set(boost::beast::http::field::host, host);
        req.set(boost::beast::http::field::user_agent, BOOST_BEAST_VERSION_STRING);

        //TODO: we need to futz with this
        const char* api_key = getenv("TECTON_KEY");
        if(api_key == nullptr) {
            std::cerr << "Error: TECTON_KEY environment variable is not set." << std::endl;
            assert(false);
        }

        req.set(boost::beast::http::field::authorization, "Bearer " + std::string(api_key)); // Set the API key for authorization
        req.set(boost::beast::http::field::content_type, "application/json"); // Required for JSON
        
        json request_json = json::object();
        request_json["model"] = "gpt-6-sol";
        request_json["messages"] = json::array({
            {
                {"role", "system"},
                {"content", sysprompt}
            },
            {
                {"role", "user"},
                {"content", userprompt}
            }
        });

        req.body() = std::move(request_json.dump());
        req.prepare_payload(); // Automatically calculates Content-Length header

        boost::beast::http::write(stream, req, ec);
        if(ec) {
            std::cerr << "Error during write: " << ec.message() << std::endl;
            assert(false);
        }

        // Receive the response
        boost::beast::flat_buffer buffer;
        boost::beast::http::response<boost::beast::http::string_body> res;
        boost::beast::http::read(stream, buffer, res, ec);
        if(ec) {
            std::cerr << "Error reading response: " << ec.message() << std::endl;
            assert(false);
        }

        // Gracefully close the socket
        stream.next_layer().socket().shutdown(boost::asio::ip::tcp::socket::shutdown_both, ec);

        return json::parse(res.body());
    }

    HoleBodyContextManager g_hole_body_contexts;
    
    bool HoleBodyContextManager::trySingleStdInRead(const TypeInfo* ofinfo, void* outvalue)
    {
        size_t obytes = 0;
        std::list<uint8_t*> iobb;
        iobb.push_back(g_alloc_info.io_buffer_alloc());
    
        int c = std::cin.get();
        while(c != ';' && c != std::char_traits<char>::eof()) {
            if(obytes != 0 && obytes % MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE == 0) {
                iobb.push_back(g_alloc_info.io_buffer_alloc());
            }

            (iobb.back())[obytes % MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE] = static_cast<uint8_t>(c);
            ++obytes;

            c = std::cin.get();
        }

        BAPILexer lexer(IOBufferIterator::initializeBegin(iobb.cbegin(), obytes), IOBufferIterator::initializeEnd(iobb.cend(), obytes), true);
        lexer.initialize();
        
        bool allconsumed = false;
        if (setjmp(*tl_bosque_info.current_task->error_handler) > 0) {
            std::cout << "Error occurred while trying to process input -- retrying" << std::endl;
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
        
        //TODO: check for memoized match here

        if(ctx->argtypes.empty()) {
            std::cout << "[ ]";
        }
        else {
            IOBufferStreamingBuilder builder(true);

            for(size_t j = 0; j < args.size(); ++j) {
                ctx->argtypes[j]->opdispatch.bsqToBAPIFp(ctx->argtypes[j], args[j], &builder);
                builder.appendConstString(", ");
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
            std::cout << " ]" << std::endl;

            while(!oibb.empty()) {
                g_alloc_info.io_buffer_free(oibb.back());
                oibb.pop_back();
            }
        }

        std::jmp_buf env;
        std::jmp_buf* origenv = tl_bosque_info.current_task->error_handler;
        tl_bosque_info.current_task->error_handler = &env;
        bool done = false;
        while(!done) {
            done = trySingleStdInRead(ctx->resulttype, result);
        }

        tl_bosque_info.current_task->error_handler = origenv;
    }

    void HoleBodyContextManager::completeViaLLMValueGeneration(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result)
    {
        /*
        std::string sysmsg = "We are creating mocks for testing. Given the user input, relevant code and input values, generate the appropriate return result as a valid JSON value.";
        std::string othercode = "The other relevant code for this task is --\n\n  function getBestTeams(results: List<TeamResult>): List<CString>     requires !results.empty(); { let maxscore = getMaxScore(results.map<Int>(fn(t) => t.round1), results.map<Int>(fn(t) => t.round2)); return results.filter(pred(t) => t.round1 + t.round2 == maxscore.0 + maxscore.1).map<CString>(fn(t) => t.team); }";
        
        std::string testingusermsg = "The input function is --\n\n  %** Get the maximum combined scores for the rounds in l1 and l2 **%\nfunction getMaxScore(l1: List<Int>, l2: List<Int>): (|Int, Int|)\n    requires !l1.empty() && !l2.empty();\n    requires l1.size() == l2.size()\n{...}";
        std::string data = "The input data is --\n\n  {l1: [10, 7], l2: [20, 25]}";

        json testingschema = json::object({
            {"type", "array"},
            {"items", {"type", "integer"}},
            {"minItems", 2},
            {"maxItems", 2}
        });

        std::cout << "Hit hole definition of invoke: " << ctx->invokename << std::endl;
        std::cout << "Constructing output using LLM Agent..." << std::endl;
        json jres = makeAIHoleRequest(sysmsg + "\n\n" + othercode, testingusermsg + data, testingschema);

        json jj = json::parse(jres["choices"][0]["message"]["content"].get<std::string>());
        ctx->resulttype->opdispatch.jsonParseToBSQFp(ctx->resulttype, jj, result);

        ctx->resulttype->opdispatch.displayFp(ctx->resulttype, result, std::cout, std::nullopt);
        std::cout << std::endl;
        */

        assert(false); //completeViaLLMValueGeneration not yet implemented well -- next after commit
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
