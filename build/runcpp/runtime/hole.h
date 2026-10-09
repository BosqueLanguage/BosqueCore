#pragma once

#include "../common.h"

#include "../core/bsqtype.h"

#include "./utils/lexer.h"
#include "./utils/builder.h"

namespace ᐸRuntimeᐳ 
{

    class HoleBodyContext
    {
    public:
        size_t holeid;

        std::string invokename;
        std::string filename;
        size_t lineStart;
        size_t lineEnd;

        std::optional<std::string> doccomment;
        std::vector<const TypeInfo*> argtypes;
        const TypeInfo* resulttype;

        std::vector<std::pair<std::vector<std::string>, std::string>> examples;
        std::optional<std::string> imploption;

        HoleBodyContext() : holeid{}, invokename{}, filename{}, lineStart{}, lineEnd{}, doccomment{}, argtypes{}, resulttype(nullptr), examples{}, imploption{std::nullopt} {}
        HoleBodyContext(const HoleBodyContext&) = default;
        
        HoleBodyContext(size_t holeid, const std::string& invokename, const std::string& filename, size_t lineStart, size_t lineEnd, const std::optional<std::string>& doccomment, const std::vector<const TypeInfo*>& argtypes, const TypeInfo* resulttype) : holeid(holeid), invokename(invokename), filename(filename), lineStart(lineStart), lineEnd(lineEnd), doccomment(doccomment), argtypes(argtypes), resulttype(resulttype), examples{}, imploption{std::nullopt} {}
    };

    class HoleBodyContextManager
    {
    private:
        std::vector<HoleBodyContext> contexts;

        bool trySingleStdInRead(const TypeInfo* ofinfo, void* outvalue);

    public:
        HoleBodyContext* getHoleContextForID(size_t holeid);
        void addHoleContextForID(size_t holeid, const HoleBodyContext& ctx);

        void completeViaCommandLinePrompt(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result);
        void completeViaLLMValueGeneration(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result);

        std::string completeViaLLMVCodeGeneration(HoleBodyContext* ctx, const std::vector<const void*>& args, void* result);

        void loadHoleExamples(size_t holeid, std::istream& in);
        void emitHoleExample(size_t holeid, std::ostream& out);

        void emitAllBodyHolesToStdOut();
    };
    
    extern HoleBodyContextManager g_hole_body_contexts;
}
