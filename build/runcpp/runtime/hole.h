#pragma once

#include "../common.h"

#include "../core/bsqtype.h"

#include "./utils/lexer.h"
#include "./utils/builder.h"

namespace ᐸRuntimeᐳ 
{
    HoleBodyContext* getHoleBodyContextForID(size_t holeid);
    void addHoleBodyContextForID(size_t holeid, HoleBodyContext& ctx);

    void completeViaCommandLinePrompt(HoleBodyContext* ctx, const std::vector<void*>& args, void* result);
    void completeViaLLMValueGeneration(HoleBodyContext* ctx, const std::vector<void*>& args, void* result);

    std::string completeViaLLMVCodeGeneration(HoleBodyContext* ctx, const std::vector<void*>& args, void* result);

    void loadHoleExamples(size_t holeid, std::istream& in);
    void emitHoleExample(size_t holeid, std::ostream& out);

    void emitAllBodyHolesToStdOut();
}
