#pragma once

#include <cmath>
#include <cstring>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <curl/curl.h>
#include "json.hpp"

#include "../runcpp/common.h"
#include "../runcpp/core/bytebuff.h"
#include "../runcpp/core/strings.h"

using json = nlohmann::json;

ᐸRuntimeᐳ::XByteBuffer generateArgsOpenAPI(const ᐸRuntimeᐳ::XString& systemPrompt, const ᐸRuntimeᐳ::XString& userPrompt, const ᐸRuntimeᐳ::XString& dataformat);
