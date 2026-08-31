#include "tecton.h"

static const std::string g_openai_url   = "https://api.openai.com/v1/responses";
static const std::string g_model = "gpt-5.6";

constexpr const char* g_model_template = "[**MODEL**]";
constexpr const char* g_developer_prompt_template = "[**DEVELOPER_PROMPT**]";
constexpr const char* g_user_prompt_template = "[**USER_PROMPT**]";
constexpr const char* g_dataformat_template = "[**DATA_FORMAT**]";

static const std::string g_api_json = R"(
{
    "model": "[**MODEL**]",
    "reasoning": {"effort": "low"},
    "input": [
        {
            "role": "developer",
            "content": [**DEVELOPER_PROMPT**]
        },
        {
            "role": "user",
            "content": [**USER_PROMPT**]
        }
    ]
}
)";

size_t WriteCallback(void* contents, size_t size, size_t nmemb, std::string* output) 
{
    size_t totalSize = size * nmemb;
    output->append((char*)contents, totalSize);
    return totalSize;
}

std::string makeAPIRequest(const std::string& apiKey, const std::string& url, const std::string& payload) 
{
    CURL* curl = curl_easy_init();

    std::string responseString;
    
    struct curl_slist* headers = nullptr;

    headers = curl_slist_append(headers, "Content-Type: application/json");
    headers = curl_slist_append(headers, ("Authorization: Bearer " + apiKey).c_str());
    
    curl_easy_setopt(curl, CURLOPT_URL, url.c_str());
    curl_easy_setopt(curl, CURLOPT_POST, 1L);
    curl_easy_setopt(curl, CURLOPT_POSTFIELDS, payload.c_str());
    curl_easy_setopt(curl, CURLOPT_HTTPHEADER, headers);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, WriteCallback);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, &responseString);

    CURLcode res = curl_easy_perform(curl);
    if (res != CURLE_OK) {
        std::cerr << "cURL Error: " << curl_easy_strerror(res) << std::endl;
    }

    // Cleanup
    curl_easy_cleanup(curl);
    curl_slist_free_all(headers);

    return responseString;
}

std::string generateOpenAPIMsg(const std::string& systemPrompt, const std::string& userPrompt, const std::string& dataformat)
{
    json jsys = json(systemPrompt);
    json juser = json(userPrompt);
    json jdataformat = json(dataformat);

    std::string result = g_api_json;
    size_t pos;
    if((pos = result.find(g_model_template)) != std::string::npos) {
        result.replace(pos, strlen(g_model_template), g_model);
    }
    if((pos = result.find(g_developer_prompt_template)) != std::string::npos) {
        result.replace(pos, strlen(g_developer_prompt_template), jsys.dump());
    }
    if((pos = result.find(g_user_prompt_template)) != std::string::npos) {
        result.replace(pos, strlen(g_user_prompt_template), juser.dump());
    }
    if((pos = result.find(g_dataformat_template)) != std::string::npos) {
        result.replace(pos, strlen(g_dataformat_template), jdataformat.dump());
    }

    return result;
}

ᐸRuntimeᐳ::XByteBuffer generateArgsOpenAPI(const ᐸRuntimeᐳ::XString& systemPrompt, const ᐸRuntimeᐳ::XString& userPrompt, const ᐸRuntimeᐳ::XString& dataformat)
{
    std::string apiKey = std::getenv("TECTON_KEY") ? std::string{std::getenv("TECTON_KEY")} : std::string{""};
    if(apiKey.empty()) {
        return ᐸRuntimeᐳ::XByteBuffer::mk({});
    }

    const std::string cppsys = ᐸRuntimeᐳ::fromXString(systemPrompt);
    const std::string cppuser = ᐸRuntimeᐳ::fromXString(userPrompt);
    const std::string cppdataformat = ᐸRuntimeᐳ::fromXString(dataformat);
    std::string prompt = generateOpenAPIMsg(cppsys, cppuser, cppdataformat);

    std::cout << prompt << std::endl;

    std::string response = makeAPIRequest(apiKey, g_openai_url, prompt);
    json responseJson = json::parse(response);
    std::cout << "---- Raw Response ----" << std::endl << responseJson.dump(8) << std::endl;

    std::string contentString = responseJson["choices"][0]["message"]["content"];
    size_t start = contentString.find("[");
    size_t end = contentString.rfind("]");
    if (start == std::string::npos || end == std::string::npos) {
        return ᐸRuntimeᐳ::XByteBuffer::mk({});
    }

    std::string extractedJson = contentString.substr(start, end - start + 1);   

    return ᐸRuntimeᐳ::XByteBuffer::mk(extractedJson.cbegin(), extractedJson.cend(), extractedJson.size());
}

/*
curl "https://api.openai.com/v1/responses" \
    -H "Content-Type: application/json" \
    -H "Authorization: Bearer $OPENAI_API_KEY" \
    -d '{
        "model": "gpt-5.6",
        "reasoning": {"effort": "low"},
        "instructions": "Talk like a pirate.",
        "input": "Are semicolons optional in JavaScript?"
    }'
*/
