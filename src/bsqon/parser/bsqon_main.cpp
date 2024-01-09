#include "../info/type_info.h"
#include "../info/bsqon.h"
#include "bsqon_parse.h"

#include <iostream>
#include <fstream>

int main(int argc, char** argv)
{
    //argv is a file name to a JSON file
    if(argc < 3) {
        printf("usage: bsqon <metadata.json> <type> [data.bsqon]\n");
        exit(1);
    }

    //parse the JSON 
    json jv = nullptr;
    try
    {
        std::ifstream infile(argv[1]);
        infile >> jv;
    }
    catch(const std::exception& e)
    {
        printf("Error parsing JSON: %s\n", e.what());
        exit(1);
    }
    
    //the property assembly is the code so load it
    BSQON::AssemblyInfo assembly;
    BSQON::AssemblyInfo::parse(jv, assembly);

    //the property loadtype is the type so look it up
    const BSQON::Type* loadtype = nullptr;
    loadtype = assembly.resolveType(argv[2]);
    if(loadtype->isUnresolved()) {
        printf("Invalid 'loadtype'\n");
        exit(1);
    }

    //the property value is the BSQON value (as a JSON string) so parse it
    BSQON_AST_Node* node = argc == 3 ? parse_from_stdin() : parse_from_file(argv[3]);
    char** errorInfo = (char**)malloc(sizeof(char*) * 128);
    size_t errorInfoCount = BSQON_AST_getErrorInfo(errorInfo);

    if(node == nullptr) {
        for(size_t i = 0; i < errorInfoCount; ++i) {
            printf("++ %s\n", errorInfo[i]);
        }

        fflush(stdout);
        exit(1);
    }
    else {
        BSQON::Parser parser(&assembly);
        BSQON::Value* res = parser.parseValue(loadtype, node);

        if(parser.errors.empty() && errorInfoCount == 0) {
            std::string rstr = res->toString();
            printf("%s\n", rstr.c_str());

            fflush(stdout);
            exit(0);
        }
        else {
            for(size_t i = 0; i < errorInfoCount; ++i) {
                std::string sstr(errorInfo[i]);
                if(!sstr.starts_with("syntax error")) {
                    printf("%s\n", sstr.c_str());
                }
            }

            for(size_t i = 0; i < parser.errors.size(); ++i) {
                const BSQON::ParseError& pe = parser.errors.at(i);
                printf("%s -- line %u\n", pe.message.c_str(), pe.loc.first_line);
            }

            fflush(stdout);
            exit(1);
        }
    }
}
