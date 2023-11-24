#include "../info/type_info.h"
#include "../info/bsqon.h"
#include "bsqon_parse.h"

#include <iostream>
#include <fstream>

int main(int argc, char** argv)
{
    //argv is a file name to a JSON file
    if(argc != 4) {
        printf("Expected 3 arguments to a file containing the assembly file, type, and value file\n");
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
    BSQON_AST_Node* node = parse_from_file(argv[3]);

    BSQON::Parser parser(&assembly);
    BSQON::Value* res = parser.parseValue(loadtype, node);

    if(parser.errors.empty()) {
        std::string rstr = res->toString();
        printf("%s\n", rstr.c_str());

        exit(0);
    }
    else {
        for(size_t i = 0; i < parser.errors.size(); ++i) {
            const BSQON::ParseError& pe = parser.errors.at(i);
            printf("%s -- line %u\n", pe.message.c_str(), pe.loc.first_line);
        }

        exit(1);
    }
}
