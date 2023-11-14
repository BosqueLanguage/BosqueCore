#include "../info/type_info.h"
#include "../info/bsqon.h"
#include "bsqon_parse.h"

int main(int argc, char** argv)
{
    //argv is a file name to a JSON file
    if(argc != 3) {
        printf("Expected 2 arguments to a file containing the assembly/loadtype/and value\n");
        exit(1);
    }


    //parse the JSON 
    json jv = ;
    
    //the property assembly is the code so load it
    if(jv["assembly"].is_null()) {
        printf("Missing 'assembly' information\n");
        exit(1);
    }

    BSQON::AssemblyInfo assembly;
    BSQON::AssemblyInfo::parse(jv["assembly"], assembly);

    //the property loadtype is the type so look it up
    if(!jv["loadtype"].is_string()) {
        printf("Missing 'loadtype' information\n");
        exit(1);
    }

    const BSQON::Type* loadtype = nullptr;
    loadtype = assembly.resolveType(jv["loadtype"].get<BSQON::TypeKey>());
    if(loadtype->isUnresolved()) {
        printf("Invalid 'loadtype'\n");
        exit(1);
    }

    //the property value is the BSQON value (as a JSON string) so parse it
    BSQON_AST_Node* node = parse_from_file(argv[2]);

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
