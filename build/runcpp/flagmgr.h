#pragma once

#include <vector>
#include <string>

#define REGISTER_DIAGNOSTIC_FLAG(NAME, ACTUAL, DESC, DEFAULT, ...) ᐸFlagInfoᐳ::registerGeneralFlag({#NAME, DESC, std::to_string(DEFAULT), {__VA_ARGS__}})

namespace ᐸFlagInfoᐳ
{
    struct GeneralFlagInfo
    {
        std::string name;
        std::string setting;
        std::string description;
        std::string defaultValue;

        std::vector<std::string> mustenable;
    };

    struct DiagnosticFlagInfo
    {
        std::string name;
        std::string setting;
        std::string description;
        std::string defaultValue;

        std::vector<std::string> mustenable;
    };

    struct GCFlagInfo
    {
        std::string name;
        std::string setting;
        std::string description;
        std::string defaultValue;

        std::vector<std::string> mustenable;
    };

    inline std::vector<GeneralFlagInfo> g_general_flags{};
    inline std::vector<DiagnosticFlagInfo> g_diagnostic_flags{};
    inline std::vector<GCFlagInfo> g_gc_flags{};

    inline void registerGeneralFlag(const GeneralFlagInfo& flag)
    {
        g_general_flags.push_back(flag);
    }

    inline void registerDiagnosticFlag(const DiagnosticFlagInfo& flag)
    {
        g_diagnostic_flags.push_back(flag);
    }

    inline void registerGCFlag(const GCFlagInfo& flag)
    {
        g_gc_flags.push_back(flag);
    }
}
