#pragma once

#include <assert.h>

#include <cstdlib>
#include <cstdint>
#include <math.h>
#include <ctime>
#include <cstdio>

#include <string>
#include <regex>
#include <optional>

#include <set>

#include "json.hpp"
typedef nlohmann::json json;

namespace BSQON
{
    typedef uint32_t CharCode;
    typedef size_t StateID;

    class CharCodeIterator
    {
    public:
        CharCodeIterator() {;}
        virtual ~CharCodeIterator() {;}

        virtual bool valid() const = 0;
        virtual void advance() = 0;

        virtual CharCode get() const = 0;
    };

    class StdStringCodeIterator : public CharCodeIterator
    {
    public:
        const std::string sstr;
        int64_t curr;

        StdStringCodeIterator(std::string& sstr) : CharCodeIterator(), sstr(sstr), curr(0) {;}
        virtual ~StdStringCodeIterator() {;}

        virtual bool valid() const override final
        {
            return this->curr != (int64_t)this->sstr.size();
        }

        virtual void advance() override final
        {
            this->curr++;
        }

        virtual CharCode get() const override final
        {
            return this->sstr.at(this->curr);
        }
    };
}

