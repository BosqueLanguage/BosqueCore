#include "bsqregex.h"

namespace BSQON
{
    BSQRegexOpt* BSQRegexOpt::parse(json j)
    {
        auto tag = j["tag"].get<std::string>();
        
        if(tag == "TreeIR::RegexLiteral") {
            return BSQLiteralRe::parse(j);
        }
        else if(tag == "TreeIR::RegexCharRange") {
            return BSQCharRangeRe::parse(j);
        }
        else if(tag == "TreeIR::RegexDotCharClass") {
            return BSQCharClassDotRe::parse(j);
        }
        else if(tag == "TreeIR::RegexStarRepeat") {
            return BSQStarRepeatRe::parse(j);
        }
        else if(tag == "TreeIR::RegexPlusRepeat") {
            return BSQPlusRepeatRe::parse(j);
        }
        else if(tag == "TreeIR::RegexRangeRepeat") {
            return BSQRangeRepeatRe::parse(j);
        }
        else if(tag == "TreeIR::RegexOptional") {
            return BSQOptionalRe::parse(j);
        }
        else if(tag == "TreeIR::RegexAlternation") {
            return BSQAlternationRe::parse(j);
        }
        else {
            return BSQSequenceRe::parse(j);
        }
    }

    std::string BSQLiteralRe::escapeCode(CharCode c)
    {
        auto pct = "%";
        if(c == '/') {
            return pct + std::string("slash;");
        }
        else if( c == '%') {
            return pct + std::string("percent;");
        }
        else if(c == '\n') {
            return pct + std::string("newline;");
        }
        else if(c == '\t') {
            return pct + std::string("tab;");
        }
        else if(c == '.') {
            return pct + std::string("dot;");
        }
        else if(c == '$') {
            return pct + std::string("dollar;");
        }
        else if(c == '^') {
            return pct + std::string("carat;");
        }
        else if(c == '*') {
            return pct + std::string("star;");
        }
        else if(c == '+') {
            return pct + std::string("plus;");
        }
        else if(c == '?') {
            return pct + std::string("question;");
        }
        else if(c == '|') {
            return pct + std::string("pipe;");
        }
        else if(c == '(') {
            return pct + std::string("lparen;");
        }
        else if(c == ')') {
            return pct + std::string("rparen;");
        }
        else if(c == '[') {
            return pct + std::string("lbracket;");
        }
        else if(c == ']') {
            return pct + std::string("rbracket;");
        }
        else if(c == '{') {
            return pct + std::string("lbrace;");
        }
        else if(c == '}') {
            return pct + std::string("rbrace;");
        }
        else {
            if(' ' <= c && c <= '~') {
                return std::to_string(c);
            }
            else {
                char buf[64];
                sprintf(buf, "u%x;", c);

                return pct + std::string(std::string(buf) + ";");
            }
        }
    }

    BSQLiteralRe* BSQLiteralRe::parse(json j)
    {
        auto litstr = j[1]["escstr"].get<std::string>();
        std::u32string utf32 = std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t>{}.from_bytes(litstr);

        return new BSQLiteralRe(utf32);
    }

    StateID BSQLiteralRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        for(int64_t i = this->litstr.size() - 1; i >= 0; --i) {
            auto thisstate = (StateID)states.size();
            states.push_back(new NFAOptCharCode(thisstate, this->litstr[i], follows));

            follows = thisstate;
        }

        return follows;
    }

    std::string BSQCharRangeRe::escapeCode(CharCode c)
    {
        auto pct = "%";
        if(c == '/') {
            return pct + std::string("slash;");
        }
        else if( c == '%') {
            return pct + std::string("percent;");
        }
        else if(c == '\n') {
            return pct + std::string("newline;");
        }
        else if(c == '\t') {
            return pct + std::string("tab;");
        }
        else if(c == '^') {
            return pct + std::string("carat;");
        }
        else if(c == '-') {
            return pct + std::string("dash;");
        }
        else if(c == '[') {
            return pct + std::string("lbracket;");
        }
        else if(c == ']') {
            return pct + std::string("rbracket;");
        }
        else {
            if(' ' <= c && c <= '~') {
                return std::to_string(c);
            }
            else {
                char buf[64];
                sprintf(buf, "u%x;", c);

                return pct + std::string(std::string(buf) + ";");
            }
        }
    }

    BSQCharRangeRe* BSQCharRangeRe::parse(json j)
    {
        const bool compliment = j[1]["compliment"].get<bool>();

        std::vector<SingleCharRange> ranges;
        auto jranges = j[1]["range"];
        std::transform(jranges.cbegin(), jranges.cend(), std::back_inserter(ranges), [](const json& rv) {
            auto lb = rv["lb"].get<CharCode>();
            auto ub = rv["ub"].get<CharCode>();

            return SingleCharRange{lb, ub};
        });

        return new BSQCharRangeRe(compliment, ranges);
    }

    StateID BSQCharRangeRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptRange(thisstate, this->compliment, this->ranges, follows));

        return thisstate;
    }

    BSQCharClassDotRe* BSQCharClassDotRe::parse(json j)
    {
        return new BSQCharClassDotRe();
    }

    StateID BSQCharClassDotRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptDot(thisstate, follows));

        return thisstate;
    }

    BSQStarRepeatRe* BSQStarRepeatRe::parse(json j)
    {
        auto repeat = BSQRegexOpt::parse(j[1]["repeat"]);

        return new BSQStarRepeatRe(repeat);
    }

    StateID BSQStarRepeatRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        auto thisstate = (StateID)states.size();
        states.push_back(nullptr); //placeholder

        auto optfollows = this->opt->compile(thisstate, states);
        states[thisstate] = new NFAOptStar(thisstate, optfollows, follows);

        auto altstate = (StateID)states.size();
        states.push_back(new NFAOptAlternate(altstate, { optfollows, follows }));

        return altstate;
    }

    BSQPlusRepeatRe* BSQPlusRepeatRe::parse(json j)
    {
        auto repeat = BSQRegexOpt::parse(j[1]["repeat"]);

        return new BSQPlusRepeatRe(repeat);
    }

    StateID BSQPlusRepeatRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        auto thisstate = (StateID)states.size();
        states.push_back(nullptr); //placeholder

        auto optfollows = this->opt->compile(thisstate, states);
        states[thisstate] = new NFAOptStar(thisstate, optfollows, follows);

        return thisstate;
    }

    BSQRangeRepeatRe* BSQRangeRepeatRe::parse(json j)
    {
        auto min = j[1]["min"].get<uint8_t>();
        auto max = j[1]["max"].get<uint8_t>();
        auto repeat = BSQRegexOpt::parse(j[1]["repeat"]);

        return new BSQRangeRepeatRe(min, max, repeat);
    }

    StateID BSQRangeRepeatRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        auto followfinal = follows;
        for(int64_t i = this->high; i > this->low; --i) {
            auto followopt = this->opt->compile(follows, states);

            auto thisstate = (StateID)states.size();
            states.push_back(new NFAOptAlternate(thisstate, { followopt, followfinal }));

            follows = thisstate;
        }

        for(int64_t i = this->low; i > 0; --i) {
            follows = this->opt->compile(follows, states);
        }

        return follows;
    }

    BSQOptionalRe* BSQOptionalRe::parse(json j)
    {
        auto opt = BSQRegexOpt::parse(j[1]["opt"]);

        return new BSQOptionalRe(opt);
    }

    StateID BSQOptionalRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        auto followopt = this->opt->compile(follows, states);

        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptAlternate(thisstate, { followopt, follows }));

        return thisstate;
    }

    BSQAlternationRe* BSQAlternationRe::parse(json j)
    {
        std::vector<const BSQRegexOpt*> opts;
        auto jopts = j[1]["opts"];
        std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(opts), [](json arg) {
            return BSQRegexOpt::parse(arg);
        });

        return new BSQAlternationRe(opts);
    }

    StateID BSQAlternationRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        std::vector<StateID> followopts;
        for(size_t i = 0; i < this->opts.size(); ++i) {
            followopts.push_back(this->opts[i]->compile(follows, states));
        }

        auto thisstate = (StateID)states.size();
        states.push_back(new NFAOptAlternate(thisstate, followopts));

        return thisstate;
    }

    BSQSequenceRe* BSQSequenceRe::parse(json j)
    {
        std::vector<const BSQRegexOpt*> elems;
        auto jopts = j[1]["elems"];
        std::transform(jopts.cbegin(), jopts.cend(), std::back_inserter(elems), [](json arg) {
            return BSQRegexOpt::parse(arg);
        });

        return new BSQSequenceRe(elems);
    }

    StateID BSQSequenceRe::compile(StateID follows, std::vector<NFAOpt*>& states) const
    {
        for(int64_t i = this->opts.size() - 1; i >= 0; --i) {
            follows = this->opts[i]->compile(follows, states);
        }

        return follows;
    }

    BSQRegex* BSQRegex::jparse(json j)
    {
        auto bsqre = BSQRegexOpt::parse(j["re"]);

        std::vector<NFAOpt*> nfastates = { new NFAOptAccept(0) };
        auto nfastart = bsqre->compile(0, nfastates);

        auto nfare = new NFA(nfastart, 0, nfastates);
        return new BSQRegex(bsqre, nfare);
    }
}
