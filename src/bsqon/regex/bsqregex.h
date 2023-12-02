#pragma once

#include "../common.h"

namespace BSQON
{
    struct SingleCharRange
    {
        CharCode low;
        CharCode high;
    };

    class NFAOpt
    {
    public:
        const StateID stateid;

        NFAOpt(StateID stateid) : stateid(stateid) {;}
        virtual ~NFAOpt() {;}

        virtual void advanceChar(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const
        {
            return;
        }
        
        virtual void advanceEpsilon(const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const
        {
            nstates.push_back(this->stateid);
        }
    };

    class NFAOptAccept : public NFAOpt
    {
    public:
        NFAOptAccept(StateID stateid) : NFAOpt(stateid) {;}
        virtual ~NFAOptAccept() {;}
    };

    class NFAOptCharCode : public NFAOpt
    {
    public:
        const CharCode c;
        const StateID follow;

        NFAOptCharCode(StateID stateid, CharCode c, StateID follow) : NFAOpt(stateid), c(c), follow(follow) {;}
        virtual ~NFAOptCharCode() {;}

        virtual void advanceChar(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
        {
            if(this->c == c) {
                nstates.push_back(this->follow);
            }
        }
    };

    class NFAOptRange : public NFAOpt
    {
    public:
        const bool compliment;
        const std::vector<SingleCharRange> ranges;
        const StateID follow;

        NFAOptRange(StateID stateid, bool compliment, std::vector<SingleCharRange> ranges, StateID follow) : NFAOpt(stateid), compliment(compliment), ranges(ranges), follow(follow) {;}
        virtual ~NFAOptRange() {;}

        virtual void advanceChar(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
        {
            auto chkrng = std::find_if(this->ranges.cbegin(), this->ranges.cend(), [c](const SingleCharRange& rr) {
                return (rr.low <= c && c <= rr.high);
            });

            if(!compliment) {
                if(chkrng != this->ranges.cend()) {
                    nstates.push_back(this->follow);
                }
            }
            else {
                if(chkrng == this->ranges.cend()) {
                    nstates.push_back(this->follow);
                }
            }
        }
    };

    class NFAOptDot : public NFAOpt
    {
    public:
        const StateID follow;

        NFAOptDot(StateID stateid, StateID follow) : NFAOpt(stateid), follow(follow) {;}
        virtual ~NFAOptDot() {;}

        virtual void advanceChar(CharCode c, const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
        {
            nstates.push_back(this->follow);
        }
    };

    class NFAOptAlternate : public NFAOpt
    {
    public:
        const std::vector<StateID> follows;

        NFAOptAlternate(StateID stateid, std::vector<StateID> follows) : NFAOpt(stateid), follows(follows) {;}
        virtual ~NFAOptAlternate() {;}

        virtual void advanceEpsilon(const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
        {
            for(size_t i = 0; i < this->follows.size(); ++i) {
                nfaopts[this->follows[i]]->advanceEpsilon(nfaopts, nstates);
            }
        }
    };

    class NFAOptStar : public NFAOpt
    {
    public:
        const StateID matchfollow;
        const StateID skipfollow;

        NFAOptStar(StateID stateid, StateID matchfollow, StateID skipfollow) : NFAOpt(stateid), matchfollow(matchfollow), skipfollow(skipfollow) {;}
        virtual ~NFAOptStar() {;}

        virtual void advanceEpsilon(const std::vector<NFAOpt*>& nfaopts, std::vector<StateID>& nstates) const override final
        {
            nfaopts[this->matchfollow]->advanceEpsilon(nfaopts, nstates);
            nfaopts[this->skipfollow]->advanceEpsilon(nfaopts, nstates);
        }
    };

    class NFA
    {
    public:
        const StateID startstate;
        const StateID acceptstate;

        const std::vector<NFAOpt*> nfaopts;

        NFA(StateID startstate, StateID acceptstate, std::vector<NFAOpt*> nfaopts) : startstate(startstate), acceptstate(acceptstate), nfaopts(nfaopts) 
        {
            ;
        }
        
        ~NFA() 
        {
            for(size_t i = 0; i < this->nfaopts.size(); ++i) {
                delete this->nfaopts[i];
            }
        }

        bool test(CharCodeIterator& cci) const
        {
            std::vector<StateID> cstates;
            this->nfaopts[this->startstate]->advanceEpsilon(this->nfaopts, cstates);
            
            while(cci.valid()) {
                auto cc = cci.get();
                cci.advance();

                std::vector<StateID> nstates;
                for(size_t i = 0; i < cstates.size(); ++i) {
                    this->nfaopts[cstates[i]]->advanceChar(cc, this->nfaopts, nstates);
                }

                std::sort(nstates.begin(), nstates.end());
                auto nend = std::unique(nstates.begin(), nstates.end());
                nstates.erase(nend, nstates.end());

                std::vector<StateID> estates;
                for(size_t i = 0; i < nstates.size(); ++i) {
                    this->nfaopts[nstates[i]]->advanceEpsilon(this->nfaopts, estates);
                }

                std::sort(estates.begin(), estates.end());
                auto eend = std::unique(estates.begin(), estates.end());
                estates.erase(eend, estates.end());

                cstates = std::move(estates);
                if(cstates.empty()) {
                    return false;
                }
            }

            return std::find(cstates.cbegin(), cstates.cend(), this->acceptstate) != cstates.cend();
        }
    };

    class BSQRegexOpt
    {
    public:
        BSQRegexOpt() {;}
        virtual ~BSQRegexOpt() {;}

        virtual std::string toString() const = 0;

        static BSQRegexOpt* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const = 0;

        virtual bool isLiteral() const
        {
            return false;
        }
    };

    class BSQLiteralRe : public BSQRegexOpt
    {
    public:
        UnicodeString litstr;

        BSQLiteralRe(UnicodeString litstr) : BSQRegexOpt(), litstr(litstr) {;}
        virtual ~BSQLiteralRe() {;}

        static std::string escapeCode(CharCode c);

        virtual std::string toString() const override
        {
            return std::accumulate(this->litstr.cbegin(), this->litstr.cend(), std::string(), [](std::string&& acc, CharCode c) {
                return std::move(acc) + escapeCode(c);
            });
        }

        static BSQLiteralRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;

        virtual bool isLiteral() const override
        {
            return true;
        }

        static BSQLiteralRe* mergeLiterals(const BSQLiteralRe* l1, const BSQLiteralRe* l2)
        {
            return new BSQLiteralRe(l1->litstr + l2->litstr);
        }
    };

    class BSQCharRangeRe : public BSQRegexOpt
    {
    public:
        const bool compliment;
        const std::vector<SingleCharRange> ranges;

        BSQCharRangeRe(bool compliment, std::vector<SingleCharRange> ranges) : BSQRegexOpt(), compliment(compliment), ranges(ranges) {;}
        virtual ~BSQCharRangeRe() {;}

        static std::string escapeCode(CharCode c);

        virtual std::string toString() const override
        {
            return "[" + std::accumulate(this->ranges.cbegin(), this->ranges.cend(), std::string(this->compliment ? "^" : ""), [](std::string&& acc, SingleCharRange cr) {
                if(cr.low == cr.high) {
                    return std::move(acc) + escapeCode(cr.low);
                }
                else {
                    return std::move(acc) + escapeCode(cr.low) + "-" + escapeCode(cr.high);
                }
            }) + "]";
        }

        static BSQCharRangeRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQCharClassDotRe : public BSQRegexOpt
    {
    public:
        BSQCharClassDotRe() : BSQRegexOpt() {;}
        virtual ~BSQCharClassDotRe() {;}

        virtual std::string toString() const override
        {
            return ".";
        }

        static BSQCharClassDotRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQStarRepeatRe : public BSQRegexOpt
    {
    public:
        const BSQRegexOpt* opt;

        BSQStarRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}

        virtual ~BSQStarRepeatRe() 
        {
            delete this->opt;
        }

        virtual std::string toString() const override
        {
            return "(" + this->opt->toString() + "*)";
        }

        static BSQStarRepeatRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQPlusRepeatRe : public BSQRegexOpt
    {
    public:
        const BSQRegexOpt* opt;

        BSQPlusRepeatRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
        
        virtual ~BSQPlusRepeatRe()
        {
            delete this->opt;
        }

        virtual std::string toString() const override
        {
            return "(" + this->opt->toString() + "+)";
        }

        static BSQPlusRepeatRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQRangeRepeatRe : public BSQRegexOpt
    {
    public:
        const BSQRegexOpt* opt;
        const uint16_t low;
        const uint16_t high;

        BSQRangeRepeatRe(uint16_t low, uint16_t high, const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt), low(low), high(high) {;}
        
        virtual ~BSQRangeRepeatRe() 
        {
            delete this->opt;
        }

        virtual std::string toString() const override
        {
            if(this->high == UINT16_MAX)
            {
                return "(" + this->opt->toString() + "{" + std::to_string(this->low) + ",})";
            }
            else if(this->low == this->high)
            {
                return "(" + this->opt->toString() + "{" + std::to_string(this->low) + "})";
            }
            else {
                return "(" + this->opt->toString() + "{" + std::to_string(this->low) + "," + std::to_string(this->high) + "})";
            }
        }

        static BSQRangeRepeatRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQOptionalRe : public BSQRegexOpt
    {
    public:
        const BSQRegexOpt* opt;

        BSQOptionalRe(const BSQRegexOpt* opt) : BSQRegexOpt(), opt(opt) {;}
        virtual ~BSQOptionalRe() {;}

        virtual std::string toString() const override
        {
            return "(" + this->opt->toString() + "?)";
        }

        static BSQOptionalRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQAlternationRe : public BSQRegexOpt
    {
    public:
        const std::vector<const BSQRegexOpt*> opts;

        BSQAlternationRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}

        virtual ~BSQAlternationRe()
        {
            for(size_t i = 0; i < this->opts.size(); ++i) {
                delete this->opts[i];
            }
        }

        virtual std::string toString() const override
        {
            return "(" + std::accumulate(this->opts.cbegin(), this->opts.cend(), std::string(), [](std::string&& acc, const BSQRegexOpt* re) {
                return std::move(acc) + re->toString() + "|";
            }) + ")";
        }

        static BSQAlternationRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQSequenceRe : public BSQRegexOpt
    {
    public:
        const std::vector<const BSQRegexOpt*> opts;

        BSQSequenceRe(std::vector<const BSQRegexOpt*> opts) : BSQRegexOpt(), opts(opts) {;}

        virtual ~BSQSequenceRe()
        {
            for(size_t i = 0; i < this->opts.size(); ++i) {
                delete this->opts[i];
            }
        }

        virtual std::string toString() const override
        {
            return "(" + std::accumulate(this->opts.cbegin(), this->opts.cend(), std::string(), [](std::string&& acc, const BSQRegexOpt* re) {
                return std::move(acc) + re->toString();
            }) + ")";
        }

        static BSQSequenceRe* parse(json j);
        virtual StateID compile(StateID follows, std::vector<NFAOpt*>& states) const override final;
    };

    class BSQRegex
    {
    public:
        const BSQRegexOpt* re;
        const NFA* nfare;

        BSQRegex(const BSQRegexOpt* re, NFA* nfare): re(re), nfare(nfare) {;}
        ~BSQRegex() {;}

        static BSQRegex* jparse(json j);

        std::string toString() const 
        {
            return re->toString();
        }

        bool test(CharCodeIterator& cci) const
        {
            return this->nfare->test(cci);
        }

        bool test(const UnicodeString* s) const
        {
            UnicodeIterator siter(s);
            return this->nfare->test(siter);
        }

        bool test(const std::string* s) const
        {
            ASCIIIterator siter(s);
            return this->nfare->test(siter);
        }
    };

    class RegexParser 
    {
    private:
        UnicodeString restr;
        size_t pos;

        RegexParser(const UnicodeString& restr) : restr(restr), pos(0) { ; }

        bool done()
        {
            return this->restr.size() <= this->pos;
        }

        bool isToken(CharCode tk)
        {
            return this->restr[this->pos] == tk;
        }

        CharCode token() {
            return this->restr[this->pos];
        }

        void advance() {
            this->pos++;
        }

        void advance(size_t dist) {
            this->pos = this->pos + dist;
        }

        bool matchLiteralPrefix(UnicodeString pfx)
        {
            for(size_t i = 0; i < pfx.size(); ++i) {
                if(this->pos + i >= this->restr.size()) {
                    return false;
                }

                if(pfx[i] != this->restr[this->pos + i]) {
                    return false;
                }
            }

            return true;
        }

        CharCode readUnescapedChar()
        {
            auto c = this->token();
            this->advance();

            if(this->token() != U'%') {
                return c;
            }
            else {
                if(this->matchLiteralPrefix(U"slash;")) {
                    this->advance(6);
                    return U'/';
                }
                else if(this->matchLiteralPrefix(U"percent;")) {
                    this->advance(8);
                    return U'%';
                }
                else if(this->matchLiteralPrefix(U"newline;")) {
                    this->advance(8);
                    return U'\n';
                }
                else if(this->matchLiteralPrefix(U"tab;")) {
                    this->advance(4);
                    return U'\t';
                }
                else if(this->matchLiteralPrefix(U"dot;")) {
                    this->advance(4);
                    return U'.';
                }
                else if(this->matchLiteralPrefix(U"dollar;")) {
                    this->advance(7);
                    return U'$';
                }
                else if(this->matchLiteralPrefix(U"carat;")) {
                    this->advance(6);
                    return U'^';
                }
                else if(this->matchLiteralPrefix(U"star;")) {
                    this->advance(5);
                    return U'*';
                }
                else if(this->matchLiteralPrefix(U"plus;")) {
                    this->advance(5);
                    return U'+';
                }
                else if(this->matchLiteralPrefix(U"question;")) {
                    this->advance(9);
                    return U'?';
                }
                else if(this->matchLiteralPrefix(U"pipe;")) {
                    this->advance(5);
                    return U'|';
                }
                else if(this->matchLiteralPrefix(U"lparen;")) {
                    this->advance(7);
                    return U'(';
                }
                else if(this->matchLiteralPrefix(U"rparen;")) {
                    this->advance(7);
                    return U')';
                }
                else if(this->matchLiteralPrefix(U"lbracket;")) {
                    this->advance(9);
                    return U'[';
                }
                else if(this->matchLiteralPrefix(U"rbracket;")) {
                    this->advance(9);
                    return U']';
                }
                else if(this->matchLiteralPrefix(U"lbrace;")) {
                    this->advance(7);
                    return U'{';
                }
                else if(this->matchLiteralPrefix(U"rbrace;")) {
                    this->advance(7);
                    return U'}';
                }
                else {
                    uint32_t cc = 0;
                    while(!this->done() && U'0' < this->token() && this->token() < U'9') {
                        cc = cc * 10 + (this->token() - U'0');
                        this->advance();
                    }

                    if(this->done() || !this->isToken(U';')) {
                        return 0;
                    }
                    this->advance();
                    
                    return (CharCode)cc;
                }
            }
        }

        const BSQRegexOpt* parseBaseComponent() 
        {
            const BSQRegexOpt* res = nullptr;
            if(this->isToken(U'(')) {
                this->advance();

                res = this->parseComponent();
                if(!this->isToken(U')')) {
                    return nullptr;
                }

                this->advance();
            }
            else if(this->isToken(U'[')) {
                this->advance();

                auto compliment = this->isToken(U'^');
                if(compliment) {
                    this->advance();
                }

                std::vector<SingleCharRange> range;
                while(!this->isToken(U']')) {
                    auto lb = this->readUnescapedChar();

                    if (!this->isToken(U'-')) {
                        range.push_back({ lb, lb });
                    }
                    else {
                        this->advance();

                        auto ub = this->token();
                        range.push_back({ lb, ub });
                    }
                }

                if(!this->isToken(U']')) {
                    return nullptr;
                }
                this->advance();

                return new BSQCharRangeRe(compliment, range);
            }
            else {
                res = new BSQLiteralRe({ this->readUnescapedChar() });
            }

            return res;
        }

        const BSQRegexOpt* parseCharClassOrEscapeComponent()
        {
            if(this->isToken(U'.')) {
                this->advance();
                return new BSQCharClassDotRe();
            }
            else {
                return this->parseBaseComponent();
            }
        }

        const BSQRegexOpt* parseRepeatComponent()
        {
            auto rcc = this->parseCharClassOrEscapeComponent();
            if(rcc == nullptr) {
                return nullptr;
            }

            while(this->isToken(U'*') || this->isToken(U'+') || this->isToken(U'?') || this->isToken(U'{')) {
                if(this->isToken(U'*')) {
                    rcc = new BSQStarRepeatRe(rcc);
                    this->advance();
                }
                else if(this->isToken(U'+')) {
                    rcc = new BSQPlusRepeatRe(rcc);
                    this->advance();
                }
                else if(this->isToken(U'?')) {
                    rcc = new BSQOptionalRe(rcc);
                    this->advance();
                }
                else {
                    this->advance();
                    uint16_t min = 0;
                    while(!this->done() && U'0' < this->token() && this->token() < U'9') {
                        min = min * 10 + (this->token() - U'0');
                        this->advance();
                    }

                    uint16_t max = min;
                    if (!this->done() && this->isToken(U',')) {
                        this->advance();

                        max = 0;
                        while(!this->done() && U'0' < this->token() && this->token() < U'9') {
                            max = max * 10 + (this->token() - U'0');
                            this->advance();
                        }
                    }

                    if(this->done() || !this->isToken(U'}')) {
                        return nullptr;
                    }
                    this->advance();

                    rcc = new BSQRangeRepeatRe(min, max, rcc);
                }
            }   

            return rcc;
        }

        const BSQRegexOpt* parseSequenceComponent()
        {
            std::vector<const BSQRegexOpt*> sre;

            while(!this->done() && !this->isToken(U'|') && !this->isToken(U')')) {
                auto rpe = this->parseRepeatComponent();
                if(rpe == nullptr) {
                    return nullptr;
                }

                if(sre.empty()) {
                    sre.push_back(rpe);
                }
                else {
                    auto lcc = sre[sre.size() - 1];
                    if(lcc->isLiteral() && rpe->isLiteral()) {
                        sre[sre.size() - 1] = BSQLiteralRe::mergeLiterals(static_cast<const BSQLiteralRe*>(lcc), static_cast<const BSQLiteralRe*>(rpe));
                        delete lcc;
                        delete rpe;
                    }
                    else {
                        sre.push_back(rpe);
                    }
                }
            }

            if(sre.empty()) {
                return nullptr;
            }

            if (sre.size() == 1) {
                return sre[0];
            }
            else {
                return new BSQSequenceRe(sre);
            }
        }

        const BSQRegexOpt* parseAlternationComponent()
        {
            auto rpei = this->parseSequenceComponent();
            if (rpei == nullptr) {
                return nullptr;
            }

            std::vector<const BSQRegexOpt*> are = {rpei};

            while (!this->done() && this->isToken(U'|')) {
                this->advance();
                auto rpe = this->parseSequenceComponent();
                if (rpe == nullptr) {
                    return nullptr;
                }

                are.push_back(rpe);
            }

            if(are.size() == 1) {
                return are[0];
            }
            else {
                return new BSQAlternationRe(are);
            }
        }

        const BSQRegexOpt* parseComponent()
        {
            return this->parseAlternationComponent();
        }
    };
}