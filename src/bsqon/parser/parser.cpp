#include "parser.h"

namespace BSQON
{
    void Parser::recoverErrorAssumeTokenFound(UnicodeString expected, const LexerToken& found)
    {
        if(found.kind == TokenKind::TOKEN_EOF) {
            this->m_errors.push_back(ParseError::createExpectedMissing(expected, this->m_lex.m_input.size(), this->m_lex.m_input.size()));
        }
        else {
            this->m_errors.push_back(ParseError::createExpectedMissing(expected, this->m_lex.tokenStartToTextPos(found), this->m_lex.tokenEndToTextPos(found) + 1));
        }
    }

    void Parser::recoverErrorConsumeUntil(UnicodeString expected, const LexerToken& found, std::vector<TokenKind> tks)
    {
        std::sort(tks.begin(), tks.end());
        while(this->m_lex.peekToken().kind != TokenKind::TOKEN_EOF && !std::binary_search(tks.begin(), tks.end(), this->m_lex.peekToken().kind)) {
            this->m_lex.popToken();
        }

        if(found.kind == TokenKind::TOKEN_EOF) {
            this->m_errors.push_back(ParseError::createExpectedButGot(expected, found, this->m_lex.m_input.size(), this->m_lex.m_input.size()));
        }
        else {
            this->m_errors.push_back(ParseError::createExpectedButGot(expected, found, this->m_lex.tokenStartToTextPos(found), this->m_lex.tokenEndToTextPos(found)));
        }
    }
}
