#include "parser.h"

namespace BSQON
{
    void Parser::recoverErrorInsertExpected(UnicodeString expected, const LexerToken& found)
    {
        if(found.kind == TokenKind::TOKEN_EOF) {
            this->m_errors.push_back(ParseError::createExpectedMissing(expected, this->m_lex.m_input.size(), this->m_lex.m_input.size()));
        }
        else {
            this->m_errors.push_back(ParseError::createExpectedMissing(expected, this->m_lex.tokenStartToTextPos(found), this->m_lex.tokenEndToTextPos(found) + 1));
        }
    }

    void Parser::recoverErrorSynchronizeToken(UnicodeString expected, const LexerToken& found, FollowSet syncTokens, TokenKind openParen, TokenKind closeParen)
    {
        while(!this->m_lex.testToken(TokenKind::TOKEN_EOF) && this->m_lex.testToken(TokenKind::TOKEN_UNKNOWN)) {
            this->m_lex.popToken();
        }

        if(syncTokens.empty() && closeParen == TokenKind::TOKEN_CLEAR) {
            return;
        }

        std::list<TokenKind> parens;
        std::list<TokenKind> keyparens;
        if(openParen != TokenKind::TOKEN_CLEAR) {
            parens.push_front(openParen);
        }

        while(!this->m_lex.testToken(TokenKind::TOKEN_EOF) && !this->m_lex.testToken(closeParen) && !syncTokens.contains(this->m_lex.peekToken().kind)) {
            auto tk = this->m_lex.popToken();

            if(tk.kind == TokenKind::TOKEN_LPAREN || tk.kind == TokenKind::TOKEN_LBRACKET || tk.kind == TokenKind::TOKEN_LBRACE || tk.kind == TokenKind::TOKEN_LANGLE) {
                if(tk.kind == openParen) {
                    keyparens.push_front(openParen);
                }

                parens.push_front(tk.kind);
            }

            while(tk.kind != TokenKind::TOKEN_EOF) {
                tk = this->m_lex.peekToken();

                if(tk.kind == TokenKind::TOKEN_RPAREN || tk.kind == TokenKind::TOKEN_RBRACKET || tk.kind == TokenKind::TOKEN_RBRACE || tk.kind == TokenKind::TOKEN_RANGLE) {
                    if(tk.kind == closeParen) {
                        keyparens.pop_back();
                    }
                    
                    auto ii = parens.begin();
                    if(tk.kind == TokenKind::TOKEN_RPAREN) {
                        ii = std::find(parens.begin(), parens.end(), TokenKind::TOKEN_LPAREN);
                    }
                    else if(tk.kind == TokenKind::TOKEN_RBRACKET) {
                        ii = std::find(parens.begin(), parens.end(), TokenKind::TOKEN_LBRACKET);
                    }
                    else if(tk.kind == TokenKind::TOKEN_RBRACE) {
                        ii = std::find(parens.begin(), parens.end(), TokenKind::TOKEN_LBRACE);
                    }
                    else {
                        assert(tk.kind == TokenKind::TOKEN_RANGLE);
                        ii = std::find(parens.begin(), parens.end(), TokenKind::TOKEN_LANGLE);
                    }

                    parens.erase(parens.begin(), ii == parens.end() ? ii : ii++);

                    if(keyparens.empty() && tk.kind == closeParen) {
                        break;
                    }
                    else if(keyparens.empty()) {
                        break;
                    }
                    else {
                        this->m_lex.popToken();
                    }
                }
                else {
                    this->m_lex.popToken();
                }
            }
        }

        if(found.kind == TokenKind::TOKEN_EOF) {
            this->m_errors.push_back(ParseError::createExpectedButGot(expected, found, this->m_lex.m_input.size(), this->m_lex.m_input.size()));
        }
        else {
            this->m_errors.push_back(ParseError::createExpectedButGot(expected, found, this->m_lex.tokenStartToTextPos(found), this->m_lex.tokenEndToTextPos(found)));
        }
    }
}
