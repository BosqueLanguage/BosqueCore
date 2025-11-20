#pragma once

#include "../common.h"

namespace Core 
{
    class CStrTree { } %% Internal map this to union (inline) of CStrEmpty, CStrBuff, CStrNode

    __internal entity CStrBuff provides CStrTree { } %% Internal map this to CCharBuffer of 16 ascii chars
    __internal entity CStrNode provides CStrTree { } %% Internal map this to struct with count, left and right CStrTree

    class CString
    {

    };

    class String
    {

    };
}
