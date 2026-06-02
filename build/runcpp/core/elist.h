#pragma once

#include "../common.h"

namespace ᐸRuntimeᐳ 
{
    template<typename T1, typename T2>
    class EList2
    {
    public:
        T1 first;
        T2 second;

        template<size_t idx, typename T>
        constexpr T at() const
        {
            static_assert(idx < 2, "Index out of bounds for EList2");
            if constexpr (idx == 0) {
                return this->first;
            }
            else {
                return this->second;
            }
        }
    };

    template<typename T1, typename T2, typename T3>
    class EList3
    {
    public:
        T1 first;
        T2 second;
        T3 third;

        template<size_t idx, typename T>
        constexpr T at() const
        {
            static_assert(idx < 3, "Index out of bounds for EList3");
            if constexpr (idx == 0) {
                return this->first;
            }
            else if constexpr (idx == 1) {
                return this->second;
            }
            else {
                return this->third;
            }
        }
    };

    template<typename T1, typename T2, typename T3, typename T4>
    class EList4
    {
    public:
        T1 first;
        T2 second;
        T3 third;
        T4 fourth;

        template<size_t idx, typename T>
        constexpr T at() const
        {
            static_assert(idx < 4, "Index out of bounds for EList4");

            if constexpr (idx == 0) {
                return this->first;
            }
            else if constexpr (idx == 1) {
                return this->second;
            }
            else if constexpr (idx == 2) {
                return this->third;
            }
            else {
                return this->fourth;
            }
        }
    };
}
