#pragma once

#include "../common.h"

namespace ᐸRuntimeᐳ
{
    class UUIDv4
    {
    private:
        boost::uuids::uuid value;

    public:
        constexpr UUIDv4() noexcept : value(boost::uuids::nil_uuid()) {}
        constexpr UUIDv4(const boost::uuids::uuid& v) noexcept : value(v) {}
        constexpr UUIDv4(const UUIDv4& other) noexcept = default;

        friend constexpr bool operator<(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const UUIDv4 &lhs, const UUIDv4 &rhs) noexcept { return !(lhs.value < rhs.value); }
    };

    class UUIDv7
    {
    private:
        boost::uuids::uuid value;

    public:
        constexpr UUIDv7() noexcept : value(boost::uuids::nil_uuid()) {}
        constexpr UUIDv7(const boost::uuids::uuid& v) noexcept : value(v) {}
        constexpr UUIDv7(const UUIDv7& other) noexcept = default;

        friend constexpr bool operator<(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return lhs.value < rhs.value; }
        friend constexpr bool operator==(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return lhs.value == rhs.value; }
        friend constexpr bool operator>(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return rhs.value < lhs.value; }
        friend constexpr bool operator!=(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return !(lhs.value == rhs.value); }
        friend constexpr bool operator<=(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return !(lhs.value > rhs.value); }
        friend constexpr bool operator>=(const UUIDv7 &lhs, const UUIDv7 &rhs) noexcept { return !(lhs.value < rhs.value); }
    };
}
