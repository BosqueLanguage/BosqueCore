#pragma once

#include <cmath>
#include <cstring>
#include <csetjmp>

#include <stdint.h>
#include <stddef.h>
#include <stdalign.h>

#include <optional>
#include <chrono>
#include <random>
#include <string>
#include <array>
#include <vector>
#include <set>
#include <unordered_set>
#include <map>
#include <list>
#include <algorithm>

#include <regex>

#include <type_traits>
#include <concepts>

#include <execution>
#include <mutex>
#include <thread>

#include <sys/mman.h> //mmap

//Boost dependencies
#include <boost/regex.hpp>
#include <boost/regex/icu.hpp>

//JSON dependency
#include <json.hpp>
using json = nlohmann::json;

//Only for diagnostics
#include <assert.h>
#include <iostream>

#include "./flags.h"

namespace ᐸRuntimeᐳ
{
    constexpr size_t MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE = 8192; //8KB blocks for buffer allocation

    class IOBufferIterator
    {
    private:
        std::list<uint8_t*>::const_iterator iobuffs;
        int64_t cindex;

        int64_t gindex;
        int64_t totalbytes;

        IOBufferIterator(std::list<uint8_t*>::const_iterator iobuffs, int64_t cindex, int64_t gindex, int64_t totalbytes) : iobuffs(iobuffs), cindex(cindex), gindex(gindex), totalbytes(totalbytes) {}

        void incrementSlow()
        {        
            this->iobuffs++;
            this->cindex = 0;
        }

        void decrementSlow()
        {        
            this->iobuffs--;
            this->cindex = MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE - 1;
        }

    public:
        using value_type = uint8_t;
        using difference_type = std::ptrdiff_t;
        using iterator_category = std::bidirectional_iterator_tag;

        using pointer = value_type*;
        using reference = value_type&;

        IOBufferIterator() : iobuffs(), cindex(0), gindex(0), totalbytes(0) {}
        IOBufferIterator(const IOBufferIterator& other) = default;
        
        static IOBufferIterator initializeBegin(std::list<uint8_t*>::const_iterator iobuffs, size_t totalbytes)
        {
            return IOBufferIterator(iobuffs, 0, 0, totalbytes);
        }

        static IOBufferIterator initializeEnd(std::list<uint8_t*>::const_iterator iobuffs, size_t totalbytes)
        {
            const size_t cindex = totalbytes % MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE;
            if(cindex != 0) {
                --iobuffs;
            }
            
            return IOBufferIterator(iobuffs, cindex, totalbytes, totalbytes);
        }

        value_type operator*() const 
        { 
            return (*this->iobuffs)[this->cindex]; 
        }

        IOBufferIterator& operator++()
        {
            this->gindex++;
            this->cindex++;
            if(this->cindex >= (int64_t)MINT_IO_BUFFER_ALLOCATOR_BLOCK_SIZE) {
                this->incrementSlow();
            }

            return *this;
        }
 
        IOBufferIterator operator++(int)
        {
            auto tmp = *this;
            ++*this;
            return tmp;
        }

        IOBufferIterator& operator--()
        {
            this->gindex--;
            this->cindex--;
            if(this->cindex < 0) {
                this->decrementSlow();
            }

            return *this;
        }
 
        IOBufferIterator operator--(int)
        {
            auto tmp = *this;
            --*this;
            return tmp;
        }
 
        friend bool operator==(const IOBufferIterator& lhs, const IOBufferIterator& rhs)
        {
            return lhs.gindex == rhs.gindex;
        }

        friend bool operator!=(const IOBufferIterator& lhs, const IOBufferIterator& rhs) 
        {
            return lhs.gindex != rhs.gindex;
        }

        inline size_t getIndex() const 
        {
            return this->gindex;
        }

        inline bool canRead() const
        {
            return this->gindex < this->totalbytes;
        }
    };
    static_assert(std::bidirectional_iterator<IOBufferIterator>);

    constexpr int64_t BSQ_NUMERIC_DYNAMIC_RANGE_BASE = 4611686018427387903ll;
    constexpr __int128_t BSQ_NUMERIC_DYNAMIC_RANGE_EXTENDED = ((__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE * (__int128_t)BSQ_NUMERIC_DYNAMIC_RANGE_BASE);

    enum class ErrorKind
    {
        Generic,
        OutOfMemory,
        RuntimeAssertion,

        NumericBounds,
        NumericUnderflow,
        DivisionByZero,

        InvalidCast,
        ExhaustiveCheck,

        UserAbort,
        UserAssertion,
        UserInvariant,
        UserValidation,
        UserPrecondition,
        UserPostcondition
    };

    class ErrorInfo
    {
    public:
        const char* file;
        uint32_t line;

        ErrorKind kerror;
        const char* tag; //optional
        const char* message; //optional
    };

    template <typename U> 
    concept ConceptUnionRepr = std::is_union<U>::value;

    //slow path error handler
    [[noreturn]] void bsq_handle_error(const char* file, uint32_t line, ErrorKind kerror, const char* tag, const char* message);


    inline void bsq_typeassert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::InvalidCast, tag, message);
        }
    }

    [[noreturn]] inline void bsq_exhaustive(const char* file, uint32_t line, const char* message)
    {
        bsq_handle_error(file, line, ErrorKind::ExhaustiveCheck, nullptr, message);
    }

    [[noreturn]] inline void bsq_abort(const char* file, uint32_t line, const char* tag, const char* message)
    {
        bsq_handle_error(file, line, ErrorKind::UserAbort, tag, message);
    }

    inline void bsq_assert(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserAssertion, tag, message);
        }
    }

    inline void bsq_validate(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserValidation, tag, message);
        }
    }

    inline void bsq_invariant(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserInvariant, tag, message);
        }
    }

    inline void bsq_requires(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserPrecondition, tag, message);
        }
    }

    inline void bsq_ensures(bool cond, const char* file, uint32_t line, const char* tag, const char* message)
    {
        if(!cond) [[unlikely]] {
            bsq_handle_error(file, line, ErrorKind::UserPostcondition, tag, message);
        }
    }

    //forward declaration of types that are stored in a thread local way
    class TaskInfo;

    class BosqueThreadLocalInfo
    {
    public:
        TaskInfo* current_task;

        BosqueThreadLocalInfo() : current_task(nullptr) {}

        // Cannot copy or move thread local info
        BosqueThreadLocalInfo(const BosqueThreadLocalInfo&) = delete;
        BosqueThreadLocalInfo &operator=(const BosqueThreadLocalInfo&) = delete;

        static void generate_uuid4(char out[16])
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }

        static void generate_uuid7(char out[16])
        {
            assert(false); //UUIDv7 generation not yet implemented;
        }
    };

    extern thread_local BosqueThreadLocalInfo tl_bosque_info;

    //See also allocator/alloc.h for allocator specific thread local and global info -- no other globals should be hanging around!
}
