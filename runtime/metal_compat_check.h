#ifndef LEAN_NATIVE_METAL_COMPAT_CHECK_H
#define LEAN_NATIVE_METAL_COMPAT_CHECK_H

/* ============================================================================
 * C++14 Compatibility Header for Validating Apple Metal Shading Language (MSL)
 * Shaders on Linux via `/usr/bin/clang++ -std=c++14 -fsyntax-only`
 * ============================================================================ */

#include <stdint.h>
#include <stddef.h>

namespace metal {

typedef uint8_t  uchar;
typedef uint16_t ushort;
typedef uint32_t uint;
typedef uint64_t ulong;

struct uint2 {
    uint x;
    uint y;
};

struct ulong2 {
    ulong x;
    ulong y;
};

struct atomic_uint {
    uint val;
};

struct atomic_ulong {
    ulong val;
};

enum memory_order {
    memory_order_relaxed = 0
};

namespace mem_flags {
    enum flags {
        mem_none        = 0,
        mem_device      = 1,
        mem_threadgroup = 2,
        mem_texture     = 4
    };
}

inline void threadgroup_barrier(int flags) {
    (void)flags;
}

inline uint atomic_fetch_add_explicit(atomic_uint* obj, uint operand, memory_order order) {
    (void)order;
    uint prev = obj ? obj->val : 0u;
    if (obj) {
        obj->val += operand;
    }
    return prev;
}

inline uint atomic_exchange_explicit(atomic_uint* obj, uint desired, memory_order order) {
    (void)order;
    uint prev = obj ? obj->val : 0u;
    if (obj) {
        obj->val = desired;
    }
    return prev;
}

} /* namespace metal */

#ifndef kernel
#define kernel
#endif

#ifndef device
#define device
#endif

#ifndef constant
#define constant const
#endif

#ifndef threadgroup
#define threadgroup
#endif

#ifndef thread
#define thread
#endif

#endif /* LEAN_NATIVE_METAL_COMPAT_CHECK_H */
