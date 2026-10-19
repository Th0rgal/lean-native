#include "lean_native_runtime.h"
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#ifdef __APPLE__

#import <Foundation/Foundation.h>
#import <Metal/Metal.h>

static const char* LEAN_NATIVE_EMBEDDED_METAL_SOURCE =
    "#include <metal_stdlib>\n"
    "using namespace metal;\n"
    "\n"
    "kernel void lean_native_kernel_saxpy(\n"
    "    device const ulong* x [[buffer(0)]],\n"
    "    device const ulong* y [[buffer(1)]],\n"
    "    device ulong* out [[buffer(2)]],\n"
    "    constant ulong& alpha [[buffer(3)]],\n"
    "    constant ulong& n [[buffer(4)]],\n"
    "    uint gid [[thread_position_in_grid]]\n"
    ") {\n"
    "    if ((ulong)gid < n) {\n"
    "        out[gid] = alpha * x[gid] + y[gid];\n"
    "    }\n"
    "}\n"
    "\n"
    "kernel void lean_native_kernel_matmul_tiled_u64(\n"
    "    device const ulong* A [[buffer(0)]],\n"
    "    device const ulong* B [[buffer(1)]],\n"
    "    device ulong* C [[buffer(2)]],\n"
    "    constant ulong& dim [[buffer(3)]],\n"
    "    uint2 gid [[thread_position_in_grid]],\n"
    "    uint2 tid [[thread_position_in_threadgroup]],\n"
    "    uint2 ctaid [[threadgroup_position_in_grid]]\n"
    ") {\n"
    "    threadgroup ulong tileA[256];\n"
    "    threadgroup ulong tileB[256];\n"
    "    ulong row = (ulong)(ctaid.y * 16u + tid.y);\n"
    "    ulong col = (ulong)(ctaid.x * 16u + tid.x);\n"
    "    ulong acc = 0UL;\n"
    "    ulong num_tiles = (dim + 15UL) / 16UL;\n"
    "    for (ulong t = 0UL; t < num_tiles; ++t) {\n"
    "        ulong a_col = t * 16UL + (ulong)tid.x;\n"
    "        ulong b_row = t * 16UL + (ulong)tid.y;\n"
    "        tileA[tid.y * 16u + tid.x] = (row < dim && a_col < dim) ? A[row * dim + a_col] : 0UL;\n"
    "        tileB[tid.y * 16u + tid.x] = (b_row < dim && col < dim) ? B[b_row * dim + col] : 0UL;\n"
    "        threadgroup_barrier(mem_flags::mem_threadgroup);\n"
    "        for (uint k = 0u; k < 16u; ++k) {\n"
    "            acc += tileA[tid.y * 16u + k] * tileB[k * 16u + tid.x];\n"
    "        }\n"
    "        threadgroup_barrier(mem_flags::mem_threadgroup);\n"
    "    }\n"
    "    if (row < dim && col < dim) {\n"
    "        C[row * dim + col] = acc;\n"
    "    }\n"
    "}\n";

static id<MTLDevice> g_mtl_device = nil;
static id<MTLCommandQueue> g_mtl_queue = nil;
static id<MTLLibrary> g_mtl_library = nil;
static id<MTLComputePipelineState> g_mtl_saxpy_pso = nil;
static id<MTLComputePipelineState> g_mtl_matmul_pso = nil;
static int g_mtl_initialized = 0;
static char g_mtl_device_name[256] = "Apple Metal Unavailable (CPU Fallback)";

static int lean_native_ensure_metal_initialized(void) {
    if (g_mtl_initialized) {
        return g_mtl_device != nil && g_mtl_queue != nil && g_mtl_library != nil;
    }
    g_mtl_initialized = 1;
    @autoreleasepool {
        g_mtl_device = MTLCreateSystemDefaultDevice();
        if (!g_mtl_device) {
            return 0;
        }
        const char* utf8_name = [[g_mtl_device name] UTF8String];
        if (utf8_name) {
            strncpy(g_mtl_device_name, utf8_name, sizeof(g_mtl_device_name) - 1);
            g_mtl_device_name[sizeof(g_mtl_device_name) - 1] = '\0';
        }
        g_mtl_queue = [g_mtl_device newCommandQueue];
        if (!g_mtl_queue) {
            return 0;
        }
        NSError* err = nil;
        NSString* src = [NSString stringWithUTF8String:LEAN_NATIVE_EMBEDDED_METAL_SOURCE];
        MTLCompileOptions* opts = [[MTLCompileOptions alloc] init];
        g_mtl_library = [g_mtl_device newLibraryWithSource:src options:opts error:&err];
        if (!g_mtl_library || err != nil) {
            return 0;
        }
        id<MTLFunction> fn_saxpy = [g_mtl_library newFunctionWithName:@"lean_native_kernel_saxpy"];
        if (fn_saxpy) {
            g_mtl_saxpy_pso = [g_mtl_device newComputePipelineStateWithFunction:fn_saxpy error:&err];
        }
        id<MTLFunction> fn_matmul = [g_mtl_library newFunctionWithName:@"lean_native_kernel_matmul_tiled_u64"];
        if (fn_matmul) {
            g_mtl_matmul_pso = [g_mtl_device newComputePipelineStateWithFunction:fn_matmul error:&err];
        }
    }
    return (g_mtl_saxpy_pso != nil && g_mtl_matmul_pso != nil) ? 1 : 0;
}

int lean_native_metal_available(void) {
    return lean_native_ensure_metal_initialized();
}

const char* lean_native_metal_device_name(void) {
    lean_native_ensure_metal_initialized();
    return g_mtl_device_name;
}

int lean_native_metal_validate_msl(const char* msl_src) {
    if (!msl_src || msl_src[0] == '\0') {
        return 0;
    }
    if (!strstr(msl_src, "#include <metal_stdlib>") ||
        !strstr(msl_src, "[[buffer(") ||
        !strstr(msl_src, "[[thread_position_in_grid]]")) {
        return 0;
    }
    if (lean_native_ensure_metal_initialized()) {
        @autoreleasepool {
            NSError* err = nil;
            NSString* src = [NSString stringWithUTF8String:msl_src];
            MTLCompileOptions* opts = [[MTLCompileOptions alloc] init];
            id<MTLLibrary> lib = [g_mtl_device newLibraryWithSource:src options:opts error:&err];
            return (lib != nil && err == nil) ? 1 : 0;
        }
    }
    return 1;
}

int lean_native_metal_launch_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
) {
    if (!out || !x || !y) {
        return -1;
    }
    if (n == 0) {
        return 0;
    }
    if (lean_native_ensure_metal_initialized() && g_mtl_saxpy_pso != nil) {
        @autoreleasepool {
            size_t bytes = n * sizeof(uint64_t);
            /* Zero-copy unified-memory buffers on Apple Silicon (M1/M2/M3/M4) when page-aligned */
            id<MTLBuffer> buf_x = [g_mtl_device newBufferWithBytesNoCopy:(void*)x
                                                                  length:bytes
                                                                 options:MTLResourceStorageModeShared
                                                             deallocator:nil];
            id<MTLBuffer> buf_y = [g_mtl_device newBufferWithBytesNoCopy:(void*)y
                                                                  length:bytes
                                                                 options:MTLResourceStorageModeShared
                                                             deallocator:nil];
            id<MTLBuffer> buf_out = [g_mtl_device newBufferWithBytesNoCopy:(void*)out
                                                                    length:bytes
                                                                   options:MTLResourceStorageModeShared
                                                               deallocator:nil];
            int used_nocopy = (buf_x != nil && buf_y != nil && buf_out != nil);
            if (!used_nocopy) {
                buf_x = [g_mtl_device newBufferWithBytes:x length:bytes options:MTLResourceStorageModeShared];
                buf_y = [g_mtl_device newBufferWithBytes:y length:bytes options:MTLResourceStorageModeShared];
                buf_out = [g_mtl_device newBufferWithLength:bytes options:MTLResourceStorageModeShared];
            }
            if (buf_x && buf_y && buf_out) {
                uint64_t n_u64 = (uint64_t)n;
                id<MTLCommandBuffer> cmd = [g_mtl_queue commandBuffer];
                id<MTLComputeCommandEncoder> enc = [cmd computeCommandEncoder];
                [enc setComputePipelineState:g_mtl_saxpy_pso];
                [enc setBuffer:buf_x offset:0 atIndex:0];
                [enc setBuffer:buf_y offset:0 atIndex:1];
                [enc setBuffer:buf_out offset:0 atIndex:2];
                [enc setBytes:&alpha length:sizeof(uint64_t) atIndex:3];
                [enc setBytes:&n_u64 length:sizeof(uint64_t) atIndex:4];
                MTLSize grid = MTLSizeMake(n, 1, 1);
                NSUInteger tg_width = g_mtl_saxpy_pso.maxTotalThreadsPerThreadgroup;
                if (tg_width > 256) tg_width = 256;
                MTLSize tg = MTLSizeMake(tg_width, 1, 1);
                [enc dispatchThreads:grid threadsPerThreadgroup:tg];
                [enc endEncoding];
                [cmd commit];
                [cmd waitUntilCompleted];
                if (!used_nocopy) {
                    memcpy(out, [buf_out contents], bytes);
                }
                return 0;
            }
        }
    }
    lean_native_cpu_saxpy_u64(out, x, y, alpha, n);
    return 0;
}

int lean_native_metal_launch_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
) {
    if (!c || !a || !b) {
        return -1;
    }
    if (m == 0 || n == 0 || k == 0) {
        return 0;
    }
    if (m == n && n == k && lean_native_ensure_metal_initialized() && g_mtl_matmul_pso != nil) {
        @autoreleasepool {
            size_t bytes = m * n * sizeof(uint64_t);
            id<MTLBuffer> buf_a = [g_mtl_device newBufferWithBytesNoCopy:(void*)a
                                                                  length:bytes
                                                                 options:MTLResourceStorageModeShared
                                                             deallocator:nil];
            id<MTLBuffer> buf_b = [g_mtl_device newBufferWithBytesNoCopy:(void*)b
                                                                  length:bytes
                                                                 options:MTLResourceStorageModeShared
                                                             deallocator:nil];
            id<MTLBuffer> buf_c = [g_mtl_device newBufferWithBytesNoCopy:(void*)c
                                                                  length:bytes
                                                                 options:MTLResourceStorageModeShared
                                                             deallocator:nil];
            int used_nocopy = (buf_a != nil && buf_b != nil && buf_c != nil);
            if (!used_nocopy) {
                buf_a = [g_mtl_device newBufferWithBytes:a length:bytes options:MTLResourceStorageModeShared];
                buf_b = [g_mtl_device newBufferWithBytes:b length:bytes options:MTLResourceStorageModeShared];
                buf_c = [g_mtl_device newBufferWithLength:bytes options:MTLResourceStorageModeShared];
            }
            if (buf_a && buf_b && buf_c) {
                uint64_t dim_u64 = (uint64_t)m;
                id<MTLCommandBuffer> cmd = [g_mtl_queue commandBuffer];
                id<MTLComputeCommandEncoder> enc = [cmd computeCommandEncoder];
                [enc setComputePipelineState:g_mtl_matmul_pso];
                [enc setBuffer:buf_a offset:0 atIndex:0];
                [enc setBuffer:buf_b offset:0 atIndex:1];
                [enc setBuffer:buf_c offset:0 atIndex:2];
                [enc setBytes:&dim_u64 length:sizeof(uint64_t) atIndex:3];
                NSUInteger groups_x = (n + 15) / 16;
                NSUInteger groups_y = (m + 15) / 16;
                MTLSize tg_groups = MTLSizeMake(groups_x, groups_y, 1);
                MTLSize tg_size = MTLSizeMake(16, 16, 1);
                [enc dispatchThreadgroups:tg_groups threadsPerThreadgroup:tg_size];
                [enc endEncoding];
                [cmd commit];
                [cmd waitUntilCompleted];
                if (!used_nocopy) {
                    memcpy(c, [buf_c contents], bytes);
                }
                return 0;
            }
        }
    }
    lean_native_cpu_matmul_u64(c, a, b, m, n, k);
    return 0;
}

#else /* Non-Apple (Linux / x86_64 / ARM64 Grace-Blackwell) C11 Fallback */

int lean_native_metal_available(void) {
    return 0;
}

const char* lean_native_metal_device_name(void) {
    return "Apple Metal Unavailable (CPU Fallback)";
}

int lean_native_metal_validate_msl(const char* msl_src) {
    if (!msl_src || msl_src[0] == '\0') {
        return 0;
    }
    if (!strstr(msl_src, "#include <metal_stdlib>")) {
        return 0;
    }
    if (!strstr(msl_src, "[[buffer(")) {
        return 0;
    }
    if (!strstr(msl_src, "[[thread_position_in_grid]]")) {
        return 0;
    }
    int open_braces = 0;
    int close_braces = 0;
    for (const char* p = msl_src; *p != '\0'; ++p) {
        if (*p == '{') open_braces++;
        else if (*p == '}') close_braces++;
    }
    if (open_braces <= 0 || open_braces != close_braces) {
        return 0;
    }
    return 1;
}

int lean_native_metal_launch_saxpy_u64(
    uint64_t* out,
    const uint64_t* x,
    const uint64_t* y,
    uint64_t alpha,
    size_t n
) {
    if (!out || !x || !y) {
        return -1;
    }
    lean_native_cpu_saxpy_u64(out, x, y, alpha, n);
    return 0;
}

int lean_native_metal_launch_matmul_u64(
    uint64_t* c,
    const uint64_t* a,
    const uint64_t* b,
    size_t m,
    size_t n,
    size_t k
) {
    if (!c || !a || !b) {
        return -1;
    }
    lean_native_cpu_matmul_u64(c, a, b, m, n, k);
    return 0;
}

#endif /* __APPLE__ */
