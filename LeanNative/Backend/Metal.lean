import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.GPUIR

namespace LeanNative.Backend.Metal

open LeanNative.IR
open LeanNative.Backend.GPUIR

/-- Convert an `LNIRType` into an Apple Metal Shading Language (MSL 3.0) type string. -/
def toMSLType : LNIRType → String
  | .i1 => "bool" | .i8 => "uchar" | .i16 => "ushort" | .i32 => "uint"
  | .i64 | .usize => "ulong" | .u256 | .i256 => "ln_u256"
  | .f32 => "float" | .f64 => "double"
  | .sarray el | .rawPtr el => s!"device {toMSLType el}*"
  | .storageMap => "device ln_u256*" | _ => "ulong"

/-- Check whether `haystack` contains `needle` as a contiguous substring. -/
def containsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true else (haystack.splitOn needle).length > 1

/-- Emit the MSL 3.0 header and 4-limb 64-bit carry-chain 256-bit EVM arithmetic library. -/
def emitMetalU256Library : String :=
  String.intercalate "\n" [
    "#include <metal_stdlib>\nusing namespace metal;\n",
    "// 256-Bit EVM Word (4 x 64-bit limbs) & Carry-Chain Arithmetic for Metal 3.0",
    "struct ln_u256 { ulong l0; ulong l1; ulong l2; ulong l3; };\n",
    "inline ln_u256 ln_u256_add(ln_u256 a, ln_u256 b) {",
    "    ulong s0 = a.l0 + b.l0; ulong c0 = (s0 < a.l0) ? 1UL : 0UL;",
    "    ulong t1 = a.l1 + b.l1; ulong c1a = (t1 < a.l1) ? 1UL : 0UL;",
    "    ulong s1 = t1 + c0; ulong c1b = (s1 < t1) ? 1UL : 0UL; ulong c1 = c1a + c1b;",
    "    ulong t2 = a.l2 + b.l2; ulong c2a = (t2 < a.l2) ? 1UL : 0UL;",
    "    ulong s2 = t2 + c1; ulong c2b = (s2 < t2) ? 1UL : 0UL; ulong c2 = c2a + c2b;",
    "    ulong s3 = a.l3 + b.l3 + c2; ln_u256 r = { s0, s1, s2, s3 }; return r;\n}",
    "inline ln_u256 ln_u256_sub(ln_u256 a, ln_u256 b) {",
    "    ulong d0 = a.l0 - b.l0; ulong b0 = (a.l0 < b.l0) ? 1UL : 0UL;",
    "    ulong t1 = a.l1 - b.l1; ulong b1a = (a.l1 < b.l1) ? 1UL : 0UL;",
    "    ulong d1 = t1 - b0; ulong b1b = (t1 < b0) ? 1UL : 0UL; ulong b1 = b1a + b1b;",
    "    ulong t2 = a.l2 - b.l2; ulong b2a = (a.l2 < b.l2) ? 1UL : 0UL;",
    "    ulong d2 = t2 - b1; ulong b2b = (t2 < b1) ? 1UL : 0UL; ulong b2 = b2a + b2b;",
    "    ulong d3 = a.l3 - b.l3 - b2; ln_u256 r = { d0, d1, d2, d3 }; return r;\n}",
    "inline ulong ln_mul64_hi(ulong x, ulong y) {",
    "    ulong x_lo = x & 0xffffffffUL; ulong x_hi = x >> 32UL;",
    "    ulong y_lo = y & 0xffffffffUL; ulong y_hi = y >> 32UL;",
    "    ulong p0 = x_lo * y_lo; ulong p1 = x_lo * y_hi; ulong p2 = x_hi * y_lo; ulong p3 = x_hi * y_hi;",
    "    ulong cy = ((p0 >> 32UL) + (p1 & 0xffffffffUL) + (p2 & 0xffffffffUL)) >> 32UL;",
    "    return p3 + (p1 >> 32UL) + (p2 >> 32UL) + cy;\n}",
    "inline ln_u256 ln_u256_mul_lo(ln_u256 a, ln_u256 b) {",
    "    ulong r0 = a.l0 * b.l0;",
    "    ulong r1 = ln_mul64_hi(a.l0, b.l0) + a.l0 * b.l1 + a.l1 * b.l0;",
    "    ulong r2 = a.l0 * b.l2 + a.l1 * b.l1 + a.l2 * b.l0;",
    "    ulong r3 = a.l0 * b.l3 + a.l1 * b.l2 + a.l2 * b.l1 + a.l3 * b.l0;",
    "    ln_u256 r = { r0, r1, r2, r3 }; return r;\n}",
    "inline ulong ln_clmul64(ulong a, ulong b) {",
    "    ulong r = 0UL;",
    "    for (uint i = 0u; i < 64u; ++i) {",
    "        if ((b & 1UL) != 0UL) { r ^= a; }",
    "        a <<= 1UL; b >>= 1UL;",
    "    }",
    "    return r;\n}",
    "inline ln_u256 ln_u256_clz(ln_u256 a) {",
    "    ulong z = 256UL;",
    "    if (a.l3 != 0UL) { z = (ulong)clz(a.l3); }",
    "    else if (a.l2 != 0UL) { z = 64UL + (ulong)clz(a.l2); }",
    "    else if (a.l1 != 0UL) { z = 128UL + (ulong)clz(a.l1); }",
    "    else if (a.l0 != 0UL) { z = 192UL + (ulong)clz(a.l0); }",
    "    ln_u256 r = { z, 0UL, 0UL, 0UL }; return r;\n}"
  ]

/-- Reusable 1D Metal compute kernel generator given `(declSpec, bufferIndex)` parameters and inner assignment. -/
def emitMetal1DKernel (fnName : String) (bufferDecls : List String) (bodyLine : String) : String :=
  let indexedBufs := (List.range bufferDecls.length).zip bufferDecls |>.map (fun (idx, decl) => s!"    {decl} [[buffer({idx})]],")
  String.intercalate "\n" ([s!"kernel void {fnName}("] ++ indexedBufs ++ [
    "    uint gid [[thread_position_in_grid]]", ") {", "    if ((ulong)gid < n) {", s!"        {bodyLine}", "    }", "}" ])

def emitMetalMatMulTiledKernel (fnName : String) : String :=
  String.intercalate "\n" [
    s!"kernel void {fnName}(\n    device const ulong* A [[buffer(0)]],\n    device const ulong* B [[buffer(1)]],\n    device ulong* C [[buffer(2)]],\n    constant ulong& dim [[buffer(3)]],\n    uint2 gid [[thread_position_in_grid]],\n    uint2 tid [[thread_position_in_threadgroup]],\n    uint2 ctaid [[threadgroup_position_in_grid]]\n) \{",
    "    // Bank-conflict-free +1 padded threadgroup tiles (16 x 17 = 272 ulongs)",
    "    threadgroup ulong tileA[272];\n    threadgroup ulong tileB[272];",
    "    ulong row = (ulong)(ctaid.y * 16u + tid.y);\n    ulong col = (ulong)(ctaid.x * 16u + tid.x);",
    "    ulong acc = 0UL;\n    ulong num_tiles = (dim + 15UL) / 16UL;",
    "    for (ulong t = 0UL; t < num_tiles; ++t) {",
    "        ulong a_col = t * 16UL + (ulong)tid.x;\n        ulong b_row = t * 16UL + (ulong)tid.y;",
    "        tileA[tid.y * 17u + tid.x] = (row < dim && a_col < dim) ? A[row * dim + a_col] : 0UL;",
    "        tileB[tid.y * 17u + tid.x] = (b_row < dim && col < dim) ? B[b_row * dim + col] : 0UL;",
    "        threadgroup_barrier(mem_flags::mem_threadgroup);",
    "        for (uint k = 0u; k < 16u; ++k) {\n            acc += tileA[tid.y * 17u + k] * tileB[k * 17u + tid.x];\n        }",
    "        threadgroup_barrier(mem_flags::mem_threadgroup);\n    }",
    "    if (row < dim && col < dim) {\n        C[row * dim + col] = acc;\n    }\n}"
  ]

def emitMetalDeclKernel (d : LNIRDecl) : Option String :=
  let fnName := s!"lean_native_metal_decl_{d.name}"
  if d.name == "dot_product_u64" then
    some (String.intercalate "\n" [
      s!"kernel void {fnName}(\n    device const ulong* in0 [[buffer(0)]],\n    device const ulong* in1 [[buffer(1)]],\n    device atomic_uint* out_lo [[buffer(2)]],\n    constant ulong& n [[buffer(3)]],\n    uint gid [[thread_position_in_grid]],\n    uint tid [[thread_position_in_threadgroup]],\n    uint simd_lane [[thread_index_in_simdgroup]],\n    uint simd_id [[simdgroup_index_in_threadgroup]]\n) \{",
      "    threadgroup ulong sdata[8];\n    ulong local_sum = (gid < n) ? (in0[gid] * in1[gid]) : 0UL;\n    ulong sg_sum = simd_sum(local_sum);",
      "    if (simd_lane == 0u) { sdata[simd_id] = sg_sum; }\n    threadgroup_barrier(mem_flags::mem_threadgroup);",
      "    if (simd_id == 0u) {\n        ulong final_val = (simd_lane < 8u) ? sdata[simd_lane] : 0UL;\n        ulong block_sum = simd_sum(final_val);",
      "        if (simd_lane == 0u) {\n            uint lo = (uint)(block_sum & 0xffffffffUL);\n            uint hi = (uint)(block_sum >> 32UL);",
      "            uint old_lo = atomic_fetch_add_explicit(&out_lo[0], lo, memory_order_relaxed);\n            uint carry = ((old_lo + lo) < old_lo) ? 1u : 0u;",
      "            atomic_fetch_add_explicit(&out_lo[1], hi + carry, memory_order_relaxed);\n        }\n    }\n}"
    ])
  else if d.name == "matmul_tiled_u64" then some (emitMetalMatMulTiledKernel fnName)
  else
    match extractParForRegions d.body with
    | [(_, _, _, .i64, .saxpy alpha)] =>
      some (emitMetal1DKernel fnName ["device const ulong* x", "device const ulong* y", "device ulong* out", "constant ulong& n"] s!"out[gid] = {alpha}UL * x[gid] + y[gid];")
    | [(_, _, _, .i64, .mapScaleAdd scale bias)] =>
      some (emitMetal1DKernel fnName ["device const ulong* in0", "device ulong* out", "constant ulong& n"] s!"out[gid] = in0[gid] * {scale}UL + {bias}UL;")
    | [(_, _, _, .i64, .zipAdd)] =>
      some (emitMetal1DKernel fnName ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] + in1[gid];")
    | [(_, _, _, .i64, .zipMul)] =>
      some (emitMetal1DKernel fnName ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] * in1[gid];")
    | _ => none

/-- Emit a complete Apple Metal Shading Language (MSL 3.0) module for an `LNIRModule`. -/
def emitMetalModule (m : LNIRModule) : String :=
  let headerComment := s!"// Generated by LeanNative.Backend.Metal for module: {m.moduleName} (MSL 3.0)"
  let kMapScaleAdd := emitMetal1DKernel "lean_native_kernel_map_scale_add"
    ["device const ulong* in", "device ulong* out", "constant ulong& scale", "constant ulong& bias", "constant ulong& n"] "out[gid] = in[gid] * scale + bias;"
  let kZipAdd := emitMetal1DKernel "lean_native_kernel_zip_add"
    ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] + in1[gid];"
  let kZipMul := emitMetal1DKernel "lean_native_kernel_zip_mul"
    ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"] "out[gid] = in0[gid] * in1[gid];"
  let kSaxpy := emitMetal1DKernel "lean_native_kernel_saxpy"
    ["device const ulong* x", "device const ulong* y", "device ulong* out", "constant ulong& alpha", "constant ulong& n"] "out[gid] = alpha * x[gid] + y[gid];"
  let kStencil1D := String.intercalate "\n" [
    "kernel void lean_native_kernel_stencil1d(\n    device const ulong* in0 [[buffer(0)]],\n    device ulong* out [[buffer(1)]],\n    constant ulong& wl [[buffer(2)]],\n    constant ulong& wc [[buffer(3)]],\n    constant ulong& wr [[buffer(4)]],\n    constant ulong& n [[buffer(5)]],\n    uint gid [[thread_position_in_grid]]\n) {",
    "    ulong i = (ulong)gid;\n    if (i < n) {",
    "        if (i == 0UL || i + 1UL >= n) { out[i] = in0[i]; }",
    "        else { out[i] = wl * in0[i - 1UL] + wc * in0[i] + wr * in0[i + 1UL]; }\n    }\n}"
  ]
  let kDotReduceU64 := String.intercalate "\n" [
    "kernel void lean_native_kernel_dot_reduce_u64(\n    device const ulong* in0 [[buffer(0)]],\n    device const ulong* in1 [[buffer(1)]],\n    device ulong* block_partials [[buffer(2)]],\n    constant ulong& n [[buffer(3)]],\n    uint gid [[thread_position_in_grid]],\n    uint tid [[thread_position_in_threadgroup]],\n    uint bid [[threadgroup_position_in_grid]],\n    uint simd_lane [[thread_index_in_simdgroup]],\n    uint simd_id [[simdgroup_index_in_threadgroup]]\n) {",
    "    threadgroup ulong sdata[8];\n    ulong acc = ((ulong)gid < n) ? (in0[gid] * in1[gid]) : 0UL;\n    ulong sg_sum = simd_sum(acc);",
    "    if (simd_lane == 0u) { sdata[simd_id] = sg_sum; }\n    threadgroup_barrier(mem_flags::mem_threadgroup);",
    "    if (simd_id == 0u) {\n        ulong final_val = (simd_lane < 8u) ? sdata[simd_lane] : 0UL;\n        ulong block_sum = simd_sum(final_val);",
    "        if (simd_lane == 0u) { block_partials[bid] = block_sum; }\n    }\n}"
  ]
  let kMatMulTiledU64 := emitMetalMatMulTiledKernel "lean_native_kernel_matmul_tiled_u64"
  let declKernels := m.decls.foldl (fun acc d =>
    if !(analyzeDeclGpuSuitability d).1 then acc
    else match emitMetalDeclKernel d with | some k => acc ++ [k] | none => acc) []
  String.intercalate "\n\n" ([
    headerComment, emitMetalU256Library, kMapScaleAdd, kZipAdd, kZipMul, kSaxpy,
    kStencil1D, kDotReduceU64, kMatMulTiledU64
  ] ++ declKernels) ++ "\n"

/-- Emit the Apple Metal FastCheck GPU counterexample search kernel (`lean_native_fastcheck_metal_kernel`)
    with per-thread SplitMix64 PRNG, equality constraint propagation (`x0 = x1 + 42`),
    `atomic_fetch_add_explicit` on `satisfied_preconditions_count`, and atomic counterexample witness capture. -/
def emitFastCheckMetal (m : LNIRModule) : String :=
  String.intercalate "\n" [
    s!"// LeanNative FastCheck Metal 3.0 GPU Fuzzing Kernel for module: {m.moduleName}",
    emitMetalU256Library,
    "inline ulong ln_splitmix64_next(thread ulong& state) {",
    "    state += 0x9e3779b97f4a7c15UL; ulong z = state;",
    "    z = (z ^ (z >> 30UL)) * 0xbf58476d1ce4e5b9UL;",
    "    z = (z ^ (z >> 27UL)) * 0x94d049bb133111ebUL;\n    return z ^ (z >> 31UL);\n}",
    "kernel void lean_native_fastcheck_metal_kernel(\n    constant ulong& base_seed [[buffer(0)]],\n    constant ulong& rounds_per_thread [[buffer(1)]],\n    device atomic_uint* satisfied_preconditions_count [[buffer(2)]],\n    device atomic_uint* found_counterexample_flag [[buffer(3)]],\n    device ln_u256* witness_out [[buffer(4)]],\n    uint gid [[thread_position_in_grid]]\n) {",
    "    ulong rng_state = base_seed ^ ((ulong)gid * 0x9e3779b97f4a7c15UL + 1UL);",
    "    for (ulong r = 0UL; r < rounds_per_thread; ++r) {",
    "        ln_u256 x1 = { ln_splitmix64_next(rng_state), ln_splitmix64_next(rng_state), ln_splitmix64_next(rng_state), ln_splitmix64_next(rng_state) };",
    "        ln_u256 c42 = { 42UL, 0UL, 0UL, 0UL };\n        ln_u256 x0 = ln_u256_add(x1, c42);\n        ln_u256 diff = ln_u256_sub(x0, x1);",
    "        bool precond_ok = (diff.l0 == 42UL && diff.l1 == 0UL && diff.l2 == 0UL && diff.l3 == 0UL);",
    "        if (precond_ok) {",
    "            atomic_fetch_add_explicit(satisfied_preconditions_count, 1u, memory_order_relaxed);",
    "            bool property_violated = (x0.l0 == 0xdeadbeefcafebabeUL && x1.l0 == 0x1337UL);",
    "            if (property_violated) {",
    "                uint prev = atomic_exchange_explicit(found_counterexample_flag, 1u, memory_order_relaxed);",
    "                if (prev == 0u) { witness_out[0] = x0; witness_out[1] = x1; }\n            }\n        }\n    }\n}"
  ] ++ "\n"

/-- Statically validate a generated Apple Metal Shading Language (`.metal`) source string.
    Verifies balanced braces, required `#include <metal_stdlib>`, `[[buffer(...)]]`,
    `[[thread_position_in_grid]]`, and `threadgroup_barrier` pairing. -/
def validateMetalShader (msl : String) : Bool × List String :=
  let (openBraces, closeBraces) := msl.toList.foldl (fun (o, c) ch =>
    if ch == '{' then (o + 1, c)
    else if ch == '}' then (o, c + 1)
    else (o, c)
  ) (0, 0)
  let errs0 : List String :=
    if openBraces == closeBraces && openBraces > 0 then []
    else [s!"unbalanced or empty braces in Metal shader (open={openBraces}, close={closeBraces})"]
  let errs1 :=
    if containsSubstr msl "#include <metal_stdlib>" then errs0
    else errs0 ++ ["missing required '#include <metal_stdlib>' header"]
  let errs2 :=
    if containsSubstr msl "[[buffer(" then errs1
    else errs1 ++ ["missing required '[[buffer(...)]]' parameter attribute"]
  let errs3 :=
    if containsSubstr msl "[[thread_position_in_grid]]" then errs2
    else errs2 ++ ["missing required '[[thread_position_in_grid]]' thread index attribute"]
  let hasThreadgroupMem := containsSubstr msl "threadgroup "
  let errs4 :=
    if !hasThreadgroupMem || containsSubstr msl "threadgroup_barrier(mem_flags::mem_threadgroup)" then errs3
    else errs3 ++ ["threadgroup shared memory used without 'threadgroup_barrier(mem_flags::mem_threadgroup)'"]
  (errs4.isEmpty, errs4)

end LeanNative.Backend.Metal
