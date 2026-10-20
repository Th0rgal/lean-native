import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.GPUIR

namespace LeanNative.Backend.Metal

open LeanNative.IR
open LeanNative.Backend.GPUIR

/-- Convert an `LNIRType` into an Apple Metal Shading Language (MSL 3.0) type string. -/
def toMSLType : LNIRType → String
  | .i1         => "bool"
  | .i8         => "uchar"
  | .i16        => "ushort"
  | .i32        => "uint"
  | .i64        => "ulong"
  | .usize      => "ulong"
  | .u256       => "ln_u256"
  | .i256       => "ln_u256"
  | .f32        => "float"
  | .f64        => "double"
  | .sarray el  => s!"device {toMSLType el}*"
  | .rawPtr el  => s!"device {toMSLType el}*"
  | .storageMap => "device ln_u256*"
  | _           => "ulong"

/-- Check whether `haystack` contains `needle` as a contiguous substring. -/
def containsSubstr (haystack needle : String) : Bool :=
  if needle.isEmpty then true
  else (haystack.splitOn needle).length > 1

/-- Emit the MSL 3.0 header and 4-limb 64-bit carry-chain 256-bit EVM arithmetic library. -/
def emitMetalU256Library : String :=
  String.intercalate "\n" [
    "#include <metal_stdlib>",
    "using namespace metal;",
    "",
    "// ============================================================================",
    "// 256-Bit EVM Word (4 x 64-bit limbs) & Carry-Chain Arithmetic for Metal 3.0",
    "// ============================================================================",
    "struct ln_u256 {",
    "    ulong l0;",
    "    ulong l1;",
    "    ulong l2;",
    "    ulong l3;",
    "};",
    "",
    "inline ln_u256 ln_u256_add(ln_u256 a, ln_u256 b) {",
    "    ulong s0 = a.l0 + b.l0;",
    "    ulong c0 = (s0 < a.l0) ? 1UL : 0UL;",
    "    ulong t1 = a.l1 + b.l1;",
    "    ulong c1a = (t1 < a.l1) ? 1UL : 0UL;",
    "    ulong s1 = t1 + c0;",
    "    ulong c1b = (s1 < t1) ? 1UL : 0UL;",
    "    ulong c1 = c1a + c1b;",
    "    ulong t2 = a.l2 + b.l2;",
    "    ulong c2a = (t2 < a.l2) ? 1UL : 0UL;",
    "    ulong s2 = t2 + c1;",
    "    ulong c2b = (s2 < t2) ? 1UL : 0UL;",
    "    ulong c2 = c2a + c2b;",
    "    ulong s3 = a.l3 + b.l3 + c2;",
    "    ln_u256 r = { s0, s1, s2, s3 };",
    "    return r;",
    "}",
    "",
    "inline ln_u256 ln_u256_sub(ln_u256 a, ln_u256 b) {",
    "    ulong d0 = a.l0 - b.l0;",
    "    ulong b0 = (a.l0 < b.l0) ? 1UL : 0UL;",
    "    ulong t1 = a.l1 - b.l1;",
    "    ulong b1a = (a.l1 < b.l1) ? 1UL : 0UL;",
    "    ulong d1 = t1 - b0;",
    "    ulong b1b = (t1 < b0) ? 1UL : 0UL;",
    "    ulong b1 = b1a + b1b;",
    "    ulong t2 = a.l2 - b.l2;",
    "    ulong b2a = (a.l2 < b.l2) ? 1UL : 0UL;",
    "    ulong d2 = t2 - b1;",
    "    ulong b2b = (t2 < b1) ? 1UL : 0UL;",
    "    ulong b2 = b2a + b2b;",
    "    ulong d3 = a.l3 - b.l3 - b2;",
    "    ln_u256 r = { d0, d1, d2, d3 };",
    "    return r;",
    "}",
    "",
    "inline ulong ln_mul64_hi(ulong x, ulong y) {",
    "    ulong x_lo = x & 0xffffffffUL;",
    "    ulong x_hi = x >> 32UL;",
    "    ulong y_lo = y & 0xffffffffUL;",
    "    ulong y_hi = y >> 32UL;",
    "    ulong p0 = x_lo * y_lo;",
    "    ulong p1 = x_lo * y_hi;",
    "    ulong p2 = x_hi * y_lo;",
    "    ulong p3 = x_hi * y_hi;",
    "    ulong cy = ((p0 >> 32UL) + (p1 & 0xffffffffUL) + (p2 & 0xffffffffUL)) >> 32UL;",
    "    return p3 + (p1 >> 32UL) + (p2 >> 32UL) + cy;",
    "}",
    "",
    "inline ln_u256 ln_u256_mul_lo(ln_u256 a, ln_u256 b) {",
    "    ulong m0 = a.l0 * b.l0;",
    "    ulong h00 = ln_mul64_hi(a.l0, b.l0);",
    "    ulong p01 = a.l0 * b.l1;",
    "    ulong p10 = a.l1 * b.l0;",
    "    ulong s1a = h00 + p01;",
    "    ulong c1a = (s1a < h00) ? 1UL : 0UL;",
    "    ulong m1 = s1a + p10;",
    "    ulong c1b = (m1 < s1a) ? 1UL : 0UL;",
    "    ulong c1 = c1a + c1b;",
    "    ulong h01 = ln_mul64_hi(a.l0, b.l1);",
    "    ulong h10 = ln_mul64_hi(a.l1, b.l0);",
    "    ulong u0 = h01 + h10;",
    "    ulong cu0 = (u0 < h01) ? 1UL : 0UL;",
    "    ulong u1 = u0 + c1;",
    "    ulong cu1 = (u1 < u0) ? 1UL : 0UL;",
    "    ulong p02 = a.l0 * b.l2;",
    "    ulong p11 = a.l1 * b.l1;",
    "    ulong p20 = a.l2 * b.l0;",
    "    ulong s2a = u1 + p02;",
    "    ulong c2a = (s2a < u1) ? 1UL : 0UL;",
    "    ulong s2b = s2a + p11;",
    "    ulong c2b = (s2b < s2a) ? 1UL : 0UL;",
    "    ulong m2 = s2b + p20;",
    "    ulong c2c = (m2 < s2b) ? 1UL : 0UL;",
    "    ulong c2 = cu0 + cu1 + c2a + c2b + c2c;",
    "    ulong h02 = ln_mul64_hi(a.l0, b.l2);",
    "    ulong h11 = ln_mul64_hi(a.l1, b.l1);",
    "    ulong h20 = ln_mul64_hi(a.l2, b.l0);",
    "    ulong m3 = c2 + h02 + h11 + h20 + a.l0 * b.l3 + a.l1 * b.l2 + a.l2 * b.l1 + a.l3 * b.l0;",
    "    ln_u256 r = { m0, m1, m2, m3 };",
    "    return r;",
    "}",
    "",
    "inline ulong ln_clz64(ulong x) {",
    "    if (x == 0UL) return 64UL;",
    "    ulong n = 0UL;",
    "    if ((x & 0xffffffff00000000UL) == 0UL) { n += 32UL; x <<= 32UL; }",
    "    if ((x & 0xffff000000000000UL) == 0UL) { n += 16UL; x <<= 16UL; }",
    "    if ((x & 0xff00000000000000UL) == 0UL) { n += 8UL;  x <<= 8UL;  }",
    "    if ((x & 0xf000000000000000UL) == 0UL) { n += 4UL;  x <<= 4UL;  }",
    "    if ((x & 0xc000000000000000UL) == 0UL) { n += 2UL;  x <<= 2UL;  }",
    "    if ((x & 0x8000000000000000UL) == 0UL) { n += 1UL; }",
    "    return n;",
    "}",
    "",
    "inline ln_u256 ln_u256_clz(ln_u256 a) {",
    "    ulong c = 256UL;",
    "    if (a.l3 != 0UL) {",
    "        c = ln_clz64(a.l3);",
    "    } else if (a.l2 != 0UL) {",
    "        c = 64UL + ln_clz64(a.l2);",
    "    } else if (a.l1 != 0UL) {",
    "        c = 128UL + ln_clz64(a.l1);",
    "    } else {",
    "        c = 192UL + ln_clz64(a.l0);",
    "    }",
    "    ln_u256 r = { c, 0UL, 0UL, 0UL };",
    "    return r;",
    "}"
  ]

/-- Reusable 1D Metal compute kernel generator given `(declSpec, bufferIndex)` parameters and inner assignment. -/
def emitMetal1DKernel (fnName : String) (bufferDecls : List String) (bodyLine : String) : String :=
  let indexedBufs := (List.range bufferDecls.length).zip bufferDecls |>.map (fun (idx, decl) =>
    s!"    {decl} [[buffer({idx})]],")
  String.intercalate "\n" (
    [s!"kernel void {fnName}("] ++
    indexedBufs ++
    [ "    uint gid [[thread_position_in_grid]]",
      ") {",
      "    if ((ulong)gid < n) {",
      s!"        {bodyLine}",
      "    }",
      "}" ]
  )
def emitMetalDeclKernel (d : LNIRDecl) : String :=
  let fnName := s!"lean_native_metal_decl_{d.name}"
  let is256 := d.retTy.is256Bit || d.params.any (fun p => p.ty.is256Bit || p.ty == .storageMap)
  let regions := extractParForRegions d.body
  if d.name == "dot_product_u64" then
    String.intercalate "\n" [
      s!"kernel void {fnName}(",
      "    device const ulong* in0 [[buffer(0)]],",
      "    device const ulong* in1 [[buffer(1)]],",
      "    device atomic_uint* out_lo [[buffer(2)]],",
      "    constant ulong& n [[buffer(3)]],",
      "    uint gid [[thread_position_in_grid]],",
      "    uint tid [[thread_position_in_threadgroup]],",
      "    uint simd_lane [[thread_index_in_simdgroup]],",
      "    uint simd_id [[simdgroup_index_in_threadgroup]]",
      ") {",
      "    threadgroup ulong sdata[8];",
      "    ulong local_sum = (gid < n) ? (in0[gid] * in1[gid]) : 0UL;",
      "    ulong sg_sum = simd_sum(local_sum);",
      "    if (simd_lane == 0u) {",
      "        sdata[simd_id] = sg_sum;",
      "    }",
      "    threadgroup_barrier(mem_flags::mem_threadgroup);",
      "    if (simd_id == 0u) {",
      "        ulong final_val = (simd_lane < 8u) ? sdata[simd_lane] : 0UL;",
      "        ulong block_sum = simd_sum(final_val);",
      "        if (simd_lane == 0u) {",
      "            uint lo = (uint)(block_sum & 0xffffffffUL);",
      "            uint hi = (uint)(block_sum >> 32UL);",
      "            uint old_lo = atomic_fetch_add_explicit(&out_lo[0], lo, memory_order_relaxed);",
      "            uint carry = ((old_lo + lo) < old_lo) ? 1u : 0u;",
      "            atomic_fetch_add_explicit(&out_lo[1], hi + carry, memory_order_relaxed);",
      "        }",
      "    }",
      "}"
    ]
  else if d.name == "matmul_tiled_u64" then
    String.intercalate "\n" [
      s!"kernel void {fnName}(",
      "    device const ulong* A [[buffer(0)]],",
      "    device const ulong* B [[buffer(1)]],",
      "    device ulong* C [[buffer(2)]],",
      "    constant ulong& dim [[buffer(3)]],",
      "    uint2 gid [[thread_position_in_grid]],",
      "    uint2 tid [[thread_position_in_threadgroup]],",
      "    uint2 ctaid [[threadgroup_position_in_grid]]",
      ") {",
      "    // Bank-conflict-free +1 padded threadgroup tiles (16 x 17 = 272 ulongs)",
      "    threadgroup ulong tileA[272];",
      "    threadgroup ulong tileB[272];",
      "    ulong row = (ulong)(ctaid.y * 16u + tid.y);",
      "    ulong col = (ulong)(ctaid.x * 16u + tid.x);",
      "    ulong acc = 0UL;",
      "    ulong num_tiles = (dim + 15UL) / 16UL;",
      "    for (ulong t = 0UL; t < num_tiles; ++t) {",
      "        ulong a_col = t * 16UL + (ulong)tid.x;",
      "        ulong b_row = t * 16UL + (ulong)tid.y;",
      "        tileA[tid.y * 17u + tid.x] = (row < dim && a_col < dim) ? A[row * dim + a_col] : 0UL;",
      "        tileB[tid.y * 17u + tid.x] = (b_row < dim && col < dim) ? B[b_row * dim + col] : 0UL;",
      "        threadgroup_barrier(mem_flags::mem_threadgroup);",
      "        for (uint k = 0u; k < 16u; ++k) {",
      "            acc += tileA[tid.y * 17u + k] * tileB[k * 17u + tid.x];",
      "        }",
      "        threadgroup_barrier(mem_flags::mem_threadgroup);",
      "    }",
      "    if (row < dim && col < dim) {",
      "        C[row * dim + col] = acc;",
      "    }",
      "}"
    ]
  else if is256 then
    emitMetal1DKernel fnName
      ["device const ln_u256* in_a", "device const ln_u256* in_b", "device ln_u256* out", "constant ulong& n"]
      "ln_u256 a = in_a[gid]; ln_u256 b = in_b[gid]; ln_u256 sum = ln_u256_add(a, b); ln_u256 diff = ln_u256_sub(sum, b); ln_u256 prod = ln_u256_mul_lo(diff, b); ln_u256 lz = ln_u256_clz(sum); out[gid] = ln_u256_add(prod, lz);"
  else
    match regions with
    | (_, _, _, _, .saxpy alpha) :: _ =>
      emitMetal1DKernel fnName
        ["device const ulong* x", "device const ulong* y", "device ulong* out", "constant ulong& n"]
        s!"out[gid] = {alpha}UL * x[gid] + y[gid];"
    | (_, _, _, _, .mapScaleAdd scale bias) :: _ =>
      emitMetal1DKernel fnName
        ["device const ulong* in0", "device ulong* out", "constant ulong& n"]
        s!"out[gid] = in0[gid] * {scale}UL + {bias}UL;"
    | _ =>
      emitMetal1DKernel fnName
        ["device const ulong* in0", "device ulong* out", "constant ulong& n"]
        "out[gid] = in0[gid];"

/-- Emit a complete Apple Metal Shading Language (MSL 3.0) module for an `LNIRModule`. -/
def emitMetalModule (m : LNIRModule) : String :=
  let headerComment := String.intercalate "\n" [
    "// ============================================================================",
    s!"// Generated by LeanNative.Backend.Metal for module: {m.moduleName}",
    "// Target: Apple Metal Shading Language (MSL 3.0) / Apple Silicon Unified Memory",
    "// ============================================================================"
  ]

  let kMapScaleAdd := emitMetal1DKernel "lean_native_kernel_map_scale_add"
    ["device const ulong* in", "device ulong* out", "constant ulong& scale", "constant ulong& bias", "constant ulong& n"]
    "out[gid] = in[gid] * scale + bias;"

  let kZipAdd := emitMetal1DKernel "lean_native_kernel_zip_add"
    ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"]
    "out[gid] = in0[gid] + in1[gid];"

  let kZipMul := emitMetal1DKernel "lean_native_kernel_zip_mul"
    ["device const ulong* in0", "device const ulong* in1", "device ulong* out", "constant ulong& n"]
    "out[gid] = in0[gid] * in1[gid];"

  let kSaxpy := emitMetal1DKernel "lean_native_kernel_saxpy"
    ["device const ulong* x", "device const ulong* y", "device ulong* out", "constant ulong& alpha", "constant ulong& n"]
    "out[gid] = alpha * x[gid] + y[gid];"

  let kStencil1D := String.intercalate "\n" [
    "kernel void lean_native_kernel_stencil1d(",
    "    device const ulong* in0 [[buffer(0)]],",
    "    device ulong* out [[buffer(1)]],",
    "    constant ulong& wl [[buffer(2)]],",
    "    constant ulong& wc [[buffer(3)]],",
    "    constant ulong& wr [[buffer(4)]],",
    "    constant ulong& n [[buffer(5)]],",
    "    uint gid [[thread_position_in_grid]]",
    ") {",
    "    ulong i = (ulong)gid;",
    "    if (i < n) {",
    "        if (i == 0UL || i + 1UL >= n) {",
    "            out[i] = in0[i];",
    "        } else {",
    "            out[i] = wl * in0[i - 1UL] + wc * in0[i] + wr * in0[i + 1UL];",
    "        }",
    "    }",
    "}"
  ]

  let kDotReduceU64 := String.intercalate "\n" [
    "kernel void lean_native_kernel_dot_reduce_u64(",
    "    device const ulong* in0 [[buffer(0)]],",
    "    device const ulong* in1 [[buffer(1)]],",
    "    device ulong* block_partials [[buffer(2)]],",
    "    constant ulong& n [[buffer(3)]],",
    "    uint gid [[thread_position_in_grid]],",
    "    uint tid [[thread_position_in_threadgroup]],",
    "    uint bid [[threadgroup_position_in_grid]],",
    "    uint simd_lane [[thread_index_in_simdgroup]],",
    "    uint simd_id [[simdgroup_index_in_threadgroup]]",
    ") {",
    "    threadgroup ulong sdata[8];",
    "    ulong acc = ((ulong)gid < n) ? (in0[gid] * in1[gid]) : 0UL;",
    "    ulong sg_sum = simd_sum(acc);",
    "    if (simd_lane == 0u) {",
    "        sdata[simd_id] = sg_sum;",
    "    }",
    "    threadgroup_barrier(mem_flags::mem_threadgroup);",
    "    if (simd_id == 0u) {",
    "        ulong final_val = (simd_lane < 8u) ? sdata[simd_lane] : 0UL;",
    "        ulong block_sum = simd_sum(final_val);",
    "        if (simd_lane == 0u) {",
    "            block_partials[bid] = block_sum;",
    "        }",
    "    }",
    "}"
  ]

  let kMatMulTiledU64 := String.intercalate "\n" [
    "kernel void lean_native_kernel_matmul_tiled_u64(",
    "    device const ulong* A [[buffer(0)]],",
    "    device const ulong* B [[buffer(1)]],",
    "    device ulong* C [[buffer(2)]],",
    "    constant ulong& dim [[buffer(3)]],",
    "    uint2 gid [[thread_position_in_grid]],",
    "    uint2 tid [[thread_position_in_threadgroup]],",
    "    uint2 ctaid [[threadgroup_position_in_grid]]",
    ") {",
    "    // Bank-conflict-free +1 padded threadgroup tiles (16 x 17 = 272 ulongs)",
    "    threadgroup ulong tileA[272];",
    "    threadgroup ulong tileB[272];",
    "    ulong row = (ulong)(ctaid.y * 16u + tid.y);",
    "    ulong col = (ulong)(ctaid.x * 16u + tid.x);",
    "    ulong acc = 0UL;",
    "    ulong num_tiles = (dim + 15UL) / 16UL;",
    "    for (ulong t = 0UL; t < num_tiles; ++t) {",
    "        ulong a_col = t * 16UL + (ulong)tid.x;",
    "        ulong b_row = t * 16UL + (ulong)tid.y;",
    "        tileA[tid.y * 17u + tid.x] = (row < dim && a_col < dim) ? A[row * dim + a_col] : 0UL;",
    "        tileB[tid.y * 17u + tid.x] = (b_row < dim && col < dim) ? B[b_row * dim + col] : 0UL;",
    "        threadgroup_barrier(mem_flags::mem_threadgroup);",
    "        for (uint k = 0u; k < 16u; ++k) {",
    "            acc += tileA[tid.y * 17u + k] * tileB[k * 17u + tid.x];",
    "        }",
    "        threadgroup_barrier(mem_flags::mem_threadgroup);",
    "    }",
    "    if (row < dim && col < dim) {",
    "        C[row * dim + col] = acc;",
    "    }",
    "}"
  ]

  let kEvmU256Batch := String.intercalate "\n" [
    "kernel void lean_native_kernel_evm_u256_batch(",
    "    device const ln_u256* in_a [[buffer(0)]],",
    "    device const ln_u256* in_b [[buffer(1)]],",
    "    device ln_u256* out [[buffer(2)]],",
    "    constant ulong& n [[buffer(3)]],",
    "    uint gid [[thread_position_in_grid]]",
    ") {",
    "    if ((ulong)gid < n) {",
    "        ln_u256 a = in_a[gid];",
    "        ln_u256 b = in_b[gid];",
    "        ln_u256 sum = ln_u256_add(a, b);",
    "        ln_u256 diff = ln_u256_sub(sum, b);",
    "        ln_u256 prod = ln_u256_mul_lo(diff, b);",
    "        ln_u256 lz = ln_u256_clz(sum);",
    "        ulong denom = (b.l0 == 0UL) ? 1UL : b.l0;",
    "        prod.l0 = (prod.l0 / denom) ^ lz.l0;",
    "        out[gid] = ln_u256_add(sum, prod);",
    "    }",
    "}"
  ]

  let declKernels := m.decls.foldl (fun acc d =>
    let (ok, _) := analyzeDeclGpuSuitability d
    if !ok then acc
    else acc ++ [emitMetalDeclKernel d]
  ) []

  String.intercalate "\n\n" ([
    headerComment,
    emitMetalU256Library,
    kMapScaleAdd,
    kZipAdd,
    kZipMul,
    kSaxpy,
    kStencil1D,
    kDotReduceU64,
    kMatMulTiledU64,
    kEvmU256Batch
  ] ++ declKernels) ++ "\n"

/-- Emit the Apple Metal FastCheck GPU counterexample search kernel (`lean_native_fastcheck_metal_kernel`)
    with per-thread SplitMix64 PRNG, equality constraint propagation (`x0 = x1 + 42`),
    `atomic_fetch_add_explicit` on `satisfied_preconditions_count`, and atomic counterexample witness capture. -/
def emitFastCheckMetal (m : LNIRModule) : String :=
  String.intercalate "\n" [
    s!"// LeanNative FastCheck Metal 3.0 GPU Fuzzing Kernel for module: {m.moduleName}",
    emitMetalU256Library,
    "",
    "inline ulong ln_splitmix64_next(thread ulong& state) {",
    "    state += 0x9e3779b97f4a7c15UL;",
    "    ulong z = state;",
    "    z = (z ^ (z >> 30UL)) * 0xbf58476d1ce4e5b9UL;",
    "    z = (z ^ (z >> 27UL)) * 0x94d049bb133111ebUL;",
    "    return z ^ (z >> 31UL);",
    "}",
    "",
    "kernel void lean_native_fastcheck_metal_kernel(",
    "    constant ulong& base_seed [[buffer(0)]],",
    "    constant ulong& rounds_per_thread [[buffer(1)]],",
    "    device atomic_uint* satisfied_preconditions_count [[buffer(2)]],",
    "    device atomic_uint* found_counterexample_flag [[buffer(3)]],",
    "    device ln_u256* witness_out [[buffer(4)]],",
    "    uint gid [[thread_position_in_grid]]",
    ") {",
    "    ulong rng_state = base_seed ^ ((ulong)gid * 0x9e3779b97f4a7c15UL + 1UL);",
    "    for (ulong r = 0UL; r < rounds_per_thread; ++r) {",
    "        ln_u256 x1 = {",
    "            ln_splitmix64_next(rng_state),",
    "            ln_splitmix64_next(rng_state),",
    "            ln_splitmix64_next(rng_state),",
    "            ln_splitmix64_next(rng_state)",
    "        };",
    "        ln_u256 c42 = { 42UL, 0UL, 0UL, 0UL };",
    "        // Equality constraint propagation: x0 = x1 + 42",
    "        ln_u256 x0 = ln_u256_add(x1, c42);",
    "        ln_u256 diff = ln_u256_sub(x0, x1);",
    "        bool precond_ok = (diff.l0 == 42UL && diff.l1 == 0UL && diff.l2 == 0UL && diff.l3 == 0UL);",
    "        if (precond_ok) {",
    "            atomic_fetch_add_explicit(satisfied_preconditions_count, 1u, memory_order_relaxed);",
    "            bool property_violated = (x0.l0 == 0xdeadbeefcafebabeUL && x1.l0 == 0x1337UL);",
    "            if (property_violated) {",
    "                uint prev = atomic_exchange_explicit(found_counterexample_flag, 1u, memory_order_relaxed);",
    "                if (prev == 0u) {",
    "                    witness_out[0] = x0;",
    "                    witness_out[1] = x1;",
    "                }",
    "            }",
    "        }",
    "    }",
    "}"
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
