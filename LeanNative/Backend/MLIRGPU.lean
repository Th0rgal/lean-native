import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.Backend.GPUIR

namespace LeanNative.Backend.MLIRGPU

open LeanNative.IR
open LeanNative.Backend.GPUIR

/-- Inspect an `LNIRExpr` for constructs incompatible with GPU execution.
    Delegates to `LeanNative.Backend.GPUIR.checkExprGpuCompatibility`. -/
def checkExprGpuCompatibility (e : LNIRExpr) : List String :=
  GPUIR.checkExprGpuCompatibility e

/-- Recursively check an `LNIRCode` block for GPU compatibility violations.
    Delegates to `LeanNative.Backend.GPUIR.checkCodeGpuCompatibility`. -/
def checkCodeGpuCompatibility (code : LNIRCode) : List String :=
  GPUIR.checkCodeGpuCompatibility code

/-- Check whether an `LNIRCode` contains at least one `parFor` data-parallel region.
    Delegates to `LeanNative.Backend.GPUIR.containsParFor`. -/
def containsParFor (code : LNIRCode) : Bool :=
  GPUIR.containsParFor code

/-- Automatic GPU suitability analyzer for an `LNIRDecl`.
    Delegates to `LeanNative.Backend.GPUIR.analyzeDeclGpuSuitability`. -/
def analyzeGpuCompatibility (d : LNIRDecl) : Bool × List String :=
  GPUIR.analyzeDeclGpuSuitability d

/-- Convert an `LNIRType` into an MLIR type string (`i64`, `i256`, `f64`, `memref<?xi64>`, etc.). -/
def toMLIRType : LNIRType → String
  | .i1         => "i1"
  | .i8         => "i8"
  | .i16        => "i16"
  | .i32        => "i32"
  | .i64        => "i64"
  | .usize      => "index"
  | .u256       => "i256"
  | .i256       => "i256"
  | .f32        => "f32"
  | .f64        => "f64"
  | .sarray el  => s!"memref<?x{toMLIRType el}>"
  | .rawPtr el  => s!"memref<?x{toMLIRType el}>"
  | .storageMap => "memref<?xi256>"
  | _           => "i64"

/-- Lower a `ScalarExpr` to MLIR `arith.*` SSA instructions, returning `(preambleLines, resultSSA)`. -/
partial def emitMLIRScalarExpr (e : ScalarExpr) (counter : Nat) : List String × String × Nat :=
  match e with
  | .constU64 v =>
    let ssa := s!"%c_{counter}"
    ([s!"      {ssa} = arith.constant {v} : i64"], ssa, counter + 1)
  | .constBool b =>
    let ssa := s!"%cb_{counter}"
    let lit := if b then "true" else "false"
    ([s!"      {ssa} = arith.constant {lit} : i1"], ssa, counter + 1)
  | .var id =>
    ([], s!"%v{id}", counter)
  | .binOp op lhs rhs =>
    let (lLines, lVal, c1) := emitMLIRScalarExpr lhs counter
    let (rLines, rVal, c2) := emitMLIRScalarExpr rhs c1
    let dst := s!"%t_{c2}"
    let instr := match op with
      | .add           => s!"{dst} = arith.addi {lVal}, {rVal} : i64"
      | .sub           => s!"{dst} = arith.subi {lVal}, {rVal} : i64"
      | .mul           => s!"{dst} = arith.muli {lVal}, {rVal} : i64"
      | .div           => s!"{dst} = arith.divui {lVal}, {rVal} : i64"
      | .mod           => s!"{dst} = arith.remui {lVal}, {rVal} : i64"
      | .bitAnd        => s!"{dst} = arith.andi {lVal}, {rVal} : i64"
      | .bitOr         => s!"{dst} = arith.ori {lVal}, {rVal} : i64"
      | .bitXor        => s!"{dst} = arith.xori {lVal}, {rVal} : i64"
      | .shl           => s!"{dst} = arith.shli {lVal}, {rVal} : i64"
      | .shr           => s!"{dst} = arith.shrui {lVal}, {rVal} : i64"
      | .sar           => s!"{dst} = arith.shrsi {lVal}, {rVal} : i64"
      | .eq            => s!"{dst} = arith.cmpi eq, {lVal}, {rVal} : i64"
      | .lt            => s!"{dst} = arith.cmpi ult, {lVal}, {rVal} : i64"
      | .le            => s!"{dst} = arith.cmpi ule, {lVal}, {rVal} : i64"
      | .addChecked256 => s!"{dst} = arith.addi {lVal}, {rVal} : i64"
      | .subChecked256 => s!"{dst} = arith.subi {lVal}, {rVal} : i64"
      | .mulChecked256 => s!"{dst} = arith.muli {lVal}, {rVal} : i64"
    (lLines ++ rLines ++ [s!"      {instr}"], dst, c2 + 1)
  | .unaryOp op arg =>
    let (aLines, aVal, c1) := emitMLIRScalarExpr arg counter
    let dst := s!"%u_{c1}"
    let instr := match op with
      | .not    => s!"%ones_{c1} = arith.constant -1 : i64\n      {dst} = arith.xori {aVal}, %ones_{c1} : i64"
      | .neg    => s!"%zero_{c1} = arith.constant 0 : i64\n      {dst} = arith.subi %zero_{c1}, {aVal} : i64"
      | .clz256 => s!"{dst} = math.ctlz {aVal} : i64"
    (aLines ++ [s!"      {instr}"], dst, c1 + 1)
  | .select cond thenVal elseVal =>
    let (cLines, cVal, c1) := emitMLIRScalarExpr cond counter
    let (tLines, tVal, c2) := emitMLIRScalarExpr thenVal c1
    let (eLines, eVal, c3) := emitMLIRScalarExpr elseVal c2
    let dst := s!"%sel_{c3}"
    (cLines ++ tLines ++ eLines ++ [s!"      {dst} = arith.select {cVal}, {tVal}, {eVal} : i64"], dst, c3 + 1)
  | .fma a b c =>
    let (aLines, aVal, c1) := emitMLIRScalarExpr a counter
    let (bLines, bVal, c2) := emitMLIRScalarExpr b c1
    let (cLines, cVal, c3) := emitMLIRScalarExpr c c2
    let mulVal := s!"%fma_mul_{c3}"
    let dst := s!"%fma_{c3}"
    (aLines ++ bLines ++ cLines ++ [
      s!"      {mulVal} = arith.muli {aVal}, {bVal} : i64",
      s!"      {dst} = arith.addi {mulVal}, {cVal} : i64"
    ], dst, c3 + 1)

/-- Emit MLIR `gpu.func` and `scf.parallel` representation for a `ParallelKernelKind`. -/
def emitMLIRKernelBody (elemTy : LNIRType) (kernel : ParallelKernelKind) : String :=
  let mlirElem := toMLIRType elemTy
  match kernel with
  | .mapScaleAdd scale bias =>
    String.intercalate "\n" [
      s!"      %in_val = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %c_scale = arith.constant {scale} : {mlirElem}",
      s!"      %c_bias = arith.constant {bias} : {mlirElem}",
      s!"      %scaled = arith.muli %in_val, %c_scale : {mlirElem}",
      s!"      %res = arith.addi %scaled, %c_bias : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .zipAdd =>
    String.intercalate "\n" [
      s!"      %lhs = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %rhs = memref.load %in1[%iv] : memref<?x{mlirElem}>",
      s!"      %res = arith.addi %lhs, %rhs : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .zipMul =>
    String.intercalate "\n" [
      s!"      %lhs = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %rhs = memref.load %in1[%iv] : memref<?x{mlirElem}>",
      s!"      %res = arith.muli %lhs, %rhs : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .saxpy alphaBits =>
    String.intercalate "\n" [
      s!"      %x_val = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %y_val = memref.load %in1[%iv] : memref<?x{mlirElem}>",
      s!"      %c_alpha = arith.constant {alphaBits} : {mlirElem}",
      s!"      %ax = arith.muli %c_alpha, %x_val : {mlirElem}",
      s!"      %res = arith.addi %ax, %y_val : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .dotProduct =>
    String.intercalate "\n" [
      s!"      %lhs = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      s!"      %rhs = memref.load %in1[%iv] : memref<?x{mlirElem}>",
      s!"      %prod = arith.muli %lhs, %rhs : {mlirElem}",
      s!"      memref.store %prod, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .stencil1D3Pt wLeft wCenter wRight =>
    String.intercalate "\n" [
      "      %c1_idx = arith.constant 1 : index",
      "      %n_minus_1 = arith.subi %n_idx, %c1_idx : index",
      "      %is_lo = arith.cmpi eq, %iv, %c0_idx : index",
      "      %is_hi = arith.cmpi uge, %iv, %n_minus_1 : index",
      "      %is_boundary = arith.ori %is_lo, %is_hi : i1",
      s!"      %center_val = memref.load %in0[%iv] : memref<?x{mlirElem}>",
      "      %iv_m1 = arith.subi %iv, %c1_idx : index",
      "      %iv_p1 = arith.addi %iv, %c1_idx : index",
      "      %safe_m1 = arith.select %is_boundary, %iv, %iv_m1 : index",
      "      %safe_p1 = arith.select %is_boundary, %iv, %iv_p1 : index",
      s!"      %left_val = memref.load %in0[%safe_m1] : memref<?x{mlirElem}>",
      s!"      %right_val = memref.load %in0[%safe_p1] : memref<?x{mlirElem}>",
      s!"      %c_wl = arith.constant {wLeft} : {mlirElem}",
      s!"      %c_wc = arith.constant {wCenter} : {mlirElem}",
      s!"      %c_wr = arith.constant {wRight} : {mlirElem}",
      s!"      %tl = arith.muli %left_val, %c_wl : {mlirElem}",
      s!"      %tc = arith.muli %center_val, %c_wc : {mlirElem}",
      s!"      %tr = arith.muli %right_val, %c_wr : {mlirElem}",
      s!"      % tlc = arith.addi %tl, %tc : {mlirElem}",
      s!"      %stencil_val = arith.addi %tlc, %tr : {mlirElem}",
      s!"      %res = arith.select %is_boundary, %center_val, %stencil_val : {mlirElem}",
      s!"      memref.store %res, %out[%iv] : memref<?x{mlirElem}>"
    ]
  | .customScalar idxVar inVars body =>
    let rec buildLoadLines (idx : Nat) : List VarId → List String
      | [] => []
      | vId :: rest =>
        let bufName := if idx == 0 then "%in0" else "%in1"
        s!"      %v{vId} = memref.load {bufName}[%iv] : memref<?x{mlirElem}>" :: buildLoadLines (idx + 1) rest
    let loadLines := buildLoadLines 0 inVars
    let idxCast := s!"      %v{idxVar} = arith.index_cast %iv : index to i64"
    let (exprLines, resVal, _) := emitMLIRScalarExpr body 0
    let storeLine := s!"      memref.store {resVal}, %out[%iv] : memref<?x{mlirElem}>"
    String.intercalate "\n" ([idxCast] ++ loadLines ++ exprLines ++ [storeLine])

/-- Extract all `(outVar, lenVar, inputs, elemTy, kernel)` regions from an `LNIRCode` tree. -/
def extractParForRegions (code : LNIRCode) :
    List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) :=
  GPUIR.extractParForRegions code

/-- Emit an MLIR `gpu.func` for a single extracted `parFor` region inside a declaration. -/
def emitMLIRGpuFunc (declName : String) (regionIdx : Nat) (elemTy : LNIRType)
    (kernel : ParallelKernelKind) : String :=
  let mlirElem := toMLIRType elemTy
  let kName := s!"@{declName}_parfor_{regionIdx}"
  let bodyStr := emitMLIRKernelBody elemTy kernel
  String.intercalate "\n" [
    s!"    gpu.func {kName}(%out: memref<?x{mlirElem}>, %in0: memref<?x{mlirElem}>, %in1: memref<?x{mlirElem}>, %n: i64) kernel attributes \{nvvm.maxntid = array<i32: 256, 1, 1>} \{",
    "      %tidx = nvvm.read.ptx.sreg.tid.x : i32",
    "      %bidx = nvvm.read.ptx.sreg.ctaid.x : i32",
    "      %bdim = nvvm.read.ptx.sreg.ntid.x : i32",
    "      %gdim = nvvm.read.ptx.sreg.nctaid.x : i32",
    "      %bid_mul = arith.muli %bidx, %bdim : i32",
    "      %gid_i32 = arith.addi %bid_mul, %tidx : i32",
    "      %stride_i32 = arith.muli %bdim, %gdim : i32",
    "      %gid = arith.index_cast %gid_i32 : i32 to index",
    "      %stride = arith.index_cast %stride_i32 : i32 to index",
    "      %c0_idx = arith.constant 0 : index",
    "      %n_idx = arith.index_cast %n : i64 to index",
    "      scf.parallel (%iv) = (%gid) to (%n_idx) step (%stride) {",
    bodyStr,
    "        scf.reduce",
    "      }",
    "      gpu.return",
    "    }"
  ]

/-- Lower GPU-compatible `LNIRDecl`s and `parFor` kernels in `m` to valid MLIR
    (`gpu.module`, `gpu.func`, `scf.parallel`, `arith.*`, `memref.*`, `nvvm.*`). -/
def emitMLIRModule (m : LNIRModule) : String :=
  let header := String.intercalate "\n" [
    s!"// LeanNative MLIR/NVVM GPU Module: {m.moduleName}",
    "module attributes {gpu.container_module} {",
    "  gpu.module @lean_native_gpu_kernels {"
  ]
  let builtinKernels := [
    emitMLIRGpuFunc "lean_native_builtin_map_scale_add" 0 .i64 (.mapScaleAdd 3 7),
    emitMLIRGpuFunc "lean_native_builtin_zip_add" 0 .i64 .zipAdd,
    emitMLIRGpuFunc "lean_native_builtin_zip_mul" 0 .i64 .zipMul,
    emitMLIRGpuFunc "lean_native_builtin_saxpy" 0 .i64 (.saxpy 5),
    emitMLIRGpuFunc "lean_native_builtin_stencil1d" 0 .i64 (.stencil1D3Pt 1 2 1)
  ]
  let declKernels := m.decls.foldl (fun acc d =>
    let (ok, _) := analyzeGpuCompatibility d
    if !ok then acc
    else
      let regions := extractParForRegions d.body
      if regions.isEmpty then
        acc ++ [emitMLIRGpuFunc d.name 0 .i64 (.mapScaleAdd 1 0)]
      else
        let rec emitRegions (idx : Nat) :
            List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) → List String
          | [] => []
          | (_, _, _, elemTy, k) :: rest =>
            emitMLIRGpuFunc d.name idx elemTy k :: emitRegions (idx + 1) rest
        acc ++ emitRegions 0 regions
  ) []
  let footer := String.intercalate "\n" [
    "  }",
    "}"
  ]
  String.intercalate "\n\n" ([header] ++ builtinKernels ++ declKernels ++ [footer]) ++ "\n"

/-- Emit a shared-memory parallel tree reduction PTX 8.0 kernel for `dot_product_u64`.
    Uses `.shared .align 8 .b8 sdata_raw[2048];` (256 x u64), grid-stride register accumulation,
    `bar.sync 0;` tree reduction (`stride = 128, 64, 32, 16, 8, 4, 2, 1`), and thread-0
    `atom.global.add.u64`. -/
def emitPTXDotReduceKernel (fnSymbol : String) : String :=
  let sharedSteps : List (Nat × Nat) := [
    (128, 1024), (64, 512), (32, 256)
  ]
  let sharedLines := sharedSteps.foldl (fun acc (stride, byteOff) =>
    acc ++ [
      s!"    setp.lt.u32   %p2, %r3, {stride};",
      s!"    @!%p2 bra     $L_red_sync_{stride}_{fnSymbol};",
      s!"    ld.shared.u64 %rd15, [%rd14+{byteOff}];",
      "    add.u64       %rd9, %rd9, %rd15;",
      "    st.shared.u64 [%rd14], %rd9;",
      s!"$L_red_sync_{stride}_{fnSymbol}:",
      "    bar.sync      0;"
    ]
  ) []
  let warpSteps : List Nat := [16, 8, 4, 2, 1]
  let warpLines := [
    "    setp.lt.u32   %p2, %r3, 32;",
    s!"    @!%p2 bra     $L_warp_done_{fnSymbol};"
  ] ++ warpSteps.foldl (fun acc offset =>
    acc ++ [
      "    mov.b64            {%r5, %r6}, %rd9;",
      s!"    shfl.sync.bfly.b32 %r7, %r5, {offset}, 31, 0xffffffff;",
      s!"    shfl.sync.bfly.b32 %r8, %r6, {offset}, 31, 0xffffffff;",
      "    mov.b64            %rd15, {%r7, %r8};",
      "    add.u64            %rd9, %rd9, %rd15;"
    ]
  ) [] ++ [
    s!"$L_warp_done_{fnSymbol}:"
  ]
  let reduceLines := sharedLines ++ warpLines
  String.intercalate "\n" ([
    s!".visible .entry {fnSymbol}(",
    "    .param .u64 param_out,",
    "    .param .u64 param_in0,",
    "    .param .u64 param_in1,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .shared .align 8 .b8 sdata_raw[2048];",
    "    .reg .pred %p<3>;",
    "    .reg .b32  %r<9>;",
    "    .reg .b64  %rd<16>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_in0];",
    "    ld.param.u64 %rd3, [param_in1];",
    "    ld.param.u64 %rd4, [param_n];",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mov.u32      %r4, %nctaid.x;",
    "    mul.wide.u32 %rd5, %r1, %r2;",
    "    cvt.u64.u32  %rd6, %r3;",
    "    add.u64      %rd7, %rd5, %rd6;",
    "    mul.wide.u32 %rd8, %r2, %r4;",
    "    mov.u64      %rd9, 0;",
    "",
    s!"$L_grid_loop_{fnSymbol}:",
    "    setp.ge.u64  %p1, %rd7, %rd4;",
    s!"    @%p1 bra     $L_grid_done_{fnSymbol};",
    "    shl.b64      %rd10, %rd7, 3;",
    "    add.u64      %rd11, %rd2, %rd10;",
    "    add.u64      %rd12, %rd3, %rd10;",
    "    ld.global.u64 %rd11, [%rd11];",
    "    ld.global.u64 %rd12, [%rd12];",
    "    mad.lo.u64   %rd9, %rd11, %rd12, %rd9;",
    "    add.u64      %rd7, %rd7, %rd8;",
    s!"    bra          $L_grid_loop_{fnSymbol};",
    "",
    s!"$L_grid_done_{fnSymbol}:",
    "    mov.u64      %rd13, sdata_raw;",
    "    shl.b64      %rd14, %rd6, 3;",
    "    add.u64      %rd14, %rd13, %rd14;",
    "    st.shared.u64 [%rd14], %rd9;",
    "    bar.sync     0;"
  ] ++ reduceLines ++ [
    "    setp.ne.u32  %p1, %r3, 0;",
    s!"    @%p1 bra     $L_done_{fnSymbol};",
    "    atom.global.add.u64 %rd15, [%rd1], %rd9;",
    "",
    s!"$L_done_{fnSymbol}:",
    "    ret;",
    "}"
  ])

/-- Emit a 2D thread-block shared-memory tiled matrix multiplication PTX 8.0 kernel (16x16 tiles,
    with +1 shared-memory column padding `16x17` = 2176 bytes to eliminate 32-way shared memory bank conflicts).
    Uses `.shared .align 8 .b8 tileA_raw[2176]; .shared .align 8 .b8 tileB_raw[2176];` (stride = 136 bytes = 17 x 8B),
    2D CTA/thread coordinates (`%ctaid.x`, `%ctaid.y`, `%tid.x`, `%tid.y`), collaborative tile loads,
    `bar.sync 0;`, unrolled 16-step `mad.lo.u64` inner product, and global store `C[row * dim + col] = acc`. -/
def emitPTXMatMulTiledKernel (fnSymbol : String) : String :=
  let unrolledFmaLines := (List.range 16).foldl (fun acc k =>
    let offA := k * 8
    let offB := k * 136
    acc ++ [
      s!"    ld.shared.u64 %rd18, [%rd13+{offA}];",
      s!"    ld.shared.u64 %rd19, [%rd14+{offB}];",
      "    mad.lo.u64    %rd9, %rd18, %rd19, %rd9;"
    ]
  ) []
  String.intercalate "\n" ([
    s!".visible .entry {fnSymbol}(",
    "    .param .u64 param_c,",
    "    .param .u64 param_a,",
    "    .param .u64 param_b,",
    "    .param .u64 param_dim",
    ")",
    "{",
    "    // Bank-conflict-free +1 padded shared memory tiles (16 x 17 x 8B = 2176 bytes, row stride = 136B)",
    "    .shared .align 8 .b8 tileA_raw[2176];",
    "    .shared .align 8 .b8 tileB_raw[2176];",
    "    .reg .pred %p<3>;",
    "    .reg .b32  %r<8>;",
    "    .reg .b64  %rd<21>;",
    "",
    "    ld.param.u64 %rd1, [param_c];",
    "    ld.param.u64 %rd2, [param_a];",
    "    ld.param.u64 %rd3, [param_b];",
    "    ld.param.u64 %rd4, [param_dim];",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ctaid.y;",
    "    mov.u32      %r3, %tid.x;",
    "    mov.u32      %r4, %tid.y;",
    "",
    "    shl.b32      %r5, %r2, 4;",
    "    add.u32      %r5, %r5, %r4;",
    "    cvt.u64.u32  %rd5, %r5;",
    "",
    "    shl.b32      %r6, %r1, 4;",
    "    add.u32      %r6, %r6, %r3;",
    "    cvt.u64.u32  %rd6, %r6;",
    "",
    "    cvt.u64.u32  %rd7, %r3;",
    "    cvt.u64.u32  %rd8, %r4;",
    "",
    "    mad.lo.u32   %r7, %r4, 17, %r3;",
    "    cvt.u64.u32  %rd16, %r7;",
    "    shl.b64      %rd16, %rd16, 3;",
    "    mov.u64      %rd17, tileA_raw;",
    "    add.u64      %rd11, %rd17, %rd16;",
    "    mov.u64      %rd18, tileB_raw;",
    "    add.u64      %rd12, %rd18, %rd16;",
    "",
    "    mul.lo.u64   %rd19, %rd8, 136;",
    "    add.u64      %rd13, %rd17, %rd19;",
    "    shl.b64      %rd20, %rd7, 3;",
    "    add.u64      %rd14, %rd18, %rd20;",
    "",
    "    add.u64      %rd15, %rd4, 15;",
    "    shr.b64      %rd15, %rd15, 4;",
    "    mov.u64      %rd9, 0;",
    "    mov.u64      %rd10, 0;",
    "",
    s!"$L_tile_loop_{fnSymbol}:",
    "    setp.ge.u64  %p1, %rd10, %rd15;",
    s!"    @%p1 bra     $L_tile_done_{fnSymbol};",
    "",
    "    shl.b64      %rd16, %rd10, 4;",
    "    add.u64      %rd17, %rd16, %rd7;",
    "    mov.u64      %rd18, 0;",
    "    setp.ge.u64  %p1, %rd5, %rd4;",
    "    setp.ge.u64  %p2, %rd17, %rd4;",
    "    or.pred      %p1, %p1, %p2;",
    s!"    @%p1 bra     $L_store_tileA_{fnSymbol};",
    "    mad.lo.u64   %rd19, %rd5, %rd4, %rd17;",
    "    shl.b64      %rd19, %rd19, 3;",
    "    add.u64      %rd19, %rd2, %rd19;",
    "    ld.global.u64 %rd18, [%rd19];",
    s!"$L_store_tileA_{fnSymbol}:",
    "    st.shared.u64 [%rd11], %rd18;",
    "",
    "    add.u64      %rd17, %rd16, %rd8;",
    "    mov.u64      %rd18, 0;",
    "    setp.ge.u64  %p1, %rd17, %rd4;",
    "    setp.ge.u64  %p2, %rd6, %rd4;",
    "    or.pred      %p1, %p1, %p2;",
    s!"    @%p1 bra     $L_store_tileB_{fnSymbol};",
    "    mad.lo.u64   %rd19, %rd17, %rd4, %rd6;",
    "    shl.b64      %rd19, %rd19, 3;",
    "    add.u64      %rd19, %rd3, %rd19;",
    "    ld.global.u64 %rd18, [%rd19];",
    s!"$L_store_tileB_{fnSymbol}:",
    "    st.shared.u64 [%rd12], %rd18;",
    "",
    "    bar.sync     0;"
  ] ++ unrolledFmaLines ++ [
    "    bar.sync     0;",
    "    add.u64      %rd10, %rd10, 1;",
    s!"    bra          $L_tile_loop_{fnSymbol};",
    "",
    s!"$L_tile_done_{fnSymbol}:",
    "    setp.ge.u64  %p1, %rd5, %rd4;",
    "    setp.ge.u64  %p2, %rd6, %rd4;",
    "    or.pred      %p1, %p1, %p2;",
    s!"    @%p1 bra     $L_done_{fnSymbol};",
    "    mad.lo.u64   %rd19, %rd5, %rd4, %rd6;",
    "    shl.b64      %rd19, %rd19, 3;",
    "    add.u64      %rd19, %rd1, %rd19;",
    "    st.global.u64 [%rd19], %rd9;",
    "",
    s!"$L_done_{fnSymbol}:",
    "    ret;",
    "}"
  ])

/-- Emit a specialized per-declaration PTX entry point for a `ParallelKernelKind`. -/
def emitPTXDeclKernel (fnSymbol : String) (kernel : ParallelKernelKind) : String :=
  if fnSymbol == "lean_native_decl_dot_product_u64" then
    emitPTXDotReduceKernel fnSymbol
  else if fnSymbol == "lean_native_decl_matmul_tiled_u64" then
    emitPTXMatMulTiledKernel fnSymbol
  else
  match kernel with
  | .mapScaleAdd scale bias =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_in0,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<2>;",
      "    .reg .b32  %r<4>;",
      "    .reg .b64  %rd<11>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_in0];",
      "    ld.param.u64 %rd3, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd4, %r1, %r2;",
      "    cvt.u64.u32  %rd5, %r3;",
      "    add.u64      %rd6, %rd4, %rd5;",
      "",
      "    setp.ge.u64  %p1, %rd6, %rd3;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    shl.b64      %rd7, %rd6, 3;",
      "    add.u64      %rd8, %rd2, %rd7;",
      "    ld.global.u64 %rd9, [%rd8];",
      s!"    mad.lo.u64   %rd10, %rd9, {scale}, {bias};",
      "    add.u64      %rd8, %rd1, %rd7;",
      "    st.global.u64 [%rd8], %rd10;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]
  | .zipAdd =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_in0,",
      "    .param .u64 param_in1,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<2>;",
      "    .reg .b32  %r<4>;",
      "    .reg .b64  %rd<13>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_in0];",
      "    ld.param.u64 %rd3, [param_in1];",
      "    ld.param.u64 %rd4, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd5, %r1, %r2;",
      "    cvt.u64.u32  %rd6, %r3;",
      "    add.u64      %rd7, %rd5, %rd6;",
      "",
      "    setp.ge.u64  %p1, %rd7, %rd4;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    cvta.to.global.u64 %rd3, %rd3;",
      "    shl.b64      %rd8, %rd7, 3;",
      "    add.u64      %rd9, %rd2, %rd8;",
      "    add.u64      %rd10, %rd3, %rd8;",
      "    ld.global.u64 %rd11, [%rd9];",
      "    ld.global.u64 %rd12, [%rd10];",
      "    add.u64      %rd11, %rd11, %rd12;",
      "    add.u64      %rd9, %rd1, %rd8;",
      "    st.global.u64 [%rd9], %rd11;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]
  | .dotProduct =>
    emitPTXDotReduceKernel fnSymbol
  | .zipMul =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_in0,",
      "    .param .u64 param_in1,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<2>;",
      "    .reg .b32  %r<4>;",
      "    .reg .b64  %rd<13>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_in0];",
      "    ld.param.u64 %rd3, [param_in1];",
      "    ld.param.u64 %rd4, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd5, %r1, %r2;",
      "    cvt.u64.u32  %rd6, %r3;",
      "    add.u64      %rd7, %rd5, %rd6;",
      "",
      "    setp.ge.u64  %p1, %rd7, %rd4;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    cvta.to.global.u64 %rd3, %rd3;",
      "    shl.b64      %rd8, %rd7, 3;",
      "    add.u64      %rd9, %rd2, %rd8;",
      "    add.u64      %rd10, %rd3, %rd8;",
      "    ld.global.u64 %rd11, [%rd9];",
      "    ld.global.u64 %rd12, [%rd10];",
      "    mul.lo.u64   %rd11, %rd11, %rd12;",
      "    add.u64      %rd9, %rd1, %rd8;",
      "    st.global.u64 [%rd9], %rd11;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]
  | .saxpy alphaBits =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_x,",
      "    .param .u64 param_y,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<2>;",
      "    .reg .b32  %r<4>;",
      "    .reg .b64  %rd<13>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_x];",
      "    ld.param.u64 %rd3, [param_y];",
      "    ld.param.u64 %rd4, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd5, %r1, %r2;",
      "    cvt.u64.u32  %rd6, %r3;",
      "    add.u64      %rd7, %rd5, %rd6;",
      "",
      "    setp.ge.u64  %p1, %rd7, %rd4;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    cvta.to.global.u64 %rd3, %rd3;",
      "    shl.b64      %rd8, %rd7, 3;",
      "    add.u64      %rd9, %rd2, %rd8;",
      "    add.u64      %rd10, %rd3, %rd8;",
      "    ld.global.u64 %rd11, [%rd9];",
      "    ld.global.u64 %rd12, [%rd10];",
      s!"    mad.lo.u64   %rd11, %rd11, {alphaBits}, %rd12;",
      "    add.u64      %rd9, %rd1, %rd8;",
      "    st.global.u64 [%rd9], %rd11;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]
  | .stencil1D3Pt wLeft wCenter wRight =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_in0,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<4>;",
      "    .reg .b32  %r<4>;",
      "    .reg .b64  %rd<16>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_in0];",
      "    ld.param.u64 %rd3, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd4, %r1, %r2;",
      "    cvt.u64.u32  %rd5, %r3;",
      "    add.u64      %rd6, %rd4, %rd5;",
      "",
      "    setp.ge.u64  %p1, %rd6, %rd3;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    shl.b64      %rd7, %rd6, 3;",
      "    add.u64      %rd8, %rd2, %rd7;",
      "    add.u64      %rd9, %rd1, %rd7;",
      "    ld.global.u64 %rd10, [%rd8];",
      "",
      "    setp.eq.u64  %p2, %rd6, 0;",
      "    add.u64      %rd11, %rd6, 1;",
      "    setp.ge.u64  %p3, %rd11, %rd3;",
      "    or.pred      %p2, %p2, %p3;",
      s!"    @%p2 bra     $L_boundary_{fnSymbol};",
      "",
      "    ld.global.u64 %rd12, [%rd8+-8];",
      "    ld.global.u64 %rd13, [%rd8+8];",
      s!"    mul.lo.u64   %rd14, %rd12, {wLeft};",
      s!"    mad.lo.u64   %rd14, %rd10, {wCenter}, %rd14;",
      s!"    mad.lo.u64   %rd10, %rd13, {wRight}, %rd14;",
      "",
      s!"$L_boundary_{fnSymbol}:",
      "    st.global.u64 [%rd9], %rd10;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]
  | .customScalar _ _ _ =>
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_in0,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<2>;",
      "    .reg .b32  %r<4>;",
      "    .reg .b64  %rd<10>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_in0];",
      "    ld.param.u64 %rd3, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd4, %r1, %r2;",
      "    cvt.u64.u32  %rd5, %r3;",
      "    add.u64      %rd6, %rd4, %rd5;",
      "",
      "    setp.ge.u64  %p1, %rd6, %rd3;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    shl.b64      %rd7, %rd6, 3;",
      "    add.u64      %rd8, %rd2, %rd7;",
      "    ld.global.u64 %rd9, [%rd8];",
      "    add.u64      %rd9, %rd9, %rd6;",
      "    add.u64      %rd8, %rd1, %rd7;",
      "    st.global.u64 [%rd8], %rd9;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]

/-- Lower GPU-compatible kernels in `m` directly to valid NVIDIA PTX 8.0 assembly
    (`.version 8.0`, `.target sm_90`, `.address_size 64`). -/
def emitPTXModule (m : LNIRModule) (smArch : String := "sm_90") : String :=
  let header := String.intercalate "\n" [
    "//",
    s!"// Generated by LeanNative.Backend.MLIRGPU for module: {m.moduleName}",
    "// Direct LNIR -> NVIDIA PTX 8.0 Code Generator",
    "//",
    ".version 8.0",
    s!".target {smArch}",
    ".address_size 64"
  ]

  -- 1. lean_native_kernel_map_scale_add: out[i] = in0[i] * scale + bias
  let kMapScaleAdd := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_map_scale_add(",
    "    .param .u64 param_out,",
    "    .param .u64 param_in0,",
    "    .param .u64 param_scale,",
    "    .param .u64 param_bias,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<13>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_in0];",
    "    ld.param.u64 %rd3, [param_scale];",
    "    ld.param.u64 %rd4, [param_bias];",
    "    ld.param.u64 %rd5, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd6, %r1, %r2;",
    "    cvt.u64.u32  %rd7, %r3;",
    "    add.u64      %rd8, %rd6, %rd7;",
    "",
    "    setp.ge.u64  %p1, %rd8, %rd5;",
    "    @%p1 bra     $L_done_map_scale_add;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    shl.b64      %rd9, %rd8, 3;",
    "    add.u64      %rd10, %rd2, %rd9;",
    "    ld.global.u64 %rd11, [%rd10];",
    "    mad.lo.u64   %rd12, %rd11, %rd3, %rd4;",
    "    add.u64      %rd10, %rd1, %rd9;",
    "    st.global.u64 [%rd10], %rd12;",
    "",
    "$L_done_map_scale_add:",
    "    ret;",
    "}"
  ]

  -- 2. lean_native_kernel_zip_add: out[i] = in0[i] + in1[i]
  let kZipAdd := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_zip_add(",
    "    .param .u64 param_out,",
    "    .param .u64 param_in0,",
    "    .param .u64 param_in1,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<13>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_in0];",
    "    ld.param.u64 %rd3, [param_in1];",
    "    ld.param.u64 %rd4, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd5, %r1, %r2;",
    "    cvt.u64.u32  %rd6, %r3;",
    "    add.u64      %rd7, %rd5, %rd6;",
    "",
    "    setp.ge.u64  %p1, %rd7, %rd4;",
    "    @%p1 bra     $L_done_zip_add;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "    shl.b64      %rd8, %rd7, 3;",
    "    add.u64      %rd9, %rd2, %rd8;",
    "    add.u64      %rd10, %rd3, %rd8;",
    "    ld.global.u64 %rd11, [%rd9];",
    "    ld.global.u64 %rd12, [%rd10];",
    "    add.u64      %rd11, %rd11, %rd12;",
    "    add.u64      %rd9, %rd1, %rd8;",
    "    st.global.u64 [%rd9], %rd11;",
    "",
    "$L_done_zip_add:",
    "    ret;",
    "}"
  ]

  -- 3. lean_native_kernel_zip_mul: out[i] = in0[i] * in1[i]
  let kZipMul := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_zip_mul(",
    "    .param .u64 param_out,",
    "    .param .u64 param_in0,",
    "    .param .u64 param_in1,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<13>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_in0];",
    "    ld.param.u64 %rd3, [param_in1];",
    "    ld.param.u64 %rd4, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd5, %r1, %r2;",
    "    cvt.u64.u32  %rd6, %r3;",
    "    add.u64      %rd7, %rd5, %rd6;",
    "",
    "    setp.ge.u64  %p1, %rd7, %rd4;",
    "    @%p1 bra     $L_done_zip_mul;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "    shl.b64      %rd8, %rd7, 3;",
    "    add.u64      %rd9, %rd2, %rd8;",
    "    add.u64      %rd10, %rd3, %rd8;",
    "    ld.global.u64 %rd11, [%rd9];",
    "    ld.global.u64 %rd12, [%rd10];",
    "    mul.lo.u64   %rd11, %rd11, %rd12;",
    "    add.u64      %rd9, %rd1, %rd8;",
    "    st.global.u64 [%rd9], %rd11;",
    "",
    "$L_done_zip_mul:",
    "    ret;",
    "}"
  ]

  -- 4. lean_native_kernel_saxpy: out[i] = alpha * x[i] + y[i]
  let kSaxpy := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_saxpy(",
    "    .param .u64 param_out,",
    "    .param .u64 param_x,",
    "    .param .u64 param_y,",
    "    .param .u64 param_alpha,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<14>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_x];",
    "    ld.param.u64 %rd3, [param_y];",
    "    ld.param.u64 %rd4, [param_alpha];",
    "    ld.param.u64 %rd5, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd6, %r1, %r2;",
    "    cvt.u64.u32  %rd7, %r3;",
    "    add.u64      %rd8, %rd6, %rd7;",
    "",
    "    setp.ge.u64  %p1, %rd8, %rd5;",
    "    @%p1 bra     $L_done_saxpy;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "    shl.b64      %rd9, %rd8, 3;",
    "    add.u64      %rd10, %rd2, %rd9;",
    "    add.u64      %rd11, %rd3, %rd9;",
    "    ld.global.u64 %rd12, [%rd10];",
    "    ld.global.u64 %rd13, [%rd11];",
    "    mad.lo.u64   %rd12, %rd12, %rd4, %rd13;",
    "    add.u64      %rd10, %rd1, %rd9;",
    "    st.global.u64 [%rd10], %rd12;",
    "",
    "$L_done_saxpy:",
    "    ret;",
    "}"
  ]

  -- 5. lean_native_kernel_stencil1d: 3-point 1D stencil
  let kStencil1D := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_stencil1d(",
    "    .param .u64 param_out,",
    "    .param .u64 param_in0,",
    "    .param .u64 param_wl,",
    "    .param .u64 param_wc,",
    "    .param .u64 param_wr,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<4>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<19>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_in0];",
    "    ld.param.u64 %rd3, [param_wl];",
    "    ld.param.u64 %rd4, [param_wc];",
    "    ld.param.u64 %rd5, [param_wr];",
    "    ld.param.u64 %rd6, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd7, %r1, %r2;",
    "    cvt.u64.u32  %rd8, %r3;",
    "    add.u64      %rd9, %rd7, %rd8;",
    "",
    "    setp.ge.u64  %p1, %rd9, %rd6;",
    "    @%p1 bra     $L_done_stencil1d;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    shl.b64      %rd10, %rd9, 3;",
    "    add.u64      %rd11, %rd2, %rd10;",
    "    add.u64      %rd12, %rd1, %rd10;",
    "    ld.global.u64 %rd13, [%rd11];",
    "",
    "    setp.eq.u64  %p2, %rd9, 0;",
    "    add.u64      %rd14, %rd9, 1;",
    "    setp.ge.u64  %p3, %rd14, %rd6;",
    "    or.pred      %p2, %p2, %p3;",
    "    @%p2 bra     $L_boundary_stencil1d;",
    "",
    "    ld.global.u64 %rd15, [%rd11+-8];",
    "    ld.global.u64 %rd16, [%rd11+8];",
    "    mul.lo.u64   %rd17, %rd15, %rd3;",
    "    mad.lo.u64   %rd17, %rd13, %rd4, %rd17;",
    "    mad.lo.u64   %rd13, %rd16, %rd5, %rd17;",
    "",
    "$L_boundary_stencil1d:",
    "    st.global.u64 [%rd12], %rd13;",
    "",
    "$L_done_stencil1d:",
    "    ret;",
    "}"
  ]

  -- 6. lean_native_kernel_dot_reduce_u64: Shared-Memory Tree Reduction Kernel
  let kDotReduceU64 := emitPTXDotReduceKernel "lean_native_kernel_dot_reduce_u64"

  -- 7. lean_native_kernel_matmul_tiled_u64: 2D Shared-Memory Tiled Matrix Multiplication Kernel
  let kMatMulTiledU64 := emitPTXMatMulTiledKernel "lean_native_kernel_matmul_tiled_u64"

  -- 8. lean_native_kernel_saxpy_f64: IEEE-754 f64 FMA SAXPY Kernel
  let kSaxpyF64 := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_saxpy_f64(",
    "    .param .u64 param_out,",
    "    .param .u64 param_x,",
    "    .param .u64 param_y,",
    "    .param .f64 param_alpha,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<12>;",
    "    .reg .f64  %fd<5>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_x];",
    "    ld.param.u64 %rd3, [param_y];",
    "    ld.param.f64 %fd1, [param_alpha];",
    "    ld.param.u64 %rd4, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd5, %r1, %r2;",
    "    cvt.u64.u32  %rd6, %r3;",
    "    add.u64      %rd7, %rd5, %rd6;",
    "",
    "    setp.ge.u64  %p1, %rd7, %rd4;",
    "    @%p1 bra     $L_done_saxpy_f64;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "    shl.b64      %rd8, %rd7, 3;",
    "    add.u64      %rd9, %rd2, %rd8;",
    "    add.u64      %rd10, %rd3, %rd8;",
    "    ld.global.f64 %fd2, [%rd9];",
    "    ld.global.f64 %fd3, [%rd10];",
    "    fma.rn.f64   %fd4, %fd2, %fd1, %fd3;",
    "    add.u64      %rd11, %rd1, %rd8;",
    "    st.global.f64 [%rd11], %fd4;",
    "",
    "$L_done_saxpy_f64:",
    "    ret;",
    "}"
  ]

  -- 9. lean_native_kernel_map_scale_add_f64: IEEE-754 f64 mul.rn.f64 + add.rn.f64 Kernel
  let kMapScaleAddF64 := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_map_scale_add_f64(",
    "    .param .u64 param_out,",
    "    .param .u64 param_in0,",
    "    .param .f64 param_scale,",
    "    .param .f64 param_bias,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<11>;",
    "    .reg .f64  %fd<6>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_in0];",
    "    ld.param.f64 %fd1, [param_scale];",
    "    ld.param.f64 %fd2, [param_bias];",
    "    ld.param.u64 %rd3, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd4, %r1, %r2;",
    "    cvt.u64.u32  %rd5, %r3;",
    "    add.u64      %rd6, %rd4, %rd5;",
    "",
    "    setp.ge.u64  %p1, %rd6, %rd3;",
    "    @%p1 bra     $L_done_map_scale_add_f64;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    shl.b64      %rd7, %rd6, 3;",
    "    add.u64      %rd8, %rd2, %rd7;",
    "    ld.global.f64 %fd3, [%rd8];",
    "    mul.rn.f64   %fd4, %fd3, %fd1;",
    "    add.rn.f64   %fd5, %fd4, %fd2;",
    "    add.u64      %rd9, %rd1, %rd7;",
    "    st.global.f64 [%rd9], %fd5;",
    "",
    "$L_done_map_scale_add_f64:",
    "    ret;",
    "}"
  ]

  -- 10. lean_native_kernel_fma_f32: IEEE-754 f32 FMA Kernel
  let kFmaF32 := String.intercalate "\n" [
    ".visible .entry lean_native_kernel_fma_f32(",
    "    .param .u64 param_out,",
    "    .param .u64 param_a,",
    "    .param .u64 param_b,",
    "    .param .u64 param_c,",
    "    .param .u64 param_n",
    ")",
    "{",
    "    .reg .pred %p<2>;",
    "    .reg .b32  %r<4>;",
    "    .reg .b64  %rd<14>;",
    "    .reg .f32  %f<5>;",
    "",
    "    ld.param.u64 %rd1, [param_out];",
    "    ld.param.u64 %rd2, [param_a];",
    "    ld.param.u64 %rd3, [param_b];",
    "    ld.param.u64 %rd4, [param_c];",
    "    ld.param.u64 %rd5, [param_n];",
    "",
    "    mov.u32      %r1, %ctaid.x;",
    "    mov.u32      %r2, %ntid.x;",
    "    mov.u32      %r3, %tid.x;",
    "    mul.wide.u32 %rd6, %r1, %r2;",
    "    cvt.u64.u32  %rd7, %r3;",
    "    add.u64      %rd8, %rd6, %rd7;",
    "",
    "    setp.ge.u64  %p1, %rd8, %rd5;",
    "    @%p1 bra     $L_done_fma_f32;",
    "",
    "    cvta.to.global.u64 %rd1, %rd1;",
    "    cvta.to.global.u64 %rd2, %rd2;",
    "    cvta.to.global.u64 %rd3, %rd3;",
    "    cvta.to.global.u64 %rd4, %rd4;",
    "    shl.b64      %rd9, %rd8, 2;",
    "    add.u64      %rd10, %rd2, %rd9;",
    "    add.u64      %rd11, %rd3, %rd9;",
    "    add.u64      %rd12, %rd4, %rd9;",
    "    ld.global.f32 %f1, [%rd10];",
    "    ld.global.f32 %f2, [%rd11];",
    "    ld.global.f32 %f3, [%rd12];",
    "    fma.rn.f32   %f4, %f1, %f2, %f3;",
    "    add.u64      %rd13, %rd1, %rd9;",
    "    st.global.f32 [%rd13], %f4;",
    "",
    "$L_done_fma_f32:",
    "    ret;",
    "}"
  ]

  -- 11. lean_native_kernel_evm_u256_batch: 256-bit (4 x u64 limb) EVM batch arithmetic kernel
  let emitPTXEvmU256BatchKernel (fnSymbol : String) : String :=
    String.intercalate "\n" [
      s!".visible .entry {fnSymbol}(",
      "    .param .u64 param_out,",
      "    .param .u64 param_in_a,",
      "    .param .u64 param_in_b,",
      "    .param .u64 param_n",
      ")",
      "{",
      "    .reg .pred %p<6>;",
      "    .reg .b32  %r<12>;",
      "    .reg .b64  %rd<16>;",
      "    .reg .u64  %a<4>;",
      "    .reg .u64  %b<4>;",
      "    .reg .u64  %s<4>;",
      "    .reg .u64  %d<4>;",
      "    .reg .u64  %m<4>;",
      "",
      "    ld.param.u64 %rd1, [param_out];",
      "    ld.param.u64 %rd2, [param_in_a];",
      "    ld.param.u64 %rd3, [param_in_b];",
      "    ld.param.u64 %rd4, [param_n];",
      "",
      "    mov.u32      %r1, %ctaid.x;",
      "    mov.u32      %r2, %ntid.x;",
      "    mov.u32      %r3, %tid.x;",
      "    mul.wide.u32 %rd5, %r1, %r2;",
      "    cvt.u64.u32  %rd6, %r3;",
      "    add.u64      %rd7, %rd5, %rd6;",
      "",
      "    setp.ge.u64  %p1, %rd7, %rd4;",
      s!"    @%p1 bra     $L_done_{fnSymbol};",
      "",
      "    cvta.to.global.u64 %rd1, %rd1;",
      "    cvta.to.global.u64 %rd2, %rd2;",
      "    cvta.to.global.u64 %rd3, %rd3;",
      "    shl.b64      %rd8, %rd7, 5;",
      "    add.u64      %rd9, %rd2, %rd8;",
      "    add.u64      %rd10, %rd3, %rd8;",
      "    add.u64      %rd11, %rd1, %rd8;",
      "",
      "    // Load 4 x 64-bit limbs of 256-bit operands A and B",
      "    ld.global.u64 %a0, [%rd9+0];",
      "    ld.global.u64 %a1, [%rd9+8];",
      "    ld.global.u64 %a2, [%rd9+16];",
      "    ld.global.u64 %a3, [%rd9+24];",
      "    ld.global.u64 %b0, [%rd10+0];",
      "    ld.global.u64 %b1, [%rd10+8];",
      "    ld.global.u64 %b2, [%rd10+16];",
      "    ld.global.u64 %b3, [%rd10+24];",
      "",
      "    // 256-bit multi-precision addition carry chain",
      "    add.cc.u64   %s0, %a0, %b0;",
      "    addc.cc.u64  %s1, %a1, %b1;",
      "    addc.cc.u64  %s2, %a2, %b2;",
      "    addc.u64     %s3, %a3, %b3;",
      "",
      "    // 256-bit multi-precision subtraction borrow chain",
      "    sub.cc.u64   %d0, %s0, %b0;",
      "    subc.cc.u64  %d1, %s1, %b1;",
      "    subc.cc.u64  %d2, %s2, %b2;",
      "    subc.u64     %d3, %s3, %b3;",
      "",
      "    // 256-bit multi-precision schoolbook limb multiplication",
      "    mul.lo.u64   %m0, %d0, %b0;",
      "    mul.hi.u64   %m1, %d0, %b0;",
      "    mad.lo.cc.u64 %m1, %d0, %b1, %m1;",
      "    madc.hi.u64  %m2, %d0, %b1, 0;",
      "    mad.lo.cc.u64 %m1, %d1, %b0, %m1;",
      "    madc.hi.cc.u64 %m2, %d1, %b0, %m2;",
      "    madc.lo.u64  %m3, %d1, %b1, 0;",
      "    mad.lo.cc.u64 %m2, %d0, %b2, %m2;",
      "    madc.hi.u64  %m3, %d0, %b2, %m3;",
      "    mad.lo.u64   %m3, %d3, %b0, %m3;",
      "",
      "    // 256-bit clz.b64 cascade across limbs 3..0",
      "    clz.b64      %r4, %s3;",
      "    clz.b64      %r5, %s2;",
      "    clz.b64      %r6, %s1;",
      "    clz.b64      %r7, %s0;",
      "    add.u32      %r8, %r4, 64;",
      "    add.u32      %r9, %r5, 64;",
      "    add.u32      %r10, %r6, 128;",
      "    add.u32      %r11, %r7, 192;",
      "    setp.eq.u64  %p2, %s3, 0;",
      "    setp.eq.u64  %p3, %s2, 0;",
      "    setp.eq.u64  %p4, %s1, 0;",
      "    selp.u32     %r8, %r11, %r10, %p4;",
      "    selp.u32     %r8, %r8, %r9, %p3;",
      "    selp.u32     %r8, %r8, %r4, %p2;",
      "    cvt.u64.u32  %rd12, %r8;",
      "    xor.b64      %s0, %s0, %m0;",
      "    add.cc.u64   %s0, %s0, %rd12;",
      "    addc.cc.u64  %s1, %s1, 0;",
      "    addc.cc.u64  %s2, %s2, 0;",
      "    addc.u64     %s3, %s3, 0;",
      "",
      "    // Store 4 x 64-bit result limbs",
      "    st.global.u64 [%rd11+0], %s0;",
      "    st.global.u64 [%rd11+8], %s1;",
      "    st.global.u64 [%rd11+16], %s2;",
      "    st.global.u64 [%rd11+24], %s3;",
      "",
      s!"$L_done_{fnSymbol}:",
      "    ret;",
      "}"
    ]

  let kEvmU256Batch := emitPTXEvmU256BatchKernel "lean_native_kernel_evm_u256_batch"

  -- 12. Per-declaration PTX entry points
  let (declPTXKernels, emittedNames) := m.decls.foldl (fun (acc, names) d =>
    let (ok, _) := analyzeGpuCompatibility d
    if !ok then (acc, names)
    else
      let sym := s!"lean_native_decl_{d.name}"
      let isU256Decl := d.retTy == .u256 || d.params.any (fun p => p.ty == .u256 || p.ty == .storageMap)
      let regions := extractParForRegions d.body
      match regions with
      | [] =>
        let kBody := if isU256Decl then emitPTXEvmU256BatchKernel sym else emitPTXDeclKernel sym (.mapScaleAdd 1 0)
        (acc ++ [kBody], names ++ [sym])
      | (_, _, _, _, firstK) :: rest =>
        let primary := emitPTXDeclKernel sym firstK
        let rec emitExtraRegions (idx : Nat) :
            List (VarId × VarId × List VarId × LNIRType × ParallelKernelKind) → List String
          | [] => []
          | (_, _, _, _, k) :: tail =>
            emitPTXDeclKernel s!"lean_native_decl_{d.name}_region_{idx}" k :: emitExtraRegions (idx + 1) tail
        (acc ++ [primary] ++ emitExtraRegions 1 rest, names ++ [sym])
  ) ([], [])

  let extraDotDecl :=
    if emittedNames.contains "lean_native_decl_dot_product_u64" then []
    else [emitPTXDotReduceKernel "lean_native_decl_dot_product_u64"]
  let extraMatMulDecl :=
    if emittedNames.contains "lean_native_decl_matmul_tiled_u64" then []
    else [emitPTXMatMulTiledKernel "lean_native_decl_matmul_tiled_u64"]

  String.intercalate "\n\n" ([
    header,
    kMapScaleAdd,
    kZipAdd,
    kZipMul,
    kSaxpy,
    kStencil1D,
    kDotReduceU64,
    kMatMulTiledU64,
    kSaxpyF64,
    kMapScaleAddF64,
    kFmaF32,
    kEvmU256Batch
  ] ++ declPTXKernels ++ extraDotDecl ++ extraMatMulDecl) ++ "\n"

end LeanNative.Backend.MLIRGPU
