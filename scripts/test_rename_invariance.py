#!/usr/bin/env python3
"""
Identifier-Renaming Invariance Regression Suite for `scripts/ln_c_opt.py`.
Verifies that general passes (Pass 1, Pass 2, Pass 3, Pass 3b) trigger identically
even when all benchmark function names are systematically renamed (e.g., benchX -> renamedTaskX).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import ln_c_opt  # noqa: E402


def verify_rename_invariance(raw_c_path: str) -> None:
    raw = Path(raw_c_path).read_text()
    renamed = re.sub(r"bench([A-Z][a-zA-Z0-9_]*)", r"renamedTask\1", raw)

    c1 = ln_c_opt.apply_pass1_scalar_array(renamed)
    c2 = ln_c_opt.apply_pass2_range_forin(c1)
    c3 = ln_c_opt.apply_pass3b_structural_peepholes(ln_c_opt.apply_pass3_while_sroa(c2))

    # 1. Verify Sub-pass 2D (Range.forIn' push preallocation) fired on renamed init loops
    for fn in [
        "renamedTaskSArrayScaleBias_spec__1___redArg",
        "renamedTaskDotProductU64_spec__0___redArg",
        "renamedTaskSaxpyKernel_spec__0___redArg",
        "renamedTaskMatmulTiledU64_spec__0___redArg",
    ]:
        m = re.search(rf"LEAN_EXPORT lean_object\* [^\n]*{fn}\([^)]*\)\{{", c3)
        assert m, f"Missing {fn}"
        snippet = c3[m.start() : m.start() + 1400]
        assert "lean_alloc_sarray(8, ln_n, ln_n)" in snippet, f"Sub-pass 2D failed on {fn}"

    # 1b. Verify Sub-pass 2D 2-tuple in-place SArray fill fired on renamed Dijkstra init
    m_dijk = re.search(r"LEAN_EXPORT lean_object\* [^\n]*renamedTaskDijkstraPairingHeap_spec__2___redArg\([^)]*\)\{", c3)
    assert m_dijk and "ln_sarray_ensure_exclusive_u64" in c3[m_dijk.start() : m_dijk.start() + 1400]

    # 1c. Verify Sub-pass 2E mixed (Array, ByteArray) and nested 3-tuple CSR setup loops fired on renamed CSR init
    for fn_csr in [
        "renamedTaskSparseMatmulCsr_spec__0___redArg",
        "renamedTaskSparseMatmulCsr_spec__1___redArg",
    ]:
        m_csr = re.search(rf"LEAN_EXPORT lean_object\* [^\n]*{fn_csr}\([^)]*\)\{{", c3)
        assert m_csr, f"Missing {fn_csr}"
        assert "lean_copy_expand_array" in c3[m_csr.start() : m_csr.start() + 1400], f"Sub-pass 2E failed on {fn_csr}"

    # 1d. Verify Pass 2 2D/3D outer->inner Range.forIn', stack Range elision, and indirect gather fast-paths
    for fn_2d in [
        "renamedTaskSpectralNorm_spec__1___redArg",
        "renamedTaskSpectralNorm_spec__3___redArg",
        "renamedTaskSparseMatmulCsr_spec__2___redArg",
        "renamedTaskSparseMatmulCsr_spec__3___redArg",
        "renamedTaskMatmulTiledU64_spec__1___redArg",
        "renamedTaskMatmulTiledU64_spec__2___redArg",
        "renamedTaskMatmulTiledU64_spec__3___redArg",
    ]:
        m_2d = re.search(rf"LEAN_EXPORT [^\n]*(?:lean_object\*|uint64_t) [^\n]*{fn_2d}\([^)]*\)\{{", c3)
        assert m_2d, f"Missing {fn_2d}"
        assert "for (; ln_i < ln_limit; ++ln_i)" in c3[m_2d.start() : m_2d.start() + 2800], f"Pass 2 2D/3D failed on {fn_2d}"

    # 2. Verify Pass 3 interprocedural scalar companion emission and outer-loop scalarization
    for inner_fn in [
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskSha256Compress_spec__0___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskKeccakF1600_spec__0___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskJsonSimdScanner_spec__0___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskMandelbrotSimd_spec__0___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskMandelbrotSimd_spec__1___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskMandelbrotSimd_spec__2___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskRobinHoodHtab_spec__0___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskRobinHoodHtab_spec__1___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskRobinHoodHtab_spec__2___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskRobinHoodHtab_spec__3___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskRegexDfaStep_spec__2___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskRegexDfaStep_spec__3___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskFannkuchRedux_spec__0___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskFannkuchRedux_spec__1___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskFannkuchRedux_spec__2___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskFannkuchRedux_spec__3___redArg_scalar",
        "l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00renamedTaskNbody_spec__0___redArg_scalar",
        "l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00renamedTaskNbody_spec__1___redArg_scalar",
        "l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00renamedTaskNbody_spec__2___redArg_scalar",
        "l___private_Init_While_0__repeatM_erased___at___00renamedTaskNbody_spec__3___redArg_scalar",
    ]:
        assert f"void {inner_fn}(" in c3, f"Missing scalar helper {inner_fn}"

    # 2b. Verify early-return Prod constructor stripping in renamed Mandelbrot scalar companions
    m_mb0 = c3.find("void l___private_Init_While_0__repeatM_erased___at___00renamedTaskMandelbrotSimd_spec__0___redArg_scalar(")
    m_mb0_end = c3.find("\nLEAN_EXPORT ", m_mb0)
    assert "lean_alloc_ctor" not in c3[m_mb0:m_mb0_end], "Early-return ctor not stripped in Mandelbrot _scalar"
    assert "((int64_t)(" in c3[m_mb0:m_mb0_end], "Peephole D arithmetic shift did not fire in Mandelbrot _scalar"

    # 2c. Verify Peephole D return-diamond (sar64) and Peephole E in-body stack Range elision (SpectralNorm)
    m_sar = c3.find("LEAN_EXPORT uint64_t l_sar64__16(uint64_t ")
    assert m_sar != -1 and "return (uint64_t)(((int64_t)(" in c3[m_sar : m_sar + 400], "Peephole D return-diamond failed on l_sar64__16"
    m_sn5 = c3.find("LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00renamedTaskSpectralNorm_spec__5___redArg(uint64_t ")
    assert m_sn5 != -1 and "ln_st_v_" in c3[m_sn5 : m_sn5 + 3200], "Peephole E stack Range elision failed on SpectralNorm_spec__5"
    for fn_pe in [
        "renamedTaskNbody_spec__1___redArg",
        "renamedTaskSparseMatmulCsr_spec__4___redArg",
        "renamedTaskMatmulTiledU64",
    ]:
        m_pe = re.search(rf"LEAN_EXPORT [^\n]*(?:lean_object\*|uint64_t) [^\n]*{fn_pe}\([^)]*\)\{{", c3)
        assert m_pe and "ln_st_v_" in c3[m_pe.start() : m_pe.start() + 12000], f"Peephole E stack Range elision failed on {fn_pe}"

    # 3. Verify Pass 3b structural peepholes (mulHi __uint128_t and __builtin_popcountll)
    assert "__uint128_t" in c3, "Pass 3b mulHi __uint128_t peephole did not fire on renamed C"
    assert "__builtin_popcountll" in c3, "Pass 3b popcount64 peephole did not fire on renamed C"
    print("RENAME_INVARIANCE_SUITE=PASSED")


if __name__ == "__main__":
    c_file = sys.argv[1] if len(sys.argv) > 1 else "/tmp/opencode/raw_bench.c"
    verify_rename_invariance(c_file)
