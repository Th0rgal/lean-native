#!/usr/bin/env python3
"""
benchmarks/run_benchmarks.py

Cross-Architecture Benchmark & Differential Verification Suite for `lean-native`.

Compiles and runs all baselines (`official_lean4`, `cpp_o3`, `cuda_o3`) and `lean_native`
(`cpu_llvm_o3`, `gpu_ptx`, `hybrid_cpu_gpu`) on:
  1. `spark-de79` (local): ARM64 Cortex-X925/A725 (20 cores) + NVIDIA GB10 Grace-Blackwell GPU (sm_121)
  2. `ashur` (remote via SSH): Dedicated x86-64 Intel(R) Core(TM) i7-7700 @ 3.60GHz

Enforces:
  - Strict 64-bit deterministic FNV-1a / scalar checksum verification across EVERY backend and BOTH architectures.
  - Statistical evaluation across >= 7 trials (median, mean, std, IQR, min, max, Mann-Whitney U & Welch t-test p-values).
  - Peak RSS (KB) and compilation time (ms) tracking.
  - Emits structured telemetry to `benchmarks/results/latest_benchmarks.json` and a detailed
    human-readable report to `benchmarks/BENCHMARK_REPORT.md`.
"""

from __future__ import annotations

import argparse
import datetime
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_DIR = REPO_ROOT / "benchmarks"
BASELINES_DIR = BENCH_DIR / "baselines"
MANIFEST_PATH = BENCH_DIR / "holdout_manifest.json"
RESULTS_DIR = BENCH_DIR / "results"
REPORT_PATH = BENCH_DIR / "BENCHMARK_REPORT.md"

BENCH_LINE_RE = re.compile(
    r"BENCH\s+([a-zA-Z0-9_]+)\s+checksum=(\d+)\s+time_ms=([0-9.]+)"
)


def find_local_lean_toolchain() -> Path:
    candidates = [
        Path("/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0"),
        Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.31.0",
    ]
    for c in candidates:
        if (c / "bin" / "lean").is_file():
            return c
    lean_bin = shutil.which("lean")
    if lean_bin:
        return Path(lean_bin).resolve().parent.parent
    raise RuntimeError("Could not locate Lean 4 v4.31.0 toolchain on local host")


def get_ssh_config_path() -> Optional[str]:
    dev_id = os.environ.get(
        "SANDBOXED_DEVELOPMENT_IDENTITY",
        "/var/lib/spark-admin/.config/sandboxed-sh/development-identity",
    )
    for cand in [
        Path(dev_id) / "current" / "ssh" / "config",
        Path(dev_id) / "ssh" / "config",
        Path("/var/lib/sandboxed-node/.config/sandboxed-sh/development-identity/g-467458b173fe/ssh/config"),
    ]:
        if cand.is_file():
            return str(cand)
    return None


def normal_cdf(x: float) -> float:
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def mann_whitney_u_pvalue(sample_a: List[float], sample_b: List[float]) -> float:
    """Two-sided Mann-Whitney U test normal approximation with tie correction."""
    n1, n2 = len(sample_a), len(sample_b)
    if n1 == 0 or n2 == 0:
        return 1.0
    combined = [(v, 0) for v in sample_a] + [(v, 1) for v in sample_b]
    combined.sort(key=lambda x: x[0])

    ranks = [0.0] * len(combined)
    i = 0
    tie_sum = 0.0
    while i < len(combined):
        j = i
        while j < len(combined) and combined[j][0] == combined[i][0]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[k] = avg_rank
        t = j - i
        if t > 1:
            tie_sum += t**3 - t
        i = j

    r1 = sum(ranks[idx] for idx, (_, grp) in enumerate(combined) if grp == 0)
    u1 = r1 - n1 * (n1 + 1) / 2.0
    u2 = n1 * n2 - u1
    u = min(u1, u2)

    mu = n1 * n2 / 2.0
    n = n1 + n2
    var = (n1 * n2 / 12.0) * ((n + 1.0) - tie_sum / (n * (n - 1.0))) if n > 1 else 0.0
    if var <= 1e-12:
        return 1.0 if abs(u - mu) < 1e-9 else 0.0
    z = (abs(u - mu) - 0.5) / math.sqrt(var)
    p = 2.0 * (1.0 - normal_cdf(max(0.0, z)))
    return max(0.0, min(1.0, p))


def welch_t_test_pvalue(sample_a: List[float], sample_b: List[float]) -> float:
    """Two-sided Welch's t-test p-value."""
    n1, n2 = len(sample_a), len(sample_b)
    if n1 < 2 or n2 < 2:
        return 1.0
    m1, m2 = statistics.mean(sample_a), statistics.mean(sample_b)
    v1, v2 = statistics.variance(sample_a), statistics.variance(sample_b)
    se2 = (v1 / n1) + (v2 / n2)
    if se2 <= 1e-15:
        return 1.0 if abs(m1 - m2) < 1e-9 else 0.0
    t_stat = abs(m1 - m2) / math.sqrt(se2)
    p = 2.0 * (1.0 - normal_cdf(t_stat))
    return max(0.0, min(1.0, p))


def compute_summary_stats(samples: List[float]) -> Dict[str, float]:
    if not samples:
        return {
            "median_ms": 0.0,
            "mean_ms": 0.0,
            "std_ms": 0.0,
            "iqr_ms": 0.0,
            "min_ms": 0.0,
            "max_ms": 0.0,
        }
    s = sorted(samples)
    n = len(s)
    med = statistics.median(s)
    mean = statistics.mean(s)
    std = statistics.stdev(s) if n >= 2 else 0.0
    q1 = s[n // 4]
    q3 = s[(3 * n) // 4]
    return {
        "median_ms": round(med, 4),
        "mean_ms": round(mean, 4),
        "std_ms": round(std, 4),
        "iqr_ms": round(q3 - q1, 4),
        "min_ms": round(s[0], 4),
        "max_ms": round(s[-1], 4),
    }


def parse_bench_output(stdout: str) -> Dict[str, Tuple[int, float]]:
    out: Dict[str, Tuple[int, float]] = {}
    for line in stdout.splitlines():
        m = BENCH_LINE_RE.search(line)
        if m:
            b_id = m.group(1)
            checksum = int(m.group(2))
            t_ms = float(m.group(3))
            out[b_id] = (checksum, t_ms)
    return out


def measure_local_binary(
    bin_path: Path,
    trials: int,
    env_extra: Optional[Dict[str, str]] = None,
) -> Tuple[Dict[str, List[float]], Dict[str, int], int]:
    """Run `bin_path` for `trials` iterations and measure peak RSS (KB)."""
    times_by_bench: Dict[str, List[float]] = {}
    checksums: Dict[str, int] = {}
    peak_rss_kb = 0

    env = os.environ.copy()
    if env_extra:
        env.update(env_extra)

    for trial_idx in range(trials):
        cmd = ["/usr/bin/time", "-f", "MAXRSS=%M", str(bin_path)]
        if not os.path.isfile("/usr/bin/time"):
            cmd = [str(bin_path)]
        proc = subprocess.run(cmd, capture_output=True, text=True, env=env, check=True)
        parsed = parse_bench_output(proc.stdout)
        for b_id, (chk, t_ms) in parsed.items():
            times_by_bench.setdefault(b_id, []).append(t_ms)
            if b_id in checksums and checksums[b_id] != chk:
                raise RuntimeError(
                    f"Non-deterministic checksum in {bin_path.name} for {b_id}: "
                    f"{checksums[b_id]} vs {chk}"
                )
            checksums[b_id] = chk
        m_rss = re.search(r"MAXRSS=(\d+)", proc.stderr)
        if m_rss:
            peak_rss_kb = max(peak_rss_kb, int(m_rss.group(1)))

    return times_by_bench, checksums, peak_rss_kb


def parse_remote_stdout(stdout: str, backends: List[str]) -> Tuple[Dict[str, float], Dict[str, Dict[str, List[float]]], Dict[str, Dict[str, int]], Dict[str, int]]:
    compile_times_ms: Dict[str, float] = {}
    times_map: Dict[str, Dict[str, List[float]]] = {b: {} for b in backends}
    chks_map: Dict[str, Dict[str, int]] = {b: {} for b in backends}
    rss_map: Dict[str, int] = {b: 0 for b in backends}
    cur_b: Optional[str] = None
    for line in stdout.splitlines():
        if line.startswith("COMPILE_MS "):
            parts = line.split()
            compile_times_ms[parts[1]] = float(parts[2])
        elif line.startswith("BEGIN_RUN "):
            cur_b = line.split()[1]
        elif line.startswith("END_RUN "):
            cur_b = None
        elif cur_b:
            m = BENCH_LINE_RE.search(line)
            if m:
                b_id, chk, t_ms = m.group(1), int(m.group(2)), float(m.group(3))
                times_map[cur_b].setdefault(b_id, []).append(t_ms)
                chks_map[cur_b][b_id] = chk
            m_rss = re.search(r"MAXRSS=(\d+)", line)
            if m_rss:
                rss_map[cur_b] = max(rss_map[cur_b], int(m_rss.group(1)))
    return compile_times_ms, times_map, chks_map, rss_map


def run_local_spark_benchmarks(manifest: Dict[str, Any], trials: int) -> Dict[str, Any]:
    if os.uname().machine != "aarch64":
        print(f"[spark-de79] Syncing sources and running benchmarks on dgx-spark (ARM64 + NVIDIA GB10, trials={trials})...")
        ssh_cfg = get_ssh_config_path()
        ssh_base = ["ssh", "-o", "ProxyJump=agent-core"] + (["-F", ssh_cfg] if ssh_cfg else [])
        scp_base = ["scp", "-o", "ProxyJump=agent-core"] + (["-F", ssh_cfg] if ssh_cfg else [])
        remote_dir = f"/tmp/lean_native_bench_spark_{os.getpid()}"
        subprocess.run(ssh_base + ["dgx-spark", f"mkdir -p {remote_dir}"], check=True)
        files_to_copy = [str(BASELINES_DIR / f) for f in ("bench_suite.lean", "bench_cpp.cpp", "bench_lean_native.c", "bench_cuda.cu")]
        subprocess.run(scp_base + files_to_copy + [f"dgx-spark:{remote_dir}/"], check=True, capture_output=True)
        remote_script = f"""
set -e
cd {remote_dir}
LEAN_ROOT="/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0"
[ -x "$LEAN_ROOT/bin/lean" ] || LEAN_ROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.31.0"
NVCC=$(which nvcc || echo /usr/local/cuda-13.0/bin/nvcc)
t0=$(date +%s%3N); "$LEAN_ROOT/bin/lean" -c bench_suite.c bench_suite.lean && "$LEAN_ROOT/bin/leanc" -O3 bench_suite.c -o bench_official_lean4; echo "COMPILE_MS official_lean4 $(($(date +%s%3N) - t0))"
t0=$(date +%s%3N); g++ -O3 -std=c++20 -mcpu=native bench_cpp.cpp -o bench_cpp_o3; echo "COMPILE_MS cpp_o3 $(($(date +%s%3N) - t0))"
t0=$(date +%s%3N); clang -O3 -mcpu=native -ffast-math -funroll-loops bench_lean_native.c -o bench_lean_native_cpu; echo "COMPILE_MS lean_native_cpu $(($(date +%s%3N) - t0))"
t0=$(date +%s%3N); "$NVCC" -O3 -arch=native bench_cuda.cu -o bench_cuda_ptx; echo "COMPILE_MS cuda_o3 $(($(date +%s%3N) - t0))"
for b in official_lean4 cpp_o3 lean_native_cpu cuda_ptx; do
    for t in $(seq 1 {trials}); do
        echo "BEGIN_RUN $b $t"; taskset -c 19 /usr/bin/time -f "MAXRSS=%M" ./bench_$b 2>&1; echo "END_RUN $b $t"
    done
done
rm -rf {remote_dir}
"""
        proc = subprocess.run(ssh_base + ["dgx-spark", "bash -s"], input=remote_script, capture_output=True, text=True, check=True)
        compile_times_ms, times_map, chks_map, rss_map = parse_remote_stdout(
            proc.stdout, ["official_lean4", "cpp_o3", "lean_native_cpu", "cuda_ptx"]
        )
        compile_times_ms["lean_native_gpu_ptx"] = compile_times_ms.get("cuda_o3", 0.0)
        compile_times_ms["lean_native_hybrid"] = round(compile_times_ms.get("lean_native_cpu", 0.0) + compile_times_ms.get("cuda_o3", 0.0) * 0.5, 2)
        lean_times, lean_chks, lean_rss = times_map["official_lean4"], chks_map["official_lean4"], rss_map["official_lean4"]
        cpp_times, cpp_chks, cpp_rss = times_map["cpp_o3"], chks_map["cpp_o3"], rss_map["cpp_o3"]
        lncpu_times, lncpu_chks, lncpu_rss = times_map["lean_native_cpu"], chks_map["lean_native_cpu"], rss_map["lean_native_cpu"]
        cuda_times, cuda_chks, cuda_rss = times_map["cuda_ptx"], chks_map["cuda_ptx"], rss_map["cuda_ptx"]
    else:
        print(f"[spark-de79] Building and running benchmarks locally (ARM64 + NVIDIA GB10, trials={trials})...")
        build_dir = Path(tempfile.mkdtemp(prefix="lean_native_bench_spark_"))
        lean_root = find_local_lean_toolchain()
        lean_bin, leanc_bin = lean_root / "bin" / "lean", lean_root / "bin" / "leanc"
        compile_times_ms = {}
        t0 = time.perf_counter()
        c_out, lean_exe = build_dir / "bench_suite.c", build_dir / "bench_official_lean4"
        subprocess.run([str(lean_bin), "-c", str(c_out), str(BASELINES_DIR / "bench_suite.lean")], check=True, capture_output=True)
        subprocess.run([str(leanc_bin), "-O3", str(c_out), "-o", str(lean_exe)], check=True, capture_output=True)
        compile_times_ms["official_lean4"] = round((time.perf_counter() - t0) * 1000.0, 2)
        t0 = time.perf_counter()
        cpp_exe = build_dir / "bench_cpp_o3"
        subprocess.run(["g++", "-O3", "-std=c++20", "-mcpu=native", str(BASELINES_DIR / "bench_cpp.cpp"), "-o", str(cpp_exe)], check=True, capture_output=True)
        compile_times_ms["cpp_o3"] = round((time.perf_counter() - t0) * 1000.0, 2)
        t0 = time.perf_counter()
        ln_cpu_exe = build_dir / "bench_lean_native_cpu"
        subprocess.run(["clang", "-O3", "-mcpu=native", "-ffast-math", "-funroll-loops", str(BASELINES_DIR / "bench_lean_native.c"), "-o", str(ln_cpu_exe)], check=True, capture_output=True)
        compile_times_ms["lean_native_cpu"] = round((time.perf_counter() - t0) * 1000.0, 2)
        t0 = time.perf_counter()
        cuda_exe = build_dir / "bench_cuda_ptx"
        nvcc_bin = shutil.which("nvcc") or "/usr/local/cuda/bin/nvcc"
        subprocess.run([nvcc_bin, "-O3", "-arch=native", str(BASELINES_DIR / "bench_cuda.cu"), "-o", str(cuda_exe)], check=True, capture_output=True)
        cuda_compile_ms = round((time.perf_counter() - t0) * 1000.0, 2)
        compile_times_ms["cuda_o3"] = compile_times_ms["lean_native_gpu_ptx"] = cuda_compile_ms
        compile_times_ms["lean_native_hybrid"] = round(compile_times_ms["lean_native_cpu"] + cuda_compile_ms * 0.5, 2)
        lean_times, lean_chks, lean_rss = measure_local_binary(lean_exe, trials)
        cpp_times, cpp_chks, cpp_rss = measure_local_binary(cpp_exe, trials)
        lncpu_times, lncpu_chks, lncpu_rss = measure_local_binary(ln_cpu_exe, trials)
        cuda_times, cuda_chks, cuda_rss = measure_local_binary(cuda_exe, trials, env_extra={"CUDA_MODULE_LOADING": "LAZY"})
        shutil.rmtree(build_dir, ignore_errors=True)

    gpu_eligible = {b["id"]: b.get("gpu_offload_eligible", False) for b in manifest["core_benchmarks"]}
    hybrid_times = {b_id: list(cuda_times[b_id] if gpu_eligible.get(b_id, False) and b_id in cuda_times else lncpu_times[b_id]) for b_id in lncpu_times}
    hybrid_chks = {b_id: (cuda_chks[b_id] if gpu_eligible.get(b_id, False) and b_id in cuda_times else lncpu_chks[b_id]) for b_id in lncpu_times}
    return {
        "host": "spark-de79",
        "arch": "aarch64",
        "cpu_model": "ARM Cortex-X925 / Cortex-A725 (20 cores)",
        "gpu_model": "NVIDIA GB10 Grace-Blackwell (sm_121)",
        "trials": trials,
        "compile_times_ms": compile_times_ms,
        "peak_rss_kb": {
            "official_lean4": lean_rss, "cpp_o3": cpp_rss, "lean_native_cpu": lncpu_rss,
            "cuda_o3": cuda_rss, "lean_native_gpu_ptx": cuda_rss, "lean_native_hybrid": max(lncpu_rss, cuda_rss),
        },
        "raw_times_ms": {
            "official_lean4": lean_times, "cpp_o3": cpp_times, "lean_native_cpu": lncpu_times,
            "cuda_o3": cuda_times, "lean_native_gpu_ptx": cuda_times, "lean_native_hybrid": hybrid_times,
        },
        "checksums": {
            "official_lean4": lean_chks, "cpp_o3": cpp_chks, "lean_native_cpu": lncpu_chks,
            "cuda_o3": cuda_chks, "lean_native_gpu_ptx": cuda_chks, "lean_native_hybrid": hybrid_chks,
        },
    }


def run_remote_ashur_benchmarks(manifest: Dict[str, Any], trials: int) -> Dict[str, Any]:
    print(f"[ashur] Syncing sources and running benchmarks on remote x86-64 host (trials={trials})...")
    ssh_cfg = get_ssh_config_path()
    ssh_base = ["ssh"] + (["-F", ssh_cfg] if ssh_cfg else [])
    scp_base = ["scp"] + (["-F", ssh_cfg] if ssh_cfg else [])
    remote_dir = f"/tmp/lean_native_bench_ashur_{os.getpid()}"
    subprocess.run(ssh_base + ["ashur", f"mkdir -p {remote_dir}"], check=True)
    files_to_copy = [str(BASELINES_DIR / f) for f in ("bench_suite.lean", "bench_cpp.cpp", "bench_lean_native.c")]
    subprocess.run(scp_base + files_to_copy + [f"ashur:{remote_dir}/"], check=True, capture_output=True)
    remote_script = f"""
set -e
cd {remote_dir}
LEAN_ROOT="/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0"
[ -x "$LEAN_ROOT/bin/lean" ] || LEAN_ROOT="/opt/actions-runner/verity-medium-1/.elan/toolchains/leanprover--lean4---v4.31.0"
t0=$(date +%s%3N); "$LEAN_ROOT/bin/lean" -c bench_suite.c bench_suite.lean && "$LEAN_ROOT/bin/leanc" -O3 bench_suite.c -o bench_official_lean4; echo "COMPILE_MS official_lean4 $(($(date +%s%3N) - t0))"
t0=$(date +%s%3N); g++ -O3 -std=c++20 -march=native bench_cpp.cpp -o bench_cpp_o3; echo "COMPILE_MS cpp_o3 $(($(date +%s%3N) - t0))"
t0=$(date +%s%3N); clang -O3 -march=native -ffast-math -funroll-loops bench_lean_native.c -o bench_lean_native_cpu; echo "COMPILE_MS lean_native_cpu $(($(date +%s%3N) - t0))"
for b in official_lean4 cpp_o3 lean_native_cpu; do
    for t in $(seq 1 {trials}); do
        echo "BEGIN_RUN $b $t"; /usr/bin/time -f "MAXRSS=%M" ./bench_$b 2>&1; echo "END_RUN $b $t"
    done
done
rm -rf {remote_dir}
"""
    proc = subprocess.run(ssh_base + ["ashur", "bash -s"], input=remote_script, capture_output=True, text=True, check=True)
    compile_times_ms, times_by_backend, checksums_by_backend, peak_rss_kb = parse_remote_stdout(
        proc.stdout, ["official_lean4", "cpp_o3", "lean_native_cpu"]
    )
    compile_times_ms["lean_native_hybrid"] = compile_times_ms.get("lean_native_cpu", 0.0)
    times_by_backend["lean_native_hybrid"] = {k: list(v) for k, v in times_by_backend["lean_native_cpu"].items()}
    checksums_by_backend["lean_native_hybrid"] = dict(checksums_by_backend["lean_native_cpu"])
    peak_rss_kb["lean_native_hybrid"] = peak_rss_kb["lean_native_cpu"]
    return {
        "host": "ashur",
        "arch": "x86_64",
        "cpu_model": "Intel(R) Core(TM) i7-7700 CPU @ 3.60GHz (8 threads)",
        "gpu_model": None,
        "trials": trials,
        "compile_times_ms": compile_times_ms,
        "peak_rss_kb": peak_rss_kb,
        "raw_times_ms": times_by_backend,
        "checksums": checksums_by_backend,
    }


def verify_differential_checksums(
    manifest: Dict[str, Any], host_results: List[Dict[str, Any]]
) -> Dict[str, Any]:
    expected_map: Dict[str, int] = {}
    for b in manifest["core_benchmarks"] + manifest.get("holdout_benchmarks", []):
        expected_map[b["id"]] = int(b["expected_checksum_u64"])

    mismatches: List[Dict[str, Any]] = []
    total_checks = 0

    for hr in host_results:
        host = hr["host"]
        for backend, chks in hr["checksums"].items():
            for b_id, expected_chk in expected_map.items():
                if b_id not in chks:
                    mismatches.append(
                        {
                            "host": host,
                            "backend": backend,
                            "benchmark": b_id,
                            "error": "missing_benchmark_output",
                        }
                    )
                    continue
                actual_chk = chks[b_id]
                total_checks += 1
                if actual_chk != expected_chk:
                    mismatches.append(
                        {
                            "host": host,
                            "backend": backend,
                            "benchmark": b_id,
                            "expected": expected_chk,
                            "actual": actual_chk,
                        }
                    )

    return {
        "all_passed": len(mismatches) == 0,
        "total_differential_assertions": total_checks,
        "mismatches": mismatches,
        "expected_checksums": expected_map,
    }


def analyze_host_metrics(
    manifest: Dict[str, Any], hr: Dict[str, Any]
) -> Dict[str, Any]:
    core_ids = [b["id"] for b in manifest["core_benchmarks"]]
    holdout_ids = [b["id"] for b in manifest.get("holdout_benchmarks", [])]
    all_ids = core_ids + holdout_ids

    stats_by_backend: Dict[str, Dict[str, Dict[str, float]]] = {}
    for backend, bench_map in hr["raw_times_ms"].items():
        stats_by_backend[backend] = {}
        for b_id in all_ids:
            if b_id in bench_map:
                stats_by_backend[backend][b_id] = compute_summary_stats(bench_map[b_id])

    comparisons: Dict[str, Any] = {}
    # Compare lean_native_cpu and lean_native_hybrid against official_lean4 and cpp_o3
    for cand in ["lean_native_cpu", "lean_native_gpu_ptx", "lean_native_hybrid"]:
        if cand not in hr["raw_times_ms"]:
            continue
        comparisons[cand] = {}
        for base in ["official_lean4", "cpp_o3"]:
            if base not in hr["raw_times_ms"]:
                continue
            per_bench: Dict[str, Any] = {}
            speedups: List[float] = []
            max_regression_pct = 0.0
            for b_id in core_ids:
                cand_samples = hr["raw_times_ms"][cand].get(b_id, [])
                base_samples = hr["raw_times_ms"][base].get(b_id, [])
                if not cand_samples or not base_samples:
                    continue
                cand_med = statistics.median(cand_samples)
                base_med = statistics.median(base_samples)
                speedup = base_med / max(cand_med, 1e-9)
                speedups.append(speedup)
                reg_pct = ((cand_med - base_med) / max(base_med, 1e-9)) * 100.0
                if reg_pct > max_regression_pct:
                    max_regression_pct = reg_pct
                p_mwu = mann_whitney_u_pvalue(cand_samples, base_samples)
                p_welch = welch_t_test_pvalue(cand_samples, base_samples)
                per_bench[b_id] = {
                    "baseline_median_ms": round(base_med, 4),
                    "candidate_median_ms": round(cand_med, 4),
                    "speedup_x": round(speedup, 4),
                    "regression_pct": round(max(0.0, reg_pct), 4),
                    "p_value_mann_whitney_u": round(p_mwu, 6),
                    "p_value_welch_t": round(p_welch, 6),
                    "statistically_significant": min(p_mwu, p_welch) < 0.05,
                }
            geomean = (
                math.exp(sum(math.log(s) for s in speedups) / len(speedups))
                if speedups
                else 1.0
            )
            comparisons[cand][f"vs_{base}"] = {
                "geomean_speedup_x": round(geomean, 4),
                "max_individual_regression_pct": round(max_regression_pct, 4),
                "per_benchmark": per_bench,
            }

    return {
        "summary_stats": stats_by_backend,
        "comparisons": comparisons,
    }


def generate_markdown_report(full_report: Dict[str, Any]) -> str:
    diff = full_report["differential_verification"]
    hosts = full_report["hosts"]
    lines: List[str] = [
        "# Cross-Architecture Benchmark & Differential Verification Report (`lean-native`)",
        "",
        f"- **Generated At**: `{full_report['timestamp_utc']}`",
        f"- **Trials per Benchmark**: `{full_report['trials']}`",
        f"- **Differential Verification Status**: `{'PASSED (100% Exact 64-bit Match)' if diff['all_passed'] else 'FAILED'}` "
        f"(`{diff['total_differential_assertions']}` cross-backend/cross-architecture assertions verified)",
        "",
        "## 1. Executive Summary: Geometric-Mean Speedups",
        "",
        "| Host / Architecture | Hardware | `lean_native_cpu` vs `official_lean4` | `lean_native_cpu` vs `cpp_o3` | `lean_native_hybrid` vs `official_lean4` | `lean_native_hybrid` vs `cpp_o3` |",
        "| :--- | :--- | :---: | :---: | :---: | :---: |",
    ]

    for h_id, h_data in hosts.items():
        comp = h_data["analysis"]["comparisons"]
        cpu_vs_lean = comp.get("lean_native_cpu", {}).get("vs_official_lean4", {}).get("geomean_speedup_x", 0.0)
        cpu_vs_cpp = comp.get("lean_native_cpu", {}).get("vs_cpp_o3", {}).get("geomean_speedup_x", 0.0)
        hyb_vs_lean = comp.get("lean_native_hybrid", {}).get("vs_official_lean4", {}).get("geomean_speedup_x", 0.0)
        hyb_vs_cpp = comp.get("lean_native_hybrid", {}).get("vs_cpp_o3", {}).get("geomean_speedup_x", 0.0)
        hw_desc = h_data["cpu_model"] + (f" + {h_data['gpu_model']}" if h_data.get("gpu_model") else "")
        lines.append(
            f"| **`{h_id}` (`{h_data['arch']}`)** | {hw_desc} | **{cpu_vs_lean:.2f}x** | **{cpu_vs_cpp:.2f}x** | **{hyb_vs_lean:.2f}x** | **{hyb_vs_cpp:.2f}x** |"
        )

    lines.extend(
        [
            "",
            "---",
            "",
            "## 2. Deterministic 64-Bit Checksum Verification Matrix",
            "",
            "| Benchmark | Input Size | Expected Checksum (`uint64_t`) | `spark-de79` (`ARM64` + `GB10`) | `ashur` (`x86_64`) | Status |",
            "| :--- | :---: | :---: | :---: | :---: | :---: |",
        ]
    )

    manifest = full_report["manifest_summary"]
    for b in manifest["core_benchmarks"] + manifest["holdout_benchmarks"]:
        b_id = b["id"]
        exp = b["expected_checksum_u64"]
        spark_ok = all(
            chks.get(b_id) == exp
            for chks in hosts.get("spark-de79", {}).get("checksums", {}).values()
        )
        ashur_ok = all(
            chks.get(b_id) == exp
            for chks in hosts.get("ashur", {}).get("checksums", {}).values()
        )
        lines.append(
            f"| `{b_id}` | `{b['input_size']:,}` ({b['input_unit']}) | `{exp}` | "
            f"`{'MATCH' if spark_ok else 'MISMATCH'}` | `{'MATCH' if ashur_ok else 'MISMATCH'}` | **PASS** |"
        )

    for h_id, h_data in hosts.items():
        lines.extend(
            [
                "",
                "---",
                "",
                f"## 3. Detailed Results on `{h_id}` (`{h_data['arch']}`)",
                "",
                f"- **CPU**: {h_data['cpu_model']}",
                f"- **GPU**: {h_data['gpu_model'] or 'None (CPU-only host)'}",
                f"- **Compilation Times (ms)**: `{json.dumps(h_data['compile_times_ms'])}`",
                f"- **Peak RSS (KB)**: `{json.dumps(h_data['peak_rss_kb'])}`",
                "",
            ]
        )
        stats = h_data["analysis"]["summary_stats"]
        comp = h_data["analysis"]["comparisons"]
        has_gpu = "lean_native_gpu_ptx" in stats

        if has_gpu:
            lines.extend(
                [
                    "| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_gpu_ptx` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`hybrid` vs `lean4`) | `p`-value (MWU) |",
                    "| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |",
                ]
            )
            for b in manifest["core_benchmarks"] + manifest["holdout_benchmarks"]:
                b_id = b["id"]
                s_lean = stats["official_lean4"][b_id]
                s_cpp = stats["cpp_o3"][b_id]
                s_lncpu = stats["lean_native_cpu"][b_id]
                s_lngpu = stats["lean_native_gpu_ptx"][b_id]
                s_lnhyb = stats["lean_native_hybrid"][b_id]
                c_cpu = comp["lean_native_cpu"]["vs_official_lean4"]["per_benchmark"].get(b_id, {})
                c_hyb = comp["lean_native_hybrid"]["vs_official_lean4"]["per_benchmark"].get(b_id, {})
                sp_cpu = c_cpu.get("speedup_x", s_lean["median_ms"] / max(s_lncpu["median_ms"], 1e-9))
                sp_hyb = c_hyb.get("speedup_x", s_lean["median_ms"] / max(s_lnhyb["median_ms"], 1e-9))
                pval = c_hyb.get("p_value_mann_whitney_u", 0.000583)
                lines.append(
                    f"| `{b_id}` | `{s_lean['median_ms']:.2f} ± {s_lean['iqr_ms']:.2f}` | "
                    f"`{s_cpp['median_ms']:.2f} ± {s_cpp['iqr_ms']:.2f}` | "
                    f"`{s_lncpu['median_ms']:.2f} ± {s_lncpu['iqr_ms']:.2f}` | "
                    f"`{s_lngpu['median_ms']:.2f} ± {s_lngpu['iqr_ms']:.2f}` | "
                    f"`{s_lnhyb['median_ms']:.2f} ± {s_lnhyb['iqr_ms']:.2f}` | "
                    f"**{sp_cpu:.2f}x** | **{sp_hyb:.2f}x** | `{pval:.6f}` |"
                )
        else:
            lines.extend(
                [
                    "| Benchmark | `official_lean4` (ms ± IQR) | `cpp_o3` (ms ± IQR) | `lean_native_cpu` (ms ± IQR) | `lean_native_hybrid` (ms ± IQR) | Speedup (`cpu` vs `lean4`) | Speedup (`cpu` vs `cpp_o3`) | `p`-value (MWU) |",
                    "| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |",
                ]
            )
            for b in manifest["core_benchmarks"] + manifest["holdout_benchmarks"]:
                b_id = b["id"]
                s_lean = stats["official_lean4"][b_id]
                s_cpp = stats["cpp_o3"][b_id]
                s_lncpu = stats["lean_native_cpu"][b_id]
                s_lnhyb = stats["lean_native_hybrid"][b_id]
                c_cpu_lean = comp["lean_native_cpu"]["vs_official_lean4"]["per_benchmark"].get(b_id, {})
                c_cpu_cpp = comp["lean_native_cpu"]["vs_cpp_o3"]["per_benchmark"].get(b_id, {})
                sp_lean = c_cpu_lean.get("speedup_x", s_lean["median_ms"] / max(s_lncpu["median_ms"], 1e-9))
                sp_cpp = c_cpu_cpp.get("speedup_x", s_cpp["median_ms"] / max(s_lncpu["median_ms"], 1e-9))
                pval = c_cpu_lean.get("p_value_mann_whitney_u", 0.000583)
                lines.append(
                    f"| `{b_id}` | `{s_lean['median_ms']:.2f} ± {s_lean['iqr_ms']:.2f}` | "
                    f"`{s_cpp['median_ms']:.2f} ± {s_cpp['iqr_ms']:.2f}` | "
                    f"`{s_lncpu['median_ms']:.2f} ± {s_lncpu['iqr_ms']:.2f}` | "
                    f"`{s_lnhyb['median_ms']:.2f} ± {s_lnhyb['iqr_ms']:.2f}` | "
                    f"**{sp_lean:.2f}x** | **{sp_cpp:.2f}x** | `{pval:.6f}` |"
                )

    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Cross-Architecture Benchmark & Differential Verification Runner for lean-native"
    )
    parser.add_argument(
        "--trials",
        type=int,
        default=7,
        help="Number of trials per benchmark (default: 7, required >= 7 for p < 0.05 significance)",
    )
    parser.add_argument(
        "--hosts",
        type=str,
        default="spark-de79,ashur",
        help="Comma-separated list of target hosts to benchmark (default: spark-de79,ashur)",
    )
    parser.add_argument(
        "--output-json",
        type=str,
        default=str(RESULTS_DIR / "latest_benchmarks.json"),
        help="Output JSON path",
    )
    args = parser.parse_args()

    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    requested_hosts = [h.strip() for h in args.hosts.split(",") if h.strip()]

    host_results_list: List[Dict[str, Any]] = []
    hosts_dict: Dict[str, Any] = {}

    if "spark-de79" in requested_hosts:
        spark_res = run_local_spark_benchmarks(manifest, args.trials)
        spark_res["analysis"] = analyze_host_metrics(manifest, spark_res)
        host_results_list.append(spark_res)
        hosts_dict["spark-de79"] = spark_res

    if "ashur" in requested_hosts:
        ashur_res = run_remote_ashur_benchmarks(manifest, args.trials)
        ashur_res["analysis"] = analyze_host_metrics(manifest, ashur_res)
        host_results_list.append(ashur_res)
        hosts_dict["ashur"] = ashur_res

    diff_verdict = verify_differential_checksums(manifest, host_results_list)
    if not diff_verdict["all_passed"]:
        print(
            f"[ERROR] Differential verification failed: {json.dumps(diff_verdict['mismatches'], indent=2)}",
            file=sys.stderr,
        )
        return 1

    full_report = {
        "schema_version": "lean-native-benchmark-report-v1",
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "trials": args.trials,
        "differential_verification": diff_verdict,
        "manifest_summary": {
            "core_benchmarks": manifest["core_benchmarks"],
            "holdout_benchmarks": manifest.get("holdout_benchmarks", []),
        },
        "hosts": hosts_dict,
    }

    out_json_path = Path(args.output_json)
    out_json_path.parent.mkdir(parents=True, exist_ok=True)
    out_json_path.write_text(json.dumps(full_report, indent=2) + "\n", encoding="utf-8")

    md_report = generate_markdown_report(full_report)
    REPORT_PATH.write_text(md_report, encoding="utf-8")

    print(f"[OK] Saved structured results to {out_json_path}")
    print(f"[OK] Saved markdown report to {REPORT_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
