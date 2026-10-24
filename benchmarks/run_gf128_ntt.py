#!/usr/bin/env python3
import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import statistics
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def parse(text):
    out = {}
    for line in text.splitlines():
        fields = line.split(":")
        if len(fields) == 4 and fields[0] == "BENCH":
            name = fields[1]
            out[name] = {"checksum": int(fields[2].split("=", 1)[1]), "time_ns": int(fields[3].split("=", 1)[1])}
    return out

def run(cmd):
    return parse(subprocess.run(cmd, cwd=ROOT, check=True, capture_output=True, text=True).stdout)

def stats(xs, ops):
    ys = sorted(xs)
    median_ns = statistics.median(ys)
    return {"samples_ns": xs, "median_ns": median_ns, "iqr_ns": ys[(len(ys) * 3) // 4] - ys[len(ys) // 4], "min_ns": min(ys), "max_ns": max(ys), "stdev_ns": statistics.stdev(xs) if len(xs) > 1 else 0, "ops_per_trial": ops, "median_ops_per_sec": (ops * 1_000_000_000.0) / median_ns}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--warmups", type=int, default=9)
    ap.add_argument("--trials", type=int, default=9)
    ap.add_argument("--out", type=Path, default=ROOT / "benchmarks/results/gf128_ntt_v1.raw.json")
    args = ap.parse_args()
    if args.warmups < 9 or args.trials < 9:
        raise SystemExit("warmups and trials must be >= 9")
    ops = {"gf128_scalar": {"unit": "field_muls_per_sec", "count": 4096}, "ntt_modular": {"unit": "butterflies_per_sec", "count": 64 * 8 * 128}}
    lean_bin = Path("/tmp/gf128_ntt_v1_lean")
    c_bin = Path("/tmp/gf128_ntt_v1_c")
    subprocess.run([str(ROOT / ".lake/build/bin/lean-native"), "build-exe", "benchmarks/gf128_ntt_v1.lean", "-o", str(lean_bin)], cwd=ROOT, check=True)
    subprocess.run(["clang", "-O3", "-march=native", "benchmarks/gf128_ntt_v1.c", "-o", str(c_bin)], cwd=ROOT, check=True)
    targets = [("lean_native", [str(lean_bin)]), ("c_o3", [str(c_bin)])]
    for step in range(args.warmups):
        ordered = targets if step % 2 == 0 else list(reversed(targets))
        for _, command in ordered:
            run(command)
    samples = {"lean_native": {}, "c_o3": {}}
    checksums = {"lean_native": {}, "c_o3": {}}
    for trial in range(args.trials):
        ordered = targets if trial % 2 == 0 else list(reversed(targets))
        for label, command in ordered:
            result = run(command)
            for name, value in result.items():
                samples[label].setdefault(name, []).append(value["time_ns"])
                checksums[label].setdefault(name, value["checksum"])
                if checksums[label][name] != value["checksum"]:
                    raise RuntimeError(f"checksum changed for {label}/{name}")
    all_results = {label: {name: {"checksum": checksums[label][name], "metric": ops[name]["unit"], **stats(values, ops[name]["count"])} for name, values in samples[label].items()} for label in samples}
    for name in all_results["lean_native"]:
        if all_results["lean_native"][name]["checksum"] != all_results["c_o3"][name]["checksum"]:
            raise RuntimeError(f"checksum mismatch for {name}")
    metadata = {"suite": "gf128_ntt", "version": "v1", "warmups": args.warmups, "trials": args.trials, "interleaving": "alternating (lean_native,c_o3) / (c_o3,lean_native) across warmups and trials", "flags": {"lean_native": ["build-exe", "--opt", "-O3", "-march=native"], "c_o3": ["-O3", "-march=native"]}, "primitives_truth": {"gf128": "4 independent 64x64->128 carryless products (clmul64 + clmul64Hi) lowered to @llvm.x86.pclmulqdq / @llvm.aarch64.neon.pmull64 with deferred reduction mod x^128+x^7+x^2+x+1 (0x87); portable fallback on wasm32/nvptx64/baseline; gf2Affine remains scalar parity; eor3 remains packed binary", "ntt": "iterative modular butterfly mod 998244353 with 2-round radix-4 lookahead (no Karatsuba)", "build_exe_path": "Lean source -> LCNF -> emitC + ln_c_opt.py + LNIR LLVM intrinsic override + opt -O3"}, "host": {"uname": platform.uname()._asdict(), "cpu": platform.processor()}, "commit_id": subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip(), "scripts_ln_c_opt_status": subprocess.run(["git", "status", "--short", "--", "scripts/ln_c_opt.py"], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip(), "commands": {"lean_build": [str(ROOT / ".lake/build/bin/lean-native"), "build-exe", "benchmarks/gf128_ntt_v1.lean", "-o", "/tmp/gf128_ntt_v1_lean"], "c_build": ["clang", "-O3", "-march=native", "benchmarks/gf128_ntt_v1.c", "-o", "/tmp/gf128_ntt_v1_c"]}, "generated_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(), "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT / "benchmarks/gf128_ntt_v1.lean", ROOT / "benchmarks/gf128_ntt_v1.c", ROOT / "scripts/ln_c_opt.py"]}, "results": all_results}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps(metadata, indent=2))

if __name__ == "__main__":
    main()
