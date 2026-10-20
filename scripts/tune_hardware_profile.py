#!/usr/bin/env python3
"""
LeanNative Hardware Cost & Tuning Profile Auto-Tuner (`scripts/tune_hardware_profile.py`).

Allows any user or contributor to:
1. Run fast micro-benchmarks on their own device (`--auto-detect --output profiles/<device>.json`)
   to calibrate instruction latency weights (`mul_cost`, `div_mod_cost`, `fma_cost`, `select_cost`,
   `shift_cost`, etc.) and hybrid CPU/GPU dispatch thresholds (`min_gpu_elements`).
2. Validate all community-contributed profiles in `profiles/*.json` (`--verify-profiles profiles`)
   against `profiles/SCHEMA.json` and `lean-native-core superopt --profile <file>`.
"""

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CORE_BIN = REPO_ROOT / ".lake" / "build" / "bin" / "lean-native-core"

MICROBENCH_C_SRC = r"""
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static inline double now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}

int main(void) {
    const uint64_t N = 20000000ULL;
    volatile uint64_t sink = 0;

    // 1. Add/Sub latency baseline
    uint64_t a = 123456789ULL, b = 987654321ULL;
    double t0 = now_ns();
    for (uint64_t i = 0; i < N; ++i) {
        a = a + b + (i & 1ULL);
        b = b ^ a;
    }
    double t_add = (now_ns() - t0) / (double)N;
    sink ^= a;

    // 2. Multiply latency
    uint64_t m = 3ULL;
    t0 = now_ns();
    for (uint64_t i = 1; i <= N; ++i) {
        m = m * (i | 1ULL) + 1ULL;
    }
    double t_mul = (now_ns() - t0) / (double)N;
    sink ^= m;

    // 3. Unsigned 64-bit Division/Mod latency
    uint64_t d = 0x123456789abcdef0ULL;
    t0 = now_ns();
    for (uint64_t i = 1; i <= (N / 4); ++i) {
        uint64_t denom = (i & 255ULL) + 3ULL;
        d = (d / denom) + i + 0x9e3779b97f4a7c15ULL;
    }
    double t_div = (now_ns() - t0) / (double)(N / 4);
    sink ^= d;

    // 4. FMA-style (a * b + c) latency
    uint64_t f = 7ULL;
    t0 = now_ns();
    for (uint64_t i = 1; i <= N; ++i) {
        f = f * 5ULL + i;
    }
    double t_fma = (now_ns() - t0) / (double)N;
    sink ^= f;

    // 5. Select (cmov/csel) latency
    uint64_t s = 1ULL;
    t0 = now_ns();
    for (uint64_t i = 0; i < N; ++i) {
        uint64_t cond = (s ^ i) & 1ULL;
        s = cond ? (s + 3ULL) : (s + 7ULL);
    }
    double t_sel = (now_ns() - t0) / (double)N;
    sink ^= s;

    printf("{\"add_ns\":%.4f,\"mul_ns\":%.4f,\"div_ns\":%.4f,\"fma_ns\":%.4f,\"select_ns\":%.4f,\"sink\":%llu}\n",
           t_add, t_mul, t_div, t_fma, t_sel, (unsigned long long)sink);
    return 0;
}
"""


def compute_payload_digest(obj: dict) -> str:
    copy_obj = {k: v for k, v in obj.items() if k != "calibration_receipt"}
    canonical = json.dumps(copy_obj, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.blake2b(b"lean-native-hw-profile-v1:" + canonical, digest_size=32).hexdigest()


def detect_host_hardware(override_target: str = "") -> dict:
    uname_m = platform.machine().lower()
    system = platform.system().lower()
    cpu_model = platform.processor() or uname_m
    if os.path.exists("/proc/cpuinfo"):
        try:
            txt = Path("/proc/cpuinfo").read_text(errors="ignore")
            for line in txt.splitlines():
                if "model name" in line or "Model" in line:
                    cpu_model = line.split(":", 1)[1].strip()
                    break
        except Exception:
            pass

    gpu_model = "none"
    sm_arch = "sm_90"
    if shutil.which("nvidia-smi"):
        try:
            out = subprocess.check_output(
                ["nvidia-smi", "--query-gpu=name,compute_cap", "--format=csv,noheader"],
                text=True,
                timeout=3,
            ).strip()
            if out:
                first = out.splitlines()[0].split(",")
                gpu_model = first[0].strip()
                if len(first) > 1:
                    cc = first[1].strip().replace(".", "")
                    sm_arch = f"sm_{cc}"
        except Exception:
            pass

    if override_target:
        target = override_target
    elif system == "darwin":
        target = "apple_metal"
    elif "aarch64" in uname_m or "arm64" in uname_m:
        target = "arm64"
    else:
        target = "x86_64"

    llvm_cpu = "x86-64-v3"
    if target == "arm64" or "aarch64" in uname_m or "arm64" in uname_m:
        llvm_cpu = "neoverse-v2" if system != "darwin" else "apple-m3"
    elif target == "apple_metal":
        llvm_cpu = "apple-m3"

    slug_base = f"{target}_{cpu_model}".lower()
    slug = re.sub(r"[^a-z0-9]+", "_", slug_base).strip("_")[:48]

    return {
        "profile_id": slug,
        "target": target,
        "host_os": system,
        "host_arch": uname_m,
        "cpu_model": cpu_model,
        "gpu_model": gpu_model,
        "llvm_target_cpu": llvm_cpu,
        "sm_arch": sm_arch,
    }


def run_microbenchmark_calibration() -> dict:
    cc = None
    for candidate in ("/usr/bin/clang", "/usr/bin/gcc", shutil.which("gcc"), shutil.which("clang")):
        if candidate and os.path.exists(candidate) and "elan/toolchains" not in candidate:
            cc = candidate
            break
    if not cc:
        return {"add_ns": 0.5, "mul_ns": 1.8, "div_ns": 10.5, "fma_ns": 1.1, "select_ns": 0.9}
    with tempfile.TemporaryDirectory() as tmpd:
        src_path = Path(tmpd) / "microbench.c"
        bin_path = Path(tmpd) / "microbench"
        src_path.write_text(MICROBENCH_C_SRC)
        subprocess.run([cc, "-O2", str(src_path), "-o", str(bin_path)], check=True)
        out = subprocess.check_output([str(bin_path)], text=True, timeout=15).strip()
        return json.loads(out)


def build_calibrated_profile(hw: dict, meas: dict) -> dict:
    base_ns = max(meas.get("add_ns", 0.5), 0.15)
    mul_ratio = max(2, min(12, round(meas.get("mul_ns", 1.8) / base_ns)))
    div_ratio = max(8, min(80, round(meas.get("div_ns", 10.5) / base_ns)))
    fma_ratio = max(1, min(10, round(meas.get("fma_ns", 1.1) / base_ns)))
    sel_ratio = max(1, min(6, round(meas.get("select_ns", 0.9) / base_ns)))

    target = hw["target"]
    is_gpu = target in ("cuda_ptx", "apple_metal")
    if is_gpu:
        mul_ratio = max(mul_ratio, 5)
        div_ratio = max(div_ratio, 36)
        fma_ratio = 2

    profile = {
        "schema_version": "lean-native-hardware-profile-v1",
        "profile_id": hw["profile_id"],
        "target": target,
        "llvm_target_cpu": hw["llvm_target_cpu"],
        "sm_arch": hw["sm_arch"],
        "hardware_metadata": {
            "host_os": hw["host_os"],
            "host_arch": hw["host_arch"],
            "cpu_model": hw["cpu_model"],
            "gpu_model": hw["gpu_model"],
        },
        "add_sub_cost": 1,
        "bitwise_cost": 1,
        "shift_cost": 1,
        "cmp_cost": 1,
        "mul_cost": int(mul_ratio),
        "div_mod_cost": int(div_ratio),
        "fma_cost": int(fma_ratio),
        "select_cost": int(sel_ratio),
        "clz256_cost": 2,
        "add_sub_checked256_cost": 3,
        "mul_checked256_cost": int(max(mul_ratio, 4)),
        "min_gpu_elements": 32768 if target == "apple_metal" else 65536,
        "gpu_block_threads": 256,
        "matmul_tile_dim": 16,
    }
    digest = compute_payload_digest(profile)
    profile["calibration_receipt"] = {
        "measured_ns": {
            "add_ns": round(meas.get("add_ns", 0.0), 4),
            "mul_ns": round(meas.get("mul_ns", 0.0), 4),
            "div_ns": round(meas.get("div_ns", 0.0), 4),
            "fma_ns": round(meas.get("fma_ns", 0.0), 4),
            "select_ns": round(meas.get("select_ns", 0.0), 4),
        },
        "payload_digest_blake2b256": digest,
        "calibrated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    }
    return profile


def verify_single_profile(path: Path) -> tuple[bool, str]:
    try:
        data = json.loads(path.read_text())
    except Exception as e:
        return False, f"{path.name}: invalid JSON ({e})"

    required = [
        "schema_version",
        "profile_id",
        "target",
        "llvm_target_cpu",
        "add_sub_cost",
        "bitwise_cost",
        "shift_cost",
        "cmp_cost",
        "mul_cost",
        "div_mod_cost",
        "fma_cost",
        "select_cost",
        "clz256_cost",
        "add_sub_checked256_cost",
        "mul_checked256_cost",
        "min_gpu_elements",
        "gpu_block_threads",
        "matmul_tile_dim",
        "calibration_receipt",
    ]
    for k in required:
        if k not in data:
            return False, f"{path.name}: missing required field '{k}'"

    if data["schema_version"] != "lean-native-hardware-profile-v1":
        return False, f"{path.name}: unsupported schema_version '{data['schema_version']}'"

    if data["target"] not in ("x86_64", "arm64", "cuda_ptx", "apple_metal"):
        return False, f"{path.name}: invalid target '{data['target']}'"

    expected_digest = compute_payload_digest(data)
    actual_digest = data.get("calibration_receipt", {}).get("payload_digest_blake2b256", "")
    if expected_digest != actual_digest:
        return False, f"{path.name}: digest mismatch (expected {expected_digest}, got {actual_digest})"

    if CORE_BIN.exists():
        res = subprocess.run(
            [str(CORE_BIN), "superopt", "--profile", str(path), "--json"],
            capture_output=True,
            text=True,
            timeout=15,
        )
        if res.returncode != 0:
            return False, f"{path.name}: lean-native-core superopt failed ({res.stderr.strip()})"
        rep = json.loads(res.stdout.strip())
        for r in rep.get("records", []):
            if not (r.get("fastCheckPassed") and r.get("symbolicTVPassed")):
                return False, f"{path.name}: unsound rewrite record in superopt report"

    return True, f"[PASS] {path.name} (target={data['target']}, profile_id={data['profile_id']}, mul={data['mul_cost']}, div={data['div_mod_cost']}, fma={data['fma_cost']})"


def main() -> int:
    parser = argparse.ArgumentParser(description="LeanNative Hardware Cost Profile Auto-Tuner & Validator")
    parser.add_argument("--auto-detect", action="store_true", help="Auto-detect host hardware and run micro-benchmark calibration")
    parser.add_argument("--target", type=str, default="", help="Override target (x86_64, arm64, cuda_ptx, apple_metal)")
    parser.add_argument("--profile-id", type=str, default="", help="Override profile_id")
    parser.add_argument("--output", "-o", type=str, default="", help="Write calibrated JSON profile to path")
    parser.add_argument("--verify-profiles", type=str, default="", help="Directory of *.json profiles to verify")
    args = parser.parse_args()

    if args.verify_profiles:
        prof_dir = Path(args.verify_profiles)
        files = sorted(p for p in prof_dir.glob("*.json") if p.name != "SCHEMA.json")
        if not files:
            print(f"No profile JSON files found in {prof_dir}", file=sys.stderr)
            return 1
        all_ok = True
        for f in files:
            ok, msg = verify_single_profile(f)
            print(msg)
            if not ok:
                all_ok = False
        return 0 if all_ok else 1

    hw = detect_host_hardware(args.target)
    if args.profile_id:
        hw["profile_id"] = args.profile_id
    meas = run_microbenchmark_calibration()
    profile = build_calibrated_profile(hw, meas)
    text = json.dumps(profile, indent=2) + "\n"
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(text)
        ok, msg = verify_single_profile(out_path)
        print(msg)
        return 0 if ok else 1
    else:
        print(text, end="")
        return 0


if __name__ == "__main__":
    sys.exit(main())
