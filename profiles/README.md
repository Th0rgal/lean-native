# LeanNative Hardware Cost & Tuning Profiles (`profiles/`)

This directory contains declarative, hardware-calibrated cost and dispatch profiles (`*.json`) used by:
- **`LeanNative.Transform.Superopt`** (`lean-native-core superopt --profile profiles/<device>.json`)
- **`LeanNative.Backend.Hybrid`** (`lean-native-core compile-hybrid --profile profiles/<device>.json`)
- **`autoresearch/`** (profile-guided superoptimization & cross-architecture benchmarking)

---

## 1. Safety & Soundness Guarantee (Law 1 & Law 5)

**Can a misconfigured or adversarial hardware profile break compiler correctness?**
**No.** By design (**Law 1: Segregated Plugin & Cost Boundary**), a `HardwareCostProfile` only supplies integer latency weights (`mul_cost`, `div_mod_cost`, `fma_cost`, `shift_cost`, etc.) and dispatch thresholds (`min_gpu_elements`, `gpu_block_threads`, `matmul_tile_dim`).
Every candidate rewrite considered under any profile is still strictly gated by:
1. `fastCheckScalarEquiv` (concrete boundary + SplitMix64 counterexample filter)
2. `symCheckScalarEquiv` (Alive2-style symbolic translation validation) or an in-kernel Lean 4 theorem (`LeanNative.Proofs.rewriteScalarVerified_sound` with `0 sorryAx`).

---

## 2. Auto-Tuning on Your Own Device

You can generate a calibrated profile for your own CPU/GPU in ~3 seconds using [`scripts/tune_hardware_profile.py`](../scripts/tune_hardware_profile.py):

```bash
# Auto-detect your local CPU/GPU, run micro-benchmark calibration, and emit a signed JSON profile:
python3 scripts/tune_hardware_profile.py --auto-detect --output profiles/my_device.json

# Test your profile with lean-native-core:
./.lake/build/bin/lean-native-core superopt --profile profiles/my_device.json

# Validate all profiles in profiles/ (run automatically in GitHub Actions CI):
python3 scripts/tune_hardware_profile.py --verify-profiles profiles
```

---

## 3. Submitting a Pull Request for a New Hardware Target

Community PRs adding or refining hardware profiles in `profiles/*.json` are welcome!
To contribute a profile for your hardware (e.g., AMD Zen 4/5 AVX-512, Apple M1/M2/M3/M4, AWS Graviton3/4, NVIDIA Ada/Hopper/Blackwell):
1. Run `python3 scripts/tune_hardware_profile.py --auto-detect --output profiles/<arch>_<vendor>_<chip>.json` on your device.
2. Verify that `python3 scripts/tune_hardware_profile.py --verify-profiles profiles` and `./.lake/build/bin/lean-native-core pr-verify --disallow-spec-changes` pass.
3. Open a Pull Request touching only `profiles/<arch>_<vendor>_<chip>.json`. Because `LeanNative/Spec.lean` and `tests/test_runner.lean` remain untouched, **Law 5 (`pr-verify --disallow-spec-changes`)** automatically certifies that your PR preserves 100% of formal specifications.
