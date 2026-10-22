#!/usr/bin/env python3
"""
scripts/accelerator_worker.py — Canonical Hardware-Agnostic Stage-1 Accelerator Worker
(`--target auto|cpu-simd|spark-cuda|tpu-v6e`) for `lean-native` and `turbo-lean`.

Delegates to the unified multi-target RPN/SIMD/CUDA/XLA engine while preserving
100% compatibility with `scripts/colab_gpu_worker.py`.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from colab_gpu_worker import *  # noqa: F401,F403
from colab_gpu_worker import main

if __name__ == "__main__":
    raise SystemExit(main())
