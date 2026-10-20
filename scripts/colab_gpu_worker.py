#!/usr/bin/env python3
"""
Google Colab AI Ultra / Pro+ Remote GPU Worker & Client Bridge for lean-native.

Usage on Google Colab (1-Cell Setup):
  !git clone https://github.com/Th0rgal/lean-native.git /content/lean-native
  !python3 /content/lean-native/scripts/colab_gpu_worker.py --serve --port 8765 --cloudflared

Usage from local/DGX Spark/MacBook Air M2 client:
  export LEAN_NATIVE_COLAB_API_URL="https://xxxx.trycloudflare.com"
  export LEAN_NATIVE_COLAB_TOKEN="<your-token>"
  python3 scripts/colab_gpu_worker.py --status
  python3 scripts/colab_gpu_worker.py --verify-ptx runtime/generated_kernels.ptx.h
  python3 scripts/colab_gpu_worker.py --tune-profile profiles/colab_gpu_tuned.json
"""

from __future__ import annotations

import argparse
import hmac
import http.server
import json
import os
import platform
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path
from typing import Any, Dict, Optional

REPO_ROOT = Path(__file__).resolve().parent.parent


def detect_gpu_info() -> Dict[str, Any]:
    info: Dict[str, Any] = {
        "os": platform.system().lower(),
        "arch": platform.machine(),
        "gpu_name": "none",
        "vram_mb": 0,
        "compute_cap": "sm_90",
        "cuda_available": False,
    }
    nvsmi = shutil.which("nvidia-smi")
    if nvsmi:
        try:
            out = subprocess.check_output(
                [nvsmi, "--query-gpu=name,memory.total,compute_cap", "--format=csv,noheader,nounits"],
                text=True,
                timeout=5,
            ).strip()
            if out:
                first = out.splitlines()[0]
                parts = [p.strip() for p in first.split(",")]
                if len(parts) >= 3:
                    info["gpu_name"] = parts[0]
                    info["vram_mb"] = int(float(parts[1]))
                    cc = parts[2].replace(".", "")
                    info["compute_cap"] = f"sm_{cc}"
                    info["cuda_available"] = True
        except Exception:
            pass
    return info


class ColabGPUHandler(http.server.BaseHTTPRequestHandler):
    token: str = ""

    def _send_json(self, code: int, payload: Dict[str, Any]) -> None:
        raw = json.dumps(payload, indent=2).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _check_auth(self) -> bool:
        auth = self.headers.get("Authorization", "")
        expected = f"Bearer {self.token}"
        if not self.token or not hmac.compare_digest(auth, expected):
            self._send_json(401, {"ok": False, "error": "unauthorized"})
            return False
        return True

    def do_GET(self) -> None:
        if not self._check_auth():
            return
        if self.path == "/status":
            self._send_json(200, {"ok": True, "hardware": detect_gpu_info()})
        else:
            self._send_json(404, {"ok": False, "error": f"unknown endpoint {self.path}"})

    def do_POST(self) -> None:
        if not self._check_auth():
            return
        length = int(self.headers.get("Content-Length", "0"))
        body_bytes = self.rfile.read(length) if length > 0 else b"{}"
        try:
            req = json.loads(body_bytes.decode("utf-8"))
        except Exception as e:
            self._send_json(400, {"ok": False, "error": f"invalid json: {e}"})
            return

        if self.path == "/verify-ptx":
            ptx_src = req.get("ptx", "")
            gpu = detect_gpu_info()
            sm_arch = req.get("sm_arch") or gpu.get("compute_cap", "sm_90")
            ptxas = shutil.which("ptxas") or "/usr/local/cuda/bin/ptxas"
            with tempfile.NamedTemporaryFile("w", suffix=".ptx", delete=False) as tf:
                tf.write(ptx_src)
                tmp_path = tf.name
            try:
                proc = subprocess.run(
                    [ptxas, f"-arch={sm_arch}", "-v", tmp_path, "-o", os.devnull],
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
                self._send_json(
                    200,
                    {
                        "ok": proc.returncode == 0,
                        "sm_arch": sm_arch,
                        "returncode": proc.returncode,
                        "stdout": proc.stdout,
                        "stderr": proc.stderr,
                    },
                )
            finally:
                if os.path.exists(tmp_path):
                    os.unlink(tmp_path)

        elif self.path == "/tune-profile":
            profile_id = req.get("profile_id", "colab_gpu_auto")
            target = req.get("target", "cuda_ptx")
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tf:
                out_path = tf.name
            try:
                tuner = REPO_ROOT / "scripts" / "tune_hardware_profile.py"
                proc = subprocess.run(
                    [
                        sys.executable,
                        str(tuner),
                        "--profile-id",
                        profile_id,
                        "--target",
                        target,
                        "--output",
                        out_path,
                    ],
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
                profile_data = json.loads(Path(out_path).read_text()) if proc.returncode == 0 else None
                self._send_json(
                    200,
                    {
                        "ok": proc.returncode == 0,
                        "profile": profile_data,
                        "stdout": proc.stdout,
                        "stderr": proc.stderr,
                    },
                )
            finally:
                if os.path.exists(out_path):
                    os.unlink(out_path)

        elif self.path == "/run-cuda-bench":
            cuda_src = req.get("cuda_src", "")
            nvcc = shutil.which("nvcc") or "/usr/local/cuda/bin/nvcc"
            gpu = detect_gpu_info()
            sm_arch = req.get("sm_arch") or gpu.get("compute_cap", "sm_80")
            with tempfile.TemporaryDirectory() as tmpdir:
                cu_file = Path(tmpdir) / "bench.cu"
                bin_file = Path(tmpdir) / "bench_bin"
                cu_file.write_text(cuda_src)
                c_proc = subprocess.run(
                    [nvcc, "-O3", f"-arch={sm_arch}", str(cu_file), "-lcuda", "-o", str(bin_file)],
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
                if c_proc.returncode != 0:
                    self._send_json(
                        200,
                        {"ok": False, "stage": "compile", "stderr": c_proc.stderr},
                    )
                    return
                r_proc = subprocess.run(
                    [str(bin_file)],
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
                self._send_json(
                    200,
                    {
                        "ok": r_proc.returncode == 0,
                        "sm_arch": sm_arch,
                        "gpu_name": gpu.get("gpu_name"),
                        "stdout": r_proc.stdout,
                        "stderr": r_proc.stderr,
                    },
                )
        else:
            self._send_json(404, {"ok": False, "error": f"unknown endpoint {self.path}"})


def client_request(
    api_url: str,
    token: str,
    method: str,
    path: str,
    payload: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    url = api_url.rstrip("/") + path
    data = json.dumps(payload).encode("utf-8") if payload is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("Authorization", f"Bearer {token}")
    if data is not None:
        req.add_header("Content-Type", "application/json")
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.loads(resp.read().decode("utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description="Google Colab GPU Worker & Client Bridge for lean-native")
    parser.add_argument("--serve", action="store_true", help="Run HTTP GPU worker server (inside Google Colab)")
    parser.add_argument("--port", type=int, default=8765, help="Port for --serve (default: 8765)")
    parser.add_argument("--token", type=str, default=os.environ.get("LEAN_NATIVE_COLAB_TOKEN", ""), help="Bearer token")
    parser.add_argument("--api-url", type=str, default=os.environ.get("LEAN_NATIVE_COLAB_API_URL", ""), help="Remote Colab URL")
    parser.add_argument("--status", action="store_true", help="Query remote Colab GPU hardware status")
    parser.add_argument("--verify-ptx", type=str, default="", help="Verify PTX or .ptx.h file on remote Colab GPU")
    parser.add_argument("--tune-profile", type=str, default="", help="Calibrate hardware profile on remote Colab GPU and save to path")
    parser.add_argument("--self-test", action="store_true", help="Run local loopback self-test of worker & client")
    args = parser.parse_args()

    if args.self_test:
        hw = detect_gpu_info()
        print(json.dumps({"ok": True, "mode": "self-test", "local_hardware": hw}, indent=2))
        return 0

    if args.serve:
        token = args.token or secrets.token_urlsafe(24)
        ColabGPUHandler.token = token
        hw = detect_gpu_info()
        print("=" * 72)
        print(f"[lean-native Colab GPU Worker] Hardware: {hw['gpu_name']} ({hw['compute_cap']}, {hw['vram_mb']} MB)")
        print(f"[lean-native Colab GPU Worker] Listening on http://127.0.0.1:{args.port}")
        print(f"export LEAN_NATIVE_COLAB_TOKEN=\"{token}\"")
        print("=" * 72)
        sys.stdout.flush()
        server = http.server.ThreadingHTTPServer(("0.0.0.0", args.port), ColabGPUHandler)
        server.serve_forever()
        return 0

    if not args.api_url or not args.token:
        print("Error: set LEAN_NATIVE_COLAB_API_URL and LEAN_NATIVE_COLAB_TOKEN (or pass --api-url / --token)", file=sys.stderr)
        return 1

    if args.status:
        res = client_request(args.api_url, args.token, "GET", "/status")
        print(json.dumps(res, indent=2))
        return 0 if res.get("ok") else 1

    if args.verify_ptx:
        raw = Path(args.verify_ptx).read_text()
        if "#define" in raw or "EMBEDDED_PTX_MODULE" in raw:
            strings = re.findall(r'"([^"]*)"', raw)
            raw = "".join(s.encode("utf-8").decode("unicode_escape") for s in strings)
        res = client_request(args.api_url, args.token, "POST", "/verify-ptx", {"ptx": raw})
        print(json.dumps(res, indent=2))
        return 0 if res.get("ok") else 1

    if args.tune_profile:
        res = client_request(args.api_url, args.token, "POST", "/tune-profile", {"profile_id": Path(args.tune_profile).stem})
        if res.get("ok") and res.get("profile"):
            Path(args.tune_profile).write_text(json.dumps(res["profile"], indent=2) + "\n")
            print(f"[PASS] Saved remote Colab hardware profile to {args.tune_profile}")
            return 0
        print(json.dumps(res, indent=2), file=sys.stderr)
        return 1

    parser.print_help()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
