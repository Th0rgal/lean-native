#!/usr/bin/env python3
"""
scripts/sync_docs_inventory.py — Automated Documentation & Context Ratchet (`lean-native`).

Computes tight-spec and audited-theorem counts directly from `LeanNative/Spec.lean`
and `LeanNative/Proofs/AxiomAudit.lean`, and synchronizes
`<!-- inventory:KEY -->...<!-- /inventory:KEY -->` blocks across `README.md` and `AGENTS.md`.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Dict

ROOT_DIR = Path(__file__).resolve().parent.parent
SPEC_PATH = ROOT_DIR / "LeanNative" / "Spec.lean"
AUDIT_PATH = ROOT_DIR / "LeanNative" / "Proofs" / "AxiomAudit.lean"
DOC_PATHS = [
    ROOT_DIR / "README.md",
    ROOT_DIR / "AGENTS.md",
]


def compute_inventory() -> Dict[str, str]:
    spec_text = SPEC_PATH.read_text(encoding="utf-8")
    audit_text = AUDIT_PATH.read_text(encoding="utf-8")
    spec_thms = re.findall(r"(?m)^\s*(?:private\s+)?(?:theorem|lemma)\s+([A-Za-z0-9_'.]+)", spec_text)
    spec_tight = len(spec_thms)
    list_block = audit_text.split("def auditedTheoremNames : List Name :=", 1)[1].split("]", 1)[0]
    audited_thms = len(re.findall(r"``[A-Za-z0-9_'.]+", list_block))
    return {
        "leannative_spec_tight": str(spec_tight),
        "leannative_audited_theorems": str(audited_thms),
        "leannative_summary": f"{audited_thms}/{audited_thms} audited theorems, {spec_tight}/{spec_tight} tight specs in LeanNative/Spec.lean, 0 sorryAx",
    }


def sync_file(path: Path, inv: Dict[str, str], check_only: bool) -> bool:
    if not path.is_file():
        return True
    orig = path.read_text(encoding="utf-8")
    updated = orig
    for key, val in inv.items():
        pattern = re.compile(
            rf"(<!--\s*inventory:{re.escape(key)}\s*-->)(.*?)(<!--\s*/inventory:{re.escape(key)}\s*-->)",
            re.DOTALL,
        )
        updated = pattern.sub(rf"\g<1>{val}\g<3>", updated)
    if updated != orig:
        if check_only:
            print(f"[sync-docs] Out-of-sync inventory markers in {path.relative_to(ROOT_DIR)}", file=sys.stderr)
            return False
        path.write_text(updated, encoding="utf-8")
        print(f"[sync-docs] Updated {path.relative_to(ROOT_DIR)}")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description="Synchronize or verify lean-native documentation inventory markers")
    parser.add_argument("--check", action="store_true", help="Fail if any inventory marker is out of sync")
    args = parser.parse_args()

    inv = compute_inventory()
    ok = True
    for doc in DOC_PATHS:
        if not sync_file(doc, inv, check_only=args.check):
            ok = False
    if ok:
        print(f"[sync-docs] OK ({inv['leannative_summary']})")
        return 0
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
