#!/usr/bin/env python3
"""Check that every \\lean{file}{decl} reference in paper/*.tex resolves.

A reference resolves when the file exists in the repo and the declaration
name appears in it as a top-level declaration. Exits nonzero on any broken
reference. Run from the repo root: python3 tools/check_lean_refs.py
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}\{([^}]*)\}")
DECL_KW = r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)"


def decl_in_file(text: str, name: str) -> bool:
    pat = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
        + DECL_KW + r"\s+" + re.escape(name) + r"(?![A-Za-z0-9_'!?])",
        re.MULTILINE,
    )
    return bool(pat.search(text))


CODE_PATH_RE = re.compile(r"\\code\{([^}]*\.lean)\}")

# `\code{...}` mentions that legitimately point at Mathlib rather than at this repo.
MATHLIB_CODE_PATHS = {
    "AbelSummation.lean",
    "PrimesInAP.lean",
    "Mathlib/NumberTheory/LSeries/PrimesInAP.lean",
}


def check_code_paths() -> list:
    """`\\code{...lean}` mentions are prose, not links, so nothing else validates them.

    They rotted silently through the 2026-08 layout reorg; this catches that."""
    bad = []
    for tex in sorted(list((ROOT / "paper").glob("*.tex")) + list((ROOT / "paper" / "short").glob("*.tex"))):
        for m in CODE_PATH_RE.finditer(tex.read_text()):
            raw = m.group(1)
            path = raw.replace(r"\_", "_").replace(r"\-", "")
            if path in MATHLIB_CODE_PATHS:
                continue
            if not ((ROOT / path).is_file() or (ROOT / "EM" / path).is_file()):
                bad.append((tex.name, raw))
    return bad


def main() -> int:
    broken = []
    total = 0
    file_cache = {}
    for tex in sorted(list((ROOT / "paper").glob("*.tex")) + list((ROOT / "paper" / "short").glob("*.tex"))):
        for m in LEAN_RE.finditer(tex.read_text()):
            total += 1
            raw_path, raw_decl = m.group(1), m.group(2)
            path = re.sub(r"\\?#.*$", "", raw_path).replace(r"\_", "_")
            decl = raw_decl.replace(r"\_", "_").replace("\\", "")
            target = ROOT / path
            if not target.is_file():
                broken.append((tex.name, raw_path, decl, "file missing"))
                continue
            if path not in file_cache:
                file_cache[path] = target.read_text()
            candidates = {decl, decl.split(".")[-1]}
            if not any(decl_in_file(file_cache[path], c) for c in candidates):
                broken.append((tex.name, raw_path, decl, "decl not found"))
    for tex, path, decl, why in broken:
        print(f"{tex}: \\lean{{{path}}}{{{decl}}} — {why}")
    print(f"\n{total} references checked, {len(broken)} broken")

    stale = check_code_paths()
    for tex, path in stale:
        print(f"{tex}: \\code{{{path}}} — file missing")
    print(f"{len(stale)} stale \\code{{}} path mentions")
    return 1 if (broken or stale) else 0


if __name__ == "__main__":
    sys.exit(main())
