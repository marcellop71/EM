#!/usr/bin/env python3
"""Source-level lint for the live Lean tree (everything under EM/ except EM/Archive/):
after stripping `--` line comments and (nested) `/- … -/` block comments, fail on
  sorry, native_decide, axiom, unsafe, implemented_by, extern, admit, set_option autoImplicit true.
The kernel-level guarantee is tools/check_axioms.py; this catches the same things without a
build and also the non-axiom escape hatches (unsafe/implemented_by/extern).
Run from the repo root:  python3 tools/check_forbidden.py
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAT = re.compile(r"\b(sorry|native_decide|admit|unsafe|implemented_by|extern)\b|^\s*axiom\s|autoImplicit\s+true", re.M)

def strip_comments(src: str) -> str:
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j
        elif src.startswith("/-", i):
            depth += 1; i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1; i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)

def main() -> int:
    bad = []
    for f in sorted((ROOT / "EM").rglob("*.lean")):
        if "Archive" in f.relative_to(ROOT).parts:
            continue
        code = strip_comments(f.read_text())
        for m in PAT.finditer(code):
            line = code.count("\n", 0, m.start()) + 1
            bad.append(f"{f.relative_to(ROOT)}:{line}: {m.group(0).strip()}")
    for b in bad:
        print(b)
    print(f"check_forbidden: {len(bad)} hit(s)")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
