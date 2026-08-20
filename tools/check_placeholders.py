#!/usr/bin/env python3
"""Placeholder gate for the live Lean tree (EM/ minus EM/Archive/).
A *placeholder* is a `def`/`abbrev` of type `Prop` whose body (comments stripped) is
literally `True`, or a binder stub ending in `→ True` / `∧ True` / `∀ …, True`.
Every such def must carry the literal token PLACEHOLDER, either in its docstring or in
a comment within the 3 lines above the `def`, so nobody mistakes it for a hypothesis.
Run from the repo root:  python3 tools/check_placeholders.py
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?(?:private\s+)?(?:def|abbrev)\s+([\w.']+)", re.M)
TRUE_BODY = re.compile(r"(?:^|:=|→|∧|,)\s*True\s*$")

def strip_comments(src: str) -> str:   # same as tools/check_forbidden.py
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

def placeholders(code: str):
    """Yield (line, name) for every Prop-valued def whose body is a `True` stub."""
    for m in HEAD.finditer(code):
        end = code.find("\n\n", m.end()); end = len(code) if end < 0 else end
        decl = code[m.start():end]
        if ":=" not in decl or not re.search(r":\s*Prop\s*:=", decl):
            continue
        body = decl.split(":=", 1)[1].strip()
        if TRUE_BODY.search(body) and "\n\n" not in body:
            yield code.count("\n", 0, m.start()) + 1, m.group(1)

def main() -> int:
    marked, bad = 0, []
    for f in sorted((ROOT / "EM").rglob("*.lean")):
        if "Archive" in f.relative_to(ROOT).parts:
            continue
        raw = f.read_text().split("\n")
        for line, name in placeholders(strip_comments(f.read_text())):
            k = line - 2                         # walk back over blank/attribute lines, then the docstring
            while k >= 0 and (not raw[k].strip() or raw[k].lstrip().startswith("@[")):
                k -= 1
            if k >= 0 and raw[k].rstrip().endswith("-/"):
                while k >= 0 and "/--" not in raw[k]:
                    k -= 1
            ctx = "\n".join(raw[max(0, min(k, line - 4)):line])   # docstring + 3 lines above the def
            if "PLACEHOLDER" in ctx:
                marked += 1
            else:
                bad.append(f"{f.relative_to(ROOT)}:{line}: {name}")
    for b in bad:
        print(b)
    print(f"check_placeholders: {marked} marked placeholder def(s), {len(bad)} unmarked")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
