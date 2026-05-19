#!/usr/bin/env python3
"""Axiom gate: every registry-published declaration must depend only on the three standard
axioms (propext, Classical.choice, Quot.sound).  Fails (exit 1) on native_decide / sorryAx /
any user axiom.  Run from the repo root after `lake build`:  python3 tools/check_axioms.py
"""
import json, subprocess, sys, tempfile, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def main() -> int:
    decls = json.load(open(ROOT / "registry" / "declarations.json"))
    names = sorted({d["name"] for d in decls if "name" in d})
    src = "import EM\n" + "".join(f"#print axioms {n}\n" for n in names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=ROOT, delete=False) as f:
        f.write(src); path = f.name
    try:
        out = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True).stdout
    finally:
        Path(path).unlink(missing_ok=True)
    bad = []
    # messages look like: "'name' depends on axioms: [propext, Classical.choice, Quot.sound]"
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        axs = {a.strip() for a in m.group(2).split(",") if a.strip()}
        extra = axs - ALLOWED
        if extra:
            bad.append((m.group(1), sorted(extra)))
    n_checked = len(re.findall(r"depends on axioms|does not depend on any axioms", out))
    print(f"checked {n_checked} declarations; {len(bad)} with non-standard axioms")
    for n, extra in bad:
        print(f"  {n}: {extra}")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
