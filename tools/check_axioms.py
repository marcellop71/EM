#!/usr/bin/env python3
"""Axiom gate.  Run from the repo root after `lake build`:  python3 tools/check_axioms.py

Two passes, both must succeed (exit 0):
  1. Whole library: `lake env lean tools/lean/AxiomGate.lean` walks every declaration defined in
     `EM` / `EM.*` (the full `lean_lib EM` import closure, ~5.4k declarations) and fails on any
     that depends on an axiom other than propext / Classical.choice / Quot.sound
     (covers sorryAx, native_decide's Lean.ofReduceBool, and user axioms).
  2. Registry: `#print axioms` for every registry-published declaration
     (registry/declarations.json), so the published set is checked by name even if a name
     moves out of the EM namespace.
"""
import json, subprocess, sys, tempfile, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def whole_library() -> int:
    r = subprocess.run(["lake", "env", "lean", "tools/lean/AxiomGate.lean"], cwd=ROOT,
                       capture_output=True, text=True)
    sys.stdout.write(r.stdout)
    if r.returncode != 0:
        sys.stderr.write(r.stderr)
        print("whole-library gate FAILED")
    return r.returncode

def registry() -> int:
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
    print(f"registry: checked {n_checked}/{len(names)} declarations; {len(bad)} with non-standard axioms")
    for n, extra in bad:
        print(f"  {n}: {extra}")
    if n_checked != len(names):
        print("registry: some declarations produced no #print axioms output (unknown name?)")
        return 1
    return 1 if bad else 0

def main() -> int:
    return 1 if (whole_library() or registry()) else 0

if __name__ == "__main__":
    sys.exit(main())
