#!/usr/bin/env python3
"""Refresh the 8-hex L1 (CA type-hash prefix) column of paper/the_Lean_formalization.tex
from registry/declarations.json.  Rows whose declaration is not in the registry are left
untouched and reported.  Run after `lake build EMRegistry` whenever the registry changes."""
import json, re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
REG = ROOT / "registry" / "declarations.json"
TEX = ROOT / "paper" / "the_Lean_formalization.tex"
reg = {d["name"]: d["type_hash"] for d in json.loads(REG.read_text())}
tex = TEX.read_text()
pat = re.compile(r'(\\code\{([^}]*)\}\s*&\s*)([0-9a-f]{8})(\s*\\\\)')
updated = unchanged = missing = 0
missing_names = []
def sub(m):
    global updated, unchanged, missing
    name = m.group(2).replace("\\_", "_")
    cands = [k for k in reg if k == name or k.endswith("." + name)]
    if not cands:
        missing += 1; missing_names.append(name); return m.group(0)
    h = reg[cands[0]][:8]
    if h == m.group(3):
        unchanged += 1; return m.group(0)
    updated += 1
    return f"{m.group(1)}{h}{m.group(4)}"
new = pat.sub(sub, tex)
TEX.write_text(new)
print(f"L1 hashes: {updated} updated, {unchanged} unchanged, {missing} not in registry")
for n in missing_names: print("  not in registry:", n, file=sys.stderr)
