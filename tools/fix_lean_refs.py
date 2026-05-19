#!/usr/bin/env python3
"""One-shot repair of \\lean{file}{decl} references in paper/*.tex.

- Strips all #L line anchors (they have long drifted).
- For every reference whose (file, decl) pair does not resolve, greps the
  live EM/ tree (Archive excluded) for the declaration's current home and
  rewrites the path when the home is unique.
- Prints a report: rewritten / ambiguous (untouched) / unresolved (untouched).
"""
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}\{([^}]*)\}")
DECL_KW = r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)"


def decl_pattern(name: str) -> re.Pattern:
    return re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
        + DECL_KW + r"\s+" + re.escape(name) + r"(?![A-Za-z0-9_'!?])",
        re.MULTILINE,
    )


def main() -> int:
    live = {}
    for p in sorted((ROOT / "EM").rglob("*.lean")):
        rel = p.relative_to(ROOT)
        if rel.parts[1] == "Archive":
            continue
        live[str(rel)] = p.read_text()

    def homes(decl: str) -> list:
        cands = {decl, decl.split(".")[-1]}
        pats = [decl_pattern(c) for c in cands]
        return [f for f, text in live.items() if any(p.search(text) for p in pats)]

    rewritten, ambiguous, unresolved = [], defaultdict(list), []
    for tex in sorted((ROOT / "paper").glob("*.tex")):
        src = tex.read_text()

        def repl(m):
            raw_path, raw_decl = m.group(1), m.group(2)
            path = re.sub(r"\\?#.*$", "", raw_path).replace(r"\_", "_")
            decl = raw_decl.replace(r"\_", "_").replace("\\", "")
            target = ROOT / path
            ok = target.is_file() and str(Path(path)) in live and \
                any(decl_pattern(c).search(live[str(Path(path))])
                    for c in {decl, decl.split(".")[-1]})
            if ok:
                new_path = path.replace("_", r"\_")
                return r"\lean{%s}{%s}" % (new_path, raw_decl)
            hs = homes(decl)
            if len(hs) == 1:
                rewritten.append((tex.name, path, hs[0], decl))
                return r"\lean{%s}{%s}" % (hs[0].replace("_", r"\_"), raw_decl)
            if len(hs) > 1:
                ambiguous[(path, decl)].append((tex.name, hs))
                return m.group(0)
            unresolved.append((tex.name, path, decl))
            return m.group(0)

        out = LEAN_RE.sub(repl, src)
        if out != src:
            tex.write_text(out)

    print(f"rewritten: {len(rewritten)}")
    for t, old, new, d in rewritten:
        print(f"  {t}: {d}: {old} -> {new}")
    print(f"\nambiguous (untouched): {len(ambiguous)}")
    for (path, decl), sites in ambiguous.items():
        print(f"  {decl} (was {path}): candidates {sites[0][1]} in {[s[0] for s in sites]}")
    print(f"\nunresolved (untouched): {len(unresolved)}")
    for t, path, d in unresolved:
        print(f"  {t}: \\lean{{{path}}}{{{d}}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
