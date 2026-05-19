"""Custom MCP server exposing Lean-specific tools to agents."""

import asyncio
import re
from pathlib import Path

from claude_agent_sdk import create_sdk_mcp_server, tool

ROOT = Path(__file__).resolve().parent.parent.parent  # project root


@tool(
    "lean_build",
    "Run `lake build` in the project root. Returns compiler output (errors/warnings).",
    {"timeout_seconds": int},
)
async def lean_build(args: dict) -> dict:
    timeout = args.get("timeout_seconds", 300)
    proc = await asyncio.create_subprocess_exec(
        "lake", "build",
        cwd=str(ROOT),
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
    )
    try:
        stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout)
    except asyncio.TimeoutError:
        proc.kill()
        return {
            "content": [{"type": "text", "text": f"lake build timed out after {timeout}s"}],
            "is_error": True,
        }

    output = stdout.decode(errors="replace").strip()
    if proc.returncode == 0:
        summary = "Build succeeded (zero errors)."
        if output:
            summary += f"\n\nOutput:\n{output}"
    else:
        summary = f"Build FAILED (exit code {proc.returncode}).\n\n{output}"

    return {"content": [{"type": "text", "text": summary}]}


@tool(
    "lean_check_sorry",
    "Grep all .lean files for `sorry`. Returns file:line locations.",
    {},
)
async def lean_check_sorry(args: dict) -> dict:
    em_dir = ROOT / "EM"
    hits: list[str] = []
    for p in sorted(em_dir.rglob("*.lean")):
        for i, line in enumerate(p.read_text().splitlines(), 1):
            if re.search(r"\bsorry\b", line):
                rel = p.relative_to(ROOT)
                hits.append(f"{rel}:{i}: {line.strip()}")

    if not hits:
        return {"content": [{"type": "text", "text": "No `sorry` found. All proofs complete."}]}
    return {"content": [{"type": "text", "text": f"Found {len(hits)} sorry:\n" + "\n".join(hits)}]}


@tool(
    "lean_list_open_hypotheses",
    "Find open hypotheses (declared as `def ... : Prop` without proof).",
    {},
)
async def lean_list_open_hypotheses(args: dict) -> dict:
    em_dir = ROOT / "EM"
    pattern = re.compile(r"^def\s+(\w+).*:\s*Prop\s*:=")
    hits: list[str] = []
    for p in sorted(em_dir.rglob("*.lean")):
        for i, line in enumerate(p.read_text().splitlines(), 1):
            m = pattern.match(line.strip())
            if m:
                rel = p.relative_to(ROOT)
                hits.append(f"{rel}:{i}: {m.group(1)} — {line.strip()}")

    if not hits:
        return {"content": [{"type": "text", "text": "No open hypotheses found."}]}
    return {"content": [{"type": "text", "text": f"Open hypotheses ({len(hits)}):\n" + "\n".join(hits)}]}


@tool(
    "lean_file_info",
    "Get line count, imports, and namespace for a Lean file.",
    {"file": str},
)
async def lean_file_info(args: dict) -> dict:
    filepath = args.get("file", "")
    # Resolve relative to ROOT
    p = ROOT / filepath
    if not p.exists():
        # Try under EM/
        p = ROOT / "EM" / filepath
    if not p.exists():
        return {
            "content": [{"type": "text", "text": f"File not found: {filepath}"}],
            "is_error": True,
        }

    text = p.read_text()
    lines = text.splitlines()
    line_count = len(lines)

    imports = [l.strip() for l in lines if l.strip().startswith("import ")]
    namespaces = [l.strip() for l in lines if l.strip().startswith("namespace ")]
    opens = [l.strip() for l in lines if l.strip().startswith("open ")]

    info_parts = [
        f"File: {p.relative_to(ROOT)}",
        f"Lines: {line_count}",
    ]
    if imports:
        info_parts.append(f"Imports:\n  " + "\n  ".join(imports))
    if namespaces:
        info_parts.append(f"Namespaces: {', '.join(namespaces)}")
    if opens:
        info_parts.append(f"Opens: {', '.join(opens)}")

    return {"content": [{"type": "text", "text": "\n".join(info_parts)}]}


lean_mcp_server = create_sdk_mcp_server(
    name="lean",
    version="1.0.0",
    tools=[lean_build, lean_check_sorry, lean_list_open_hypotheses, lean_file_info],
)
