"""Tool dispatch for the QwenBackend.

Mirrors the operations `tools.openai_tools` exposes to the
openai-agents SDK, but as plain async functions callable directly
(without the @function_tool decorator). The QwenBackend's manual
agent loop dispatches against `HANDLERS` and presents `SCHEMAS`
to the model.

Kept separate from `openai_tools.py` to avoid pulling in the
openai-agents SDK's import machinery when we're not using it.
"""

from __future__ import annotations

import asyncio
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any, Awaitable, Callable

from ..config import ROOT


# ---------------------------------------------------------------------------
# Tool schemas (OpenAI `tools` array format)
# ---------------------------------------------------------------------------
#
# Each entry describes what the model may call. The names here match
# what `HANDLERS` below knows how to dispatch. They're the same names
# `tools.openai_tools` uses, so a prompt that worked there works here.

SCHEMAS: dict[str, dict[str, Any]] = {
    "Read": {
        "type": "function",
        "function": {
            "name": "Read",
            "description": "Read a file's contents (line-numbered).",
            "parameters": {
                "type": "object",
                "properties": {
                    "path":   {"type": "string", "description": "File path (project-relative or absolute)."},
                    "offset": {"type": "integer", "default": 0, "description": "Line number to start at (0-based)."},
                    "limit":  {"type": "integer", "default": 2000, "description": "Max number of lines to read."},
                },
                "required": ["path"],
            },
        },
    },
    "Write": {
        "type": "function",
        "function": {
            "name": "Write",
            "description": "Create a NEW file. Refuses to overwrite — use Edit for existing files.",
            "parameters": {
                "type": "object",
                "properties": {
                    "path":    {"type": "string"},
                    "content": {"type": "string"},
                },
                "required": ["path", "content"],
            },
        },
    },
    "Edit": {
        "type": "function",
        "function": {
            "name": "Edit",
            "description": "Replace an exact string in an existing file. old_string must appear EXACTLY once.",
            "parameters": {
                "type": "object",
                "properties": {
                    "path":       {"type": "string"},
                    "old_string": {"type": "string"},
                    "new_string": {"type": "string"},
                },
                "required": ["path", "old_string", "new_string"],
            },
        },
    },
    "Bash": {
        "type": "function",
        "function": {
            "name": "Bash",
            "description": "Execute a shell command and return stdout+stderr.",
            "parameters": {
                "type": "object",
                "properties": {
                    "command":         {"type": "string"},
                    "timeout_seconds": {"type": "integer", "default": 120},
                },
                "required": ["command"],
            },
        },
    },
    "Glob": {
        "type": "function",
        "function": {
            "name": "Glob",
            "description": "List files matching a glob pattern under a base path.",
            "parameters": {
                "type": "object",
                "properties": {
                    "pattern": {"type": "string", "default": "**/*"},
                    "path":    {"type": "string", "default": "."},
                },
            },
        },
    },
    "Grep": {
        "type": "function",
        "function": {
            "name": "Grep",
            "description": "Search file contents with ripgrep.",
            "parameters": {
                "type": "object",
                "properties": {
                    "pattern":          {"type": "string"},
                    "path":             {"type": "string", "default": "."},
                    "glob":             {"type": "string", "default": ""},
                    "case_insensitive": {"type": "boolean", "default": False},
                    "context_lines":    {"type": "integer", "default": 0},
                },
                "required": ["pattern"],
            },
        },
    },
    "Task": {
        "type": "function",
        "function": {
            "name": "Task",
            "description": (
                "Dispatch a specialist sub-agent on the Qwen backend. "
                "The sub-agent runs autonomously with its own tool set, "
                "then returns its final transcript as a string. Use this "
                "to delegate work to formalizer, scout, attack-*, "
                "code-stylist, paper-writer, etc. Blocks until the "
                "sub-agent finishes."
            ),
            "parameters": {
                "type": "object",
                "properties": {
                    "subagent_type": {
                        "type": "string",
                        "description": (
                            "Agent name: lean-formalizer, literature-scout, "
                            "attack-analytic, attack-algebraic, "
                            "attack-combinatorial, attack-dynamicalsystem, "
                            "paper-writer, code-stylist."
                        ),
                    },
                    "description": {
                        "type": "string",
                        "description": "Short task title (1 line).",
                    },
                    "prompt": {
                        "type": "string",
                        "description": "Full task prompt for the sub-agent.",
                    },
                },
                "required": ["subagent_type", "prompt"],
            },
        },
    },
}


# ---------------------------------------------------------------------------
# Handlers — bare async functions
# ---------------------------------------------------------------------------

def _abs_path(p: str) -> Path:
    pp = Path(p)
    return pp if pp.is_absolute() else (ROOT / pp)


# Cap on any single tool result. The DGX model's context is 64k tokens
# and the agent loop's history is never compacted, so one unbounded
# `lake build` error dump would blow the window and 400 the session.
# Keep head + tail: build errors put the useful part at both ends.
_MAX_TOOL_RESULT_CHARS = 30_000


def _truncate_result(text: str) -> str:
    if len(text) <= _MAX_TOOL_RESULT_CHARS:
        return text
    half = _MAX_TOOL_RESULT_CHARS // 2
    omitted = len(text) - 2 * half
    return (
        text[:half]
        + f"\n... [tool output truncated: {omitted} chars omitted] ...\n"
        + text[-half:]
    )


async def _h_read(args: dict[str, Any]) -> str:
    path = str(args.get("path", ""))
    offset = int(args.get("offset", 0))
    limit = int(args.get("limit", 2000))
    if not path:
        return "ERROR: missing required parameter 'path'."
    p = _abs_path(path)
    if not p.exists():
        return f"File not found: {path}"
    if not p.is_file():
        return f"Not a file: {path}"
    text = p.read_text(errors="replace")
    lines = text.splitlines()
    selected = lines[offset:offset + limit]
    out = [f"{i:>6}\t{line}" for i, line in enumerate(selected, start=offset + 1)]
    return "\n".join(out) or "(empty file)"


async def _h_write(args: dict[str, Any]) -> str:
    path = str(args.get("path", ""))
    content = args.get("content")
    if not path or content is None:
        return "ERROR: Write requires 'path' and 'content'."
    if not isinstance(content, str):
        content = str(content)
    p = _abs_path(path)
    if p.exists():
        return f"ERROR: {path} already exists. Use Edit to modify existing files."
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content)
    rel = p.relative_to(ROOT) if str(p).startswith(str(ROOT)) else p
    return f"Created {rel} ({len(content)} bytes)"


async def _h_edit(args: dict[str, Any]) -> str:
    path = str(args.get("path", ""))
    old = args.get("old_string")
    new = args.get("new_string")
    if not path or old is None or new is None:
        return "ERROR: Edit requires 'path', 'old_string', 'new_string'."
    if not isinstance(old, str): old = str(old)
    if not isinstance(new, str): new = str(new)
    p = _abs_path(path)
    if not p.exists():
        return f"ERROR: File not found: {path}"
    if not p.is_file():
        return f"ERROR: Not a file: {path}"
    text = p.read_text(errors="replace")
    count = text.count(old)
    if count == 0:
        preview = text[:500] + ("..." if len(text) > 500 else "")
        return (
            f"ERROR: old_string not found in {path}. Read the file first. "
            f"File starts with:\n{preview}"
        )
    if count > 1:
        return (
            f"ERROR: old_string appears {count} times in {path}. "
            f"Provide more context so it matches exactly once."
        )
    p.write_text(text.replace(old, new, 1))
    return f"Edited {path}"


async def _h_bash(args: dict[str, Any]) -> str:
    cmd = str(args.get("command", ""))
    if not cmd:
        return "ERROR: Bash requires 'command'."
    timeout = int(args.get("timeout_seconds", 120))
    proc = await asyncio.create_subprocess_shell(
        cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        cwd=str(ROOT),
        env={**os.environ, "TERM": "dumb"},
    )
    try:
        stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout)
    except asyncio.TimeoutError:
        proc.kill()
        return f"[TIMEOUT] Command killed after {timeout}s: {cmd}"
    output = stdout.decode(errors="replace").strip()
    if proc.returncode != 0:
        return f"[EXIT {proc.returncode}]\n{output}"
    return output or "(no output)"


# Directories that must never be traversed by Glob: .lake alone holds
# hundreds of thousands of build artifacts and would hang the walk.
# Pruned during the walk (not post-filtered) so we never descend into them.
_GLOB_PRUNE = {".lake", ".git", "__pycache__", "node_modules", ".venv"}


async def _h_glob(args: dict[str, Any]) -> str:
    import fnmatch
    pattern = str(args.get("pattern", "**/*"))
    base = str(args.get("path", "."))
    bp = _abs_path(base)
    if not bp.exists() or not bp.is_dir():
        return f"Not a directory: {base}"
    # `**/` in pathlib-style globs means "any directory depth, including
    # none"; fnmatch has no `**`, so normalize to a plain wildcard match
    # against the relative posix path.
    fn_pattern = pattern.replace("**/", "*")
    matches = []
    for dirpath, dirnames, filenames in os.walk(bp):
        dirnames[:] = [d for d in dirnames if d not in _GLOB_PRUNE]
        for fname in filenames:
            rel = str((Path(dirpath) / fname).relative_to(bp))
            if fnmatch.fnmatch(rel, fn_pattern) or fnmatch.fnmatch(fname, fn_pattern):
                matches.append(rel)
    matches.sort()
    if not matches:
        return "(no matches)"
    if len(matches) > 200:
        return "\n".join(matches[:200]) + f"\n... ({len(matches) - 200} more)"
    return "\n".join(matches)


async def _h_grep(args: dict[str, Any]) -> str:
    import shutil
    pattern = str(args.get("pattern", ""))
    if not pattern:
        return "ERROR: Grep requires 'pattern'."
    path = str(args.get("path", "."))
    glob = str(args.get("glob", ""))
    case_i = bool(args.get("case_insensitive", False))
    ctx = int(args.get("context_lines", 0))
    if shutil.which("rg"):
        # --no-ignore: the project .gitignore excludes docs/ and tmp/
        # entirely, which would make the swarm's own analyses and working
        # notes unsearchable. Re-exclude the genuinely huge dirs explicitly.
        cmd = ["rg", "--no-heading", "--line-number", "--no-ignore"]
        for excl in _GLOB_PRUNE:
            cmd.extend(["--glob", f"!{excl}/**"])
        if case_i:
            cmd.append("-i")
        if ctx > 0:
            cmd.extend(["-C", str(ctx)])
        if glob:
            cmd.extend(["--glob", glob])
        cmd.append(pattern)
        cmd.append(path)
    else:
        # GNU grep fallback (rg not installed on this machine).
        cmd = ["grep", "-rn", "-E"]
        for excl in _GLOB_PRUNE:
            cmd.append(f"--exclude-dir={excl}")
        if case_i:
            cmd.append("-i")
        if ctx > 0:
            cmd.extend(["-C", str(ctx)])
        if glob:
            cmd.append(f"--include={glob}")
        cmd.append(pattern)
        cmd.append(path)
    proc = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        cwd=str(ROOT),
    )
    stdout, _ = await proc.communicate()
    output = stdout.decode(errors="replace").strip()
    if proc.returncode == 1:
        return "(no matches)"
    if proc.returncode not in (0, 1):
        return f"[rg error, exit {proc.returncode}]\n{output}"
    lines = output.splitlines()
    if len(lines) > 200:
        return "\n".join(lines[:200]) + f"\n... ({len(lines) - 200} more lines)"
    return output or "(no matches)"


def _task_model_for(name: str) -> str:
    """Pick the DGX model for a Task sub-agent dispatch.

    Resolution order:
      1. `DGX_AGENT_MODELS` env (JSON dict subagent_type -> model string),
         set by the coordinator from its --dgx-agents mapping.
      2. `DGX_TASK_DEFAULT_MODEL` env (fallback for unlisted agents).
      3. `dgx:qwen`.
    This lets a DGX-hosted coordinator fan sub-agents across BOTH DGX
    models (e.g. lean-formalizer -> dgx:ornith, attack-* -> dgx:qwen)."""
    raw = os.environ.get("DGX_AGENT_MODELS", "")
    if raw:
        try:
            mapping = json.loads(raw)
            if isinstance(mapping, dict) and name in mapping:
                return str(mapping[name])
        except (ValueError, TypeError):
            pass
    return os.environ.get("DGX_TASK_DEFAULT_MODEL", "dgx:qwen")


async def _h_task(args: dict[str, Any]) -> str:
    name = str(args.get("subagent_type", "")).strip()
    prompt = str(args.get("prompt", ""))
    if not name or not prompt:
        return "ERROR: Task requires 'subagent_type' and 'prompt'."
    sub_model = _task_model_for(name)
    # Write the prompt to a tempfile to avoid argv-length / quoting issues.
    fd, prompt_file = tempfile.mkstemp(suffix=".txt", prefix=f"qwen-task-{name}-")
    try:
        os.write(fd, prompt.encode())
        os.close(fd)
        proc = await asyncio.create_subprocess_exec(
            sys.executable, "-m", "agents", "run-openai",
            "--agent", name,
            "--prompt", "(see --prompt-file)",
            "--prompt-file", prompt_file,
            "--model", sub_model,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            cwd=str(ROOT),
            env={**os.environ, "TERM": "dumb"},
        )
        # No artificial timeout — sub-agents can run for many minutes.
        stdout, _ = await proc.communicate()
        output = stdout.decode(errors="replace").strip()
        if proc.returncode != 0:
            return f"[sub-agent {name} exit {proc.returncode}]\n{output}"
        return output or f"(sub-agent {name} returned no output)"
    finally:
        try:
            os.unlink(prompt_file)
        except OSError:
            pass


HANDLERS: dict[str, Callable[[dict[str, Any]], Awaitable[str]]] = {
    "Read": _h_read,
    "Write": _h_write,
    "Edit": _h_edit,
    "Bash": _h_bash,
    "Glob": _h_glob,
    "Grep": _h_grep,
    "Task": _h_task,
}
