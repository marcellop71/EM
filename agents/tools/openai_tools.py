"""Function tools for OpenAI Agents SDK.

These wrap subprocess calls (Bash, Grep) so OpenAI agents get similar
capabilities to Claude Code's built-in tools.

NOTE: The `openai-agents` pip package installs as `agents`, which collides
with this project's `agents/` package.  We use `_import_openai_agents()` to
resolve the correct module at runtime via importlib.
"""

from __future__ import annotations

import asyncio
import importlib
import importlib.util
import os
import sys
from pathlib import Path


_ROOT = Path(__file__).resolve().parent.parent.parent  # project root


_oai_sdk = None  # cached top-level openai-agents module


def _import_openai_agents(submodule: str | None = None):
    """Import the openai-agents SDK, bypassing our local ``agents`` package.

    The openai-agents pip package installs as ``agents`` in site-packages,
    colliding with our local ``agents/`` directory.  There are **no**
    submodule-level collisions (our files are agents.coordinator,
    agents.config, ... while the SDK's are agents.run, agents.agent, ...).

    Strategy:
    1. Temporarily remove our local ``agents`` top-level entry from
       ``sys.modules`` and strip the project root from ``sys.path``.
    2. Import the SDK — this populates ``sys.modules`` with
       ``agents``, ``agents.run``, ``agents.agent``, etc.
    3. Cache the SDK top-level module object.
    4. **Leave all SDK submodule entries in ``sys.modules``** so the
       SDK's internal lazy imports (``from .agent_tool_state import ...``)
       keep working at runtime.
    5. Restore only ``sys.modules["agents"]`` to our local package and
       restore ``sys.path``.

    Since there are no submodule collisions, both packages' submodules
    coexist happily under the ``agents.*`` namespace in ``sys.modules``.
    """
    global _oai_sdk

    # Fast path: already bootstrapped.
    if _oai_sdk is not None:
        if submodule:
            mod = sys.modules.get(f"agents.{submodule}")
            if mod is not None:
                return mod
            return _import_oai_submodule(submodule)
        return _oai_sdk

    # --- First-time bootstrap ---
    import importlib

    local_agents_dir = Path(__file__).resolve().parent.parent.parent

    # 1. Save and remove ONLY the top-level 'agents' key (our local package).
    #    Also save our local submodule entries temporarily.
    saved_top = sys.modules.pop("agents", None)
    saved_local_subs = {}
    for k in list(sys.modules):
        if k.startswith("agents."):
            saved_local_subs[k] = sys.modules.pop(k)

    saved_path = sys.path[:]

    try:
        # 2. Strip project root from sys.path
        sys.path = [
            p for p in sys.path
            if Path(p).resolve() != local_agents_dir.resolve()
            and not (p == "" and (Path.cwd() / "agents" / "__init__.py").exists())
        ]

        # 3. Import the SDK (populates agents + agents.* submodules)
        oai = importlib.import_module("agents")
        if not hasattr(oai, "function_tool"):
            raise ImportError("Found 'agents' but it lacks function_tool")

        # Import requested submodule while path is clean
        sub_mod = None
        if submodule:
            sub_mod = importlib.import_module(f"agents.{submodule}")

        _oai_sdk = oai

    except ImportError:
        raise ImportError(
            "openai-agents SDK not found. Install with: pip install openai-agents"
        )
    finally:
        # 4. Restore sys.path
        sys.path = saved_path

        # 5. Keep all SDK submodule entries (agents.run, agents.agent, ...)
        #    in sys.modules — no collisions with our local submodules.
        #    Put our local submodules back too.
        sys.modules.update(saved_local_subs)

        # 6. Restore our local package as the top-level 'agents' entry.
        if saved_top is not None:
            sys.modules["agents"] = saved_top

    return sub_mod if sub_mod is not None else oai


def _import_oai_submodule(submodule: str):
    """Import an additional SDK submodule after initial bootstrap."""
    import importlib

    local_agents_dir = Path(__file__).resolve().parent.parent.parent

    # Temporarily swap the top-level 'agents' to the SDK module
    saved_top = sys.modules.get("agents")
    sys.modules["agents"] = _oai_sdk

    saved_path = sys.path[:]
    sys.path = [
        p for p in sys.path
        if Path(p).resolve() != local_agents_dir.resolve()
        and not (p == "" and (Path.cwd() / "agents" / "__init__.py").exists())
    ]

    try:
        mod = importlib.import_module(f"agents.{submodule}")
        return mod
    finally:
        sys.path = saved_path
        if saved_top is not None:
            sys.modules["agents"] = saved_top


# Lazy initialization — tools are decorated on first import of this module,
# but only if the SDK is available.
try:
    _oai = _import_openai_agents()
    function_tool = _oai.function_tool
except ImportError:
    # SDK not installed — define a passthrough decorator so the module
    # can still be imported (will fail at runtime when actually called).
    def function_tool(fn):  # type: ignore[misc]
        fn._openai_tool_stub = True
        return fn


@function_tool
async def run_command(command: str, timeout_seconds: int = 120) -> str:
    """Execute a shell command and return its output.

    Args:
        command: The bash command to run.
        timeout_seconds: Maximum seconds before killing the process (default 120).

    Returns:
        Combined stdout+stderr output, or an error message on timeout/failure.
    """
    proc = await asyncio.create_subprocess_shell(
        command,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        cwd=str(_ROOT),
        env={**os.environ, "TERM": "dumb"},
    )
    try:
        stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout_seconds)
    except asyncio.TimeoutError:
        proc.kill()
        return f"[TIMEOUT] Command killed after {timeout_seconds}s: {command}"

    output = stdout.decode(errors="replace").strip()
    if proc.returncode != 0:
        return f"[EXIT {proc.returncode}]\n{output}"
    return output or "(no output)"


@function_tool
async def grep_search(
    pattern: str,
    path: str = ".",
    glob: str = "",
    case_insensitive: bool = False,
    context_lines: int = 0,
) -> str:
    """Search file contents using ripgrep.

    Args:
        pattern: Regex pattern to search for.
        path: Directory or file to search in (relative to project root).
        glob: Optional glob filter (e.g. "*.lean", "*.py").
        case_insensitive: If True, search case-insensitively.
        context_lines: Number of context lines around each match.

    Returns:
        Matching lines with file paths and line numbers.
    """
    cmd = ["rg", "--no-heading", "--line-number"]
    if case_insensitive:
        cmd.append("-i")
    if context_lines > 0:
        cmd.extend(["-C", str(context_lines)])
    if glob:
        cmd.extend(["--glob", glob])
    cmd.append(pattern)
    cmd.append(path)

    proc = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        cwd=str(_ROOT),
    )
    stdout, _ = await proc.communicate()
    output = stdout.decode(errors="replace").strip()

    if proc.returncode == 1:
        return "(no matches)"
    if proc.returncode not in (0, 1):
        return f"[rg error, exit {proc.returncode}]\n{output}"

    # Truncate very large outputs
    lines = output.splitlines()
    if len(lines) > 200:
        return "\n".join(lines[:200]) + f"\n... ({len(lines) - 200} more lines)"
    return output or "(no matches)"


@function_tool
async def read_file(path: str, offset: int = 0, limit: int = 2000) -> str:
    """Read a file's contents.

    Args:
        path: File path relative to project root (or absolute).
        offset: Line number to start reading from (0-based).
        limit: Maximum number of lines to read.

    Returns:
        File contents with line numbers.
    """
    p = Path(path)
    if not p.is_absolute():
        p = _ROOT / p
    if not p.exists():
        return f"File not found: {path}"
    if not p.is_file():
        return f"Not a file: {path}"

    text = p.read_text(errors="replace")
    lines = text.splitlines()
    selected = lines[offset:offset + limit]

    numbered = []
    for i, line in enumerate(selected, start=offset + 1):
        numbered.append(f"{i:>6}\t{line}")
    return "\n".join(numbered) or "(empty file)"


@function_tool
async def write_file(path: str, content: str) -> str:
    """Create a NEW file with the given content. Refuses to overwrite existing files.

    For modifying existing files, use edit_file instead.

    Args:
        path: File path relative to project root (or absolute).
        content: The content to write.

    Returns:
        Confirmation message, or an error if the file already exists.
    """
    p = Path(path)
    if not p.is_absolute():
        p = _ROOT / p
    if p.exists():
        return (
            f"ERROR: {path} already exists. Use edit_file to modify existing files. "
            f"write_file is only for creating NEW files."
        )
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content)
    return f"Created {p.relative_to(_ROOT)} ({len(content)} bytes)"


@function_tool
async def edit_file(path: str, old_string: str, new_string: str) -> str:
    """Edit an existing file by replacing an exact string match.

    Works like a surgical find-and-replace. The old_string must appear
    EXACTLY once in the file (to avoid ambiguous edits). Read the file
    first to get the exact text to replace.

    Args:
        path: File path relative to project root (or absolute).
        old_string: The exact text to find and replace (must be unique in the file).
        new_string: The replacement text.

    Returns:
        Confirmation with line count change, or error if old_string not found
        or appears multiple times.
    """
    p = Path(path)
    if not p.is_absolute():
        p = _ROOT / p
    if not p.exists():
        return f"ERROR: File not found: {path}"
    if not p.is_file():
        return f"ERROR: Not a file: {path}"

    text = p.read_text(errors="replace")
    count = text.count(old_string)

    if count == 0:
        # Show a snippet of the file to help the model find the right text
        preview = text[:500] + "..." if len(text) > 500 else text
        return (
            f"ERROR: old_string not found in {path}. "
            f"Read the file first to get the exact text. "
            f"File starts with:\n{preview}"
        )
    if count > 1:
        return (
            f"ERROR: old_string appears {count} times in {path}. "
            f"Provide a longer/more specific old_string that matches exactly once."
        )

    new_text = text.replace(old_string, new_string, 1)
    p.write_text(new_text)

    old_lines = len(old_string.splitlines())
    new_lines = len(new_string.splitlines())
    delta = new_lines - old_lines
    sign = f"+{delta}" if delta >= 0 else str(delta)
    return f"Edited {p.relative_to(_ROOT)} ({sign} lines)"


@function_tool
async def dispatch_agent(
    agent: str,
    prompt: str,
    model: str = "openai:gpt-5.2",
    timeout_seconds: int = 600,
) -> str:
    """Dispatch a specialist sub-agent and wait for its output.

    Use this to launch sub-agents (lean-formalizer, literature-scout,
    attack-analytic, attack-algebraic, attack-combinatorial,
    attack-information, paper-writer) with a specific goal.

    Args:
        agent: Agent name (e.g. "lean-formalizer", "literature-scout").
        prompt: Detailed instructions/goal for the agent.
        model: Provider-qualified model (e.g. "openai:gpt-5.2", "claude:opus").
        timeout_seconds: Max seconds to wait (default 600 = 10 min).

    Returns:
        The agent's console output (text, tool calls, result).
    """
    import shlex

    venv_python = str(_ROOT / ".venv" / "bin" / "python")
    cmd = [
        venv_python, "-m", "agents", "run-openai",
        "--agent", agent,
        "--prompt", prompt,
        "--model", model,
    ]

    proc = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        cwd=str(_ROOT),
        env={**os.environ, "TERM": "dumb"},
    )
    try:
        stdout, _ = await asyncio.wait_for(proc.communicate(), timeout=timeout_seconds)
    except asyncio.TimeoutError:
        proc.kill()
        return f"[TIMEOUT] Agent {agent} killed after {timeout_seconds}s"

    output = stdout.decode(errors="replace").strip()
    if proc.returncode != 0:
        return f"[Agent {agent} exited with code {proc.returncode}]\n{output}"
    return output or f"[Agent {agent} produced no output]"


@function_tool
async def list_files(pattern: str = "**/*", path: str = ".") -> str:
    """List files matching a glob pattern.

    Args:
        pattern: Glob pattern (e.g. "**/*.lean", "agents/*.py").
        path: Base directory relative to project root.

    Returns:
        Matching file paths, one per line.
    """
    base = _ROOT / path
    if not base.exists():
        return f"Directory not found: {path}"

    matches = sorted(base.glob(pattern))
    files = [str(m.relative_to(_ROOT)) for m in matches if m.is_file()]

    if len(files) > 200:
        return "\n".join(files[:200]) + f"\n... ({len(files) - 200} more files)"
    return "\n".join(files) or "(no matches)"
