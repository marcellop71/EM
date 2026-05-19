"""OpenAI Agents SDK backend.

Uses the `openai-agents` package (PyPI: openai-agents) with @function_tool
wrappers for filesystem ops, Bash, and Grep.  No MCP servers — the function
tools are pure-Python and avoid the npx startup / timeout issues.

NOTE: The `openai-agents` pip package installs as `agents`, which collides
with this project's `agents/` package.  We use the same importlib trick as
openai_tools.py to resolve the correct module.
"""

from __future__ import annotations

import asyncio
import json
from typing import AsyncIterator

from ..config import ROOT
from ..rendering import AgentEvent, EventKind
from . import AgentSpec


# ---------------------------------------------------------------------------
# Retry configuration
# ---------------------------------------------------------------------------

MAX_RETRIES = 5
INITIAL_BACKOFF_S = 30.0   # first retry waits 30s
BACKOFF_MULTIPLIER = 2.0   # double each retry
MAX_BACKOFF_S = 300.0       # cap at 5 min


def _import_openai_agents(submodule: str | None = None):
    """Import the openai-agents SDK, bypassing our local `agents` package."""
    from ..tools.openai_tools import _import_openai_agents as _imp
    return _imp(submodule)


_AGENTS_SDK_AVAILABLE: bool | None = None


def _ensure_sdk() -> None:
    global _AGENTS_SDK_AVAILABLE
    if _AGENTS_SDK_AVAILABLE is None:
        try:
            _import_openai_agents()
            _AGENTS_SDK_AVAILABLE = True
        except ImportError:
            _AGENTS_SDK_AVAILABLE = False
    if not _AGENTS_SDK_AVAILABLE:
        raise ImportError(
            "openai-agents is not installed. Run: pip install openai-agents"
        )


def _build_tools(tool_names: list[str]) -> list:
    """Map tool name strings to OpenAI function_tool objects."""
    from ..tools.openai_tools import (
        dispatch_agent,
        edit_file,
        grep_search,
        list_files,
        read_file,
        run_command,
        write_file,
    )

    _TOOL_MAP = {
        "Bash": run_command,
        "Read": read_file,
        "Write": write_file,
        "Edit": edit_file,
        "Glob": list_files,
        "Grep": grep_search,
        "Task": dispatch_agent,
    }

    tools = []
    seen = set()
    for name in tool_names:
        t = _TOOL_MAP.get(name)
        if t is not None and id(t) not in seen:
            tools.append(t)
            seen.add(id(t))
    return tools


def _is_rate_limit_error(exc: BaseException) -> bool:
    """Check if an exception is an OpenAI rate-limit (429) error."""
    try:
        import openai
        return isinstance(exc, openai.RateLimitError)
    except ImportError:
        return False


def _parse_retry_after(exc: BaseException) -> float | None:
    """Extract Retry-After seconds from an OpenAI rate-limit response."""
    response = getattr(exc, "response", None)
    if response is None:
        return None
    headers = getattr(response, "headers", {})
    val = headers.get("retry-after") or headers.get("Retry-After")
    if val is not None:
        try:
            return float(val)
        except (ValueError, TypeError):
            pass
    return None


class OpenAIBackend:
    """ProviderBackend for the OpenAI Agents SDK (openai-agents)."""

    async def run(
        self,
        spec: AgentSpec,
        prompt: str,
    ) -> AsyncIterator[AgentEvent]:
        """Stream AgentEvents from an OpenAI agent session.

        Retries with exponential backoff on rate-limit (429) errors.
        """
        _ensure_sdk()
        oai = _import_openai_agents()
        Agent = oai.Agent
        Runner = oai.Runner

        label = spec.label
        model = spec.model_name

        yield AgentEvent(
            kind=EventKind.START,
            label=label,
            provider="openai",
            model=model,
        )

        tools = _build_tools(spec.tools)
        sdk_max_turns = spec.max_turns * 3

        backoff = INITIAL_BACKOFF_S

        for attempt in range(1, MAX_RETRIES + 1):
            agent = Agent(
                name=spec.name,
                instructions=spec.system_prompt,
                model=model,
                tools=tools,
            )

            turn = 0
            text_buf: list[str] = []
            hit_rate_limit = False

            try:
                result = Runner.run_streamed(
                    agent,
                    input=prompt,
                    max_turns=sdk_max_turns,
                )
                async for event in result.stream_events():
                    ev_type = getattr(event, "type", "")

                    if ev_type == "raw_response_event":
                        data = getattr(event, "data", None)
                        if data is not None:
                            delta_text = getattr(data, "delta", None)
                            if isinstance(delta_text, str) and delta_text:
                                text_buf.append(delta_text)

                    elif ev_type == "run_item_stream_event":
                        item = getattr(event, "item", None)
                        name = getattr(event, "name", "")
                        if item is None:
                            continue

                        item_type = getattr(item, "type", "")

                        if name == "tool_called" and item_type == "tool_call_item":
                            if text_buf:
                                turn += 1
                                yield AgentEvent(
                                    kind=EventKind.TEXT,
                                    label=label,
                                    provider="openai",
                                    model=model,
                                    turn=turn,
                                    text="".join(text_buf),
                                )
                                text_buf.clear()

                            raw = getattr(item, "raw_item", None)
                            tool_name = getattr(raw, "name", "") if raw else ""
                            raw_args = getattr(raw, "arguments", "") if raw else ""
                            try:
                                args_dict = json.loads(raw_args) if raw_args else {}
                            except (json.JSONDecodeError, TypeError):
                                args_dict = {}

                            detail = ""
                            if tool_name == "run_command":
                                detail = args_dict.get("command", "")[:80]
                            elif tool_name == "read_file":
                                detail = args_dict.get("path", "")
                            elif tool_name == "write_file":
                                detail = args_dict.get("path", "")
                            elif tool_name == "edit_file":
                                detail = args_dict.get("path", "")
                            elif tool_name == "grep_search":
                                detail = args_dict.get("pattern", "")
                            elif tool_name == "list_files":
                                detail = args_dict.get("pattern", "")
                            elif tool_name == "dispatch_agent":
                                detail = f"{args_dict.get('agent', '')} → {args_dict.get('prompt', '')[:50]}"
                            else:
                                for v in args_dict.values():
                                    detail = str(v)[:60]
                                    break

                            yield AgentEvent(
                                kind=EventKind.TOOL_USE,
                                label=label,
                                provider="openai",
                                model=model,
                                tool_name=tool_name,
                                tool_detail=detail,
                                extra=args_dict,
                            )

                        elif name == "tool_output":
                            pass

                        elif name == "message_output_created" and item_type == "message_output_item":
                            raw = getattr(item, "raw_item", None)
                            if raw is not None:
                                content = getattr(raw, "content", [])
                                parts = []
                                for part in content:
                                    text = getattr(part, "text", "")
                                    if text:
                                        parts.append(text)
                                if parts:
                                    turn += 1
                                    yield AgentEvent(
                                        kind=EventKind.TEXT,
                                        label=label,
                                        provider="openai",
                                        model=model,
                                        turn=turn,
                                        text="\n".join(parts),
                                    )

                # Flush remaining text
                if text_buf:
                    turn += 1
                    yield AgentEvent(
                        kind=EventKind.TEXT,
                        label=label,
                        provider="openai",
                        model=model,
                        turn=turn,
                        text="".join(text_buf),
                    )
                    text_buf.clear()

                yield AgentEvent(
                    kind=EventKind.RESULT,
                    label=label,
                    provider="openai",
                    model=model,
                    is_error=False,
                    num_turns=turn,
                    cost="(see OpenAI dashboard)",
                )
                return  # success — exit retry loop

            except BaseException as exc:
                import traceback

                # MaxTurnsExceeded is graceful, not a crash.
                oai_exc = _import_openai_agents("exceptions")
                if isinstance(exc, oai_exc.MaxTurnsExceeded):
                    if text_buf:
                        turn += 1
                        yield AgentEvent(
                            kind=EventKind.TEXT,
                            label=label,
                            provider="openai",
                            model=model,
                            turn=turn,
                            text="".join(text_buf),
                        )
                        text_buf.clear()

                    yield AgentEvent(
                        kind=EventKind.RESULT,
                        label=label,
                        provider="openai",
                        model=model,
                        is_error=False,
                        num_turns=turn,
                        cost=f"(max turns {sdk_max_turns} reached)",
                    )
                    return

                # Rate-limit error → retry with backoff
                if _is_rate_limit_error(exc):
                    hit_rate_limit = True
                    retry_after = _parse_retry_after(exc)
                    wait = retry_after if retry_after else backoff

                    if attempt < MAX_RETRIES:
                        yield AgentEvent(
                            kind=EventKind.RETRY,
                            label=label,
                            provider="openai",
                            model=model,
                            text=f"Rate limited (429). Waiting {wait:.0f}s before retry {attempt}/{MAX_RETRIES}...",
                        )
                        await asyncio.sleep(wait)
                        backoff = min(backoff * BACKOFF_MULTIPLIER, MAX_BACKOFF_S)
                        continue  # retry
                    else:
                        yield AgentEvent(
                            kind=EventKind.ERROR,
                            label=label,
                            provider="openai",
                            model=model,
                            text=f"Rate limited after {MAX_RETRIES} retries. Last error:\n{traceback.format_exc()}",
                        )
                        return

                # Also catch generic APIError with status 429 (belt and suspenders)
                status = getattr(exc, "status_code", None)
                if status == 429:
                    hit_rate_limit = True
                    retry_after = _parse_retry_after(exc)
                    wait = retry_after if retry_after else backoff

                    if attempt < MAX_RETRIES:
                        yield AgentEvent(
                            kind=EventKind.RETRY,
                            label=label,
                            provider="openai",
                            model=model,
                            text=f"Rate limited (429). Waiting {wait:.0f}s before retry {attempt}/{MAX_RETRIES}...",
                        )
                        await asyncio.sleep(wait)
                        backoff = min(backoff * BACKOFF_MULTIPLIER, MAX_BACKOFF_S)
                        continue
                    else:
                        yield AgentEvent(
                            kind=EventKind.ERROR,
                            label=label,
                            provider="openai",
                            model=model,
                            text=f"Rate limited after {MAX_RETRIES} retries. Last error:\n{traceback.format_exc()}",
                        )
                        return

                # Any other error — crash immediately, no retry
                yield AgentEvent(
                    kind=EventKind.ERROR,
                    label=label,
                    provider="openai",
                    model=model,
                    text=traceback.format_exc(),
                )
                return
