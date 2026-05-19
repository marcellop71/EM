"""Qwen backend — self-hosted OpenAI-compatible endpoint (vLLM or sglang).

Originally a thin subclass of OpenAIBackend that pointed the
openai-agents SDK at our DGX endpoint. That worked for plain
chat but broke for tool-using agents: Qwen models emit tool calls
as Hermes-style XML in the `content` field (and vLLM 0.6.x
refuses `tool_choice: auto` without the `--enable-auto-tool-choice
--tool-call-parser …` server flags, which weren't reliably
configurable in our deployment).

This version is a **hand-rolled agent loop**: direct HTTP POSTs
to `/v1/chat/completions`, manual conversation history, manual
tool dispatch. We parse both:

  * Structured `tool_calls` (if the server happens to be doing
    server-side XML→OpenAI conversion).
  * Hermes-style XML inside `content`:
      `<tool_call><function=NAME><parameter=K>V…</tool_call>`
  * JSON-in-XML:
      `<tool_call>{"name":"NAME","arguments":{"K":"V"}}</tool_call>`

Tools are dispatched against a small fixed registry in
`qwen_tool_dispatch.py` that mirrors the operations
`openai_tools.py` exposes to the openai-agents SDK.
"""

from __future__ import annotations

import asyncio
import json
import os
import re
import time
import uuid
from typing import Any, AsyncIterator

import httpx

from ..config import DGX_API_KEY, DGX_CHARS_PER_TOKEN, resolve_dgx_model
from ..rendering import AgentEvent, EventKind
from . import AgentSpec
from . import qwen_tool_dispatch as _qtd


# ---------------------------------------------------------------------------
# Hermes-style XML tool-call parser
# ---------------------------------------------------------------------------

# Two formats observed in practice; we try both.
#
# Format A — JSON-in-XML (Qwen3 / newer Hermes):
#   <tool_call>{"name": "read_file", "arguments": {"path": "/tmp/foo"}}</tool_call>
#
# Format B — pseudo-XML (older Hermes):
#   <tool_call>
#     <function=read_file>
#       <parameter=path> /tmp/foo
#     </function>
#   </tool_call>
#
# Some servers emit the block without `<tool_call>` wrappers at all —
# just `<function=NAME><parameter=K>V…</function>`. We accept that
# too as a fallback.

_BLOCK_RX = re.compile(r"<tool_call>\s*(.*?)\s*</tool_call>", re.DOTALL)
_JSON_INNER_RX = re.compile(r"^\s*(\{.*\})\s*$", re.DOTALL)
_FN_RX = re.compile(r"<function=([\w.\-]+)>", re.DOTALL)
_PARAM_RX = re.compile(
    # Match `<parameter=NAME>VALUE` where VALUE runs up to (but not
    # including) the next `<parameter=…>` start, an optional
    # `</parameter>` closer, a `</function>` / `</tool_call>` block
    # closer, or end-of-string. The optional `</parameter>` closer
    # matters: Qwen3.5 emits it; the older Hermes format doesn't.
    r"<parameter=([\w.\-]+)>\s*(.*?)\s*(?=</parameter>|<parameter=|</function>|</tool_call>|$)",
    re.DOTALL,
)


def _parse_xml_tool_calls(content: str) -> list[dict[str, Any]]:
    """Return a list of OpenAI-format `tool_calls` dicts extracted
    from any Hermes-style XML in `content`. Returns [] if nothing
    looks like a tool call."""
    if not content:
        return []

    calls: list[dict[str, Any]] = []
    blocks = _BLOCK_RX.findall(content)

    # If no <tool_call> wrappers found but we have <function=…>,
    # treat the whole content as one implicit block.
    if not blocks and "<function=" in content:
        blocks = [content]

    for block in blocks:
        # Try JSON inside the block first.
        json_m = _JSON_INNER_RX.match(block)
        if json_m:
            try:
                obj = json.loads(json_m.group(1))
                name = obj.get("name") or obj.get("function")
                args = obj.get("arguments") or obj.get("parameters") or {}
                if name:
                    calls.append({
                        "id": f"call_{uuid.uuid4().hex[:8]}",
                        "type": "function",
                        "function": {
                            "name": str(name),
                            "arguments": (
                                json.dumps(args) if isinstance(args, dict)
                                else (args if isinstance(args, str) else str(args))
                            ),
                        },
                    })
                    continue
            except (json.JSONDecodeError, ValueError, TypeError):
                pass

        # Otherwise treat as pseudo-XML.
        fn_m = _FN_RX.search(block)
        if not fn_m:
            continue
        name = fn_m.group(1)
        params: dict[str, str] = {}
        for pm in _PARAM_RX.finditer(block):
            params[pm.group(1)] = pm.group(2).strip()
        calls.append({
            "id": f"call_{uuid.uuid4().hex[:8]}",
            "type": "function",
            "function": {
                "name": name,
                "arguments": json.dumps(params),
            },
        })

    return calls


def _strip_tool_call_xml(content: str) -> str:
    """Remove tool-call XML from `content` so we don't redundantly
    print the same call as text. Best-effort; if regex doesn't
    match cleanly, returns the original string."""
    stripped = _BLOCK_RX.sub("", content)
    # Also strip lone <function=…>…</function> if present.
    stripped = re.sub(r"<function=[^>]*>.*?</function>", "", stripped, flags=re.DOTALL)
    # And any orphan <parameter=…>…</parameter> fragments the model
    # may emit without a tool_call wrapper.
    stripped = re.sub(r"<parameter=[^>]*>.*?</parameter>", "", stripped, flags=re.DOTALL)
    return stripped.strip()


# ---------------------------------------------------------------------------
# Tool schemas + dispatch
# ---------------------------------------------------------------------------

def _build_tool_schemas(tool_names: list[str]) -> list[dict[str, Any]]:
    """OpenAI-format `tools` array describing what the model may call.
    The names match what `qwen_tool_dispatch` knows how to invoke."""
    return [_qtd.SCHEMAS[name] for name in tool_names if name in _qtd.SCHEMAS]


async def _dispatch_tool(name: str, args: dict[str, Any]) -> str:
    """Invoke a named tool with parsed arguments. Returns the result
    as a string (the model's tool message). Never raises — returns
    an error string on failure so the agent loop can continue."""
    handler = _qtd.HANDLERS.get(name)
    if handler is None:
        return f"<tool-error>unknown tool: {name}</tool-error>"
    try:
        result = await handler(args)
        text = result if isinstance(result, str) else json.dumps(result)
        return _qtd._truncate_result(text)
    except Exception as e:
        return f"<tool-error>{type(e).__name__}: {e}</tool-error>"


# ---------------------------------------------------------------------------
# Context-window guard
# ---------------------------------------------------------------------------
#
# The DGX serves the model with max_model_len = 65536 tokens, and the
# largest system prompts (formalizer.md) are ~30k tokens on their own.
# The agent loop never compacts history, so long tool-heavy sessions
# would exceed the window and the server would 400 — killing the agent
# mid-run with all progress lost. Before each request we enforce a
# character budget (~3.5 chars/token heuristic) by stubbing out the
# OLDEST tool results first; the system prompt, the task prompt, and
# the most recent exchanges are never touched.

_MAX_CONTEXT_CHARS = 190_000   # legacy default budget (~54k tokens @ 3.5 c/t)
_KEEP_RECENT_MESSAGES = 8      # never shrink the last N messages
_TOOL_STUB = "[older tool output dropped to fit the context window]"


def _parse_reported_input_tokens(body: str) -> int | None:
    """Extract the input-token count a vLLM/sglang 400 reports, e.g.
    '...prompt contains at least 61441 input tokens...' or
    '"value":61441'. Returns None if not found."""
    for rx in (r"contains at least (\d+) input tokens",
               r"(\d+)\s+input tokens",
               r'"value"\s*:\s*(\d+)'):
        m = re.search(rx, body)
        if m:
            try:
                return int(m.group(1))
            except ValueError:
                pass
    return None


def _messages_chars(messages: list[dict[str, Any]]) -> int:
    total = 0
    for m in messages:
        total += len(m.get("content") or "")
        for tc in m.get("tool_calls") or []:
            total += len(json.dumps(tc))
    return total


def _shrink_history(messages: list[dict[str, Any]],
                    budget: int = _MAX_CONTEXT_CHARS,
                    hard: bool = False) -> None:
    """Drop oldest tool-result contents in place until under `budget` chars.

    `budget` is derived by the caller from the model's context window minus
    the completion reserve (see QwenBackend.run); it defaults to the legacy
    constant for any out-of-band caller. When `hard=True` (used on a
    context-length 400 retry) the normally-protected recent tail and the
    task prompt (index 1) are trimmed too — last-resort, but better than a
    dead agent."""
    if _messages_chars(messages) <= budget:
        return
    # Candidates: tool messages outside the protected recent tail,
    # oldest first (skip index 0/1 = system + task prompt).
    cutoff = max(2, len(messages) - _KEEP_RECENT_MESSAGES)
    for m in messages[2:cutoff]:
        if m.get("role") == "tool" and m.get("content") not in (None, _TOOL_STUB):
            m["content"] = _TOOL_STUB
            if _messages_chars(messages) <= budget:
                return
    # Still over budget (huge assistant turns): truncate old assistant
    # text as a last resort.
    for m in messages[2:cutoff]:
        content = m.get("content")
        if m.get("role") == "assistant" and content and len(content) > 2_000:
            m["content"] = content[:2_000] + "\n[truncated]"
            if _messages_chars(messages) <= budget:
                return
    # Final pass: the protected tail itself can hold several near-cap
    # tool results. Truncate (don't stub) them, keeping the END of each
    # — for build output the latest errors are what matters.
    for m in messages[cutoff:]:
        content = m.get("content")
        if m.get("role") == "tool" and content and len(content) > 8_000:
            m["content"] = "[truncated to fit context]\n...\n" + content[-8_000:]
            if _messages_chars(messages) <= budget:
                return
    if not hard:
        return
    # HARD mode: shrink the protected tail aggressively (tool results to 2k,
    # keeping the END where build errors live), then the task prompt.
    for m in messages[cutoff:]:
        content = m.get("content")
        if m.get("role") == "tool" and content and len(content) > 2_000:
            m["content"] = "[hard-truncated]\n...\n" + content[-2_000:]
            if _messages_chars(messages) <= budget:
                return
    for m in messages[cutoff:]:
        content = m.get("content")
        if m.get("role") == "assistant" and content and len(content) > 800:
            m["content"] = content[:800] + "\n[hard-truncated]"
            if _messages_chars(messages) <= budget:
                return
    # Task prompt (index 1) as the final lever — keep as much of its HEAD as
    # the remaining budget allows (the goal/plan lives at the top).
    if len(messages) > 1:
        c1 = messages[1].get("content") or ""
        overflow = _messages_chars(messages) - budget
        if overflow > 0 and len(c1) > 2_000:
            keep = max(2_000, len(c1) - overflow - 200)
            if keep < len(c1):
                messages[1]["content"] = (
                    c1[:keep] + "\n[task prompt truncated to fit context]")


# ---------------------------------------------------------------------------
# HTTP transport
# ---------------------------------------------------------------------------

class _Http:
    """Tiny httpx wrapper that holds the AsyncClient open across the
    agent loop's turns (saves TCP/TLS handshake per call)."""

    def __init__(self, endpoint: str, api_key: str, timeout: float = 600.0,
                 server: str = "sglang"):
        self.endpoint = endpoint.rstrip("/")
        self.api_key = api_key
        self.server = server  # "sglang" | "vllm" | "llamacpp"
        self._client = httpx.AsyncClient(timeout=timeout)

    async def close(self) -> None:
        await self._client.aclose()

    async def chat_completion(
        self,
        model: str,
        messages: list[dict[str, Any]],
        tools: list[dict[str, Any]] | None,
        max_tokens: int = 4096,
        temperature: float = 0.0,
    ) -> dict[str, Any]:
        body: dict[str, Any] = {
            "model": model,
            "messages": messages,
            "max_tokens": max_tokens,
            "temperature": temperature,
            "stream": False,
        }
        # sglang/vLLM accept chat_template_kwargs (used to disable Qwen3
        # thinking); llama.cpp rejects unknown top-level keys, so only
        # send it to servers that understand it.
        if model.lower().startswith("qwen3") and self.server != "llamacpp":
            body["chat_template_kwargs"] = {"enable_thinking": False}
        if tools:
            body["tools"] = tools
            # Avoid `tool_choice: auto` — vLLM 400s without the
            # server-side parser flag. The model decides whether to
            # call a tool based on the prompt and tool descriptions.
        r = await self._client.post(
            f"{self.endpoint}/chat/completions",
            json=body,
            headers={"Authorization": f"Bearer {self.api_key}"},
        )
        r.raise_for_status()
        return r.json()


# ---------------------------------------------------------------------------
# QwenBackend — hand-rolled agent loop
# ---------------------------------------------------------------------------

class QwenBackend:
    """ProviderBackend for the DGX's local OpenAI-compatible endpoints
    (registered under BOTH the `dgx:` and legacy `qwen:` prefixes; the
    model suffix selects the endpoint via `config.resolve_dgx_model` —
    e.g. `dgx:qwen` → sglang:8000, `dgx:ornith` → llama.cpp:8001). Implements its own multi-
    turn agent loop so we can parse XML tool calls client-side,
    independent of the server's tool-call parser configuration."""

    async def run(
        self,
        spec: AgentSpec,
        prompt: str,
    ) -> AsyncIterator[AgentEvent]:
        # Resolve `dgx:<alias>` / `qwen:<alias>` → (alias, endpoint,
        # served-model id, server flavour) via the DGX registry.
        alias, endpoint, model_name, server, context_window = resolve_dgx_model(spec.model_name)
        provider_label = f"dgx:{alias}"

        label = spec.label
        yield AgentEvent(
            kind=EventKind.START,
            label=label,
            provider=provider_label,
            model=model_name,
        )

        http = _Http(endpoint, DGX_API_KEY, server=server)
        tools_schema = _build_tool_schemas(list(spec.tools))

        # Optional per-agent overrides (spec.extra); defaults match the
        # previous hardcoded values.
        temperature = float(spec.extra.get("temperature", 0.0))
        # Context-window budgeting. The server's hard window is
        # `context_window` tokens (default 65536; overridable via
        # --dgx-ctx / DGX_CONTEXT_WINDOW / {ALIAS}_MAX_MODEL_LEN). Reserve
        # `max_tokens` for the completion, keep a small safety margin, and
        # convert the remaining token room to a character budget for
        # `_shrink_history`. `spec.extra["context_window"]` overrides the
        # resolved value for this one agent if provided.
        context_window = int(spec.extra.get("context_window", context_window))
        _env_mt = os.environ.get("DGX_MAX_TOKENS")
        # `want_tokens` is the DESIRED completion cap (default 4096). It is an
        # upper bound, NOT a fixed reservation: the actual per-request cap is
        # recomputed below from the real prompt size so that
        #   input_tokens + max_tokens <= context_window
        # always holds — otherwise the server 400s (e.g. --dgx-max-tokens 65536
        # in a 65536 window leaves no room for input). See `_effective_cap`.
        want_tokens = int(spec.extra.get("max_tokens",
                                         int(_env_mt) if _env_mt else 4096))
        _MIN_COMPLETION = 256   # never request fewer than this
        _SAFETY_TOK = 1024      # tokenizer variance + role/format overhead
        # For history shrinking we reserve room for a completion of at most
        # min(want, 8192) tokens; a larger `want` is only satisfiable when the
        # prompt is small (handled dynamically per request, not by starving
        # history down to nothing).
        _hist_reserve = min(max(want_tokens, _MIN_COMPLETION), 8192)
        history_budget = int(
            max(1024, context_window - _hist_reserve - _SAFETY_TOK)
            * DGX_CHARS_PER_TOKEN)

        def _effective_cap(msgs: list[dict[str, Any]]) -> int:
            """Completion cap that fits: window - est_input_tokens - safety,
            clamped into [_MIN_COMPLETION, want_tokens]. Estimates input tokens
            from the char count (rounded UP) so we never overshoot the window."""
            import math
            est_input = math.ceil(_messages_chars(msgs) / DGX_CHARS_PER_TOKEN)
            room = context_window - est_input - _SAFETY_TOK
            return max(_MIN_COMPLETION, min(want_tokens, room))

        def _effective_cap_ratio(msgs: list[dict[str, Any]], ratio: float) -> int:
            """Like `_effective_cap` but with a calibrated chars/token `ratio`
            (from the server's reported token count on a 400 retry)."""
            import math as _m
            est_input = _m.ceil(_messages_chars(msgs) / max(1.5, ratio))
            room = context_window - est_input - _SAFETY_TOK
            return max(_MIN_COMPLETION, min(want_tokens, room))

        messages: list[dict[str, Any]] = [
            {"role": "system", "content": spec.system_prompt},
            {"role": "user", "content": prompt},
        ]

        turn = 0
        try:
            for turn_idx in range(1, spec.max_turns + 1):
                _shrink_history(messages, history_budget)
                max_tokens = _effective_cap(messages)
                resp = None
                for attempt in range(4):
                    try:
                        resp = await http.chat_completion(
                            model=model_name,
                            messages=messages,
                            tools=tools_schema,
                            max_tokens=max_tokens,
                            temperature=temperature,
                        )
                        break
                    except httpx.HTTPStatusError as e:
                        body = e.response.text or ""
                        is_ctx = e.response.status_code == 400 and (
                            "context length" in body or "input_tokens" in body)
                        reported = _parse_reported_input_tokens(body)
                        if is_ctx and reported and attempt < 3:
                            # Calibrate the REAL chars/token from the server's
                            # count, then tighten the budget to fit and re-shrink
                            # (hard) — the char heuristic under-counted here.
                            cur_chars = _messages_chars(messages)
                            ratio = max(1.5, cur_chars / max(1, reported))
                            target_tok = max(
                                1024, context_window - _MIN_COMPLETION - _SAFETY_TOK)
                            history_budget = int(target_tok * ratio * 0.92)
                            _shrink_history(messages, history_budget, hard=True)
                            max_tokens = _effective_cap_ratio(messages, ratio)
                            continue
                        yield AgentEvent(
                            kind=EventKind.ERROR,
                            label=label,
                            provider=provider_label,
                            model=model_name,
                            text=f"HTTP {e.response.status_code}: {body[:400]}",
                        )
                        return
                    except Exception as e:
                        yield AgentEvent(
                            kind=EventKind.ERROR,
                            label=label,
                            provider=provider_label,
                            model=model_name,
                            text=f"{type(e).__name__}: {str(e)[:400]}",
                        )
                        return
                if resp is None:
                    yield AgentEvent(
                        kind=EventKind.ERROR, label=label,
                        provider=provider_label, model=model_name,
                        text="context-length retries exhausted (prompt too large "
                             "to fit the model window even after hard shrink)",
                    )
                    return

                choice = (resp.get("choices") or [{}])[0]
                msg = choice.get("message", {}) or {}
                raw_content = msg.get("content") or ""

                # Combine structured + XML-parsed tool calls.
                tool_calls = list(msg.get("tool_calls") or [])
                if not tool_calls:
                    tool_calls = _parse_xml_tool_calls(raw_content)
                # Strip the XML from the printable content so the
                # user doesn't see the raw `<tool_call>…</tool_call>`
                # block twice (once as text, once as tool_use event).
                display_content = (
                    _strip_tool_call_xml(raw_content) if tool_calls else raw_content
                )

                if display_content.strip():
                    turn += 1
                    yield AgentEvent(
                        kind=EventKind.TEXT,
                        label=label,
                        provider=provider_label,
                        model=model_name,
                        turn=turn,
                        text=display_content.strip(),
                    )

                if not tool_calls:
                    # Final turn — no more tools to call.
                    yield AgentEvent(
                        kind=EventKind.RESULT,
                        label=label,
                        provider=provider_label,
                        model=model_name,
                        is_error=False,
                        num_turns=turn,
                        cost="(local: free)",
                    )
                    return

                # Append the assistant message to the history. We
                # echo the (possibly transformed) tool_calls back as
                # what the assistant said — this is what the next
                # turn's input needs.
                messages.append({
                    "role": "assistant",
                    "content": display_content or None,
                    "tool_calls": tool_calls,
                })

                # Dispatch each tool call and emit events.
                for tc in tool_calls:
                    fn = tc.get("function", {}) or {}
                    tool_name = fn.get("name", "?")
                    args_str = fn.get("arguments", "{}")
                    try:
                        args = (
                            json.loads(args_str) if isinstance(args_str, str)
                            else (args_str or {})
                        )
                    except (json.JSONDecodeError, ValueError):
                        args = {}

                    # Build a 60-char detail for the UI.
                    detail = ""
                    for v in args.values():
                        detail = str(v)[:60]
                        break

                    turn += 1
                    yield AgentEvent(
                        kind=EventKind.TOOL_USE,
                        label=label,
                        provider=provider_label,
                        model=model_name,
                        turn=turn,
                        tool_name=tool_name,
                        tool_detail=detail,
                        extra=args,
                    )

                    tool_result = await _dispatch_tool(tool_name, args)

                    # Tool result becomes a `tool` role message,
                    # required by OpenAI chat format for multi-turn
                    # tool-using conversations.
                    messages.append({
                        "role": "tool",
                        "tool_call_id": tc.get("id", ""),
                        "content": tool_result,
                    })

            # If we exit the loop without returning, max_turns hit.
            yield AgentEvent(
                kind=EventKind.RESULT,
                label=label,
                provider=provider_label,
                model=model_name,
                is_error=False,
                num_turns=turn,
                cost=f"(max turns {spec.max_turns} reached)",
            )
        finally:
            await http.close()
