"""Claude Agent SDK backend.

Extracts the core Claude Code streaming logic from coordinator.py into
a ProviderBackend implementation.
"""

from __future__ import annotations

from typing import AsyncIterator

from claude_agent_sdk import (
    AgentDefinition,
    AssistantMessage,
    ClaudeAgentOptions,
    ResultMessage,
    SystemMessage,
    TextBlock,
    query,
)
from claude_agent_sdk.types import ToolUseBlock

from ..config import ROOT
from ..rendering import AgentEvent, EventKind, console, _tool_detail
from . import AgentSpec, ProviderBackend

# 50 MB buffer — Claude Code's system context is large.
_MAX_BUF = 50 * 1024 * 1024

# Short aliases accepted after the ``claude:`` prefix.  The CLI understands
# ``opus``/``sonnet``/``haiku``/``fable`` natively; ``fable`` is mapped to its
# full id so ``--model claude:fable`` works regardless of CLI alias support.
# ``claude:fable`` is a valid COORDINATOR model (``coordinate --model claude:fable``).
_CLAUDE_MODEL_ALIASES: dict[str, str] = {
    "fable": "claude-fable-5",
    "fable-5": "claude-fable-5",
    "opus": "opus",
    "sonnet": "sonnet",
    "haiku": "haiku",
}


def resolve_claude_model(name: str) -> str:
    """Map a short alias (``fable``, ``opus``, ...) to what the CLI expects."""
    return _CLAUDE_MODEL_ALIASES.get(name, name)


class ClaudeBackend:
    """ProviderBackend for the Claude Agent SDK (claude-agent-sdk)."""

    def _build_options(
        self,
        spec: AgentSpec,
        *,
        agents: dict[str, AgentDefinition] | None = None,
    ) -> ClaudeAgentOptions:
        """Build ClaudeAgentOptions from an AgentSpec."""
        tools = spec.tools
        opts = ClaudeAgentOptions(
            model=resolve_claude_model(spec.model_name),
            system_prompt=spec.system_prompt,
            allowed_tools=tools,
            agents=agents,
            cwd=str(ROOT),
            permission_mode="default",
            max_turns=spec.max_turns,
            max_budget_usd=spec.budget,
            max_buffer_size=_MAX_BUF,
            setting_sources=[],
            stderr=lambda line: console.print(f"[dim red]stderr:[/] [dim]{line}[/]"),
        )
        # Only restrict tool visibility for agents WITHOUT sub-agents.
        # The coordinator needs tools=None so sub-agents can access their
        # own tools; direct runners get a locked-down list.
        if agents is None:
            opts.tools = tools
        return opts

    async def run(
        self,
        spec: AgentSpec,
        prompt: str,
        *,
        agents: dict[str, AgentDefinition] | None = None,
    ) -> AsyncIterator[AgentEvent]:
        """Stream AgentEvents from a Claude Code session."""
        options = self._build_options(spec, agents=agents)
        label = spec.label
        turn = 0

        yield AgentEvent(
            kind=EventKind.START,
            label=label,
            provider="claude",
            model=spec.model_name,
        )

        try:
            async for message in query(prompt=prompt, options=options):
                if isinstance(message, ResultMessage):
                    cost = f"${message.total_cost_usd:.4f}" if message.total_cost_usd else "?"
                    yield AgentEvent(
                        kind=EventKind.RESULT,
                        label=label,
                        provider="claude",
                        model=spec.model_name,
                        is_error=message.is_error,
                        num_turns=message.num_turns or 0,
                        cost=cost,
                    )

                elif isinstance(message, AssistantMessage):
                    turn += 1
                    for block in message.content:
                        if isinstance(block, TextBlock) and block.text.strip():
                            yield AgentEvent(
                                kind=EventKind.TEXT,
                                label=label,
                                provider="claude",
                                model=spec.model_name,
                                turn=turn,
                                text=block.text,
                            )
                        elif isinstance(block, ToolUseBlock):
                            inp = block.input or {}
                            yield AgentEvent(
                                kind=EventKind.TOOL_USE,
                                label=label,
                                provider="claude",
                                model=spec.model_name,
                                tool_name=block.name,
                                tool_detail=_tool_detail(block.name, inp),
                                extra=inp,
                            )

                elif isinstance(message, SystemMessage):
                    subtype = getattr(message, "subtype", "")
                    data = getattr(message, "data", {})
                    if subtype == "agent_start":
                        yield AgentEvent(
                            kind=EventKind.SUBAGENT_START,
                            label=label,
                            provider="claude",
                            model=spec.model_name,
                            subagent_name=data.get("agent_name", "?"),
                        )
                    elif subtype == "agent_stop":
                        yield AgentEvent(
                            kind=EventKind.SUBAGENT_STOP,
                            label=label,
                            provider="claude",
                            model=spec.model_name,
                            subagent_name=data.get("agent_name", "?"),
                        )

        except BaseException:
            import traceback
            yield AgentEvent(
                kind=EventKind.ERROR,
                label=label,
                provider="claude",
                model=spec.model_name,
                text=traceback.format_exc(),
            )
