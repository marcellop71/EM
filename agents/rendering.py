"""Shared rich console rendering for all provider backends."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Any

from rich.console import Console
from rich.markdown import Markdown
from rich.markup import escape
from rich.panel import Panel
from rich.table import Table
from rich.text import Text

console = Console()


# ---------------------------------------------------------------------------
# Agent events — the universal currency between backends and the renderer.
# ---------------------------------------------------------------------------

class EventKind(Enum):
    START = auto()          # agent session started
    TEXT = auto()           # assistant produced text
    TOOL_USE = auto()       # assistant invoked a tool
    SUBAGENT_START = auto() # sub-agent dispatched
    SUBAGENT_STOP = auto()  # sub-agent returned
    RETRY = auto()          # transient error, retrying after backoff
    RESULT = auto()         # session finished (success or error)
    ERROR = auto()          # unrecoverable crash


@dataclass
class AgentEvent:
    kind: EventKind
    label: str                          # human-visible agent name (e.g. "Formalizer")
    provider: str = ""                  # "claude" or "openai"
    model: str = ""                     # "opus", "o3", etc.
    turn: int = 0
    text: str = ""
    tool_name: str = ""
    tool_detail: str = ""
    subagent_name: str = ""
    is_error: bool = False
    num_turns: int = 0
    cost: str = ""
    extra: dict[str, Any] = field(default_factory=dict)


# ---------------------------------------------------------------------------
# Style registry — color, model badge, short role per agent label.
# ---------------------------------------------------------------------------

AGENT_STYLES: dict[str, tuple[str, str, str]] = {
    # label → (border color, default model badge, role)
    "Coordinator":            ("bright_magenta", "opus",   "Orchestrates agents, updates strategy"),
    "Formalizer":             ("bright_cyan",    "opus",   "Writes & compiles Lean 4 proofs"),
    "Scout":                  ("bright_green",   "sonnet", "Searches papers & Mathlib"),
    "Attack (analytic)":      ("bright_red",     "opus",   "Bombieri–Vinogradov / equidistribution"),
    "Attack (algebraic)":     ("bright_red",     "opus",   "SubgroupEscape + Mixing"),
    "Attack (combinatorial)": ("bright_red",     "opus",   "DivisorWalkHypothesis / pumping"),
    "Attack (dynamicalsystem)": ("yellow",       "opus",   "Dynamical systems / Weak Ergodicity"),
    "Paper Writer":           ("bright_blue",    "sonnet", "Maintains paper/ (main.tex + sections)"),
    "Transcriber":            ("bright_white",   "opus",   "Transcribes book pages to markdown"),
    "Stylist":                ("bright_yellow",  "opus",   "Proof improvement & Mathlib alignment"),
}


def style_for(label: str) -> tuple[str, str, str]:
    """Return (color, model_badge, role) for an agent label."""
    return AGENT_STYLES.get(label, ("white", "?", ""))


# ---------------------------------------------------------------------------
# Tool-detail extraction (shared between backends for uniform display).
# ---------------------------------------------------------------------------

def _tool_detail(tool_name: str, inp: dict[str, Any]) -> str:
    """Extract a short human-readable detail from a tool invocation."""
    if tool_name == "Bash":
        return inp.get("command", "")[:80]
    if tool_name in ("Read", "Write", "Edit"):
        return inp.get("file_path", "")
    if tool_name in ("Grep", "Glob"):
        return inp.get("pattern", "")
    if tool_name == "Task":
        return inp.get("description", "")
    if tool_name in ("WebSearch", "WebFetch"):
        return inp.get("query", inp.get("url", ""))[:60]
    return ""


# ---------------------------------------------------------------------------
# Render functions — consume AgentEvents, produce rich console output.
# ---------------------------------------------------------------------------

def render_event(event: AgentEvent) -> None:
    """Render a single AgentEvent to the console."""
    color, default_model, _role = style_for(event.label)
    model_badge = event.model or default_model
    provider_tag = f"{event.provider}:" if event.provider else ""
    title_badge = f"[{provider_tag}{model_badge}]"

    match event.kind:
        case EventKind.START:
            console.print(Panel(
                Text("Starting...", style="dim"),
                title=f" {event.label} {title_badge} ",
                border_style=color,
                expand=False,
            ))

        case EventKind.TEXT:
            console.print(Panel(
                Markdown(event.text),
                title=f" {event.label} · turn {event.turn} ",
                title_align="left",
                border_style=color,
                padding=(0, 1),
            ))

        case EventKind.TOOL_USE:
            # escape(): tool details are arbitrary text (shell commands,
            # regexes). Unescaped `[...]` fragments parse as rich markup
            # tags and a bad one (e.g. `[/\w]`) raises MarkupError,
            # crashing the whole streaming loop mid-session.
            detail = event.tool_detail or _tool_detail(event.tool_name, event.extra)
            console.print(
                f"  [dim {color}]▸ {escape(event.tool_name)}[/] "
                f"[dim]{escape(detail)}[/]"
            )

        case EventKind.SUBAGENT_START:
            console.print(
                f"  [bold {color}]◆ Dispatching → {escape(event.subagent_name)}[/]"
            )

        case EventKind.SUBAGENT_STOP:
            console.print(
                f"  [bold {color}]◇ {escape(event.subagent_name)} returned[/]"
            )

        case EventKind.RETRY:
            console.print(
                f"  [bold yellow]⟳ {escape(event.text)}[/]"
            )

        case EventKind.RESULT:
            status_style = "bold red" if event.is_error else "bold green"
            status_text = "ERROR" if event.is_error else "DONE"
            summary = Table.grid(padding=(0, 2))
            summary.add_row(
                Text(status_text, style=status_style),
                Text(f"{event.num_turns} turns", style="dim"),
                Text(event.cost, style="bold yellow"),
            )
            console.print(Panel(
                summary,
                title=f" {event.label} ",
                border_style="red" if event.is_error else "green",
                expand=False,
            ))

        case EventKind.ERROR:
            console.print(Panel(
                Text(event.text, style="red"),
                title=f" {event.label} CRASHED ",
                border_style="bold red",
            ))

    # Blank line after RESULT/ERROR for visual separation
    if event.kind in (EventKind.RESULT, EventKind.ERROR):
        console.print()


def render_status_table() -> None:
    """Print the agent roster table."""
    agents_table = Table(
        title="Agent Roster",
        show_header=True, header_style="bold",
        border_style="bright_magenta", expand=False,
    )
    agents_table.add_column("Agent", style="bold")
    agents_table.add_column("Model", justify="center")
    agents_table.add_column("Role")
    for label, (color, model, role) in AGENT_STYLES.items():
        badge = f"[bold magenta]{model}[/]" if model == "opus" else f"[blue]{model}[/]"
        agents_table.add_row(f"[{color}]{label}[/]", badge, f"[dim]{role}[/]")
    console.print(agents_table)
    console.print()
