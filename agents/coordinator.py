"""Main orchestration logic for the agent swarm."""

import asyncio
import sys
import json
import os
from datetime import datetime
from pathlib import Path

from claude_agent_sdk import AgentDefinition

from rich.console import Console
from rich.markdown import Markdown
from rich.panel import Panel

from .config import CLAUDE_MD, PROMPTS_DIR, ROOT, STATE_DIR
from .rendering import (
    AgentEvent,
    EventKind,
    console,
    render_event,
    render_status_table,
    style_for,
    AGENT_STYLES,
)
from .providers import AgentSpec, get_backend
from .providers.claude_backend import ClaudeBackend


# Tools available to each direct-runner role.  These lists serve double duty:
#   • `tools`         — restricts which tools the agent CAN see
#   • `allowed_tools` — pre-approves them (no interactive prompt needed)
#
# IMPORTANT: Do NOT give Task to direct runners (scout, formalizer, attack).
# Only the coordinator dispatches sub-agents.  A scout with Task will spawn
# 7+ parallel Claude Code sessions at ~$10 each.
_TOOLS_COORDINATOR = [
    "Read", "Edit", "Write", "Glob", "Grep", "Bash", "Task",
    "WebSearch", "WebFetch",
]
_TOOLS_FORMALIZER = [
    "Read", "Edit", "Write", "Bash", "Glob", "Grep",
]
_TOOLS_SCOUT = [
    "WebSearch", "WebFetch", "Read", "Write", "Edit", "Glob", "Grep",
]
_TOOLS_ATTACK = [
    "Read", "Write", "Edit", "Glob", "Grep", "WebSearch", "WebFetch",
]
_TOOLS_TRANSCRIBER = [
    "Read", "Write", "Edit", "Glob", "Grep",
]

# Per-session budget caps (USD).
_BUDGET_COORDINATOR = 50.0
_BUDGET_DIRECT = 25.0


def _read(path: Path) -> str:
    if path.exists():
        return path.read_text()
    return ""


def _load_prompt(name: str) -> str:
    return (PROMPTS_DIR / f"{name}.md").read_text()


# ---------------------------------------------------------------------------
# Agent definitions (used as SUB-agents by the coordinator via Claude SDK)
# ---------------------------------------------------------------------------

def _build_agents() -> dict[str, AgentDefinition]:
    return {
        "lean-formalizer": AgentDefinition(
            description=(
                "Writes abstract Lean 4 proofs. Give it a specific lemma to formalize. "
                "NEVER ask it to compute sequence values or verify primality."
            ),
            prompt=_load_prompt("formalizer"),
            tools=["Read", "Edit", "Write", "Bash", "Glob", "Grep"],
            model="opus",
        ),
        "literature-scout": AgentDefinition(
            description=(
                "Searches for relevant math papers and Mathlib lemmas. "
                "Focus on proof techniques, not computational data."
            ),
            prompt=_load_prompt("scout"),
            tools=["WebSearch", "WebFetch", "Read", "Write", "Edit", "Glob", "Grep"],
            model="sonnet",
        ),
        "attack-analytic": AgentDefinition(
            description=(
                "Proposes abstract proof strategies for DynamicalHitting via "
                "Bombieri-Vinogradov / equidistribution. No computation."
            ),
            prompt=_load_prompt("attack_analytic"),
            tools=["Read", "Glob", "Grep", "WebSearch", "WebFetch"],
            model="opus",
        ),
        "attack-algebraic": AgentDefinition(
            description=(
                "Proposes abstract proof strategies via SubgroupEscape + Mixing. "
                "No computation."
            ),
            prompt=_load_prompt("attack_algebraic"),
            tools=["Read", "Glob", "Grep", "WebSearch", "WebFetch"],
            model="opus",
        ),
        "attack-combinatorial": AgentDefinition(
            description=(
                "Proposes abstract proof strategies via DivisorWalkHypothesis and "
                "pumping. No computation."
            ),
            prompt=_load_prompt("attack_combinatorial"),
            tools=["Read", "Glob", "Grep", "WebSearch", "WebFetch"],
            model="opus",
        ),
        "attack-dynamicalsystem": AgentDefinition(
            description=(
                "Proposes dynamical systems / ergodic approaches to Weak Ergodicity: "
                "population transfer, CRT dynamics, non-autonomous walks. No computation."
            ),
            prompt=_load_prompt("attack_dynamicalsystem"),
            tools=["Read", "Glob", "Grep", "WebSearch", "WebFetch"],
            model="opus",
        ),
        "paper-writer": AgentDefinition(
            description=(
                "Updates the paper in paper/ (main.tex + section files, lualatex) to reflect new Lean theorems. "
                "Dispatch AFTER the formalizer lands new code. Reads Lean files for exact details."
            ),
            prompt=_load_prompt("paper"),
            tools=["Read", "Edit", "Write", "Bash", "Glob", "Grep"],
            model="sonnet",
        ),
        "code-stylist": AgentDefinition(
            description=(
                "Deep code quality: simplifies proofs, finds better Mathlib lemmas, "
                "reorganizes structure, enforces Mathlib style. Give it a specific "
                "file or glob pattern."
            ),
            prompt=_load_prompt("stylist"),
            tools=["Read", "Edit", "Write", "Bash", "Glob", "Grep"],
            model="opus",
        ),
    }


# ---------------------------------------------------------------------------
# Streaming helper — runs any backend and renders events.
# ---------------------------------------------------------------------------

async def _stream_with_backend(
    spec: AgentSpec,
    prompt: str,
    *,
    agents: dict[str, AgentDefinition] | None = None,
) -> None:
    """Run an agent via its provider backend, rendering events to the console."""
    backend = get_backend(spec.provider)

    try:
        if isinstance(backend, ClaudeBackend):
            event_iter = backend.run(spec, prompt, agents=agents)
        else:
            event_iter = backend.run(spec, prompt)

        async for event in event_iter:
            try:
                render_event(event)
            except Exception as render_err:
                # Rendering is cosmetic — never let a display error kill
                # the agent session (a rich MarkupError once aborted a
                # coordinator run mid-edit).
                console.print(
                    f"[render error: {type(render_err).__name__}] "
                    f"{event.kind.name} {event.tool_name or ''}"
                )
    except BaseException:
        import traceback
        render_event(AgentEvent(
            kind=EventKind.ERROR,
            label=spec.label,
            provider=spec.provider,
            model=spec.model_name,
            text=traceback.format_exc(),
        ))


# Legacy wrapper — preserves the old _stream() call signature for code that
# builds ClaudeAgentOptions directly.  Used only during the transition.
async def _stream_legacy(
    spec: AgentSpec,
    prompt: str,
    *,
    agents: dict[str, AgentDefinition] | None = None,
) -> None:
    await _stream_with_backend(spec, prompt, agents=agents)


# ---------------------------------------------------------------------------
# Coordinator
# ---------------------------------------------------------------------------

async def run_coordinator(
    goal: str | None = None,
    *,
    no_paper: bool = False,
    model: str = "claude:opus",
    qwen_agents: tuple[str, ...] = (),
    dgx_agents: dict[str, str] | None = None,
) -> None:
    """Launch the coordinator agent.

    `dgx_agents` maps specialist name → provider-qualified DGX model
    (e.g. {"lean-formalizer": "dgx:ornith", "attack-analytic": "dgx:qwen"}).
    Listed specialists are dispatched via Bash + direct-runner against
    the DGX endpoints instead of via the Claude Agent SDK's Task tool.
    The coordinator itself stays on Anthropic (the `model` param) — it
    is the one issuing instructions; the DGX models execute them.
    Listed agents are REMOVED from the SDK registry so the coordinator
    can't Task-dispatch them (the Claude SDK doesn't speak dgx:/qwen:
    prefixes).

    `qwen_agents` (legacy) is a tuple of specialist names all routed to
    `dgx:qwen`; merged into `dgx_agents`.
    """
    dgx_agents = dict(dgx_agents or {})
    for name in qwen_agents:
        dgx_agents.setdefault(name, "dgx:qwen")

    # Is the COORDINATOR itself on a DGX model? Then it dispatches sub-agents
    # through the QwenBackend's own `Task` handler (which shells out to
    # `run-openai`), routed per-agent via the DGX_AGENT_MODELS env map — so we
    # do NOT strip agents or force Bash-routing (that path is for a Claude
    # coordinator that can't speak dgx: prefixes).
    _coord_provider = (model.split(":", 1)[0] if ":" in model else model)
    coordinator_on_dgx = _coord_provider in ("dgx", "qwen")
    if coordinator_on_dgx:
        _ALL_SPECIALISTS = (
            "code-stylist", "attack-combinatorial", "attack-algebraic",
            "attack-analytic", "attack-dynamicalsystem", "literature-scout",
            "lean-formalizer", "paper-writer",
        )
        # Every specialist gets a model: explicit --dgx-agents wins, the rest
        # default to the coordinator's own DGX model.
        _coord_model = model if ":" in model else f"dgx:{model}"
        task_model_map = {n: dgx_agents.get(n, _coord_model) for n in _ALL_SPECIALISTS}
        task_model_map.update(dgx_agents)
        os.environ["DGX_AGENT_MODELS"] = json.dumps(task_model_map)
        os.environ["DGX_TASK_DEFAULT_MODEL"] = _coord_model
    progress = _read(STATE_DIR / "progress.md")
    strategy_log = _read(STATE_DIR / "strategy_log.md")
    strategy_summary = _read(STATE_DIR / "strategy_log_summary.md")

    inbox_path = STATE_DIR / "inbox.md"
    inbox = _read(inbox_path)

    goal_section = f"\n\n## Current Goal\n\n{goal}" if goal else ""
    paper_note = (
        "\n\n**NOTE:** The paper-writer agent is running separately. "
        "Do NOT dispatch the paper-writer sub-agent this session."
        if no_paper else ""
    )
    inbox_section = (
        f"\n\n## Inbox (live instructions from operator)\n\n{inbox}"
        if inbox.strip() else ""
    )

    # Map specialist name → direct-runner invocation hint (with a {model}
    # slot), used when --dgx-agents routes them through Bash rather than Task.
    _DGX_BASH_HINTS = {
        "code-stylist":           f"{sys.executable} -m agents style --target EM/<file>.lean --model {{model}}",
        "attack-combinatorial":   f"{sys.executable} -m agents attack --vector combinatorial --model {{model}}",
        "attack-algebraic":       f"{sys.executable} -m agents attack --vector algebraic --model {{model}}",
        "attack-analytic":        f"{sys.executable} -m agents attack --vector analytic --model {{model}}",
        "attack-dynamicalsystem": f"{sys.executable} -m agents attack --vector dynamicalsystem --model {{model}}",
        "literature-scout":       f"{sys.executable} -m agents scout --topic <topic> --model {{model}}",
        "lean-formalizer":        f"{sys.executable} -m agents formalize --goal '<lemma + proof sketch>' --model {{model}}",
        "paper-writer":           f"{sys.executable} -m agents paper --goal '<focus area>' --model {{model}}",
    }
    qwen_section = ""
    if dgx_agents:
        lines = [
            "",
            "## Specialists routed to the DGX models — use Bash, NOT Task",
            "",
            "The following specialists are NOT available via the Task tool "
            "this session. To dispatch them, use the Bash tool with the "
            "direct-runner equivalent; each runs on the DGX model shown "
            "(endpoints in agents/config.py — `dgx:qwen` = Qwen3.5-122B on "
            "sglang:8000, `dgx:ornith` = Ornith-1.0-35B on llama.cpp:8001). "
            "You are the one issuing instructions; the DGX models execute "
            "them. Give them SELF-CONTAINED goals (file paths, exact lemma "
            "statements, proof sketches): they do not share your context.",
            "",
        ]
        for name, mdl in dgx_agents.items():
            tmpl = _DGX_BASH_HINTS.get(
                name, f"{sys.executable} -m agents <subcommand> --model {{model}}  # for {name}")
            lines.append(f"  - **{name}** (`{mdl}`) → `{tmpl.format(model=mdl)}`")
        lines.extend([
            "",
            "You may override the model per call (`--model dgx:qwen` or "
            "`--model dgx:ornith`) — e.g. use `dgx:qwen` (larger, 122B) for "
            "reasoning-heavy attacks and `dgx:ornith` (35B, native tool "
            "calls, faster) for mechanical Lean/style/transcription work — "
            "and you may run TWO direct-runners concurrently (one per DGX "
            "model) with `run_in_background`, since they occupy different "
            "GPUs/servers.",
            "",
            "Use Task tool ONLY for specialists not in this list. The "
            "direct-runner Bash invocations stream events to stdout — read "
            "them to evaluate the agent's result, just like Task tool outputs.",
            "",
            "If you forget and try Task on a DGX-routed agent, you'll get "
            "an `Unknown agent` error from the SDK. Fall back to the Bash "
            "form documented above.",
        ])
        qwen_section = "\n".join(lines)

    if coordinator_on_dgx:
        # A DGX-hosted coordinator dispatches specialists with the ordinary
        # Task tool; the QwenBackend routes each to the model below.
        rows = "\n".join(
            f"  - **{n}** -> `{m}`" for n, m in sorted(task_model_map.items()))
        qwen_section = (
            "\n## Dispatching specialists (you run on a DGX model)\n\n"
            "Use the **Task** tool normally: `Task(subagent_type=\"<name>\", "
            "prompt=\"<self-contained goal>\")`. Each specialist runs on the "
            "DGX model assigned below (larger `dgx:qwen` = Qwen3.5-122B for "
            "reasoning; faster `dgx:ornith` = Ornith-1.0-35B for mechanical "
            "Lean/style work); the two sit on different servers so independent "
            "Task calls can proceed in parallel.\n\n" + rows + "\n\n"
            "You do NOT share context with them: every Task prompt must be "
            "self-contained (exact file paths, precise lemma statements, proof "
            "sketch, and the acceptance check such as compiles under "
            "`lake env lean <file>`). You are Qwen — think carefully and keep "
            "the ABSOLUTE RULE (no computation) in force for yourself and them."
        )

    prompt = f"""You are the coordinator for the EM formalization agent swarm.

## Current State

### progress.md
{progress}

### strategy_log_summary.md (compressed history of all sessions)
{strategy_summary[-4000:] if len(strategy_summary) > 4000 else strategy_summary}

### strategy_log.md (recent sessions)
{strategy_log[-3000:] if len(strategy_log) > 3000 else strategy_log}
{goal_section}{paper_note}{inbox_section}{qwen_section}

## Instructions

Read the coordinator prompt carefully, then:
1. Assess the current state
2. Choose the most promising action
3. Dispatch specialist agents with specific goals
4. After each agent returns, evaluate results
5. Update strategy_log.md with outcomes
6. **FINAL STEP**: Update agent prompts in agents/prompts/ to reflect what you learned
   (remove dead ends, add new directions, update infrastructure sections)

**INBOX**: After each sub-agent returns, re-read `{inbox_path}` for new
instructions from the operator. If the file has content, follow those
instructions before choosing your next action. After handling a message,
clear the file by writing an empty string to it.

Write your strategy log updates to: {STATE_DIR / 'strategy_log.md'}
Write any progress updates to: {STATE_DIR / 'progress.md'}
Write any findings to: {STATE_DIR / 'findings.md'}
Update agent prompts at: {PROMPTS_DIR}/
Update public status (only if Lean code changed): {ROOT / 'docs' / 'status.md'}

Today's date: {datetime.now().strftime('%Y-%m-%d')}
"""

    agents = _build_agents()
    if no_paper:
        agents.pop("paper-writer", None)

    # Strip any agent the user routed to the DGX ONLY when the coordinator is
    # on Claude — the SDK can't dispatch provider-qualified models, so removing
    # them from the registry forces Bash-routing (documented in qwen_section).
    # A DGX coordinator keeps them: it dispatches via its own Task handler,
    # routed per-agent through DGX_AGENT_MODELS.
    if not coordinator_on_dgx:
        for name in dgx_agents:
            if name in agents:
                del agents[name]

    spec = AgentSpec(
        name="coordinator",
        label="Coordinator",
        model=model,
        system_prompt=_load_prompt("coordinator"),
        tools=_TOOLS_COORDINATOR,
        max_turns=30,
        budget=_BUDGET_COORDINATOR,
    )

    await _stream_with_backend(spec, prompt, agents=agents)


# ---------------------------------------------------------------------------
# Direct agent runners
# ---------------------------------------------------------------------------

async def run_formalizer(goal: str, *, model: str = "claude:opus") -> None:
    """Launch the formalizer agent directly."""
    spec = AgentSpec(
        name="formalizer",
        label="Formalizer",
        model=model,
        system_prompt=_load_prompt("formalizer"),
        tools=_TOOLS_FORMALIZER,
        max_turns=40,
        budget=_BUDGET_DIRECT,
    )

    strategy_log_path = STATE_DIR / "strategy_log.md"
    strategy_log = _read(strategy_log_path)

    prompt = f"""## Goal

{goal}

## Recent Strategy Log (learn from prior sessions)

{strategy_log[-1500:] if len(strategy_log) > 1500 else strategy_log}

## URGENT: WRITE CODE EARLY

You have 40 turns. Spend at most 5 turns reading context. START WRITING LEAN CODE BY TURN 5.
Use the technical notes in your system prompt — they have all the Mathlib API details you need.
Do NOT re-read Mathlib source files that are already documented in your prompt.

## CRITICAL CONSTRAINT

Do NOT compute sequence values, verify primality, or add concrete `mullin_for_*` theorems.
Do NOT use `decide`/`native_decide`/`norm_num` on large numbers.
Write ONLY abstract mathematical proofs. This project proves a theorem for ALL primes, not one at a time.

## Project Context

{_read(CLAUDE_MD)[:4000]}

Work in the project at {ROOT}. Follow the conventions from the formalizer prompt.
Always run `lake build` via Bash after making changes.

## Session Logging

When you finish, append a brief session entry to `{strategy_log_path}` using Edit/Write:

```
## Session {{N}} — {datetime.now().strftime('%Y-%m-%d')} — {{1-line summary}}
**Role**: formalizer
- What you proved/attempted (with file:line references)
- What remains open
- Build status: green/red
```

Read the last few lines of `{strategy_log_path}` to determine the next session number N.
"""

    await _stream_with_backend(spec, prompt)


async def run_scout(topic: str, *, model: str = "claude:sonnet") -> None:
    """Launch the literature scout directly."""
    findings_path = STATE_DIR / "findings.md"
    existing_findings = _read(findings_path)

    spec = AgentSpec(
        name="scout",
        label="Scout",
        model=model,
        system_prompt=_load_prompt("scout"),
        tools=_TOOLS_SCOUT,
        max_turns=20,
        budget=_BUDGET_DIRECT,
    )

    strategy_log_path = STATE_DIR / "strategy_log.md"

    prompt = f"""## Topic

{topic}

## Existing Findings

{existing_findings[:2000]}

## Instructions

Search for papers, Mathlib lemmas, and computational data relevant to: {topic}

Do your own searches directly — do NOT delegate to sub-agents.

IMPORTANT: After every 2-3 searches, IMMEDIATELY use the Edit or Write tool to
append your findings so far to: {findings_path}
Do NOT wait until the end — you will run out of turns. Write early, write often.

## Session Logging

When you finish, append a brief session entry to `{strategy_log_path}`:

```
## Session {{N}} — {datetime.now().strftime('%Y-%m-%d')} — {{1-line summary}}
**Role**: scout
- What you searched for and found
- Key references with relevance assessment
```

Read the last few lines of `{strategy_log_path}` to determine the next session number N.

## Project Context (abbreviated)

The project formalizes Mullin's Conjecture in Lean 4 / Mathlib v4.27.0.
Key open hypothesis: DynamicalHitting (EquidistBootstrap.lean).
Three attack vectors: analytic (Bombieri-Vinogradov), algebraic (SE+Mixing), combinatorial (DWH).
"""

    await _stream_with_backend(spec, prompt)


async def run_attack(
    vector: str, *, goal: str | None = None, model: str = "claude:opus"
) -> None:
    """Launch an attack agent directly."""
    valid = {"analytic", "algebraic", "combinatorial", "dynamicalsystem"}
    if vector not in valid:
        print(f"Unknown attack vector: {vector}. Choose from: {', '.join(sorted(valid))}")
        return

    prompt_name = f"attack_{vector}"
    progress = _read(STATE_DIR / "progress.md")
    findings_path = STATE_DIR / "findings.md"
    existing_findings = _read(findings_path)
    strategy_log_path = STATE_DIR / "strategy_log.md"
    strategy_log = _read(strategy_log_path)

    spec = AgentSpec(
        name=f"attack-{vector}",
        label=f"Attack ({vector})",
        model=model,
        system_prompt=_load_prompt(prompt_name),
        tools=_TOOLS_ATTACK,
        max_turns=30,
        budget=_BUDGET_DIRECT,
    )

    catalog_path = ROOT / "agents" / "catalogs" / f"{vector}_techniques.md"
    dead_ends_path = ROOT / "EM" / "Meta" / "DeadEnds.lean"

    goal_section = f"\n\n## Focus\n\n{goal}" if goal else ""

    prompt = f"""## Attack Vector: {vector}
{goal_section}

## CRITICAL CONSTRAINT

Do NOT compute sequence values, verify primality, or propose concrete calculations.
Do NOT use `decide`/`native_decide`/`norm_num` on large numbers.
Propose ONLY abstract mathematical proof strategies. The conjecture is about ALL primes.

## FIRST STEP: Read Your Technique Catalog

**Read `{catalog_path}` BEFORE proposing anything.** It contains:
- All known techniques with EM status (PROVED/DEAD/OPEN/MATHLIB BLOCKED)
- Decomposition and generalization strategies with UNTRIED items flagged
- Track record of past proposals (success/failure patterns)
- The only genuinely open frontier directions

Also consult `{dead_ends_path}` for the full dead ends catalog (138+ entries,
categories + weak-MC revival scores; 13 have formal Lean witnesses).

## Current Progress

{progress}

## Recent Strategy Log (cross-agent context)

{strategy_log[-2000:] if len(strategy_log) > 2000 else strategy_log}

## Recent Findings

{existing_findings[-2000:] if len(existing_findings) > 2000 else existing_findings}

## Instructions

1. Read your technique catalog (`{catalog_path}`) first
2. Read the relevant Lean files for the {vector} attack vector
3. Analyze the current state and propose concrete next steps
4. Focus on identifying the minimal abstract mathematical input needed to make progress

Do your own analysis directly — do NOT delegate to sub-agents.

IMPORTANT: After your analysis, use the Edit or Write tool to:
- Append findings and recommendations to: {findings_path}
- Append a brief session summary (date, vector, key conclusions, feasibility scores) to: {strategy_log_path}
- **Update your technique catalog** (`{catalog_path}`): add new track record entries, update technique status, flag new UNTRIED combinations
Do NOT wait until the end — you will run out of turns. Write early, write often.

Be specific about:
1. What abstract lemma statements would bridge the gap
2. What mathematical obstacles exist
3. What literature might help
4. Feasibility assessment (1-10 scale)

Project root: {ROOT}
Lean source: {ROOT / 'EM'}
"""

    await _stream_with_backend(spec, prompt)


async def run_paper(goal: str | None = None, *, model: str = "claude:opus") -> None:
    """Launch the paper-writer agent to update the paper in paper/."""
    progress = _read(STATE_DIR / "progress.md")
    strategy_log = _read(STATE_DIR / "strategy_log.md")

    spec = AgentSpec(
        name="paper-writer",
        label="Paper Writer",
        model=model,
        system_prompt=_load_prompt("paper"),
        tools=_TOOLS_FORMALIZER,  # same tools: Read, Edit, Write, Bash, Glob, Grep
        max_turns=20,
        budget=_BUDGET_DIRECT,
    )

    goal_section = f"\n\n## Focus\n\n{goal}" if goal else ""

    strategy_log_path = STATE_DIR / "strategy_log.md"

    prompt = f"""## Task: Update the paper in paper/
{goal_section}

## Current Proof Progress

{progress}

## Recent Strategy Log (what changed)

{strategy_log[-3000:] if len(strategy_log) > 3000 else strategy_log}

## Instructions

The paper lives in `paper/`: `main.tex` inputs the section files
(abstract, introduction, background, the_residue_walk,
the_character_sum_reduction, the_ensemble_reduction, why_its_hard,
variants, appendix, the_Lean_formalization, bibliography).
Read the relevant section file(s), then read the corresponding Lean files
to get exact theorem names and file paths (Lean sources are organized in
subject subdirectories under EM/ — grep for the theorem name).
Update the paper to reflect any new results that aren't yet documented.
Keep the `\\lean{{EM/<dir>/<file>.lean}}{{name}}` links accurate.
After editing, compile with:
`cd {ROOT / 'paper'} && lualatex -interaction=nonstopmode main.tex`
(the paper uses fontspec — pdflatex will NOT work).

## Session Logging

When you finish, append a brief session entry to `{strategy_log_path}`:

```
## Session {{N}} — {datetime.now().strftime('%Y-%m-%d')} — {{1-line summary}}
**Role**: paper-writer
- Sections updated
- New results documented
```

Read the last few lines of `{strategy_log_path}` to determine the next session number N.

Project root: {ROOT}
Lean source: {ROOT / 'EM'}
"""

    await _stream_with_backend(spec, prompt)


async def run_stylist(target: str, *, model: str = "claude:opus") -> None:
    """Launch the code style agent on a specific file or pattern."""
    spec = AgentSpec(
        name="code-stylist",
        label="Stylist",
        model=model,
        system_prompt=_load_prompt("stylist"),
        tools=_TOOLS_FORMALIZER,
        max_turns=100,
        budget=_BUDGET_DIRECT,
    )

    strategy_log_path = STATE_DIR / "strategy_log.md"

    prompt = f"""## Target

{target}

## Instructions

Improve the target file(s): simplify proofs, find better Mathlib lemmas, reorganize
structure, and enforce Mathlib style. Follow the priority order in your system prompt
(proof improvement > reorganization > Mathlib alignment > documentation).

Search `.lake/packages/mathlib/Mathlib/` for existing lemmas that could replace
hand-rolled proofs. This is the highest-value improvement you can make.

**CRITICAL**: Run `lake build` after each batch of changes. Never leave the build broken.

## Session Logging

When you finish, append a brief session entry to `{strategy_log_path}`:

```
## Session {{N}} — {datetime.now().strftime('%Y-%m-%d')} — {{1-line summary}}
**Role**: stylist
- Files improved, lines saved
- Mathlib lemmas substituted
- Build status: green/red
```

Read the last few lines of `{strategy_log_path}` to determine the next session number N.

## Project Context (abbreviated)

{_read(CLAUDE_MD)[:3000]}

Project root: {ROOT}
Lean source: {ROOT / 'EM'}
"""

    await _stream_with_backend(spec, prompt)


async def run_transcriber(
    sources: list[str], output: str, *, model: str = "claude:opus",
) -> None:
    """Launch the transcriber agent to transcribe book pages (images or PDF)."""
    spec = AgentSpec(
        name="transcriber",
        label="Transcriber",
        model=model,
        system_prompt=_load_prompt("transcriber"),
        tools=_TOOLS_TRANSCRIBER,
        max_turns=40,
        budget=_BUDGET_DIRECT,
    )

    source_list = "\n".join(f"- `{src}`" for src in sources)
    prompt = f"""## Task: Transcribe book pages

## Source files (in order)

{source_list}

## Output

Write the transcript to: `{output}`

## Instructions

1. Read each source file in order using the Read tool
   - For images (PNG, JPG): read directly
   - For PDFs: use the `pages` parameter to read in chunks of up to 20 pages
2. Transcribe faithfully to markdown with LaTeX math
3. Write the complete transcript to the output file
4. Re-read sources and transcript to verify accuracy, fix any errors
"""

    await _stream_with_backend(spec, prompt)


# ---------------------------------------------------------------------------
# OpenAI direct runner (invoked via `python -m agents run-openai`)
# ---------------------------------------------------------------------------

async def run_openai_agent(
    agent: str,
    prompt: str,
    *,
    model: str = "openai:gpt-5.2",
) -> None:
    """Launch a single agent on the OpenAI backend.

    This is the entry point for `python -m agents run-openai --agent NAME`.
    The coordinator dispatches OpenAI agents by shelling out to this command.
    """
    # Map agent names to labels and tool sets
    _AGENT_CONFIG = {
        "lean-formalizer":    ("Formalizer",             _TOOLS_FORMALIZER),
        "literature-scout":   ("Scout",                  _TOOLS_SCOUT),
        "attack-analytic":    ("Attack (analytic)",      _TOOLS_ATTACK),
        "attack-algebraic":   ("Attack (algebraic)",     _TOOLS_ATTACK),
        "attack-combinatorial": ("Attack (combinatorial)", _TOOLS_ATTACK),
        "attack-dynamicalsystem": ("Attack (dynamicalsystem)", _TOOLS_ATTACK),
        "paper-writer":       ("Paper Writer",           _TOOLS_FORMALIZER),
        "transcriber":        ("Transcriber",            _TOOLS_TRANSCRIBER),
        "code-stylist":       ("Stylist",                _TOOLS_FORMALIZER),
    }

    label, tools = _AGENT_CONFIG.get(agent, (agent, _TOOLS_ATTACK))

    # Load system prompt if available
    prompt_map = {
        "lean-formalizer": "formalizer",
        "literature-scout": "scout",
        "attack-analytic": "attack_analytic",
        "attack-algebraic": "attack_algebraic",
        "attack-combinatorial": "attack_combinatorial",
        "attack-dynamicalsystem": "attack_dynamicalsystem",
        "paper-writer": "paper",
        "transcriber": "transcriber",
        "code-stylist": "stylist",
    }
    prompt_name = prompt_map.get(agent)
    system_prompt = _load_prompt(prompt_name) if prompt_name else ""

    spec = AgentSpec(
        name=agent,
        label=label,
        model=model,
        system_prompt=system_prompt,
        tools=tools,
        max_turns=20,
        budget=_BUDGET_DIRECT,
    )

    await _stream_with_backend(spec, prompt)


# ---------------------------------------------------------------------------
# Status display
# ---------------------------------------------------------------------------

async def print_status() -> None:
    """Print current state from state files with rich formatting."""
    progress = _read(STATE_DIR / "progress.md")
    strategy_log = _read(STATE_DIR / "strategy_log.md")
    findings = _read(STATE_DIR / "findings.md")

    render_status_table()

    if progress.strip():
        console.print(Panel(
            Markdown(progress),
            title=" Proof Progress ",
            border_style="bright_cyan",
        ))
    else:
        from rich.text import Text
        console.print(Panel(
            Text("No progress file found.", style="dim"),
            title=" Proof Progress ",
            border_style="dim",
        ))

    if strategy_log.strip():
        tail = strategy_log[-2000:] if len(strategy_log) > 2000 else strategy_log
        console.print(Panel(
            Markdown(tail),
            title=" Strategy Log (recent) ",
            border_style="bright_magenta",
        ))

    if findings.strip():
        tail = findings[-2000:] if len(findings) > 2000 else findings
        console.print(Panel(
            Markdown(tail),
            title=" Findings (recent) ",
            border_style="bright_green",
        ))
