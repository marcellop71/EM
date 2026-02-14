# Agent Swarm Framework

A multi-agent system built on the [Claude Agent SDK](https://github.com/anthropics/claude-agent-sdk-python) that autonomously explores proof strategies, searches literature, writes Lean code, maintains the paper, and evolves the EM formalization.

## Prerequisites

- Python 3.13+ (via `.venv`)
- `claude-agent-sdk` v0.1.37+ (already installed in `.venv`)
- A valid Anthropic API key (set `ANTHROPIC_API_KEY` in your environment)
- `lake` on `PATH` (for Lean builds)
- `pdflatex` on `PATH` (for paper compilation, optional)

## Quick Start

```bash
# From the project root
source .venv/bin/activate

# Check current proof status
python -m agents status

# Let the coordinator decide what to do
python -m agents coordinate

# Or run a specific agent directly
python -m agents attack --vector analytic
```

## Commands

### `status` — View current state

Prints the contents of all three state files (progress, strategy log, findings). No API calls, no cost.

```bash
python -m agents status
```

### `coordinate` — Run the coordinator

The coordinator (Opus) reads the current state, picks the most promising action, dispatches specialist agents, evaluates results, updates state files, and evolves agent prompts. This is the primary entry point for autonomous exploration.

```bash
# Open-ended: coordinator chooses what to do
python -m agents coordinate

# Directed: coordinator pursues a specific goal
python -m agents coordinate --goal "formalize PositiveEscapeDensity reduction chain"
```

The coordinator has access to eight subagents and dispatches them as needed. It runs for up to 30 turns. Budget cap: $50 per session. Use `--no-paper` to exclude the paper-writer (useful when running the paper agent in parallel).

```bash
python -m agents coordinate --goal-file goals/next.md --no-paper
```

### `formalize` — Write Lean code

Launches the formalizer (Sonnet) with a specific goal. The agent reads existing files, writes or modifies Lean code, and runs `lake build` to verify. Up to 20 turns, $25 budget cap.

```bash
python -m agents formalize --goal "add §31: DecorrelationHypothesis and PED reduction"
python -m agents formalize --goal-file goals/formalize.md
```

### `scout` — Search literature

Launches the literature scout (Opus) to find relevant papers and Mathlib lemmas. Up to 20 turns, $25 budget cap. Results are appended to `agents/state/findings.md`.

```bash
python -m agents scout --topic "partial sums in cyclic groups Stinson"
python -m agents scout --topic "Kummer theory cyclotomic extensions Chebotarev"
```

### `attack` — Explore an attack vector

Launches a specialist agent (Opus) focused on one of four attack vectors. Up to 20 turns, $25 budget cap.

```bash
python -m agents attack --vector analytic       # Bombieri-Vinogradov / character sums / PED
python -m agents attack --vector algebraic      # SubgroupEscape + Mixing + Kummer theory
python -m agents attack --vector combinatorial  # DivisorWalkHypothesis + pumping
python -m agents attack --vector information    # Kolmogorov complexity / oracle impossibility
```

### `paper` — Update the LaTeX paper

Launches the paper-writer (Opus) to update `docs/paper.tex` to reflect new Lean results. Reads the Lean source files for exact theorem names and line numbers, then makes targeted edits and compiles with `pdflatex`. Up to 20 turns, $25 budget cap.

```bash
python -m agents paper
python -m agents paper --goal "update §7 with new large sieve results"
python -m agents paper --goal-file goals/paper_focus.md
```

### `transcribe` — Transcribe book pages

Launches the transcriber (Opus) to convert book pages (images or PDF) into faithful markdown with LaTeX math. Produces a single output file preserving the original text, notation, and structure. Up to 20 turns, $25 budget cap.

```bash
python -m agents transcribe page1.png page2.png page3.png -o docs/transcripts/ch7.md
python -m agents transcribe book.pdf -o docs/transcripts/ch7.md
```

### `send` — Message the running coordinator

Writes a timestamped message to `agents/state/inbox.md`, which the coordinator checks after each sub-agent returns. Use this to steer a running coordinator session from another terminal.

```bash
python -m agents send "focus on the analytic route next"
```

## Architecture

```
coordinator (Opus, 30 turns, $50 cap)
├── lean-formalizer (Sonnet)        — writes Lean code, runs lake build
├── literature-scout (Opus)         — searches papers and Mathlib
├── attack-analytic (Opus)          — character sums, PED, equidistribution
├── attack-algebraic (Opus)         — SE + Mixing, Kummer theory
├── attack-combinatorial (Opus)     — DWH, pumping, additive combinatorics
├── attack-information (Opus)       — Kolmogorov complexity, oracle impossibility
├── paper-writer (Opus)             — maintains docs/paper.tex
└── transcriber (Opus)              — book page images → markdown/LaTeX
```

Each agent is defined as an `AgentDefinition` with its own system prompt, tool access, and model choice. The coordinator dispatches them as subagents via the SDK's `agents` parameter. Each CLI command can also run agents directly, bypassing the coordinator.

### Model Selection

| Agent | Model | Rationale |
|-------|-------|-----------|
| Coordinator | Opus | Strategic reasoning, multi-step planning |
| Formalizer | Sonnet | Fast iteration on compilation cycles |
| Scout | Opus | Deep literature analysis |
| Paper writer | Opus | Accurate LaTeX editing with full context |
| Attack agents | Opus | Deep mathematical reasoning |
| Transcriber | Opus | Faithful multi-page transcription (images + PDF) |

### Tool Access

| Agent | Tools |
|-------|-------|
| Coordinator | Read, Edit, Write, Glob, Grep, Bash, Task, WebSearch, WebFetch |
| Formalizer | Read, Edit, Write, Bash, Glob, Grep |
| Scout | WebSearch, WebFetch, Read, Write, Edit, Glob, Grep |
| Paper writer | Read, Edit, Write, Bash, Glob, Grep |
| Attack agents | Read, Write, Edit, Glob, Grep, WebSearch, WebFetch |
| Transcriber | Read, Write, Edit, Glob, Grep |

The formalizer and paper writer run shell commands via Bash (`lake build`, `pdflatex`). No custom MCP server is used.

> **Note:** SDK MCP servers (`create_sdk_mcp_server`) are broken in
> `claude-agent-sdk` 0.1.37 + Claude Code 2.1.45 (transport crash). The
> MCP server code is kept in `agents/tools/lean_mcp.py` for when this is
> fixed, but is not currently wired in.

## Self-Evolving Prompts

Agent prompts are **living documents** that evolve after each coordinator session. The coordinator's final step is to update `agents/prompts/*.md` to reflect what it learned:

- **Remove** questions and directions confirmed as dead ends
- **Add** new promising directions, lemma targets, and Mathlib discoveries
- **Update** infrastructure sections when new theorems are formalized

This prevents agents from wasting turns rediscovering settled territory. Each session starts from the frontier.

## State Files

All state is stored as git-tracked markdown in `agents/state/`. Human-readable, diffable, persistent across sessions.

| File | Purpose | Updated by |
|------|---------|------------|
| `progress.md` | Current proof status, open hypotheses, attack vector assessment | Coordinator |
| `strategy_log.md` | Timestamped log of attempts, outcomes, and dead ends | Coordinator |
| `findings.md` | Literature survey results (papers, Mathlib lemmas) | Scout |

The state files include a **Guiding Principle** section and a **Dead Ends** section to prevent agents from repeating failed strategies.

## Prompt Files

Each agent's system prompt lives in `agents/prompts/*.md`. Edit these to adjust agent behavior without touching Python code.

| File | Agent | Key content |
|------|-------|-------------|
| `coordinator.md` | Coordinator | Decision framework, prompt evolution instructions |
| `formalizer.md` | Formalizer | Lean conventions, session-specific technical notes |
| `scout.md` | Scout | Search strategy, incremental writing instructions |
| `attack_analytic.md` | Analytic | ComplexCharSumBound, PED, Kummer theory status |
| `attack_algebraic.md` | Algebraic | Dead ends, Kummer route, escape density |
| `attack_combinatorial.md` | Combinatorial | Dead ends (confirmed), remaining directions |
| `attack_information.md` | Information | Route assessment, remaining value |
| `paper.md` | Paper writer | LaTeX conventions, paper structure, `\lean{}` links |
| `transcriber.md` | Transcriber | Faithfulness rules, LaTeX math conventions |

## Directory Layout

```
agents/
├── __init__.py
├── __main__.py                  # python -m agents entrypoint
├── cli.py                       # argparse CLI (9 subcommands)
├── coordinator.py               # Agent definitions + runner functions
├── config.py                    # Path constants
├── tools/
│   ├── __init__.py
│   └── lean_mcp.py              # MCP server (kept for future use, not wired in)
├── prompts/
│   ├── coordinator.md
│   ├── formalizer.md
│   ├── scout.md
│   ├── attack_analytic.md
│   ├── attack_algebraic.md
│   ├── attack_combinatorial.md
│   ├── attack_information.md
│   ├── paper.md
│   └── transcriber.md
└── state/
    ├── progress.md              # Current proof status
    ├── strategy_log.md          # Attempt history + dead ends
    ├── findings.md              # Literature results
    └── inbox.md                 # Messages from `send` command
```

## Typical Workflows

### Daily exploration session

```bash
# 1. Check where things stand
python -m agents status

# 2. Let the coordinator decide what to do
python -m agents coordinate

# 3. Review what changed
git diff agents/state/
git diff agents/prompts/
git diff docs/paper.tex
```

### Targeted formalization

```bash
# Formalize a specific lemma
python -m agents formalize --goal "prove cofinal_orbit_iterate in EquidistOrbitAnalysis.lean"

# Update the paper to reflect the new result
python -m agents paper
```

### Strategic analysis

```bash
# Deep-dive into the most promising vector
python -m agents attack --vector analytic

# Search for relevant literature
python -m agents scout --topic "character sum cancellation partial products cyclic groups"
```

## Budget and Cost

| Command | Budget cap | Typical cost | Duration |
|---------|-----------|-------------|----------|
| `status` | $0 | $0 | instant |
| `send` | $0 | $0 | instant |
| `scout` | $25 | $0.50-2.00 | 2-5 min |
| `formalize` | $25 | $0.50-3.00 | 3-15 min |
| `attack` | $25 | $1.00-5.00 | 3-15 min |
| `paper` | $25 | $0.50-2.00 | 2-5 min |
| `transcribe` | $25 | $1.00-5.00 | 3-10 min |
| `coordinate` | $50 | $3.00-15.00 | 5-30 min |

Budget caps are defined in `coordinator.py` (`_BUDGET_COORDINATOR = 50.0`, `_BUDGET_DIRECT = 25.0`). The JSON message buffer is set to 50MB (`_MAX_BUF`).

## Permissions

Agents run as non-interactive subprocesses — there is no terminal to click "approve". Each agent has an `allowed_tools` list that pre-approves the tools it needs. Any tool not in the list is silently denied in headless mode.

Direct runners (scout, formalizer, attack, paper) do NOT have `Task` — only the coordinator can dispatch sub-agents. This prevents agents from spawning expensive parallel sessions.

## Critical Constraint

All agents are instructed: **NO COMPUTATION, ONLY PROOF.** Agents must not compute sequence values, verify primality, use `decide`/`native_decide` on large numbers, or propose "calculate and verify" approaches. The conjecture is about ALL primes — only abstract proof strategies are acceptable. This rule is enforced at five levels: system prompts, agent descriptions, runtime prompts, state file headers, and findings annotations.

## Extending the Framework

### Adding a new agent

1. Create a prompt file in `agents/prompts/new_agent.md`
2. Add an `AgentDefinition` in `_build_agents()` in `coordinator.py`
3. Add a direct runner function (e.g., `run_new_agent()`) in `coordinator.py`
4. Add a CLI subcommand in `cli.py`
5. Add the agent to the coordinator prompt (`coordinator.md`)
