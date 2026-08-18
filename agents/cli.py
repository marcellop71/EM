"""CLI entry point for the EM agent swarm."""

import argparse
import asyncio
import os
import sys

# The SDK launches Claude Code as a subprocess.  If we're already inside a
# Claude Code session (e.g. the user ran this from the CC terminal), the
# child process will refuse to start ("cannot be launched inside another
# Claude Code session").  Clearing this env var before any SDK import
# avoids the nesting check.
os.environ.pop("CLAUDECODE", None)


def main() -> None:
    parser = argparse.ArgumentParser(
        prog="agents",
        description="Multi-agent swarm for evolving the EM Lean formalization",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # coordinate
    p_coord = sub.add_parser("coordinate", help="Run the coordinator agent")
    p_coord.add_argument("--goal", type=str, default=None, help="Optional goal to pursue")
    p_coord.add_argument(
        "--goal-file", type=str, default=None,
        help="Path to a file containing the goal (overrides --goal)",
    )
    p_coord.add_argument(
        "--no-paper", action="store_true", default=False,
        help="Exclude paper-writer sub-agent (use when running paper agent in parallel)",
    )
    p_coord.add_argument(
        "--model", type=str, default="claude:opus",
        help="Provider-qualified model (e.g. claude:opus, claude:fable, openai:gpt-5.2, dgx:qwen, dgx:ornith)",
    )
    p_coord.add_argument(
        "--dgx-agents", type=str, default="",
        help=(
            "Route specialists to the DGX models. Comma-separated "
            "`name[=model]` entries; model defaults to --dgx-default-model. "
            "The coordinator itself stays on Claude (--model) and issues "
            "the instructions; listed specialists are removed from the SDK "
            "registry and Bash-routed to direct-runners on the DGX. "
            "Models: dgx:qwen (Qwen3.5-122B, sglang:8000), dgx:ornith "
            "(Ornith-1.0-35B, llama.cpp:8001). "
            "Examples: --dgx-agents all  |  --dgx-agents all=dgx:ornith  |  "
            "--dgx-agents lean-formalizer=dgx:ornith,attack-analytic=dgx:qwen,"
            "code-stylist=dgx:ornith. "
            "`all` expands to: code-stylist, attack-combinatorial, "
            "attack-algebraic, attack-analytic, attack-dynamicalsystem, "
            "literature-scout, lean-formalizer, paper-writer."
        ),
    )
    p_coord.add_argument(
        "--dgx-default-model", type=str, default="dgx:qwen",
        help="Model used for --dgx-agents entries without an explicit =model "
             "(default: dgx:qwen).",
    )
    p_coord.add_argument(
        "--dgx-split", action="store_true", default=False,
        help=(
            "Preset: route ALL specialists to the DGX with the recommended "
            "two-model split — reasoning-heavy roles (attack-*, "
            "literature-scout, paper-writer) on dgx:qwen, mechanical roles "
            "(lean-formalizer, code-stylist) on dgx:ornith. Explicit "
            "--dgx-agents entries override the preset per specialist."
        ),
    )
    p_coord.add_argument(
        "--qwen-agents", type=str, default="",
        help="LEGACY alias: comma-separated specialists routed to dgx:qwen "
             "(`all` allowed). Prefer --dgx-agents.",
    )
    p_coord.add_argument(
        "--dgx-ctx", type=int, default=None,
        help="Context window (tokens) for the DGX models this session — both "
             "are served at 65536 (the max). Sets DGX_CONTEXT_WINDOW for the "
             "coordinator AND every sub-agent it spawns. Lower it to leave "
             "headroom / speed up; do not exceed the served max_model_len or "
             "the endpoint 400s. Per-model override: QWEN_MAX_MODEL_LEN / "
             "ORNITH_MAX_MODEL_LEN env vars.",
    )
    p_coord.add_argument(
        "--dgx-max-tokens", type=int, default=None,
        help="Desired UPPER BOUND on completion tokens for DGX models (default "
             "4096). This is a ceiling, not a fixed reservation: the backend "
             "recomputes the per-request cap from the actual prompt size so "
             "input+output always fits the window — so even --dgx-max-tokens "
             "65536 is safe (you simply get less output room when the prompt is "
             "large). Raise it to allow longer completions when prompts are "
             "short.",
    )

    # formalize
    p_form = sub.add_parser("formalize", help="Run the formalizer agent directly")
    p_form.add_argument("--goal", type=str, default=None, help="What to formalize")
    p_form.add_argument(
        "--goal-file", type=str, default=None,
        help="Path to a file containing the goal (overrides --goal)",
    )
    p_form.add_argument(
        "--model", type=str, default="claude:opus",
        help="Provider-qualified model (e.g. claude:opus, claude:fable, openai:gpt-5.2, dgx:qwen, dgx:ornith)",
    )

    # scout
    p_scout = sub.add_parser("scout", help="Run the literature scout")
    p_scout.add_argument("--topic", type=str, required=True, help="Topic to search for")
    p_scout.add_argument(
        "--model", type=str, default="claude:sonnet",
        help="Provider-qualified model (e.g. claude:sonnet, dgx:qwen, dgx:ornith)",
    )

    # attack
    p_attack = sub.add_parser("attack", help="Run a specific attack vector agent")
    p_attack.add_argument(
        "--vector", type=str, required=True,
        choices=["analytic", "algebraic", "combinatorial", "dynamicalsystem"],
        help="Which attack vector to pursue",
    )
    p_attack.add_argument("--goal", type=str, default=None, help="Focus for this attack")
    p_attack.add_argument(
        "--goal-file", type=str, default=None,
        help="Path to a file containing the focus (overrides --goal)",
    )
    p_attack.add_argument(
        "--model", type=str, default="claude:opus",
        help="Provider-qualified model (e.g. claude:opus, claude:fable, openai:gpt-5.2, dgx:qwen, dgx:ornith)",
    )

    # paper
    p_paper = sub.add_parser(
        "paper",
        help="Update the paper in paper/ (main.tex + section files) to reflect new Lean results",
    )
    p_paper.add_argument("--goal", type=str, default=None, help="Focus area for the revision")
    p_paper.add_argument(
        "--goal-file", type=str, default=None,
        help="Path to a file containing the revision focus (overrides --goal)",
    )
    p_paper.add_argument(
        "--model", type=str, default="claude:opus",
        help="Provider-qualified model (e.g. claude:opus, claude:fable, openai:gpt-5.2, dgx:qwen, dgx:ornith)",
    )

    # transcribe
    p_trans = sub.add_parser("transcribe", help="Transcribe book pages (images or PDF) to markdown")
    p_trans.add_argument("sources", nargs="+", help="Image or PDF file paths (in page order)")
    p_trans.add_argument(
        "--output", "-o", type=str, default=None,
        help="Output markdown file path (default: docs/transcripts/<first_source_stem>.md)",
    )
    p_trans.add_argument(
        "--model", type=str, default="claude:opus",
        help="Provider-qualified model (e.g. claude:opus, claude:fable, openai:gpt-5.2, dgx:qwen, dgx:ornith)",
    )

    # style
    p_style = sub.add_parser("style", help="Run the code style agent on a Lean file")
    p_style.add_argument("--target", type=str, required=True, help="File or glob pattern to style-check")
    p_style.add_argument(
        "--model", type=str, default="claude:opus",
        help="Provider-qualified model (e.g. claude:opus, claude:sonnet)",
    )

    # run-openai — generic OpenAI agent runner (used by coordinator for dispatch)
    p_oai = sub.add_parser(
        "run-openai",
        help="Run a single agent on the OpenAI backend",
    )
    p_oai.add_argument("--agent", type=str, required=True, help="Agent name to run")
    p_oai.add_argument("--prompt", type=str, required=True, help="Prompt for the agent")
    p_oai.add_argument(
        "--prompt-file", type=str, default=None,
        help="Path to a file containing the prompt (overrides --prompt)",
    )
    p_oai.add_argument(
        "--model", type=str, default="openai:gpt-5.2",
        help="Provider-qualified model (e.g. openai:gpt-5.2, openai:gpt-4.1)",
    )

    # send
    p_send = sub.add_parser("send", help="Send a message to the running coordinator")
    p_send.add_argument("message", nargs="+", help="Message text")

    # status
    sub.add_parser("status", help="Print current state from state files")

    args = parser.parse_args()

    from .coordinator import (
        print_status,
        run_attack,
        run_coordinator,
        run_formalizer,
        run_openai_agent,
        run_paper,
        run_scout,
        run_stylist,
        run_transcriber,
    )

    match args.command:
        case "coordinate":
            goal = args.goal
            if args.goal_file:
                from pathlib import Path
                goal = Path(args.goal_file).read_text().strip()
            # `all` expands to every known specialist; otherwise treat
            # the flag as a comma-separated list.
            _ALL_QWEN_SPECIALISTS = (
                "code-stylist",
                "attack-combinatorial",
                "attack-algebraic",
                "attack-analytic",
                "attack-dynamicalsystem",
                "literature-scout",
                "lean-formalizer",
                "paper-writer",
            )
            raw = (args.qwen_agents or "").strip()
            if raw.lower() == "all":
                qwen_agents = _ALL_QWEN_SPECIALISTS
            else:
                qwen_agents = tuple(
                    s.strip() for s in raw.split(",") if s.strip()
                )
            # --dgx-agents: name[=model] entries; `all[=model]` expands.
            dgx_agents: dict[str, str] = {}
            if args.dgx_split:
                _HEAVY = ("attack-combinatorial", "attack-algebraic",
                          "attack-analytic", "attack-dynamicalsystem",
                          "literature-scout", "paper-writer")
                _MECH = ("lean-formalizer", "code-stylist")
                dgx_agents.update({n: "dgx:qwen" for n in _HEAVY})
                dgx_agents.update({n: "dgx:ornith" for n in _MECH})
            for entry in (args.dgx_agents or "").split(","):
                entry = entry.strip()
                if not entry:
                    continue
                name, _, mdl = entry.partition("=")
                name, mdl = name.strip(), (mdl.strip() or args.dgx_default_model)
                if ":" not in mdl:
                    mdl = f"dgx:{mdl}"
                if name.lower() == "all":
                    for n in _ALL_QWEN_SPECIALISTS:
                        dgx_agents[n] = mdl
                else:
                    dgx_agents[name] = mdl
            if args.dgx_ctx is not None:
                os.environ["DGX_CONTEXT_WINDOW"] = str(args.dgx_ctx)
            if args.dgx_max_tokens is not None:
                os.environ["DGX_MAX_TOKENS"] = str(args.dgx_max_tokens)
            asyncio.run(run_coordinator(
                goal=goal,
                no_paper=args.no_paper,
                model=args.model,
                qwen_agents=qwen_agents,
                dgx_agents=dgx_agents,
            ))
        case "formalize":
            goal = args.goal
            if args.goal_file:
                from pathlib import Path
                goal = Path(args.goal_file).read_text().strip()
            if not goal:
                parser.error("formalize requires --goal or --goal-file")
            asyncio.run(run_formalizer(goal=goal, model=args.model))
        case "scout":
            asyncio.run(run_scout(topic=args.topic, model=args.model))
        case "attack":
            goal = args.goal
            if args.goal_file:
                from pathlib import Path
                goal = Path(args.goal_file).read_text().strip()
            asyncio.run(run_attack(vector=args.vector, goal=goal, model=args.model))
        case "paper":
            goal = args.goal
            if args.goal_file:
                from pathlib import Path
                goal = Path(args.goal_file).read_text().strip()
            asyncio.run(run_paper(goal=goal, model=args.model))
        case "style":
            asyncio.run(run_stylist(target=args.target, model=args.model))
        case "transcribe":
            from pathlib import Path
            sources = [str(Path(p).resolve()) for p in args.sources]
            if args.output:
                output = args.output
            else:
                stem = Path(args.sources[0]).stem
                output = f"docs/transcripts/{stem}.md"
            Path(output).parent.mkdir(parents=True, exist_ok=True)
            asyncio.run(run_transcriber(sources=sources, output=output, model=args.model))
        case "run-openai":
            prompt = args.prompt
            if args.prompt_file:
                from pathlib import Path
                prompt = Path(args.prompt_file).read_text().strip()
            asyncio.run(run_openai_agent(
                agent=args.agent, prompt=prompt, model=args.model,
            ))
        case "send":
            from datetime import datetime
            from .config import STATE_DIR
            inbox = STATE_DIR / "inbox.md"
            msg = " ".join(args.message)
            stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            # Append, don't overwrite — the coordinator clears the file
            # after handling it, so any existing content is an unread
            # message that must not be silently dropped.
            with inbox.open("a") as f:
                f.write(f"[{stamp}] {msg}\n")
            print(f"Sent to inbox: {msg}")
        case "status":
            asyncio.run(print_status())


if __name__ == "__main__":
    main()
