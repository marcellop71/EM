# Running swarm sessions — operator handbook

Practical reference for launching the agent swarm, recovering from failures, and retrying a
session with a different model. Written 2026-08-19 (after Sessions 308–311).

The authoritative record of *what* the swarm is doing lives in `agents/state/strategy_log.md`,
`agents/state/findings.md` and `docs/status.md`. This file is about *how* to run it.

---

## 1. The normal launch

```bash
.venv/bin/python -m agents coordinate --model claude:fable \
    --goal-file tmp/<goal-file>.md
```

Use `--goal-file`, **not** `--goal`. `--goal` passes the string itself; with a path as the
string the coordinator has to go open it, which works by luck rather than design.
`--goal-file` injects the document's contents.

Nothing else is needed: `CLAUDE_CODE_PRINT_BG_WAIT_CEILING_MS=0` is set from Python, and the
retry / job-supervisor machinery is in the code.

### Model selection

| Flag | Controls | Default |
|---|---|---|
| `--model` | the coordinator only | `claude:opus` |
| `--agents-model` | every Task-dispatched sub-agent (SDK alias: `opus`, `sonnet`, `haiku`, `inherit`) | `opus` |
| `--fallback-model` | model the coordinator switches to on a usage limit | `claude:opus` |

Coordinator on fable, specialists on opus:

```bash
.venv/bin/python -m agents coordinate --model claude:fable --agents-model opus \
    --goal-file tmp/<goal-file>.md
```

`--agents-model fable` does **not** work — the SDK accepts only `opus`/`sonnet`/`haiku`/
`inherit` or a full model ID in that position. Use `inherit` to put sub-agents on the
coordinator's own model.

### Fallback on usage limits

`--fallback-model` fires when the current model reports a usage/consumption limit (an API
error, or the CLI's own `Claude AI usage limit reached|…` error result), and as a last resort
when the primary stays overloaded past the retry budget. On a switch you see a yellow
`⟳ SWITCHING MODEL a → b` line. One switch only; `--fallback-model none` disables it.

Running on opus with fable as the safety net:

```bash
.venv/bin/python -m agents coordinate --model claude:opus \
    --fallback-model claude:fable --goal-file tmp/<goal-file>.md
```

**A model switch restarts the session from turn 1** — the SDK has no resume. Same for a
transient retry. After any run showing `⟳`, check `findings.md` and `strategy_log.md` for
double-appended blocks.

---

## 2. Retrying a session with a different model

There is no session resume. What makes a retry work is that all state is on disk — git
commits, `strategy_log.md`, `findings.md` — and every session begins by reading it. A later
session with a different model picks up where the last one stopped.

**Before a run you might want to undo**, tag the starting point:

```bash
git tag -f pre-sNNN HEAD
```

**To discard a whole session and retry:**

```bash
git reset --hard pre-sNNN
.venv/bin/python -m agents coordinate --model claude:fable --goal-file tmp/<same-goal-file>.md
```

**To keep the good parts** (the usual case): revert only the commits you don't want and
re-run the same goal file. The coordinator reads the log, sees which work packages landed,
and goes straight to what's left.

```bash
git revert <sha-of-one-WP-commit>
```

Delete the tag when done: `git tag -d pre-sNNN`.

### Make retries cheap — put this in every goal file

A "retry contract" section, requiring the coordinator to:

* commit **each work package separately**, with the WP tag in the subject (`S312 WP-N: …`),
  so one package can be reverted without losing the others;
* never leave `[IN PROGRESS]` dangling in `strategy_log.md` — finish the entry with an
  explicit `### NOT LANDED` subsection naming every package that did not finish, why it
  stopped, and what the next attempt should do differently (an empty one, stated explicitly,
  is the success case);
* say which theorem statements are final and which are provisional, and **never commit a
  weakened statement to make a package look finished**;
* record which model it ran on.

The last point is the one that matters most with a weaker model. A retry is easy; what is
expensive is a session that *looks* finished but quietly narrowed a theorem — that gives you
no signal to retry at all.

---

## 3. Long-running work: `spawn` / `wait` / `jobs`

The SDK ends the coordinator's session as soon as the model finishes a turn without a tool
call, and Claude Code then kills every shell process that session started. A direct-runner
launched with `cmd &` therefore **dies when the coordinator exits** — this lost the WP0
scoper reports three times on 2026-08-18. Task-dispatched sub-agents were always safe; only
shell launches were affected.

```bash
.venv/bin/python -m agents spawn -- attack --vector analytic --goal-file tmp/x.md
.venv/bin/python -m agents wait --timeout 590      # blocks; repeat until "all jobs finished"
.venv/bin/python -m agents jobs --tail 20          # list jobs, state, log tails
.venv/bin/python -m agents jobs --kill             # SIGTERM every running job
```

Jobs run detached in their own session and log to `agents/state/jobs/<name>.log`.

**The supervisor**: if the coordinator's session ends while spawned jobs are alive, the
command does *not* return — it waits, then re-invokes the coordinator with the job logs and a
"resume, evaluate, don't exit with work running" prompt (at most 6 continuations). Ctrl-C
terminates the jobs so nothing is left running behind you.

Running a scoper yourself, outside any coordinator, is always safe:

```bash
.venv/bin/python -m agents attack --vector dynamicalsystem --goal-file tmp/x.md
```

---

## 4. Checking a session's results

Never take the log's word for it. The checks, in order of value:

```bash
git log --oneline <pre-tag>..HEAD          # what actually landed
timeout 1200 lake build                    # must be green
.venv/bin/python tools/check_axioms.py     # must report 0 non-standard
grep -c "sorry\|native_decide" EM/Population/<new-file>.lean
```

Then, for any headline theorem:

```bash
cat > /tmp/ax.lean <<'LEAN'
import EM.Population.<File>
#print axioms <Namespace>.<theorem>
#check @<Namespace>.<theorem>
LEAN
lake env lean /tmp/ax.lean
```

`[propext, Classical.choice, Quot.sound]` means unconditional — no `sorry`, no custom axiom.

**A green build proves the proofs, not the statements.** The two things it cannot catch:

* **Vacuity.** Hypotheses that cannot be simultaneously satisfied make a theorem trivially
  true. Session 311 hit exactly this: an agent resolved a policy-window mismatch by requiring
  `log Y = n²` *exactly*, unsatisfiable over ℕ. Always ask whether the hypotheses are
  satisfiable, and whether the conclusion could hold for a degenerate reason (an empty
  sample space, a zero denominator).
* **Quiet weakening.** A statement that compiles but says less than intended. Read the
  `#check` output and the definitions it mentions.

Budget an hour reading the definitions behind any theorem before it is claimed in the paper.

---

## 5. Failure modes seen so far, and what fixed them

| Symptom | Cause | Fix (already in the code) |
|---|---|---|
| `API Error: 529 Overloaded`, run dies | transient overload propagated out of `query()` | retry with backoff in `claude_backend.py`; falls back to the other model past the budget |
| `Background tasks still running after 600s; terminating` | harness killed the coordinator mid-subagent | `CLAUDE_CODE_PRINT_BG_WAIT_CEILING_MS=0`, set from Python |
| Coordinator exits, agent reports never appear | direct-runners launched as background bash children died with the session | `agents spawn` + `wait`, and the supervisor loop |
| Agent returns findings as text, nothing on disk | subagent tool policy blocked report files | direct-runners append to `findings.md` themselves; prefer them for anything whose output must survive |
| Session "completes" but a theorem is vacuous | hypothesis windows intersected to nothing | manual satisfiability check, §4 above |

---

## 6. Other subcommands

```bash
.venv/bin/python -m agents status                       # agent roster + state summary
.venv/bin/python -m agents send "<message>"             # append to the coordinator's inbox
.venv/bin/python -m agents attack --vector <v> [--goal-file F]
.venv/bin/python -m agents formalize --goal '<lemma + sketch>'
.venv/bin/python -m agents scout --topic '<topic>'
.venv/bin/python -m agents paper [--goal-file F]
.venv/bin/python -m agents style --target EM/<file>.lean
```

`agents/state/inbox.md` is read by the coordinator after each sub-agent returns, and cleared
once handled — use `send` to steer a session that is already running.
