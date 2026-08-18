"""Detached job supervision for the coordinator.

The Claude Agent SDK ends the coordinator's session the moment the model
finishes a turn without a tool call, and Claude Code then kills every shell
process that session started.  Anything the coordinator launched with a plain
``cmd &`` therefore dies with it — which is how the WP0 scopers were lost
three times on 2026-08-18.

This module gives the coordinator a way to launch direct-runners that outlive
its own session (``spawn``), a way to block on them from inside a Bash call
(``wait``), and gives ``run_coordinator`` a supervisor loop that refuses to let
the operator's command return while a spawned job is still alive — instead it
waits, then re-invokes the coordinator with the results.

Job records live in ``agents/state/jobs/``: ``<name>.json`` (metadata),
``<name>.pid`` (present while running), ``<name>.log`` (stdout+stderr).
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

from .config import ROOT, STATE_DIR

JOBS_DIR = STATE_DIR / "jobs"


@dataclass
class Job:
    name: str
    pid: int
    cmd: list[str]
    started: str
    log: Path

    @property
    def alive(self) -> bool:
        return _pid_alive(self.pid)


def _pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    # A zombie still answers kill(0); check its state.
    try:
        state = Path(f"/proc/{pid}/stat").read_text().split(")")[-1].split()[0]
        return state != "Z"
    except OSError:
        return True


def _job_name(cmd: list[str]) -> str:
    """``attack --vector analytic`` → ``attack-analytic-221345``."""
    # Keep the subcommand and the values of the first flag only, e.g. the
    # vector for `attack --vector analytic`; skip paths and later flags.
    parts: list[str] = []
    skip_value = False
    for c in cmd:
        if c.startswith("--"):
            skip_value = c not in ("--vector", "--topic", "--target")
            continue
        if skip_value or "/" in c or c.endswith(".md"):
            skip_value = False
            continue
        parts.append(c)
    stem = "-".join(parts[:2]) or "job"
    stem = "".join(ch if ch.isalnum() or ch == "-" else "-" for ch in stem)
    return f"{stem}-{datetime.now().strftime('%H%M%S')}"


def spawn(agent_args: list[str], *, name: str | None = None) -> Job:
    """Launch ``python -m agents <agent_args>`` detached; return the Job.

    The child gets its own session (``start_new_session``), so it survives
    the coordinator's Claude Code process exiting.  Output is line-buffered
    to the job log so a killed job still leaves a readable trace.
    """
    JOBS_DIR.mkdir(parents=True, exist_ok=True)
    name = name or _job_name(agent_args)
    log = JOBS_DIR / f"{name}.log"
    cmd = [sys.executable, "-u", "-m", "agents", *agent_args]
    env = dict(os.environ)
    env.pop("CLAUDECODE", None)  # same nesting workaround as cli.py
    with log.open("w") as fh:
        proc = subprocess.Popen(
            cmd, cwd=str(ROOT), stdout=fh, stderr=subprocess.STDOUT,
            stdin=subprocess.DEVNULL, start_new_session=True, env=env,
        )
    job = Job(name=name, pid=proc.pid, cmd=cmd,
              started=datetime.now().isoformat(timespec="seconds"), log=log)
    (JOBS_DIR / f"{name}.json").write_text(json.dumps({
        "name": name, "pid": job.pid, "cmd": cmd, "started": job.started,
        "log": str(log),
    }, indent=2))
    (JOBS_DIR / f"{name}.pid").write_text(str(job.pid))
    return job


def _load(meta: Path) -> Job | None:
    try:
        d = json.loads(meta.read_text())
        return Job(name=d["name"], pid=int(d["pid"]), cmd=d["cmd"],
                   started=d["started"], log=Path(d["log"]))
    except (OSError, KeyError, ValueError):
        return None


def all_jobs() -> list[Job]:
    if not JOBS_DIR.exists():
        return []
    jobs = [j for j in (_load(p) for p in sorted(JOBS_DIR.glob("*.json"))) if j]
    return jobs


def running_jobs() -> list[Job]:
    """Jobs whose pidfile exists and whose process is alive.

    A pidfile for a dead process is a job that finished (or was killed)
    without being reaped; it is removed here so it does not read as running.
    """
    live: list[Job] = []
    for j in all_jobs():
        pidfile = JOBS_DIR / f"{j.name}.pid"
        if not pidfile.exists():
            continue
        if j.alive:
            live.append(j)
        else:
            pidfile.unlink(missing_ok=True)
    return live


def wait(timeout: float | None = None, *, poll: float = 10.0,
         on_tick=None) -> list[Job]:
    """Block until no spawned job is running or ``timeout`` elapses.

    Returns the jobs still running when it returns (empty ⇒ all finished).
    ``on_tick(live_jobs, elapsed)`` is called every poll, if given.
    """
    start = time.monotonic()
    while True:
        live = running_jobs()
        if not live:
            return []
        elapsed = time.monotonic() - start
        if on_tick:
            on_tick(live, elapsed)
        if timeout is not None and elapsed >= timeout:
            return live
        time.sleep(poll)


def kill_all(sig: int = signal.SIGTERM) -> list[Job]:
    """Signal every running job's process group. Returns the jobs signalled."""
    killed = []
    for j in running_jobs():
        try:
            os.killpg(j.pid, sig)   # spawn() made the child a session leader
            killed.append(j)
        except ProcessLookupError:
            pass
    return killed


def tail(job: Job, lines: int = 40) -> str:
    try:
        return "\n".join(job.log.read_text(errors="replace").splitlines()[-lines:])
    except OSError:
        return ""


def summary_line(j: Job) -> str:
    state = "RUNNING" if j.alive else "done"
    return f"{j.name:32} pid={j.pid:<7} {state:8} started {j.started}  log={j.log}"
