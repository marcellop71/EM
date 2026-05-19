import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent  # <repo root>
AGENTS_DIR = ROOT / "agents"
STATE_DIR = AGENTS_DIR / "state"
PROMPTS_DIR = AGENTS_DIR / "prompts"
EM_DIR = ROOT / "EM"
CLAUDE_MD = ROOT / ".claude" / "CLAUDE.md"

# OpenAI configuration (optional — only needed for openai: provider)
OPENAI_API_KEY = os.environ.get("OPENAI_API_KEY", "")

# ---------------------------------------------------------------------------
# DGX (local OpenAI-compatible) model registry
# ---------------------------------------------------------------------------
# The DGX Spark at <DGX_HOST> serves TWO models behind OpenAI-compatible
# servers (see `~/dev/serve.sh --list` on the DGX host):
#
#   dgx:qwen    sglang    :8000  qwen35-122b-hybrid-int4fp8  (Qwen3.5-122B,
#               hybrid INT4+FP8, 64k ctx). Tool calls arrive as raw
#               `<tool_call>` XML (no server-side parser) — the backend
#               parses them client-side.
#   dgx:ornith  llama.cpp :8001  Ornith-1.0-35B-GGUF          (Q8_0, n_ctx
#               65536). Native OpenAI `tool_calls`. Do NOT send
#               `chat_template_kwargs` (llama.cpp rejects unknown keys).
#
# Model strings are provider-qualified: `dgx:<alias>`. The legacy `qwen:`
# prefix is kept as an alias (`qwen:default` == `dgx:qwen`). Verify what is
# actually up with:  curl http://<DGX_HOST>:800{0,1}/v1/models
DGX_HOST = os.environ.get("DGX_HOST", "localhost")  # set to your local inference host

DGX_MODELS: dict[str, dict[str, str]] = {
    "qwen": {
        "endpoint": os.environ.get(
            "QWEN_ENDPOINT",
            os.environ.get("AI_ENDPOINT", f"http://{DGX_HOST}:8000/v1")),
        "model": os.environ.get(
            "QWEN_MODEL",
            os.environ.get("AI_MODEL", "qwen35-122b-hybrid-int4fp8")),
        "server": "sglang",
        # Hard context window the server was launched with (max_model_len /
        # n_ctx). Prompt + completion must fit inside it or the server 400s.
        "context_window": int(os.environ.get("QWEN_MAX_MODEL_LEN", "65536")),
    },
    "ornith": {
        "endpoint": os.environ.get("ORNITH_ENDPOINT", f"http://{DGX_HOST}:8001/v1"),
        "model": os.environ.get("ORNITH_MODEL", "Ornith-1.0-35B-GGUF"),
        "server": "llamacpp",
        "context_window": int(os.environ.get("ORNITH_MAX_MODEL_LEN", "65536")),
    },
}

# Fallback context window for models addressed by a raw served-id (unknown
# alias). Both current DGX models are 65536; override with DGX_CONTEXT_WINDOW.
DGX_DEFAULT_CONTEXT_WINDOW = 65536
# Heuristic bytes-per-token for the char-budget context guard (conservative;
# the true ratio for code/Lean is ~3.5–4).
DGX_CHARS_PER_TOKEN = float(os.environ.get("DGX_CHARS_PER_TOKEN", "3.2"))
# Aliases resolving to registry keys.
DGX_ALIASES: dict[str, str] = {
    "default": "qwen",
    "qwen35": "qwen",
    "qwen35-122b-hybrid-int4fp8": "qwen",
    "ornith-1.0-35b-gguf": "ornith",
    "ornith35": "ornith",
}
DGX_DEFAULT = os.environ.get("DGX_DEFAULT_MODEL", "qwen")


def resolve_dgx_model(name: str | None) -> tuple[str, str, str, str, int]:
    """Resolve a `dgx:`/`qwen:` model suffix to
    (alias, endpoint, model, server, context_window).

    Accepts registry keys (`qwen`, `ornith`), aliases (`default`, …), or a
    raw served-model id. Unknown names fall back to DGX_DEFAULT's endpoint
    with the raw name passed through as the model id (lets you address a
    freshly served model without editing this file).

    The context window is read fresh from the environment on every call so a
    CLI flag (`--dgx-ctx`, which sets `DGX_CONTEXT_WINDOW`) or per-model env
    (`QWEN_MAX_MODEL_LEN` / `ORNITH_MAX_MODEL_LEN`) takes effect even though it
    is set after this module is imported. A global `DGX_CONTEXT_WINDOW`
    overrides all models; a per-model env overrides just that one."""
    key = (name or DGX_DEFAULT).strip()
    key = DGX_ALIASES.get(key.lower(), key)

    def _ctx(alias: str, base: int) -> int:
        g = os.environ.get("DGX_CONTEXT_WINDOW")
        if g:
            try:
                return int(g)
            except ValueError:
                pass
        per = os.environ.get(f"{alias.upper()}_MAX_MODEL_LEN")
        if per:
            try:
                return int(per)
            except ValueError:
                pass
        return base

    if key in DGX_MODELS:
        e = DGX_MODELS[key]
        return key, e["endpoint"], e["model"], e["server"], _ctx(key, e["context_window"])
    e = DGX_MODELS[DGX_DEFAULT]
    return (DGX_DEFAULT, e["endpoint"], key, e["server"],
            _ctx(DGX_DEFAULT, DGX_DEFAULT_CONTEXT_WINDOW))


# Backwards-compatible names (older modules import these).
QWEN_ENDPOINT = DGX_MODELS["qwen"]["endpoint"]
QWEN_MODEL_DEFAULT = DGX_MODELS["qwen"]["model"]
QWEN_API_KEY = os.environ.get("QWEN_API_KEY", os.environ.get("DGX_API_KEY", "sglang-dummy"))
DGX_API_KEY = QWEN_API_KEY
