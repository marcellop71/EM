"""Provider abstraction for multi-backend agent dispatch."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, AsyncIterator, Protocol, runtime_checkable

from ..rendering import AgentEvent


# ---------------------------------------------------------------------------
# AgentSpec — describes what to run, on which provider.
# ---------------------------------------------------------------------------

@dataclass
class AgentSpec:
    """Specification for a single agent invocation.

    The ``model`` field uses provider-qualified strings:
        "claude:opus", "claude:sonnet", "openai:gpt-5.2", "openai:gpt-4.1", etc.
    """
    name: str                                   # e.g. "lean-formalizer"
    label: str                                  # human-readable, e.g. "Formalizer"
    model: str                                  # provider-qualified, e.g. "claude:opus"
    system_prompt: str = ""
    tools: list[str] = field(default_factory=list)
    max_turns: int = 20
    budget: float = 25.0
    # Provider-qualified model to switch to if `model` hits a usage /
    # consumption limit (or stays overloaded past the retry budget), e.g.
    # "claude:opus" behind "claude:fable".  None = no fallback.
    fallback_model: str | None = None
    extra: dict[str, Any] = field(default_factory=dict)

    @property
    def provider(self) -> str:
        """Extract provider prefix (before colon)."""
        return self.model.split(":")[0] if ":" in self.model else "claude"

    @property
    def model_name(self) -> str:
        """Extract model name (after colon)."""
        return self.model.split(":", 1)[1] if ":" in self.model else self.model


# ---------------------------------------------------------------------------
# ProviderBackend — protocol that both Claude and OpenAI backends implement.
# ---------------------------------------------------------------------------

@runtime_checkable
class ProviderBackend(Protocol):
    """Async interface for running an agent on a specific provider."""

    async def run(
        self,
        spec: AgentSpec,
        prompt: str,
    ) -> AsyncIterator[AgentEvent]:
        """Stream AgentEvents from running the agent.

        Implementations yield events as the agent progresses.
        """
        ...


# ---------------------------------------------------------------------------
# Factory
# ---------------------------------------------------------------------------

_backends: dict[str, ProviderBackend] = {}


def register_backend(provider: str, backend: ProviderBackend) -> None:
    """Register a backend for a provider name."""
    _backends[provider] = backend


def get_backend(provider: str) -> ProviderBackend:
    """Get the backend for a provider, lazily importing if needed."""
    if provider not in _backends:
        if provider == "claude":
            from .claude_backend import ClaudeBackend
            _backends["claude"] = ClaudeBackend()
        elif provider == "openai":
            from .openai_backend import OpenAIBackend
            _backends["openai"] = OpenAIBackend()
        elif provider in ("qwen", "dgx"):
            # One backend serves both prefixes; the model suffix picks
            # the DGX endpoint (see config.DGX_MODELS).
            from .qwen_backend import QwenBackend
            _backends[provider] = QwenBackend()
        else:
            raise ValueError(
                f"Unknown provider: {provider!r}. "
                "Use 'claude', 'openai', 'dgx', or 'qwen'."
            )
    return _backends[provider]
