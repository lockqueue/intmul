"""Always-on runtime checks (SPEC §6.8 "runtime assertions"; SPEC §5.10).

SPEC §6.8 requires the runtime assertions to stay on in every run.  Python's ``assert`` statement is
compiled away by ``python -O`` (``__debug__`` is False), so the package contains no ``assert``
statement (enforced by ``tests/test_runtime_checks.py``, which parses every module): each check is an
explicit ``raise`` -- through :func:`require`, or inline ``if not cond: raise RuntimeCheckError(...)``
in hot loops, where the message is formatted only on failure.  ``subnlogn/__init__.py`` also refuses
to import under ``-O``.  Checks that already were explicit ``raise AssertionError(...)`` /
``raise ValueError(...)`` statements are kept as they are (they survive ``-O`` too).

:class:`RuntimeCheckError` subclasses :class:`AssertionError`, so ``except AssertionError`` and
``pytest.raises(AssertionError)`` catch every runtime check, old or new.
"""

from __future__ import annotations

from typing import Callable

__all__ = ["RuntimeCheckError", "require"]


class RuntimeCheckError(AssertionError):
    """A runtime check of SPEC §6.8 / §5.10 (or a hypothesis of the lemma it guards) failed.
    Raised by an explicit ``raise``, so ``python -O`` cannot strip it."""


def require(cond: object, msg: str | Callable[[], str] = "runtime check failed") -> None:
    """Raise :class:`RuntimeCheckError` unless ``cond`` is true (SPEC §6.8: runtime assertions are
    always on).  ``msg`` is the message, or a zero-argument callable returning it; a callable is
    evaluated only on failure, so messages that format data cost nothing on the passing path."""
    if not cond:
        raise RuntimeCheckError(msg() if callable(msg) else msg)
