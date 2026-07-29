#!/usr/bin/env python3
"""Enforce the sorry boundary and the meta/math root separation.

Policy:

1. Everything transitively imported by either production root — `ReverseMathlib.lean` (the
   mathematical root) or `ReverseMathlib/Registry.lean` (the tooling/registry root) — is
   sorry-free.
2. Work in progress lives under `ReverseMathlibExperimental/` and is never imported by either
   root. It may contain sorries; it still has to typecheck, which the separate
   `ReverseMathlibExperimental` lake target ensures.
3. The mathematical root's closure never contains tooling modules (`ReverseMathlib.Meta.*`,
   `ReverseMathlib.Ports.*`, or `ReverseMathlib.Registry`): ordinary users of the mathematics
   must not load metaprogramming machinery, and the mathematical axiom audit stays
   interpretable. The tooling root is audited separately by `scripts/MetaAxiomAudit.lean`.
4. Every `.lean` file under `ReverseMathlib/` is reachable from one of the two roots (no
   orphans): the lakefile builds the roots by exact glob, so an unimported file would otherwise
   silently escape CI.
5. Promotion into a root's closure requires removing all sorries and passing the axiom audit.
   Promotion is the reviewable event: a file appearing in a root's transitive closure is a
   claim that it is finished.

This script checks 1-4. It computes import closures from the source text rather than from build
artefacts, so it works on a clean checkout and cannot be fooled by a stale `.lake`.

Usage: scripts/check_sorry_boundary.py   (from anywhere inside the repo)
Exit status 1 on any violation.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

MATH_ROOT = "ReverseMathlib"
TOOLING_ROOT = "ReverseMathlib.Registry"
ROOTS = [MATH_ROOT, TOOLING_ROOT]
# Module prefixes owned by the tooling root; forbidden in the mathematical root's closure.
TOOLING_PREFIXES = ("ReverseMathlib.Meta", "ReverseMathlib.Ports")
EXPERIMENTAL_PREFIX = "ReverseMathlibExperimental"

# `sorry` and friends as whole words. `sorryAx` is the kernel-level form; `admit` is the
# tactic alias. Substring matches like `sorryFree` are excluded by the word boundaries.
SORRY_RE = re.compile(r"\b(sorry|sorryAx|admit)\b")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)")
# A line comment or the opening of a block comment; enough to skip prose mentions of the
# word "sorry" in docstrings, which are legitimate (this file's own policy text, say).
LINE_COMMENT_RE = re.compile(r"^\s*(--|/-|\*|-/)")


def repo_root() -> Path:
    here = Path(__file__).resolve().parent.parent
    if not (here / "lakefile.toml").exists():
        sys.exit(f"check_sorry_boundary: no lakefile.toml at {here}")
    return here


def module_path(root: Path, module: str) -> Path | None:
    """Source file for a repo-local module name, or None if it is not ours.

    Locality is decided by whether the file exists in the repo, not by a namespace
    prefix, so both `ReverseMathlib.*` and `ReverseMathlibExperimental.*` resolve. (Those are
    separate top-level namespaces on purpose: Lake's `isLocalModule` treats a name prefix as
    library ownership, so `ReverseMathlib.Experimental.*` would be claimed by the strict
    `ReverseMathlib` library too and its `sorry`s would become build errors.)
    """
    p = root / (module.replace(".", "/") + ".lean")
    return p if p.exists() else None


def imports_of(path: Path) -> list[str]:
    out = []
    for line in path.read_text().splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def closure(root: Path, start: str) -> set[str]:
    """Transitive repo-local import closure of `start`."""
    seen: set[str] = set()
    stack = [start]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        p = module_path(root, mod)
        if p is None:
            continue  # mathlib or a missing module; `lake build` is the judge of those
        seen.add(mod)
        stack.extend(imports_of(p))
    return seen


def sorries_in(path: Path) -> list[tuple[int, str]]:
    hits = []
    for i, line in enumerate(path.read_text().splitlines(), 1):
        if LINE_COMMENT_RE.match(line):
            continue
        if SORRY_RE.search(line):
            hits.append((i, line.strip()))
    return hits


def is_tooling(mod: str) -> bool:
    return mod == TOOLING_ROOT or any(
        mod == p or mod.startswith(p + ".") for p in TOOLING_PREFIXES)


def main() -> int:
    root = repo_root()
    math_spine = closure(root, MATH_ROOT)
    tooling_spine = closure(root, TOOLING_ROOT)
    spine = math_spine | tooling_spine
    status = 0

    # (1) both spines are sorry-free
    for mod in sorted(spine):
        p = module_path(root, mod)
        assert p is not None
        for lineno, text in sorries_in(p):
            rel = p.relative_to(root)
            print(f"{rel}:{lineno}: sorry in a production root's import spine — {text}",
                  file=sys.stderr)
            status = 1

    # (2) no Experimental or Fixtures module is in either spine
    for mod in sorted(spine):
        if mod == EXPERIMENTAL_PREFIX or mod.startswith(EXPERIMENTAL_PREFIX + "."):
            print(f"{mod} is reachable from a production root: experimental modules must "
                  f"not be imported by the production roots", file=sys.stderr)
            status = 1
        if mod == "ReverseMathlibFixtures" or mod.startswith("ReverseMathlibFixtures."):
            print(f"{mod} is reachable from a production root: collision-test fixtures must "
                  f"not be imported by the production roots", file=sys.stderr)
            status = 1

    # (3) the mathematical root's closure contains no tooling modules
    for mod in sorted(math_spine):
        if mod != MATH_ROOT and is_tooling(mod):
            print(f"{mod} is reachable from {MATH_ROOT}.lean: tooling modules must not be "
                  f"imported by the mathematical root", file=sys.stderr)
            status = 1

    # (3b) principle statements and relative proofs never import the classical instances:
    # Standard/ and Slice/ must stay hypothesis-relative so factorization audits stay clean
    for mod in sorted(spine):
        if mod.startswith("ReverseMathlib.Standard") or mod.startswith("ReverseMathlib.Slice"):
            p = module_path(root, mod)
            assert p is not None
            for imp in imports_of(p):
                if imp.startswith("ReverseMathlib.Classical"):
                    print(f"{mod} imports {imp}: Standard/ and Slice/ modules must never "
                          f"import the classical instances", file=sys.stderr)
                    status = 1

    # (4) no orphans: every .lean file under ReverseMathlib/ is reachable from some root
    lib_dir = root / MATH_ROOT
    for p in sorted(lib_dir.rglob("*.lean")):
        mod = MATH_ROOT + "." + ".".join(p.relative_to(lib_dir).with_suffix("").parts)
        if mod not in spine:
            print(f"{p.relative_to(root)}: orphan — not reachable from any production root "
                  f"({', '.join(ROOTS)}); import it or remove it", file=sys.stderr)
            status = 1

    # Informational: what is staged outside the spine.
    exp_dir = root / EXPERIMENTAL_PREFIX
    staged = sorted(p.relative_to(root) for p in exp_dir.rglob("*.lean")) if exp_dir.is_dir() else []
    n_sorry = sum(1 for p in staged if sorries_in(root / p))

    if status == 0:
        print(f"check_sorry_boundary: {len(math_spine)} math + {len(tooling_spine)} tooling "
              f"spine module(s) sorry-free, meta-isolated, no orphans; {len(staged)} "
              f"experimental module(s) outside the spine ({n_sorry} containing sorries)")
    return status


if __name__ == "__main__":
    sys.exit(main())
