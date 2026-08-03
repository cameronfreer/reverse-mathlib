#!/usr/bin/env python3
"""RMZoo source census (issue #7, ingestion stage 1).

Exhaustive accounting over the vendored, pinned RMZoo snapshot: every source line
receives exactly one disposition, disposition totals must equal the source census, the
snapshot digest is verified against the pin, and the committed census golden must match
regeneration byte for byte. Comments may supply provenance but never become edges — the
commented Hall citation is the regression fixture. Symbol resolution is read exclusively
from the exported catalog's explicit rmzoo exact-alias crosswalk: no fuzzy or
acronym-based identity, unresolved symbols stay visible and non-inferential.

Runs entirely offline: the snapshot is vendored in-repo.

  rmzoo_census.py build   regenerate corpus/rmzoo/census-<rev>.json
  rmzoo_census.py check   verify digest, dispositions, golden, and the regression fixture
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

TOOL_VERSION = "2"
CENSUS_SCHEMA = "rmzoo-census/1"
REPOSITORY = "ericastor/rmzoo"
REVISION = "e92f57acf072115744e818cabd0ac13f2e724754"
SHA256 = "5544e76b7ab60374bdf65fb0afdbc759669148543c89164cc54618e91b1ba046"
SOURCE_FILE = "results.txt"

# The recognized relation operators, explicit and closed for this parser version.
# Anything else is unsupportedSyntax — visible, counted, never dropped silently.
OPS = {"->", "w->", "<->", "-|>", "w-|>", "form",
       "<=_c", "</=_c", "<=_w", "</=_w", "<=_sc", "</=_sc", "<=_sw", "</=_sw",
       "<=_gc", "</=_gc"}
CONSERVATION_RE = re.compile(r"^[nru]?(Pi|Sig)\d\d?c$")
SYM_RE = re.compile(r"^[A-Za-z][A-Za-z0-9]*$")
RELATION_RE = re.compile(r'^(\S+)\s+(\S+)\s+(\S+)\s*(?:"(.*)")?\s*$')


def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def snapshot_path(root: Path) -> Path:
    return root / "corpus" / "rmzoo" / f"results-{REVISION[:8]}.txt"


def census_path(root: Path) -> Path:
    return root / "corpus" / "rmzoo" / f"census-{REVISION[:8]}.json"


def crosswalk(root: Path) -> dict[str, str]:
    """The explicit rmzoo exact-alias crosswalk from the exported catalog. Never fuzzy."""
    cat_path = root / ".lake" / "build" / "zoo" / "catalog.direct.json"
    if not cat_path.exists():
        sys.exit("rmzoo_census: catalog.direct.json not found; run `rmlib-zoo build` "
                 "first (the crosswalk is read from the exported catalog, never guessed)")
    cat = json.loads(cat_path.read_text())
    walk: dict[str, str] = {}
    for r in cat.get("externalRefs", []):
        if r.get("namespace") == "rmzoo" and r.get("relation") == "exactAlias":
            walk[r["key"]] = f"{r['target']['kind']}:{r['target']['id']}"
    return walk


def is_op(tok: str) -> bool:
    return tok in OPS or bool(CONSERVATION_RE.match(tok))


def build_census(root: Path) -> dict:
    src = snapshot_path(root)
    data = src.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != SHA256:
        sys.exit(f"rmzoo_census: snapshot digest {digest} does not match the pin {SHA256}")
    lines = data.decode("utf-8").split("\n")
    if lines and lines[-1] == "":
        lines = lines[:-1]  # trailing newline
    dispositions = {"parsedRelation": 0, "parsedDirective": 0, "comment": 0,
                    "blank": 0, "unsupportedSyntax": 0}
    relations, directives, unsupported = [], [], []
    symbols: dict[str, int] = {}

    def note_symbols(syms: list[str]) -> None:
        for s in syms:
            symbols[s] = symbols.get(s, 0) + 1

    for i, raw in enumerate(lines, start=1):
        text = raw.strip()
        if text == "":
            dispositions["blank"] += 1
            continue
        if text.startswith("#"):
            dispositions["comment"] += 1
            continue
        m = re.match(r"^(\S+)\s+is\s+primary$", text)
        if m and all(SYM_RE.match(x) for x in m.group(1).split("+")):
            dispositions["parsedDirective"] += 1
            directives.append({"line": i, "symbols": m.group(1).split("+"),
                               "directive": "primary"})
            note_symbols(m.group(1).split("+"))
            continue
        m = RELATION_RE.match(text)
        if m and is_op(m.group(2)):
            lhs = m.group(1).split("+")
            rhs = m.group(3).split("+")
            if all(SYM_RE.match(x) for x in lhs) and all(SYM_RE.match(x) for x in rhs):
                dispositions["parsedRelation"] += 1
                relations.append({"line": i, "lhs": lhs, "op": m.group(2), "rhs": rhs,
                                  "justification": m.group(4)})
                note_symbols(lhs)
                if m.group(2) != "form":
                    note_symbols(rhs)
                continue
        dispositions["unsupportedSyntax"] += 1
        unsupported.append({"line": i, "text": raw})

    total = sum(dispositions.values())
    if total != len(lines):
        sys.exit(f"rmzoo_census: disposition total {total} != source census {len(lines)}")
    walk = crosswalk(root)
    symbol_rows = [{"symbol": s,
                    "occurrences": n,
                    "resolution": walk.get(s, "unresolved")}
                   for s, n in sorted(symbols.items())]
    return {
        "schema": CENSUS_SCHEMA,
        "tool": {"name": "rmzoo_census.py", "version": TOOL_VERSION},
        "source": {"repository": REPOSITORY, "revision": REVISION,
                   "file": SOURCE_FILE, "sha256": SHA256, "lineCount": len(lines)},
        "dispositions": dispositions,
        "relations": relations,
        "directives": directives,
        "unsupported": unsupported,
        "symbols": symbol_rows,
        "resolutionNote": "resolution comes exclusively from the catalog's explicit "
                          "rmzoo exact-alias crosswalk; 'unresolved' symbols are visible "
                          "and non-inferential — no fuzzy or acronym-based identity",
    }


def cmd_build() -> None:
    root = repo_root()
    census = build_census(root)
    census_path(root).write_text(json.dumps(census, indent=1, ensure_ascii=False) + "\n")
    d = census["dispositions"]
    print(f"rmzoo_census build: {census['source']['lineCount']} lines — "
          f"{d['parsedRelation']} relations, {d['parsedDirective']} directives, "
          f"{d['comment']} comments, {d['blank']} blank, "
          f"{d['unsupportedSyntax']} unsupported; "
          f"{sum(1 for s in census['symbols'] if s['resolution'] != 'unresolved')}"
          f"/{len(census['symbols'])} symbols crosswalked")


LEDGER_SCHEMA = "rmzoo-crosswalk/1"
DISPOSITIONS = {"exactAlias", "ambiguous", "relatedButNotAlias", "outOfCurrentCatalog",
                "unknownFromSource"}


def ledger_path(root: Path) -> Path:
    return root / "corpus" / "rmzoo" / f"crosswalk-{REVISION[:8]}.json"


def check_ledger(root: Path, census: dict) -> dict:
    """The 131-symbol disposition ledger: exhaustive, pinned, machine-checked."""
    lp = ledger_path(root)
    if not lp.exists():
        sys.exit("rmzoo_census check: crosswalk ledger missing")
    ledger = json.loads(lp.read_text())
    fail = lambda m: sys.exit(f"rmzoo_census check (ledger): {m}")
    if ledger.get("schema") != LEDGER_SCHEMA:
        fail(f"schema {ledger.get('schema')!r}, expected {LEDGER_SCHEMA!r}")
    src = ledger.get("source", {})
    if src.get("revision") != REVISION or src.get("sha256") != SHA256:
        fail("ledger is not pinned to the snapshot revision and digest")
    rows = ledger.get("symbols", [])
    names = [r.get("symbol") for r in rows]
    if names != sorted(names):
        fail("symbols not sorted")
    if len(names) != len(set(names)):
        fail("duplicate symbol dispositions")
    census_syms = {s["symbol"] for s in census["symbols"]}
    if set(names) != census_syms:
        missing = sorted(census_syms - set(names))
        extra = sorted(set(names) - census_syms)
        fail(f"ledger/census symbol mismatch: missing {missing}, extra {extra}")
    walk = crosswalk(root)
    counts = {k: 0 for k in DISPOSITIONS}
    for r in rows:
        d = r.get("disposition")
        if d not in DISPOSITIONS:
            fail(f"{r.get('symbol')}: unknown disposition {d!r}")
        counts[d] += 1
        if d == "exactAlias":
            tgt = r.get("target", "")
            if not tgt.startswith("concept:"):
                fail(f"{r['symbol']}: exactAlias must target a concept, never a "
                     f"statement variant or uniform problem (got {tgt!r})")
            if walk.get(r["symbol"]) != tgt:
                fail(f"{r['symbol']}: ledger alias {tgt!r} disagrees with the catalog "
                     f"crosswalk {walk.get(r['symbol'])!r}")
            if r.get("reason"):
                fail(f"{r['symbol']}: exactAlias carries no reason field")
        else:
            if not r.get("reason"):
                fail(f"{r['symbol']}: non-alias disposition requires a concise reason")
            if r.get("target"):
                fail(f"{r['symbol']}: non-alias disposition must not carry a target")
    for sym, tgt in walk.items():
        row = next((r for r in rows if r["symbol"] == sym), None)
        if row is None or row["disposition"] != "exactAlias" or row.get("target") != tgt:
            fail(f"catalog crosswalk entry {sym!r} not mirrored as an exactAlias row")
    if ledger.get("counts") != {k: counts[k] for k in sorted(counts)}:
        fail("counts object does not match recomputation")
    if sum(counts.values()) != len(census_syms):
        fail("disposition totals do not equal the symbol census")
    return counts


def cmd_check() -> None:
    root = repo_root()
    census = build_census(root)
    committed = census_path(root)
    if not committed.exists():
        sys.exit("rmzoo_census check: committed census golden missing; run build")
    if json.loads(committed.read_text()) != census:
        sys.exit("rmzoo_census check: committed census golden does not match "
                 "regeneration — rerun build and review the diff")
    # Regression fixture: the commented Hall citation supplies provenance only —
    # it must be a comment, and no parsed relation may reproduce its edge.
    src_lines = snapshot_path(root).read_text().split("\n")
    hall_lines = [i for i, l in enumerate(src_lines, start=1)
                  if "Marriage theorems and reverse mathematics" in l]
    if not hall_lines:
        sys.exit("rmzoo_census check: the Hall citation regression line is missing")
    for i in hall_lines:
        if not src_lines[i - 1].strip().startswith("#"):
            sys.exit(f"rmzoo_census check: Hall citation line {i} is not a comment")
        if any(r["line"] == i for r in census["relations"]):
            sys.exit(f"rmzoo_census check: Hall citation line {i} produced a relation")
    if any(r["op"] == "<->" and r["lhs"] == ["WKL"] and r["rhs"] == ["COLORk"]
           for r in census["relations"]):
        sys.exit("rmzoo_census check: the commented WKL <-> COLORk citation became an "
                 "edge — comments must never become mathematical relations")
    lcounts = check_ledger(root, census)
    d = census["dispositions"]
    print(f"rmzoo_census check: ledger ok ({lcounts['exactAlias']} exactAlias, "
          f"{lcounts['ambiguous']} ambiguous, {lcounts['relatedButNotAlias']} related, "
          f"{lcounts['outOfCurrentCatalog']} outOfCurrentCatalog, "
          f"{lcounts['unknownFromSource']} unknownFromSource — only exactAlias resolves)")
    print(f"rmzoo_census check: ok ({census['source']['lineCount']} lines fully "
          f"accounted: {d['parsedRelation']} relations, {d['parsedDirective']} "
          f"directives, {d['comment']} comments, {d['blank']} blank, "
          f"{d['unsupportedSyntax']} unsupported; Hall citation stays provenance-only)")


def main() -> None:
    if len(sys.argv) != 2 or sys.argv[1] not in ("build", "check"):
        sys.exit(__doc__)
    (cmd_build if sys.argv[1] == "build" else cmd_check)()


if __name__ == "__main__":
    main()
