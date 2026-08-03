#!/usr/bin/env python3
"""rmlib-zoo: orchestration and rendering for the reverse-mathlib catalog.

Division of labor: Lean owns the meaning and validation of the catalog (the exporter reads the
elaborated environment's persistent extension state); this tool owns orchestration, Graphviz
rendering, HTML generation, and CI diffs. It never parses Lean source, never scrapes
human-readable command output, and never decides that a mathematical fact follows.

Commands:
  build   Run the Lean exporter, project views, render DOT (+SVG when Graphviz is present),
          and generate the static site under .lake/build/zoo/.
  check   Validate canonical invariants of catalog.direct.json (schema id, sortedness of
          set-like arrays, direction-aware edge recomputation, no timestamps). Exit 1 on any
          violation. These are custom checks; schema/registry-v0.schema.json is the DOCUMENTED
          schema, not yet a machine-validated contract (real validation arrives with the first
          Python dependency and a lockfile).
  serve   Serve the generated site locally.
  diff    Semantic diff of two catalog files (added/removed principles, ports, edges).

Invocation: `python3 tools/zoo/rmlib_zoo.py ...` or `uv run --project tools/zoo rmlib-zoo ...`.

The only graph generated today is the honest ambient-factorization view: kernel-checked
relative certificates in unrestricted Lean. It is deliberately NOT named "implications" —
nothing in it is a reverse-mathematics implication.
"""

from __future__ import annotations

import argparse
import html
import json
import shutil
import subprocess
import sys
from pathlib import Path

SCHEMA_ID = "reverse-mathlib.catalog/v2"


def repo_root() -> Path:
    here = Path(__file__).resolve()
    root = here.parent.parent.parent
    if not (root / "lakefile.toml").exists():
        sys.exit(f"rmlib-zoo: no lakefile.toml at {root}")
    return root


def zoo_dir(root: Path) -> Path:
    return root / ".lake" / "build" / "zoo"


def load_catalog(root: Path) -> dict:
    path = zoo_dir(root) / "catalog.direct.json"
    if not path.exists():
        sys.exit(f"rmlib-zoo: {path} not found; run `rmlib-zoo build` (or the Lean exporter)")
    return json.loads(path.read_text())


def run_exporter(root: Path) -> None:
    print("rmlib-zoo: running Lean exporter (lake env lean scripts/ExportZoo.lean)")
    res = subprocess.run(["lake", "env", "lean", "scripts/ExportZoo.lean"], cwd=root)
    if res.returncode != 0:
        sys.exit("rmlib-zoo: Lean exporter failed")


# ---------------------------------------------------------------- edge recomputation

def recompute_edges(catalog: dict) -> list[dict]:
    """Recompute ambient edges from ports+principles, direction-aware.

    upper: principle interface -> port statement; lower: port statement -> interface;
    exact: both. Mirrors the Lean-side derivation; `check` compares the two exactly.
    """
    interfaces = {v["id"]: v["interface"]
                  for v in catalog["statementVariants"] if v["interface"]}
    edges = []
    for port in catalog["ports"]:
        target = port["portDecl"]
        if target is None:
            continue
        for i, e in enumerate(port["evidence"]):
            if e["kind"] != "relativeProof":
                continue
            if e["verification"] != "kernelChecked":
                continue
            if e["certificate"] is None or e["assumes"] is None:
                continue
            interface = interfaces.get(e["assumes"])
            if interface is None:
                continue

            def mk(src: str, tgt: str) -> dict:
                return {"source": src, "target": tgt, "direction": e["direction"],
                        "certificate": e["certificate"], "port": port["id"],
                        "evidenceIdx": i, "scope": "ambientFactorization"}

            if e["direction"] == "upper":
                edges.append(mk(interface, target))
            elif e["direction"] == "lower":
                edges.append(mk(target, interface))
            elif e["direction"] == "exact":
                edges.append(mk(interface, target))
                edges.append(mk(target, interface))
    edges.sort(key=lambda e: (e["source"], e["target"], e["port"], e["evidenceIdx"]))
    return edges


# ---------------------------------------------------------------- check

def find_key(obj, key: str) -> bool:
    if isinstance(obj, dict):
        return key in obj or any(find_key(v, key) for v in obj.values())
    if isinstance(obj, list):
        return any(find_key(v, key) for v in obj)
    return False


def cmd_check(args: argparse.Namespace) -> None:
    root = repo_root()
    catalog = load_catalog(root)
    problems: list[str] = []
    if catalog.get("schema") != SCHEMA_ID:
        problems.append(f"schema is {catalog.get('schema')!r}, expected {SCHEMA_ID!r}")
    deps = catalog.get("dependencies", {})
    for k in ("leanVersion", "mathlibRevision"):
        if not deps.get(k):
            problems.append(f"dependencies.{k} missing")
    if args.require_pin and deps.get("mathlibRevision") == "unavailable":
        problems.append("mathlibRevision is 'unavailable' (allowed locally, a failure in CI)")
    node_ids = [n["id"] for n in catalog.get("ambientGraph", {}).get("nodes", [])]
    if node_ids != sorted(node_ids):
        problems.append("ambientGraph.nodes not sorted")
    for section, key in (("concepts", "id"), ("statementVariants", "id"),
                         ("uniformProblems", "id"), ("ports", "id"),
                         ("baseTheories", "id"), ("formulaClasses", "id"),
                         ("reducibilityNotions", "id"), ("facts", "id"),
                         ("semanticContexts", "id")):
        ids = [x[key] for x in catalog.get(section, [])]
        if ids != sorted(ids):
            problems.append(f"{section} not sorted by {key}")
        if len(ids) != len(set(ids)):
            problems.append(f"duplicate ids in {section}")
    contexts = {c["id"] for c in catalog.get("semanticContexts", [])}
    for f in catalog.get("facts", []):
        for ev in f.get("evidence", []):
            if not ev.get("certificate") or not ev.get("context"):
                problems.append(f"fact {f.get('id')!r} has a certification without a "
                                "certificate or context")
            elif ev["context"] not in contexts:
                problems.append(f"fact {f.get('id')!r} cites unregistered semantic context "
                                f"{ev['context']!r}")
    got = catalog.get("ambientGraph", {}).get("edges", [])
    expected = recompute_edges(catalog)
    if got != expected:
        problems.append("ambientGraph.edges do not match direction-aware recomputation "
                        "from ports and principles")
    for e in got:
        if e.get("scope") != "ambientFactorization":
            problems.append(f"edge {e.get('source')} -> {e.get('target')} has scope "
                            f"{e.get('scope')!r}; every current edge must be an "
                            f"ambientFactorization")
    if find_key(catalog, "timestamp"):
        problems.append("canonical catalog must not contain timestamps")
    imps = catalog.get("importedReductions", [])
    imp_ids = [x["id"] for x in imps]
    if imp_ids != sorted(imp_ids):
        problems.append("importedReductions not sorted by id")
    if len(imp_ids) != len(set(imp_ids)):
        problems.append("duplicate ids in importedReductions")
    notion_ids = {x["id"] for x in catalog.get("reducibilityNotions", [])}
    uprob_ids = {x["id"].split(":", 1)[-1] for x in catalog.get("uniformProblems", [])}
    DEGREES = {"exact", "representative", "variantSensitive", "notAssigned"}
    for r in imps:
        rid = r.get("id")
        if r.get("status") not in ("importedChecked", "reported"):
            problems.append(f"imported reduction {rid!r} has invalid status")
        if r.get("status") == "importedChecked":
            if not (r.get("theorem") and r.get("mechanism")):
                problems.append(f"imported reduction {rid!r} importedChecked without trust fields")
            rev = r.get("revision", "")
            if not (len(rev) == 40 and all(c in "0123456789abcdef" for c in rev)):
                problems.append(f"imported reduction {rid!r} importedChecked without 40-hex revision")
        if r.get("degree") not in DEGREES:
            problems.append(f"imported reduction {rid!r} has unknown degree")
        ext, loc = r.get("external"), r.get("local")
        if not (ext and loc and all(ext.get(k) for k in ("notion", "lhs", "rhs"))
                and all(loc.get(k) for k in ("notion", "lhs", "rhs"))):
            problems.append(f"imported reduction {rid!r} missing external/local crosswalk keys")
            continue
        if loc["notion"] not in notion_ids:
            problems.append(f"imported reduction {rid!r} resolves unknown notion")
        for side in ("lhs", "rhs"):
            if loc[side].split(":", 1)[-1] not in uprob_ids:
                problems.append(f"imported reduction {rid!r} {side} resolves unknown problem")
    # per-family graph views: every direct edge corresponds to exactly one source
    # record; endpoints carry the required kind and layer; families never mix; an
    # equivalence renders as ONE bidirectional edge; bridges and unary form claims never
    # become edges; DOT and JSON agree; derived closure is absent by design.
    views_dir = zoo_dir(root) / "views"
    fam_views = build_family_views(catalog)
    variants = {v["id"].split(":", 1)[-1]: v for v in catalog.get("statementVariants", [])}
    uprobs = {q["id"].split(":", 1)[-1] for q in catalog.get("uniformProblems", [])}
    certified = [f for f in catalog.get("facts", []) if f.get("evidence")]
    ov = fam_views["omega-facts"]
    if len(ov["edges"]) != len([f for f in certified
                                if f.get("context", {}).get("scope") == "omegaModels"]):
        problems.append("omega-facts edges do not correspond 1:1 to certified ω facts")
    for ed in ov["edges"]:
        if ed["family"] != "certifiedOmegaFact":
            problems.append("omega-facts view mixes families")
        for side in ("lhs", "rhs"):
            v = variants.get(ed[side])
            if not v or v.get("layer") != "turingIdealOmega":
                problems.append(f"omega edge endpoint {ed[side]!r} not a turingIdealOmega variant")
        if (ed["kind"] == "equivalence") != bool(ed.get("bidirectional")):
            problems.append("equivalence must render as one bidirectional edge")
    iv = fam_views["imported-reductions"]
    if len(iv["edges"]) != len(catalog.get("importedReductions", [])):
        problems.append("imported-reductions edges do not correspond 1:1 to records")
    for ed in iv["edges"]:
        if ed["family"] != "importedReduction":
            problems.append("imported-reductions view mixes families")
        for side in ("lhs", "rhs"):
            if ed[side] not in uprobs:
                problems.append(f"imported edge endpoint {ed[side]!r} not a uniform problem")
    pv = fam_views["concept-projection"]
    expected = (len(catalog.get("ambientGraph", {}).get("edges", []))
                + len(ov["edges"]) + len(iv["edges"]))
    if len(pv["edges"]) != expected:
        problems.append("concept projection must contain exactly the direct edges — no "
                        "derived closure, no bridges, no unary claims")
    allowed = {"ambientFactorization", "certifiedOmegaFact", "importedReduction"}
    for ed in pv["edges"]:
        if ed["family"] not in allowed:
            problems.append(f"projection edge with forbidden family {ed['family']!r}")
        if not (ed.get("exactLhs") and ed.get("exactRhs") and ed.get("status")):
            problems.append("projection edge missing exact endpoints or status")
    for vname, view in fam_views.items():
        vpath = views_dir / vname / "graph.json"
        if not vpath.exists():
            problems.append(f"view file missing: {vname}")
            continue
        if json.loads(vpath.read_text()) != json.loads(
                json.dumps(view, sort_keys=True)):
            problems.append(f"view {vname} JSON does not match recomputation")
        dot = (views_dir / vname / "graph.dot").read_text()
        if dot.count(" -> ") != len(view["edges"]):
            problems.append(f"view {vname} DOT/JSON edge counts disagree")
    # corpus section: a separate family with stable ids, referential integrity, and the
    # fail-closed display statuses (claims reported, bridges missing)
    corpus = catalog.get("corpus", {})
    for section, key in (("sources", "namespace"), ("presentationFamilies", "id"),
                         ("claims", "id"), ("bridges", "id"), ("audits", "id")):
        ids = [x[key] for x in corpus.get(section, [])]
        if ids != sorted(ids):
            problems.append(f"corpus.{section} not sorted by {key}")
        if len(ids) != len(set(ids)):
            problems.append(f"duplicate ids in corpus.{section}")
    src_ids = {x["namespace"] for x in corpus.get("sources", [])}
    fam_ids = {x["id"] for x in corpus.get("presentationFamilies", [])}
    problem_ids = {x["id"].split(":", 1)[-1] for x in catalog.get("uniformProblems", [])}
    variant_ids = {x["id"].split(":", 1)[-1] for x in catalog.get("statementVariants", [])}
    for c in corpus.get("claims", []):
        if c.get("source") not in src_ids:
            problems.append(f"corpus claim {c.get('id')!r} cites unpinned source")
        if c.get("presentationFamily") not in fam_ids:
            problems.append(f"corpus claim {c.get('id')!r} cites unknown family")
        if c.get("status") != "reported":
            problems.append(f"corpus claim {c.get('id')!r} must be reported")
        if c.get("level") != "concept":
            problems.append(f"corpus claim {c.get('id')!r} must be concept-level")
        if (c.get("wordingKind") == "absent") != (c.get("wording") is None):
            problems.append(f"corpus claim {c.get('id')!r} wording/kind mismatch")
    for b in corpus.get("bridges", []):
        if b.get("fromFamily") not in fam_ids:
            problems.append(f"corpus bridge {b.get('id')!r} cites unknown family")
        if b.get("status") != "missing":
            problems.append(f"corpus bridge {b.get('id')!r} must be missing")
        tgt = b.get("target", {})
        tid = tgt.get("id", "").split(":", 1)[-1]
        if tgt.get("kind") == "uniformProblem" and tid not in problem_ids:
            problems.append(f"corpus bridge {b.get('id')!r} targets unknown problem")
        if tgt.get("kind") == "statement" and tid not in variant_ids:
            problems.append(f"corpus bridge {b.get('id')!r} targets unknown variant")
    if problems:
        for p in problems:
            print(f"rmlib-zoo check: {p}", file=sys.stderr)
        sys.exit(1)
    print(f"rmlib-zoo check: ok ({len(catalog['concepts'])} concepts, "
          f"{len(catalog['statementVariants'])} variants, "
          f"{len(catalog.get('facts', []))} facts, "
          f"{len(catalog['ports'])} ports, {len(got)} ambient edges; "
          f"corpus: {len(catalog.get('corpus', {}).get('sources', []))} sources, "
          f"{len(catalog.get('corpus', {}).get('claims', []))} claims, "
          f"{len(catalog.get('corpus', {}).get('bridges', []))} bridges, "
          f"{len(catalog.get('corpus', {}).get('audits', []))} audits — "
          f"separate from certified counts)")


# ---------------------------------------------------------------- rendering

DOT_HEADER = """\
// ambient-factorizations: kernel-checked relative certificates in unrestricted Lean.
// NOT reverse-mathematics implications. Generated by rmlib-zoo; do not edit.
digraph ambient_factorizations {
  rankdir=LR;
  node [shape=box, style="rounded", fontname="Helvetica"];
  edge [fontname="Helvetica", fontsize=10];
"""


def dot_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def to_dot(catalog: dict) -> str:
    graph = catalog["ambientGraph"]
    lines = [DOT_HEADER]
    for n in graph["nodes"]:
        label = dot_escape(n["display"]["label"])
        lines.append(f'  "{dot_escape(n["id"])}" [label="{label}", '
                     f'tooltip="{dot_escape(n["id"])}"];')
    for e in graph["edges"]:
        lines.append(f'  "{dot_escape(e["source"])}" -> "{dot_escape(e["target"])}" '
                     f'[label="ambient, kernel checked", '
                     f'tooltip="{dot_escape(e["certificate"])}"];')
    lines.append("}")
    return "\n".join(lines) + "\n"


def render_svg(dot_path: Path, svg_path: Path) -> bool:
    dot = shutil.which("dot")
    if dot is None:
        print("rmlib-zoo: graphviz `dot` not found; skipping SVG (DOT is the comparand anyway)")
        return False
    res = subprocess.run([dot, "-Tsvg", str(dot_path), "-o", str(svg_path)])
    if res.returncode != 0:
        # Graphviz being absent and Graphviz erroring are different outcomes: the latter fails.
        sys.exit("rmlib-zoo: graphviz `dot` failed")
    return True


def site_html(catalog: dict, have_svg: bool, dot_text: str) -> str:
    deps = catalog["dependencies"]
    e = html.escape

    def note_html(text: str | None) -> str:
        if not text:
            return "<em>unknown</em>"
        return f"{e(text)} <em>[claimed, UNVERIFIED]</em>"

    def variant_cards() -> str:
        cards = []
        for v in catalog["statementVariants"]:
            cards.append(f"""<div class="card">
<h3><code>{e(v['id'])}</code> <span class="tag">{e(v['layer'])}</span></h3>
<p>{e(v['description'])}</p>
<dl>
<dt>concept</dt><dd><code>{e(v['concept'])}</code></dd>
<dt>Lean interface</dt><dd><code>{e(v['interface'] or 'none')}</code></dd>
<dt>module</dt><dd><code>{e(v.get('interfaceModule') or '—')}</code></dd>
</dl></div>""")
        return "\n".join(cards)

    def evidence_items(port: dict) -> str:
        items = []
        for ev in port["evidence"]:
            d = ev["display"]
            bits = [f"<strong>{e(ev['direction'])}</strong> · {e(d['kind'])}: "
                    f"{e(d['verification'])}"]
            if ev["certificate"]:
                bits.append(f"certificate <code>{e(ev['certificate'])}</code>")
            if ev["assumes"]:
                bits.append(f"assumes <code>{e(ev['assumes'])}</code>")
            bits.append(f"ambient: {e(d['ambient'])}; scope: {e(d['scope'])}")
            items.append("<li>" + " — ".join(bits) + "</li>")
        return "<ul>" + "\n".join(items) + "</ul>"

    def graph_panels() -> str:
        views = build_family_views(catalog)
        titles = {"omega-facts": ("Certified ω facts", "bold edges; certified"),
                  "imported-reductions": ("Imported reductions", "dashed edges; external evidence"),
                  "concept-projection": ("Concept projection (noncanonical, lossy, direct-only)",
                                         "per-family line styles; derived closure deliberately absent")}
        parts = []
        for vname in ("omega-facts", "imported-reductions", "concept-projection"):
            v = views[vname]
            title, styling = titles[vname]
            items = []
            for ed in v["edges"]:
                src = ed.get("lhsConcept") or ed.get("lhs") or ed.get("exactLhs")
                tgt = ed.get("rhsConcept") or ed.get("rhs") or ed.get("exactRhs")
                detail = "; ".join(
                    f"{k}: {ed[k]}" for k in ("family", "fact", "record", "source",
                                              "scope", "notion", "status", "revision",
                                              "theorem", "exactLhs", "exactRhs")
                    if ed.get(k))
                certs = ", ".join(ed.get("certificates", []))
                if certs:
                    detail += f"; certificates: {certs}"
                arrow = "⇔" if ed.get("bidirectional") else "→"
                items.append(f"<li><code>{e(str(src))}</code> {e(ed.get('label', ''))} "
                             f"{arrow} <code>{e(str(tgt))}</code>"
                             f"<br/><small>{e(detail)}</small></li>")
            parts.append(f"""<details class="graphpanel"><summary><strong>{e(title)}</strong>
({len(v['edges'])} edges; {e(styling)})</summary>
<p><em>{e(v['comment'])}</em></p>
<p>Edge details (accessible list; families distinguished by label text and line style,
not color alone):</p><ul>{''.join(items)}</ul>
<p>DOT (canonical comparand; also at <code>views/{e(vname)}/graph.json</code>):</p>
<pre>{e(view_dot(vname, v))}</pre></details>""")
        return "\n".join(parts)

    def facts_section() -> str:
        facts = catalog.get("facts", [])
        if not facts:
            return ""
        contexts = {c["id"]: c for c in catalog.get("semanticContexts", [])}
        parts = ["<h2 id=\"facts-sec\">Certified semantic facts</h2>",
                 "<p><em>Extensional classifications, distinct from the proof routes "
                 "below: each fact is certified by a typed semantic certificate against a "
                 "registered context. Kernel-checked over every model of the context "
                 "predicate; the context's own status wording states what remains "
                 "literature-backed or pending.</em></p>"]
        for f_ in facts:
            evs = f_.get("evidence", [])
            if not evs:
                continue  # uncertified facts render in the catalog data, not here
            lhs = "+".join(x for x in f_.get("lhs", []))
            rhs = "+".join(x for x in f_.get("rhs", []))
            ctx = f_.get("context", {})
            ev_items = []
            for ev in evs:
                cdesc = contexts.get(ev.get("context"), {}).get("description", "")
                note = f" — {e(ev['note'])}" if ev.get("note") else ""
                ev_items.append(
                    f"<li>certificate <code>{e(ev['certificate'])}</code> "
                    f"[context <code>{e(ev['context'])}</code>]{note}"
                    f"<br/><em>context status:</em> {e(cdesc)}</li>")
            note_row = (f"<dt>note</dt><dd>{e(f_['note'])}</dd>" if f_.get("note") else "")
            parts.append(f"""<div class="card" data-family="certified">
<h3><code>{e(f_['id'])}</code> <span class="tag">{e(f_['kind'])}</span></h3>
<dl>
<dt>endpoints</dt><dd><code>{e(lhs)}</code> {e('⇔' if f_['kind'] == 'equivalence' else '⇒')} <code>{e(rhs)}</code></dd>
<dt>base / scope</dt><dd><code>{e(str(ctx.get('base', '')))}</code> / <code>{e(str(ctx.get('scope', '')))}</code></dd>
{note_row}
<dt>certifications</dt><dd><ul>{''.join(ev_items)}</ul></dd>
</dl></div>""")
        return "\n".join(parts)

    def imports_section() -> str:
        imps = catalog.get("importedReductions", [])
        if not imps:
            return ""
        parts = ["<h2 id=\"imports-sec\">Imported reductions</h2>",
                 "<p><em>Checked in an external machine-model repository at a pinned "
                 "revision and ingested as external evidence — never Lean axioms, never "
                 "certified counts; records without complete validated trust data are "
                 "downgraded to reported.</em></p>"]
        for r in imps:
            trust = (f"theorem <code>{e(r['theorem'] or '(none)')}</code>; mechanism "
                     f"<code>{e(r['mechanism'] or '(none)')}</code>")
            down = (f"<dt>downgraded</dt><dd>{e(r['downgraded'])}</dd>"
                    if r.get("downgraded") else "")
            parts.append(f"""<div class="card" data-family="imported">
<h3><code>{e(r['id'])}</code> <span class="tag">{e(r['status'])}</span></h3>
<dl>
<dt>local (resolved)</dt><dd><code>{e(r['local']['lhs'])}</code> ≤ <code>{e(r['local']['rhs'])}</code> [{e(r['local']['notion'])}, {e(r['degree'])}]</dd>
<dt>external (as ingested)</dt><dd><code>{e(r['external']['lhs'])}</code> ≤ <code>{e(r['external']['rhs'])}</code> [notion <code>{e(r['external']['notion'])}</code>, namespace <code>{e(r['namespace'])}</code>]</dd>
<dt>source</dt><dd><code>{e(r['repository'])}</code> @ <code>{e(r['revision'])}</code></dd>
<dt>checking</dt><dd>{trust}</dd>{down}
<dt>note</dt><dd>{e(r['note'])}</dd>
</dl></div>""")
        return "\n".join(parts)

    def corpus_section() -> str:
        corpus = catalog.get("corpus")
        if not corpus:
            return ""
        parts = ["<h2 id=\"corpus-sec\">Corpus audits</h2>",
                 "<p><em>Pinned external classification claims — scoped literature "
                 "findings, a separate family: never fact-graph edges, never certified "
                 "counts. An absence finding means <strong>not found in this pinned "
                 "corpus snapshot</strong>, never a mathematical negation; a "
                 "<strong>MISSING</strong> bridge is an unproved required bridge, never "
                 "evidence that no bridge exists.</em></p>"]
        for a in corpus.get("audits", []):
            parts.append(f"""<div class="card" data-family="corpus">
<h3><code>{e(a['id'])}</code> <span class="tag">audit</span></h3>
<dl><dt>scope</dt><dd>{e(a['scope'])}</dd>
<dt>outcome</dt><dd><strong>{e(a['outcome'])}</strong></dd></dl></div>""")
        parts.append("<h3>Pinned sources</h3><ul>")
        for src in corpus.get("sources", []):
            parts.append(f"<li><code>{e(src['namespace'])}</code> @ "
                         f"<code>{e(src['pin'])}</code> — {e(src['description'])}</li>")
        parts.append("</ul><h3>Presentation families</h3><ul>")
        for f_ in corpus.get("presentationFamilies", []):
            parts.append(f"<li><code>{e(f_['id'])}</code> — {e(f_['description'])}</li>")
        parts.append("</ul><h3>Claims (all reported; concept-level, never attached to "
                     "exact variants)</h3>")
        for c in corpus.get("claims", []):
            subjects = ", ".join(f"<code>{e(x)}</code> <span class=\"tag\">concept</span>"
                                 for x in c.get("concepts", []))
            if c["wordingKind"] == "absent":
                wording = "<em>wording not captured; locator only</em>"
            else:
                wording = f"<em>({e(c['wordingKind'])})</em> “{e(c['wording'])}”"
            parts.append(f"""<div class="card" data-family="corpus">
<h3><code>{e(c['id'])}</code> <span class="tag">{e(c['status'])}</span></h3>
<dl>
<dt>provenance</dt><dd><code>{e(c['source'])}</code>:“{e(c['locator'])}”</dd>
<dt>presentation family</dt><dd><code>{e(c['presentationFamily'])}</code></dd>
<dt>subjects</dt><dd>{subjects}</dd>
<dt>source wording</dt><dd>{wording}</dd>
<dt>normalized claim</dt><dd>{e(c['normalizedClaim'])}</dd>
</dl></div>""")
        parts.append("<h3>Presentation bridges</h3>")
        for b in corpus.get("bridges", []):
            parts.append(f"""<div class="card" data-family="corpus">
<h3><code>{e(b['id'])}</code> <span class="tag">MISSING — unproved required bridge</span></h3>
<dl>
<dt>from family</dt><dd><code>{e(b['fromFamily'])}</code></dd>
<dt>to exact target</dt><dd><code>{e(b['target']['id'])}</code> ({e(b['target']['kind'])})</dd>
<dt>requires</dt><dd>{e(b['requirement'])}</dd>
</dl></div>""")
        return "\n".join(parts)

    def port_cards() -> str:
        cards = []
        for p_ in catalog["ports"]:
            cards.append(f"""<div class="card" data-family="ambient">
<h3><code>{e(p_['id'])}</code> <span class="tag">{e(p_['display']['relation'])}</span></h3>
<dl>
<dt>mathlib</dt><dd><code>{e(p_['mathlibDecl'] or 'none')}</code></dd>
<dt>target variant</dt><dd><code>{e(p_['target'])}</code></dd>
<dt>port statement</dt><dd><code>{e(p_['portDecl'] or 'none')}</code></dd>
<dt>literature note</dt><dd>{note_html(p_.get('literatureNote'))}</dd>
</dl>
<h4>Evidence</h4>
{evidence_items(p_)}
<details><summary>note</summary><p>{e(p_['note'])}</p></details>
</div>""")
        return "\n".join(cards)

    def concept_cards() -> str:
        refs_by_target: dict[str, list[dict]] = {}
        for r in catalog.get("externalRefs", []):
            refs_by_target.setdefault(r["target"]["id"], []).append(r)
        cards = []
        for c in catalog.get("concepts", []):
            refs = refs_by_target.get(c["id"], [])
            ref_html = "".join(
                f'<li><code>{e(r["namespace"])}:&quot;{e(r["key"])}&quot;</code> '
                f'<span class="tag">{e(r["relation"])}</span></li>' for r in refs)
            refs_block = f"<ul class='refs'>{ref_html}</ul>" if ref_html else ""
            cards.append(f"""<div class="card">
<h3><code>{e(c['id'])}</code></h3>
<p>{e(c['description'])}</p>
{refs_block}</div>""")
        return "\n".join(cards)

    graph_block = ('<p class="graph"><img src="ambient-factorizations.svg" '
                   'alt="Ambient factorization graph: kernel-checked relative certificates">'
                   '</p>'
                   if have_svg else f'<div class="scroll"><pre>{e(dot_text)}</pre></div>')
    return f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>reverse-mathlib atlas</title>
<style>
* {{ box-sizing: border-box; }}
body {{ font-family: -apple-system, "Segoe UI", Helvetica, Arial, sans-serif;
       margin: 0; padding: 1.25rem 1rem 3rem; color: #1a1a1a; background: #fafafa;
       line-height: 1.5; }}
main {{ max-width: 56rem; margin: 0 auto; }}
h1 {{ font-size: 1.5rem; }}
h2 {{ font-size: 1.2rem; margin-top: 2rem; border-bottom: 1px solid #ddd;
      padding-bottom: 0.3rem; }}
h3 {{ font-size: 1rem; margin: 0 0 0.5rem; overflow-wrap: anywhere; }}
h4 {{ font-size: 0.9rem; margin: 0.75rem 0 0.25rem; }}
code {{ font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
        font-size: 0.85em; background: #f0f0f0; padding: 0.1em 0.3em;
        border-radius: 3px; overflow-wrap: anywhere; }}
.card {{ background: #fff; border: 1px solid #e2e2e2; border-radius: 6px;
         padding: 0.9rem 1.1rem; margin: 0.75rem 0; }}
.card p {{ margin: 0.4rem 0; }}
.tag {{ font-size: 0.72rem; font-weight: normal; color: #555; background: #eee;
        border-radius: 10px; padding: 0.1rem 0.55rem; vertical-align: middle;
        white-space: nowrap; }}
dl {{ display: grid; grid-template-columns: max-content 1fr; gap: 0.15rem 0.9rem;
      margin: 0.5rem 0; }}
dt {{ color: #666; font-size: 0.85rem; }}
dd {{ margin: 0; overflow-wrap: anywhere; }}
ul {{ margin: 0.3rem 0; padding-left: 1.2rem; }}
li {{ margin: 0.25rem 0; overflow-wrap: anywhere; }}
.banner {{ background: #fff6df; border: 1px solid #e6cf8a; padding: 0.75rem 1rem;
           border-radius: 6px; overflow-wrap: anywhere; }}
.graph {{ text-align: center; }}
.graph img {{ max-width: 100%; height: auto; }}
.scroll {{ overflow-x: auto; }}
details summary {{ cursor: pointer; color: #666; font-size: 0.85rem; }}
details p {{ font-size: 0.85rem; color: #444; }}
footer {{ color: #666; font-size: 0.8rem; margin-top: 2.5rem;
          border-top: 1px solid #ddd; padding-top: 0.75rem;
          overflow-wrap: anywhere; }}
a {{ color: #205ea6; }}
</style></head><body><main>
<h1>reverse-mathlib atlas</h1>
<p><a href="https://github.com/cameronfreer/reverse-mathlib">cameronfreer/reverse-mathlib</a></p>
<p class="banner"><strong>Honesty note:</strong> this page displays four grades of
evidence, permanently distinct. Every edge in the <em>graph below</em> is a kernel-checked
relative certificate in unrestricted Lean over standard ℕ (ambient factorization — proof
architecture, not strength). The <em>port cards</em> additionally carry the certified
ω-model facts — kernel-checked over every Turing ideal, with the identification of Turing
ideals with RCA₀'s ω-models literature-backed and backend object-syntax adequacy pending.
The <em>imported reductions</em> section holds Weihrauch reductions checked in a separate
machine-model repository at pinned revisions and ingested as external evidence, never
axioms. The
<em>corpus section</em> holds reported literature findings at pinned snapshots, with
missing presentation bridges named explicitly. No <code>RCA₀ ⊢ …</code> turnstile theorem
exists at any scope; scopes are never promoted, and derived closure results are computed,
never registered.</p>
<nav class="toc"><strong>Contents:</strong>
<a href="#graphs">Graphs</a> ·
<a href="#concepts-sec">Concepts</a> ·
<a href="#variants-sec">Variants</a> ·
<a href="#facts-sec">Certified facts</a> ·
<a href="#ports-sec">Ports</a> ·
<a href="#imports-sec">Imported reductions</a> ·
<a href="#corpus-sec">Corpus audits</a></nav>
<p class="summary"><strong>Counts (each family separate):</strong>
{len(catalog['concepts'])} concepts · {len(catalog['statementVariants'])} variants ·
{len([f for f in catalog.get('facts', []) if f.get('evidence')])} certified facts
(ω-model) · {len(catalog['ports'])} ports ·
{len(catalog.get('importedReductions', []))} imported reductions ·
{len(catalog.get('corpus', {}).get('claims', []))} corpus claims ·
{len(catalog.get('corpus', {}).get('bridges', []))} missing bridges</p>
<p class="filters">Filter:
<input type="text" id="ftext" placeholder="text, ids, theorems…" oninput="applyFilter()">
<select id="ffam" onchange="applyFilter()"><option value="">all families</option>
<option>ambient</option><option>certified</option><option>imported</option>
<option>corpus</option></select>
<noscript>(filtering needs JavaScript; all content below is fully visible without
it)</noscript></p>
<h2 id="graphs">Graphs (one per evidence family — never flattened into one)</h2>
{graph_panels()}
<h2>Ambient factorizations</h2>
{graph_block}
<h2 id="concepts-sec">Concepts</h2>
{concept_cards()}
<h2 id="variants-sec">Statement variants and Lean interfaces</h2>
{variant_cards()}
{facts_section()}
<h2 id="ports-sec">Ports</h2>
{port_cards()}
{imports_section()}
{corpus_section()}
<footer>Canonical data: <a href="catalog.direct.json">catalog.direct.json</a>
(schema <code>{e(catalog["schema"])}</code>) —
Lean {e(deps["leanVersion"])}, mathlib <code>{e(deps["mathlibRevision"])}</code>.
No timestamp by design: the catalog depends only on the environment and the pin.</footer>
</main><script>
/* Filtering changes visibility only; the canonical data is catalog.direct.json. */
function applyFilter() {{
  var t = document.getElementById('ftext').value.toLowerCase();
  var f = document.getElementById('ffam').value;
  document.querySelectorAll('.card').forEach(function (c) {{
    var okT = !t || c.textContent.toLowerCase().indexOf(t) >= 0;
    var okF = !f || c.getAttribute('data-family') === f;
    c.style.display = (okT && okF) ? '' : 'none';
  }});
}}
</script>
</body></html>
"""




def build_family_views(catalog: dict) -> dict:
    """The per-family direct-evidence views. Every edge corresponds to exactly one source
    record; families never mix inside a view; derived closure is deliberately absent
    (deferred until edges can carry typed derivation records)."""
    variants = {v["id"].split(":", 1)[-1]: v for v in catalog.get("statementVariants", [])}
    problems = {q["id"].split(":", 1)[-1]: q for q in catalog.get("uniformProblems", [])}
    omega_edges, omega_nodes = [], set()
    for f in catalog.get("facts", []):
        if not f.get("evidence"):
            continue
        if f.get("context", {}).get("scope") != "omegaModels":
            continue
        if f["kind"] not in ("implication", "equivalence"):
            continue
        lhs = f["lhs"][0].split(":", 1)[-1]
        rhs = f["rhs"][0].split(":", 1)[-1]
        omega_nodes.update([lhs, rhs])
        omega_edges.append({
            "family": "certifiedOmegaFact", "fact": f["id"], "kind": f["kind"],
            "bidirectional": f["kind"] == "equivalence",
            "label": "⊨ω ⇔" if f["kind"] == "equivalence" else "⊨ω →",
            "scope": f["context"].get("scope"), "base": f["context"].get("base"),
            "lhs": lhs, "rhs": rhs,
            "certificates": [e["certificate"] for e in f.get("evidence", [])]})
    imp_edges, imp_nodes = [], set()
    for r in catalog.get("importedReductions", []):
        lhs = r["local"]["lhs"].split(":", 1)[-1]
        rhs = r["local"]["rhs"].split(":", 1)[-1]
        notion = r["local"]["notion"]
        label = {"strongWeihrauch": "≤sW", "weihrauch": "≤W"}.get(notion, notion)
        imp_nodes.update([lhs, rhs])
        imp_edges.append({
            "family": "importedReduction", "record": r["id"], "label": label,
            "notion": notion, "degree": r["degree"], "status": r["status"],
            "lhs": lhs, "rhs": rhs, "repository": r["repository"],
            "revision": r["revision"], "theorem": r.get("theorem"),
            "external": r["external"]})
    # direct-only concept projection: noncanonical and lossy by construction; every
    # edge keeps its family, scope/notion, exact endpoint ids, and evidence status;
    # parallel edges stay separate; bridges and unary claims never appear.
    def concept_of_variant(vid: str) -> str:
        c = variants.get(vid, {}).get("concept", "")
        return c.split(":", 1)[-1] if c else ""
    iface_concept = {v.get("interface"): concept_of_variant(v["id"].split(":", 1)[-1])
                     for v in catalog.get("statementVariants", []) if v.get("interface")}
    def concept_of_problem(pid: str) -> str:
        c = problems.get(pid, {}).get("concept", "")
        return c.split(":", 1)[-1] if c else ""
    proj_edges = []
    for e in catalog.get("ambientGraph", {}).get("edges", []):
        proj_edges.append({"family": "ambientFactorization",
                           "label": "→" if e.get("direction") != "exact" else "⇔",
                           "lhsConcept": iface_concept.get(e.get("source"), ""),
                           "rhsConcept": iface_concept.get(e.get("target"), ""),
                           "exactLhs": e.get("source"), "exactRhs": e.get("target"),
                           "status": "kernelChecked", "scope": "ambientFactorization"})
    for e in omega_edges:
        proj_edges.append({"family": "certifiedOmegaFact", "label": e["label"],
                           "lhsConcept": concept_of_variant(e["lhs"]),
                           "rhsConcept": concept_of_variant(e["rhs"]),
                           "exactLhs": e["lhs"], "exactRhs": e["rhs"],
                           "status": "kernelChecked", "scope": "omegaModels",
                           "source": e["fact"], "bidirectional": e["bidirectional"]})
    for e in imp_edges:
        proj_edges.append({"family": "importedReduction", "label": e["label"],
                           "lhsConcept": concept_of_problem(e["lhs"]),
                           "rhsConcept": concept_of_problem(e["rhs"]),
                           "exactLhs": e["lhs"], "exactRhs": e["rhs"],
                           "status": e["status"], "scope": e["notion"],
                           "source": e["record"]})
    return {
        "omega-facts": {
            "view": "omega-facts", "family": "certifiedOmegaFact",
            "comment": "certified semantic facts at scope omegaModels; exact "
                       "Turing-ideal statement variants; an equivalence is ONE "
                       "bidirectional edge, never two leaves",
            "nodes": sorted(omega_nodes), "edges": omega_edges},
        "imported-reductions": {
            "view": "imported-reductions", "family": "importedReduction",
            "comment": "imported checked/reported reductions over represented uniform "
                       "problems; external evidence at pinned revisions, never axioms",
            "nodes": sorted(imp_nodes), "edges": imp_edges},
        "concept-projection": {
            "view": "concept-projection", "family": "mixed-direct-only",
            "comment": "NONCANONICAL, LOSSY, direct-only projection to concept "
                       "granularity; every edge keeps family, scope, exact endpoint "
                       "ids, and status; parallel edges stay separate; derived closure "
                       "is deliberately absent until edges can carry typed derivation "
                       "records; missing bridges and unary form claims never render as "
                       "edges",
            "nodes": sorted({c["id"].split(":", 1)[-1]
                             for c in catalog.get("concepts", [])}),
            "edges": proj_edges},
    }


STYLE = {"ambientFactorization": 'style=solid',
         "certifiedOmegaFact": 'style=bold',
         "importedReduction": 'style=dashed'}


def view_dot(name: str, view: dict) -> str:
    lines = [f'digraph "{name}" {{', '  rankdir=LR;', '  node [shape=box];']
    for n in view["nodes"]:
        lines.append(f'  "{n}";')
    for e in view["edges"]:
        fam = e.get("family", view.get("family", ""))
        style = STYLE.get(fam, "style=dotted")
        src = e.get("lhsConcept") or e.get("lhs") or e.get("exactLhs")
        tgt = e.get("rhsConcept") or e.get("rhs") or e.get("exactRhs")
        extra = ", dir=both" if e.get("bidirectional") else ""
        lines.append(f'  "{src}" -> "{tgt}" [label="{e.get("label", "")}", '
                     f'{style}{extra}];')
    lines.append('}')
    return "\n".join(lines) + "\n"


def cmd_build(args: argparse.Namespace) -> None:
    root = repo_root()
    if not args.skip_lean:
        run_exporter(root)
    catalog = load_catalog(root)
    out = zoo_dir(root)
    view_dir = out / "views" / "ambient-standard"
    view_dir.mkdir(parents=True, exist_ok=True)
    (view_dir / "graph.json").write_text(json.dumps(
        {"view": "ambient-standard", "axis": "ambientFactorization",
         "trust": ["kernelChecked"], "graph": catalog["ambientGraph"]},
        indent=1, sort_keys=True) + "\n")
    family_views = build_family_views(catalog)
    for vname, view in family_views.items():
        vdir = out / "views" / vname
        vdir.mkdir(parents=True, exist_ok=True)
        (vdir / "graph.json").write_text(
            json.dumps(view, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        (vdir / "graph.dot").write_text(view_dot(vname, view))
    dot_text = to_dot(catalog)
    dot_path = out / "ambient-factorizations.dot"
    dot_path.write_text(dot_text)
    svg_path = out / "ambient-factorizations.svg"
    have_svg = render_svg(dot_path, svg_path)
    site = out / "site"
    site.mkdir(parents=True, exist_ok=True)
    if have_svg:
        shutil.copy(svg_path, site / "ambient-factorizations.svg")
    # the canonical JSON is part of the public site: honest data over rendered views
    shutil.copy(zoo_dir(root) / "catalog.direct.json", site / "catalog.direct.json")
    page = site_html(catalog, have_svg, dot_text)
    for marker in ("Graphs (one per evidence family — never flattened into one)",
                   "noncanonical, lossy, direct-only",
                   "Filtering changes visibility only"):
        if marker not in page:
            sys.exit(f"rmlib-zoo build: graph/filter marker missing: {marker!r}")
    if catalog.get("corpus", {}).get("claims"):
        # rendered-page golden markers: the corpus section must frame absence and
        # missing bridges honestly, in the canonical order the JSON fixes
        for marker in ("Corpus audits", "not found in this pinned corpus snapshot",
                       "MISSING — unproved required bridge"):
            if marker not in page:
                sys.exit(f"rmlib-zoo build: corpus section marker missing: {marker!r}")
    (site / "index.html").write_text(page)
    print(f"rmlib-zoo build: wrote {dot_path.name}"
          f"{', ' + svg_path.name if have_svg else ''}, views/ambient-standard/graph.json, "
          f"site/index.html under {out}")


def cmd_serve(args: argparse.Namespace) -> None:
    import http.server

    root = repo_root()
    site = zoo_dir(root) / "site"
    if not site.exists():
        sys.exit("rmlib-zoo: no site generated; run `rmlib-zoo build` first")

    class Handler(http.server.SimpleHTTPRequestHandler):
        def __init__(self, *a, **kw):
            super().__init__(*a, directory=str(site), **kw)

    print(f"rmlib-zoo: serving {site} at http://localhost:{args.port}/")
    http.server.ThreadingHTTPServer(("", args.port), Handler).serve_forever()


def cmd_diff(args: argparse.Namespace) -> None:
    base = json.loads(Path(args.base).read_text())
    head = json.loads(Path(args.head).read_text())

    def ids(cat: dict, section: str) -> set:
        return {x["id"] for x in cat.get(section, [])}

    def edge_keys(cat: dict) -> set:
        return {(e["source"], e["target"], e["certificate"])
                for e in cat.get("ambientGraph", {}).get("edges", [])}

    for section in ("principles", "ports"):
        b, h = ids(base, section), ids(head, section)
        print(f"{section.capitalize():18s} +{len(h - b)} / -{len(b - h)}")
    b, h = edge_keys(base), edge_keys(head)
    print(f"{'Ambient edges':18s} +{len(h - b)} / -{len(b - h)}")
    for src, tgt, cert in sorted(h - b):
        print(f"  + {src} -> {tgt}  [{cert}]")
    for src, tgt, cert in sorted(b - h):
        print(f"  - {src} -> {tgt}  [{cert}]")


def main() -> None:
    parser = argparse.ArgumentParser(prog="rmlib-zoo", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p_build = sub.add_parser("build", help="export, project views, render, generate site")
    p_build.add_argument("--skip-lean", action="store_true",
                         help="reuse an existing catalog.direct.json")
    p_build.set_defaults(func=cmd_build)
    p_check = sub.add_parser("check", help="validate canonical catalog invariants")
    p_check.add_argument("--require-pin", action="store_true",
                         help="fail when mathlibRevision is 'unavailable' (used in CI)")
    p_check.set_defaults(func=cmd_check)
    p_serve = sub.add_parser("serve", help="serve the generated site")
    p_serve.add_argument("--port", type=int, default=8123)
    p_serve.set_defaults(func=cmd_serve)
    p_diff = sub.add_parser("diff", help="semantic diff of two catalog files")
    p_diff.add_argument("base")
    p_diff.add_argument("head")
    p_diff.set_defaults(func=cmd_diff)
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
