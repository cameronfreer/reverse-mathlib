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

SCHEMA_ID = "reverse-mathlib.catalog/v0"


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
                         ("uniformProblems", "id"), ("ports", "id")):
        ids = [x[key] for x in catalog.get(section, [])]
        if ids != sorted(ids):
            problems.append(f"{section} not sorted by {key}")
        if len(ids) != len(set(ids)):
            problems.append(f"duplicate ids in {section}")
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
    if problems:
        for p in problems:
            print(f"rmlib-zoo check: {p}", file=sys.stderr)
        sys.exit(1)
    print(f"rmlib-zoo check: ok ({len(catalog['concepts'])} concepts, "
          f"{len(catalog['statementVariants'])} variants, "
          f"{len(catalog['ports'])} ports, {len(got)} ambient edges)")


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

    def port_cards() -> str:
        cards = []
        for p_ in catalog["ports"]:
            cards.append(f"""<div class="card">
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
<title>reverse-mathlib zoo — ambient factorizations</title>
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
<h1>reverse-mathlib zoo — ambient factorizations</h1>
<p><a href="https://github.com/cameronfreer/reverse-mathlib">cameronfreer/reverse-mathlib</a></p>
<p class="banner"><strong>Honesty note:</strong> every edge below is a kernel-checked
<em>relative certificate in unrestricted Lean over standard ℕ</em> (scope:
ambientFactorization). Nothing on this page is a reverse-mathematics implication, an ω-model
result, or a subsystem theorem; those require the typed catalog and backend, and render as
<em>pending</em> until they exist.</p>
{graph_block}
<h2>Concepts</h2>
{concept_cards()}
<h2>Statement variants (capability layer)</h2>
{variant_cards()}
<h2>Ports</h2>
{port_cards()}
<footer>Canonical data: <a href="catalog.direct.json">catalog.direct.json</a>
(schema <code>{e(catalog["schema"])}</code>) —
Lean {e(deps["leanVersion"])}, mathlib <code>{e(deps["mathlibRevision"])}</code>.
No timestamp by design: the catalog depends only on the environment and the pin.</footer>
</main></body></html>
"""


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
    (site / "index.html").write_text(site_html(catalog, have_svg, dot_text))
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
