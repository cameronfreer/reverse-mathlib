#!/usr/bin/env python3
"""rmlib-zoo: orchestration and rendering for the reverse-mathlib catalog.

Division of labor: Lean owns the meaning and validation of the catalog (the exporter reads the
elaborated environment's persistent extension state); this tool owns orchestration, Graphviz
rendering, HTML generation, and CI diffs. It never parses Lean source, never scrapes
human-readable command output, and never decides that a mathematical fact follows.

Commands:
  build   Run the Lean exporter, project views, render DOT (+SVG when Graphviz is present),
          and generate the static site under .lake/build/zoo/.
  check   Validate canonical invariants of catalog.direct.json (schema id, sortedness,
          direction-aware edge recomputation, no timestamps). Exit 1 on any violation.
  serve   Serve the generated site locally.
  diff    Semantic diff of two catalog files (added/removed principles, ports, edges).

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
    interfaces = {p["id"]: p["interface"] for p in catalog["principles"] if p["interface"]}
    edges = []
    for port in catalog["ports"]:
        target = port["portDecl"]
        if target is None:
            continue
        for i, e in enumerate(port["evidence"]):
            if e["kind"] != "relative Lean factorization":
                continue
            if e["verification"] != "kernel checked":
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
    for section, key in (("principles", "id"), ("ports", "id")):
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
    print(f"rmlib-zoo check: ok ({len(catalog['principles'])} principles, "
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


def to_dot(catalog: dict) -> str:
    graph = catalog["ambientGraph"]
    lines = [DOT_HEADER]
    for n in graph["nodes"]:
        label = n["display"]["label"]
        lines.append(f'  "{n["id"]}" [label="{label}", tooltip="{n["id"]}"];')
    for e in graph["edges"]:
        lines.append(f'  "{e["source"]}" -> "{e["target"]}" '
                     f'[label="ambient, kernel checked", tooltip="{e["certificate"]}"];')
    lines.append("}")
    return "\n".join(lines) + "\n"


def render_svg(dot_path: Path, svg_path: Path) -> bool:
    dot = shutil.which("dot")
    if dot is None:
        print("rmlib-zoo: graphviz `dot` not found; skipping SVG (DOT is the comparand anyway)")
        return False
    res = subprocess.run([dot, "-Tsvg", str(dot_path), "-o", str(svg_path)])
    return res.returncode == 0


def site_html(catalog: dict, svg: str | None, dot_text: str) -> str:
    deps = catalog["dependencies"]
    e = html.escape

    def principle_rows() -> str:
        rows = []
        for p in catalog["principles"]:
            note = f"{e(p['literatureNote'])} <em>[claimed, UNVERIFIED]</em>" \
                if p.get("literatureNote") else "unknown"
            rows.append(
                f"<tr><td><code>{e(p['id'])}</code></td>"
                f"<td><code>{e(p['interface'] or 'none')}</code></td>"
                f"<td>{e(p['description'])}</td><td>{note}</td></tr>")
        return "\n".join(rows)

    def evidence_list(port: dict) -> str:
        items = []
        for ev in port["evidence"]:
            bits = [f"{e(ev['direction'])} · {e(ev['kind'])}: {e(ev['verification'])}"]
            if ev["certificate"]:
                bits.append(f"certificate <code>{e(ev['certificate'])}</code>")
            if ev["assumes"]:
                bits.append(f"assumes <code>{e(ev['assumes'])}</code>")
            bits.append(f"ambient: {e(ev['ambient'])}; scope: {e(ev['scope'])}")
            items.append("<li>" + " — ".join(bits) + "</li>")
        return "<ul>" + "\n".join(items) + "</ul>"

    def port_rows() -> str:
        rows = []
        for p in catalog["ports"]:
            note = f"{e(p['literatureNote'])} <em>[claimed, UNVERIFIED]</em>" \
                if p.get("literatureNote") else "unknown"
            rows.append(
                f"<tr><td><code>{e(p['id'])}</code></td>"
                f"<td><code>{e(p['mathlibDecl'] or 'none')}</code></td>"
                f"<td><code>{e(p['portDecl'] or 'none')}</code></td>"
                f"<td>{e(p['relation'])}</td><td>{note}</td>"
                f"<td>{evidence_list(p)}</td></tr>")
        return "\n".join(rows)

    graph_block = svg if svg is not None else f"<pre>{e(dot_text)}</pre>"
    return f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>reverse-mathlib zoo — ambient factorizations</title>
<style>
body {{ font-family: Helvetica, Arial, sans-serif; max-width: 72rem; margin: 2rem auto;
       padding: 0 1rem; }}
table {{ border-collapse: collapse; width: 100%; margin: 1rem 0; }}
td, th {{ border: 1px solid #ccc; padding: 0.4rem; text-align: left; vertical-align: top;
          font-size: 0.9rem; }}
.banner {{ background: #fff3cd; border: 1px solid #e0c060; padding: 0.75rem 1rem;
           border-radius: 4px; }}
footer {{ color: #666; font-size: 0.85rem; margin-top: 2rem; }}
</style></head><body>
<h1>reverse-mathlib zoo — ambient factorizations</h1>
<p class="banner"><strong>Honesty note:</strong> every edge below is a kernel-checked
<em>relative certificate in unrestricted Lean over standard ℕ</em> (scope:
ambientFactorization). Nothing on this page is a reverse-mathematics implication, an ω-model
result, or a subsystem theorem; those require the typed catalog and backend, and render as
<em>pending</em> until they exist.</p>
{graph_block}
<h2>Principles</h2>
<table><tr><th>id</th><th>Lean interface</th><th>description</th>
<th>literature note</th></tr>
{principle_rows()}
</table>
<h2>Ports</h2>
<table><tr><th>id</th><th>mathlib</th><th>port statement</th><th>relation</th>
<th>literature note</th><th>evidence</th></tr>
{port_rows()}
</table>
<footer>Generated by rmlib-zoo from <code>catalog.direct.json</code> —
Lean {e(deps["leanVersion"])}, mathlib {e(deps["mathlibRevision"])}.
No timestamp by design: the catalog depends only on the environment and the pin.</footer>
</body></html>
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
    svg = None
    if render_svg(dot_path, svg_path):
        svg = svg_path.read_text()
    site = out / "site"
    site.mkdir(parents=True, exist_ok=True)
    (site / "index.html").write_text(site_html(catalog, svg, dot_text))
    if svg is not None:
        shutil.copy(svg_path, site / "ambient-factorizations.svg")
    print(f"rmlib-zoo build: wrote {dot_path.name}"
          f"{', ' + svg_path.name if svg else ''}, views/ambient-standard/graph.json, "
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
