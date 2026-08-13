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
import re
import json
import shutil
import subprocess
import sys
from pathlib import Path

SCHEMA_ID = "reverse-mathlib.catalog/v6"
# The one label the canonical ambient graph carries; shared so the label gate covers
# to_dot as well as the family views. Directional glyphs are forbidden in ALL graph
# labels — direction belongs to drawn arrowheads only.
AMBIENT_EDGE_LABEL = "ambient, kernel checked"


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
    for c in catalog.get("concepts", []):
        if not str(c.get("statement", "")).strip():
            problems.append(f"concept {c.get('id')!r} missing a nonempty statement "
                            "(every displayed item must be defined)")
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
    bes = catalog.get("backendEvidence", [])
    be_ids = [x["id"] for x in bes]
    if be_ids != sorted(be_ids):
        problems.append("backendEvidence not sorted by id")
    if len(be_ids) != len(set(be_ids)):
        problems.append("duplicate ids in backendEvidence")
    BE_KINDS = {"contextRealization", "statementAdapter", "calculusIdentity",
                "calculusNonderivability", "semanticCountermodel"}
    for r in bes:
        rid = r.get("id")
        if r.get("kind") not in BE_KINDS:
            problems.append(f"backendEvidence {rid}: unknown kind {r.get('kind')!r}")
        if r.get("status") not in ("backendChecked", "reported"):
            problems.append(f"backendEvidence {rid}: unknown status {r.get('status')!r}")
        src = r.get("source", {})
        chk = r.get("checking", {})
        for f in ("repository", "exportRevision", "artifactRevision", "artifactPath",
                  "toolchain"):
            if not src.get(f):
                problems.append(f"backendEvidence {rid}: missing source.{f}")
        for f in ("reverse-mathlib", "Foundation", "mathlib"):
            if not src.get("dependencies", {}).get(f):
                problems.append(f"backendEvidence {rid}: missing source.dependencies.{f}")
        if r.get("status") == "backendChecked":
            if not chk.get("mechanism") or not chk.get("audit") or \
                    not chk.get("allowedAxioms"):
                problems.append(f"backendEvidence {rid}: backendChecked without complete "
                                "checking coordinates")
        if r.get("kind") == "semanticCountermodel":
            data = r.get("data", {})
            for ref_field in ("contextRealization", "sentenceAdapter"):
                if data.get(ref_field) not in be_ids:
                    problems.append(f"backendEvidence {rid}: broken record reference "
                                    f"{ref_field}={data.get(ref_field)!r}")
            if data.get("scope") != "allModels" or                     data.get("modelClass") != "foundationStruc2General":
                problems.append(f"backendEvidence {rid}: unknown scope/modelClass tags")
            rendered = r.get("display", {}).get("rendered", "")
            for marker in ("allModels", "ω-countermodel", "conventional-RCA₀"):
                if marker not in rendered:
                    problems.append(f"backendEvidence {rid}: rendering must carry the "
                                    f"scope, witness-provenance, and honesty markers "
                                    f"(missing {marker!r})")
        if r.get("kind") == "calculusNonderivability":
            data = r.get("data", {})
            for ref_field in ("calculusRecord", "sentenceAdapter"):
                if data.get(ref_field) not in be_ids:
                    problems.append(f"backendEvidence {rid}: broken record reference "
                                    f"{ref_field}={data.get(ref_field)!r}")
            rendered = r.get("display", {}).get("rendered", "")
            if "pending" not in rendered or data.get("calculusId", "") not in rendered:
                problems.append(f"backendEvidence {rid}: rendering must carry the "
                                "calculus id and the pending comparison qualifier")
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
    EDGE_KINDS = ("implication", "equivalence", "nonImplication")
    for f in certified:
        if f.get("kind") not in EDGE_KINDS:
            problems.append(f"certified fact {f.get('id')!r} has kind {f.get('kind')!r} "
                            "with no rendering rule — fail closed, never render silently")
    ov = fam_views["omega-facts"]
    if len(ov["edges"]) != len([f for f in certified
                                if f.get("context", {}).get("scope") == "omegaModels"
                                and f.get("kind") in EDGE_KINDS]):
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
        if (ed["kind"] == "nonImplication") != (ed.get("label") == "⊭ω"):
            problems.append("a certified separation must render as exactly the ⊭ω edge "
                            "(and nothing else may use that label)")
    iv = fam_views["imported-reductions"]
    iv_records = []
    for ed in iv["edges"]:
        iv_records += ed.get("records", [ed.get("record")])
    if sorted(iv_records) != sorted(x["id"] for x in imps):
        problems.append("imported-reductions edges do not cover the records exactly "
                        "once each (antiparallel pairs merge into one bidirectional "
                        "edge carrying both records)")
    imp_by_id = {x["id"]: x for x in imps}
    for ed in iv["edges"]:
        if ed.get("bidirectional"):
            if len(ed.get("records", [])) != 2:
                problems.append("a merged bidirectional imported edge must carry exactly "
                                "its two source records")
                continue
            fwd = imp_by_id.get(ed.get("forwardRecord"))
            rev = imp_by_id.get(ed.get("reverseRecord"))
            if fwd is None or rev is None:
                problems.append("merged imported edge lacks directional source metadata "
                                "(forwardRecord/reverseRecord)")
                continue
            if (fwd["local"]["lhs"].split(":", 1)[-1] != ed["lhs"]
                    or fwd["local"]["rhs"].split(":", 1)[-1] != ed["rhs"]
                    or rev["local"]["lhs"].split(":", 1)[-1] != ed["rhs"]
                    or rev["local"]["rhs"].split(":", 1)[-1] != ed["lhs"]):
                problems.append("merged imported edge's directional records do not "
                                "certify the directions they are attached to")
            notions = {fwd["local"]["notion"], rev["local"]["notion"]}
            if ed.get("derivation") == "strongImpliesOrdinary":
                if notions != {"strongWeihrauch", "weihrauch"}:
                    problems.append("strongImpliesOrdinary weakening claimed but the "
                                    "two records are not one strong + one ordinary")
                strong = fwd if fwd["local"]["notion"] == "strongWeihrauch" else rev
                want_end = "head" if strong is fwd else "tail"
                if ed.get("strongEnd") != want_end:
                    problems.append("merged edge's strongEnd does not point at the "
                                    "direction certified strong")
            elif len(notions) != 1:
                problems.append("mixed-notion merged edge must carry the explicit "
                                "strongImpliesOrdinary weakening annotation")
            want_status = ("importedChecked"
                           if fwd["status"] == "importedChecked"
                           and rev["status"] == "importedChecked" else "reported")
            if ed.get("status") != want_status:
                problems.append("merged edge status must be derived from both premises "
                                "(importedChecked only when both directions are)")
    for ed in iv["edges"]:
        if ed["family"] != "importedReduction":
            problems.append("imported-reductions view mixes families")
        for side in ("lhs", "rhs"):
            if ed[side] not in uprobs:
                problems.append(f"imported edge endpoint {ed[side]!r} not a uniform problem")
    pv = fam_views["concept-projection"]
    amb_edges = catalog.get("ambientGraph", {}).get("edges", [])
    amb_pair_count = sum(1 for e in amb_edges
                         if (e["target"], e["source"]) in
                            {(x["source"], x["target"]) for x in amb_edges}
                         and e["source"] < e["target"])
    cluster_edges = [e for cl in pv.get("clusters", {}).values() for e in cl["edges"]]
    expected = ((len(amb_edges) - amb_pair_count)
                + len(ov["edges"]) + len(iv["edges"]))
    if len(pv["edges"]) + len(cluster_edges) != expected:
        problems.append("concept projection must contain exactly the direct edges "
                        "(antiparallel pairs merged with both sources; intra-concept "
                        "calibrations inside their concept enclosure) — no derived "
                        "closure beyond the explicit weakening annotation, no bridges, "
                        "no unary claims")
    allowed = {"ambientFactorization", "certifiedOmegaFact", "importedReduction"}
    for ed in pv["edges"]:
        if ed["family"] not in allowed:
            problems.append(f"projection edge with forbidden family {ed['family']!r}")
        if not (ed.get("exactLhs") and ed.get("exactRhs") and ed.get("status")):
            problems.append("projection edge missing exact endpoints or status")
        if ed.get("lhsConcept") and ed.get("lhsConcept") == ed.get("rhsConcept"):
            problems.append(f"projected concept self-loop survived on "
                            f"{ed.get('lhsConcept')!r}; an intra-concept calibration "
                            "renders only inside its concept enclosure")
    # the enclosure gates: every intra-concept fact exactly once inside its concept
    # enclosure, internal nodes resolving to exact registered ω variants, the
    # certificate carried into the accessible details
    for cname, cl in pv.get("clusters", {}).items():
        endpoint_variants = set()
        for ed in cl["edges"]:
            if ed.get("family") != "certifiedOmegaFact":
                problems.append(f"cluster {cname!r} contains a "
                                f"{ed.get('family')!r} edge; only certified ω "
                                "calibrations have an enclosure rule")
            if not (ed.get("lhsConcept") == cname == ed.get("rhsConcept")):
                problems.append(f"cluster {cname!r} contains an edge that does not "
                                "belong to its concept")
            for side in ("exactLhs", "exactRhs"):
                if ed.get(side) not in variants:
                    problems.append(f"cluster {cname!r} internal endpoint "
                                    f"{ed.get(side)!r} is not a registered variant")
                endpoint_variants.add(ed.get(side))
            if not ed.get("certificates"):
                problems.append(f"cluster {cname!r} edge {ed.get('source')!r} carries "
                                "no certificate")
        if sorted(endpoint_variants) != cl.get("variants", []):
            problems.append(f"cluster {cname!r} variant list must be exactly the "
                            "internal edges' endpoints")
        if len(cl.get("variants", [])) < 2:
            problems.append(f"cluster {cname!r} must contain at least two variants — "
                            "a single-variant enclosure is a self-loop in disguise")
    cluster_srcs = [ed.get("source") for ed in cluster_edges]
    if len(cluster_srcs) != len(set(cluster_srcs)):
        problems.append("an intra-concept fact appears more than once across "
                        "concept enclosures")
    problems.extend(check_scoped_results(catalog))
    for name in selftest_scoped_results():
        problems.append(f"scoped-results checker selftest did not fail closed: {name}")
    # typed computed closure: view-only derived edges, each the conclusion of a proof
    # tree that typechecks; the evaluator's fail-closed fixtures run here too
    for name in selftest_derivations():
        problems.append(f"computed-closure evaluator fixture did not fail closed: {name}")
    cv = fam_views["computed-closure"]
    derived = [e for e in cv["edges"] if e.get("family") == "computedClosure"]
    premises = [e for e in cv["edges"] if e.get("family") != "computedClosure"]
    if len(derived) != len(COMPUTED_DERIVATIONS):
        problems.append("computed-closure must contain exactly the declared derivations "
                        "— derived edges are hand-declared, never searched")
    if len({e["id"] for e in derived}) != len(derived):
        problems.append("derived edge ids must be unique and stable")
    fact_ids = {f["id"] for f in catalog.get("facts", []) if f.get("evidence")}
    red_ids = {r["id"] for r in catalog.get("importedReductions", [])}
    cited: set[str] = set()
    for ed in derived:
        if ed.get("status") != "computedView":
            problems.append(f"derived edge {ed['id']!r} must carry status computedView, "
                            "never a certified or imported status")
        if not ed.get("leaves"):
            problems.append(f"derived edge {ed['id']!r} cites no leaves")
        for leaf in ed.get("leaves", []):
            if leaf not in fact_ids and leaf not in red_ids:
                problems.append(f"derived edge {ed['id']!r} cites unknown leaf {leaf!r}")
            cited.add(leaf)
        if not ed.get("derivation") or not ed.get("derivationText"):
            problems.append(f"derived edge {ed['id']!r} lacks its proof term")
        # the stored conclusion must be exactly what the stored term proves
        try:
            j = eval_derivation(ed["derivation"], {
                "facts": {f["id"]: f for f in catalog.get("facts", []) if f.get("evidence")},
                "reductions": {r["id"]: r for r in catalog.get("importedReductions", [])}})
        except DerivationError as exc:
            problems.append(f"derived edge {ed['id']!r} does not typecheck: {exc}")
            continue
        if (j["lhs"], j["rhs"], j["relation"]) != (ed["lhs"], ed["rhs"], ed["relation"]):
            problems.append(f"derived edge {ed['id']!r} does not match its proof term's "
                            "conclusion")
        if sorted(set(j["leaves"])) != sorted(ed["leaves"]):
            problems.append(f"derived edge {ed['id']!r} does not cite every leaf of its "
                            "proof term")
    for ed in premises:
        # canonical constructors key on fact/record, not a synthetic id
        pid = ed.get("fact") or ed.get("record")
        if pid not in cited:
            problems.append(f"computed-closure premise edge {pid!r} is not cited by "
                            "any derivation — the view shows exactly the cited premises")
        if ed.get("status") == "computedView" or ed.get("family") == "computedClosure":
            problems.append("a direct premise edge must keep its own family and status")
        # provenance parity: the displayed premise must be byte-identical to the same
        # record's canonical edge, so no skinny duplicate can drift
        canon = (direct_omega_edge(next(f for f in catalog.get("facts", [])
                                        if f["id"] == pid))
                 if ed.get("fact") else
                 direct_imported_edge(next(r for r in catalog.get("importedReductions", [])
                                           if r["id"] == pid)))
        if ed != canon:
            problems.append(f"computed-closure premise edge {pid!r} is not the canonical "
                            "direct-edge record for that source")
    # the canonical views stay direct-only: no derived edge may leak into them
    # (concept enclosures included — an enclosure is display grouping, not closure)
    for vname in ("omega-facts", "imported-reductions", "concept-projection"):
        vw = fam_views[vname]
        all_edges = vw["edges"] + [e for cl in vw.get("clusters", {}).values()
                                   for e in cl["edges"]]
        for ed in all_edges:
            if ed.get("family") == "computedClosure" or ed.get("status") == "computedView":
                problems.append(f"canonical view {vname} contains a computed edge; "
                                "canonical graphs are direct-only")
    # closed label sets per family, and no directional glyph may appear in any graph
    # label: direction is carried by drawn arrowheads only (dir=both / tee), never by
    # label text — the gate that keeps the Stroop bug from returning
    LABELS_BY_FAMILY = {"certifiedOmegaFact": {"⊨ω", "⊭ω"},
                        "importedReduction": {"≤sW", "≤W"},
                        "ambientFactorization": {"ambient"},
                        "computedClosure": {"⊨ω", "⊭ω", "≤W"}}
    GLYPHS = ("→", "←", "⇒", "⇐", "⇔", "->", "<-", "=>", "<=>")
    for dot_name, dot_text_ in ([("ambient-factorizations", to_dot(catalog))]
                                + [(vn, view_dot(vn, vw)) for vn, vw in fam_views.items()]):
        for lab in re.findall(r'label="([^"]*)"', dot_text_):
            if any(g in lab for g in GLYPHS):
                problems.append(f"DOT {dot_name} label {lab!r} contains a directional "
                                "glyph; direction belongs to drawn arrowheads only")
    for vname, view in fam_views.items():
        for ed in view["edges"] + [e for cl in view.get("clusters", {}).values()
                                   for e in cl["edges"]]:
            lab = ed.get("label", "")
            allowed = LABELS_BY_FAMILY.get(ed.get("family"))
            if allowed is not None and lab not in allowed:
                problems.append(f"view {vname} edge label {lab!r} outside the closed "
                                f"label set of family {ed.get('family')!r}")
            if any(g in lab for g in GLYPHS):
                problems.append(f"view {vname} edge label {lab!r} contains a directional "
                                "glyph; direction belongs to drawn arrowheads only")
    for vname, view in fam_views.items():
        vpath = views_dir / vname / "graph.json"
        if not vpath.exists():
            problems.append(f"view file missing: {vname}")
            continue
        if json.loads(vpath.read_text()) != json.loads(
                json.dumps(view, sort_keys=True)):
            problems.append(f"view {vname} JSON does not match recomputation")
        dot = (views_dir / vname / "graph.dot").read_text()
        # a concept enclosure contributes its internal calibration edges and its
        # variant nodes to the drawing, and removes the concept's own plain node
        cl_edge_count = sum(len(cl["edges"])
                            for cl in view.get("clusters", {}).values())
        cl_variant_count = len({vn for cl in view.get("clusters", {}).values()
                                for vn in cl["variants"]})
        drawn_nodes = (len(view["nodes"]) - len(view.get("clusters", {}))
                       + cl_variant_count)
        if dot.count(" -> ") != len(view["edges"]) + cl_edge_count:
            problems.append(f"view {vname} DOT/JSON edge counts disagree")
        # every DOT edge endpoint must be a declared node — otherwise Graphviz would
        # invent nodes and the rendered SVG would disagree with the canonical JSON
        declared = set(view["nodes"])
        for ed in view["edges"]:
            src = ed.get("lhsConcept") or ed.get("lhs") or ed.get("exactLhs")
            tgt = ed.get("rhsConcept") or ed.get("rhs") or ed.get("exactRhs")
            for x in (src, tgt):
                if x not in declared:
                    problems.append(f"view {vname} edge endpoint {x!r} not a declared node")
        svgp = views_dir / vname / "graph.svg"
        if svgp.exists():
            svg = svgp.read_text()
            if (svg.count('class="node"') != drawn_nodes
                    or svg.count('class="edge"') != len(view["edges"]) + cl_edge_count):
                problems.append(f"view {vname} SVG node/edge counts disagree with JSON/DOT")
    ambient_svg = zoo_dir(root) / "ambient-factorizations.svg"
    ag = catalog.get("ambientGraph", {})
    if ambient_svg.exists():
        svg = ambient_svg.read_text()
        aedges = ag.get("edges", [])
        apairs = sum(1 for e in aedges
                     if (e["target"], e["source"]) in
                        {(x["source"], x["target"]) for x in aedges}
                     and e["source"] < e["target"])
        if (svg.count('class="node"') != len(ag.get("nodes", []))
                or svg.count('class="edge"') != len(aedges) - apairs):
            problems.append("ambient SVG node/edge counts disagree with the catalog "
                            "graph (antiparallel pairs draw once, double-headed)")
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
    # antiparallel pairs (exact-direction relative certificates) draw once, double-headed,
    # with BOTH certificates in the tooltip — a display merge, records stay canonical
    pairs = {(e["source"], e["target"]): e for e in graph["edges"]}
    seen = set()
    for e in graph["edges"]:
        k = (e["source"], e["target"])
        if k in seen:
            continue
        rk = (k[1], k[0])
        other = pairs.get(rk)
        if other is not None and rk not in seen and k != rk:
            tooltip = f'{e["certificate"]} / {other["certificate"]}'
            extra = ", dir=both"
            seen.add(rk)
        else:
            tooltip = e["certificate"]
            extra = ""
        seen.add(k)
        lines.append(f'  "{dot_escape(e["source"])}" -> "{dot_escape(e["target"])}" '
                     f'[label="{AMBIENT_EDGE_LABEL}", '
                     f'tooltip="{dot_escape(tooltip)}"{extra}];')
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


def principles_section(catalog: dict) -> str:
    """The definitions block: what each concept-level item asserts, right at the top.
    Statements are typed registry data (the required rm_concept `statement` field),
    never prose invented at render time."""
    items = "\n".join(
        f'<dt><strong>{html.escape(c["display"]["label"])}</strong> — '
        f'<code>{html.escape(c["id"])}</code></dt>'
        f'<dd>{html.escape(c["statement"])}</dd>'
        for c in catalog.get("concepts", []))
    return f"""<section id="principles"><h2>The principles</h2>
<p><em>What each concept-level item asserts. Exact Lean interfaces, presentation
caveats, and per-variant forms are in the <a href="#concepts-sec">concepts</a> and
<a href="#variants-sec">variants</a> sections.</em></p>
<dl class="principles">
{items}
</dl></section>"""


def site_html(catalog: dict, have_svg: bool, dot_text: str,
              view_svgs: set[str] | None = None) -> str:
    deps = catalog["dependencies"]
    e = html.escape
    view_svgs = view_svgs or set()
    case_study_href = ("https://github.com/cameronfreer/reverse-mathlib/blob/main/"
                       "docs/hall-efilc-case-study.md")
    case_study_concepts = {
        "reverse-mathlib:wkl",
        "reverse-mathlib:explicitFiniteInverseLimitCompactness",
        "reverse-mathlib:countableHall",
    }
    case_study_facts = {"wklEfilcOmega", "efilcHallOmega", "rca0CoreWklOmega"}

    def case_study_link(record_id: str) -> str:
        if record_id not in case_study_concepts | case_study_facts:
            return ""
        return (f'<p class="meta"><a data-case-study="hall-efilc" '
                f'href="{case_study_href}">Hall–EFILC case study</a></p>')

    def gloss(text: str, cap: int = 100) -> str:
        """Lead-in label for a summary line: the first clause of the full text, which
        always remains one click away — progressive disclosure, never information loss."""
        t = (text or "").split(": ", 1)[0].split(". ", 1)[0]
        if len(t) > cap:
            t = t[:cap - 1].rstrip() + "…"
        return t

    def note_html(text: str | None) -> str:
        if not text:
            return "<em>unknown</em>"
        return f"{e(text)} <em>[claimed, UNVERIFIED]</em>"

    def section(sec_id: str, title: str, total: int, inner: str, note: str = "") -> str:
        return (f'<section data-sec id="{sec_id}"><h2>{title} '
                f'<span class="scount">({total})</span></h2>\n{note}{inner}</section>')

    def graph_panel(title: str, styling: str, comment: str, nodes_n: int | str,
                    edge_items: str, edges_n: int, svg_name: str | None,
                    dot_href: str, json_href: str, open_: bool = False) -> str:
        if svg_name:
            fig = (f'<figure class="graph"><img src="{e(svg_name)}" '
                   f'alt="{e(title)}: directed graph with {e(str(nodes_n))} nodes and '
                   f'{edges_n} edges"/></figure>')
        else:
            fig = ("<p><em>(graph image rendered when Graphviz is available at build "
                   "time; the edge-detail list below is the always-present accessible "
                   "form)</em></p>")
        return f"""<details class="graphpanel"{" open" if open_ else ""}><summary><strong>{e(title)}</strong>
({nodes_n} nodes, {edges_n} edges; {e(styling)})</summary>
<p><em>{e(comment)}</em></p>
{fig}
<details><summary>Edge details (accessible list; families distinguished by label
text and line style, never by color alone)</summary><ul>{edge_items}</ul></details>
<p><small>Download: <a href="{e(dot_href)}">DOT</a> · <a href="{e(json_href)}">JSON</a></small></p>
</details>"""

    def view_edge_items(view: dict) -> str:
        items = []
        for ed in view["edges"]:
            # an enclosed intra-concept calibration reads at VARIANT level — its
            # accessible headline must never collapse to `concept ⊨ω concept`
            enclosed = bool(ed.get("lhsConcept")) and \
                ed.get("lhsConcept") == ed.get("rhsConcept")
            if enclosed:
                src, tgt = ed.get("exactLhs"), ed.get("exactRhs")
            else:
                src = ed.get("lhsConcept") or ed.get("lhs") or ed.get("exactLhs")
                tgt = ed.get("rhsConcept") or ed.get("rhs") or ed.get("exactRhs")
            detail = "; ".join(
                f"{k}: {ed[k]}" for k in ("family", "kind", "fact", "record", "source",
                                          "id", "relation", "premiseFamily", "degree",
                                          "scope", "notion", "status", "revision",
                                          "theorem", "exactLhs", "exactRhs")
                if ed.get(k))
            if ed.get("contexts"):
                detail += "; contexts: " + ", ".join(ed["contexts"])
            if ed.get("certificates"):
                detail += "; certificates: " + ", ".join(
                    str(c) for c in ed["certificates"] if c)
            if ed.get("derivationText"):
                detail += (f"; derivation: {ed['derivationText']}"
                           f"; premises cited: {', '.join(ed.get('leaves', []))}")
            if ed.get("records"):
                detail += "; records (both directions): " + ", ".join(ed["records"])
            if ed.get("derivation") == "strongImpliesOrdinary":
                detail += ("; one direction certified strong (≤sW) — the filled "
                           "arrowhead — and shown here at the ordinary notion by the "
                           "explicit weakening ≤sW ⇒ ≤W; the open arrowhead direction "
                           "is certified ordinary only")
            # the label already encodes the connector (⊨ω →, ≤sW, ⇔, …); fall back to a
            # bare arrow only when a view supplies none
            conn = ed.get("label") or ("⇔" if ed.get("bidirectional") else "→")
            items.append(f"<li><code>{e(str(src))}</code> {e(conn)} "
                         f"<code>{e(str(tgt))}</code>"
                         f"<br/><small>{e(detail)}</small></li>")
        return "".join(items)

    views = build_family_views(catalog)

    def legend_html() -> str:
        def arrow(stroke: str, width: str, dash: str = "", head: str = "arrow",
                  both: bool = False, open_head: bool = False,
                  open_tail: bool = False) -> str:
            d = f' stroke-dasharray="{dash}"' if dash else ""
            tail_style = ('fill="none" stroke="#444" stroke-width="1.2"'
                          if open_tail else 'fill="#444"')
            left = (f'<path d="M8 1 L1 5 L8 9 z" {tail_style}/>' if both else "")
            if head == "tee":
                right = ('<line x1="43" y1="0.5" x2="43" y2="9.5" stroke="#444" '
                         'stroke-width="2.5"/>')
                x2 = "43"
            else:
                head_style = ('fill="none" stroke="#444" stroke-width="1.2"'
                              if open_head else 'fill="#444"')
                right = f'<path d="M38 1 L45 5 L38 9 z" {head_style}/>'
                x2 = "38"
            x1 = "8" if both else "1"
            return (f'<svg width="46" height="10" viewBox="0 0 46 10" aria-hidden="true">'
                    f'<line x1="{x1}" y1="5" x2="{x2}" y2="5" stroke="{stroke}" '
                    f'stroke-width="{width}"{d}/>{left}{right}</svg>')
        return f"""<div class="legend" role="img" aria-label="Graph legend: solid arrow =
ambient kernel-checked proof route; bold arrow = certified omega-model fact; bold
double-headed arrow = certified equivalence; bold arrow ending in a bar = certified
separation; dashed arrows = imported reductions at pinned revisions, filled head
certified strong, open head certified ordinary only; dashed double-headed arrow with one
filled and one open head = mutual ordinary reduction where the filled head marks the
direction also certified strong">
<span class="lg">{arrow("#444", "1.3")} ambient: kernel-checked proof route (not
strength)</span>
<span class="lg">{arrow("#444", "2.8")} ⊨ω: certified ω-model fact</span>
<span class="lg">{arrow("#444", "2.8", both=True)} ⊨ω: certified equivalence</span>
<span class="lg">{arrow("#444", "2.8", head="tee")} ⊭ω: certified separation
(countermodel)</span>
<span class="lg">{arrow("#444", "1.6", dash="5 3")} imported ≤sW reduction: filled
head (pinned, external)</span>
<span class="lg">{arrow("#444", "1.6", dash="5 3", open_head=True)} imported ≤W
reduction: open head (pinned, external)</span>
<span class="lg">{arrow("#444", "1.6", dash="5 3", both=True, open_head=True)} mutual
≤W: the filled end is additionally certified ≤sW; the open end is ordinary-only</span>
</div>"""

    def projection_section() -> str:
        v = views["concept-projection"]
        # intra-concept calibrations render inside their concept enclosure; their
        # accessible details (full variant ids, certificate, source fact) list right
        # alongside the external projection edges
        cluster_edges = [e for cl in v.get("clusters", {}).values()
                         for e in cl["edges"]]
        # an enclosure replaces its concept's plain node with the variant nodes it
        # contains, so the drawn-node count differs from the concept count
        displayed = (len(v["nodes"]) - len(v.get("clusters", {}))
                     + len({vn for cl in v.get("clusters", {}).values()
                            for vn in cl["variants"]}))
        panel = graph_panel(
            "Concept projection", "per-family line styles; no transitive closure; "
            "concept enclosures hold intra-concept calibrations at variant level",
            "orientation only — the exact merge and enclosure rules are in the "
            "projection fine print above",
            f"{len(v['nodes'])} concepts, {displayed} displayed",
            view_edge_items({**v, "edges": v["edges"] + cluster_edges}),
            len(v["edges"]) + len(cluster_edges),
            "concept-projection.svg" if "concept-projection" in view_svgs else None,
            "views/concept-projection/graph.dot", "views/concept-projection/graph.json",
            open_=True)
        fine_print = (f'<details class="fineprint"><summary>Projection fine print '
                      f'(exact merge and enclosure rules)</summary>'
                      f'<p>{e(v["comment"])}</p></details>')
        return (f'<h2 id="overview">Concept overview — a noncanonical, lossy, '
                f'direct-only projection</h2>\n'
                f'<p><em>One edge per direct evidence record, projected to concept '
                f'granularity for orientation only; the per-family graphs below are '
                f'canonical.</em></p>\n{fine_print}\n{legend_html()}\n{panel}')

    def canonical_graphs_section() -> str:
        ag = catalog.get("ambientGraph", {})
        ambient_items = "".join(
            f'<li><code>{e(ed["source"])}</code> ambient → '
            f'<code>{e(ed["target"])}</code>'
            f'<br/><small>kernel-checked relative certificate: '
            f'{e(ed["certificate"])}</small></li>'
            for ed in ag.get("edges", []))
        panels = [graph_panel(
            "Ambient factorizations", "solid edges; kernel-checked relative "
            "certificates — proof architecture, not strength",
            "kernel-checked relative certificates in unrestricted Lean over standard "
            "ℕ; ambient factorization, no RM semantic scope",
            len(ag.get("nodes", [])), ambient_items, len(ag.get("edges", [])),
            "ambient-factorizations.svg" if have_svg else None,
            "ambient-factorizations.dot", "views/ambient-standard/graph.json")]
        for vname, title, styling in (
                ("omega-facts", "Certified ω facts", "bold edges; certified"),
                ("imported-reductions", "Imported reductions",
                 "dashed edges; external evidence")):
            v = views[vname]
            panels.append(graph_panel(
                title, styling, v["comment"], len(v["nodes"]), view_edge_items(v),
                len(v["edges"]), f"{vname}.svg" if vname in view_svgs else None,
                f"views/{vname}/graph.dot", f"views/{vname}/graph.json"))
        return ('<h2 id="graphs">Canonical graphs (one per evidence family — never '
                'flattened into one)</h2>\n'
                '<p><em>Line styles as in the legend under the concept overview '
                'above.</em></p>\n'
                + "\n".join(panels))

    def facts_section() -> str:
        facts = [f_ for f_ in catalog.get("facts", []) if f_.get("evidence")]
        if not facts:
            return ""
        cards = []
        for f_ in facts:
            lhs = "+".join(f_.get("lhs", []))
            rhs = "+".join(f_.get("rhs", []))
            arrow = {"equivalence": "⇔", "implication": "⇒",
                     "nonImplication": "⊭"}.get(f_["kind"], "⇒")
            ctx = f_.get("context", {})
            ctx_ids = sorted({ev["context"] for ev in f_["evidence"]
                              if ev.get("context")})
            ctx_links = ", ".join(f'<a href="#ctx-{e(c)}"><code>{e(c)}</code></a>'
                                  for c in ctx_ids)
            ev_items = (
                f"<li>base <code>{e(str(ctx.get('base', '')))}</code> · "
                f"context {ctx_links}</li>" + "".join(
                    f"<li>certificate <code>{e(ev['certificate'])}</code> "
                    f"[context <code>{e(ev['context'])}</code>]"
                    + (f" — {e(ev['note'])}" if ev.get("note") else "") + "</li>"
                    for ev in f_["evidence"]))
            note_block = f"<p>{e(f_['note'])}</p>" if f_.get("note") else ""
            study_link = case_study_link(f_["id"])
            cards.append(f"""<div class="card" data-family="certified">
<h3><code>{e(lhs)}</code> {arrow} <code>{e(rhs)}</code>
<span class="tag">{e(f_['kind'])}</span> <span class="tag">kernelChecked</span>
<span class="tag">scope {e(str(ctx.get('scope', '')))}</span></h3>
<p class="meta"><code>{e(f_['id'])}</code></p>
<details><summary>base, context, certifications, note, and case study</summary><ul>{ev_items}</ul>{note_block}{study_link}</details>
</div>""")
        return section(
            "facts-sec", "Certified semantic facts", len(cards), "\n".join(cards),
            "<p><em>The principal conclusions, certified by typed semantic "
            "certificates against registered contexts (exact context statuses in the "
            "<a href=\"#reference\">reference</a>). A nonimplication (⊭) fact is a "
            "countermodel-witnessed model-class separation — never a turnstile "
            "underivability claim, never a closure edge.</em></p>\n")

    def concept_index() -> str:
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
            study_link = case_study_link(c["id"])
            cards.append(f"""<details class="card">
<summary><strong>{e(gloss(c['description']))}</strong> — <code>{e(c['id'])}</code></summary>
<p>{e(c['statement'])}</p>
<p class="meta">{e(c['description'])}</p>
{refs_block}{study_link}</details>""")
        return section("concepts-sec", "Concepts", len(cards), "\n".join(cards))

    def variant_index() -> str:
        cards = []
        for v in catalog["statementVariants"]:
            cards.append(f"""<details class="card">
<summary><strong>{e(gloss(v['description']))}</strong> — <code>{e(v['id'])}</code>
<span class="tag">{e(v['layer'])}</span></summary>
<p>{e(v['description'])}</p>
<dl>
<dt>concept</dt><dd><code>{e(v['concept'])}</code></dd>
<dt>Lean interface</dt><dd><code>{e(v['interface'] or 'none')}</code></dd>
<dt>module</dt><dd><code>{e(v.get('interfaceModule') or '—')}</code></dd>
</dl></details>""")
        return section("variants-sec", "Statement variants and Lean interfaces",
                       len(cards), "\n".join(cards))

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

    def ports_section() -> str:
        cards = []
        for p_ in catalog["ports"]:
            cards.append(f"""<details class="card" data-family="ambient">
<summary><strong>{e(p_['display']['relation'])}</strong> — <code>{e(p_['id'])}</code>
<span class="tag">{len(p_['evidence'])} evidence</span></summary>
<dl>
<dt>mathlib</dt><dd><code>{e(p_['mathlibDecl'] or 'none')}</code></dd>
<dt>target variant</dt><dd><code>{e(p_['target'])}</code></dd>
<dt>port statement</dt><dd><code>{e(p_['portDecl'] or 'none')}</code></dd>
<dt>literature note</dt><dd>{note_html(p_.get('literatureNote'))}</dd>
</dl>
<h4>Evidence</h4>
{evidence_items(p_)}
<p>{e(p_['note'])}</p>
</details>""")
        return section(
            "ports-sec", "Ports (proof routes)", len(cards), "\n".join(cards),
            "<p><em>Mined proof architecture: how a mathlib proof factors, with "
            "input-access records — routes, not classifications.</em></p>\n")

    def imports_section() -> str:
        imps = catalog.get("importedReductions", [])
        if not imps:
            return ""
        labels = {"strongWeihrauch": "≤sW", "weihrauch": "≤W"}
        cards = []
        for r in imps:
            loc = r["local"]
            label = labels.get(loc["notion"], loc["notion"])
            lshort = loc["lhs"].split(":", 1)[-1]
            rshort = loc["rhs"].split(":", 1)[-1]
            trust = (f"theorem <code>{e(r['theorem'] or '(none)')}</code>; mechanism "
                     f"<code>{e(r['mechanism'] or '(none)')}</code>")
            down = (f"<dt>downgraded</dt><dd>{e(r['downgraded'])}</dd>"
                    if r.get("downgraded") else "")
            cards.append(f"""<details class="card" data-family="imported">
<summary><strong><code>{e(lshort)}</code> {e(label)} <code>{e(rshort)}</code></strong>
— <code>{e(r['id'])}</code> <span class="tag">{e(r['status'])}</span></summary>
<dl>
<dt>local (resolved)</dt><dd><code>{e(loc['lhs'])}</code> ≤ <code>{e(loc['rhs'])}</code> [{e(loc['notion'])}, {e(r['degree'])}]</dd>
<dt>external (as ingested)</dt><dd><code>{e(r['external']['lhs'])}</code> ≤ <code>{e(r['external']['rhs'])}</code> [notion <code>{e(r['external']['notion'])}</code>, namespace <code>{e(r['namespace'])}</code>]</dd>
<dt>source</dt><dd><code>{e(r['repository'])}</code> @ <code>{e(r['revision'])}</code></dd>
<dt>checking</dt><dd>{trust}</dd>{down}
<dt>note</dt><dd>{e(r['note'])}</dd>
</dl></details>""")
        return section(
            "imports-sec", "Imported reductions", len(cards), "\n".join(cards),
            "<p><em>Checked in an external machine-model repository at a pinned "
            "revision and ingested as external evidence — never Lean axioms, never "
            "certified counts; records without complete validated trust data are "
            "downgraded to reported.</em></p>\n")

    def computed_section() -> str:
        v = views.get("computed-closure", {})
        derived = [e for e in v.get("edges", []) if e.get("family") == "computedClosure"]
        if not derived:
            return ""
        cards = []
        for d in derived:
            leaves = "".join(f"<li><code>{e(l)}</code></li>" for l in d["leaves"])
            cards.append(f"""<details class="card" data-family="computed">
<summary><strong><code>{e(d['lhs'])}</code> {e(d['label'])} <code>{e(d['rhs'])}</code></strong>
— <code>{e(d['id'])}</code> <span class="tag">{e(d['status'])}</span></summary>
<dl>
<dt>derivation</dt><dd><code>{e(d['derivationText'])}</code></dd>
<dt>premises cited</dt><dd><ul>{leaves}</ul></dd>
<dt>premise family</dt><dd>{e(d['premiseFamily'])} ({e(d['relation'])})</dd>
<dt>note</dt><dd>{e(d['note'])}</dd>
</dl></details>""")
        panel = graph_panel(
            "Computed closure (view-only)",
            "dotted edges — open heads for derived implications/reductions, tees "
            "for derived separations; derived, never certified",
            v["comment"], len(v["nodes"]), view_edge_items(v), len(v["edges"]),
            "computed-closure.svg" if "computed-closure" in view_svgs else None,
            "views/computed-closure/graph.dot", "views/computed-closure/graph.json")
        return section(
            "computed-sec", "Computed closure (view-only)", len(cards),
            panel + "\n" + "\n".join(cards),
            "<p><em>Derived edges, each the conclusion of an explicit typed proof "
            "<strong>tree</strong> — premise orientation is part of the term, and every "
            "rule node is typechecked against family-specific rule vocabularies and "
            "exact endpoint composition. No generic reachability: these derivations are "
            "hand-declared, never searched. Status <code>computedView</code>: never "
            "certified, never imported, never a registered fact, and absent from the "
            "canonical direct-only graphs and every certified count.</em></p>\n")

    def backend_section() -> str:
        bes = catalog.get("backendEvidence", [])
        if not bes:
            return ""
        cards = []
        for r in bes:
            src = r["source"]
            chk = r["checking"]
            deps = src["dependencies"]
            trust = (f"mechanism <code>{e(chk.get('mechanism') or '(none)')}</code>; "
                     f"audit <code>{e(chk.get('audit') or '(none)')}</code>; allowed "
                     f"axioms <code>{e(', '.join(chk.get('allowedAxioms', [])))}</code>; "
                     f"theorem <code>{e(r.get('theorem') or '(none)')}</code>; export "
                     f"<code>{e(r['export'])}</code>")
            down = (f"<dt>downgraded</dt><dd>{e(r['downgraded'])}</dd>"
                    if r.get("downgraded") else "")
            cards.append(f"""<details class="card" data-family="backend">
<summary><strong>[{e(r['kind'])}]</strong> <code>{e(r['id'])}</code>
<span class="tag">{e(r['status'])}</span></summary>
<dl>
<dt>statement</dt><dd>{e(r['display']['rendered'])}</dd>
<dt>source</dt><dd><code>{e(src['repository'])}</code> — export/check
<code>{e(src['exportRevision'])}</code>, artifact
<code>{e(src['artifactRevision'])}</code>
(<a href="https://github.com/{e(src['repository'])}/blob/{e(src['artifactRevision'])}/evidence/rmlib-bridge-evidence.json">raw artifact</a>;
vendored at <code>{e(src['artifactPath'])}</code>)</dd>
<dt>dependencies</dt><dd>reverse-mathlib <code>{e(deps['reverse-mathlib'])}</code>;
Foundation <code>{e(deps['Foundation'])}</code>; mathlib
<code>{e(deps['mathlib'])}</code>; toolchain <code>{e(src['toolchain'])}</code></dd>
<dt>checking</dt><dd>{trust}</dd>{down}
</dl></details>""")
        return section(
            "backend-sec", "Backend evidence", len(cards), "\n".join(cards),
            "<p><em>External checked backend records (the ω-semantics bridge), with "
            "interface fingerprints recomputed locally at ingestion. Kept distinct: "
            "checked forward context realization (one-way — never unrestricted "
            "semantic RCA₀ claims); checked unconditional statement adapters; "
            "converse context adequacy still pending; the nonderivability is "
            "calculus-relative with the standard-calculus comparison still pending. "
            "No local certified fact, no graph edge, no port, no closure edge; the "
            "validated semantic-countermodel record contributes exactly the "
            "backend-qualified all-model scoped result.</em></p>\n")

    def corpus_section() -> str:
        corpus = catalog.get("corpus")
        if not corpus:
            return ""
        cards = []
        for a in corpus.get("audits", []):
            cards.append(f"""<details class="card" data-family="corpus">
<summary><strong>{e(gloss(a['scope'], 80))}</strong> — <code>{e(a['id'])}</code>
<span class="tag">audit</span></summary>
<dl><dt>scope</dt><dd>{e(a['scope'])}</dd>
<dt>outcome</dt><dd><strong>{e(a['outcome'])}</strong></dd></dl></details>""")
        for c in corpus.get("claims", []):
            subjects = ", ".join(f"<code>{e(x)}</code> <span class=\"tag\">concept</span>"
                                 for x in c.get("concepts", []))
            if c["wordingKind"] == "absent":
                wording = "<em>wording not captured; locator only</em>"
            else:
                wording = f"<em>({e(c['wordingKind'])})</em> “{e(c['wording'])}”"
            cards.append(f"""<details class="card" data-family="corpus">
<summary><strong>{e(gloss(c['normalizedClaim'], 80))}</strong> — <code>{e(c['id'])}</code>
<span class="tag">{e(c['status'])}</span></summary>
<dl>
<dt>provenance</dt><dd><code>{e(c['source'])}</code>:“{e(c['locator'])}”</dd>
<dt>presentation family</dt><dd><code>{e(c['presentationFamily'])}</code></dd>
<dt>subjects</dt><dd>{subjects}</dd>
<dt>source wording</dt><dd>{wording}</dd>
<dt>normalized claim</dt><dd>{e(c['normalizedClaim'])}</dd>
</dl></details>""")
        for b in corpus.get("bridges", []):
            cards.append(f"""<details class="card" data-family="corpus">
<summary><strong>{e(gloss(b['requirement'], 80))}</strong> — <code>{e(b['id'])}</code>
<span class="tag">MISSING — unproved required bridge</span></summary>
<dl>
<dt>from family</dt><dd><code>{e(b['fromFamily'])}</code></dd>
<dt>to exact target</dt><dd><code>{e(b['target']['id'])}</code> ({e(b['target']['kind'])})</dd>
<dt>requires</dt><dd>{e(b['requirement'])}</dd>
</dl></details>""")
        return section(
            "corpus-sec", "Corpus audits", len(cards), "\n".join(cards),
            "<p><em>Pinned external classification claims — scoped literature "
            "findings, a separate family: never fact-graph edges, never certified "
            "counts. An absence finding means <strong>not found in this pinned "
            "corpus snapshot</strong>, never a mathematical negation; a "
            "<strong>MISSING</strong> bridge is an unproved required bridge, never "
            "evidence that no bridge exists. Pinned sources and presentation "
            "families are in the <a href=\"#reference\">reference</a>.</em></p>\n")

    def reference_section() -> str:
        parts = ['<h2 id="reference">Reference</h2>',
                 "<p><em>Dictionaries cited by the records above — lookup material, "
                 "not new claims.</em></p>", "<h3>Semantic contexts</h3>"]
        for c in catalog.get("semanticContexts", []):
            parts.append(
                f'<div class="refitem" id="ctx-{e(c["id"])}"><code>{e(c["id"])}</code> '
                f'<span class="tag">base {e(str(c.get("base", "")))} · scope '
                f'{e(str(c.get("scope", "")))}</span><br/>{e(c["description"])} '
                f'— context predicate <code>{e(c.get("contextDecl") or "")}</code></div>')
        notions = catalog.get("reducibilityNotions", [])
        if notions:
            parts.append("<h3>Reducibility notions</h3>")
            for n_ in notions:
                parts.append(f'<div class="refitem"><code>{e(n_["id"])}</code><br/>'
                             f'{e(n_["description"])}</div>')
        corpus = catalog.get("corpus", {})
        if corpus.get("sources"):
            parts.append("<h3>Pinned corpus sources</h3><ul>")
            for src in corpus["sources"]:
                parts.append(f"<li><code>{e(src['namespace'])}</code> @ "
                             f"<code>{e(src['pin'])}</code> — {e(src['description'])}</li>")
            parts.append("</ul>")
        if corpus.get("presentationFamilies"):
            parts.append("<h3>Presentation families</h3><ul>")
            for f_ in corpus["presentationFamilies"]:
                parts.append(f"<li><code>{e(f_['id'])}</code> — {e(f_['description'])}</li>")
            parts.append("</ul>")
        return "\n".join(parts)

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
.principles dt {{ margin-top: 0.55rem; }}
.principles dd {{ margin: 0.15rem 0 0 1.2rem; max-width: 62rem; }}
.banner {{ background: #fff6df; border: 1px solid #e6cf8a; padding: 0.75rem 1rem;
           border-radius: 6px; overflow-wrap: anywhere; }}
.banner p {{ margin: 0.3rem 0; }}
figure.graph {{ margin: 0.75rem 0; text-align: center; }}
figure.graph img {{ max-width: 100%; height: auto; }}
figcaption {{ color: #666; font-size: 0.8rem; }}
.scroll {{ overflow-x: auto; }}
details summary {{ cursor: pointer; color: #666; font-size: 0.85rem; }}
details p {{ font-size: 0.85rem; color: #444; }}
details.card > summary, details.graphpanel > summary {{ color: #1a1a1a;
    font-size: 0.95rem; overflow-wrap: anywhere; }}
details.graphpanel {{ background: #fff; border: 1px solid #e2e2e2;
    border-radius: 6px; padding: 0.6rem 0.9rem; margin: 0.75rem 0; }}
.meta {{ color: #555; font-size: 0.85rem; overflow-wrap: anywhere; }}
.refitem {{ background: #fff; border: 1px solid #e2e2e2; border-radius: 6px;
    padding: 0.6rem 0.9rem; margin: 0.5rem 0; font-size: 0.9rem;
    overflow-wrap: anywhere; }}
.scount {{ font-size: 0.8rem; color: #666; font-weight: normal; }}
.legend {{ display: flex; flex-direction: column; gap: 0.3rem; font-size: 0.78rem;
    color: #555; background: #fff; border: 1px solid #e2e2e2; border-radius: 6px;
    padding: 0.5rem 0.9rem; margin: 0.5rem 0; }}
.legend .lg {{ display: flex; align-items: center; gap: 0.45rem; }}
.legend svg {{ flex: none; }}
footer {{ color: #666; font-size: 0.8rem; margin-top: 2.5rem;
          border-top: 1px solid #ddd; padding-top: 0.75rem;
          overflow-wrap: anywhere; }}
a {{ color: #205ea6; }}
</style></head><body><main>
<h1>reverse-mathlib atlas</h1>
<p><a href="https://github.com/cameronfreer/reverse-mathlib">cameronfreer/reverse-mathlib</a></p>
<div class="banner"><p><strong>Honesty note:</strong> this atlas displays five families
of evidence, permanently distinct, plus a computed closure that is a view, not
evidence. No <code>RCA₀ ⊢ …</code> turnstile theorem exists at any scope; scopes are
never promoted, and derived closure results are computed, never registered.</p>
<details><summary>Full epistemics statement (what each family is and is not)</summary>
<p>Every edge in the <em>ambient factorizations</em> panel is a kernel-checked relative
certificate in unrestricted Lean over standard ℕ — ambient factorization, proof
architecture, not strength. The <em>certified facts</em> are kernel-checked over every
Turing ideal; the identification of Turing ideals with RCA₀'s ω-models is
literature-backed. The <em>backend</em> records come from the external checked
ω-semantics bridge to FormalizedFormalLogic/Foundation: the forward context
realization (every Turing ideal satisfies an explicit semantic RCA₀ theory on
ω-structures) and exact statement adapters for ŴKL/EFILC/Hall are <strong>checked</strong>
at pinned revisions with interface fingerprints recomputed locally, while converse
context adequacy and the backend calculus's standard-calculus comparison remain
pending. The <em>imported reductions</em> are Weihrauch reductions checked in a separate
machine-model repository at pinned revisions and ingested as external evidence, never
axioms. The <em>corpus</em> holds reported literature findings at pinned snapshots, with
missing presentation bridges named explicitly; an absence finding means not found in
the pinned snapshot, never a mathematical negation. The <em>computed closure</em> is a
view: typed proof trees over the certified and imported leaves, hand-declared and
typechecked, never registered and never counted. The <em>concept projection</em> is a
noncanonical, lossy, direct-only overview; the per-family graphs are canonical, and
they are never flattened into one.</p></details></div>
<p class="summary"><strong>Checked scoped results:</strong>
ω-model: {scoreboard_cell(catalog, 'omegaModels')} ·
all-model: {scoreboard_cell(catalog, 'allModels')} ·
syntactic: {scoreboard_cell(catalog, 'provability')}</p>
<p class="summary"><strong>Counts (each family separate):</strong>
{len(catalog['concepts'])} concepts · {len(catalog['statementVariants'])} variants ·
{len([f for f in catalog.get('facts', []) if f.get('evidence')])} certified facts
(ω-model) · {len(catalog['ports'])} ports ·
{len(catalog.get('importedReductions', []))} imported reductions ·
{len(catalog.get('backendEvidence', []))} backend evidence records ·
{len([x for x in views.get('computed-closure', {}).get('edges', []) if x.get('family') == 'computedClosure'])} computed edges (view-only) ·
{len(catalog.get('corpus', {}).get('claims', []))} corpus claims ·
{len(catalog.get('corpus', {}).get('bridges', []))} missing bridges</p>
{principles_section(catalog)}
<p class="filters">Filter:
<input type="text" id="ftext" placeholder="text, ids, theorems…" oninput="applyFilter()">
<select id="ffam" onchange="applyFilter()"><option value="">all families</option>
<option>ambient</option><option>certified</option><option>imported</option>
<option>backend</option><option>computed</option><option>corpus</option></select>
<noscript>(filtering needs JavaScript; all content below is fully visible without
it)</noscript></p>
<nav class="toc"><strong>Contents:</strong>
<a href="#principles">Principles</a> ·
<a href="#overview">Overview</a> ·
<a href="#facts-sec">Certified facts</a> ·
<a href="#graphs">Canonical graphs</a> ·
<a href="#concepts-sec">Concepts</a> ·
<a href="#variants-sec">Variants</a> ·
<a href="#ports-sec">Ports</a> ·
<a href="#imports-sec">Imported reductions</a> ·
<a href="#backend-sec">Backend evidence</a> ·
<a href="#computed-sec">Computed closure</a> ·
<a href="#corpus-sec">Corpus audits</a> ·
<a href="#reference">Reference</a></nav>
{projection_section()}
{facts_section()}
{canonical_graphs_section()}
{concept_index()}
{variant_index()}
{ports_section()}
{imports_section()}
{backend_section()}
{computed_section()}
{corpus_section()}
{reference_section()}
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
  document.querySelectorAll('section[data-sec]').forEach(function (s) {{
    var cards = s.querySelectorAll('.card'), shown = 0;
    cards.forEach(function (c) {{ if (c.style.display !== 'none') shown += 1; }});
    var badge = s.querySelector('.scount');
    if (badge) {{
      badge.textContent = (shown === cards.length)
        ? '(' + cards.length + ')'
        : '(' + shown + ' of ' + cards.length + ' shown)';
    }}
    s.style.display = (cards.length > 0 && shown === 0) ? 'none' : '';
  }});
}}
</script>
</body></html>
"""



# ---------------------------------------------------------------------------
# Typed computed closure (view-only)
#
# A derivation is a typed PROOF TREE, never a flat premise list: premise
# orientation is part of the term, and every rule node must compose at the exact
# endpoint ids. Rule vocabularies are FAMILY-SPECIFIC — a rule is looked up in
# its family's table, so applying a Weihrauch weakening to an ω fact (or vice
# versa) fails closed. There is NO generic reachability: the derivations below
# are an explicit, hand-declared list, and nothing computes a transitive closure.
# Conclusions carry status `computedView`, never `kernelChecked`/`importedChecked`,
# they live only under `views/` (the canonical catalog stays direct-only and
# needs no schema change), and they contribute nothing to any certified count.
# ---------------------------------------------------------------------------

# Family-specific relation vocabularies. A judgment's relation must be in its
# family's set, at every node.
FAMILY_RELATIONS = {
    "certifiedOmegaFact": {"implication", "equivalence", "nonImplication"},
    "importedReduction": {"strongWeihrauch", "weihrauch"},
}

# Family-specific rule vocabularies (arity included). Leaves are family-typed too.
# countermodelPullback is the ONLY rule that touches separations: from Base ⊭ P and
# Q → P, conclude Base ⊭ Q (the countermodel transports along the implication's
# contrapositive). Transitivity NEVER applies to separations.
FAMILY_RULES = {
    "certifiedOmegaFact": {"equivalenceElimForward": 1, "equivalenceElimReverse": 1,
                           "transitivity": 2, "countermodelPullback": 2},
    "importedReduction": {"strongToOrdinary": 1, "transitivity": 2},
}
LEAF_RULES = {"fact": "certifiedOmegaFact", "reduction": "importedReduction"}

# The declared derivations. Each is a proof term; the conclusion is *computed*,
# then checked against the declared endpoints — the declaration never overrides
# what the tree proves.
COMPUTED_DERIVATIONS = [
    {
        "id": "computed.omega.wklImpliesHall",
        "term": ["transitivity",
                 ["equivalenceElimForward", ["fact", "wklEfilcOmega"]],
                 ["fact", "efilcHallOmega"]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "implication",
            "lhs": "wkl.binaryTree.turingIdealOmega",
            "rhs": "countableHall.oneSidedInjective.enumeratedCandidates."
                   "turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "WKLω → Hallω: the certified equivalence used forward, then the "
                "certified EFILCω → Hallω implication. A display derivation only — "
                "Hall's reversal remains an audited open question, and no fact is "
                "registered.",
    },
    {
        "id": "computed.weihrauch.hallLeWkl",
        "term": ["transitivity",
                 ["strongToOrdinary", ["reduction", "hall_le_efilc.strongWeihrauch"]],
                 ["reduction", "efilc_le_wkl.weihrauch"]],
        "expect": {
            "family": "importedReduction", "relation": "weihrauch",
            "lhs": "hall.oneSidedRelationEnumerator",
            "rhs": "wkl.streamCodedTree",
            "contexts": None},
        "note": "Hall ≤W WKL: the strong Hall ≤sW EFILC weakened to the ordinary "
                "notion, then composed with the imported EFILC ≤W WKL. Ordinary "
                "notion only — the composition never inherits strength.",
    },
    {
        "id": "computed.omega.boundedKonigImpliesHall",
        "term": ["transitivity",
                 ["equivalenceElimForward", ["fact", "boundedKonigWklOmega"]],
                 ["transitivity",
                  ["equivalenceElimForward", ["fact", "wklEfilcOmega"]],
                  ["fact", "efilcHallOmega"]]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "implication",
            "lhs": "wkl.explicitlyBoundedTree.internalBoundFunction.turingIdealOmega",
            "rhs": "countableHall.oneSidedInjective.enumeratedCandidates."
                   "turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "bounded-Kőnigω → Hallω: the certified bounded-Kőnig ⇔ WKL "
                "equivalence used forward, then the WKLω → Hallω chain. A display "
                "derivation only — no fact is registered.",
    },
    {
        "id": "computed.omega.recCoreNotBoundedKonig",
        "term": ["countermodelPullback",
                 ["fact", "rca0CoreWklOmega"],
                 ["equivalenceElimForward", ["fact", "boundedKonigWklOmega"]]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "nonImplication",
            "lhs": "rca0Core.turingIdealClosure.turingIdealOmega",
            "rhs": "wkl.explicitlyBoundedTree.internalBoundFunction.turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "RCA₀-core ⊭ω bounded-Kőnigω: the certified REC countermodel for "
                "binary WKL transported along bounded-Kőnig → WKL (the countermodel "
                "refutes the source of any implication into the refuted target). A "
                "display derivation only — no fact is registered.",
    },
    {
        "id": "computed.omega.recCoreNotEfilc",
        "term": ["countermodelPullback",
                 ["fact", "rca0CoreWklOmega"],
                 ["equivalenceElimReverse", ["fact", "wklEfilcOmega"]]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "nonImplication",
            "lhs": "rca0Core.turingIdealClosure.turingIdealOmega",
            "rhs": "efilc.explicitSequential.enumeratedFibers.turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "RCA₀-core ⊭ω EFILCω: the certified REC countermodel for binary WKL "
                "transported along EFILC → WKL (the reverse elimination of the "
                "certified equivalence). A display derivation only — no fact is "
                "registered.",
    },
    {
        "id": "computed.omega.matchingImpliesHall",
        "term": ["transitivity",
                 ["equivalenceElimForward", ["fact", "wklTwoRegularMatchingOmega"]],
                 ["transitivity",
                  ["equivalenceElimForward", ["fact", "wklEfilcOmega"]],
                  ["fact", "efilcHallOmega"]]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "implication",
            "lhs": "countableHall.twoRegularPerfectMatching."
                   "enumeratedNeighborhoods.turingIdealOmega",
            "rhs": "countableHall.oneSidedInjective.enumeratedCandidates."
                   "turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "2-regular matchingω → one-sided Hallω: the certified matching ⇔ WKL "
                "equivalence used forward, then the WKLω → Hallω chain. An "
                "intra-concept display derivation between the two countableHall "
                "presentations — NOT a presentation bridge: the recorded "
                "perfectMatchingToOneSidedOmega bridge (an exact correspondence, not "
                "a one-way ω implication) stays MISSING, and no fact is registered.",
    },
    {
        "id": "computed.omega.recCoreNotMatching",
        "term": ["countermodelPullback",
                 ["fact", "rca0CoreWklOmega"],
                 ["equivalenceElimForward", ["fact", "wklTwoRegularMatchingOmega"]]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "nonImplication",
            "lhs": "rca0Core.turingIdealClosure.turingIdealOmega",
            "rhs": "countableHall.twoRegularPerfectMatching."
                   "enumeratedNeighborhoods.turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "RCA₀-core ⊭ω 2-regular matchingω: the certified REC countermodel "
                "for binary WKL transported along matching → WKL (the forward "
                "elimination of the certified equivalence). A display derivation "
                "only — no fact is registered.",
    },
]


# Canonical direct-edge constructors. ONE definition per family, shared by the
# canonical views and by any view that displays a direct record (so a displayed
# premise never becomes a skinny duplicate missing its provenance).
OMEGA_EDGE_LABELS = {"equivalence": "⊨ω", "implication": "⊨ω",
                     # a certified separation: countermodel-witnessed, never an
                     # implication arrow; it enters closure only through the
                     # countermodelPullback rule, never through transitivity
                     "nonImplication": "⊭ω"}


def direct_omega_edge(f: dict) -> dict:
    """The canonical edge record for one certified ω fact."""
    return {"family": "certifiedOmegaFact", "fact": f["id"], "kind": f["kind"],
            "status": "kernelChecked",
            "bidirectional": f["kind"] == "equivalence",
            # non-directional labels: the DRAWN arrowheads carry direction (dir=both
            # for an equivalence, tee for a separation); a textual arrow beside an
            # edge fights the rendered one, so labels carry only the relation text
            "label": OMEGA_EDGE_LABELS[f["kind"]],
            "scope": f.get("context", {}).get("scope"),
            "base": f.get("context", {}).get("base"),
            "contexts": sorted({ev["context"] for ev in f.get("evidence", [])
                                if ev.get("context")}),
            "lhs": f["lhs"][0].split(":", 1)[-1],
            "rhs": f["rhs"][0].split(":", 1)[-1],
            "certificates": [ev["certificate"] for ev in f.get("evidence", [])]}


def direct_imported_edge(r: dict) -> dict:
    """The canonical edge record for one imported reduction."""
    notion = r["local"]["notion"]
    return {"family": "importedReduction", "record": r["id"],
            "label": {"strongWeihrauch": "≤sW", "weihrauch": "≤W"}.get(notion, notion),
            "notion": notion, "degree": r["degree"], "status": r["status"],
            "lhs": r["local"]["lhs"].split(":", 1)[-1],
            "rhs": r["local"]["rhs"].split(":", 1)[-1],
            "repository": r["repository"], "revision": r["revision"],
            "theorem": r.get("theorem"), "external": r["external"]}


class DerivationError(Exception):
    """A proof term that does not typecheck. Always fatal: a derivation that does
    not compose is never rendered as a weaker edge."""


def _leaf_judgment(kind: str, rid: str, index: dict) -> dict:
    family = LEAF_RULES[kind]
    if kind == "fact":
        f = index["facts"].get(rid)
        if f is None:
            raise DerivationError(f"leaf fact {rid!r} is not a certified fact")
        if f.get("context", {}).get("scope") != "omegaModels":
            raise DerivationError(f"leaf fact {rid!r} is not at scope omegaModels")
        # conjunctive endpoints are NOT silently truncated: A+B ⇒ C is a different
        # judgment from A ⇒ C, and no conjunction rule exists yet
        for side in ("lhs", "rhs"):
            if len(f.get(side, [])) != 1:
                raise DerivationError(
                    f"leaf fact {rid!r} has a conjunctive {side} "
                    f"({len(f.get(side, []))} endpoints); no conjunction rule exists, "
                    "so it is rejected rather than truncated")
        relation = f["kind"]
        lhs = f["lhs"][0].split(":", 1)[-1]
        rhs = f["rhs"][0].split(":", 1)[-1]
        # the exact semantic contexts this fact is certified over — transitivity may
        # only compose facts sharing a context
        contexts = frozenset(ev["context"] for ev in f.get("evidence", [])
                             if ev.get("context"))
        if not contexts:
            raise DerivationError(f"leaf fact {rid!r} carries no certification context")
    else:
        r = index["reductions"].get(rid)
        if r is None:
            raise DerivationError(f"leaf reduction {rid!r} is not an imported record")
        if r.get("status") != "importedChecked":
            raise DerivationError(f"leaf reduction {rid!r} is not importedChecked; a "
                                  "reported record never enters a derivation")
        # only exact-degree records compose: a representative or variant-sensitive
        # record would need its own rule saying what its composition means
        if r.get("degree") != "exact":
            raise DerivationError(
                f"leaf reduction {rid!r} has degree {r.get('degree')!r}; only exact "
                "records compose, absent a dedicated rule for weaker degrees")
        relation = r["local"]["notion"]
        lhs = r["local"]["lhs"].split(":", 1)[-1]
        rhs = r["local"]["rhs"].split(":", 1)[-1]
        contexts = None
    if relation not in FAMILY_RELATIONS[family]:
        raise DerivationError(f"leaf {rid!r} has relation {relation!r} outside its "
                              f"family vocabulary")
    return {"family": family, "relation": relation, "lhs": lhs, "rhs": rhs,
            "contexts": contexts, "leaves": [rid]}


def _compose_contexts(a: dict, b: dict):
    """Semantic contexts compose by intersection; an empty intersection means the two
    premises were certified over different ω contexts and do not compose."""
    ca, cb = a.get("contexts"), b.get("contexts")
    if ca is None and cb is None:
        return None
    if ca is None or cb is None:
        raise DerivationError("cannot compose a context-carrying premise with one that "
                              "carries no semantic context")
    both = ca & cb
    if not both:
        raise DerivationError(
            f"premises share no semantic context ({sorted(ca)} vs {sorted(cb)}); "
            "facts certified over different ω contexts never compose")
    return both


def eval_derivation(term, index: dict) -> dict:
    """Evaluate a proof term to its judgment, checking family, rule vocabulary,
    relation, and EXACT endpoint composition at every node."""
    if not isinstance(term, list) or not term or not isinstance(term[0], str):
        raise DerivationError(f"malformed proof term {term!r}")
    head, args = term[0], term[1:]
    if head in LEAF_RULES:
        if len(args) != 1 or not isinstance(args[0], str):
            raise DerivationError(f"leaf rule {head!r} takes one record id")
        return _leaf_judgment(head, args[0], index)
    prems = [eval_derivation(a, index) for a in args]
    if not prems:
        raise DerivationError(f"unknown rule {head!r} with no premises")
    family = prems[0]["family"]
    for p in prems[1:]:
        if p["family"] != family:
            raise DerivationError(f"rule {head!r} mixes families "
                                  f"({family!r} and {p['family']!r})")
    rules = FAMILY_RULES[family]
    if head not in rules:
        raise DerivationError(f"rule {head!r} is not in the {family!r} vocabulary")
    if len(prems) != rules[head]:
        raise DerivationError(f"rule {head!r} expects {rules[head]} premise(s), "
                              f"got {len(prems)}")
    leaves = [x for p in prems for x in p["leaves"]]
    if head == "equivalenceElimForward":
        p = prems[0]
        if p["relation"] != "equivalence":
            raise DerivationError("equivalenceElimForward needs an equivalence")
        return {**p, "relation": "implication", "leaves": leaves}
    if head == "equivalenceElimReverse":
        p = prems[0]
        if p["relation"] != "equivalence":
            raise DerivationError("equivalenceElimReverse needs an equivalence")
        return {**p, "relation": "implication",
                "lhs": p["rhs"], "rhs": p["lhs"], "leaves": leaves}
    if head == "strongToOrdinary":
        p = prems[0]
        if p["relation"] != "strongWeihrauch":
            raise DerivationError("strongToOrdinary needs a ≤sW premise")
        return {**p, "relation": "weihrauch", "leaves": leaves}
    if head == "countermodelPullback":
        sep, imp = prems
        if sep["relation"] != "nonImplication":
            raise DerivationError("countermodelPullback needs a separation (Base ⊭ P) "
                                  "as its first premise")
        if imp["relation"] != "implication":
            raise DerivationError("countermodelPullback needs an implication (Q → P) "
                                  "as its second premise; eliminate an equivalence "
                                  "first")
        if imp["rhs"] != sep["rhs"]:
            raise DerivationError(f"countermodelPullback does not compose: the "
                                  f"implication targets {imp['rhs']!r} but the "
                                  f"separation refutes {sep['rhs']!r} (exact "
                                  "endpoints, never concepts)")
        ctxs = _compose_contexts(sep, imp)
        return {"family": family, "relation": "nonImplication",
                "lhs": sep["lhs"], "rhs": imp["lhs"], "contexts": ctxs,
                "leaves": leaves}
    if head == "transitivity":
        a, b = prems
        if a["relation"] != b["relation"]:
            raise DerivationError(f"transitivity needs matching relations, got "
                                  f"{a['relation']!r} and {b['relation']!r}")
        if a["relation"] == "equivalence":
            raise DerivationError("transitivity is stated for implications and "
                                  "reductions; eliminate the equivalence first")
        if a["relation"] == "nonImplication":
            raise DerivationError("transitivity never applies to separations; the "
                                  "only separation rule is countermodelPullback")
        if a["rhs"] != b["lhs"]:
            raise DerivationError(f"transitivity does not compose: {a['rhs']!r} != "
                                  f"{b['lhs']!r} (exact endpoints, never concepts)")
        ctxs = _compose_contexts(a, b)
        return {"family": family, "relation": a["relation"],
                "lhs": a["lhs"], "rhs": b["rhs"], "contexts": ctxs, "leaves": leaves}
    raise DerivationError(f"unimplemented rule {head!r}")


def render_term(term) -> str:
    """The proof term as source text, for display and provenance."""
    if isinstance(term, str):
        return term
    return f"{term[0]}({', '.join(render_term(a) for a in term[1:])})"


def build_computed_closure(catalog: dict) -> dict:
    """The computed-closure view: derived edges from typed proof trees, plus the
    exact direct premises they cite (so each triangle is legible). Derived edges
    are `computedView` and dotted; premise edges keep their own family and status."""
    index = {
        "facts": {f["id"]: f for f in catalog.get("facts", []) if f.get("evidence")},
        "reductions": {r["id"]: r for r in catalog.get("importedReductions", [])},
    }
    variants = {v["id"].split(":", 1)[-1] for v in catalog.get("statementVariants", [])}
    omega_variants = {v["id"].split(":", 1)[-1]
                      for v in catalog.get("statementVariants", [])
                      if v.get("layer") == "turingIdealOmega"}
    problems = {q["id"].split(":", 1)[-1] for q in catalog.get("uniformProblems", [])}
    edges, nodes, seen_ids = [], set(), set()
    for spec in COMPUTED_DERIVATIONS:
        if spec["id"] in seen_ids:
            raise DerivationError(f"duplicate derived edge id {spec['id']!r}")
        seen_ids.add(spec["id"])
        j = eval_derivation(spec["term"], index)
        exp = spec["expect"]
        if (j["family"], j["relation"], j["lhs"], j["rhs"]) != (
                exp["family"], exp["relation"], exp["lhs"], exp["rhs"]):
            raise DerivationError(
                f"{spec['id']}: the proof term concludes "
                f"{j['relation']} {j['lhs']} → {j['rhs']} in {j['family']}, but the "
                f"declaration expects {exp['relation']} {exp['lhs']} → {exp['rhs']} "
                f"in {exp['family']}")
        got_ctx = None if j.get("contexts") is None else sorted(j["contexts"])
        if got_ctx != exp["contexts"]:
            raise DerivationError(
                f"{spec['id']}: the proof term concludes over contexts {got_ctx}, but "
                f"the declaration pins {exp['contexts']}")
        # endpoint kinds, checked against the family's node universe
        universe = omega_variants if j["family"] == "certifiedOmegaFact" else problems
        for side in ("lhs", "rhs"):
            if j[side] not in universe:
                raise DerivationError(f"{spec['id']}: endpoint {j[side]!r} is not a "
                                      f"registered node of family {j['family']!r}")
        label = {"implication": "⊨ω", "nonImplication": "⊭ω", "weihrauch": "≤W",
                 "strongWeihrauch": "≤sW"}[j["relation"]]
        nodes.update([j["lhs"], j["rhs"]])
        edges.append({
            "id": spec["id"], "family": "computedClosure", "status": "computedView",
            "premiseFamily": j["family"], "relation": j["relation"], "label": label,
            "lhs": j["lhs"], "rhs": j["rhs"],
            "contexts": got_ctx,
            "derivation": spec["term"], "derivationText": render_term(spec["term"]),
            "leaves": sorted(set(j["leaves"])), "note": spec["note"]})
    # the cited direct premises, as context edges (never merged, never recomputed)
    premise_edges = []
    cited = sorted({leaf for e in edges for leaf in e["leaves"]})
    for rid in cited:
        # the canonical constructors, so a displayed premise carries the SAME
        # provenance (certificates / repository / revision / theorem) as it does in
        # its own family view — never a skinny duplicate
        if rid in index["facts"]:
            ed = direct_omega_edge(index["facts"][rid])
        else:
            ed = direct_imported_edge(index["reductions"][rid])
        premise_edges.append(ed)
        nodes.update([ed["lhs"], ed["rhs"]])
    return {
        "view": "computed-closure", "family": "computedClosure",
        "comment": "TYPED COMPUTED CLOSURE, view-only. Each derived edge is the "
                   "conclusion of an explicit proof TREE (premise orientation is part "
                   "of the term), typechecked at every node against family-specific "
                   "rule vocabularies and EXACT endpoint composition. No generic "
                   "reachability: derivations are hand-declared, never searched. "
                   "Derived edges are computedView — never certified, never imported, "
                   "never a registered fact, never in any certified count; the "
                   "canonical graphs stay direct-only.",
        "nodes": sorted(nodes), "edges": premise_edges + edges}


def scoreboard_cell(catalog: dict, scope: str) -> str:
    """One scoped-results scoreboard cell, mirroring #revmath_stats exactly: local
    certified facts filtered by their context scope (kernelChecked by construction)
    plus scoped results filtered by scope, annotated by verification."""
    facts_k = len([f for f in catalog.get("facts", []) if f.get("evidence")
                   and f.get("context", {}).get("scope") == scope])
    contribs = [x for x in catalog.get("scopedResults", [])
                if x.get("scope") == scope]
    kc = facts_k + len([c for c in contribs
                        if c.get("verification") == "kernelChecked"])
    bc = len([c for c in contribs if c.get("verification") == "backendChecked"])
    total = kc + bc
    if total == 0:
        return "0"
    if bc == 0:
        return f"{total} (kernelChecked)"
    if kc == 0:
        return f"{total} (backendChecked)"
    return f"{total} ({kc} kernelChecked, {bc} backendChecked)"


def check_scoped_results(catalog: dict) -> list[str]:
    """Bidirectional fail-closed validation of the scopedResults family: every entry
    must reference a backendChecked semanticCountermodel with an agreeing semantic
    key, AND every backendChecked semanticCountermodel must have exactly one entry —
    deleting the family or its sole entry is a reported failure, never a silent
    pass. Entries must be sorted by unique sourceIds; semantic keys unique."""
    problems: list[str] = []
    bes = catalog.get("backendEvidence", [])
    srs = catalog.get("scopedResults", [])
    qualifying = [r for r in bes if r.get("kind") == "semanticCountermodel"
                  and r.get("status") == "backendChecked"]
    sids = [sr.get("sourceId") for sr in srs]
    if sids != sorted(sids):
        problems.append("scopedResults not sorted by sourceId")
    if len(sids) != len(set(sids)):
        problems.append("duplicate sourceIds in scopedResults")
    for sr in srs:
        sid = sr.get("sourceId")
        if sr.get("scope") != "allModels" or sr.get("verification") != "backendChecked":
            problems.append(f"scopedResults {sid}: unknown scope/verification")
        src_rec = next((x for x in bes if x["id"] == sid), None)
        if src_rec is None:
            problems.append(f"scopedResults {sid}: sourceId does not reference a "
                            "backendEvidence record")
        else:
            if src_rec.get("kind") != "semanticCountermodel" or \
                    src_rec.get("status") != "backendChecked":
                problems.append(f"scopedResults {sid}: source record must be a "
                                "backendChecked semanticCountermodel")
            data = src_rec.get("data", {})
            if (sr.get("kind"), sr.get("modelClass"), sr.get("theory"),
                    sr.get("sentence")) != ("semanticCountermodel",
                    data.get("modelClass"), data.get("theory"), data.get("sentence")):
                problems.append(f"scopedResults {sid}: semantic key disagrees with "
                                "the source record's data")
    for q in qualifying:
        n = sids.count(q["id"])
        if n != 1:
            problems.append(f"backendChecked semanticCountermodel {q['id']!r} has "
                            f"{n} scoped results (exactly one required — omission "
                            "and duplication both fail)")
    sr_keys = [(x.get("kind"), x.get("modelClass"), x.get("theory"), x.get("sentence"))
               for x in srs]
    if len(sr_keys) != len(set(sr_keys)):
        problems.append("duplicate semantic keys in scopedResults")
    return problems


def selftest_scoped_results() -> list[str]:
    """Omission/tamper fixtures: each mutation of a minimal valid catalog must be
    reported by check_scoped_results. Returns fixtures that wrongly passed."""
    rec = {"id": "cm.1", "kind": "semanticCountermodel", "status": "backendChecked",
           "data": {"modelClass": "foundationStruc2General", "theory": "T",
                    "sentence": "S"}}
    sr = {"sourceId": "cm.1", "scope": "allModels", "verification": "backendChecked",
          "kind": "semanticCountermodel", "modelClass": "foundationStruc2General",
          "theory": "T", "sentence": "S"}
    good = {"backendEvidence": [rec], "scopedResults": [sr]}
    if check_scoped_results(good):
        return ["minimal valid catalog wrongly rejected"]
    bad = {
        "whole family deleted": {"backendEvidence": [rec]},
        "sole entry deleted": {"backendEvidence": [rec], "scopedResults": []},
        "entry duplicated": {"backendEvidence": [rec], "scopedResults": [sr, sr]},
        "semantic key tampered": {"backendEvidence": [rec], "scopedResults":
            [{**sr, "sentence": "S2"}]},
        "verification tampered": {"backendEvidence": [rec], "scopedResults":
            [{**sr, "verification": "kernelChecked"}]},
        "dangling sourceId": {"backendEvidence": [rec], "scopedResults":
            [sr, {**sr, "sourceId": "cm.2"}]},
    }
    return [name for name, cat in bad.items() if not check_scoped_results(cat)]


def selftest_derivations() -> list[str]:
    """Fail-closed fixtures for the evaluator: malformed terms must raise, never
    silently weaken. Returns the list of fixtures that wrongly succeeded."""
    index = {
        "facts": {
            "eqv": {"kind": "equivalence", "context": {"scope": "omegaModels"},
                    "lhs": ["ns:A"], "rhs": ["ns:B"],
                    "evidence": [{"context": "ctx"}]},
            "imp": {"kind": "implication", "context": {"scope": "omegaModels"},
                    "lhs": ["ns:B"], "rhs": ["ns:C"],
                    "evidence": [{"context": "ctx"}]},
            "impA": {"kind": "implication", "context": {"scope": "omegaModels"},
                     "lhs": ["ns:A"], "rhs": ["ns:C"],
                     "evidence": [{"context": "ctx"}]},
            "far": {"kind": "implication", "context": {"scope": "omegaModels"},
                    "lhs": ["ns:X"], "rhs": ["ns:Y"], "evidence": [{"context": "ctx"}]},
            "amb": {"kind": "implication", "context": {"scope": "allModels"},
                    "lhs": ["ns:A"], "rhs": ["ns:B"], "evidence": [{"context": "ctx"}]},
            "conj": {"kind": "implication", "context": {"scope": "omegaModels"},
                     "lhs": ["ns:A", "ns:B"], "rhs": ["ns:C"],
                     "evidence": [{"context": "ctx"}]},
            "otherctx": {"kind": "implication", "context": {"scope": "omegaModels"},
                         "lhs": ["ns:B"], "rhs": ["ns:C"],
                         "evidence": [{"context": "otherCtx"}]},
            "noctx": {"kind": "implication", "context": {"scope": "omegaModels"},
                      "lhs": ["ns:B"], "rhs": ["ns:C"], "evidence": [{}]},
            "sep": {"kind": "nonImplication", "context": {"scope": "omegaModels"},
                    "lhs": ["ns:B0"], "rhs": ["ns:P"],
                    "evidence": [{"context": "ctx"}]},
            "sep2": {"kind": "nonImplication", "context": {"scope": "omegaModels"},
                     "lhs": ["ns:P"], "rhs": ["ns:R"],
                     "evidence": [{"context": "ctx"}]},
            "impQP": {"kind": "implication", "context": {"scope": "omegaModels"},
                      "lhs": ["ns:Q"], "rhs": ["ns:P"],
                      "evidence": [{"context": "ctx"}]},
            "impQP_other": {"kind": "implication", "context": {"scope": "omegaModels"},
                            "lhs": ["ns:Q"], "rhs": ["ns:P"],
                            "evidence": [{"context": "otherCtx"}]},
        },
        "reductions": {
            "sw": {"status": "importedChecked", "degree": "exact",
                   "local": {"notion": "strongWeihrauch", "lhs": "ns:P", "rhs": "ns:Q"}},
            "w": {"status": "importedChecked", "degree": "exact",
                  "local": {"notion": "weihrauch", "lhs": "ns:Q", "rhs": "ns:R"}},
            "rep": {"status": "reported", "degree": "exact",
                    "local": {"notion": "weihrauch", "lhs": "ns:Q", "rhs": "ns:R"}},
            "repr": {"status": "importedChecked", "degree": "representative",
                     "local": {"notion": "weihrauch", "lhs": "ns:Q", "rhs": "ns:R"}},
        },
    }
    must_fail = {
        "endpoints must compose exactly":
            ["transitivity", ["fact", "imp"], ["fact", "far"]],
        "families never mix":
            ["transitivity", ["fact", "imp"], ["reduction", "w"]],
        "rule outside its family vocabulary":
            ["strongToOrdinary", ["fact", "eqv"]],
        "omega rule outside its family vocabulary":
            ["equivalenceElimForward", ["reduction", "sw"]],
        "equivalence must be eliminated before transitivity":
            ["transitivity", ["fact", "eqv"], ["fact", "imp"]],
        "strongToOrdinary needs a strong premise":
            ["strongToOrdinary", ["reduction", "w"]],
        "reported records never enter derivations":
            ["transitivity", ["reduction", "sw"], ["reduction", "rep"]],
        "out-of-scope facts never enter derivations":
            ["equivalenceElimForward", ["fact", "amb"]],
        "unknown leaf": ["fact", "nope"],
        "unknown rule": ["magic", ["fact", "imp"]],
        "malformed term": ["transitivity", "imp", ["fact", "far"]],
        "wrong arity": ["transitivity", ["fact", "imp"]],
        "conjunctive endpoints are rejected, never truncated":
            ["transitivity", ["fact", "conj"], ["fact", "imp"]],
        "facts certified over different contexts never compose":
            ["transitivity", ["equivalenceElimForward", ["fact", "eqv"]],
             ["fact", "otherctx"]],
        "a fact carrying no certification context never enters":
            ["equivalenceElimForward", ["fact", "noctx"]],
        "non-exact degree never composes":
            ["transitivity", ["strongToOrdinary", ["reduction", "sw"]],
             ["reduction", "repr"]],
        "transitivity never applies to separations":
            ["transitivity", ["fact", "sep"], ["fact", "sep2"]],
        "pullback needs a separation first premise":
            ["countermodelPullback", ["fact", "impA"], ["fact", "impQP"]],
        "pullback needs an implication second premise, never a raw equivalence":
            ["countermodelPullback", ["fact", "sep"], ["fact", "eqv"]],
        "pullback endpoints must match exactly":
            ["countermodelPullback", ["fact", "sep"], ["fact", "imp"]],
        "pullback never crosses contexts":
            ["countermodelPullback", ["fact", "sep"], ["fact", "impQP_other"]],
        "pullback is family-typed, never a reduction rule":
            ["countermodelPullback", ["reduction", "sw"], ["reduction", "w"]],
    }
    wrong = []
    for name, term in must_fail.items():
        try:
            eval_derivation(term, index)
        except DerivationError:
            continue
        except Exception as exc:  # a crash is not a rejection
            wrong.append(f"{name} (raised {type(exc).__name__}, not DerivationError: "
                         f"{exc})")
            continue
        wrong.append(name)
    # the shapes that must SUCCEED, with the right orientation and contexts; an
    # unexpected exception here is reported, never allowed to crash the gate
    must_pass = {
        "ω triangle": (["transitivity",
                        ["equivalenceElimForward", ["fact", "eqv"]], ["fact", "imp"]],
                       ("implication", "A", "C"), frozenset({"ctx"})),
        # the reverse elimination must PRESERVE the certification contexts: a valid
        # same-context reverse composition once failed here by dropping them
        "reverse ω triangle": (["transitivity",
                                ["equivalenceElimReverse", ["fact", "eqv"]],
                                ["fact", "impA"]],
                               ("implication", "B", "C"), frozenset({"ctx"})),
        "Weihrauch triangle": (["transitivity",
                                ["strongToOrdinary", ["reduction", "sw"]],
                                ["reduction", "w"]],
                               ("weihrauch", "P", "R"), None),
        # the countermodel transports along the implication's contrapositive and the
        # conclusion keeps the certification contexts
        "countermodel pullback": (["countermodelPullback", ["fact", "sep"],
                                   ["fact", "impQP"]],
                                  ("nonImplication", "B0", "Q"), frozenset({"ctx"})),
    }
    for name, (term, want, want_ctx) in must_pass.items():
        try:
            j = eval_derivation(term, index)
        except Exception as exc:
            wrong.append(f"valid {name} rejected ({type(exc).__name__}): {exc}")
            continue
        if (j["relation"], j["lhs"], j["rhs"]) != want:
            wrong.append(f"valid {name} concluded the wrong judgment")
        if j.get("contexts") != want_ctx:
            wrong.append(f"valid {name} carried contexts {j.get('contexts')}, "
                         f"expected {want_ctx}")
    return wrong


def merge_antiparallel(edges: list[dict], src_key: str, tgt_key: str) -> list[dict]:
    """Merge antiparallel edge pairs WITHIN one family into a single bidirectional edge
    that carries BOTH source records — a display merge with full provenance, never a
    silent closure. For a mixed strong/ordinary reduction pair the merged edge is labeled
    at the ordinary notion and the strong direction is annotated with the explicit
    weakening rule (strongImpliesOrdinary)."""
    by_pair = {(e[src_key], e[tgt_key]): e for e in edges}
    out, seen = [], set()
    for e in edges:
        k = (e[src_key], e[tgt_key])
        if k in seen:
            continue
        rk = (k[1], k[0])
        other = by_pair.get(rk)
        if other is None or rk in seen or k == rk:
            out.append(e)
            seen.add(k)
            continue
        na, nb = e.get("notion"), other.get("notion")
        if na and nb and na != nb and {na, nb} != {"strongWeihrauch", "weihrauch"}:
            # an unknown mixed-notion pair never merges silently — fail open to two
            # directed edges rather than inventing a weakening rule
            out.append(e)
            seen.add(k)
            continue
        merged = dict(e)
        merged["bidirectional"] = True
        sa, sb = e.get("status"), other.get("status")
        if sa or sb:
            merged["status"] = ("importedChecked"
                                if sa == "importedChecked" and sb == "importedChecked"
                                else "reported")
        if e.get("revision") != other.get("revision"):
            merged.pop("revision", None)
        for fld in ("theorem", "external"):
            merged.pop(fld, None)
        recs = [x for ed in (e, other) for x in
                ([ed["record"]] if ed.get("record") else []) +
                ([ed["source"]] if ed.get("source") and "record" not in ed else [])]
        if recs:
            merged["records"] = recs
            # directional source metadata: which record certifies which drawn direction
            if e.get("record") and other.get("record"):
                merged["forwardRecord"] = e["record"]
                merged["reverseRecord"] = other["record"]
            merged.pop("record", None)
            merged.pop("source", None)
        certs = (e.get("certificates", []) or []) + (other.get("certificates", []) or [])
        if certs:
            merged["certificates"] = certs
        if na and nb and na != nb:
            # ≤sW entails ≤W: the merged double-headed edge is the ordinary notion, and
            # the strong direction is recorded as an explicit weakening — a typed
            # derivation annotation, never an undocumented inference. The strong
            # direction stays visible in the drawn geometry: filled arrowhead on the
            # strong direction, open arrowhead on the ordinary-only one.
            merged["notion"] = "weihrauch"
            merged["label"] = "≤W"
            merged["derivation"] = "strongImpliesOrdinary"
            merged["strongEnd"] = "head" if na == "strongWeihrauch" else "tail"
        seen.add(k)
        seen.add(rk)
        out.append(merged)
    return out


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
        if f["kind"] not in ("implication", "equivalence", "nonImplication"):
            continue
        ed = direct_omega_edge(f)
        omega_nodes.update([ed["lhs"], ed["rhs"]])
        omega_edges.append(ed)
    imp_edges, imp_nodes = [], set()
    for r in catalog.get("importedReductions", []):
        ed = direct_imported_edge(r)
        imp_nodes.update([ed["lhs"], ed["rhs"]])
        imp_edges.append(ed)
    imp_edges = merge_antiparallel(imp_edges, "lhs", "rhs")
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
    # intra-concept calibrations: a fact whose endpoints project to the SAME concept
    # never renders as a concept self-loop (which would read as a tautology). The
    # concept instead renders as an enclosure containing its exact variant nodes, and
    # the fact keeps its variant-level endpoints inside it.
    proj_clusters: dict = {}
    amb_proj = []
    for e in catalog.get("ambientGraph", {}).get("edges", []):
        amb_proj.append({"family": "ambientFactorization",
                           "label": "ambient",
                           "lhsConcept": iface_concept.get(e.get("source"), ""),
                           "rhsConcept": iface_concept.get(e.get("target"), ""),
                           "exactLhs": e.get("source"), "exactRhs": e.get("target"),
                           "certificates": [e.get("certificate")],
                           "status": "kernelChecked", "scope": "ambientFactorization"})
    proj_edges.extend(merge_antiparallel(amb_proj, "exactLhs", "exactRhs"))
    for e in omega_edges:
        pe = {"family": "certifiedOmegaFact", "label": e["label"],
              "kind": e["kind"],
              "lhsConcept": concept_of_variant(e["lhs"]),
              "rhsConcept": concept_of_variant(e["rhs"]),
              "exactLhs": e["lhs"], "exactRhs": e["rhs"],
              "certificates": e["certificates"],
              "status": "kernelChecked", "scope": "omegaModels",
              "source": e["fact"], "bidirectional": e["bidirectional"]}
        if pe["lhsConcept"] and pe["lhsConcept"] == pe["rhsConcept"]:
            cl = proj_clusters.setdefault(pe["lhsConcept"],
                                          {"variants": set(), "edges": []})
            cl["variants"].update([e["lhs"], e["rhs"]])
            cl["edges"].append(pe)
        else:
            proj_edges.append(pe)
    for e in imp_edges:
        pe = {"family": "importedReduction", "label": e["label"],
              "lhsConcept": concept_of_problem(e["lhs"]),
              "rhsConcept": concept_of_problem(e["rhs"]),
              "exactLhs": e["lhs"], "exactRhs": e["rhs"],
              "status": e["status"], "scope": e["notion"]}
        if e.get("records"):
            pe["records"] = e["records"]
            pe["bidirectional"] = True
            if e.get("derivation"):
                pe["derivation"] = e["derivation"]
            if e.get("strongEnd"):
                pe["strongEnd"] = e["strongEnd"]
        else:
            pe["source"] = e["record"]
        proj_edges.append(pe)
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
            "comment": "NONCANONICAL, LOSSY projection to concept granularity; every "
                       "edge keeps family, scope, exact endpoint ids, and status; NO "
                       "TRANSITIVE CLOSURE — only validated display merges with named "
                       "premises (antiparallel pairs; the explicit ≤sW ⇒ ≤W weakening); "
                       "missing bridges and unary form claims never render as edges. "
                       "An intra-concept calibration never renders as a concept "
                       "self-loop: its concept renders as an enclosure containing the "
                       "exact variant nodes, with the fact drawn between them",
            "nodes": sorted({c["id"].split(":", 1)[-1]
                             for c in catalog.get("concepts", [])}),
            "clusters": {c: {"variants": sorted(cl["variants"]),
                             "edges": cl["edges"]}
                         for c, cl in sorted(proj_clusters.items())},
            "edges": proj_edges},
        "computed-closure": build_computed_closure(catalog),
    }


STYLE = {"ambientFactorization": 'style=solid',
         "certifiedOmegaFact": 'style=bold',
         "importedReduction": 'style=dashed',
         "computedClosure": 'style=dotted'}


def view_dot(name: str, view: dict) -> str:
    lines = [f'digraph "{name}" {{', '  rankdir=LR;', '  node [shape=box];']
    clusters = view.get("clusters", {})
    anchors = {}
    if clusters:
        # compound lets an external concept-level arrow clip at the enclosure
        # boundary instead of pointing at any particular internal variant
        lines.append('  compound=true;')
        for ci, (cname, cl) in enumerate(sorted(clusters.items())):
            tag = f"cluster_{ci}"
            anchors[cname] = (cl["variants"][0], tag)
            lines.append(f'  subgraph "{tag}" {{')
            lines.append(f'    label="{cname} (concept)"; style=rounded;')
            for vn in cl["variants"]:
                lines.append(f'    "{vn}";')
            for e in cl["edges"]:
                st = STYLE.get(e.get("family", ""), "style=solid")
                ex = ", dir=both" if e.get("bidirectional") else ""
                if e.get("kind") == "nonImplication":
                    ex += ", arrowhead=tee"
                lines.append(f'    "{e["exactLhs"]}" -> "{e["exactRhs"]}" '
                             f'[label="{e.get("label", "")}", {st}{ex}];')
            lines.append('  }')
    for n in view["nodes"]:
        if n in clusters:
            continue
        lines.append(f'  "{n}";')
    for e in view["edges"]:
        fam = e.get("family", view.get("family", ""))
        style = STYLE.get(fam, "style=dotted")
        src = e.get("lhsConcept") or e.get("lhs") or e.get("exactLhs")
        tgt = e.get("rhsConcept") or e.get("rhs") or e.get("exactRhs")
        extra = ", dir=both" if e.get("bidirectional") else ""
        if src in anchors:
            node, tag = anchors[src]
            extra += f', ltail="{tag}"'
            src = node
        if tgt in anchors:
            node, tag = anchors[tgt]
            extra += f', lhead="{tag}"'
            tgt = node
        if e.get("family") == "computedClosure":
            # derived, never certified: dotted, and the rule name travels with the
            # edge so the geometry is never the only provenance. Open head for
            # derived implications/reductions; the tee marks a derived separation's
            # blocked direction, exactly as on direct separation edges.
            hd = "tee" if e.get("relation") == "nonImplication" else "onormal"
            lines.append(f'  "{src}" -> "{tgt}" [label="{e.get("label", "")} '
                         f'[{e["derivationText"]}]", {style}, arrowhead={hd}];')
            continue
        if e.get("strongEnd") == "head":
            extra += ", arrowhead=normal, arrowtail=onormal"
        elif e.get("strongEnd") == "tail":
            extra += ", arrowhead=onormal, arrowtail=normal"
        elif e.get("family") == "importedReduction" and e.get("notion"):
            # family-wide convention, single edges included: filled head = certified
            # strong (≤sW); open head = certified ordinary only (≤W)
            hd = "normal" if e["notion"] == "strongWeihrauch" else "onormal"
            extra += f", arrowhead={hd}"
            if e.get("bidirectional"):
                extra += f", arrowtail={hd}"
        if e.get("kind") == "nonImplication":
            # ordinary centered label: the relation holds along the whole separation
            # edge; the tee alone marks the blocked direction. Crowding is a
            # spacing/routing concern, never solved by attaching the symbol to the tee.
            lines.append(f'  "{src}" -> "{tgt}" [label="{e.get("label", "")}", '
                         f'{style}{extra}, arrowhead=tee];')
            continue
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
    view_svgs: set[str] = set()
    for vname, view in family_views.items():
        vdir = out / "views" / vname
        vdir.mkdir(parents=True, exist_ok=True)
        (vdir / "graph.json").write_text(
            json.dumps(view, indent=1, sort_keys=True, ensure_ascii=False) + "\n")
        (vdir / "graph.dot").write_text(view_dot(vname, view))
        if render_svg(vdir / "graph.dot", vdir / "graph.svg"):
            view_svgs.add(vname)
    dot_text = to_dot(catalog)
    dot_path = out / "ambient-factorizations.dot"
    dot_path.write_text(dot_text)
    svg_path = out / "ambient-factorizations.svg"
    have_svg = render_svg(dot_path, svg_path)
    site = out / "site"
    site.mkdir(parents=True, exist_ok=True)
    if have_svg:
        shutil.copy(svg_path, site / "ambient-factorizations.svg")
    for vname in view_svgs:
        shutil.copy(out / "views" / vname / "graph.svg", site / f"{vname}.svg")
    # the canonical JSON is part of the public site: honest data over rendered views
    shutil.copy(zoo_dir(root) / "catalog.direct.json", site / "catalog.direct.json")
    # downloadable canonical artifacts (only site/ is deployed): DOT/JSON per view
    shutil.copy(dot_path, site / "ambient-factorizations.dot")
    (site / "views" / "ambient-standard").mkdir(parents=True, exist_ok=True)
    shutil.copy(view_dir / "graph.json",
                site / "views" / "ambient-standard" / "graph.json")
    for vname in family_views:
        sdir = site / "views" / vname
        sdir.mkdir(parents=True, exist_ok=True)
        for fn in ("graph.json", "graph.dot"):
            shutil.copy(out / "views" / vname / fn, sdir / fn)
    page = site_html(catalog, have_svg, dot_text, view_svgs)
    for marker in ("Canonical graphs (one per evidence family — never flattened into one)",
                   "NONCANONICAL, LOSSY",
                   "only validated display merges with named premises",
                   "Filtering changes visibility only",
                   "Semantic contexts",
                   # the computed family must always announce that it is view-only and
                   # hand-declared — never searched, never certified
                   "No generic reachability: these derivations are "
                   "hand-declared, never searched",
                   "absent from the "
                   "canonical direct-only graphs and every certified count"):
        if marker not in page:
            sys.exit(f"rmlib-zoo build: graph/filter marker missing: {marker!r}")
    legend_count = page.count('<div class="legend"')
    if legend_count != 1:
        sys.exit(f"rmlib-zoo build: expected exactly one legend placement (under the "
                 f"concept overview; the canonical graphs refer back to it), found "
                 f"{legend_count}")
    expected_imgs = (1 if have_svg else 0) + len(view_svgs)
    if page.count("<img ") != expected_imgs:
        sys.exit(f"rmlib-zoo build: expected exactly one <img> per rendered graph "
                 f"panel ({expected_imgs}), found {page.count('<img ')}")
    if page.count('data-case-study="hall-efilc"') != 6:
        sys.exit("rmlib-zoo build: Hall–EFILC case study must be linked from exactly "
                 "three concept cards and three certified-fact cards")
    if any(f.get("kind") == "nonImplication" and f.get("evidence")
           for f in catalog.get("facts", [])):
        # a certified separation must be framed as a countermodel, never a turnstile claim
        for marker in ("model-class separation", "⊭ω"):
            if marker not in page:
                sys.exit(f"rmlib-zoo build: separation marker missing: {marker!r}")
    # rendered-HTML enclosure guard: an intra-concept calibration's accessible headline
    # must read at VARIANT level — the tautological `concept RELATION concept` line must
    # never regress into the page, and the exact variant-level line must be present
    for cname, cl in family_views["concept-projection"].get("clusters", {}).items():
        for ed in cl["edges"]:
            lab = html.escape(ed.get("label", ""))
            loop_line = (f"<code>{html.escape(cname)}</code> {lab} "
                         f"<code>{html.escape(cname)}</code>")
            if loop_line in page:
                sys.exit(f"rmlib-zoo build: accessible edge list renders the "
                         f"tautological {cname!r} self-loop headline")
            exact_line = (f"<code>{html.escape(ed['exactLhs'])}</code> {lab} "
                          f"<code>{html.escape(ed['exactRhs'])}</code>")
            if exact_line not in page:
                sys.exit(f"rmlib-zoo build: enclosed calibration "
                         f"{ed.get('source')!r} missing its variant-level "
                         "accessible headline")
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
