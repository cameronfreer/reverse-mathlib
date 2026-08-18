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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import readability  # noqa: E402  (sibling module, loaded from this file's directory)

SCHEMA_ID = "reverse-mathlib.catalog/v7"
# The one label the canonical ambient graph carries; shared so the label gate covers
# to_dot as well as the family views. Directional glyphs are forbidden in ALL graph
# labels — direction belongs to drawn arrowheads only.
AMBIENT_EDGE_LABEL = "ambient, kernel checked"


# Prose budgets per surface, enforced at build time and set at the baseline the
# rewrite reached, so the work cannot silently unwind. Hard rules cover only what
# is objectively wrong: an identifier used as a fragment of a sentence, a stored
# enum value in prose, scheduling vocabulary on a reader surface, one disclaimer
# copied across cards, and a reading path that outgrows its budget.
#
# Em dash density, sentence length, shouted words and compound density stay
# advisory in the report. Hard limits on them would fight good prose rather than
# bad, and a sentence is sometimes long because the mathematics is.
#
# The reference surface still carries identifiers inside registered prose that no
# renderer can mark without reading the sentence. Its allowance is a ratchet at
# the level reached, not an endorsement: it may fall, never rise.
READABILITY_BUDGETS: dict = {
    "all": {
        "noProjectVocabulary": True,
        "noDuplicateSentences": True,
        "requireAltText": True,
    },
    "public": {
        "noIdentifierLeaks": True,
        "noEnumTokens": True,
        "noImplementationVocabulary": True,
        "maxDefaultOpenWords": 1500,
        "maxSections": 6,
        "requireLinks": ["reference.html", "methods.html"],
    },
    "methods": {
        "noIdentifierLeaks": True,
        "noEnumTokens": True,
        "maxDefaultOpenWords": 1500,
        "maxSections": 8,
    },
    "reference": {
        "maxIdentifierLeaks": 79,
        "maxEnumTokensInProse": 8,
        "maxDuplicateSentences": 4,
        "maxDefaultOpenWords": 2200,
    },
}


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
                "calculusNonderivability", "semanticCountermodel",
                "standardCalculusIdentity", "calculusComparison"}
    be_kind_of = {x["id"]: x.get("kind") for x in bes}
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
        if r.get("kind") == "calculusIdentity":
            if r.get("data", {}).get("standardComparison") not in ("pending", "recorded"):
                problems.append(f"backendEvidence {rid}: unknown standardComparison tag")
        if r.get("kind") == "standardCalculusIdentity":
            data = r.get("data", {})
            if data.get("sortAssumption") != "nonemptySetSort":
                problems.append(f"backendEvidence {rid}: unknown sortAssumption tag")
            if data.get("equalityRules") != "reflAndSubstitution":
                problems.append(f"backendEvidence {rid}: unknown equalityRules tag")
            if not data.get("source"):
                problems.append(f"backendEvidence {rid}: missing documentary source pin")
            rendered = r.get("display", {}).get("rendered", "")
            for marker in (data.get("calculusId", ""), "no completeness",
                           "never a checked claim", "reflAndSubstitution",
                           "equality-correct"):
                if not marker or marker not in rendered:
                    problems.append(f"backendEvidence {rid}: rendering must carry the "
                                    f"calculus id, the equality qualification, and "
                                    f"the documented-reading honesty markers "
                                    f"(missing {marker!r})")
        if r.get("kind") == "calculusComparison":
            data = r.get("data", {})
            if data.get("relation") != "independentDirectSoundness":
                problems.append(f"backendEvidence {rid}: unknown comparison relation")
            if be_kind_of.get(data.get("standardCalculusRecord")) != \
                    "standardCalculusIdentity":
                problems.append(f"backendEvidence {rid}: standardCalculusRecord must "
                                "reference a standardCalculusIdentity record")
            if be_kind_of.get(data.get("comparedCalculusRecord")) != "calculusIdentity":
                problems.append(f"backendEvidence {rid}: comparedCalculusRecord must "
                                "reference a calculusIdentity record")
            rendered = r.get("display", {}).get("rendered", "")
            if "carries no embedding and licenses no derivability transfer" \
                    not in rendered:
                problems.append(f"backendEvidence {rid}: rendering must state exactly "
                                "the approved embedding-free relation")
        if r.get("kind") == "calculusNonderivability":
            data = r.get("data", {})
            for ref_field in ("calculusRecord", "sentenceAdapter"):
                if data.get(ref_field) not in be_ids:
                    problems.append(f"backendEvidence {rid}: broken record reference "
                                    f"{ref_field}={data.get(ref_field)!r}")
            if be_kind_of.get(data.get("calculusRecord")) not in (
                    "calculusIdentity", "standardCalculusIdentity"):
                problems.append(f"backendEvidence {rid}: calculusRecord must reference "
                                "a calculus identity record")
            rendered = r.get("display", {}).get("rendered", "")
            if data.get("calculusId", "") not in rendered or \
                    "never an unqualified" not in rendered:
                problems.append(f"backendEvidence {rid}: rendering must carry the "
                                "calculus id and refuse the unqualified reading")
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
    for name in selftest_base_context():
        problems.append(f"base-context classifier selftest failed: {name}")
    for name in selftest_projection_layout():
        problems.append(f"projection-layout selftest failed: {name}")
    for name in selftest_optional_graphviz():
        problems.append(f"optional-graphviz selftest failed: {name}")
    for name in selftest_flat_label_recenter():
        problems.append(f"flat-label recenter selftest failed: {name}")
    for name in readability.selftest_extraction():
        problems.append(f"readability extraction selftest failed: {name}")
    for name in readability.selftest_budgets():
        problems.append(f"readability budget selftest failed: {name}")
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
        # literature bands add invisible placement constraints to the DOT —
        # never drawn edges, so they count in the DOT and never in the SVG
        band_count = sum(len(b["concepts"])
                         for b in view.get("literatureBands", []))
        if dot.count(" -> ") != len(view["edges"]) + cl_edge_count + band_count:
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


def recenter_flat_edge_labels(svg: str) -> str:
    """Graphviz pins a flat edge's label to the midpoint of the *unclipped* node
    gap, so when the edge is clipped at an enclosure boundary the label can stray
    off the visible arrow (no dot-language attribute moves it — label, xlabel,
    head/tail labels, and ports all land on the same spot).

    Deterministic post-pass on the exact failure signature, general across views:
    inside each edge group whose path is horizontal (flat), a label sitting
    outside the path's x-extent is recentered onto it. Well-placed labels and
    non-flat edges are untouched.

    Placement is collision-aware. Several flat edges between the same pair share
    almost the same visible span, so recentering each to its midpoint would stack
    their labels on one point. Every label is tracked by its occurrence in the
    document — not by coordinate value, so two labels rendered on the same point
    still see each other as collisions. Candidates along the span are tried in
    order and the first clear of every other label wins; when no candidate is
    clear the label keeps its original placement, because this pass exists to
    remove collisions and must never manufacture one.
    """
    placed = [[float(x), float(y)] for x, y in
              re.findall(r'<text[^>]*\bx="([\d.eE+-]+)"[^>]*\by="([\d.eE+-]+)"', svg)]
    claimed: set[int] = set()

    def clear(x: float, y: float, own: int) -> bool:
        return all(abs(x - px) >= 34 or abs(y - py) >= 11
                   for i, (px, py) in enumerate(placed) if i != own)

    def fix_group(m: "re.Match[str]") -> str:
        g = m.group(0)
        path = re.search(r'<path[^>]*\bd="([^"]+)"', g)
        text = re.search(r'(<text[^>]*\bx=")([\d.eE+-]+)("[^>]*\by=")([\d.eE+-]+)(")', g)
        if not path or not text:
            return g
        pts = re.findall(r'([\d.eE+-]+),([\d.eE+-]+)', path.group(1))
        xs = [float(x) for x, _ in pts]
        ys = [float(y) for _, y in pts]
        if not xs or max(ys) - min(ys) > 1.0:
            return g
        x0, y0 = float(text.group(2)), float(text.group(4))
        own = next((i for i, p in enumerate(placed)
                    if p == [x0, y0] and i not in claimed), None)
        if own is None:
            # a label the global extraction did not see: leave it exactly as
            # rendered rather than reason about collisions it is not part of
            return g
        claimed.add(own)
        lo, hi = min(xs), max(xs)
        # already on its own edge and clear of every other label: leave it alone
        if lo <= x0 <= hi and clear(x0, y0, own):
            return g
        mid, quarter = (lo + hi) / 2, (hi - lo) / 4
        for cand in (mid, mid + quarter, mid - quarter, hi, lo):
            if lo <= cand <= hi and clear(cand, y0, own):
                placed[own] = [cand, y0]
                return g.replace(text.group(0),
                                 f"{text.group(1)}{cand:.2f}{text.group(3)}"
                                 f"{text.group(4)}{text.group(5)}", 1)
        # no clear candidate anywhere on the span: retain the original placement
        return g

    return re.sub(r'<g id="edge\d+" class="edge">[\s\S]*?</g>', fix_group, svg)


def selftest_optional_graphviz() -> list[str]:
    """Graphviz is optional, and a build without it is a supported path: the atlas
    still states its results, and the reference surface still lists every edge.
    A legend explains a picture, so it appears only alongside one. Returns the
    scenarios that wrongly passed."""
    bad = []
    view = {"view": "concept-projection", "family": "mixed-direct-only",
            "nodes": ["p", "q"], "baseContextConcepts": [],
            "edges": [{"family": "certifiedOmegaFact", "kind": "implication",
                       "label": "⊨ω", "lhsConcept": "p", "rhsConcept": "q"}]}
    catalog = {"schema": "test/v1", "concepts": [], "statementVariants": [],
               "facts": [], "ports": [], "scopedResults": [],
               "dependencies": {"leanVersion": "4", "mathlibRevision": "abc"}}
    # Bands and derivations have their own fixtures; this one is about pictures
    # and legends, so the synthetic catalog carries neither.
    saved_bands = list(LITERATURE_BANDS)
    saved_derivs = list(COMPUTED_DERIVATIONS)
    LITERATURE_BANDS.clear()
    COMPUTED_DERIVATIONS.clear()
    for have_svg, svgs, want_legend in ((False, set(), 0), (True, {"concept-projection"}, 1)):
        try:
            pages = site_pages(catalog, have_svg, "digraph {}", svgs)
        except Exception as exc:                      # noqa: BLE001 - reported, not raised
            bad.append(f"building with graphviz={have_svg} raised {exc!r}")
            continue
        for name, text in pages.items():
            shows = "<img " in text
            legends = text.count('<div class="legend"')
            if legends != (1 if shows else 0):
                bad.append(f"graphviz={have_svg}: {name} carries {legends} legend(s) "
                           f"with {'a picture' if shows else 'no picture'}")
        if not have_svg and "<img " in "".join(pages.values()):
            bad.append("a build without graphviz still emitted an image")
        if have_svg and pages["index.html"].count('<div class="legend"') != want_legend:
            bad.append("the atlas lost its legend when a picture was available")
    LITERATURE_BANDS[:] = saved_bands
    COMPUTED_DERIVATIONS[:] = saved_derivs
    return bad


def selftest_flat_label_recenter() -> list[str]:
    """The flat-clipped-label post-pass is frozen on its exact firing
    condition: a stray label on a flat edge is recentered onto the visible
    span; in-span labels and non-flat edges stay untouched. Returns the
    scenarios that wrongly passed."""
    def group(path: str, x: str) -> str:
        return ('<g id="edge1" class="edge">\n<title>a&#45;&gt;b</title>\n'
                f'<path fill="none" d="{path}"/>\n'
                f'<text text-anchor="middle" x="{x}" y="-275.8">L</text>\n</g>')
    bad = []
    flat = "M626,-291.4C632,-291.4 638,-291.4 644,-291.4"
    out = recenter_flat_edge_labels(group(flat, "614.5"))
    if 'x="635.00"' not in out:
        bad.append("stray flat label not recentered onto the visible span")
    if recenter_flat_edge_labels(group(flat, "630")) != group(flat, "630"):
        bad.append("in-span flat label wrongly moved")
    steep = "M626,-291.4C632,-260.1 638,-240.2 644,-215.9"
    if recenter_flat_edge_labels(group(steep, "614.5")) != group(steep, "614.5"):
        bad.append("non-flat edge label wrongly moved")

    def pair(path: str, xa: str, xb: str) -> str:
        return ('<g id="edge1" class="edge">\n<title>a&#45;&gt;b</title>\n'
                f'<path fill="none" d="{path}"/>\n'
                f'<text text-anchor="middle" x="{xa}" y="-275.8">L</text>\n</g>\n'
                '<g id="edge2" class="edge">\n<title>a&#45;&gt;c</title>\n'
                f'<path fill="none" d="{path}"/>\n'
                f'<text text-anchor="middle" x="{xb}" y="-275.8">M</text>\n</g>')

    def label_xs(svg: str) -> list[float]:
        return [float(x) for x in re.findall(r'<text[^>]*\bx="([\d.eE+-]+)"', svg)]
    wide = "M500,-291.4C560,-291.4 640,-291.4 700,-291.4"
    for scenario, xa, xb in (("exact", "600", "600"), ("near", "600", "610")):
        out_xs = label_xs(recenter_flat_edge_labels(pair(wide, xa, xb)))
        if len(out_xs) != 2 or abs(out_xs[0] - out_xs[1]) < 34:
            bad.append(f"{scenario}-overlap labels on a wide span were both "
                       "judged clear instead of being separated")
    # a stray label whose whole span is blocked by another label: the old
    # fallback forced it to the midpoint, manufacturing the very collision the
    # pass exists to remove — it must retain its original placement instead
    blocked = ('<text text-anchor="middle" x="635" y="-275.8">N</text>\n'
               + group(flat, "614.5"))
    if 'x="614.5"' not in recenter_flat_edge_labels(blocked):
        bad.append("stray label on a fully blocked span was moved into a "
                   "collision instead of retained")
    return bad


def render_svg(dot_path: Path, svg_path: Path) -> bool:
    dot = shutil.which("dot")
    if dot is None:
        print("rmlib-zoo: graphviz `dot` not found; skipping SVG (DOT is the comparand anyway)")
        return False
    res = subprocess.run([dot, "-Tsvg", str(dot_path), "-o", str(svg_path)])
    if res.returncode != 0:
        # Graphviz being absent and Graphviz erroring are different outcomes: the latter fails.
        sys.exit("rmlib-zoo: graphviz `dot` failed")
    svg_path.write_text(recenter_flat_edge_labels(svg_path.read_text(encoding="utf-8")),
                        encoding="utf-8")
    return True


SITE_CSS = """* { box-sizing: border-box; }
body { font-family: -apple-system, "Segoe UI", Helvetica, Arial, sans-serif;
       margin: 0; padding: 1.25rem 1rem 3rem; color: #1a1a1a; background: #fafafa;
       line-height: 1.5; }
main { max-width: 56rem; margin: 0 auto; }
h1 { font-size: 1.5rem; }
h2 { font-size: 1.2rem; margin-top: 2rem; border-bottom: 1px solid #ddd;
      padding-bottom: 0.3rem; }
h3 { font-size: 1rem; margin: 0 0 0.5rem; overflow-wrap: anywhere; }
h4 { font-size: 0.9rem; margin: 0.75rem 0 0.25rem; }
code { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace;
        font-size: 0.85em; background: #f0f0f0; padding: 0.1em 0.3em;
        border-radius: 3px; overflow-wrap: anywhere; }
.card { background: #fff; border: 1px solid #e2e2e2; border-radius: 6px;
         padding: 0.9rem 1.1rem; margin: 0.75rem 0; }
.card p { margin: 0.4rem 0; }
.tag { font-size: 0.72rem; font-weight: normal; color: #555; background: #eee;
        border-radius: 10px; padding: 0.1rem 0.55rem; vertical-align: middle;
        white-space: nowrap; }
dl { display: grid; grid-template-columns: max-content 1fr; gap: 0.15rem 0.9rem;
      margin: 0.5rem 0; }
dt { color: #666; font-size: 0.85rem; }
dd { margin: 0; overflow-wrap: anywhere; }
ul { margin: 0.3rem 0; padding-left: 1.2rem; }
li { margin: 0.25rem 0; overflow-wrap: anywhere; }
#principles { background: #f4f8fc; border: 1px solid #cfe0ef; border-radius: 6px;
  padding: 0.4rem 1.1rem 0.9rem; margin: 1rem 0 1.5rem; }
#principles h2 { margin-top: 0.5rem; }
.principles { font-size: 1.02rem; }
.principles dt { margin-top: 0.6rem; }
.principles dd { margin: 0.2rem 0 0 1.2rem; max-width: 62rem; }
.banner { background: #fff6df; border: 1px solid #e6cf8a; padding: 0.75rem 1rem;
           border-radius: 6px; overflow-wrap: anywhere; }
.banner p { margin: 0.3rem 0; }
figure.graph { margin: 0.75rem 0; text-align: center; }
figure.graph img { max-width: 100%; height: auto; }
figcaption { color: #666; font-size: 0.8rem; }
.scroll { overflow-x: auto; }
details summary { cursor: pointer; color: #666; font-size: 0.85rem; }
details p { font-size: 0.85rem; color: #444; }
details.card > summary, details.graphpanel > summary { color: #1a1a1a;
    font-size: 0.95rem; overflow-wrap: anywhere; }
details.graphpanel { background: #fff; border: 1px solid #e2e2e2;
    border-radius: 6px; padding: 0.6rem 0.9rem; margin: 0.75rem 0; }
.meta { color: #555; font-size: 0.85rem; overflow-wrap: anywhere; }
.refitem { background: #fff; border: 1px solid #e2e2e2; border-radius: 6px;
    padding: 0.6rem 0.9rem; margin: 0.5rem 0; font-size: 0.9rem;
    overflow-wrap: anywhere; }
.scount { font-size: 0.8rem; color: #666; font-weight: normal; }
.legend { display: flex; flex-direction: column; gap: 0.3rem; font-size: 0.78rem;
    color: #555; background: #fff; border: 1px solid #e2e2e2; border-radius: 6px;
    padding: 0.5rem 0.9rem; margin: 0.5rem 0; }
.legend .lg { display: flex; align-items: center; gap: 0.45rem; }
.legend svg { flex: none; }
footer { color: #666; font-size: 0.8rem; margin-top: 2.5rem;
          border-top: 1px solid #ddd; padding-top: 0.75rem;
          overflow-wrap: anywhere; }
a { color: #205ea6; }
.chip { text-decoration: none; }
.chip code { background: #eef2f7; border: 1px solid #d7e2ee; color: #24486d; }
nav.surfaces { margin: 0.4rem 0 1.2rem; font-size: 0.9rem; }
nav.surfaces a { margin-right: 0.9rem; }
table.results { border-collapse: collapse; width: 100%; margin: 0.6rem 0 1rem; }
table.results th, table.results td { border-bottom: 1px solid #e2e2e2;
      padding: 0.45rem 0.6rem; text-align: left; vertical-align: top;
      font-size: 0.93rem; }
table.results th { font-size: 0.78rem; text-transform: uppercase;
      letter-spacing: 0.04em; color: #555; }
table.results td.how { white-space: nowrap; color: #444; font-size: 0.86rem; }
.wrapscroll { overflow-x: auto; }
#proved { background: #f7f5ef; border: 1px solid #e0d9c8; border-radius: 6px;
      padding: 0.9rem 1.1rem; margin: 1.2rem 0; }
#proved h2 { margin-top: 0; border: 0; }
"""


FILTER_SCRIPT = """
/* Filtering changes visibility only; the canonical data is catalog.direct.json. */
function applyFilter() {
  var t = document.getElementById('ftext').value.toLowerCase();
  var f = document.getElementById('ffam').value;
  document.querySelectorAll('.card').forEach(function (c) {
    var okT = !t || c.textContent.toLowerCase().indexOf(t) >= 0;
    var okF = !f || c.getAttribute('data-family') === f;
    c.style.display = (okT && okF) ? '' : 'none';
  });
  document.querySelectorAll('section[data-sec]').forEach(function (s) {
    var cards = s.querySelectorAll('.card'), shown = 0;
    cards.forEach(function (c) { if (c.style.display !== 'none') shown += 1; });
    var badge = s.querySelector('.scount');
    if (badge) {
      badge.textContent = (shown === cards.length)
        ? '(' + cards.length + ')'
        : '(' + shown + ' of ' + cards.length + ' shown)';
    }
    s.style.display = (cards.length > 0 && shown === 0) ? 'none' : '';
  });
}"""


# One place where catalog enum values become English. Every reader-facing
# rendering goes through these maps, so a value can never reach a sentence in its
# stored form: the identifier stays in the data and in the lookup chips, and the
# page says what it means.
VERIFICATION_PROSE = {
    "kernelChecked": "checked by the Lean kernel",
    "backendChecked": "checked in the pinned external Lean bridge",
    "importedChecked": "checked in a pinned external Lean development",
    "computedView": "derived for display; not counted",
    "claimed": "claimed, not checked",
    "reported": "reported from the literature",
}

SCOPE_PROSE = {
    "omegaModels": "over ω-models",
    "allModels": "over all second-order structures",
    "provability": "in the pinned proof calculus",
    "ambientFactorization": "in ambient Lean over standard ℕ",
    "weihrauch": "as a Weihrauch reduction",
    "strongWeihrauch": "as a strong Weihrauch reduction",
    "none": "with no model-theoretic scope",
}

KIND_PROSE = {
    "equivalence": "equivalence",
    "implication": "implication",
    "nonImplication": "separation, witnessed by a countermodel",
}

RELATION_SYMBOL = {"equivalence": "⇔", "implication": "⇒", "nonImplication": "⊭"}


def prose_verification(value: str | None) -> str:
    return VERIFICATION_PROSE.get(value or "", value or "unrecorded")


def prose_scope(value: str | None) -> str:
    return SCOPE_PROSE.get(value or "", value or "unrecorded")


def short_id(identifier: str) -> str:
    """Identifiers carry a namespace for the data; a chip shows the local part."""
    return (identifier or "").split(":", 1)[-1]


def identifier_pattern(catalog: dict) -> "re.Pattern":
    """Every identifier the catalog knows, plus the shapes Lean names take.

    Registration fields are plain strings, so an identifier written inside a note
    arrives as ordinary text. Marking those occurrences as data at render time is
    what keeps the rule uniform: an identifier is data wherever it appears, and a
    sentence never has one as a fragment.
    """
    known = set()
    for key in ("concepts", "statementVariants", "facts", "ports",
                "importedReductions", "backendEvidence", "semanticContexts",
                "reducibilityNotions"):
        for item in catalog.get(key, []) or []:
            if isinstance(item, dict) and item.get("id"):
                known.add(short_id(item["id"]))
    for f_ in catalog.get("facts", []) or []:
        for ev in f_.get("evidence", []) or []:
            if ev.get("certificate"):
                known.add(ev["certificate"])
    for c in catalog.get("corpus", {}).get("claims", []) or []:
        if c.get("id"):
            known.add(c["id"])
    literal = "|".join(re.escape(k) for k in sorted(known, key=len, reverse=True))
    # dotted Lean names, file paths, and the catalog's own camelCase values
    shapes = (r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+"      # Module.Name.thing
              r"|[A-Za-z_][\w']*\.lean"                        # a source file
              r"|\b[a-z][a-z0-9]*(?:[A-Z][A-Za-z0-9]*)+\b")    # storedCamelCase
    return re.compile(f"({literal}|{shapes})" if literal else f"({shapes})")


def mark_identifiers(text: str, pattern: "re.Pattern") -> str:
    """Escape prose, then wrap identifier occurrences in a code element."""
    out, last = [], 0
    for m in pattern.finditer(text or ""):
        if m.group(0) in readability.NOTATION_ALLOWED:
            continue
        out.append(html.escape(text[last:m.start()]))
        out.append(f"<code>{html.escape(m.group(0))}</code>")
        last = m.end()
    out.append(html.escape(text[last:]))
    return "".join(out)


def principles_section(catalog: dict) -> str:
    """What each principle asserts, in the words registered with it. Statements are
    typed registry data (the required `statement` field of a principle), never prose
    invented at render time. The mathematical name is the clause the statement opens
    with; the identifier travels beside it as a lookup chip."""
    rows = []
    for c in catalog.get("concepts", []):
        st = c.get("statement") or ""
        name = st.split(":", 1)[0].strip() or short_id(c["id"])
        body = st.split(":", 1)[1].strip() if ":" in st else st
        ref = html.escape(short_id(c["id"]))
        rows.append(
            f'<dt><strong>{html.escape(name)}</strong> '
            f'<a class="chip" href="reference.html#concept-{ref}"><code>{ref}</code></a>'
            f"</dt><dd>{html.escape(body)}</dd>")
    items = "\n".join(rows)
    return f"""<section id="principles"><h2>The principles</h2>
<p>What each principle asserts. Their exact formulations, Lean statements and
presentation caveats are on the <a href="reference.html#concepts-sec">reference
page</a>.</p>
<dl class="principles">
{items}
</dl></section>"""


def site_pages(catalog: dict, have_svg: bool, dot_text: str,
               view_svgs: set[str] | None = None) -> dict[str, str]:
    """Three surfaces, three audiences.

    ``index.html`` is the atlas a mathematician reads: what is proved, over what,
    and how it was checked, in ordinary mathematical English. ``reference.html``
    carries the exact identifiers, formulations, certificates, revisions and
    corpus records, where the project's internal taxonomy is the subject matter.
    ``methods.html`` explains how each kind of checking works.

    Nothing is deleted in the move: every provenance detail the single page
    carried is still present, on the surface where a reader looking for it would
    go.
    """
    deps = catalog["dependencies"]
    e = html.escape
    view_svgs = view_svgs or set()

    ident_re = identifier_pattern(catalog)

    def prose(text: str | None) -> str:
        """Reader text with identifiers marked as data."""
        return mark_identifiers(text or "", ident_re)

    concept_by_id = {c["id"]: c for c in catalog.get("concepts", [])}
    variant_by_id = {v["id"]: v for v in catalog.get("statementVariants", [])}

    def concept_display(cid: str) -> str:
        """The principle's mathematical name: the clause its statement opens with,
        which is written for a reader, rather than the registration identifier."""
        st = (concept_by_id.get(cid, {}) or {}).get("statement") or ""
        name = st.split(":", 1)[0].strip()
        return name or short_id(cid)

    def variant_display(vid: str) -> str:
        """The formulation's mathematical name. Results are about formulations, not
        principles: two formulations of one principle can be inequivalent until a
        theorem says otherwise, and naming both by their shared principle would
        render such a result as a tautology. The phrase every formulation shares,
        that it is stated at a second-order part, is dropped as noise."""
        v = variant_by_id.get(vid, {})
        name = ((v.get("description") or "").split(":", 1)[0].strip()
                or concept_display(v.get("concept", "")) or short_id(vid))
        name = re.sub(r"\s+at a second-order part", "", name)
        return re.sub(r"^,\s*|\s*,$", "", name).strip()

    def chip(identifier: str, anchor: str | None = None, page: str = "reference.html") -> str:
        """An identifier as a lookup chip: data the reader can search for, never a
        fragment of a sentence. Every chip links to its reference entry."""
        target = f"{page}#{anchor}" if anchor else page
        return (f'<a class="chip" href="{e(target)}"><code>{e(short_id(identifier))}'
                f"</code></a>")
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
        return f"{e(text)} <em>[claimed in the literature, not checked here]</em>"

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
            # Said once per surface where it applies, not once per panel.
            fig = ""
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
            # Metadata reads as data, not as a sentence: each field keeps its
            # English key and its value stays in a code element, so an identifier
            # is never a fragment of prose. Values are strings from the catalog;
            # the keys name what they are.
            FIELD_NAMES = {"family": "evidence family", "kind": "relation",
                           "fact": "fact", "record": "record", "source": "source",
                           "id": "identifier", "relation": "relation",
                           "premiseFamily": "premise family", "degree": "degree",
                           "scope": "scope", "notion": "reducibility notion",
                           "status": "verification", "revision": "revision",
                           "theorem": "checking theorem",
                           "exactLhs": "left endpoint", "exactRhs": "right endpoint"}
            bits: list[tuple[str, str]] = []
            for k, name in FIELD_NAMES.items():
                if not ed.get(k):
                    continue
                v = str(ed[k])
                if k in ("status", "scope", "kind", "relation"):
                    # a stored value rendered on every edge: boilerplate by
                    # construction, and marked so that a disclaimer copied into a
                    # field is still caught
                    rendered = {"status": prose_verification,
                                "scope": prose_scope}.get(k, KIND_PROSE.get)(v)
                    bits.append((name, f"<span data-boilerplate>"
                                       f"{e(rendered or v)}</span>"))
                else:
                    bits.append((name, f"<code>{e(v)}</code>"))
            if ed.get("contexts"):
                bits.append(("contexts", ", ".join(
                    f"<code>{e(c)}</code>" for c in ed["contexts"])))
            if ed.get("certificates"):
                bits.append(("certificates", ", ".join(
                    f"<code>{e(str(c))}</code>" for c in ed["certificates"] if c)))
            if ed.get("derivationText"):
                bits.append(("derivation", f"<code>{e(ed['derivationText'])}</code>"))
                bits.append(("premises", ", ".join(
                    f"<code>{e(x)}</code>" for x in ed.get("leaves", []))))
            if ed.get("records"):
                bits.append(("records, both directions", ", ".join(
                    f"<code>{e(x)}</code>" for x in ed["records"])))
            if ed.get("derivation") == "strongImpliesOrdinary":
                bits.append(("both directions", "<span data-boilerplate>one is "
                             "certified strong and is "
                             "shown here at the ordinary notion by the explicit "
                             "weakening; the other is certified at the ordinary "
                             "notion only</span>"))
            detail = ("<dl class=\"fields\">"
                      + "".join(f"<dt>{n}</dt><dd>{v}</dd>" for n, v in bits)
                      + "</dl>")
            # the label already encodes the connector (⊨ω →, ≤sW, ⇔, …); fall back to a
            # bare arrow only when a view supplies none
            conn = ed.get("label") or ("⇔" if ed.get("bidirectional") else "→")
            items.append(f"<li><code>{e(str(src))}</code> {e(conn)} "
                         f"<code>{e(str(tgt))}</code>"
                         f"<br/><small>{detail}</small></li>")
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
<span class="lg">{arrow("#444", "1.3")} a proof in ambient Lean showing how one argument
factors through another; it carries no claim about strength</span>
<span class="lg">{arrow("#444", "2.8")} ⊨ω: an implication proved over every Turing ideal</span>
<span class="lg">{arrow("#444", "2.8", both=True)} ⊨ω: an equivalence proved over every Turing ideal</span>
<span class="lg">{arrow("#444", "2.8", head="tee")} ⊭ω: a failure, witnessed by an explicit
countermodel</span>
<span class="lg">{arrow("#444", "1.6", dash="5 3")} a strong Weihrauch reduction, proved in a
separate development</span>
<span class="lg">{arrow("#444", "1.6", dash="5 3", open_head=True)} a Weihrauch reduction, proved in a
separate development</span>
<span class="lg">{arrow("#444", "1.6", dash="5 3", both=True, open_head=True)} Weihrauch reductions both ways: the
filled end is strong, the open end ordinary</span>
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
        # vertical placement is geometry, so it must never be the only provenance:
        # every literature band states what positions it, and that nothing is certified
        bands = "".join(
            f'<p>{e(" and ".join(concept_display("reverse-mathlib:" + c) for c in b["concepts"]))}'
            f' are drawn above {e(concept_display("reverse-mathlib:" + b["above"]))}. '
            f'This is placement from the literature; no comparison between them is '
            f'proved here. It rests on the recorded finding '
            f'<code>{e(b["order"]["claim"])}</code>: {prose(b["order"]["reading"])}.</p>'
            for b in v.get("literatureBands", []))
        fine_print = (f'<details class="fineprint"><summary>Projection fine print '
                      f'(exact merge and enclosure rules)</summary>'
                      f'<p>{e(v["comment"])}</p>{bands}</details>')
        return (f'<h2 id="overview">Concept overview — a noncanonical, lossy, '
                f'direct-only projection</h2>\n'
                f'<p><em>One edge per direct evidence record, projected to concept '
                f'granularity for orientation only; the per-family graphs below are '
                f'canonical.</em></p>\n{fine_print}\n'
                f'{legend_html() if view_svgs else ""}\n{panel}\n'
                f'{principles_section(catalog)}')

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
        missing = ("" if view_svgs else
                   "<p><em>Graphviz was not available when these pages were built, so "
                   "the pictures are absent. Every edge is listed below each panel, "
                   "which is the form these graphs are read in either way.</em></p>\n")
        return ('<h2 id="graphs">Canonical graphs, one per kind of evidence and never '
                'flattened together</h2>\n'
                '<p><em>Line styles as in the legend under the concept projection '
                'above.</em></p>\n' + missing
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
                    + (f" — {prose(ev['note'])}" if ev.get("note") else "") + "</li>"
                    for ev in f_["evidence"]))
            note_block = f"<p>{prose(f_['note'])}</p>" if f_.get("note") else ""
            study_link = case_study_link(f_["id"])
            cards.append(f"""<div class="card" data-family="certified" id="fact-{e(f_['id'])}">
<h3><code>{e(lhs)}</code> {arrow} <code>{e(rhs)}</code>
<span class="tag">{e(KIND_PROSE.get(f_['kind'], f_['kind']))}</span>
<span class="tag" data-boilerplate>{e(prose_verification('kernelChecked'))}</span>
<span class="tag" data-boilerplate>{e(prose_scope(ctx.get('scope')))}</span></h3>
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
            cards.append(f"""<details class="card" id="concept-{e(short_id(c['id']))}">
<summary><strong>{e(gloss(c['statement']))}</strong> <code>{e(short_id(c['id']))}</code></summary>
<p>{e(c['statement'])}</p>
<p class="meta">{prose(c['description'])}</p>
{refs_block}{study_link}</details>""")
        return section("concepts-sec", "Concepts", len(cards), "\n".join(cards))

    def variant_index() -> str:
        cards = []
        for v in catalog["statementVariants"]:
            cards.append(f"""<details class="card">
<summary><strong>{e(gloss(v['description']))}</strong> — <code>{e(v['id'])}</code>
<span class="tag">{e(v['layer'])}</span></summary>
<p>{prose(v['description'])}</p>
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
— <code>{e(d['id'])}</code> <span class="tag"><code>{e(d['status'])}</code></span></summary>
<dl>
<dt>derivation</dt><dd><code>{e(d['derivationText'])}</code></dd>
<dt>premises cited</dt><dd><ul>{leaves}</ul></dd>
<dt>premise family</dt><dd><code>{e(d['premiseFamily'])}</code>
(<code>{e(d['relation'])}</code>)</dd>
<dt>note</dt><dd>{prose(d['note'])}</dd>
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
        # Every record shares one source, one artifact and one set of dependencies.
        # Stating those once and showing only what differs per record keeps the
        # provenance complete without printing it ten times.
        first = bes[0]["source"]
        deps0 = first["dependencies"]
        shared = (
            f'<p class="shared">All records below come from '
            f'<code>{e(first["repository"])}</code> at export revision '
            f'<code>{e(first["exportRevision"])}</code>, artifact '
            f'<code>{e(first["artifactRevision"])}</code> '
            f'(<a href="https://github.com/{e(first["repository"])}/blob/'
            f'{e(first["artifactRevision"])}/evidence/rmlib-bridge-evidence.json">raw '
            f'artifact</a>, vendored at <code>{e(first["artifactPath"])}</code>), '
            f'checked against reverse-mathlib <code>{e(deps0["reverse-mathlib"])}</code>, '
            f'Foundation <code>{e(deps0["Foundation"])}</code>, mathlib '
            f'<code>{e(deps0["mathlib"])}</code> on toolchain '
            f'<code>{e(first["toolchain"])}</code>, by the Lean kernel with the three '
            f'standard axioms permitted. Any record differing in any of these carries '
            f'its own line.</p>')
        cards = []
        for r in bes:
            src, chk = r["source"], r["checking"]
            deps = src["dependencies"]
            rows = [("statement", e(r["display"]["rendered"])),
                    ("checking theorem",
                     f"<code>{e(r.get('theorem') or '(none)')}</code>"),
                    ("export", f"<code>{e(r['export'])}</code>")]
            differs = []
            if src["repository"] != first["repository"] or \
                    src["exportRevision"] != first["exportRevision"] or \
                    src["artifactRevision"] != first["artifactRevision"] or \
                    deps != deps0 or src["toolchain"] != first["toolchain"]:
                differs.append(("source", f"<code>{e(src['repository'])}</code> at "
                                f"<code>{e(src['exportRevision'])}</code>, artifact "
                                f"<code>{e(src['artifactRevision'])}</code>"))
            if chk.get("mechanism") != first.get("checking", {}).get("mechanism"):
                differs.append(("checked by", f"<code>{e(chk.get('mechanism') or '')}</code>"))
            if r.get("downgraded"):
                differs.append(("downgraded", e(r["downgraded"])))
            body = "".join(f"<dt>{n}</dt><dd>{v}</dd>" for n, v in rows + differs)
            cards.append(f"""<details class="card" data-family="backend" id="backend-{e(r['id'])}">
<summary><code>{e(r['id'])}</code>
<span class="tag" data-boilerplate>{e(prose_verification(r['status']))}</span></summary>
<dl>{body}</dl></details>""")
        return section(
            "backend-sec", "Results from the semantics bridge", len(cards),
            shared + "\n" + "\n".join(cards),
            "<p><em>Results checked in the external Lean development that formalizes "
            "the syntax and semantics of second-order arithmetic, ingested with the "
            "statement fingerprint recomputed here. Three kinds are kept apart: that "
            "every Turing ideal realizes the theory, which is one direction only; that "
            "a formal sentence and a property used here agree at every second-order "
            "part; and that a sentence is not derivable in a named calculus. The "
            "converse direction, that every model of the theory is a Turing ideal, is "
            "not proved, so nothing here may be read as an unqualified statement about "
            "RCA₀. These records contribute the two results shown on the "
            "<a href=\"index.html#bridge\">atlas</a> and nothing else.</em></p>\n")

    def corpus_section() -> str:
        corpus = catalog.get("corpus")
        if not corpus:
            return ""
        cards = []
        for a in corpus.get("audits", []):
            cards.append(f"""<details class="card" data-family="corpus">
<summary><strong>{e(gloss(a['scope'], 80))}</strong> — <code>{e(a['id'])}</code>
<span class="tag">audit</span></summary>
<dl><dt>scope</dt><dd>{prose(a['scope'])}</dd>
<dt>outcome</dt><dd><strong>{prose(a['outcome'])}</strong></dd></dl></details>""")
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
<span class="tag">not proved: a correspondence this atlas needs</span></summary>
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
            "correspondence listed as unproved is one this atlas needs and has not proved, never "
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
                f'{e(str(c.get("scope", "")))}</span><br/>{prose(c["description"])} '
                f'— context predicate <code>{e(c.get("contextDecl") or "")}</code></div>')
        notions = catalog.get("reducibilityNotions", [])
        if notions:
            parts.append("<h3>Reducibility notions</h3>")
            for n_ in notions:
                parts.append(f'<div class="refitem"><code>{e(n_["id"])}</code><br/>'
                             f'{prose(n_["description"])}</div>')
        corpus = catalog.get("corpus", {})
        if corpus.get("sources"):
            parts.append("<h3>Pinned corpus sources</h3><ul>")
            for src in corpus["sources"]:
                parts.append(f"<li><code>{e(src['namespace'])}</code> @ "
                             f"<code>{e(src['pin'])}</code> — {prose(src['description'])}</li>")
            parts.append("</ul>")
        if corpus.get("presentationFamilies"):
            parts.append("<h3>Presentation families</h3><ul>")
            for f_ in corpus["presentationFamilies"]:
                parts.append(f"<li><code>{e(f_['id'])}</code> — {prose(f_['description'])}</li>")
            parts.append("</ul>")
        return "\n".join(parts)

    def fact_summary(f_: dict) -> str:
        """One sentence saying what the result asserts, in ordinary mathematical
        English. A curated sentence is used when the catalog carries one;
        otherwise the sentence is composed from the principles and the context, so
        a newly registered result is never silently unlabelled."""
        if f_.get("summary"):
            return f_["summary"]
        def mid_sentence(name: str) -> str:
            """A formulation name opening with an article is capitalised as a
            heading; inside a sentence the article is not."""
            first, _, rest = name.partition(" ")
            return f"{first.lower()} {rest}" if first in ("The", "A", "An") else name

        lhs = mid_sentence(variant_display(f_.get("lhs", [""])[0]))
        rhs = mid_sentence(variant_display(f_.get("rhs", [""])[0]))
        where = ("over every Turing ideal"
                 if f_.get("context", {}).get("scope") == "omegaModels"
                 else prose_scope(f_.get("context", {}).get("scope")))
        where = where[:1].upper() + where[1:]
        if f_["kind"] == "equivalence":
            return f"{where}, {lhs} is equivalent to {rhs}."
        if f_["kind"] == "nonImplication":
            return (f"{where}, {lhs} does not imply {rhs}; an explicit countermodel "
                    f"witnesses the failure.")
        return f"{where}, {lhs} implies {rhs}."

    def bridge_summary(x: dict) -> str:
        """One sentence for a result checked in the external bridge, stated at the
        exact objects it is about.

        These results concern a named theory and a named sentence in that bridge,
        under a named model class or a named calculus. Rendering them as claims
        about RCA₀ and weak Kőnig's lemma would promote them past what was proved:
        whether the bridge's theory captures RCA₀ is exactly the direction that
        remains open.
        """
        if x.get("summary"):
            return x["summary"]
        theory = f'<code>{e(x.get("theory", "the bridge theory"))}</code>'
        sentence = f'<code>{e(x.get("sentence", "the sentence"))}</code>'
        qualifier = f'<code>{e(x.get("qualifierId", ""))}</code>'
        if x.get("kind") == "semanticCountermodel":
            return (f"There is a model of the bridge theory {theory} in which its "
                    f"sentence {sentence} fails, among the structures {qualifier}.")
        if x.get("kind") == "calculusNonderivability":
            return (f"The bridge sentence {sentence} is not derivable from the bridge "
                    f"theory {theory} in the calculus {qualifier}.")
        return e(x.get("statement", ""))

    def methods_sections() -> str:
        """How each kind of checking works. Implementation vocabulary belongs on
        this surface, because the machinery is the subject."""
        return f"""<h2 id="kernel">Results proved in Lean</h2>
<p>A principle is stated as a property of the second-order part of an ω-model: a
collection of subsets of ℕ closed downwards under Turing reducibility and under
recursive join, which is what a Turing ideal is. A result is a Lean theorem quantified
over all such parts, and it is accepted only when the Lean kernel checks it and the
axiom audit finds nothing beyond propositional extensionality, quotient soundness and
choice.</p>
<p>Each result also records which lemmas its proof reaches and which it must avoid.
These dependency conditions are checked at build time, so a proof cannot quietly start
using the theorem it is supposed to be independent of.</p>
<h2 id="ambient">Factorizations in ambient Lean</h2>
<p>Some results are proved in ordinary Lean over the standard natural numbers rather
than at a second-order part. They show how one proof factors through another and carry
no model-theoretic scope, so they never contribute to the counts on the atlas.</p>
<h2 id="imported">Reductions from a separate development</h2>
<p>Weihrauch reductions are proved in a separate Lean development for computable
analysis and recorded here with the revision they were checked at and the name of the
checking theorem. They are read as evidence, never as axioms: nothing in this
repository assumes them.</p>
<h2 id="bridge">The semantics bridge</h2>
<p>A second Lean development formalizes the syntax and the semantics of second-order
arithmetic. Two things are checked there and imported: that every Turing ideal
realizes an explicit theory on ω-structures, and that a formal sentence and the
property used here agree at every second-order part. The reverse direction, that every
model of the theory is a Turing ideal, is not proved, so no result here may be read as
an unqualified statement about RCA₀.</p>
<p>Records are ingested with a fingerprint of the statement recomputed locally, so a
record whose statement drifted from the one this atlas expects fails ingestion instead
of being displayed.</p>
<h2 id="derived">Consequences drawn by composition</h2>
<p>Composing two results gives a third. Those consequences are displayed as explicit
derivations, each with the premises it used, and they are counted nowhere. They are
written by hand rather than searched for, so the atlas never shows a chain nobody
examined.</p>
<h2 id="corpus">Findings quoted from the literature</h2>
<p>Statements from the literature are recorded with their source, the exact locator,
and the wording as it appears there. A finding that something is absent from a source
means only that it was not found in the pinned snapshot. Where a classification in the
literature concerns a formulation different from the one proved here, the translation
that would be needed is named and marked as unproved.</p>
<h2 id="graphs-methods">How the pictures are drawn</h2>
<p>Every arrow is one recorded result. Nothing is inferred from the drawing: there is
no transitive closure in the canonical graphs, and where a principle is placed above
another without an arrow, the placement comes from a recorded literature finding and
is labelled as such.</p>"""

    # ---- shared page shell ---------------------------------------------
    def surfaces_nav(current: str) -> str:
        items = [("index.html", "Atlas"), ("reference.html", "Reference"),
                 ("methods.html", "Methods")]
        parts = []
        for href, label in items:
            parts.append(f"<strong>{e(label)}</strong>" if href == current
                         else f'<a href="{e(href)}">{e(label)}</a>')
        return ('<nav class="surfaces">' + " · ".join(parts)
                + ' · <a href="https://github.com/cameronfreer/reverse-mathlib">'
                  "cameronfreer/reverse-mathlib</a></nav>")

    def shell(page: str, title: str, body: str, script: str = "") -> str:
        return f"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{e(title)}</title>
<style>
{SITE_CSS}
</style></head><body><main>
<h1>{e(title)}</h1>
{surfaces_nav(page)}
{body}
<footer>{"The data behind these pages: " if page == "index.html" else "Canonical data: "}
<a href="catalog.direct.json"><code>catalog.direct.json</code></a>
{"" if page == "index.html" else f'(schema <code>{e(catalog["schema"])}</code>) '}—
Lean {e(deps["leanVersion"])}, mathlib <code>{e(deps["mathlibRevision"])}</code>.
{"" if page == "index.html" else "There is no timestamp by design: the data depends only on the environment and the revisions above."}</footer>
</main>{script}</body></html>
"""

    # ---- the atlas: what is proved, over what, and how it was checked ----
    def public_scoreboard() -> str:
        omega = len([f_ for f_ in catalog.get("facts", []) if f_.get("evidence")
                     and f_.get("context", {}).get("scope") == "omegaModels"])
        counter = len([x for x in catalog.get("scopedResults", [])
                       if x.get("kind") == "semanticCountermodel"])
        nonderiv = len([x for x in catalog.get("scopedResults", [])
                        if x.get("kind") == "calculusNonderivability"])
        return f"""<ul class="scoreboard">
<li>Proved in Lean over Turing-ideal ω-models: <strong>{omega}</strong></li>
<li>Countermodels over general second-order structures: <strong>{counter}</strong>,
checked in the pinned external Lean bridge</li>
<li>Nonderivability results relative to a fixed proof calculus:
<strong>{nonderiv}</strong>, checked in the pinned external Lean bridge</li>
</ul>"""

    def public_results_table() -> str:
        facts = [f_ for f_ in catalog.get("facts", []) if f_.get("evidence")]
        rows = []
        for f_ in sorted(facts, key=lambda x: x["id"]):
            lhs = f_.get("lhs", [""])[0]
            rhs = f_.get("rhs", [""])[0]
            sym = RELATION_SYMBOL.get(f_["kind"], "⇒")
            label = f"{variant_display(lhs)} {sym} {variant_display(rhs)}"
            ctx = f_.get("context", {})
            summary = fact_summary(f_)
            rows.append(
                f"<tr><td><strong>{e(label)}</strong><br/>"
                f'<span class="meta">{e(summary)}</span></td>'
                f'<td class="how" data-boilerplate>'
                f'{e(prose_verification("kernelChecked"))}<br/>'
                f'{e(prose_scope(ctx.get("scope")))}</td>'
                f'<td class="how">{chip(f_["id"], "fact-" + f_["id"])}</td></tr>')
        return ('<div class="wrapscroll"><table class="results">'
                "<thead><tr><th>Result</th><th>How it was checked</th>"
                "<th>Reference</th></tr></thead><tbody>"
                + "\n".join(rows) + "</tbody></table></div>")

    def public_bridge_results() -> str:
        items = []
        for x in catalog.get("scopedResults", []):
            rec = x.get("sourceId", "")
            items.append(
                f"<li>{bridge_summary(x)} "
                f"<span class=\"meta\">({e(prose_scope(x.get('scope')))})</span> "
                f"{chip(rec, 'backend-' + rec) if rec else ''}</li>")
        if not items:
            return ""
        return "<ul>" + "\n".join(items) + "</ul>"

    def public_graph() -> str:
        v = views["concept-projection"]
        # The legend explains the picture, so it appears only when the picture
        # does. Graphviz is optional: without it the atlas still states its
        # results, and the reference surface carries the edge lists.
        has_img = "concept-projection" in view_svgs
        img = (f'<figure class="graph"><img src="concept-projection.svg" '
               f'alt="Directed graph of the principles in this atlas: '
               f'{len(v["nodes"])} principles joined by {len(v["edges"])} results, '
               f'with weak Kőnig\'s lemma and its equivalents grouped in the centre, '
               f'the base theory below, and the jump principles above."/></figure>'
               if has_img else "")
        if not has_img:
            return ""
        band_clause = (", or is placed there by the literature where no comparison "
                       "has been proved here" if v.get("literatureBands") else "")
        return f"""<h2 id="graph">The principles and how they relate</h2>
<p>Most boxes are principles; the lowest is the base context these results are stated
over, not a principle. Boxes inside an enclosure are formulations of one principle.
Arrows are recorded results, and there are more of them than the table below lists: the
table gives the results proved over ω-models, while the picture also carries reductions
proved in a separate development and factorizations in ambient Lean, which show how one
argument is built from another and are not claims about strength. The direction of an
arrow carries the mathematics; height is layout. The base context sits at the bottom,
and a principle joined to the central circle by a one-way arrow sits above it: an arrow
pointing down into the circle marks a principle proved at least as strong as the
circle{band_clause}, while an arrow pointing up out of the circle marks one the circle
implies, whose own strength may remain unresolved.</p>
{img}
{legend_html()}
<p class="meta">Exact endpoints, certificates and downloads for every arrow are on the
<a href="reference.html#graphs">reference page</a>.</p>"""

    def proved_box() -> str:
        # the scoreboard's typed filter: certified facts at ω-model scope
        # (kernelChecked by construction) — a future fact at another scope
        # must never inflate this sentence
        n_omega = len([f for f in catalog.get("facts", []) if f.get("evidence")
                       and f.get("context", {}).get("scope") == "omegaModels"])
        spelled = {6: "six", 7: "seven", 8: "eight", 9: "nine", 10: "ten",
                   11: "eleven", 12: "twelve"}.get(n_omega, str(n_omega))
        return f"""<div id="proved"><h2>What is — and is not — proved</h2>
<p>Every result on this page was checked by a machine. The {spelled} ω-model results are
Lean theorems: each says that over every Turing ideal, one principle implies another,
is equivalent to it, or fails to imply it. A failure is always witnessed by an explicit
countermodel, never asserted as underivability.</p>
<p>Turing ideals are the second-order parts of ω-models of RCA₀. That identification is
standard in the literature ([Sim09] VIII.1) and is quoted here, not proved. No result on
these pages is a claim about derivability in RCA₀. The nonderivability result is about a
named theory and a named sentence inside the bridge, in one named calculus; whether that
theory captures RCA₀ is the direction that remains unproved, and until it is proved the
result may not be read as being about RCA₀ itself.</p>
<p>Results reached by composing others are shown as derivations on the reference page
and are counted nowhere. Findings quoted from the literature are recorded with their
source and are never treated as proved here; where a translation between two
formulations would be needed and has not been proved, the atlas says so rather than
assuming it. How each kind of checking works is described under
<a href="methods.html">methods</a>.</p></div>"""

    index_body = f"""<p class="lede">A machine-checked atlas of principles from
reverse mathematics. Each principle is stated at a second-order part of an ω-model,
each relation between principles is a Lean theorem checked by the kernel, and every
statement of provenance on these pages is separated from what has actually been
proved.</p>
{public_scoreboard()}
{public_graph()}
{principles_section(catalog)}
<h2 id="results">Results</h2>
{public_results_table()}
<h2 id="bridge">Results from the external bridge</h2>
<p>Two further results are checked in a separate Lean development that formalizes the
syntax and semantics of second-order arithmetic. They are stated about a theory and a
sentence defined in that development, under a named class of structures or a named
calculus, and they are not statements about RCA₀ or about weak Kőnig's lemma as such.</p>
{public_bridge_results()}
{proved_box()}"""

    methods_body = f"""<p class="lede">How each kind of result on this atlas is
checked, and what a reader is entitled to conclude from it.</p>
{methods_sections()}"""

    reference_body = f"""<p class="lede">Exact identifiers, formulations, Lean
statements, certificates, revisions and corpus records. The project's internal
vocabulary is used here deliberately: this surface is the dictionary.</p>
<p class="filters">Filter:
<input type="text" id="ftext" placeholder="text, ids, theorems…" oninput="applyFilter()">
<select id="ffam" onchange="applyFilter()"><option value="">all families</option>
<option>ambient</option><option>certified</option><option>imported</option>
<option>backend</option><option>computed</option><option>corpus</option></select>
<noscript>(filtering needs JavaScript; all content below is fully visible without
it)</noscript></p>
<nav class="toc"><strong>Contents:</strong>
<a href="#overview">Concept projection</a> ·
<a href="#facts-sec">Certified facts</a> ·
<a href="#graphs">Canonical graphs</a> ·
<a href="#concepts-sec">Concepts</a> ·
<a href="#variants-sec">Variants</a> ·
<a href="#ports-sec">Proof analyses</a> ·
<a href="#imports-sec">Imported reductions</a> ·
<a href="#backend-sec">Bridge records</a> ·
<a href="#computed-sec">Computed closure</a> ·
<a href="#corpus-sec">Corpus audits</a> ·
<a href="#reference">Dictionaries</a></nav>
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
{reference_section()}"""

    return {
        "index.html": shell("index.html", "reverse-mathlib atlas", index_body),
        "methods.html": shell("methods.html", "reverse-mathlib atlas: methods",
                              methods_body),
        "reference.html": shell("reference.html", "reverse-mathlib atlas: reference",
                                reference_body,
                                script="<script>" + FILTER_SCRIPT + "</script>"),
    }



# ---------------------------------------------------------------------------
# Typed computed closure (view-only)
#
# A derivation is a typed proof tree, never a flat premise list: premise
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
                "certified EFILCω → Hallω implication. Hall's reversal remains an "
                "open question.",
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
                "equivalence used forward, then the WKLω → Hallω chain.",
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
                "refutes the source of any implication into the refuted target).",
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
                "certified equivalence).",
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
                "presentations — not a presentation correspondence: the recorded "
                "perfectMatchingToOneSidedOmega bridge (an exact correspondence, not "
                "a one-way ω implication) has not been proved, and no fact is registered.",
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
                "elimination of the certified equivalence).",
    },
    {
        "id": "computed.omega.jumpClosureImpliesWkl",
        "term": ["transitivity",
                 ["fact", "jumpClosureBoundedKonigOmega"],
                 ["equivalenceElimForward", ["fact", "boundedKonigWklOmega"]]],
        "expect": {
            "family": "certifiedOmegaFact", "relation": "implication",
            "lhs": "jumpClosure.turingIdealClosure.turingIdealOmega",
            "rhs": "wkl.binaryTree.turingIdealOmega",
            "contexts": ["rca0.turingIdealOmega"]},
        "note": "jump closureω → WKLω: the certified jump closure → bounded-Kőnig "
                "implication, then the bounded-Kőnig ⇔ WKL equivalence used "
                "forward. The binary-tree consequence stays derived-only — no "
                "direct specialization fact is registered.",
    },
]


# Canonical direct-edge constructors. One definition per family, shared by the
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
    relation, and exact endpoint composition at every node."""
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
        "comment": "Derived edges, shown but never recorded. Each derived edge is the "
                   "conclusion of an explicit proof tree, in which premise orientation is part "
                   "of the term), typechecked at every node against family-specific "
                   "rule vocabularies and exact endpoint composition. No generic "
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


def scoped_qualifying(catalog: dict) -> dict[str, tuple]:
    """The backend records REQUIRED to have exactly one scoped result each, mapped to
    their expected (scope, kind, qualifierTag, qualifierId, theory, sentence) tuple:
    backendChecked semanticCountermodels (all-model column, modelClass qualifier) and
    backendChecked calculusNonderivability records whose calculusRecord references a
    standardCalculusIdentity (syntactic column, calculus qualifier — the Henkin-safe
    nonderivability never counts)."""
    bes = catalog.get("backendEvidence", [])
    be_kind_of = {x.get("id"): x.get("kind") for x in bes}
    out: dict[str, tuple] = {}
    for r in bes:
        if r.get("status") != "backendChecked":
            continue
        data = r.get("data", {})
        if r.get("kind") == "semanticCountermodel":
            out[r["id"]] = ("allModels", "semanticCountermodel", "modelClass",
                            data.get("modelClass"), data.get("theory"),
                            data.get("sentence"))
        elif (r.get("kind") == "calculusNonderivability"
              and be_kind_of.get(data.get("calculusRecord"))
                  == "standardCalculusIdentity"):
            out[r["id"]] = ("provability", "calculusNonderivability", "calculus",
                            data.get("calculusId"), data.get("theory"),
                            data.get("sentence"))
    return out


def check_scoped_results(catalog: dict) -> list[str]:
    """Bidirectional fail-closed validation of the scopedResults family: every entry
    must reference a qualifying backendChecked record with an agreeing typed semantic
    key (qualifier tag and id included), AND every qualifying record must have exactly
    one entry — deleting the family or any entry is a reported failure, never a silent
    pass. Entries must be sorted by unique sourceIds; semantic keys unique."""
    problems: list[str] = []
    srs = catalog.get("scopedResults", [])
    qualifying = scoped_qualifying(catalog)
    sids = [sr.get("sourceId") for sr in srs]
    if sids != sorted(sids):
        problems.append("scopedResults not sorted by sourceId")
    if len(sids) != len(set(sids)):
        problems.append("duplicate sourceIds in scopedResults")
    for sr in srs:
        sid = sr.get("sourceId")
        if sr.get("verification") != "backendChecked":
            problems.append(f"scopedResults {sid}: unknown verification")
        expected = qualifying.get(sid)
        if expected is None:
            problems.append(f"scopedResults {sid}: sourceId does not reference a "
                            "qualifying backendChecked record")
            continue
        actual = (sr.get("scope"), sr.get("kind"), sr.get("qualifierTag"),
                  sr.get("qualifierId"), sr.get("theory"), sr.get("sentence"))
        if actual != expected:
            problems.append(f"scopedResults {sid}: typed semantic key disagrees with "
                            "the source record's data")
    for qid in qualifying:
        n = sids.count(qid)
        if n != 1:
            problems.append(f"qualifying backendChecked record {qid!r} has "
                            f"{n} scoped results (exactly one required — omission "
                            "and duplication both fail)")
    sr_keys = [(x.get("kind"), x.get("qualifierTag"), x.get("qualifierId"),
                x.get("theory"), x.get("sentence")) for x in srs]
    if len(sr_keys) != len(set(sr_keys)):
        problems.append("duplicate semantic keys in scopedResults")
    return problems


def selftest_scoped_results() -> list[str]:
    """Omission/tamper fixtures: each mutation of a minimal valid catalog must be
    reported by check_scoped_results. Returns fixtures that wrongly passed."""
    cm = {"id": "cm.1", "kind": "semanticCountermodel", "status": "backendChecked",
          "data": {"modelClass": "foundationStruc2General", "theory": "T",
                   "sentence": "S"}}
    stdc = {"id": "calc.std", "kind": "standardCalculusIdentity",
            "status": "backendChecked",
            "data": {"calculusId": "stdLK.v1", "sortAssumption": "nonemptySetSort",
                     "source": "doc"}}
    nd = {"id": "nd.1", "kind": "calculusNonderivability", "status": "backendChecked",
          "data": {"calculusRecord": "calc.std", "calculusId": "stdLK.v1",
                   "theory": "T", "sentence": "S"}}
    sr_cm = {"sourceId": "cm.1", "scope": "allModels",
             "verification": "backendChecked", "kind": "semanticCountermodel",
             "qualifierTag": "modelClass", "qualifierId": "foundationStruc2General",
             "theory": "T", "sentence": "S"}
    sr_nd = {"sourceId": "nd.1", "scope": "provability",
             "verification": "backendChecked", "kind": "calculusNonderivability",
             "qualifierTag": "calculus", "qualifierId": "stdLK.v1",
             "theory": "T", "sentence": "S"}
    recs = [cm, stdc, nd]
    good = {"backendEvidence": recs, "scopedResults": [sr_cm, sr_nd]}
    if check_scoped_results(good):
        return ["minimal valid catalog wrongly rejected"]
    bad = {
        "whole family deleted": {"backendEvidence": recs},
        "all-model entry deleted": {"backendEvidence": recs,
                                    "scopedResults": [sr_nd]},
        "syntactic entry deleted": {"backendEvidence": recs,
                                    "scopedResults": [sr_cm]},
        "entry duplicated": {"backendEvidence": recs,
                             "scopedResults": [sr_cm, sr_cm, sr_nd]},
        "semantic key tampered": {"backendEvidence": recs,
                                  "scopedResults": [{**sr_cm, "sentence": "S2"},
                                                    sr_nd]},
        "qualifier tag swapped": {"backendEvidence": recs,
                                  "scopedResults": [sr_cm,
                                      {**sr_nd, "qualifierTag": "modelClass"}]},
        "verification tampered": {"backendEvidence": recs,
                                  "scopedResults": [{**sr_cm,
                                      "verification": "kernelChecked"}, sr_nd]},
        "dangling sourceId": {"backendEvidence": recs,
                              "scopedResults": [{**sr_cm, "sourceId": "cm.0"},
                                                sr_nd]},
        "scoreboard smuggling via the henkin record": {
            "backendEvidence": [cm, stdc, nd,
                {"id": "nd.henkin", "kind": "calculusNonderivability",
                 "status": "backendChecked",
                 "data": {"calculusRecord": "calc.other",
                          "calculusId": "henkinSafeV1",
                          "theory": "T", "sentence": "S"}}],
            "scopedResults": [sr_cm, sr_nd,
                {**sr_nd, "sourceId": "nd.henkin",
                 "qualifierId": "henkinSafeV1"}]},
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
            "baseContextConcepts": sorted(base_context_concepts(catalog)),
            "comment": "a lossy projection to concept granularity, not the canonical record; every "
                       "edge keeps family, scope, exact endpoint ids, and status; NO "
                       "transitive closure, only validated display merges with named "
                       "premises (antiparallel pairs; the explicit ≤sW ⇒ ≤W weakening); "
                       "missing bridges and unary form claims never render as edges. "
                       "An intra-concept calibration never renders as a concept "
                       "self-loop: its concept renders as an enclosure containing the "
                       "exact variant nodes, with the fact drawn between them. "
                       "Literature bands are corpus-backed vertical placement only — "
                       "no certified comparison edge exists where none is drawn",
            "nodes": sorted({c["id"].split(":", 1)[-1]
                             for c in catalog.get("concepts", [])}),
            "clusters": {c: {"variants": sorted(cl["variants"]),
                             "edges": cl["edges"]}
                         for c, cl in sorted(proj_clusters.items())},
            "literatureBands": literature_bands(catalog, set(proj_clusters)),
            "edges": proj_edges},
        "computed-closure": build_computed_closure(catalog),
    }


STYLE = {"ambientFactorization": 'style=solid',
         "certifiedOmegaFact": 'style=bold',
         "importedReduction": 'style=dashed',
         "computedClosure": 'style=dotted'}


def base_context_concepts(catalog: dict) -> set[str]:
    """Concepts identified as base contexts by TYPED data: a registered variant
    whose Lean interface is exactly a semantic context's contextDecl at the same
    layer. Never a hard-coded list, and never inferred from edge shapes — a
    principle that merely appears as the source of a separation edge is NOT a
    base context (see selftest_base_context)."""
    ctx_keys = {(c.get("contextDecl"), c.get("layer"))
                for c in catalog.get("semanticContexts", [])}
    return {str(v.get("concept", "")).split(":", 1)[-1]
            for v in catalog.get("statementVariants", [])
            if (v.get("interface"), v.get("layer")) in ctx_keys}


def selftest_base_context() -> list[str]:
    """Adversarial fixture: an ordinary principle whose ONLY fact is a direct
    registered nonimplication p ⊭ q (present as an actual fact in the fixture,
    so a reintroduced edge-shape heuristic would be exercised, not vacuously
    passed) must NOT be classified as a base context; a same-interface variant
    at the WRONG layer must not qualify either (the layer equality is
    load-bearing). Only a context-anchored variant interface at the matching
    layer qualifies. Returns the scenarios that wrongly passed."""
    cat = {
        "semanticContexts": [
            {"id": "ctx.l", "contextDecl": "Fix.CtxPred", "layer": "L"}],
        "statementVariants": [
            {"id": "ns:base.v", "concept": "ns:base",
             "interface": "Fix.CtxPred", "layer": "L"},
            # the edge adversary: a principle with its own interface, whose only
            # fact is the direct nonimplication below — edge shape must not matter
            {"id": "ns:p.v", "concept": "ns:p",
             "interface": "Fix.PPred", "layer": "L"},
            {"id": "ns:q.v", "concept": "ns:q",
             "interface": "Fix.QPred", "layer": "L"},
            # the layer adversary: the context's interface at a DIFFERENT layer
            {"id": "ns:notbase.v", "concept": "ns:notbase",
             "interface": "Fix.CtxPred", "layer": "L2"}],
        "facts": [
            {"id": "pq", "kind": "nonImplication",
             "context": {"scope": "omegaModels"},
             "lhs": ["ns:p.v"], "rhs": ["ns:q.v"],
             "evidence": [{"context": "ctx.l"}]}],
    }
    base = base_context_concepts(cat)
    bad = []
    if "base" not in base:
        bad.append("context-anchored concept not identified as base")
    if "p" in base:
        bad.append("nonimplication-source principle wrongly pinned as base")
    if "q" in base:
        bad.append("nonimplication-target principle wrongly pinned as base")
    if "notbase" in base:
        bad.append("same-interface wrong-layer variant wrongly pinned as base")
    return bad


def selftest_projection_layout() -> list[str]:
    """The visual-spacing rule is frozen, not merely present: in a synthetic
    projection view (no production names), a separation out of a typed
    base-context concept must receive the extra rank span (minlen) and the
    bottom-rank pin, while an ordinary separation between principles must
    not; and a base separation into an enclosure must anchor at the
    enclosure's rank-minimal member with the internal height taken off the
    span (dot cannot place virtual nodes inside a cluster, so any other
    anchor routes the edge around the side). Returns the scenarios that
    wrongly passed."""
    view = {
        "view": "concept-projection", "family": "mixed-direct-only",
        "baseContextConcepts": ["baseNode"],
        "nodes": ["baseNode", "p", "q", "r", "blob", "flatP", "mutM", "ordE",
                  "bandC", "jumpP", "jumpQ", "hallN"],
        "literatureBands": [{"concepts": ["bandC"], "above": "blob"}],
        "clusters": {
            "blob": {"variants": ["blob.top", "blob.bottom"],
                     "edges": [{"family": "certifiedOmegaFact", "label": "⊨ω",
                                "bidirectional": True, "exactLhs": "blob.bottom",
                                "exactRhs": "blob.top"}]}},
        "edges": [
            {"family": "certifiedOmegaFact", "kind": "nonImplication",
             "label": "⊭ω", "lhsConcept": "baseNode", "rhsConcept": "q"},
            {"family": "certifiedOmegaFact", "kind": "nonImplication",
             "label": "⊭ω", "lhsConcept": "baseNode", "rhsConcept": "blob"},
            {"family": "certifiedOmegaFact", "kind": "nonImplication",
             "label": "⊭ω", "lhsConcept": "p", "rhsConcept": "r"},
            {"family": "certifiedOmegaFact", "label": "⊨ω",
             "bidirectional": True, "lhsConcept": "flatP", "rhsConcept": "blob"},
            {"family": "certifiedOmegaFact", "label": "⊨ω",
             "bidirectional": True, "lhsConcept": "mutM", "rhsConcept": "blob"},
            {"family": "ambientFactorization", "label": "ambient",
             "lhsConcept": "blob", "rhsConcept": "mutM"},
            {"family": "computedClosureUnused", "label": "third",
             "lhsConcept": "mutM", "rhsConcept": "blob"},
            {"family": "certifiedOmegaFact", "label": "⊨ω",
             "bidirectional": True, "lhsConcept": "ordE", "rhsConcept": "blob"},
            {"family": "ambientFactorization", "label": "ambient",
             "lhsConcept": "p", "rhsConcept": "ordE"},
            {"family": "certifiedOmegaFact", "label": "⊨ω",
             "lhsConcept": "jumpP", "rhsConcept": "blob"},
            {"family": "certifiedOmegaFact", "label": "⊨ω",
             "bidirectional": True, "lhsConcept": "jumpQ", "rhsConcept": "jumpP"},
            {"family": "certifiedOmegaFact", "label": "⊨ω",
             "lhsConcept": "hallN", "rhsConcept": "q"}],
    }
    dot = view_dot("concept-projection", view)
    lines = [ln.strip() for ln in dot.splitlines()]
    bad = []
    if "nodesep=0.9;" not in lines:
        bad.append("concept projection lacks the lateral-gap node separation")
    ordinary = view_dot("family-view", {
        "view": "family-view", "family": "certifiedOmegaFact",
        "nodes": ["p", "q"],
        "edges": [{"family": "certifiedOmegaFact", "label": "⊨ω",
                   "lhsConcept": "p", "rhsConcept": "q"}]})
    if "nodesep" in ordinary:
        bad.append("ordinary view wrongly received the lateral-gap node "
                   "separation")
    if not any(ln.startswith('"baseNode" -> "q"') and "minlen=3" in ln
               and "weight=10" in ln for ln in lines):
        bad.append("non-enclosure base separation lacks the rank span with the "
                   "straight-up weight on the same edge")
    if not any(ln.startswith('"baseNode" -> "q"') and f'label="{TURNSTILE_PAD}⊭ω"' in ln
               for ln in lines):
        bad.append("separation label lacks the turnstile offset pad")
    if not any(ln.startswith('"blob.bottom" -> "blob.top"')
               and f'label="{TURNSTILE_PAD}⊨ω"' in ln for ln in lines):
        bad.append("equivalence label lacks the turnstile offset pad")
    if any(ln.startswith('"p" ->') and "weight" in ln for ln in lines):
        bad.append("ordinary separation wrongly received the straight-up weight")
    if any(ln.startswith('"p" ->') and "minlen" in ln for ln in lines):
        bad.append("ordinary separation wrongly received the extra rank span")
    if '{rank=min; "baseNode";}' not in dot:
        bad.append("base rank pin missing")
    enclosure = [ln for ln in lines
                 if ln.startswith('"baseNode" -> "blob.bottom"')]
    if not any('lhead="cluster_0"' in ln and "minlen=2" in ln and "weight=10" in ln
               for ln in enclosure):
        bad.append("base separation into an enclosure misses the rank-minimal "
                   "anchor with height-adjusted span")
    if any(ln.startswith('"baseNode" -> "blob.top"') for ln in lines):
        bad.append("base separation wrongly anchored at a higher enclosure member")
    if not any(ln.startswith('"flatP" -> "blob.bottom"') and "minlen=0" in ln
               and 'lhead="cluster_0"' in ln and "port" not in ln for ln in lines):
        bad.append("pendant equivalence misses the flat rank-minimal anchor")
    if dot.index('"flatP";') > dot.index("subgraph"):
        bad.append("pendant lateral node not declared before the enclosure "
                   "(left-side seating)")
    mut = [ln for ln in lines if ln.startswith(('"mutM" -> "blob.bottom"',
                                                '"blob.bottom" -> "mutM"'))]
    if not (len(mut) == 3 and all("minlen=0" in ln for ln in mut)):
        bad.append("mutual lateral pair misses flat anchoring")
    lanes = {(re.search(r"tailport=(\w+)", ln).group(1),
              re.search(r"headport=(\w+)", ln).group(1)) for ln in mut
             if "tailport=" in ln and "headport=" in ln}
    if len(lanes) != 2:
        bad.append("the outer lateral lanes did not get two distinct port fans")
    if len([ln for ln in mut if "tailport=" not in ln]) != 1:
        bad.append("exactly one lateral lane (the middle) must stay portless — "
                   "a straight arrow whenever an arrow can be straight")
    over = dict(view)
    over["edges"] = view["edges"] + [
        {"family": "importedReduction", "label": "≤W",
         "lhsConcept": "mutM", "rhsConcept": "blob"}]
    try:
        view_dot("concept-projection", over)
        bad.append("a fourth parallel lateral edge was routed instead of rejected")
    except ValueError:
        pass
    if any(ln.startswith(('"mutM" -> "blob.top"', '"blob.top" -> "mutM"',
                          '"flatP" -> "blob.top"')) for ln in lines):
        bad.append("lateral pair wrongly anchored at a higher enclosure member")
    if not any(ln.startswith('"ordE" -> "blob.top"') and "weight=0" in ln
               for ln in lines):
        bad.append("ordinary enclosure attachment misses the alignment-yield "
                   "weight")
    if any(ln.startswith('"baseNode" ->') and "weight=0" in ln for ln in lines):
        bad.append("base separation wrongly received the alignment-yield weight")
    if '"blob.top" -> "bandC" [style=invis, minlen=1];' not in dot:
        bad.append("literature band misses the invisible lift above the "
                   "enclosure's top member")
    if not any(ln.startswith('"blob.top" -> "jumpP"') and "dir=back" in ln
               and 'ltail="cluster_0"' in ln and "minlen=1" in ln
               and f'label="{TURNSTILE_PAD}⊨ω"' in ln for ln in lines):
        bad.append("certified implication into the enclosure misses the "
                   "rank-reversed lift above the top member")
    if any(ln.startswith('"jumpP" ->') for ln in lines):
        bad.append("certified implication into the enclosure was emitted "
                   "unreversed as well")
    if '{rank=same; "jumpQ"; "jumpP";}' not in dot:
        bad.append("plain-concept equivalence pair does not share a rank")
    if not any(ln.startswith('"hallN" -> "q"') and "dir=back" not in ln
               for ln in lines):
        bad.append("one-directional implication between plain concepts was "
                   "wrongly rewritten")
    if any("rank=same" in ln and "hallN" in ln for ln in lines):
        bad.append("one-directional plain implication wrongly rank-equalized")
    fake_catalog = {"corpus": {"claims": [
        {"id": "goodClaim", "concepts": ["ns:injectionRangeExistence",
                                         "ns:jumpClosure"]},
        {"id": "orderClaim", "concepts": ["ns:wkl", "ns:jumpClosure"]},
        {"id": "targetOnlyClaim", "concepts": ["ns:wkl"]}]}}
    ok_order = {"claim": "orderClaim", "reading": "r"}
    saved = list(LITERATURE_BANDS)
    try:
        for scenario, band in [
                ("unregistered claim", {"concepts": ["jumpClosure"], "above": "wkl",
                                        "claims": ["missingClaim"],
                                        "order": ok_order}),
                ("untagged concept", {"concepts": ["untaggedConcept"],
                                      "above": "wkl", "claims": ["goodClaim"],
                                      "order": ok_order}),
                ("non-enclosure target", {"concepts": ["jumpClosure"],
                                          "above": "notACluster",
                                          "claims": ["goodClaim"],
                                          "order": ok_order}),
                ("missing order record", {"concepts": ["jumpClosure"],
                                          "above": "wkl",
                                          "claims": ["goodClaim"]}),
                ("empty order reading", {"concepts": ["jumpClosure"], "above": "wkl",
                                         "claims": ["goodClaim"],
                                         "order": {"claim": "orderClaim",
                                                   "reading": "  "}}),
                ("unregistered order claim", {"concepts": ["jumpClosure"],
                                              "above": "wkl",
                                              "claims": ["goodClaim"],
                                              "order": {"claim": "nope",
                                                        "reading": "r"}}),
                # the finding this gate exists for: a claim that identifies the
                # band's own concepts but says nothing about the target
                ("order claim unrelated to the target",
                 {"concepts": ["jumpClosure"], "above": "wkl",
                  "claims": ["goodClaim"],
                  "order": {"claim": "goodClaim", "reading": "r"}}),
                ("order claim unrelated to the band",
                 {"concepts": ["jumpClosure"], "above": "wkl",
                  "claims": ["goodClaim"],
                  "order": {"claim": "targetOnlyClaim", "reading": "r"}})]:
            LITERATURE_BANDS[:] = [band]
            try:
                literature_bands(fake_catalog, {"wkl"})
                bad.append(f"literature-band validation passed a {scenario}")
            except ValueError:
                pass
        LITERATURE_BANDS[:] = [{"concepts": ["jumpClosure"], "above": "wkl",
                                "claims": ["goodClaim"], "order": ok_order}]
        if literature_bands(fake_catalog, {"wkl"}) != [
                {"concepts": ["jumpClosure"], "above": "wkl",
                 "order": {"claim": "orderClaim", "reading": "r"}}]:
            bad.append("literature-band validation mangled a valid band")
        # a band restored alongside a certified comparison edge: an otherwise
        # fully valid band must be rejected once a certified fact links a band
        # concept to the target — the certified edge is the ordering mechanism
        conflict_catalog = dict(fake_catalog)
        conflict_catalog["statementVariants"] = [
            {"id": "ns:jumpClosure.v", "concept": "ns:jumpClosure"},
            {"id": "ns:wkl.v", "concept": "ns:wkl"}]
        conflict_catalog["facts"] = [
            {"id": "comparisonFact", "kind": "implication",
             "evidence": [{"certificate": "c"}],
             "lhs": ["ns:jumpClosure.v"], "rhs": ["ns:wkl.v"]}]
        try:
            literature_bands(conflict_catalog, {"wkl"})
            bad.append("a literature band coexisting with a certified comparison "
                       "edge was accepted instead of rejected")
        except ValueError:
            pass
        # an UNCERTIFIED recorded fact retires nothing: the same band stays valid
        recorded_only = dict(conflict_catalog)
        recorded_only["facts"] = [
            {"id": "comparisonFact", "kind": "implication", "evidence": [],
             "lhs": ["ns:jumpClosure.v"], "rhs": ["ns:wkl.v"]}]
        try:
            literature_bands(recorded_only, {"wkl"})
        except ValueError:
            bad.append("a merely recorded (uncertified) fact wrongly retired a band")
    finally:
        LITERATURE_BANDS[:] = saved
    return bad


# A leading en-space (U+2002) pushes a turnstile label's glyphs right of the
# edge line so the turnstile's left vertical stroke never blends with the
# arrow — ⊨ and ⊭ alike, in every view: general rule, no per-edge tweaking. An
# en-space, not an ASCII space: graphviz emits SVG text without
# xml:space="preserve", so ASCII leading spaces collapse at render time.
TURNSTILE_PAD = " "


def _edge_label(label: str) -> str:
    return TURNSTILE_PAD + label if label.startswith(("⊨", "⊭")) else label


# Literature positioning: strength reads upward even where no certified
# comparison edge exists. Each band places concepts strictly above a named
# enclosure — placement only, never an edge. Identifying the band's concepts
# is not enough to justify the *ordering*, so every band carries an `order`
# record naming the registered corpus claim that relates the band to the
# target, plus the reading it licenses. Validated fail-closed by
# literature_bands().
# The jump-family band was retired when the eighth fact certified the comparison it
# had only licensed by literature: jumpClosureBoundedKonigOmega draws the edge, and
# height now follows the certified arrow (the rank-reversed implication rule in
# `view_dot`). The machinery and its fail-closed validation stay armed for any
# future band; a band and a certified comparison edge for the same placement must
# never coexist — that would be a duplicate ordering mechanism.
LITERATURE_BANDS: list = []


def literature_bands(catalog: dict, cluster_names: set) -> list:
    """Validate LITERATURE_BANDS against the pinned corpus, fail-closed. Every
    cited claim must be registered; every band concept must be tagged by a
    cited claim; the target must render as an enclosure; the part that
    justifies the *above* relation rather than mere identification — the band's
    `order` record — must name a registered claim that itself tags the target
    and at least one band concept, with a nonempty reading; and no band may
    coexist with a certified fact linking a band concept to the target — a
    certified comparison retires the band, and a duplicate ordering mechanism
    is an error, never a fallback. Returns the validated bands with placement
    plus the order record (the view never carries a drawn edge for a band)."""
    claims = {c["id"]: c for c in catalog.get("corpus", {}).get("claims", [])}
    variant_concept = {v["id"].split(":", 1)[-1]: v.get("concept", "").split(":", 1)[-1]
                       for v in catalog.get("statementVariants", [])}

    def endpoint_concepts(f: dict) -> set:
        return {variant_concept.get(vid.split(":", 1)[-1], "")
                for side in ("lhs", "rhs") for vid in (f.get(side) or [])}

    def tags(cid: str, why: str) -> set:
        if cid not in claims:
            raise ValueError(
                f"literature band cites unregistered corpus claim {cid} ({why})")
        return {x.split(":", 1)[-1] for x in claims[cid].get("concepts", [])}

    out = []
    for band in LITERATURE_BANDS:
        for f in catalog.get("facts", []):
            if not f.get("evidence"):
                continue
            eps = endpoint_concepts(f)
            hit = eps & set(band["concepts"])
            if band["above"] in eps and hit:
                raise ValueError(
                    f"literature band above {band['above']} coexists with the "
                    f"certified fact {f['id']} linking {sorted(hit)} to the "
                    "target — a certified comparison retires the band; a "
                    "duplicate ordering mechanism is forbidden")
        tagged: set = set()
        for cid in band["claims"]:
            tagged |= tags(cid, "concept identification")
        for c in band["concepts"]:
            if c not in tagged:
                raise ValueError(
                    f"literature band concept {c} is not tagged by its cited claims")
        if band["above"] not in cluster_names:
            raise ValueError(
                f"literature band target {band['above']} does not render as an enclosure")
        order = band.get("order") or {}
        if not order.get("claim") or not (order.get("reading") or "").strip():
            raise ValueError(
                f"literature band above {band['above']} carries no order record: "
                "a band must name the claim relating it to the target, and the "
                "reading that claim licenses")
        otags = tags(order["claim"], "order justification")
        if band["above"] not in otags:
            raise ValueError(
                f"literature band order claim {order['claim']} does not relate to "
                f"the target concept {band['above']} — identification of the band's "
                "own concepts never justifies an ordering")
        if not otags & set(band["concepts"]):
            raise ValueError(
                f"literature band order claim {order['claim']} does not relate to "
                "any band concept")
        out.append({"concepts": sorted(band["concepts"]), "above": band["above"],
                    "order": {"claim": order["claim"],
                              "reading": order["reading"]}})
    return out


def _cluster_top_anchor(cl: dict) -> str:
    """The enclosure member a literature band lifts from: the rank-top member
    (tails no intra-cluster edge in the rendered direction; ties sorted)."""
    tails = {e["exactLhs"] for e in cl["edges"]}
    tops = sorted(v for v in cl["variants"] if v not in tails)
    return tops[0] if tops else cl["variants"][0]


def _cluster_base_anchor(cl: dict) -> tuple[str, int]:
    """The enclosure member a rising base-context edge anchors at, with the
    enclosure's internal rank height above it: the rank-minimal member is one
    that heads no intra-cluster edge (in the rendered direction; ties resolved
    by sorted order), and the height is the longest intra-cluster chain rising
    from it. Purely geometric: `lhead` clips the arrow at the enclosure
    boundary either way, so the anchor never changes what the arrow points at."""
    heads = {e["exactRhs"] for e in cl["edges"]}
    bottoms = sorted(v for v in cl["variants"] if v not in heads)
    bottom = bottoms[0] if bottoms else cl["variants"][0]
    adj: dict[str, list[str]] = {}
    for e in cl["edges"]:
        adj.setdefault(e["exactLhs"], []).append(e["exactRhs"])

    def height(v: str, seen: tuple = ()) -> int:
        if v in seen:
            return 0
        return max((1 + height(w, seen + (v,)) for w in adj.get(v, [])), default=0)

    return bottom, height(bottom)


def _edge_concept(e: dict, end: str) -> str:
    if end == "t":
        return e.get("lhsConcept") or e.get("lhs") or e.get("exactLhs")
    return e.get("rhsConcept") or e.get("rhs") or e.get("exactRhs")


# Facing-side compass lanes for fanning a lateral pair's parallel flat edges
# (external-node port, member port), top lane first.
_FLAT_LANES = [("nw", "ne"), ("w", "e"), ("sw", "se")]


def _lateral_pairs(view: dict, clusters: dict) -> dict[tuple[str, str], str]:
    """The lateral-pair rule, general and typed on view structure: an external
    concept X and an enclosure C sit side by side — every {X, C} edge anchors at
    C's rank-minimal member with minlen=0, keeping lhead/ltail clipping — when
    the pair has no consistent vertical order. That is exactly when (a) X's only
    view edge is a single bidirectional equivalence with C (a pendant
    equivalence: symmetric, and nothing else places X), or (b) the pair carries
    edges in both emitted directions (a drawn 2-cycle). Pendants are declared
    before the cluster so dot's initial ordering seats them on the enclosure's
    left; mutual pairs stay on the right. Separation edges never participate —
    they keep the rising-lane rule."""
    deg: dict[str, int] = {}
    pair: dict[tuple[str, str], list[dict]] = {}
    for e in view["edges"]:
        s, t = _edge_concept(e, "t"), _edge_concept(e, "h")
        deg[s] = deg.get(s, 0) + 1
        deg[t] = deg.get(t, 0) + 1
        if (s in clusters) != (t in clusters):
            x, c = (t, s) if s in clusters else (s, t)
            pair.setdefault((x, c), []).append(e)
    lateral: dict[tuple[str, str], str] = {}
    for (x, c), es in pair.items():
        if any(e.get("kind") == "nonImplication" for e in es):
            continue
        if len(es) == 1 and deg[x] == 1 and es[0].get("bidirectional"):
            lateral[(x, c)] = "left"
        elif len({_edge_concept(e, "t") == x for e in es}) == 2:
            lateral[(x, c)] = "right"
    return lateral


def view_dot(name: str, view: dict) -> str:
    # The concept projection reads bottom-up: base-context concepts — identified
    # by typed data (base_context_concepts), never by edge shape — sit on the
    # bottom rank, with the interderivable principles as a blob above them.
    bottom_up = name == "concept-projection"
    lines = [f'digraph "{name}" {{',
             f'  rankdir={"BT" if bottom_up else "LR"};', '  node [shape=box];']
    if bottom_up:
        # Lateral pairs put several flat edges in the gap between a concept and an
        # enclosure. Without room there, the arrowheads are clipped at the enclosure
        # boundary and a two-way reduction stops reading as one.
        lines.append('  nodesep=0.9;')
    clusters = view.get("clusters", {})
    anchors = {}
    base_anchors = {}
    lateral = _lateral_pairs(view, clusters) if clusters else {}
    lat_edge: dict[int, str] = {}
    for (x, c), side in lateral.items():
        es = sorted((i for i, e in enumerate(view["edges"])
                     if frozenset((_edge_concept(e, "t"), _edge_concept(e, "h")))
                     == frozenset((x, c))),
                    key=lambda i: (view["edges"][i].get("family", ""),
                                   view["edges"][i].get("label", "")))
        if len(es) > len(_FLAT_LANES):
            # fail closed rather than wrap: a fourth parallel edge would reuse the
            # first lane's ports and silently draw two edges on top of each other
            raise ValueError(
                f"lateral pair {x} <-> {c} has {len(es)} parallel edges but only "
                f"{len(_FLAT_LANES)} distinct routing lanes exist")
        for k, i in enumerate(es):
            attr = ", minlen=0"
            if len(es) > 1 and _FLAT_LANES[k] != ("w", "e"):
                # outer lanes fan through facing compass ports; the middle lane
                # stays portless — a straight arrow whenever an arrow can be
                # straight, exactly like the single-edge pendant case
                xp, mp = _FLAT_LANES[k]
                if side == "left":
                    xp, mp = mp, xp
                if _edge_concept(view["edges"][i], "t") == x:
                    attr += f", tailport={xp}, headport={mp}"
                else:
                    attr += f", tailport={mp}, headport={xp}"
            lat_edge[i] = attr
    left_nodes = {x for (x, c), side in lateral.items() if side == "left"}
    for n in sorted(left_nodes):
        lines.append(f'  "{n}";')
    if clusters:
        # compound lets an external concept-level arrow clip at the enclosure
        # boundary instead of pointing at any particular internal variant
        lines.append('  compound=true;')
        for ci, (cname, cl) in enumerate(sorted(clusters.items())):
            tag = f"cluster_{ci}"
            anchors[cname] = (cl["variants"][0], tag)
            base_anchors[cname] = _cluster_base_anchor(cl) + (tag,)
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
                             f'[label="{_edge_label(e.get("label", ""))}", {st}{ex}];')
            lines.append('  }')
    for n in view["nodes"]:
        if n in clusters or n in left_nodes:
            continue
        lines.append(f'  "{n}";')
    base_nodes: set[str] = set()
    if bottom_up:
        base_nodes = {n for n in view.get("baseContextConcepts", [])
                      if n in view["nodes"] and n not in clusters}
        if base_nodes:
            lines.append('  {rank=min; '
                         + '; '.join(f'"{n}"' for n in sorted(base_nodes)) + ';}')
    for ei, e in enumerate(view["edges"]):
        fam = e.get("family", view.get("family", ""))
        style = STYLE.get(fam, "style=dotted")
        src = _edge_concept(e, "t")
        tgt = _edge_concept(e, "h")
        extra = ", dir=both" if e.get("bidirectional") else ""
        if ei in lat_edge:
            # lateral pair: flat edge into the rank-minimal member, clipped at
            # the enclosure boundary; fanned across compass lanes when parallel
            if src in anchors:
                node, _h, tag = base_anchors[src]
                extra += f', ltail="{tag}"'
                src = node
            if tgt in anchors:
                node, _h, tag = base_anchors[tgt]
                extra += f', lhead="{tag}"'
                tgt = node
            extra += lat_edge[ei]
        elif (bottom_up and fam == "certifiedOmegaFact"
                and e.get("kind") != "nonImplication" and not e.get("bidirectional")
                and src not in clusters and tgt in clusters):
            # A certified one-directional implication out of a plain concept into an
            # enclosure witnesses that the concept is at least as strong as the whole
            # equivalence circle, so height follows the certified arrow: the concept
            # sits strictly above the enclosure's top-rank member, and the edge is
            # emitted rank-reversed (dir=back) so the drawn arrowhead still enters
            # the enclosure it points into. This is the certified successor of the
            # literature-band lift, keyed to a fact instead of a recorded reading.
            top = _cluster_top_anchor(clusters[tgt])
            _n, tag = anchors[tgt]
            lines.append(f'  "{top}" -> "{src}" '
                         f'[label="{_edge_label(e.get("label", ""))}", '
                         f'{style}, dir=back, ltail="{tag}", minlen=1];')
            continue
        else:
            enclosure_touch = False
            if src in anchors:
                node, tag = anchors[src]
                extra += f', ltail="{tag}"'
                src = node
                enclosure_touch = True
            if tgt in anchors:
                node, tag = anchors[tgt]
                extra += f', lhead="{tag}"'
                tgt = node
                enclosure_touch = True
            if enclosure_touch and e.get("kind") != "nonImplication":
                # ordinary enclosure attachments yield x-alignment priority
                # (weight=0): they never fight the straightness of plain-node
                # chains, so a node stays vertically over its feeders instead
                # of being dragged toward the enclosure
                extra += ", weight=0"
        if e.get("family") == "computedClosure":
            # derived, never certified: dotted, and the rule name travels with the
            # edge so the geometry is never the only provenance. Open head for
            # derived implications/reductions; the tee marks a derived separation's
            # blocked direction, exactly as on direct separation edges.
            hd = "tee" if e.get("relation") == "nonImplication" else "onormal"
            lbl = _edge_label(f'{e.get("label", "")} [{e["derivationText"]}]')
            lines.append(f'  "{src}" -> "{tgt}" [label="{lbl}", '
                         f'{style}, arrowhead={hd}];')
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
            # A separation out of a base-context node spans extra ranks so the base
            # sits substantially below the blob it fails to reach, and carries a
            # high weight so dot aligns the base directly beneath its target and
            # routes the edge straight up instead of around the blob. When the target
            # is an enclosure, the rising edge anchors at the enclosure's
            # rank-minimal member: dot cannot place an edge's virtual nodes inside a
            # cluster, so an edge into a higher internal rank is forced around the
            # side regardless of weight. lhead still clips the arrow at the
            # enclosure boundary — the anchor is pure geometry — and the enclosure's
            # internal height comes off minlen so the base stays the same total
            # span below the enclosure's top member.
            src_concept = e.get("lhsConcept") or e.get("lhs") or e.get("exactLhs")
            if src_concept in base_nodes:
                tgt_concept = e.get("rhsConcept") or e.get("rhs") or e.get("exactRhs")
                span = 3
                if tgt_concept in base_anchors:
                    tgt, height, _tag = base_anchors[tgt_concept]
                    span = max(1, 3 - height)
                extra += f", minlen={span}, weight=10"
            lines.append(f'  "{src}" -> "{tgt}" [label="{_edge_label(e.get("label", ""))}", '
                         f'{style}{extra}, arrowhead=tee];')
            continue
        lines.append(f'  "{src}" -> "{tgt}" [label="{_edge_label(e.get("label", ""))}", '
                     f'{style}{extra}];')
    if bottom_up:
        for e in view["edges"]:
            if (e.get("family", view.get("family", "")) == "certifiedOmegaFact"
                    and e.get("bidirectional")
                    and e.get("kind") != "nonImplication"
                    and _edge_concept(e, "t") not in clusters
                    and _edge_concept(e, "h") not in clusters
                    and _edge_concept(e, "t") not in base_nodes
                    and _edge_concept(e, "h") not in base_nodes):
                # certified equivalence between plain concepts: equal strength
                # renders at equal height, so the pair shares a rank and the
                # equivalence edge lies flat between them
                lines.append(f'  {{rank=same; "{_edge_concept(e, "t")}"; '
                             f'"{_edge_concept(e, "h")}";}}')
    for band in view.get("literatureBands", []):
        cl = clusters.get(band["above"])
        if not cl:
            continue
        top = _cluster_top_anchor(cl)
        for c in band["concepts"]:
            # placement only, never an edge: the invisible constraint lifts the
            # literature-positioned band strictly above the enclosure's top rank
            lines.append(f'  "{top}" -> "{c}" [style=invis, minlen=1];')
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
    pages = site_pages(catalog, have_svg, dot_text, view_svgs)
    # The existing content guards keep their force across the split: markers that
    # must appear somewhere in the site are checked against the whole site, and
    # the per-surface budgets in the readability report cover the rest.
    page = "\n".join(pages.values())
    for marker in ("Canonical graphs, one per kind of evidence and never "
                   "flattened together",
                   "a lossy projection to concept granularity, not the canonical record",
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
    for retired in ("standard-calculus comparison remains pending",
                    "standard-calculus comparison still pending",
                    "standard-calculus comparison remain"):
        if retired in page:
            sys.exit(f"rmlib-zoo build: retired claim present: {retired!r} — the "
                     "comparison is recorded (independent soundness, no embedding, "
                     "no derivability transfer)")
    # one legend per surface that shows a graph: the atlas explains its picture to
    # a reader, the reference explains its own, and neither repeats the legend
    for name, text in pages.items():
        legend_count = text.count('<div class="legend"')
        shows_graph = "<img " in text
        if legend_count != (1 if shows_graph else 0):
            sys.exit(f"rmlib-zoo build: {name} should carry "
                     f"{'exactly one legend' if shows_graph else 'no legend'} "
                     f"(a legend explains a picture, so it appears only with one), "
                     f"found {legend_count}")
    # one image per rendered graph panel on the reference surface, and the single
    # orientation picture on the atlas
    expected = {"reference.html": (1 if have_svg else 0) + len(view_svgs),
                "index.html": 1 if "concept-projection" in view_svgs else 0,
                "methods.html": 0}
    for name, want in expected.items():
        got = pages[name].count("<img ")
        if got != want:
            sys.exit(f"rmlib-zoo build: {name} expected {want} graph image(s), "
                     f"found {got}")
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
                       "not proved: a correspondence this atlas needs"):
            if marker not in page:
                sys.exit(f"rmlib-zoo build: corpus section marker missing: {marker!r}")
    for name, text in pages.items():
        (site / name).write_text(text)
    # Prose measurement runs on the built pages, so what a reader meets is what
    # gets measured. The hard budgets in READABILITY_BUDGETS are enforced here and
    # fail the build; the advisory metrics beside them are reported every build and
    # enforced nowhere, since a limit on sentence length or em dash density would
    # fight good prose as readily as bad.
    report = readability.write_report(site, budgets=READABILITY_BUDGETS)
    print(f"rmlib-zoo build: wrote {dot_path.name}"
          f"{', ' + svg_path.name if have_svg else ''}, views/ambient-standard/graph.json, "
          f"site/index.html under {out}")
    print("rmlib-zoo readability (advisory metrics are reported, never enforced):")
    print(readability.summarize(report))
    if report["violations"]:
        for v in report["violations"]:
            print(f"rmlib-zoo readability: {v}")
        sys.exit("rmlib-zoo build: readability budgets exceeded")


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
