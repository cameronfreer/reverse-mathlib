"""Prose measurement for the generated atlas surfaces.

Measures the **built HTML**, never the generator's source strings: what a reader
actually meets on the page is what gets measured, including text that arrives
through several layers of registration fields.

Three surfaces, three audiences, three vocabularies:

* ``index.html`` — the reader's atlas. Ordinary mathematical English. Exact
  identifiers appear only as lookup chips, never as sentence fragments.
* ``methods.html`` — how the checking works. Implementation vocabulary belongs
  here.
* ``reference.html`` — identifiers, formulations, certificates, revisions and
  corpus records. The internal taxonomy is the subject matter here.

The report separates **hard rules** (a leaked identifier, a project-management
word in reader prose, a disclaimer repeated verbatim) from **advisory metrics**
(em dash density, sentence length, compound density). Advisory numbers are
reported and tracked; they never fail a build, because prose that reads well
sometimes needs a long sentence.
"""

from __future__ import annotations

import json
import re
from html.parser import HTMLParser
from pathlib import Path

# Surfaces and the audience each one serves. A surface absent from the built
# site is simply not measured, so this module works before and after the split.
SURFACE_ROLES = {
    "index.html": "public",
    "methods.html": "methods",
    "reference.html": "reference",
}

# Words that describe how work was scheduled rather than what is true. They have
# no mathematical content and are banned from reader prose outright; deletion is
# the fix, not translation.
PROJECT_VOCABULARY = [
    "walking slice", "tranche", "production fact", "production ω fact",
    "frozen", "deliverable", "milestone", "sprint", "backlog", "roadmap",
    "checkpoint", "rollout", "ship it",
]

# Words that name the machinery rather than the mathematics. Legitimate on the
# methods and reference surfaces, where the machinery *is* the subject.
IMPLEMENTATION_VOCABULARY = [
    "backend", "crosswalk", "schema", "fingerprint", "ingest", "ingestion",
    "artifact", "catalog", "enum", "gate", "route", "spine", "downgrade",
    "capability", "interface", "port", "registry", "payload", "pipeline",
]

# Enum values the catalog uses as data. Correct in a chip or a download; wrong
# in a sentence, where they should read as ordinary English.
ENUM_TOKENS = [
    "kernelChecked", "backendChecked", "importedChecked", "computedView",
    "claimed", "reported", "omegaModels", "allModels", "provability",
    "certifiedOmegaFact", "ambientFactorization", "importedReduction",
    "computedClosure", "strongWeihrauch", "weihrauch", "nonImplication",
    "statementAdapter", "contextRealization", "semanticCountermodel",
    "calculusNonderivability", "calculusComparison", "calculusIdentity",
    "standardCalculusIdentity",
]

CAMEL_CASE = re.compile(r"\b[a-z][a-z0-9]*(?:[A-Z][A-Za-z0-9]*)+\b")
# Mathematical notation that happens to mix cases: ≤sW is the strong Weihrauch
# symbol, not a leaked identifier.
NOTATION_ALLOWED = {"sW", "sWKL"}
DOTTED_ID = re.compile(r"\b[A-Za-z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9]*){2,}\b")
SENTENCE_SPLIT = re.compile(r"(?<=[.!?])\s+(?=[A-Z(“\"])")
HYPHEN_COMPOUND = re.compile(r"\b[a-zA-Zω]+(?:-[a-zA-Z]+)+\b")
UPPER_WORD = re.compile(r"\b[A-Z]{3,}\b")

# Shouted words that are genuinely names, not emphasis.
UPPER_ALLOWED = {"WKL", "ACA", "RCA", "REC", "EFILC", "SOSOA", "DOT", "JSON",
                 "SVG", "PDF", "HTML", "CSS", "URL", "III", "II", "IV", "VIII", "LK"}


class _Extract(HTMLParser):
    """Pull reader-visible text out of built HTML as **blocks**, tracking for each
    block whether it is visible by default.

    Text is accumulated across inline markup and flushed at block boundaries, so
    a sentence interrupted by ``<strong>`` or a link stays one sentence. Without
    this, every emphasised number would split its own sentence, inflating the
    sentence count and making a fragment look like a repeated disclaimer.

    A ``<details>`` without ``open`` hides its content but still shows its
    ``<summary>``, so summaries count as default-open text while the body they
    guard does not. Nesting is tracked, since a collapsed ancestor hides
    everything below it regardless of the descendant's own ``open`` attribute.

    Text inside ``<code>`` or a lookup chip is identifier data, not prose. It is
    recorded separately and excluded from prose measurement.
    """

    SKIP = {"script", "style", "head"}
    INLINE = {"a", "strong", "em", "b", "i", "span", "code", "small", "sup",
              "sub", "abbr", "cite", "kbd", "samp", "var", "u", "s", "mark",
              "time", "q", "br", "wbr", "img"}

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.blocks: list[dict] = []
        self._buf: list[str] = []
        self._buf_code: list[str] = []
        self.images: list[dict] = []
        self.links: list[dict] = []
        self.anchors: set[str] = set()
        self._closed_depth = 0          # enclosing <details> that are collapsed
        self._details_stack: list[bool] = []
        self._chip_stack: list[str] = []
        self._code_depth = 0
        self._skip_depth = 0
        self._in_summary = False
        self._block_open = True
        self._heading: str | None = None
        self.headings: list[dict] = []

    # -- structure -------------------------------------------------------
    def _flush(self) -> None:
        """End the current block: what was accumulated becomes one unit of prose."""
        text = re.sub(r"\s+", " ", "".join(self._buf)).strip()
        code = re.sub(r"\s+", " ", " ".join(self._buf_code)).strip()
        if text or code:
            self.blocks.append({"text": text, "code": code, "open": self._block_open})
        self._buf, self._buf_code = [], []
        self._block_open = self.is_open()

    def handle_starttag(self, tag: str, attrs: list) -> None:
        a = dict(attrs)
        if tag in self.SKIP:
            self._skip_depth += 1
            return
        if tag not in self.INLINE:
            self._flush()
        elif tag in ("br", "img"):
            self._buf.append(" ")   # a line break separates words, never joins them
        if tag == "details":
            collapsed = "open" not in a
            self._details_stack.append(collapsed)
            if collapsed:
                self._closed_depth += 1
        elif tag == "summary":
            self._in_summary = True
        elif tag in ("code", "kbd", "samp"):
            self._code_depth += 1
        elif tag == "img":
            self.images.append({"src": a.get("src", ""), "alt": a.get("alt")})
        elif tag == "a" and a.get("href"):
            self.links.append({"href": a["href"], "open": self.is_open()})
        elif tag in ("h1", "h2", "h3", "h4"):
            self._heading = tag
        if a.get("id"):
            self.anchors.add(a["id"])
        if a.get("class") and "chip" in a["class"].split():
            # a lookup chip is an identifier presented as data, like <code>;
            # remember the tag that opened it so the matching end tag closes it
            self._code_depth += 1
            self._chip_stack.append(tag)

    def handle_endtag(self, tag: str) -> None:
        if tag in self.SKIP:
            self._skip_depth = max(0, self._skip_depth - 1)
            return
        if tag not in self.INLINE:
            self._flush()
        if self._chip_stack and self._chip_stack[-1] == tag:
            self._chip_stack.pop()
            self._code_depth = max(0, self._code_depth - 1)
        if tag == "details" and self._details_stack:
            if self._details_stack:
                collapsed = self._details_stack.pop()
                if collapsed:
                    self._closed_depth = max(0, self._closed_depth - 1)
        elif tag == "summary":
            self._in_summary = False
        elif tag in ("code", "kbd", "samp"):
            self._code_depth = max(0, self._code_depth - 1)
        elif tag in ("h1", "h2", "h3", "h4"):
            self._heading = None

    def is_open(self) -> bool:
        """Visible without the reader expanding anything."""
        return self._closed_depth == 0 or self._in_summary

    def handle_data(self, data: str) -> None:
        if self._skip_depth or not data.strip():
            return
        if not self._buf and not self._buf_code:
            self._block_open = self.is_open()
        if self._code_depth > 0:
            self._buf_code.append(data)
            self._buf.append(" ")          # a chip is a word gap, not a word
        else:
            self._buf.append(data)
        if self._heading:
            self.headings.append({"level": self._heading, "text": data.strip()})

    def close(self) -> None:                # flush the tail block
        super().close()
        self._flush()


def parse(html_text: str) -> _Extract:
    """Parse and close, so the final block is always flushed."""
    parser = _Extract()
    parser.feed(html_text)
    parser.close()
    return parser


def _words(text: str) -> int:
    return len(re.findall(r"\b[\w’'ω₀₁²¹]+\b", text))


def _normalize_sentence(s: str) -> str:
    """Collapse a sentence to its comparable core, so that two copies of the
    same disclaimer differing only in punctuation or spacing count as one."""
    s = re.sub(r"[\s ]+", " ", s.lower()).strip()
    return re.sub(r"[^a-z0-9ωαβ ]+", "", s)


def measure_surface(path: Path, role: str) -> dict:
    """Measure one built HTML file. Returns hard findings and advisory metrics."""
    parser = parse(path.read_text(encoding="utf-8"))

    prose_open = " ".join(b["text"] for b in parser.blocks if b["open"])
    prose_all = " ".join(b["text"] for b in parser.blocks)
    text_open = " ".join(b["text"] + " " + b["code"]
                         for b in parser.blocks if b["open"])
    text_all = " ".join(b["text"] + " " + b["code"] for b in parser.blocks)

    # -- hard rules ------------------------------------------------------
    leaks: list[dict] = []
    for m in CAMEL_CASE.finditer(prose_all):
        if m.group(0) in NOTATION_ALLOWED:
            continue
        leaks.append({"token": m.group(0), "kind": "camelCase",
                      "context": _context(prose_all, m.start())})
    for m in DOTTED_ID.finditer(prose_all):
        leaks.append({"token": m.group(0), "kind": "dottedIdentifier",
                      "context": _context(prose_all, m.start())})
    seen_enum = [tok for tok in ENUM_TOKENS
                 if re.search(rf"\b{re.escape(tok)}\b", prose_all)]

    low = prose_all.lower()
    project_hits = [w for w in PROJECT_VOCABULARY if w in low]
    impl_hits = [w for w in IMPLEMENTATION_VOCABULARY
                 if re.search(rf"\b{re.escape(w)}", low)]

    # Sentences are split *within* each text segment, never across element
    # boundaries: two adjacent paragraphs are two sentences even when the second
    # starts lowercase, and joining them first would both inflate sentence length
    # and hide a disclaimer that is repeated once per card.
    sentences = [s for b in parser.blocks
                 for s in SENTENCE_SPLIT.split(b["text"]) if _words(s) >= 6]
    counts: dict[str, int] = {}
    for s in sentences:
        key = _normalize_sentence(s)
        if len(key) >= 40:
            counts[key] = counts.get(key, 0) + 1
    dupes = [{"count": n, "sentence": k[:160]}
             for k, n in sorted(counts.items(), key=lambda kv: -kv[1]) if n > 1]

    # -- advisory metrics -------------------------------------------------
    words_open, words_all = _words(prose_open), _words(prose_all)
    lens = [_words(s) for s in sentences] or [0]
    lens_sorted = sorted(lens)
    uppercase = [w for w in UPPER_WORD.findall(prose_all) if w not in UPPER_ALLOWED]
    compounds = HYPHEN_COMPOUND.findall(prose_all)
    em = prose_all.count("—")

    return {
        "role": role,
        "words": {"defaultOpen": words_open, "total": words_all,
                  "includingCode": _words(text_all),
                  "defaultOpenIncludingCode": _words(text_open)},
        "sections": sum(1 for h in parser.headings if h["level"] == "h2"),
        "headings": [h["text"] for h in parser.headings if h["level"] in ("h1", "h2")],
        "identifierLeaks": leaks,
        "enumTokensInProse": seen_enum,
        "vocabulary": {"projectManagement": project_hits, "implementation": impl_hits},
        "duplicateSentences": dupes,
        "images": {"count": len(parser.images),
                   "missingAlt": [i["src"] for i in parser.images if not i["alt"]]},
        "links": {"count": len(parser.links),
                  "internal": sorted({l["href"] for l in parser.links
                                      if l["href"].startswith("#")})},
        "anchors": sorted(parser.anchors),
        "advisory": {
            "emDashes": em,
            "emDashesPerKiloword": round(1000 * em / max(1, words_all), 1),
            "sentences": {
                "count": len(sentences),
                "meanWords": round(sum(lens) / max(1, len(lens)), 1),
                "p90Words": lens_sorted[int(0.9 * (len(lens_sorted) - 1))],
                "over40Words": sum(1 for n in lens if n > 40)},
            "uppercaseWords": {"count": len(uppercase),
                               "distinct": sorted(set(uppercase))},
            "hyphenCompounds": {"count": len(compounds),
                                "distinct": len(set(compounds)),
                                "perKiloword": round(1000 * len(compounds)
                                                     / max(1, words_all), 1)},
        },
    }


def _context(text: str, at: int, span: int = 40) -> str:
    lo, hi = max(0, at - span), min(len(text), at + span)
    return re.sub(r"\s+", " ", text[lo:hi]).strip()


def public_text(site: Path) -> str:
    """The reader-visible text of every built surface, as plain text, so prose
    changes are reviewable in a diff without scraping HTML by hand."""
    out: list[str] = []
    for name, role in SURFACE_ROLES.items():
        p = site / name
        if not p.exists():
            continue
        parser = parse(p.read_text(encoding="utf-8"))
        out.append(f"=== {name} ({role}) ===")
        for b in parser.blocks:
            line = b["text"] + (f"  [{b['code']}]" if b["code"] else "")
            if line.strip():
                out.append(("  " if b["open"] else "· ") + line.strip())
        out.append("")
    return "\n".join(out) + "\n"


def build_report(site: Path, budgets: dict | None = None) -> dict:
    """Measure every built surface. With no budgets this is a pure measurement,
    which is how the first baseline is captured."""
    surfaces = {name: measure_surface(site / name, role)
                for name, role in SURFACE_ROLES.items()
                if (site / name).exists()}
    report = {"surfaces": surfaces, "budgets": budgets or {},
              "violations": check_budgets(surfaces, budgets) if budgets else []}
    return report


def check_budgets(surfaces: dict, budgets: dict | None) -> list[str]:
    """Hard rules only. Advisory metrics are reported, never enforced: brittle
    limits on em dashes or compounds would fight good prose instead of bad."""
    if not budgets:
        return []
    bad: list[str] = []
    for name, s in surfaces.items():
        role = s["role"]
        b = {**budgets.get("all", {}), **budgets.get(role, {})}
        if b.get("noIdentifierLeaks") and s["identifierLeaks"]:
            shown = ", ".join(sorted({x["token"] for x in s["identifierLeaks"]})[:6])
            bad.append(f"{name}: identifiers in prose rather than lookup chips: {shown}")
        if b.get("noEnumTokens") and s["enumTokensInProse"]:
            bad.append(f"{name}: catalog enum values in prose: "
                       f"{', '.join(s['enumTokensInProse'][:6])}")
        if b.get("noProjectVocabulary") and s["vocabulary"]["projectManagement"]:
            bad.append(f"{name}: project-management wording in reader prose: "
                       f"{', '.join(s['vocabulary']['projectManagement'])}")
        if b.get("noImplementationVocabulary") and s["vocabulary"]["implementation"]:
            bad.append(f"{name}: implementation wording belongs on methods or "
                       f"reference: {', '.join(s['vocabulary']['implementation'])}")
        if b.get("noDuplicateSentences") and s["duplicateSentences"]:
            d = s["duplicateSentences"][0]
            bad.append(f"{name}: a disclaimer is repeated {d['count']}× instead of "
                       f"being stated once: {d['sentence'][:80]}…")
        if b.get("maxDefaultOpenWords") and \
                s["words"]["defaultOpen"] > b["maxDefaultOpenWords"]:
            bad.append(f"{name}: {s['words']['defaultOpen']} words visible before "
                       f"expanding anything, budget {b['maxDefaultOpenWords']}")
        if b.get("maxSections") and s["sections"] > b["maxSections"]:
            bad.append(f"{name}: {s['sections']} major sections, budget "
                       f"{b['maxSections']}")
        if b.get("requireAltText") and s["images"]["missingAlt"]:
            bad.append(f"{name}: image without alternative text: "
                       f"{s['images']['missingAlt'][0]}")
        for href in b.get("requireLinks", []):
            if href not in {l for l in s["links"]["internal"]} and \
                    not any(href in x for x in s["links"]["internal"]):
                bad.append(f"{name}: expected navigation link {href} is missing")
    return bad


def summarize(report: dict) -> str:
    """One line per surface for the build log."""
    lines = []
    for name, s in sorted(report["surfaces"].items()):
        a = s["advisory"]
        lines.append(
            f"  {name} ({s['role']}): {s['words']['defaultOpen']} words open / "
            f"{s['words']['total']} total, {s['sections']} sections; "
            f"{len(s['identifierLeaks'])} identifier leaks, "
            f"{len(s['enumTokensInProse'])} enum values in prose, "
            f"{len(s['duplicateSentences'])} repeated disclaimers; "
            f"advisory: {a['emDashes']} em dashes "
            f"({a['emDashesPerKiloword']}/kword), mean sentence "
            f"{a['sentences']['meanWords']} words, "
            f"{a['uppercaseWords']['count']} shouted words, "
            f"{a['hyphenCompounds']['perKiloword']} compounds/kword")
    return "\n".join(lines)


def write_report(site: Path, budgets: dict | None = None) -> dict:
    report = build_report(site, budgets)
    (site / "readability-report.json").write_text(
        json.dumps(report, indent=1, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8")
    (site / "public-text.txt").write_text(public_text(site), encoding="utf-8")
    return report


def selftest_extraction() -> list[str]:
    """The measurement itself is fail-closed: if the parser miscounts what a
    reader sees, every budget built on it is meaningless. Returns the scenarios
    that wrongly passed."""
    bad: list[str] = []
    doc = """<h2>Head</h2><p>Alpha beta gamma delta epsilon zeta.</p>
<details><summary>Sum one</summary><p>Hidden words here now.</p></details>
<details open><summary>Sum two</summary><p>Shown words here now.</p>
<details><summary>Inner</summary><p>Nested hidden text.</p></details></details>
<p>Identifier <code>turingIdealOmega</code> in a chip, kernelChecked in prose.</p>
<p>A chip <a class="chip" href="r.html#x"><code>someIdentifier</code></a> then
plain words continue afterwards in prose.</p>
<img src="a.svg" alt="x"/><img src="b.svg"/>"""
    p = parse(doc)
    op = " ".join(b["text"] for b in p.blocks if b["open"])
    cl = " ".join(b["text"] for b in p.blocks if not b["open"])
    prose = " ".join(b["text"] for b in p.blocks)
    if "Hidden words" in op:
        bad.append("collapsed details counted as default-open")
    if "Sum one" not in op:
        bad.append("a collapsed section's summary is not counted as visible")
    if "Shown words" not in op:
        bad.append("an open details body is not counted as visible")
    if "Nested hidden" in op:
        bad.append("details nested in an open details ignored its own collapsed state")
    if "Hidden words" not in cl:
        bad.append("collapsed text vanished from the measurement entirely")
    if "turingIdealOmega" in prose:
        bad.append("an identifier inside <code> counted as prose")
    if "someIdentifier" in prose:
        bad.append("an identifier inside a lookup chip counted as prose")
    if "plain words continue" not in prose:
        bad.append("prose after a lookup chip was swallowed by the chip")
    if "kernelChecked" not in prose:
        bad.append("an enum value in a sentence escaped the prose measurement")
    if measure_images(p) != ["b.svg"]:
        bad.append("missing alternative text not detected")

    # A sentence interrupted by inline markup is still one sentence. Without
    # this, an emphasised number would split its own sentence, and the tail
    # fragment would look like a disclaimer repeated once per item.
    inline = ("<li>Countermodels over general structures: <strong>1</strong>, "
              "checked in the pinned external bridge.</li>"
              "<li>Nonderivability relative to a calculus: <strong>1</strong>, "
              "checked in the pinned external bridge.</li>")
    glued = parse("<p><strong>Weak Kőnig's lemma</strong><br/>Over every ideal.</p>")
    if "lemmaOver" in " ".join(b["text"] for b in glued.blocks):
        bad.append("a line break glued two words into a false identifier")

    q = parse(inline)
    if len(q.blocks) != 2:
        bad.append(f"inline markup split a block ({len(q.blocks)} of 2)")
    if not all(b["text"].endswith("bridge.") for b in q.blocks):
        bad.append("a sentence interrupted by inline markup was truncated")

    # Two block-level copies of one sentence are two sentences, however the
    # next block begins.
    twin = ("<p>One whole disclaimer sentence that is repeated below.</p>"
            "<p>filler words that keep the two copies apart here</p>"
            "<p>One whole disclaimer sentence that is repeated below.</p>")
    t = parse(twin)
    sents = [x for b in t.blocks
             for x in SENTENCE_SPLIT.split(b["text"]) if _words(x) >= 6]
    if len(sents) != 3:
        bad.append(f"sentences merged across block boundaries ({len(sents)} of 3)")
    keys: dict[str, int] = {}
    for x in sents:
        k = _normalize_sentence(x)
        keys[k] = keys.get(k, 0) + 1
    if max(keys.values()) != 2:
        bad.append("a disclaimer repeated in two separate blocks was not detected")
    return bad


def measure_images(parser: _Extract) -> list[str]:
    return [i["src"] for i in parser.images if not i["alt"]]
