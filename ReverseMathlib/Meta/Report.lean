/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ReverseMathlib.Meta.DepGraph

/-!
# Report formatting for dependency mining

Human-readable summaries and machine-readable JSON for `MineResult`s. Reporting is fail-closed:

* facts only — no reverse-mathematical strength language appears in any report;
* unknown constants are listed as unknown, never guessed at;
* truncated results are marked `INCOMPLETE` prominently, in both formats;
* every output dimension is deterministically sorted;
* JSON reports record the Lean version and (best-effort) the pinned mathlib revision, so a
  report is meaningless without its provenance. A missing manifest yields an explicit
  `"unavailable"`, not a silent omission.

Module provenance is reported (top modules by constant count) but is never a classification:
where a constant lives says nothing about the strength of what it proves.
-/

namespace ReverseMathlib.Meta

open Lean

/-- Count of constants per owning module within `names`; current-file constants are grouped
under `<current file>`. Sorted by descending count, then by module name. -/
def moduleCounts (g : DepGraph) (names : NameSet) : Array (Name × Nat) := Id.run do
  let mut acc : Std.HashMap Name Nat := {}
  for n in names.toList do
    let m := (g.nodes[n]?.bind (·.module?)).getD `«<current file>»
    acc := acc.insert m ((acc.getD m 0) + 1)
  return acc.toArray.qsort fun a b =>
    a.2 > b.2 || (a.2 == b.2 && Name.lt a.1 b.1)

/-- Count of instance-flagged constants within `names`. -/
def instanceCount (g : DepGraph) (names : NameSet) : Nat :=
  names.foldl (init := 0) fun k n => if (g.nodes[n]?).any (·.isInstance) then k + 1 else k

/-- Breakdown of the direct edges of a mined target: `(type, value, group, instances)`. -/
def directBreakdown (r : MineResult) : Nat × Nat × Nat × Nat := Id.run do
  let mut t := 0
  let mut v := 0
  let mut grp := 0
  let mut inst := 0
  for (n, k) in r.direct.toList do
    if k.typeDep then t := t + 1
    if k.valueDep then v := v + 1
    if k.declarationGroupDep then grp := grp + 1
    if (r.state.graph.nodes[n]?).any (·.isInstance) then inst := inst + 1
  return (t, v, grp, inst)

/-- Render a sorted name array as a comma-separated list, or a placeholder when empty. -/
def renderNames (names : Array Name) (ifEmpty : String := "(none)") : String :=
  if names.isEmpty then ifEmpty
  else ", ".intercalate (names.toList.map toString)

/-- Human-readable summary of a mining result. Facts only; no strength language. -/
def MineResult.summary (r : MineResult) (header : String := "#rm_deps") : String := Id.run do
  let mut lines : Array String := #[]
  lines := lines.push s!"{header} {r.target}"
  if r.truncated then
    lines := lines.push
      s!"  INCOMPLETE: traversal truncated at maxNodes; all counts below are lower bounds \
        and no absence can be concluded"
  let (t, v, grp, inst) := directBreakdown r
  lines := lines.push s!"  kernel axioms: {renderNames r.axioms}"
  lines := lines.push s!"  statement closure: {r.statement.reached.size} constants"
  lines := lines.push s!"  value closure: {r.value.reached.size} constants"
  let proofOnly := r.proofOnlyClosure
  lines := lines.push s!"  proof-only closure: {proofOnly.size} constants"
  lines := lines.push s!"  direct deps: {t} type / {v} value / {grp} group ({inst} instances)"
  let top := (moduleCounts r.state.graph proofOnly).extract 0 5
  unless top.isEmpty do
    let rendered := ", ".intercalate (top.toList.map fun (m, k) => s!"{m} ({k})")
    lines := lines.push s!"  top modules in proof-only closure: {rendered}"
  let cuts := r.state.cuts.toArray.qsort Name.lt
  unless cuts.isEmpty do
    lines := lines.push s!"  frontier cuts: {renderNames cuts}"
  lines := lines.push s!"  unknown constants: {renderNames r.unknowns "(none)"}"
  return "\n".intercalate lines.toList

/-- Best-effort read of the pinned mathlib revision from `lake-manifest.json` in the current
working directory. Returns `none` when unavailable; callers must render that explicitly. -/
def readMathlibRev : IO (Option String) := do
  try
    let contents ← IO.FS.readFile "lake-manifest.json"
    let some json := (Json.parse contents).toOption | return none
    let some pkgs := (json.getObjVal? "packages").toOption | return none
    let some arr := pkgs.getArr?.toOption | return none
    for pkg in arr do
      if (pkg.getObjValAs? String "name").toOption == some "mathlib" then
        return (pkg.getObjValAs? String "rev").toOption
    return none
  catch _ =>
    return none

/-- Machine-readable report. Records Lean version and mathlib revision (or `"unavailable"`);
`incomplete` mirrors the truncation flag so consumers cannot miss it. -/
def MineResult.toJson (r : MineResult) (mathlibRev? : Option String) : Json :=
  let (t, v, grp, inst) := directBreakdown r
  Json.mkObj
    [("target", Json.str (toString r.target)),
     ("leanVersion", Json.str Lean.versionString),
     ("mathlibRev", Json.str (mathlibRev?.getD "unavailable")),
     ("incomplete", Json.bool r.truncated),
     ("axioms", Json.arr (r.axioms.map (Json.str <| toString ·))),
     ("statementClosureSize", Json.num r.statement.reached.size),
     ("valueClosureSize", Json.num r.value.reached.size),
     ("proofOnlyClosureSize", Json.num r.proofOnlyClosure.size),
     ("directTypeDeps", Json.num t),
     ("directValueDeps", Json.num v),
     ("directGroupDeps", Json.num grp),
     ("directInstanceDeps", Json.num inst),
     ("frontierCuts", Json.arr ((r.state.cuts.toArray.qsort Name.lt).map (Json.str <| toString ·))),
     ("unknowns", Json.arr (r.unknowns.map (Json.str <| toString ·)))]

end ReverseMathlib.Meta
