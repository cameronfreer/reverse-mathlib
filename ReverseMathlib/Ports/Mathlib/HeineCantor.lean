/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Topology.UniformSpace.HeineCantor
import ReverseMathlib.Slice.HeineFromGaugeCompactness
import ReverseMathlib.Meta.Registry
import ReverseMathlib.Ports.Catalog

/-!
# Port record: hidden-uniformity Heine from gauge compactness

Registers the gauge-compactness capability and the hidden-uniformity Heine principle
([NS18] Corollary A.2 shape), with the typed certificate of the ambient
factorization. Both are **ambient Lean factorizations** over unrestricted reals with
no RM semantic scope, no HBU-degree claim, no represented-real claim, and no entry in
the certified ω scoreboard — the checked content is the quantifier order
`∀ g, ∃ δ, ∀ f`: the modulus depends only on the local-control data.

The mathlib counterpart recorded is `CompactSpace.uniformContinuous_of_continuous` —
a **conceptual analogue by a third route**: it proves ordinary function-by-function
Heine–Cantor (uniform continuity of each continuous function, without uniform
dependence on a shared modulus) by the generic uniform-space entourage argument,
not by a gauge subcover and not sequentially. Both halves of that finding — the
positive reach of the entourage characterization and the exclusion of interval
compactness — are gated in `scripts/MetaSmoke.lean`; no claim that mathlib's proof
instantiates the gauge route is made anywhere.
-/

namespace ReverseMathlib.Ports

open ReverseMathlib

rm_concept gaugeHeineBorel where
  statement := "Gauge (canonical-cover) compactness of the unit interval: every \
    gauge positive on [0,1] admits finitely many centers whose gauge-radius \
    intervals cover it"
  description := "The HBU-shaped compactness capability ([NS18]): input is a \
    point-indexed family of positive radii, output finitely many centers — \
    deliberately distinct from countable rational-cover, sequential, and \
    maximum-attainment compactness, which are separate formulations with their own \
    presentations. Ambient interface only: unrestricted Lean proves it outright, \
    and no second-order, HBU-degree, or represented claim is attached"

rm_statement_variant gaugeHeineBorel.canonicalCover.ambient where
  concept := gaugeHeineBorel
  layer := ambient
  interface := ReverseMathlib.Standard.GaugeHeineBorelOnUnitInterval
  description := "Ambient gauge compactness on [0,1]: the subcover is an indexed \
    finite family with centers in the interval by type (never a Finset of reals — \
    no equality test on reals enters), all inequalities strict, gauges totalized \
    ambient functions with values outside the meaningful region ignored"

rm_concept uniformHeine where
  statement := "The hidden-uniformity Heine principle: for every positive pointwise \
    modulus and tolerance there is one delta uniform over every function \
    admitting that modulus"
  description := "[NS18] Corollary A.2's quantifier shape ∀g ∃δ ∀f — the modulus \
    depends only on the local-control data, never on the controlled function. \
    Deliberately distinct from ordinary Heine–Cantor, whose statement conceals \
    this dependency; establishing the stronger dependency form is the checked \
    content, and no algorithm or computational calibration is claimed"

rm_statement_variant uniformHeine.pointwiseModulus.ambient where
  concept := uniformHeine
  layer := ambient
  interface := ReverseMathlib.Standard.UniformHeineOnUnitInterval
  description := "Ambient hidden-uniformity Heine on [0,1] over totalized \
    pointwise-modulus data, strict inequalities throughout — quantifier-level \
    uniformity only; a bundled transformer or represented realizer would be a \
    separate, stronger artifact and none is registered"

/-- The typed certificate of the ambient factorization: gauge compactness implies
the hidden-uniformity Heine principle, with the chosen modulus the named
construction `gaugeUniformDelta` of the supplied subcover and gauge. -/
theorem uniformHeineRelativeCertificate :
    Meta.RelativeCertificate Standard.GaugeHeineBorelOnUnitInterval
      Standard.UniformHeineOnUnitInterval :=
  ⟨Slice.uniformHeine_of_gaugeHeineBorel⟩

revmath_port uniformHeine where
  mathlib := CompactSpace.uniformContinuous_of_continuous
  target := uniformHeine.pointwiseModulus.ambient
  relation := conceptualAnalogue
  claimedClassical := "uniform Heine-type theorems reported for several historical \
    proof routes ([NS18] §A, the attributions carrying the paper's own caveat); \
    the countable-cover Heine–Borel's reported WKL₀ level and the gauge form's \
    reported HBU level in higher-order RM are literature context only — neither \
    certified nor transferred to the registered ambient interfaces"
  note := "Ambient factorization, not an RM calibration. Mathlib's theorem is a \
    THIRD route, gated at this pin (scripts/MetaSmoke.lean): its proof reaches \
    nhdsSet_diagonal_eq_uniformity — the neighborhoods-of-the-diagonal entourage \
    characterization — and excludes isCompact_Icc: generic uniform-space \
    compactness, no gauge subcover, no sequence, and only the function-by-function \
    conclusion, without uniform dependence on a shared modulus. The registered \
    principle is the [NS18]-shaped hidden-uniformity statement instead, and the \
    factorization proof reaches no packaged mathlib compactness at all \
    (constant-level gates in scripts/MetaSmoke.lean)."
  evidence relativeProof upper kernelChecked lean
    via ReverseMathlib.Ports.uniformHeineRelativeCertificate
    assumes gaugeHeineBorel.canonicalCover.ambient
    note "Proof-only closure certified by CI (scripts/MetaSmoke.lean): reaches the \
      named delta construction gaugeUniformDelta; excludes IsCompact, \
      isCompact_Icc, the finite-subcover API, and mathlib's Heine–Cantor theorem. \
      The classical outright proof of the capability lives in a separate file with \
      mirror-image gates."

end ReverseMathlib.Ports
