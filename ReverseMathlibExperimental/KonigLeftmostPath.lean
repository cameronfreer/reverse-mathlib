import ReverseMathlib.Omega.BoundedTree
import ReverseMathlib.Omega.Jump

/-!
Slice A scratch: the leftmost path of an explicitly bounded tree is computable from
the jump of the tree joined with its bound, so a jump-closed Turing ideal satisfies
explicitly bounded Kőnig.

This file develops the combinatorics first (extendibility, the finite-branching
step), then the computability layer. Nothing here enters the spine until the whole
slice is green.

A plain `lake build` does not compile this file: the experimental root does not
import it, and CI will not catch a break here. Build it by name:

  lake build ReverseMathlibExperimental.KonigLeftmostPath
-/

namespace ReverseMathlib.Omega

open OracleCode

variable {Ω : OmegaPart}

/-- `T` has a node of length `n` extending the sequence decoded from `c`. -/
def ExtendsAt (T : Set ℕ) (c n : ℕ) : Prop :=
  ∃ d ∈ T, (decodeSeq d).length = n ∧ decodeSeq c <+: decodeSeq d

/-- The node `c` has extensions in `T` of every length: it is not a dead end. -/
def ExtendibleAt (T : Set ℕ) (c : ℕ) : Prop :=
  ∀ n, ExtendsAt T c ((decodeSeq c).length + n)

theorem extendsAt_of_prefixClosed {T : Set ℕ}
    (hpc : ∀ c ∈ T, ∀ k, seqCode ((decodeSeq c).take k) ∈ T)
    {c m n : ℕ} (hmn : m ≤ n) (hm : (decodeSeq c).length ≤ m)
    (h : ExtendsAt T c n) : ExtendsAt T c m := by
  obtain ⟨d, hdT, hlen, hpre⟩ := h
  refine ⟨seqCode ((decodeSeq d).take m), hpc d hdT m, ?_, ?_⟩
  · simp [decodeSeq_seqCode, List.length_take, hlen, hmn]
  · simp only [decodeSeq_seqCode]
    exact List.prefix_take_iff.mpr ⟨hpre, hm⟩



/-- The empty node is extendible in a tree with a node at every level. -/
theorem extendibleAt_root {T : Set ℕ} (h : HasNodeAtEveryLevel T) :
    ExtendibleAt T (seqCode []) := by
  intro n
  obtain ⟨d, hdT, hlen⟩ := h ((decodeSeq (seqCode ([] : List ℕ))).length + n)
  exact ⟨d, hdT, hlen, by simp⟩

/-- Length of a one-step extension, through the coding. -/
@[simp] theorem length_extend (c : ℕ) (v : ℕ) :
    (decodeSeq (seqCode (decodeSeq c ++ [v]))).length = (decodeSeq c).length + 1 := by
  simp

/-- Finitely many failures have a common witness: if every value below `b` kills the
node at some length, one length kills them all. Proved by induction on `b`, which
avoids choosing a witness function over a finite range. -/
theorem exists_common_failure {T : Set ℕ}
    (hpc : ∀ c ∈ T, ∀ k, seqCode ((decodeSeq c).take k) ∈ T) {c : ℕ} :
    ∀ b : ℕ, (∀ v < b, ¬ ExtendibleAt T (seqCode (decodeSeq c ++ [v]))) →
      ∃ N, ∀ v < b, ¬ ExtendsAt T (seqCode (decodeSeq c ++ [v]))
        ((decodeSeq c).length + 1 + N) := by
  have mono : ∀ (v k k' : ℕ), k ≤ k' →
      ¬ ExtendsAt T (seqCode (decodeSeq c ++ [v])) ((decodeSeq c).length + 1 + k) →
      ¬ ExtendsAt T (seqCode (decodeSeq c ++ [v])) ((decodeSeq c).length + 1 + k') := by
    intro v k k' hk hno hyes
    exact hno (extendsAt_of_prefixClosed hpc (by omega) (by simp) hyes)
  intro b
  induction b with
  | zero => exact fun _ => ⟨0, fun v hv => absurd hv (Nat.not_lt_zero v)⟩
  | succ b ih =>
    intro h
    obtain ⟨N, hN⟩ := ih fun v hv => h v (by omega)
    have hb : ¬ ExtendibleAt T (seqCode (decodeSeq c ++ [b])) := h b (by omega)
    rw [ExtendibleAt] at hb
    push Not at hb
    obtain ⟨n, hn⟩ := hb
    rw [length_extend] at hn
    refine ⟨max N n, fun v hv => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hlt | rfl
    · exact mono v N (max N n) (le_max_left _ _) (hN v hlt)
    · exact mono v n (max N n) (le_max_right _ _) hn

/-- A prefix extends by the next entry of any longer extension. -/
theorem prefix_snoc_of_prefix {c d : List ℕ} (h : c <+: d) (hlt : c.length < d.length) :
    c ++ [d.getD c.length 0] <+: d := by
  have hc : c = d.take c.length := List.prefix_iff_eq_take.mp h
  have hget : d[c.length]? = some (d.getD c.length 0) := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem?_eq_getElem hlt
  have : d.take (c.length + 1) = c ++ [d.getD c.length 0] := by
    rw [List.take_add_one, hget, ← hc]; rfl
  exact this ▸ List.take_prefix _ _

/-- **The finite-branching step.** An extendible node of an explicitly bounded tree has
an extendible child below the supplied bound. This is where boundedness is used: only
finitely many children have to be ruled out. -/
theorem exists_extendible_child (T : InternalBoundedTree Ω) {c b : ℕ}
    (hb : T.bound.MapsTo (decodeSeq c).length b)
    (hc : ExtendibleAt T.tree.1 c) :
    ∃ v < b, ExtendibleAt T.tree.1 (seqCode (decodeSeq c ++ [v])) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN⟩ := exists_common_failure T.prefix_closed b hcon
  obtain ⟨d, hdT, hlen, hpre⟩ := hc (1 + N)
  have hlt : (decodeSeq c).length < (decodeSeq d).length := by omega
  set v := (decodeSeq d).getD (decodeSeq c).length 0 with hv
  have hvb : v < b := T.entry_lt_bound d hdT _ b hlt hb
  refine hN v hvb ⟨d, hdT, by omega, ?_⟩
  simp only [decodeSeq_seqCode]
  exact prefix_snoc_of_prefix hpre hlt

/-- The least extendible child value of a node. `Nat.sInf` is total, so this is a
definition; that it names a genuine child is the invariant proved below. -/
noncomputable def leastChild (T : InternalBoundedTree Ω) (c : ℕ) : ℕ :=
  sInf {v | ExtendibleAt T.tree.1 (seqCode (decodeSeq c ++ [v]))}

/-! `Nat.sInf` is total, which is what makes `leastChild` a definition rather than a
choice. Its value on an empty candidate set is `0` and means nothing. Every lemma below
therefore carries the nonemptiness hypothesis explicitly, so that fallback value can never
be mistaken for a child of the tree. -/

/-- The least child is a child: only under the hypothesis that one exists. -/
theorem leastChild_extendible (T : InternalBoundedTree Ω) {c : ℕ}
    (h : ∃ v, ExtendibleAt T.tree.1 (seqCode (decodeSeq c ++ [v]))) :
    ExtendibleAt T.tree.1 (seqCode (decodeSeq c ++ [leastChild T c])) :=
  Nat.sInf_mem h

/-- The least child is least: again only where a child exists. -/
theorem leastChild_le (T : InternalBoundedTree Ω) {c v : ℕ}
    (hv : ExtendibleAt T.tree.1 (seqCode (decodeSeq c ++ [v]))) :
    leastChild T c ≤ v :=
  Nat.sInf_le hv

/-- Below the supplied bound, since the witnessing child is. -/
theorem leastChild_lt_bound (T : InternalBoundedTree Ω) {c b : ℕ}
    (hb : T.bound.MapsTo (decodeSeq c).length b)
    (hc : ExtendibleAt T.tree.1 c) : leastChild T c < b := by
  obtain ⟨v, hvb, hv⟩ := exists_extendible_child T hb hc
  exact lt_of_le_of_lt (leastChild_le T hv) hvb

/-- The leftmost path, taken one node at a time. -/
noncomputable def leftmostNode (T : InternalBoundedTree Ω) : ℕ → ℕ
  | 0 => seqCode []
  | n + 1 => seqCode (decodeSeq (leftmostNode T n) ++ [leastChild T (leftmostNode T n)])

@[simp] theorem leftmostNode_length (T : InternalBoundedTree Ω) :
    ∀ n, (decodeSeq (leftmostNode T n)).length = n
  | 0 => by simp [leftmostNode]
  | n + 1 => by simp [leftmostNode, leftmostNode_length T n]

/-- **The invariant.** Every node of the leftmost path is extendible, so the path never
walks into a dead end. Induction on the length, with the finite-branching step supplying
the child at each stage. -/
theorem leftmostNode_extendible (T : InternalBoundedTree Ω)
    (hlev : HasNodeAtEveryLevel T.tree.1) :
    ∀ n, ExtendibleAt T.tree.1 (leftmostNode T n)
  | 0 => extendibleAt_root hlev
  | n + 1 => by
    have hprev := leftmostNode_extendible T hlev n
    obtain ⟨b, hb⟩ := T.bound.total (decodeSeq (leftmostNode T n)).length
    obtain ⟨v, _, hv⟩ := exists_extendible_child T hb hprev
    exact leastChild_extendible T ⟨v, hv⟩

/-! ### The base oracle is available through its own jump

The construction below uses `jumpSet (T ⊕ bound.graph)` as its **only** oracle, so the
advertised graph-level reduction is exact. Recovering the base set from its jump is what
makes that honest rather than a silent second query. -/

/-- On input `a`, query the oracle at `a.unpair.1` and diverge unless it answers yes.
The `rfind` predicate ignores its own argument: there is nothing to search for, only a
halting decision to make. -/
private theorem selfQuery_recursiveIn (A : Set ℕ) :
    Nat.RecursiveIn {charFn A} fun a : ℕ =>
      Nat.rfind fun _ => (fun z => z = 0) <$>
        (charFn A a.unpair.1).bind fun w => Part.some (1 - w) := by
  have htest : Nat.RecursiveIn {charFn A} fun q : ℕ =>
      (charFn A q.unpair.1.unpair.1).bind fun w => Part.some (1 - w) := by
    have hre : Nat.Partrec fun q : ℕ => Part.some q.unpair.1.unpair.1 := by
      apply Nat.Partrec.of_primrec
      exact Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.id)
    have hflip : Nat.RecursiveIn {charFn A} fun w : ℕ =>
        (Part.some (1 - w) : Part ℕ) :=
      (Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec
        (Nat.Primrec.sub.comp (Nat.Primrec.pair (Nat.Primrec.const 1)
          Nat.Primrec.id)))).of_eq fun w => by simp [Nat.unpaired]
    have h1 := Nat.RecursiveIn.comp
      (Nat.RecursiveIn.oracle (O := {charFn A}) (charFn A) rfl) hre.recursiveIn
    have h2 := Nat.RecursiveIn.comp hflip h1
    refine h2.of_eq fun q => ?_
    simp
  refine (Nat.RecursiveIn.rfind htest).of_eq fun a => ?_
  congr 1
  funext m
  simp

/-- **Every set is computable from its own jump.** Route-gated so the leftmost-path
construction can name a single oracle and mean it. -/
theorem le_jump (A : Set ℕ) : A ≤ᵀ jumpSet A := by
  classical
  obtain ⟨c, hc⟩ := exists_code.mp (selfQuery_recursiveIn A)
  have hval : ∀ n : ℕ, ((fun z => decide (z = 0)) <$>
      ((charFn A n).bind fun w => Part.some (1 - w))) =
      Part.some (decide (n ∈ A)) := by
    intro n
    by_cases hmem : n ∈ A <;> simp [charFn, hmem]
  have key : ∀ n : ℕ, (n ∈ A ↔ Encodable.encode (OracleCode.curry c n) ∈ jumpSet A) := by
    intro n
    rw [mem_jumpSet_iff, Denumerable.ofNat_encode, ← charFn_eq_coe, eval_curry, hc]
    simp only [Nat.unpair_pair]
    constructor
    · intro hmem
      refine Part.dom_iff_mem.mpr ⟨0, ?_⟩
      rw [Nat.mem_rfind]
      refine ⟨?_, fun hk => absurd hk (Nat.not_lt_zero _)⟩
      rw [hval]
      simpa using hmem
    · intro hd
      obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp hd
      rw [Nat.mem_rfind] at hm
      have h0 := hm.1
      rw [hval] at h0
      simpa using h0
  have hmap : Nat.Partrec fun n : ℕ =>
      Part.some (Encodable.encode (OracleCode.curry c n)) := by
    apply Nat.Partrec.of_primrec
    exact Primrec.nat_iff.mp (Primrec.encode.comp
      (primrec₂_curry.comp (_root_.Primrec.const c) _root_.Primrec.id))
  have h1 := Nat.RecursiveIn.comp
    (Nat.RecursiveIn.oracle (O := {charFn (jumpSet A)}) (charFn (jumpSet A)) rfl)
    hmap.recursiveIn
  refine h1.of_eq fun n => ?_
  simp only [Part.bind_eq_bind, Part.bind_some]
  simp only [charFn]
  congr 1
  simp [key n]

/-! ### The finite extension test

Searching for an extension of a given length is a *finite* search, because the supplied
bound confines the candidates. Enumerating them explicitly is what turns "has an extension
of length L" into something a program can decide with finitely many oracle queries. -/

/-- Every list of length `L` whose entry at each position lies below the bound there. -/
def boundedLists (bnd : ℕ → ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | L + 1 => (boundedLists bnd L).flatMap fun l =>
      (List.range (bnd L)).map fun v => l ++ [v]

theorem length_of_mem_boundedLists {bnd : ℕ → ℕ} :
    ∀ {L : ℕ} {l : List ℕ}, l ∈ boundedLists bnd L → l.length = L
  | 0, l, h => by simpa [boundedLists] using h
  | L + 1, l, h => by
    simp only [boundedLists, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨l', hl', v, _, rfl⟩ := h
    simp [length_of_mem_boundedLists hl']

/-- The enumeration is complete: any list respecting the bound appears in it. -/
theorem mem_boundedLists_of_entries {bnd : ℕ → ℕ} :
    ∀ {l : List ℕ}, (∀ i, i < l.length → l.getD i 0 < bnd i) →
      l ∈ boundedLists bnd l.length := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simp [boundedLists]
  | append_singleton l v ih =>
    intro h
    have hl : ∀ i, i < l.length → l.getD i 0 < bnd i := by
      intro i hi
      have := h i (by simp; omega)
      rwa [List.getD_append l [v] 0 i hi] at this
    have hv : v < bnd l.length := by
      have := h l.length (by simp)
      rwa [show (l ++ [v]).getD l.length 0 = v by
        simp [List.getD_eq_getElem?_getD]] at this
    simp only [List.length_append, List.length_singleton, boundedLists,
      List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨l, ih hl, v, hv, rfl⟩

/-- The finite test: some enumerated candidate of length `L` extends `c` and is in `T`. -/
def ExtendsTest (T : Set ℕ) (bnd : ℕ → ℕ) (c L : ℕ) : Prop :=
  ∃ l ∈ boundedLists bnd L, decodeSeq c <+: l ∧ seqCode l ∈ T

/-- **The test is exact.** Under the supplied bound, the finite search decides the
existential it replaces. -/
theorem extendsTest_iff (T : InternalBoundedTree Ω) {bnd : ℕ → ℕ}
    (hbnd : ∀ i, T.bound.MapsTo i (bnd i)) (c L : ℕ) :
    ExtendsTest T.tree.1 bnd c L ↔ ExtendsAt T.tree.1 c L := by
  constructor
  · rintro ⟨l, hl, hpre, hmem⟩
    exact ⟨seqCode l, hmem, by simp [length_of_mem_boundedLists hl], by simpa⟩
  · rintro ⟨d, hdT, hlen, hpre⟩
    refine ⟨decodeSeq d, ?_, hpre, by simpa⟩
    have : ∀ i, i < (decodeSeq d).length → (decodeSeq d).getD i 0 < bnd i :=
      fun i hi => T.entry_lt_bound d hdT i (bnd i) hi (hbnd i)
    have := mem_boundedLists_of_entries this
    rwa [hlen] at this

/-! ### The frontier: the finite search as a recursion on depth

`ExtendsTest` settles one length at a time but enumerates every candidate at once. For a
program the useful shape is a recursion on the depth alone, carrying the surviving nodes
as state, since that is ordinary primitive recursion with the starting node as a fixed
parameter. Prefix closure is what makes the two agree: an extension in the tree drags all
of its prefixes into the tree with it. -/

open Classical in
/-- Children of `d` in `T` below the bound, as node codes. -/
noncomputable def childrenIn (T : Set ℕ) (bnd : ℕ → ℕ) (d : ℕ) : List ℕ :=
  ((List.range (bnd (decodeSeq d).length)).map
    fun v => seqCode (decodeSeq d ++ [v])).filter fun e => decide (e ∈ T)

open Classical in
/-- The nodes of `T` exactly `k` levels below `c`, reached through `T` all the way. -/
noncomputable def frontier (T : Set ℕ) (bnd : ℕ → ℕ) (c : ℕ) : ℕ → List ℕ
  | 0 => if c ∈ T then [c] else []
  | k + 1 => (frontier T bnd c k).flatMap (childrenIn T bnd)

theorem mem_childrenIn {T : Set ℕ} {bnd : ℕ → ℕ} {d e : ℕ} :
    e ∈ childrenIn T bnd d ↔
      (∃ v < bnd (decodeSeq d).length, e = seqCode (decodeSeq d ++ [v])) ∧ e ∈ T := by
  classical
  simp only [childrenIn, List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hmem⟩; exact ⟨⟨v, hv, rfl⟩, hmem⟩
  · rintro ⟨⟨v, hv, rfl⟩, hmem⟩; exact ⟨⟨v, hv, rfl⟩, hmem⟩

/-- Frontier members are in the tree, at the expected length, extending `c`. -/
theorem frontier_spec {T : Set ℕ} {bnd : ℕ → ℕ} {c : ℕ} :
    ∀ (k e : ℕ), e ∈ frontier T bnd c k →
      e ∈ T ∧ (decodeSeq e).length = (decodeSeq c).length + k ∧
        decodeSeq c <+: decodeSeq e := by
  intro k
  induction k with
  | zero =>
    intro e he
    classical
    by_cases hc : c ∈ T
    · simp only [frontier, hc, if_true, List.mem_singleton] at he
      subst he; exact ⟨hc, by simp, List.prefix_rfl⟩
    · simp [frontier, hc] at he
  | succ k ih =>
    intro e he
    simp only [frontier, List.mem_flatMap] at he
    obtain ⟨d, hd, hchild⟩ := he
    obtain ⟨hdT, hdlen, hdpre⟩ := ih d hd
    rw [mem_childrenIn] at hchild
    obtain ⟨⟨v, _, rfl⟩, hmem⟩ := hchild
    refine ⟨hmem, by simp [hdlen]; omega, ?_⟩
    simp only [decodeSeq_seqCode]
    exact hdpre.trans (List.prefix_append _ _)

/-- **The frontier is complete.** Any tree node `k` levels below `c` is reached, because
prefix closure carries every intermediate node into the tree and `entry_lt_bound` keeps
each step inside the enumerated range. This is the same architectural boundary the finite
test uses, now stated for the recursion a program can run. -/
theorem mem_frontier_of_extends (T : InternalBoundedTree Ω) {bnd : ℕ → ℕ}
    (hbnd : ∀ i, T.bound.MapsTo i (bnd i)) {c : ℕ} :
    ∀ (k d : ℕ), d ∈ T.tree.1 → (decodeSeq d).length = (decodeSeq c).length + k →
      decodeSeq c <+: decodeSeq d → d ∈ frontier T.tree.1 bnd c k := by
  intro k
  induction k with
  | zero =>
    intro d hdT hlen hpre
    have hc : decodeSeq c = decodeSeq d := List.IsPrefix.eq_of_length hpre (by omega)
    have hcd : c = d := by
      have := congrArg seqCode hc; simpa using this
    subst hcd
    simp [frontier, hdT]
  | succ k ih =>
    intro d hdT hlen hpre
    -- the parent one level up is in the tree, by prefix closure
    set par := seqCode ((decodeSeq d).take ((decodeSeq c).length + k)) with hpar
    have hparT : par ∈ T.tree.1 := T.prefix_closed d hdT _
    have hparlen : (decodeSeq par).length = (decodeSeq c).length + k := by
      simp [hpar, List.length_take]; omega
    have hparpre : decodeSeq c <+: decodeSeq par := by
      simp only [hpar, decodeSeq_seqCode]
      exact List.prefix_take_iff.mpr ⟨hpre, by omega⟩
    have hin := ih par hparT hparlen hparpre
    -- and `d` is one of its children, below the bound
    have hlt : (decodeSeq par).length < (decodeSeq d).length := by omega
    set v := (decodeSeq d).getD (decodeSeq par).length 0 with hv
    have hvb : v < bnd (decodeSeq par).length :=
      T.entry_lt_bound d hdT _ _ hlt (hbnd _)
    have hpre2 : decodeSeq par <+: decodeSeq d := by
      simp only [hpar, decodeSeq_seqCode]
      exact List.take_prefix _ _
    have hd_eq : d = seqCode (decodeSeq par ++ [v]) := by
      have h1 : decodeSeq par ++ [v] <+: decodeSeq d := prefix_snoc_of_prefix hpre2 hlt
      have h2 : (decodeSeq par ++ [v]).length = (decodeSeq d).length := by
        simp [hparlen]; omega
      have := List.IsPrefix.eq_of_length h1 h2
      rw [this, seqCode_decodeSeq]
    refine List.mem_flatMap.mpr ⟨par, hin, ?_⟩
    rw [mem_childrenIn]
    exact ⟨⟨v, hvb, hd_eq⟩, hd_eq ▸ hdT⟩

/-- **The frontier decides extension.** Nonempty exactly when an extension exists. -/
theorem frontier_ne_nil_iff (T : InternalBoundedTree Ω) {bnd : ℕ → ℕ}
    (hbnd : ∀ i, T.bound.MapsTo i (bnd i)) (c k : ℕ) :
    frontier T.tree.1 bnd c k ≠ [] ↔ ExtendsAt T.tree.1 c ((decodeSeq c).length + k) := by
  constructor
  · intro hne
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨heT, helen, hepre⟩ := frontier_spec k e he
    exact ⟨e, heT, helen, hepre⟩
  · rintro ⟨d, hdT, hlen, hpre⟩
    exact List.ne_nil_of_mem (mem_frontier_of_extends T hbnd k d hdT hlen hpre)

/-! ### Link 4: the frontier is computable from the tree joined with the bound graph

The recursion is in the *transcript-then-verify* normal form throughout: at each node one
bound lookup and one finite `valueTable` of tree-membership bits over the enumerated
candidates, then pure primitive-recursive post-processing (`filterMap`, `flatten`). Stated
generically in the oracle set, then instantiated at `joinSet T.tree.1 T.bound.graph.1` with
the bound recovered from its graph — the only two channels the construction is entitled
to. -/

/-- Filtering the image is one `filterMap` over the source. -/
private theorem filter_map_eq_filterMap {α β : Type*} (l : List α) (f : α → β)
    (p : β → Bool) :
    (l.map f).filter p = l.filterMap fun a => if p (f a) then some (f a) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p (f a) <;> simp [h, ih]

open Classical in
/-- The children list, restated on the membership *bits* — the shape a program computes:
enumerate the candidates below the bound and keep those whose tree bit is `1`. -/
private theorem childrenIn_eq_filterMap (S : Set ℕ) (bnd : ℕ → ℕ) (d : ℕ) :
    childrenIn S bnd d = (List.range (bnd (decodeSeq d).length)).filterMap fun v =>
      if charFnTot S (seqCode (decodeSeq d ++ [v])) = 1
      then some (seqCode (decodeSeq d ++ [v])) else none := by
  rw [childrenIn, filter_map_eq_filterMap]
  refine List.filterMap_congr fun v _ => ?_
  by_cases h : seqCode (decodeSeq d ++ [v]) ∈ S <;> simp [charFnTot, h]

/-- Reading a function's values off positions of its own range-indexed table. -/
private theorem map_range_getD {α : Type*} (f : ℕ → α) {w v : ℕ} (hv : v < w)
    (d : α) : ((List.range w).map f).getD v d = f v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
  rfl

/-- Iterating a function of the previous value over the whole list, through the coding. -/
private theorem map_getD_range {α : Type*} (l : List ℕ) (g : ℕ → α) :
    (List.range l.length).map (fun j => g (l.getD j 0)) = l.map g := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

/-- **One level of children is a finite oracle computation**: a single bound lookup, a
`valueTable` of tree bits over the candidates, and a pure `filterMap`. -/
theorem childrenIn_code_recursiveIn {O : Set (ℕ →. ℕ)} {S : Set ℕ} {bnd : ℕ → ℕ}
    (hS : Nat.RecursiveIn O fun e => Part.some (charFnTot S e))
    (hbnd : Nat.RecursiveIn O fun i => Part.some (bnd i)) :
    Nat.RecursiveIn O fun d => Part.some (seqCode (childrenIn S bnd d)) := by
  classical
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  -- the candidate at (node, value), as one primitive-recursive map
  have hcand : Primrec fun m : ℕ => seqCode (decodeSeq m.unpair.1 ++ [m.unpair.2]) :=
    primrec_seqCode.comp
      (Primrec₂.comp (f := fun (l : List ℕ) (a : ℕ) => l ++ [a]) Primrec.list_concat
        (primrec_decodeSeq.comp hfst) hsnd)
  -- the tree-membership bit of the candidate at (node, value)
  have hbit : Nat.RecursiveIn O fun m => Part.some
      (charFnTot S (seqCode (decodeSeq m.unpair.1 ++ [m.unpair.2]))) :=
    recursiveIn_comp_primrec hS hcand
  -- the transcript: all candidate bits below the bound at the node's length
  have htab := valueTable_recursiveIn_param
    (f := fun d v => charFnTot S (seqCode (decodeSeq d ++ [v]))) hbit
  have hw : Nat.RecursiveIn O fun d => Part.some (bnd (decodeSeq d).length) :=
    recursiveIn_comp_total hbnd (recursiveIn_of_primrec primrec_seqLength)
  have hdw := recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id) hw
  have htabd : Nat.RecursiveIn O fun d => Part.some
      (valueTable (fun v => charFnTot S (seqCode (decodeSeq d ++ [v])))
        (bnd (decodeSeq d).length)) :=
    (recursiveIn_comp_total htab hdw).of_eq fun d => by simp only [Nat.unpair_pair, id_eq]
  -- pure post-processing: keep the candidates whose recorded bit is 1
  have hpost : Primrec fun z : ℕ => seqCode
      ((List.range (decodeSeq z.unpair.2).length).filterMap fun v =>
        if (decodeSeq z.unpair.2).getD v 0 = 1
        then some (seqCode (decodeSeq z.unpair.1 ++ [v])) else none) := by
    refine primrec_seqCode.comp (Primrec.listFilterMap
      (Primrec.list_range.comp (Primrec.list_length.comp
        (primrec_decodeSeq.comp hsnd))) ?_)
    have hgetD : Primrec fun p : ℕ × ℕ => (decodeSeq p.1.unpair.2).getD p.2 0 :=
      Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet
        (hsnd.comp Primrec.fst) Primrec.snd
    have hval : Primrec fun p : ℕ × ℕ => seqCode (decodeSeq p.1.unpair.1 ++ [p.2]) :=
      primrec_seqCode.comp
        (Primrec₂.comp (f := fun (l : List ℕ) (a : ℕ) => l ++ [a]) Primrec.list_concat
          (primrec_decodeSeq.comp (hfst.comp Primrec.fst)) Primrec.snd)
    exact Primrec.ite (Primrec.eq.comp hgetD (Primrec.const 1))
      (Primrec.option_some.comp hval) (Primrec.const none)
  have hpair := recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id) htabd
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun d => ?_
  simp only [Nat.unpair_pair, id_eq, decodeSeq_valueTable, List.length_map,
    List.length_range]
  rw [childrenIn_eq_filterMap]
  refine congrArg Part.some (congrArg seqCode (List.filterMap_congr fun v hv => ?_))
  rw [map_range_getD _ (List.mem_range.mp hv)]

open Classical in
/-- One step of the frontier recursion, on frontier *codes*: decode the surviving nodes,
take all their children, re-encode. -/
private noncomputable def frontierStep (S : Set ℕ) (bnd : ℕ → ℕ) (l : ℕ) : ℕ :=
  seqCode ((decodeSeq l).flatMap (childrenIn S bnd))

private theorem frontierCode_eq_nat_rec (S : Set ℕ) (bnd : ℕ → ℕ) (c k : ℕ) :
    seqCode (frontier S bnd c k) = Nat.rec (motive := fun _ => ℕ)
      (seqCode (frontier S bnd c 0)) (fun _ ih => frontierStep S bnd ih) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : seqCode (frontier S bnd c (k + 1))
        = frontierStep S bnd (seqCode (frontier S bnd c k)) := by
      rw [frontierStep, decodeSeq_seqCode]
      conv_lhs => rw [frontier]
    rw [hstep, ih]

/-- The frontier step is a finite oracle computation: a `valueTable` of children codes
over the surviving nodes, then a pure decode-and-flatten. -/
private theorem frontierStep_recursiveIn {O : Set (ℕ →. ℕ)} {S : Set ℕ} {bnd : ℕ → ℕ}
    (hS : Nat.RecursiveIn O fun e => Part.some (charFnTot S e))
    (hbnd : Nat.RecursiveIn O fun i => Part.some (bnd i)) :
    Nat.RecursiveIn O fun l => Part.some (frontierStep S bnd l) := by
  have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hchild := childrenIn_code_recursiveIn hS hbnd
  -- the transcript: children codes of each surviving node in order
  have helem : Primrec fun m : ℕ => (decodeSeq m.unpair.1).getD m.unpair.2 0 :=
    Primrec₂.comp (f := fun n i : ℕ => (decodeSeq n).getD i 0) primrec_seqGet hfst hsnd
  have htab := valueTable_recursiveIn_param
    (f := fun l j => seqCode (childrenIn S bnd ((decodeSeq l).getD j 0)))
    (recursiveIn_comp_primrec hchild helem)
  have hlen : Nat.RecursiveIn O fun l => Part.some (Nat.pair l (decodeSeq l).length) :=
    recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id)
      (recursiveIn_of_primrec primrec_seqLength)
  have htabl : Nat.RecursiveIn O fun l => Part.some
      (valueTable (fun j => seqCode (childrenIn S bnd ((decodeSeq l).getD j 0)))
        (decodeSeq l).length) :=
    (recursiveIn_comp_total htab hlen).of_eq fun l => by simp only [Nat.unpair_pair]
  -- pure post-processing: decode each recorded children list and flatten
  have hpost : Primrec fun t : ℕ => seqCode ((decodeSeq t).flatMap decodeSeq) :=
    primrec_seqCode.comp
      (Primrec.list_flatMap primrec_decodeSeq (primrec_decodeSeq.comp Primrec.snd))
  refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) htabl).of_eq fun l => ?_
  simp only [frontierStep, decodeSeq_valueTable]
  congr 1
  rw [List.flatMap_map]
  simp only [decodeSeq_seqCode]
  rw [List.flatMap_def, List.flatMap_def, map_getD_range]

/-- **Link 4, generic form**: the frontier recursion is a relative computation from any
oracle answering tree-membership bits and bound values — primitive recursion on the depth
with the start node as parameter, one `frontierStep` transcript per level. -/
theorem frontier_code_recursiveIn {O : Set (ℕ →. ℕ)} {S : Set ℕ} {bnd : ℕ → ℕ}
    (hS : Nat.RecursiveIn O fun e => Part.some (charFnTot S e))
    (hbnd : Nat.RecursiveIn O fun i => Part.some (bnd i)) :
    Nat.RecursiveIn O fun q =>
      Part.some (seqCode (frontier S bnd q.unpair.1 q.unpair.2)) := by
  classical
  -- the base: one tree bit at the start node
  have hbase : Nat.RecursiveIn O fun c => Part.some (seqCode (frontier S bnd c 0)) := by
    have hpair := recursiveIn_pair_total (recursiveIn_of_primrec Primrec.id) hS
    have hpost : Primrec fun z : ℕ =>
        if z.unpair.2 = 1 then seqCode [z.unpair.1] else seqCode [] := by
      have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
      have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
      exact Primrec.ite (Primrec.eq.comp hsnd (Primrec.const 1))
        (primrec_seqCode.comp (Primrec.list_cons.comp hfst (Primrec.const [])))
        (Primrec.const (seqCode []))
    refine (recursiveIn_comp_total (recursiveIn_of_primrec hpost) hpair).of_eq fun c => ?_
    simp only [Nat.unpair_pair, id_eq, frontier]
    by_cases h : c ∈ S <;> simp [charFnTot, h]
  have hstep' : Nat.RecursiveIn O fun m => Part.some
      (frontierStep S bnd m.unpair.2.unpair.2) :=
    recursiveIn_comp_primrec (frontierStep_recursiveIn hS hbnd)
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair))
  have h := recursiveIn_nat_rec_param (base := fun c => seqCode (frontier S bnd c 0))
    (step := fun _ _ ih => frontierStep S bnd ih) hbase hstep'
  exact h.of_eq fun q => congrArg Part.some
    (frontierCode_eq_nat_rec S bnd q.unpair.1 q.unpair.2).symm

/-- **Link 4**: the frontier of an internally presented explicitly bounded tree is
computable from the tree joined with its bound graph — the tree bits from the even side,
the bound values by unique-graph lookup on the odd side. This is the entire base-oracle
budget of the leftmost-path construction. -/
theorem frontier_recursiveIn_join (T : InternalBoundedTree Ω) :
    Nat.RecursiveIn {charFn (joinSet T.tree.1 T.bound.graph.1)} fun q =>
      Part.some (seqCode (frontier T.tree.1 T.bound.eval q.unpair.1 q.unpair.2)) := by
  have hS : Nat.RecursiveIn {charFn (joinSet T.tree.1 T.bound.graph.1)}
      fun e => Part.some (charFnTot T.tree.1 e) := by
    refine (left_le_joinSet T.tree.1 T.bound.graph.1).of_eq fun e => ?_
    rw [charFn_eq_coe]
    rfl
  have hbnd : Nat.RecursiveIn {charFn (joinSet T.tree.1 T.bound.graph.1)}
      fun i => Part.some (T.bound.eval i) :=
    recursiveIn_of_turingReducible T.bound.eval_recursiveIn_graph
      (right_le_joinSet T.tree.1 T.bound.graph.1)
  exact frontier_code_recursiveIn hS hbnd

/-! ### Link 5: extendibility is one jump query

Dead ends are semidecidable in the joined base oracle: search the depths for an empty
frontier level. The jump of that oracle therefore decides extendibility with a single
query, through the standard curry-and-self-halt coding — the same route `le_jump` takes.
The semantic content is exactly `frontier_ne_nil_iff`, quantified over depths. -/

private theorem decodeSeq_zero : decodeSeq 0 = [] := by
  simp [decodeSeq, Denumerable.decode_eq_ofNat, Denumerable.list_ofNat_zero]

private theorem seqCode_eq_zero_iff {l : List ℕ} : seqCode l = 0 ↔ l = [] := by
  constructor
  · intro h
    have h2 := congrArg decodeSeq h
    rwa [decodeSeq_seqCode, decodeSeq_zero] at h2
  · rintro rfl
    rw [← decodeSeq_zero, seqCode_decodeSeq]

/-- A node fails extendibility exactly when some frontier level dies out — the negative
side of `frontier_ne_nil_iff`, quantified over depths. -/
theorem not_extendibleAt_iff (T : InternalBoundedTree Ω) {bnd : ℕ → ℕ}
    (hbnd : ∀ i, T.bound.MapsTo i (bnd i)) (c : ℕ) :
    ¬ ExtendibleAt T.tree.1 c ↔ ∃ k, frontier T.tree.1 bnd c k = [] := by
  rw [ExtendibleAt]
  push Not
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    by_contra hne
    exact hn ((frontier_ne_nil_iff T hbnd c n).mp hne)
  · rintro ⟨k, hk⟩
    exact ⟨k, fun hext => (frontier_ne_nil_iff T hbnd c k).mpr hext hk⟩

/-- **Link 5**: the extendible nodes are decidable from one query to the jump of the
joined base oracle. The searched program hunts depth-by-depth for an empty frontier
level; currying pins the node into the code, and the jump answers the halting
question. -/
theorem extendibleSet_le_jump (T : InternalBoundedTree Ω) :
    {c | ExtendibleAt T.tree.1 c} ≤ᵀ jumpSet (joinSet T.tree.1 T.bound.graph.1) := by
  classical
  set A := joinSet T.tree.1 T.bound.graph.1 with hA
  -- the dead-end search: the frontier code at (node, depth), tested against zero by rfind
  have hprep : Primrec fun q : ℕ => Nat.pair q.unpair.1.unpair.1 q.unpair.2 := by
    have hfst : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
    have hsnd : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
    exact Primrec₂.comp (f := Nat.pair) Primrec₂.natPair (hfst.comp hfst) hsnd
  have hfr' : Nat.RecursiveIn {charFn A} fun q => Part.some
      (seqCode (frontier T.tree.1 T.bound.eval q.unpair.1.unpair.1 q.unpair.2)) :=
    (recursiveIn_comp_primrec (frontier_recursiveIn_join T) hprep).of_eq fun q => by
      simp only [Nat.unpair_pair]
  have hsearch := Nat.RecursiveIn.rfind hfr'
  obtain ⟨e, he⟩ := exists_code.mp hsearch
  have hbnd : ∀ i, T.bound.MapsTo i (T.bound.eval i) := fun i => T.bound.pair_eval_mem i
  -- the one-query key: failing extendibility is exactly self-halting of the curried code
  have key : ∀ c : ℕ, (¬ ExtendibleAt T.tree.1 c ↔
      Encodable.encode (OracleCode.curry e c) ∈ jumpSet A) := by
    intro c
    rw [mem_jumpSet_iff, Denumerable.ofNat_encode, ← charFn_eq_coe, eval_curry, he,
      not_extendibleAt_iff T hbnd, Nat.rfind_dom]
    simp only [Nat.unpair_pair, Part.map_eq_map, Part.map_some]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_, fun {m} _ => trivial⟩
      rw [Part.mem_some_iff]
      simp [seqCode_eq_zero_iff, hk]
    · rintro ⟨n, hn, -⟩
      rw [Part.mem_some_iff] at hn
      exact ⟨n, seqCode_eq_zero_iff.mp (by simpa using hn.symm)⟩
  -- one query: ask the jump about the curried code, flip the answer
  have hmap : Nat.Partrec fun c : ℕ =>
      Part.some (Encodable.encode (OracleCode.curry e c)) := by
    apply Nat.Partrec.of_primrec
    exact Primrec.nat_iff.mp (Primrec.encode.comp
      (primrec₂_curry.comp (_root_.Primrec.const e) _root_.Primrec.id))
  have h1 := Nat.RecursiveIn.comp
    (Nat.RecursiveIn.oracle (O := {charFn (jumpSet A)}) (charFn (jumpSet A)) rfl)
    hmap.recursiveIn
  have hflip : Nat.RecursiveIn {charFn (jumpSet A)} fun w : ℕ =>
      (Part.some (1 - w) : Part ℕ) :=
    (Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec
      (Nat.Primrec.sub.comp (Nat.Primrec.pair (Nat.Primrec.const 1)
        Nat.Primrec.id)))).of_eq fun w => by simp [Nat.unpaired]
  have h2 := Nat.RecursiveIn.comp hflip h1
  refine h2.of_eq fun c => ?_
  simp only [Part.bind_eq_bind, Part.bind_some, charFn, Set.mem_setOf_eq]
  by_cases hc : ExtendibleAt T.tree.1 c
  · rw [if_neg (fun hmem => ((key c).mpr hmem) hc), if_pos hc]
  · rw [if_pos ((key c).mp hc), if_neg hc]

end ReverseMathlib.Omega
