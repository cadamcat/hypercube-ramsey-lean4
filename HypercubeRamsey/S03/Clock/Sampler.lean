import HypercubeRamsey.S03.Clock.Branching

/-!
# Lemma 3.10, Step 8: the raw clock sampler and its assembly

Source: `sections/03-…tex`, lines 805–1131. From an admissible instance with a Step 1 certificate and a finite
mesh (`ClockData`), the completed rows (real rows with trimmed laws, dummy rows with label laws) carry independent
marked first-arrival clocks (`ClockData.law`). The raw sampler of `clock_raw_sampler` is built on this clock field:
its output is the greedy matching's output at each real row, its bad events are the bad leaves of the truncated
explorations of the tests (`ClockData.Bad`), and its target rectangles are the intersections of non-giant
singleton leaves (`ClockData.targetRects`).

Node order (paper order): constants and the completed instance (Step 1 data); the exploration and leaf facts
(Steps 2–3, `Truncated.lean`); the path-insertion bound with its time sum, the two-row exception and the long-path
tail (Step 4, `Paths.lean`); the giant tail (Step 5, `Branching.lean`, specialized in `clock_giant_tail`); the
matched-failure and short-path bounds (Steps 7–8, `predicate_failure_under_insertion`, `short_path_bad_bound`);
the incidence bound (`closure_incidence_bound`, `clockBad_incidence`); forcing, goodness and the targets
(`ClockData.badEvent_forcing`, `ClockData.good`, `clock_target`). `clock_raw_sampler` is assembled from these;
`step8_trimmed_core` and `step8_bad_leaf_avoidance` (moved here from `Steps.lean`) are unchanged.
-/

namespace HypercubeRamsey.Clock

open Filter
open scoped BigOperators

/-! ### Constants -/

/-- `K₀`, large in terms of `B` (TeX 03:806, 03:986–988, 03:1101–1103): it gives `(.1 - 2√θ) K₀ > B`,
`(.4 - θ - √θ) K₀ > B`, and `K₀ > 2B`, so that `n^B L κ → 0`. -/
def clockK₀ (B : ℝ) : ℝ := 20 * B + 20

/-- `A_*`: Steps 6–7 are applied with `A_* - 1` (the completed atoms are at most `2 n^{-A_*} ≤ n^{-(A_* - 1)}`),
which needs `10 (B + K₀) < A_* - 1`; the two-row exception needs `A_* > 2B + K₀ + 2`. -/
def clockA (B : ℝ) : ℝ := 10 * (B + clockK₀ B) + 2

/-- `P_*`: Step 1 needs `4B + 4 ≤ P_*`; the matched-failure term needs `P_*/3 > B + K₀ + 4`. -/
def clockP (B : ℝ) : ℝ := 6 * B + 3 * clockK₀ B + 16

/-- The giant cutoff `L = ⌈n^{.1 K₀}⌉` (TeX 03:872). -/
noncomputable def clockLnat (B : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ (clockK₀ B / 10)⌉₊

/-- `L` as a real number, the dependency-set bound of the raw sampler. -/
noncomputable def clockL (B : ℝ) (n : ℕ) : ℝ := (clockLnat B n : ℝ)

/-- The incidence bound `κ = n^{-.6 K₀}` (TeX 03:899–902). -/
noncomputable def clockκ (B : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-(3 * clockK₀ B / 5))

/-- The short-path length threshold `⌊K₀² log n⌋` (TeX 03:926–927). -/
noncomputable def clockJ (B : ℝ) (n : ℕ) : ℕ := ⌊clockK₀ B ^ 2 * Real.log n⌋₊

/-- The bad-outcome bound for a short insertion meeting at most one row of the test (TeX 03:1086–1098): giant
tail, unmatched singleton (`n^{-(1-θ)K₀} ≤ n^{-.99K₀}`), matched predicate failure (`O(log n) n^{-P_*/3}`). -/
noncomputable def clockShortBound (B : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(2 * clockK₀ B)) + 2 * (n : ℝ) ^ (-(99 / 100 * clockK₀ B)) +
    ((clockJ B n : ℝ) + 1) * (1 + (n : ℝ)⁻¹) * (n : ℝ) ^ (-(clockP B / 3))

/-- L3.10-const: the limit `n^B L κ → 0` and, for large `n`, `4 L κ ≤ 1`, `n^B ≤ L` and `L ≥ 1`. -/
theorem clock_constants (B : ℝ) (hB : 1 ≤ B) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ B * clockL B n * clockκ B n) atTop (nhds 0) ∧
      ∃ n₀ : ℕ, ∀ n ≥ n₀, 2 ≤ n ∧ 4 * clockL B n * clockκ B n ≤ 1 ∧
        (n : ℝ) ^ B ≤ (clockLnat B n : ℝ) ∧ 1 ≤ clockLnat B n := by
  sorry

/-! ### Small facts -/

/-- A finite probability law lives on a nonempty type. -/
theorem finProb_nonempty {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := P.sum_eq_one
  simp at h1

theorem FiniteMeshPlan.δ_nonneg {n : ℕ} {K₀ : ℝ} (mesh : FiniteMeshPlan n K₀) : 0 ≤ mesh.δ := by
  rw [mesh.δ_eq]
  exact (Real.exp_pos _).le

theorem FiniteMeshPlan.δ_le_one {n : ℕ} {K₀ : ℝ} (mesh : FiniteMeshPlan n K₀) : mesh.δ ≤ 1 := by
  rw [mesh.δ_eq, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- L3.10a-empty (03:1117–1119, degenerate scopes): a predicate with empty scope is constant, and its probability
is below `1`, so it never holds. -/
theorem empty_scope_failure_false {n g : ℕ} {R K : Type*} [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (I : SamplingInstance n g R K Ω) (B A P : ℝ) (hI : I.Admissible B A P) (hn : 2 ≤ n) (hP : 0 < P)
    (k : K) (hk : I.scope k = ∅) : ∀ ω, ¬ I.failure k ω := by
  sorry

/-- On independent marked clocks every arrival mark carries its edge's label: the event of a mark with another
label is null (`outputMarkMass` vanishes off the label). -/
theorem invalid_marks_null {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) :
    (clockFieldLaw (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab)).pr
      (fun ξ => ∃ e t o, ξ e = MeshClockValue.tick t o ∧ lab e.1 o ≠ e.2) = 0 := by
  sorry

/-! ### The completed instance -/

/-- Outputs of the completed rows: a real row keeps its full outputs, a dummy row outputs a label. -/
def COut {R : Type} (Ω : R → Type) (g m : ℕ) : R ⊕ Fin m → Type
  | .inl a => Ω a
  | .inr _ => Fin g

instance COut.instFintype {R : Type} (Ω : R → Type) [∀ a, Fintype (Ω a)] (g m : ℕ) :
    ∀ a, Fintype (COut Ω g m a)
  | .inl a => inferInstanceAs (Fintype (Ω a))
  | .inr _ => inferInstanceAs (Fintype (Fin g))

instance COut.instDecidableEq {R : Type} (Ω : R → Type) [∀ a, DecidableEq (Ω a)] (g m : ℕ) :
    ∀ a, DecidableEq (COut Ω g m a)
  | .inl a => inferInstanceAs (DecidableEq (Ω a))
  | .inr _ => inferInstanceAs (DecidableEq (Fin g))

/-- One application of the clock construction (TeX 03:805–842): an admissible instance at the constants
`clockA B`, `clockP B`, a Step 1 certificate, and a finite mesh on `[0, K₀ log n]`. -/
structure ClockData (B : ℝ) (n g : ℕ) (R K : Type) [Fintype R] [DecidableEq R] [Fintype K]
    (Ω : R → Type) [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)] where
  I : SamplingInstance n g R K Ω
  admissible : I.Admissible B (clockA B) (clockP B)
  C : TrimCertificate I B (clockA B) (clockP B)
  mesh : FiniteMeshPlan n (clockK₀ B)

namespace ClockData

variable {B : ℝ} {n g : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type}
  [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)] (D : ClockData B n g R K Ω)

/-- The completed rows: real rows and the dummy rows of Step 1 (TeX 03:832–835). -/
abbrev Row : Type := R ⊕ Fin D.C.dummyRows

/-- The outputs of the completed rows. -/
abbrev Out : D.Row → Type := COut Ω g D.C.dummyRows

/-- The labels of the completed rows (a dummy row's output is its label). -/
def lab' : ∀ a : D.Row, D.Out a → Fin g
  | .inl a => D.I.lab a
  | .inr _ => id

/-- The laws of the completed rows: trimmed laws on real rows, dummy laws on dummy rows (TeX 03:825, 03:832–837). -/
def law' : ∀ a : D.Row, FinProb (D.Out a)
  | .inl a => D.C.trimmed a
  | .inr i => ⟨D.C.dummyLaw i, D.C.dummy_nonneg i, D.C.dummy_row_sum i⟩

/-- The independent marked first-arrival clocks of the completed row-label graph (TeX 03:845–848, on the mesh). -/
noncomputable def edgeLaw : ∀ e : RowLabel D.Row g, FinProb (MeshClockValue D.mesh.ticks (D.Out e.1)) :=
  samplingEdgeClockLaw D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one D.law' D.lab'

/-- The law of the clock field: the probability space of the raw sampler. -/
noncomputable def law : FinProb (ClockField D.mesh.ticks D.Row g D.Out) := clockFieldLaw D.edgeLaw

/-- Predicate scopes as completed rows. -/
def scope' (k : K) : Finset D.Row := (D.I.scope k).map Function.Embedding.inl

/-- Predicates read on the real rows of a completed output. -/
def failure' (k : K) (ω : ∀ a : D.Row, D.Out a) : Prop := D.I.failure k fun a => ω (Sum.inl a)

/-- Tests of the instance as tests of the completed rows (singleton tests only at real rows). -/
def test' : SamplingTest R K → SamplingTest D.Row K
  | .predicate k => .predicate k
  | .singleton a => .singleton (Sum.inl a)

/-- The sampler output at a real row: its greedy output if matched (a fixed output otherwise; on the avoidance
event every real row is matched). -/
noncomputable def out (ξ : ClockField D.mesh.ticks D.Row g D.Out) (a : R) : Ω a :=
  match (greedyMatching ξ).assignment (Sum.inl a) with
  | some (_, o) => o
  | none => (finProb_nonempty (D.I.p a)).some

/-- A target assignment extended to the dummy rows by fixed labels. -/
noncomputable def extendTarget (o : ∀ a, Ω a) : ∀ a : D.Row, D.Out a
  | .inl a => o a
  | .inr i => (finProb_nonempty (D.law' (.inr i))).some

/-- The bad leaves of a test's truncated exploration (giant cutoff `clockLnat B n`). -/
noncomputable def badLeaves' (t : SamplingTest R K) : Finset (ClockLeaf D.mesh.ticks D.Row g D.Out) :=
  badLeaves D.lab' D.failure' D.scope' (clockLnat B n) (D.test' t)

/-- D3.10h-bad (03:1113–1116): the bad events of the raw sampler, the bad leaves indexed by their test. -/
abbrev Bad : Type := Σ t : SamplingTest R K, ↥(D.badLeaves' t)

/-- The event of a bad leaf. -/
def badEvent (i : D.Bad) (ξ : ClockField D.mesh.ticks D.Row g D.Out) : Prop := i.2.1.Event ξ

/-- The dependency set of a bad leaf: its active endpoints (TeX 03:886–887). -/
def badAct (i : D.Bad) : Finset (Endpoint D.Row g) := i.2.1.active

/-- The singleton leaf of a real row is good for the output `o`: non-giant, with the row matched to `o`. -/
def targetLeafGood (ξ : ClockField D.mesh.ticks D.Row g D.Out) (a : R) (o : Ω a) : Prop :=
  (testExploration ξ D.scope' (D.test' (.singleton a)) (clockLnat B n)).giant = false ∧
    ∃ y, (greedyMatching ξ).assignment (Sum.inl a) = some (y, o)

/-- D3.10h-rect (03:1121–1124): the tuples of non-giant singleton leaves of the queried rows that realize the
target, i.e. the parts of the joint target event. -/
noncomputable def targetRects (S : Finset R) (o : ∀ a, Ω a) :
    Finset (S → ClockLeaf D.mesh.ticks D.Row g D.Out) := by
  classical
  exact (Finset.univ.filter fun ξ => ∀ a : S, D.targetLeafGood ξ a.1 (o a.1)).image
    fun ξ a => testLeaf ξ D.scope' (D.test' (.singleton a.1)) (clockLnat B n)

/-! ### Step 1 data of the completed instance -/

/-- Every completed row has total label rate `1`. -/
theorem completed_rows_eq : ∀ a, ∑ y, labMarg (D.law' a) (D.lab' a) y = 1 := by
  sorry

/-- L3.10a-col (03:832–837): every completed column has total rate `θ`. -/
theorem completed_columns_eq : ∀ y, ∑ a, labMarg (D.law' a) (D.lab' a) y = D.C.theta := by
  sorry

include D in
/-- L3.10a-g (03:838–840): with a real row present, `g ≥ n^{A_*}`, since a real row is a probability law with
label atoms at most `n^{-A_*}`. -/
theorem card_labels_ge [Nonempty R] (hn : 1 ≤ n) : (n : ℝ) ^ clockA B ≤ g := by
  sorry

/-- L3.10a-atom (03:837–842): the completed atoms are at most `n^{-(A_* - 1)}` (trimmed atoms `≤ 2 n^{-A_*}`,
dummy atoms `≤ 2/g ≤ 2 n^{-A_*}`). -/
theorem completed_atom_le [Nonempty R] (hn : 2 ≤ n) :
    ∀ a y, labMarg (D.law' a) (D.lab' a) y ≤ (n : ℝ) ^ (-(clockA B - 1)) := by
  sorry

/-- L3.10a-θ (03:831): `10^{-6} ≤ θ ≤ 2·10^{-6}` once `g ≥ 10^6`. -/
theorem completed_theta_bounds (hg : (10 : ℝ) ^ 6 ≤ g) : 1e-6 ≤ D.C.theta ∧ D.C.theta ≤ 2e-6 := by
  sorry

/-! ### Forcing, goodness and the dependency sets (Steps 3 and 8) -/

/-- L3.10h-act (03:886–887): a bad leaf has a nonempty active set (a giant leaf has `L ≥ 1` active endpoints; a
failing test has a root, an empty-scope predicate being unsatisfiable). -/
theorem badAct_nonempty (hn : 2 ≤ n) (hP : 0 < clockP B) (hL : 1 ≤ clockLnat B n) :
    ∀ i : D.Bad, (D.badAct i).Nonempty := by
  sorry

/-- L3.10h-card (03:1113–1114): a bad leaf has at most `L` active endpoints (with at most `L` roots). -/
theorem badAct_card (hroots : ∀ k, ((D.I.scope k).card : ℝ) ≤ (clockLnat B n : ℝ))
    (hL : 1 ≤ clockLnat B n) : ∀ i : D.Bad, ((D.badAct i).card : ℝ) ≤ clockL B n := by
  sorry

/-- L3.10c-force (03:888–896): the lopsided forcing property of a bad leaf against bad leaves with disjoint active
sets, from `leaf_forcing_coupling`. -/
theorem badEvent_forcing : ∀ (i : D.Bad) (S : Finset D.Bad), (∀ j ∈ S, Disjoint (D.badAct i) (D.badAct j)) →
    D.law.pr (fun ξ => D.badEvent i ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ) ≤
      D.law.pr (D.badEvent i) * D.law.pr (fun ξ => ∀ j ∈ S, ¬ D.badEvent j ξ) := by
  sorry

/-- Avoiding every bad leaf is the same as every test having a non-bad leaf (each clock field lies in its own
leaf). -/
theorem noBad_iff (ξ : ClockField D.mesh.ticks D.Row g D.Out) :
    (∀ i : D.Bad, ¬ D.badEvent i ξ) ↔
      ∀ t : SamplingTest R K, ¬ leafBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) := by
  sorry

/-- L3.10h-good (03:1117–1119): on the avoidance event every real row is matched with an output carrying its
matched label (distinct by `greedyMatching_label_injective`) and every predicate is avoided. -/
theorem good (ξ : ClockField D.mesh.ticks D.Row g D.Out) (hξ : ∀ i : D.Bad, ¬ D.badEvent i ξ) :
    Function.Injective (fun a => D.I.lab a (D.out ξ a)) ∧ ∀ k, ¬ D.I.failure k (D.out ξ) := by
  sorry

/-- L3.10h-cover (03:1121–1122): on the avoidance event with the queried outputs, the tuple of singleton leaves of
the queried rows is a target rectangle. -/
theorem targetRect_cover (S : Finset R) (o : ∀ a, Ω a) (ξ : ClockField D.mesh.ticks D.Row g D.Out)
    (hξ : ∀ i : D.Bad, ¬ D.badEvent i ξ) (ho : ∀ a ∈ S, D.out ξ a = o a) :
    (fun a : S => testLeaf ξ D.scope' (D.test' (.singleton a.1)) (clockLnat B n)) ∈ D.targetRects S o := by
  sorry

/-- L3.10h-part (03:1121–1128): distinct target rectangles are disjoint (`explorationLeaf_event_iff`) and each
lies in the joint target event (`nongiant_leaf_agreesBelow`, `closure_determines_root_assignment`). -/
theorem targetRects_sum_le (S : Finset R) (o : ∀ a, Ω a) :
    ∑ τ ∈ D.targetRects S o, D.law.pr (fun ξ => ∀ a, (τ a).Event ξ) ≤
      D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) := by
  sorry

end ClockData

/-! ### Steps 5, 7 and 8 on the completed instance -/

/-- L3.10e-clock (03:979–989): the giant tail for the completed clocks under a short insertion, from at most
`n^B` roots: `Pr(|closure| ≥ L) ≤ n^{-2K₀}` (`giant_tail_under_insertion` with `δ' = n^{-K₀/100}`). -/
theorem clock_giant_tail (B : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ {g : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω)
      (roots : Finset (Endpoint D.Row g)), (roots.card : ℝ) ≤ (n : ℝ) ^ B →
      ∀ ins : ∀ e : RowLabel D.Row g, Option (MeshClockValue D.mesh.ticks (D.Out e.1)),
      (insertionSize ins : ℝ) ≤ (clockK₀ B + 1) ^ 2 * Real.log n →
      D.law.pr (fun ξ => clockLnat B n ≤ (closureFrom (insertArrivals ins ξ) roots).card) ≤
        (n : ℝ) ^ (-(2 * clockK₀ B)) := by
  sorry

/-- L3.10h-pred (03:1086–1094): a predicate fails under a fixed short insertion of positive-weight values whose
rows meet its scope in at most the row `a₀`. If every scope match is ordinary, sum Step 7 over the failing output
tuples (`trimmed_failure`); otherwise one match is an inserted arrival at `a₀`: pin its output and sum Step 7 over
the other rows (`trimmed_pinned_failure`; the inserted mark is retained, having positive weight). -/
theorem predicate_failure_under_insertion (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (k : K) (a₀ : R)
      (ins : ∀ e : RowLabel D.Row g, Option (MeshClockValue D.mesh.ticks (D.Out e.1))),
      (insertionSize ins : ℝ) ≤ (clockK₀ B + 1) ^ 2 * Real.log n →
      (∀ e x, ins e = some x → 0 < (D.edgeLaw e).w x) →
      (∀ e x, ins e = some x → e.1 ∈ D.scope' k → e.1 = Sum.inl a₀) →
      D.law.pr (fun ξ => testFails D.failure' D.scope' (greedyMatching (insertArrivals ins ξ))
          (.predicate k)) ≤
        ((insertionSize ins : ℝ) + 1) * (1 + (n : ℝ)⁻¹) * (n : ℝ) ^ (-(clockP B / 3)) := by
  sorry

/-- L3.10h-short (03:1084–1098): the bad-outcome probability under the insertion of a short decreasing path from a
root `r` of the test that meets no other row of the test is at most `clockShortBound`: giant tail
(`clock_giant_tail`), unmatched singleton (`step7_unmatched_singleton`; an invalid matched mark is null,
`invalid_marks_null`), matched predicate failure (`predicate_failure_under_insertion`). -/
theorem short_path_bad_bound (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (t : SamplingTest R K) (r : R),
      r ∈ testRoots D.I.scope t → ∀ (v : Endpoint D.Row g) (j : ℕ), j ≤ clockJ B n →
      ∀ π : Fin j → ClockCandidate D.mesh.ticks D.Row g D.Out,
      π ∈ decPaths (Sum.inl (Sum.inl r)) v j →
      (∀ k, t = .predicate k → ¬ pathMeetsOtherRow π (D.scope' k) (Sum.inl r)) →
      0 < pathWeight D.edgeLaw π →
      D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n)
          (insertArrivals (pathInsertion π) ξ) (D.test' t)) ≤ clockShortBound B n := by
  sorry

/-- L3.10h-num (03:1099–1104): the final arithmetic of the incidence bound. With `D = n^B`, `x = K₀ log n + 2`,
`J = ⌊K₀² log n⌋` and `λ = n^{-(A_*-1)}`: the one-row short paths, the two-row exception and the long paths
together stay below `κ = n^{-.6K₀}`, and `e² x ≤ J` (for `walk_series_tail`). -/
theorem incidence_numerics (B : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ θ : ℝ, 1e-6 ≤ θ → θ ≤ 2e-6 →
    Real.exp 2 * (clockK₀ B * Real.log n + 2) ≤ (clockJ B n : ℝ) ∧
    ((n : ℝ) ^ B + 1) * (Real.exp (Real.sqrt θ * (clockK₀ B * Real.log n + 2)) / Real.sqrt θ) *
        clockShortBound B n +
      (clockJ B n : ℝ) ^ 2 * (n : ℝ) ^ B * ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ) *
        (Real.exp (Real.sqrt θ * (clockK₀ B * Real.log n + 2)) / Real.sqrt θ) +
      ((n : ℝ) ^ B + 1) * Real.exp (-(clockJ B n : ℝ)) ≤ clockκ B n := by
  sorry

/-- L3.10h-inc (03:897–902, 03:907–944, 03:1084–1104): the incidence bound in closure form. For every endpoint
`v`, summed over tests, the probability of a bad outcome with `v` in the test's closure is at most `n^{-.6K₀}`.
Assembled from `closure_path_union`, `decPath_weight_sum`, `two_row_weight_sum`, `short_path_bad_bound`,
`walk_series_bound`, `walk_series_tail` and `incidence_numerics` (each real row is a root of at most `n^B + 1`
tests; the mesh horizon gives `(T + j) δ ≤ K₀ log n + 2` for all path lengths, as `log g ≤ C_g n`). -/
theorem closure_incidence_bound (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (v : Endpoint D.Row g),
      ∑ t : SamplingTest R K, D.law.pr (fun ξ =>
          closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) ∧
            v ∈ activeEndpoints ξ D.scope' (D.test' t)) ≤ clockκ B n := by
  sorry

/-- L3.10h-inc' (03:897–902): the incidence field of the raw sampler, from `badLeaves_incidence_le` and
`closure_incidence_bound`. -/
theorem clockBad_incidence (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (v : Endpoint D.Row g),
      ∑ i ∈ Finset.univ.filter (fun i : D.Bad => v ∈ D.badAct i), D.law.pr (D.badEvent i) ≤
        clockκ B n := by
  sorry

/-- L3.10g-raw (03:1109–1110, 03:1127–1128): the raw joint target bound, Step 7 with the empty insertion
(noninjective targets have probability zero, the marks carrying their labels). -/
theorem target_raw_bound (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (S : Finset R) (o : ∀ a, Ω a),
      (S.card : ℝ) ≤ (n : ℝ) ^ B →
      D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) ≤
        (1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (D.C.trimmed a).w (o a) := by
  sorry

/-- L3.10h-target (03:1121–1128): the target field of the raw sampler. The rectangles are the target rectangles
(`targetRects`, enumerated), each the event of one leaf (`clockLeaf_meet`) with at most `n^B L` active endpoints,
hence forcing against bad leaves with disjoint active sets (`leaf_forcing_coupling`); they cover the target on
the avoidance event (`targetRect_cover`) and their probabilities sum to at most the raw joint bound
(`targetRects_sum_le`, `target_raw_bound`). -/
theorem clock_target (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω)
      (S : Finset R) (o : ∀ a, Ω a), (S.card : ℝ) ≤ (n : ℝ) ^ B →
      ∃ (m : ℕ) (rect : Fin m → ClockField D.mesh.ticks D.Row g D.Out → Prop)
        (actR : Fin m → Finset (Endpoint D.Row g)),
        (∀ r, ((actR r).card : ℝ) ≤ (n : ℝ) ^ B * clockL B n) ∧
        (∀ r (S' : Finset D.Bad), (∀ j ∈ S', Disjoint (actR r) (D.badAct j)) →
          D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) ≤
            D.law.pr (rect r) * D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x)) ∧
        (∀ x, (∀ i, ¬ D.badEvent i x) → (∀ a ∈ S, D.out x a = o a) → ∃ r, rect r x) ∧
        ∑ r, D.law.pr (rect r) ≤ (1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (D.C.trimmed a).w (o a) := by
  sorry

/-- L3.10h-empty (TeX 03:797, "an empty assignment may be ignored"): with no real rows the one-point space is a
raw sampler (no bad events; every predicate has empty scope and is unsatisfiable). -/
theorem rawSampler_of_isEmpty {n g : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)] [IsEmpty R]
    (I : SamplingInstance n g R K Ω) (q : ∀ a, FinProb (Ω a)) (B A P L κ η : ℝ)
    (hn : 2 ≤ n) (hP : 0 < P) (hI : I.Admissible B A P) (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hη : 0 ≤ η) :
    Nonempty (RawSampler I q B L κ η) := by
  sorry

/-! ### Assembly -/

/-- L3.10b–h without Step 1 and without the avoidance step (TeX 03:844–1111, 03:1121–1128): from a Step 1
certificate, the completed finite-mesh clock matching (Steps 2–7) with its truncated exploration leaves gives a
raw sampler for the trimmed laws, with `L = ⌈n^{.1K₀}⌉`, `κ = n^{-.6K₀}` (03:872, 03:898–902), so that
`n^B L κ → 0`. The constants come first, with `4B + 4 ≤ P` so that Step 1 applies. Assembled: the empty instance
by `rawSampler_of_isEmpty`; otherwise the clock field of `ClockData` with the bad leaves as bad events
(`ClockData.badAct_nonempty`, `ClockData.badAct_card`, `clockBad_incidence`, `ClockData.badEvent_forcing`,
`ClockData.good`) and the target rectangles (`clock_target`). -/
theorem clock_raw_sampler (B C_g : ℝ) (hB : 1 ≤ B) :
    ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ L κ : ℕ → ℝ, 4 * B + 4 ≤ P ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ B * L n * κ n) atTop (nhds 0) ∧
      ∀ n ≥ n₀, 0 ≤ L n ∧ 0 ≤ κ n ∧ 4 * L n * κ n ≤ 1 ∧
      ∀ g : ℕ, Real.log g ≤ C_g * n →
      ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
        [∀ a, DecidableEq (Ω a)] (I : SamplingInstance n g R K Ω), I.Admissible B A P →
        ∀ C : TrimCertificate I B A P,
        Nonempty (RawSampler I C.trimmed B (L n) (κ n) (n : ℝ)⁻¹) := by
  obtain ⟨hlim, n₁, hconst⟩ := clock_constants B hB
  obtain ⟨n₂, hinc⟩ := clockBad_incidence B C_g hB
  obtain ⟨n₃, htarget⟩ := clock_target B C_g hB
  have hP0 : 0 < clockP B := by unfold clockP clockK₀; linarith
  refine ⟨clockA B, clockP B, max n₁ (max n₂ n₃), clockL B, clockκ B, ?_, hlim, ?_⟩
  · unfold clockP clockK₀; linarith
  intro n hn
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hn2, hLκ, hBL, hL1⟩ := hconst n hn₁
  refine ⟨Nat.cast_nonneg _, Real.rpow_nonneg (Nat.cast_nonneg _) _, hLκ, ?_⟩
  intro g hg R K _ _ _ Ω _ _ I hI C
  rcases isEmpty_or_nonempty R with hR | hR
  · exact rawSampler_of_isEmpty I C.trimmed B (clockA B) (clockP B) (clockL B n) (clockκ B n)
      (n : ℝ)⁻¹ hn2 hP0 hI (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  · obtain ⟨mesh⟩ := finiteMeshPlan_exists n (clockK₀ B) hn2 (by unfold clockK₀; linarith)
    let D : ClockData B n g R K Ω := ⟨I, hI, C, mesh⟩
    have hroots : ∀ k, ((D.I.scope k).card : ℝ) ≤ (clockLnat B n : ℝ) :=
      fun k => le_trans (hI.2.2.2.1 k) hBL
    exact ⟨{
      Space := ClockField D.mesh.ticks D.Row g D.Out
      law := D.law
      out := D.out
      Vertex := Endpoint D.Row g
      Bad := D.Bad
      badDecEq := Classical.decEq _
      bad := D.badEvent
      act := D.badAct
      act_nonempty := D.badAct_nonempty hn2 hP0 hL1
      act_card := D.badAct_card hroots hL1
      incidence := hinc n hn₂ g hg D
      forcing := D.badEvent_forcing
      good := D.good
      target := htarget n hn₃ g hg D }⟩

/-- L3.10h without Step 1 (03:844–1128), assembled: the raw sampler of the clock construction, conditioned
through `leaf_avoidance_transfer`, gives a law on real outputs that is injective, avoids every predicate, and
has the joint product bound relative to the trimmed laws. -/
theorem step8_trimmed_core (B C_g : ℝ) (hB : 1 ≤ B) :
    ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ, 4 * B + 4 ≤ P ∧ Tendsto ε atTop (nhds 0) ∧
    ∀ n ≥ n₀, ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (I : SamplingInstance n g R K Ω), I.Admissible B A P →
      ∀ C : TrimCertificate I B A P,
      ∃ J : FinProb (∀ a, Ω a),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => I.lab a (ω a)) ∧ ∀ k, ¬ I.failure k ω) ∧
        (∀ (S : Finset R) (o : ∀ a, Ω a), ((S.card : ℝ) ≤ (n : ℝ) ^ B) →
          J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
            (1 + ε n) * ∏ a ∈ S, (C.trimmed a).w (o a)) := by
  obtain ⟨A, P, n₀, L, κ, hP, hsmall, hraw⟩ := clock_raw_sampler B C_g hB
  refine ⟨A, P, n₀,
    fun n => Real.exp (4 * ((n : ℝ) ^ B * L n) * κ n) * (1 + (n : ℝ)⁻¹) - 1, hP, ?_, ?_⟩
  · have hx : Tendsto (fun n : ℕ => 4 * ((n : ℝ) ^ B * L n) * κ n) atTop (nhds 0) := by
      have h := hsmall.const_mul 4
      simpa [mul_assoc] using h
    have hexp := (Real.continuous_exp.tendsto 0).comp hx
    have hlim := (hexp.mul ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))).sub_const 1
    convert hlim using 2 <;> simp
  · intro n hn g hg R K _ _ _ Ω _ _ I hI C
    obtain ⟨hL0, hκ0, hLκ, hrest⟩ := hraw n hn
    obtain ⟨X⟩ := hrest g hg I hI C
    obtain ⟨J, hJs, hJt⟩ :=
      leaf_avoidance_transfer I C.trimmed B (L n) (κ n) (n : ℝ)⁻¹ hL0 hκ0 hLκ X
    refine ⟨J, hJs, fun S o hS => ?_⟩
    calc J.pr (fun ω => ∀ a ∈ S, ω a = o a)
        ≤ Real.exp (4 * ((n : ℝ) ^ B * L n) * κ n) *
            ((1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (C.trimmed a).w (o a)) := hJt S o hS
      _ = (1 + (Real.exp (4 * ((n : ℝ) ^ B * L n) * κ n) * (1 + (n : ℝ)⁻¹) - 1)) *
            ∏ a ∈ S, (C.trimmed a).w (o a) := by ring

/-- L3.10h (03:1084–1131), assembled: trim and complete (Step 1), run the trimmed core, and pay the
renormalization cost of Step 1 on the queried rows (03:1128–1131). This is the sub-node consumed by the
exported theorem. -/
theorem step8_bad_leaf_avoidance (B C_g : ℝ) (hB : 1 ≤ B) :
    ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ ∀ n ≥ n₀, ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (lab : ∀ a, Ω a → Fin g) (p : ∀ a, FinProb (Ω a))
      (F : K → (∀ a, Ω a) → Prop) (sc : K → Finset R),
      (∀ y, ∑ a, labMarg (p a) (lab a) y ≤ 1e-8) →
      (∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) →
      (∀ k, FinProb.DependsOn (F k) (sc k)) →
      (∀ k, ((sc k).card : ℝ) ≤ (n : ℝ) ^ B) →
      (∀ a, ((Finset.univ.filter (fun k => a ∈ sc k)).card : ℝ) ≤ (n : ℝ) ^ B) →
      (∀ k, (FinProb.pi p).pr (F k) ≤ (n : ℝ) ^ (-P)) →
      ∃ J : FinProb (∀ a, Ω a),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => lab a (ω a)) ∧ ∀ k, ¬ F k ω) ∧
        (∀ (S : Finset R) (o : ∀ a, Ω a), ((S.card : ℝ) ≤ (n : ℝ) ^ B) →
          J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
            (1 + ε n) * ∏ a ∈ S, (p a).w (o a)) := by
  obtain ⟨A, P, n₀, ε, hP, hε, hcore⟩ := step8_trimmed_core B C_g hB
  refine ⟨A, P, max n₀ 2,
    fun n => (1 + |ε n|) * (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) - 1, ?_, ?_⟩
  · have hexp : 0 < P / 2 - 2 * B := by linarith
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * B - P / 2)) atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop hexp).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, neg_sub] using h
    have habs : Tendsto (fun n => |ε n|) atTop (nhds 0) := by
      simpa using hε.abs
    have hlim := ((tendsto_const_nhds (x := (1 : ℝ))).add habs).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hpow.const_mul 2))
    convert hlim.sub_const 1 using 2
    norm_num
  · intro n hn g hg R K _ _ _ Ω _ _ lab p F sc h1 h2 h3 h4 h5 h6
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    let I : SamplingInstance n g R K Ω := ⟨lab, p, F, sc⟩
    have hI : I.Admissible B A P := by
      unfold SamplingInstance.Admissible
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    obtain ⟨C⟩ := step1_trim_and_complete I B A P hn2 (by linarith) hP hI
    obtain ⟨J, hJsupp, hJ⟩ := hcore n hn0 g hg I hI C
    refine ⟨J, hJsupp, fun S o hS => ?_⟩
    have hcoreS := hJ S o hS
    have huntrim := untrim_product_bound I B A P hn2 (by linarith) hP C S o hS
    have hprod : 0 ≤ ∏ a ∈ S, (C.trimmed a).w (o a) :=
      Finset.prod_nonneg fun a _ => (C.trimmed a).nonneg (o a)
    have hfac : 0 ≤ 1 + |ε n| := by positivity
    calc J.pr (fun ω => ∀ a ∈ S, ω a = o a)
        ≤ (1 + ε n) * ∏ a ∈ S, (C.trimmed a).w (o a) := hcoreS
      _ ≤ (1 + |ε n|) * ∏ a ∈ S, (C.trimmed a).w (o a) :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self (ε n)]) hprod
      _ ≤ (1 + |ε n|) * ((1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) * ∏ a ∈ S, (p a).w (o a)) :=
          mul_le_mul_of_nonneg_left huntrim hfac
      _ = (1 + ((1 + |ε n|) * (1 + 2 * (n : ℝ) ^ (2 * B - P / 2)) - 1)) *
            ∏ a ∈ S, (p a).w (o a) := by ring

end HypercubeRamsey.Clock
