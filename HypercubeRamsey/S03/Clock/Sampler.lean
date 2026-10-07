import HypercubeRamsey.S03.Clock.Sampler_q_clock_sampler

set_option maxHeartbeats 5000000

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
  classical
  let α : ℝ := clockK₀ B / 10
  let β : ℝ := 3 * clockK₀ B / 5
  have hK₀ : 0 < clockK₀ B := by unfold clockK₀; linarith
  have hα : 0 < α := by dsimp [α]; linarith
  have hBα : B ≤ α := by dsimp [α, clockK₀]; ring_nf; linarith
  have hαβ : α < β := by dsimp [α, β]; linarith [hK₀]
  have he : B + α - β < 0 := by dsimp [α, β, clockK₀]; linarith
  have heTail : α - β < 0 := by linarith [hαβ]
  have hpow (n : ℕ) (hn : 2 ≤ n) :
      (n : ℝ) ^ B * (n : ℝ) ^ α * (n : ℝ) ^ (-β) =
        (n : ℝ) ^ (B + α - β) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
    calc
      (n : ℝ) ^ B * (n : ℝ) ^ α * (n : ℝ) ^ (-β) =
          ((n : ℝ) ^ B * (n : ℝ) ^ α) * (n : ℝ) ^ (-β) := rfl
      _ = (n : ℝ) ^ (B + α) * (n : ℝ) ^ (-β) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ ((B + α) + (-β)) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (B + α - β) := by congr 1 <;> ring
  have htailPow (n : ℕ) (hn : 2 ≤ n) :
      (n : ℝ) ^ α * (n : ℝ) ^ (-β) = (n : ℝ) ^ (α - β) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
    calc
      (n : ℝ) ^ α * (n : ℝ) ^ (-β) = (n : ℝ) ^ (α + (-β)) := by
        rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (α - β) := by congr 1 <;> ring
  have hncast (n : ℕ) (hn : 2 ≤ n) : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos (n : ℕ) (hn : 2 ≤ n) : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) (hncast n hn)
  have hceilLow (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) ^ α ≤ (clockLnat B n : ℝ) := by
    simpa [clockLnat, α] using (Nat.le_ceil ((n : ℝ) ^ α))
  have hceilHigh (n : ℕ) (hn : 2 ≤ n) :
      (clockLnat B n : ℝ) < (n : ℝ) ^ α + 1 := by
    have hnonneg : 0 ≤ (n : ℝ) ^ α := (Real.rpow_pos_of_pos (hnpos n hn) α).le
    simpa [clockLnat, α] using Nat.ceil_lt_add_one hnonneg
  have hαge1 (n : ℕ) (hn : 2 ≤ n) : 1 ≤ (n : ℝ) ^ α := by
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le (by linarith [hncast n hn]) (by linarith [hα])
  have hLbound (n : ℕ) (hn : 2 ≤ n) : clockL B n ≤ 2 * (n : ℝ) ^ α := by
    change (clockLnat B n : ℝ) ≤ 2 * (n : ℝ) ^ α
    calc
      (clockLnat B n : ℝ) ≤ (n : ℝ) ^ α + 1 := le_of_lt (hceilHigh n hn)
      _ ≤ 2 * (n : ℝ) ^ α := by nlinarith [hαge1 n hn]
  have hpowLimit : Tendsto (fun n : ℕ => (n : ℝ) ^ (B + α - β)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp tendsto_natCast_atTop_atTop
    have hcomp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(-(B + α - β)))) atTop (nhds 0) :=
      h.congr (fun _ => rfl)
    have heq : ∀ n : ℕ, (n : ℝ) ^ (-(-(B + α - β))) = (n : ℝ) ^ (B + α - β) := by
      intro n
      congr 1
      ring
    exact hcomp.congr heq
  have hlimit : Tendsto (fun n : ℕ => (n : ℝ) ^ B * clockL B n * clockκ B n) atTop (nhds 0) := by
    have hmajor : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (B + α - β)) atTop (nhds 0) := by
      simpa [mul_comm] using hpowLimit.const_mul 2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
    · exact Filter.Eventually.of_forall fun n => by
        simp only [clockL, clockκ]
        positivity
    · filter_upwards [Ici_mem_atTop 2] with n hn
      have hL := hLbound n hn
      have hκ : clockκ B n = (n : ℝ) ^ (-β) := by simp [clockκ, β]
      rw [hκ]
      calc
        (n : ℝ) ^ B * clockL B n * (n : ℝ) ^ (-β) ≤
            (n : ℝ) ^ B * (2 * (n : ℝ) ^ α) * (n : ℝ) ^ (-β) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg (Nat.cast_nonneg _) _))
                (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = 2 * ((n : ℝ) ^ B * (n : ℝ) ^ α * (n : ℝ) ^ (-β)) := by ring
        _ = 2 * (n : ℝ) ^ (B + α - β) := by rw [hpow n hn]
  have htailLimit : Tendsto (fun n : ℕ => 8 * (n : ℝ) ^ (α - β)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr heTail)).comp tendsto_natCast_atTop_atTop
    have hcomp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(-(α - β)))) atTop (nhds 0) :=
      h.congr (fun _ => rfl)
    have heq : ∀ n : ℕ, (n : ℝ) ^ (-(-(α - β))) = (n : ℝ) ^ (α - β) := by
      intro n
      congr 1
      ring
    simpa [mul_comm] using hcomp.congr heq |>.const_mul 8
  have htailSmall : ∀ᶠ n : ℕ in atTop, 8 * (n : ℝ) ^ (α - β) < 1 :=
    (tendsto_order.1 htailLimit).2 1 (by norm_num)
  have hfinal : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 4 * clockL B n * clockκ B n ≤ 1 ∧
        (n : ℝ) ^ B ≤ (clockLnat B n : ℝ) ∧ 1 ≤ clockLnat B n := by
    filter_upwards [Ici_mem_atTop 2, htailSmall] with n hn hsmall
    have hκ : clockκ B n = (n : ℝ) ^ (-β) := by simp [clockκ, β]
    have hLκ : 4 * clockL B n * clockκ B n ≤ 8 * (n : ℝ) ^ (α - β) := by
      rw [hκ]
      calc
        4 * clockL B n * (n : ℝ) ^ (-β) ≤ 4 * (2 * (n : ℝ) ^ α) * (n : ℝ) ^ (-β) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hLbound n hn) (by norm_num))
            (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = 8 * ((n : ℝ) ^ α * (n : ℝ) ^ (-β)) := by ring
        _ = 8 * (n : ℝ) ^ (α - β) := by rw [htailPow n hn]
    have hBpow : (n : ℝ) ^ B ≤ (n : ℝ) ^ α :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [hncast n hn]) hBα
    have hLnat : (n : ℝ) ^ B ≤ (clockLnat B n : ℝ) := hBpow.trans (hceilLow n hn)
    have hLone : (1 : ℝ) ≤ (clockLnat B n : ℝ) := hαge1 n hn |>.trans (hceilLow n hn)
    exact ⟨hn, le_trans hLκ (le_of_lt hsmall), hLnat, by exact_mod_cast hLone⟩
  rcases Filter.eventually_atTop.1 hfinal with ⟨n₀, hn₀⟩
  exact ⟨hlimit, n₀, fun n hn => hn₀ n hn⟩

/-! ### Small facts -/

-- `finProb_nonempty` comes from `Clock/Inputs_p_clock_r1.lean` (identical statement).

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
  intro ω hω
  have hall : ∀ ω', I.failure k ω' := by
    intro ω'
    have heq := hI.2.2.1 k ω ω' (by intro a ha; simp [hk] at ha)
    exact heq.mp hω
  have hfull : I.productLaw.pr (I.failure k) = 1 := by
    change (FinProb.pi I.p).pr (I.failure k) = 1
    unfold FinProb.pr
    simp_rw [if_pos (hall _)]
    exact (FinProb.pi I.p).sum_eq_one
  have hnreal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
  have hpow : (n : ℝ) ^ (-P) < 1 := by
    calc
      (n : ℝ) ^ (-P) < (1 : ℝ) ^ (-P) :=
        Real.rpow_lt_rpow_of_neg (by norm_num) hnreal (by linarith)
      _ = 1 := by simp
  have hbound := hI.2.2.2.2.2 k
  rw [hfull] at hbound
  linarith

/-- On independent marked clocks every arrival mark carries its edge's label: the event of a mark with another
label is null (`outputMarkMass` vanishes off the label). -/
theorem invalid_marks_null {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (p : ∀ a, FinProb (Ω a)) (lab : ∀ a, Ω a → Fin g) :
    (clockFieldLaw (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab)).pr
      (fun ξ => ∃ e t o, ξ e = MeshClockValue.tick t o ∧ lab e.1 o ≠ e.2) = 0 := by
  classical
  let Q := clockFieldLaw (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab)
  have hzero (ξ : ClockField T R g Ω)
      (hξ : ∃ e t o, ξ e = MeshClockValue.tick t o ∧ lab e.1 o ≠ e.2) : Q.w ξ = 0 := by
    rcases hξ with ⟨e, t, o, he, hlabel⟩
    have hedge : (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab e).w (ξ e) = 0 := by
      rw [he]
      simp [samplingEdgeClockLaw, outputEdgeClockLaw, markedClockLaw, markedClockWeight,
        outputMarkMass, hlabel]
    change ∏ e' : RowLabel R g, (samplingEdgeClockLaw (T := T) δ hδ hδ1 p lab e').w (ξ e') = 0
    exact Finset.prod_eq_zero (Finset.mem_univ e) hedge
  unfold FinProb.pr
  apply Finset.sum_eq_zero
  intro ξ hξ
  by_cases hbad : ∃ e t o, ξ e = MeshClockValue.tick t o ∧ lab e.1 o ≠ e.2
  · rw [if_pos hbad]
    change Q.w ξ = 0
    exact hzero ξ hbad
  · simp [hbad]

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
  intro a
  cases a with
  | inl a =>
      change ∑ y, labMarg (D.C.trimmed a) (D.I.lab a) y = 1
      exact labMarg_sum_one (D.C.trimmed a) (D.I.lab a)
  | inr i =>
      change ∑ y, labMarg (⟨D.C.dummyLaw i, D.C.dummy_nonneg i, D.C.dummy_row_sum i⟩ : FinProb (Fin g)) id y = 1
      simp only [labMarg]
      simp [FinProb.w]
      exact D.C.dummy_row_sum i

/-- L3.10a-col (03:832–837): every completed column has total rate `θ`. -/
theorem completed_columns_eq : ∀ y, ∑ a, labMarg (D.law' a) (D.lab' a) y = D.C.theta := by
  intro y
  have hdummy (i : Fin D.C.dummyRows) :
      labMarg (⟨D.C.dummyLaw i, D.C.dummy_nonneg i, D.C.dummy_row_sum i⟩ : FinProb (Fin g)) id y =
        D.C.dummyLaw i y := by
    simp [labMarg]
  calc
    ∑ a, labMarg (D.law' a) (D.lab' a) y =
        (∑ a : R, labMarg (D.C.trimmed a) (D.I.lab a) y) +
          ∑ i : Fin D.C.dummyRows,
            labMarg (⟨D.C.dummyLaw i, D.C.dummy_nonneg i, D.C.dummy_row_sum i⟩ : FinProb (Fin g)) id y := by
          simp [law', lab', Fintype.sum_sum_type]
          rfl
    _ = D.C.theta := by simp [hdummy, D.C.completed_columns y]

include D in
/-- L3.10a-g (03:838–840): with a real row present, `g ≥ n^{A_*}`, since a real row is a probability law with
label atoms at most `n^{-A_*}`. -/
theorem card_labels_ge [Nonempty R] (hn : 1 ≤ n) : (n : ℝ) ^ clockA B ≤ g := by
  classical
  let a : R := Classical.choice ‹Nonempty R›
  have hsum := labMarg_sum_one (D.I.p a) (D.I.lab a)
  have hatom : ∀ y, labMarg (D.I.p a) (D.I.lab a) y ≤ (n : ℝ) ^ (-clockA B) :=
    fun y => D.admissible.2.1 a y
  have hsum_le : (1 : ℝ) ≤ (g : ℝ) * (n : ℝ) ^ (-clockA B) := by
    calc
      1 = ∑ y : Fin g, labMarg (D.I.p a) (D.I.lab a) y := hsum.symm
      _ ≤ ∑ _y : Fin g, (n : ℝ) ^ (-clockA B) := Finset.sum_le_sum fun y _ => hatom y
      _ = (g : ℝ) * (n : ℝ) ^ (-clockA B) := by simp
  have hnpos : 0 < (n : ℝ) := by
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (by exact_mod_cast hn)
  have hpow : 0 < (n : ℝ) ^ clockA B := Real.rpow_pos_of_pos hnpos _
  have hmul := mul_le_mul_of_nonneg_left hsum_le hpow.le
  have hpowmul : (n : ℝ) ^ clockA B * ((n : ℝ) ^ (-clockA B)) = 1 := by
    rw [← Real.rpow_add hnpos]
    simp
  have hproduct : (n : ℝ) ^ clockA B * ((g : ℝ) * (n : ℝ) ^ (-clockA B)) = g := by
    calc
      _ = ((n : ℝ) ^ clockA B * (n : ℝ) ^ (-clockA B)) * (g : ℝ) := by ring
      _ = g := by rw [hpowmul]; ring
  calc
    (n : ℝ) ^ clockA B = (n : ℝ) ^ clockA B * 1 := by ring
    _ ≤ (n : ℝ) ^ clockA B * ((g : ℝ) * (n : ℝ) ^ (-clockA B)) := hmul
    _ = g := hproduct

/-- L3.10a-atom (03:837–842): the completed atoms are at most `n^{-(A_* - 1)}` (trimmed atoms `≤ 2 n^{-A_*}`,
dummy atoms `≤ 2/g ≤ 2 n^{-A_*}`). -/
theorem completed_atom_le [Nonempty R] (hn : 2 ≤ n) :
    ∀ a y, labMarg (D.law' a) (D.lab' a) y ≤ (n : ℝ) ^ (-(clockA B - 1)) := by
  classical
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hpow_nonneg (e : ℝ) : 0 ≤ (n : ℝ) ^ e := (Real.rpow_pos_of_pos hnpos e).le
  have hfactor : 2 * (n : ℝ) ^ (-clockA B) ≤ (n : ℝ) ^ (-(clockA B - 1)) := by
    rw [show -(clockA B - 1) = 1 + -clockA B by ring, Real.rpow_add hnpos]
    simpa [Real.rpow_one] using
      (mul_le_mul_of_nonneg_right hnreal (hpow_nonneg (-clockA B)))
  intro a y
  cases a with
  | inl a =>
      exact (D.C.trimmed_atom a y).trans hfactor
  | inr i =>
      have hcard := D.card_labels_ge (by omega)
      have hnpowpos : (0 : ℝ) < (n : ℝ) ^ clockA B := Real.rpow_pos_of_pos hnpos _
      have hgpos : (0 : ℝ) < (g : ℝ) := lt_of_lt_of_le hnpowpos hcard
      have hninvg : (g : ℝ)⁻¹ ≤ ((n : ℝ) ^ clockA B)⁻¹ :=
        (inv_le_inv₀ hgpos hnpowpos).2 hcard
      have hbound : (1 : ℝ) / (g : ℝ) ≤ (n : ℝ) ^ (-clockA B) := by
        calc
          (1 : ℝ) / g = (g : ℝ)⁻¹ := by simp
          _ ≤ ((n : ℝ) ^ clockA B)⁻¹ := hninvg
          _ = (n : ℝ) ^ (-clockA B) := by rw [Real.rpow_neg hnpos.le]
      have hdummyMarg :
          labMarg (D.law' (.inr i)) (D.lab' (.inr i)) y = D.C.dummyLaw i y := by
        change labMarg
          (⟨D.C.dummyLaw i, D.C.dummy_nonneg i, D.C.dummy_row_sum i⟩ : FinProb (Fin g)) id y =
          D.C.dummyLaw i y
        simp [labMarg]
      rw [hdummyMarg]
      calc
        D.C.dummyLaw i y ≤ 2 / (g : ℝ) := D.C.dummy_atom i y
        _ = 2 * (1 / (g : ℝ)) := by ring
        _ ≤ 2 * (n : ℝ) ^ (-clockA B) := mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ ≤ (n : ℝ) ^ (-(clockA B - 1)) := hfactor

/-- L3.10a-θ (03:831): `10^{-6} ≤ θ ≤ 2·10^{-6}` once `g ≥ 10^6`. -/
theorem completed_theta_bounds (hg : (10 : ℝ) ^ 6 ≤ g) : 1e-6 ≤ D.C.theta ∧ D.C.theta ≤ 2e-6 := by
  constructor
  · exact D.C.theta_lower
  · have hgpos : (0 : ℝ) < g := by
      have : (0 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
      exact lt_of_lt_of_le this hg
    have hinv : (1 : ℝ) / (g : ℝ) ≤ 1 / ((10 : ℝ) ^ 6) :=
      one_div_le_one_div_of_le (by norm_num) hg
    have hinv' : (1 : ℝ) / (g : ℝ) ≤ 1e-6 := by
      have heq : (1 : ℝ) / ((10 : ℝ) ^ 6) = 1e-6 := by norm_num
      rw [← heq]
      exact hinv
    have hupper := D.C.theta_upper
    norm_num at hinv'
    norm_num
    linarith

/-! ### Forcing, goodness and the dependency sets (Steps 3 and 8) -/

/-- L3.10h-act (03:886–887): a bad leaf has a nonempty active set (a giant leaf has `L ≥ 1` active endpoints; a
failing test has a root, an empty-scope predicate being unsatisfiable). -/
theorem badAct_nonempty (hn : 2 ≤ n) (hP : 0 < clockP B) (hL : 1 ≤ clockLnat B n) :
    ∀ i : D.Bad, (D.badAct i).Nonempty := by
  classical
  intro i
  rcases i with ⟨t, ⟨ℓ, hℓ⟩⟩
  change ℓ.active.Nonempty
  unfold badLeaves' badLeaves at hℓ
  rcases Finset.mem_image.mp hℓ with ⟨ξ, hξ, hEq⟩
  have hbad : leafBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) :=
    (Finset.mem_filter.mp hξ).2
  let roots := testRootEndpoints (g := g) D.scope' (D.test' t)
  rcases hbad with hgiant | hsample
  · have hgiant' : (truncatedExploration ξ roots (clockLnat B n)).giant = true := by
      simpa [roots, testExploration, ClockData.test'] using hgiant
    have hcard := (truncatedExploration_card ξ roots (clockLnat B n)).1 hgiant'
    have hpos : 0 < (truncatedExploration ξ roots (clockLnat B n)).active.card :=
      lt_of_lt_of_le (by omega) hcard
    have hne : (truncatedExploration ξ roots (clockLnat B n)).active.Nonempty :=
      Finset.card_pos.mp hpos
    rw [← hEq]
    simpa [testLeaf, roots, explorationLeaf] using hne
  · have hroots : roots.Nonempty := by
      cases t with
      | predicate k =>
          by_cases he : D.I.scope k = ∅
          · have hsample' : testFails D.failure' D.scope' (greedyMatching ξ) (.predicate k) := by
              simpa [sampleTestBad, test'] using hsample
            rcases hsample' with ⟨ω, hfail, _⟩
            have hfalse := empty_scope_failure_false D.I B (clockA B) (clockP B)
              D.admissible hn hP k he (fun a => ω (Sum.inl a))
            exact False.elim (hfalse (by simpa [failure'] using hfail))
          · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
            refine ⟨Sum.inl (Sum.inl a), ?_⟩
            apply Finset.mem_image.mpr
            refine ⟨Sum.inl a, ?_, rfl⟩
            have hsc' : Sum.inl a ∈ D.scope' k := Finset.mem_map.mpr ⟨a, ha, rfl⟩
            simpa [testRoots, test'] using hsc'
      | singleton a =>
          refine ⟨Sum.inl (Sum.inl a), ?_⟩
          simp [roots, testRootEndpoints, testRoots, test']
    have hrootSub := (truncatedExploration_sound ξ roots (clockLnat B n)).1
    obtain ⟨r, hr⟩ := hroots
    rw [← hEq]
    refine ⟨r, ?_⟩
    simpa [testLeaf, roots, explorationLeaf] using hrootSub hr

/-- L3.10h-card (03:1113–1114): a bad leaf has at most `L` active endpoints (with at most `L` roots). -/
theorem badAct_card (hroots : ∀ k, ((D.I.scope k).card : ℝ) ≤ (clockLnat B n : ℝ))
    (hL : 1 ≤ clockLnat B n) : ∀ i : D.Bad, ((D.badAct i).card : ℝ) ≤ clockL B n := by
  classical
  intro i
  rcases i with ⟨t, ⟨ℓ, hℓ⟩⟩
  change (ℓ.active.card : ℝ) ≤ clockL B n
  let roots := testRootEndpoints (g := g) D.scope' (D.test' t)
  have hroots' : roots.card ≤ clockLnat B n := by
    cases t with
    | predicate k =>
        have hroot : (D.I.scope k).card ≤ clockLnat B n := by exact_mod_cast hroots k
        have hrootCard : (testRootEndpoints (g := g) D.scope' (.predicate k)).card =
            (D.I.scope k).card := by
          unfold testRootEndpoints testRoots
          rw [Finset.card_image_of_injective _ Sum.inl_injective]
          simp [scope']
        change (testRootEndpoints (g := g) D.scope' (.predicate k)).card ≤ clockLnat B n
        rw [hrootCard]
        exact hroot
    | singleton a =>
        have hrootCard : (testRootEndpoints (g := g) D.scope' (.singleton (Sum.inl a))).card = 1 := by
          simp [testRootEndpoints, testRoots]
        change (testRootEndpoints (g := g) D.scope' (.singleton (Sum.inl a))).card ≤ clockLnat B n
        rw [hrootCard]
        exact hL
  unfold badLeaves' badLeaves at hℓ
  rcases Finset.mem_image.mp hℓ with ⟨ξ, hξ, hEq⟩
  have hcard := (truncatedExploration_card ξ roots (clockLnat B n)).2.2 hroots'
  have hleafcard : ℓ.active.card ≤ clockLnat B n := by
    rw [← hEq]
    simpa [testLeaf, roots, explorationLeaf] using hcard
  change ((ℓ.active.card : ℕ) : ℝ) ≤ (clockLnat B n : ℝ)
  exact_mod_cast hleafcard

/-- L3.10c-force (03:888–896): the lopsided forcing property of a bad leaf against bad leaves with disjoint active
sets, from `leaf_forcing_coupling`. -/
theorem badEvent_forcing : ∀ (i : D.Bad) (S : Finset D.Bad), (∀ j ∈ S, Disjoint (D.badAct i) (D.badAct j)) →
    D.law.pr (fun ξ => D.badEvent i ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ) ≤
      D.law.pr (D.badEvent i) * D.law.pr (fun ξ => ∀ j ∈ S, ¬ D.badEvent j ξ) := by
  classical
  intro i S hdis
  let ℓ := i.2.1
  let leafList : List (ClockLeaf D.mesh.ticks D.Row g D.Out) := S.toList.map fun j => j.2.1
  have hnonneighbor : ∀ ℓ' ∈ leafList, ℓ.Nonneighbor ℓ' := by
    intro ℓ' hℓ'
    simp only [leafList, List.mem_map] at hℓ'
    rcases hℓ' with ⟨j, hj, rfl⟩
    simpa [ClockLeaf.Nonneighbor, badAct, ℓ] using hdis j (Finset.mem_toList.mp hj)
  have havoid (ξ : ClockField D.mesh.ticks D.Row g D.Out) :
      avoidsLeaves leafList ξ ↔ ∀ j ∈ S, ¬ D.badEvent j ξ := by
    constructor
    · intro h j hj
      apply h (j.2.1)
      apply List.mem_map.mpr
      exact ⟨j, Finset.mem_toList.mpr hj, rfl⟩
    · intro h L hL
      simp only [leafList, List.mem_map] at hL
      rcases hL with ⟨j, hj, rfl⟩
      exact h j (Finset.mem_toList.mp hj)
  have hnonneg : 0 ≤ D.law.pr ℓ.Event := finProb_pr_nonneg D.law ℓ.Event
  change D.law.pr (fun ξ => ℓ.Event ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ) ≤
    D.law.pr ℓ.Event * D.law.pr (fun ξ => ∀ j ∈ S, ¬ D.badEvent j ξ)
  by_cases hp0 : D.law.pr ℓ.Event = 0
  · calc
      D.law.pr (fun ξ => ℓ.Event ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ) ≤ D.law.pr ℓ.Event :=
        finProb_pr_mono D.law (by intro ξ hξ; exact hξ.1)
      _ = 0 := hp0
      _ = D.law.pr ℓ.Event * D.law.pr (fun ξ => ∀ j ∈ S, ¬ D.badEvent j ξ) := by rw [hp0]; ring
  · have hpos : 0 < D.law.pr ℓ.Event := by
      by_contra h
      have hle : D.law.pr ℓ.Event ≤ 0 := le_of_not_gt h
      exact hp0 (le_antisymm hle hnonneg)
    have hforce := leaf_forcing_coupling D.edgeLaw ℓ leafList hpos hnonneighbor
    change D.law.pr (fun ξ => ℓ.Event ξ ∧ avoidsLeaves leafList ξ) / D.law.pr ℓ.Event ≤
      D.law.pr (avoidsLeaves leafList) at hforce
    have hmul := (div_le_iff₀ hpos).mp hforce
    have prEq {A B : ClockField D.mesh.ticks D.Row g D.Out → Prop}
        (hAB : ∀ x, A x ↔ B x) : D.law.pr A = D.law.pr B := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hA : A x
      · have hB := (hAB x).mp hA
        simp [hA, hB]
      · have hB : ¬ B x := by intro h; exact hA ((hAB x).mpr h)
        simp [hA, hB]
    have havoidEq : D.law.pr (avoidsLeaves leafList) =
        D.law.pr (fun ξ => ∀ j ∈ S, ¬ D.badEvent j ξ) := by
      apply prEq
      intro ξ
      exact havoid ξ
    have hrectEq : D.law.pr (fun ξ => ℓ.Event ξ ∧ avoidsLeaves leafList ξ) =
        D.law.pr (fun ξ => ℓ.Event ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ) := by
      apply prEq
      intro ξ
      change (ℓ.Event ξ ∧ avoidsLeaves leafList ξ) ↔
        (ℓ.Event ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ)
      constructor
      · intro h
        exact ⟨h.1, (havoid ξ).mp h.2⟩
      · intro h
        exact ⟨h.1, (havoid ξ).mpr h.2⟩
    rw [hrectEq, havoidEq] at hmul
    change D.law.pr (fun ξ => ℓ.Event ξ ∧ ∀ j ∈ S, ¬ D.badEvent j ξ) ≤
      D.law.pr (fun ξ => ∀ j ∈ S, ¬ D.badEvent j ξ) * D.law.pr ℓ.Event at hmul
    simpa [mul_comm] using hmul

/-- Avoiding every bad leaf is the same as every test having a non-bad leaf (each clock field lies in its own
leaf). -/
theorem noBad_iff (ξ : ClockField D.mesh.ticks D.Row g D.Out) :
    (∀ i : D.Bad, ¬ D.badEvent i ξ) ↔
      ∀ t : SamplingTest R K, ¬ leafBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) := by
  classical
  constructor
  · intro h t hbad
    let ℓ := testLeaf ξ D.scope' (D.test' t) (clockLnat B n)
    have hmem : ℓ ∈ D.badLeaves' t := by
      unfold badLeaves' badLeaves
      apply Finset.mem_image.mpr
      refine ⟨ξ, ?_, rfl⟩
      simp [hbad]
    have hself : ℓ.Event ξ := by
      dsimp [ℓ, testLeaf]
      exact (explorationLeaf_event_iff ξ ξ (testRootEndpoints (g := g) D.scope' (D.test' t))
        (clockLnat B n)).2 ⟨rfl, rfl⟩
    let i : D.Bad := ⟨t, ⟨ℓ, hmem⟩⟩
    exact h i (by simpa [badEvent] using hself)
  · intro h i
    rcases i with ⟨t, ⟨ℓ, hℓ⟩⟩
    intro hbadEvent
    unfold badLeaves' badLeaves at hℓ
    rcases Finset.mem_image.mp hℓ with ⟨ξ', hξ', hEq⟩
    have hbad' : leafBad D.lab' D.failure' D.scope' (clockLnat B n) ξ' (D.test' t) :=
      (Finset.mem_filter.mp hξ').2
    have hev : (testLeaf ξ' D.scope' (D.test' t) (clockLnat B n)).Event ξ := by
      rw [hEq]
      exact hbadEvent
    have hinv := leafBad_leaf_invariant D.lab' D.failure' D.scope' (clockLnat B n)
      ξ' ξ (D.test' t) hev
    exact h t (hinv.mpr hbad')

/-- L3.10h-good (03:1117–1119): on the avoidance event every real row is matched with an output carrying its
matched label (distinct by `greedyMatching_label_injective`) and every predicate is avoided. -/
theorem good (ξ : ClockField D.mesh.ticks D.Row g D.Out) (hξ : ∀ i : D.Bad, ¬ D.badEvent i ξ) :
    Function.Injective (fun a => D.I.lab a (D.out ξ a)) ∧ ∀ k, ¬ D.I.failure k (D.out ξ) := by
  classical
  have hno := (D.noBad_iff ξ).mp hξ
  have hrow (a : R) : ∃ y, (greedyMatching ξ).assignment (Sum.inl a) = some (y, D.out ξ a) ∧
      D.I.lab a (D.out ξ a) = y := by
    have hnot : ¬ sampleTestBad D.lab' D.failure' D.scope' (greedyMatching ξ)
        (.singleton (Sum.inl a)) := by
      intro hbad
      exact hno (.singleton a) (Or.inr hbad)
    have hex : ∃ y o, (greedyMatching ξ).assignment (Sum.inl a) = some (y, o) ∧
        D.lab' (Sum.inl a) o = y := by
      have hdouble : ¬ ¬ ∃ y o, (greedyMatching ξ).assignment (Sum.inl a) = some (y, o) ∧
          D.lab' (Sum.inl a) o = y := by
        simpa [sampleTestBad, test'] using hnot
      exact Classical.not_not.mp hdouble
    rcases hex with ⟨y, o, hass, hlab⟩
    have hout : D.out ξ a = o := by
      unfold out
      rw [hass]
    refine ⟨y, ?_, ?_⟩
    · rw [hout]
      exact hass
    · rw [hout]
      simpa [lab'] using hlab
  refine ⟨?_, ?_⟩
  · intro a b hab
    rcases hrow a with ⟨ya, ha, hla⟩
    rcases hrow b with ⟨yb, hb, hlb⟩
    have hlabels : ya = yb := by
      calc
        ya = D.I.lab a (D.out ξ a) := hla.symm
        _ = D.I.lab b (D.out ξ b) := hab
        _ = yb := hlb
    have hab' := greedyMatching_label_injective ξ (Sum.inl a) (Sum.inl b) ya (D.out ξ a) (D.out ξ b)
      ha (by rw [← hlabels] at hb; exact hb)
    exact Sum.inl.inj hab'
  · intro k hfail
    have hnot : ¬ sampleTestBad D.lab' D.failure' D.scope' (greedyMatching ξ)
        (.predicate k) := by
      intro hbad
      exact hno (.predicate k) (Or.inr hbad)
    have hnotTest : ¬ testFails D.failure' D.scope' (greedyMatching ξ) (.predicate k) := by
      simpa [sampleTestBad, test'] using hnot
    apply hnotTest
    refine ⟨D.extendTarget (D.out ξ), ?_, ?_⟩
    · simpa [failure', extendTarget] using hfail
    · intro a ha
      cases a with
      | inl a =>
          have ha' : a ∈ D.I.scope k := by simpa [scope'] using ha
          obtain ⟨y, hy, _⟩ := hrow a
          refine ⟨y, ?_⟩
          change (greedyMatching ξ).assignment (Sum.inl a) = some (y, D.extendTarget (D.out ξ) (Sum.inl a))
          rw [show D.extendTarget (D.out ξ) (Sum.inl a) = D.out ξ a by rfl]
          exact hy
      | inr i => simp [scope'] at ha

/-- L3.10h-cover (03:1121–1122): on the avoidance event with the queried outputs, the tuple of singleton leaves of
the queried rows is a target rectangle. -/
theorem targetRect_cover (S : Finset R) (o : ∀ a, Ω a) (ξ : ClockField D.mesh.ticks D.Row g D.Out)
    (hξ : ∀ i : D.Bad, ¬ D.badEvent i ξ) (ho : ∀ a ∈ S, D.out ξ a = o a) :
    (fun a : S => testLeaf ξ D.scope' (D.test' (.singleton a.1)) (clockLnat B n)) ∈ D.targetRects S o := by
  classical
  have hno := (D.noBad_iff ξ).mp hξ
  have hgood (a : R) (ha : a ∈ S) : D.targetLeafGood ξ a (o a) := by
    have hnobad := hno (.singleton a)
    have hnotgiant :
        (testExploration ξ D.scope' (D.test' (.singleton a)) (clockLnat B n)).giant ≠ true := by
      intro hgiant
      exact hnobad (Or.inl hgiant)
    have hgiantfalse :
        (testExploration ξ D.scope' (D.test' (.singleton a)) (clockLnat B n)).giant = false := by
      cases hflag : (testExploration ξ D.scope' (D.test' (.singleton a)) (clockLnat B n)).giant with
      | false => rfl
      | true => exact False.elim (hnotgiant hflag)
    have hnotbad : ¬ sampleTestBad D.lab' D.failure' D.scope' (greedyMatching ξ)
        (.singleton (Sum.inl a)) := by
      intro hbad
      exact hnobad (Or.inr hbad)
    have hassign : ∃ y v, (greedyMatching ξ).assignment (Sum.inl a) = some (y, v) ∧
        D.lab' (Sum.inl a) v = y := by
      have hdouble : ¬ ¬ ∃ y v, (greedyMatching ξ).assignment (Sum.inl a) = some (y, v) ∧
          D.lab' (Sum.inl a) v = y := by
        simpa [sampleTestBad] using hnotbad
      exact Classical.not_not.mp hdouble
    rcases hassign with ⟨y, v, hass, _⟩
    have hout : D.out ξ a = v := by
      unfold out
      rw [hass]
    have hv : v = o a := by
      exact hout.symm.trans (ho a ha)
    have hmatch : (greedyMatching ξ).assignment (Sum.inl a) = some (y, o a) := by
      rw [hv] at hass
      exact hass
    exact ⟨hgiantfalse, ⟨y, hmatch⟩⟩
  unfold targetRects
  apply Finset.mem_image.mpr
  refine ⟨ξ, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro a
  exact hgood a.1 a.2

/-- L3.10h-part (03:1121–1128): distinct target rectangles are disjoint (`explorationLeaf_event_iff`) and each
lies in the joint target event (`nongiant_leaf_agreesBelow`, `closure_determines_root_assignment`). -/
theorem targetRects_sum_le (S : Finset R) (o : ∀ a, Ω a) :
    ∑ τ ∈ D.targetRects S o, D.law.pr (fun ξ => ∀ a, (τ a).Event ξ) ≤
      D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) := by
  classical
  let T := D.targetRects S o
  let E := fun τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out =>
    fun ξ => ∀ a, (τ a).Event ξ
  have hrep (τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out) (hτ : τ ∈ T) :
      ∃ z, (∀ a : S, τ a = testLeaf z D.scope' (D.test' (.singleton a.1)) (clockLnat B n)) ∧
        ∀ a : S, D.targetLeafGood z a.1 (o a.1) := by
    unfold T targetRects at hτ
    rcases Finset.mem_image.mp hτ with ⟨z, hz, hEq⟩
    have hgood := (Finset.mem_filter.mp hz).2
    refine ⟨z, ?_, hgood⟩
    intro a
    exact (congrFun hEq a).symm
  have hdisjoint (τ σ : S → ClockLeaf D.mesh.ticks D.Row g D.Out)
      (hτ : τ ∈ T) (hσ : σ ∈ T) (hne : τ ≠ σ) :
      ∀ ξ, ¬ (E τ ξ ∧ E σ ξ) := by
    rcases hrep τ hτ with ⟨zτ, hτleaf, _⟩
    rcases hrep σ hσ with ⟨zσ, hσleaf, _⟩
    intro ξ hev
    apply hne
    funext a
    let roots := testRootEndpoints (g := g) D.scope' (D.test' (.singleton a.1))
    have hevτ : (testLeaf zτ D.scope' (D.test' (.singleton a.1)) (clockLnat B n)).Event ξ := by
      rw [← hτleaf a]
      exact hev.1 a
    have hevσ : (testLeaf zσ D.scope' (D.test' (.singleton a.1)) (clockLnat B n)).Event ξ := by
      rw [← hσleaf a]
      exact hev.2 a
    have hrunτ := (explorationLeaf_event_iff zτ ξ roots (clockLnat B n)).mp hevτ
    have hrunσ := (explorationLeaf_event_iff zσ ξ roots (clockLnat B n)).mp hevσ
    have hbase : testLeaf zτ D.scope' (D.test' (.singleton a.1)) (clockLnat B n) =
        testLeaf zσ D.scope' (D.test' (.singleton a.1)) (clockLnat B n) := by
      simpa [testLeaf] using hrunτ.2.symm.trans hrunσ.2
    calc
      τ a = testLeaf zτ D.scope' (D.test' (.singleton a.1)) (clockLnat B n) := hτleaf a
      _ = testLeaf zσ D.scope' (D.test' (.singleton a.1)) (clockLnat B n) := hbase
      _ = σ a := (hσleaf a).symm
  have hsubset (τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out) (hτ : τ ∈ T) :
      ∀ ξ, E τ ξ → matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o) := by
    rcases hrep τ hτ with ⟨z, hτleaf, hgood⟩
    intro ξ hev
    intro r hr
    rcases Finset.mem_map.mp hr with ⟨a, ha, rfl⟩
    let roots := testRootEndpoints (g := g) D.scope' (D.test' (.singleton a))
    have hng : (truncatedExploration z roots (clockLnat B n)).giant = false := by
      simpa [roots, testExploration, test'] using (hgood ⟨a, ha⟩).1
    have hevLeaf : (testLeaf z D.scope' (D.test' (.singleton a)) (clockLnat B n)).Event ξ := by
      rw [← hτleaf ⟨a, ha⟩]
      exact hev ⟨a, ha⟩
    have hagree := nongiant_leaf_agreesBelow z ξ roots (clockLnat B n) hng hevLeaf
    have hroot : Sum.inl (Sum.inl a) ∈ roots := by
      simp [roots, testRootEndpoints, testRoots, test']
    have hassign := closure_determines_root_assignment z ξ roots hagree (Sum.inl a) hroot
    rcases (hgood ⟨a, ha⟩).2 with ⟨y, hbase⟩
    have hbase' : (greedyMatching z).assignment (Sum.inl a) = some (y, o a) := by
      simpa using hbase
    refine ⟨y, ?_⟩
    change (greedyMatching ξ).assignment (Sum.inl a) = some (y, D.extendTarget o (Sum.inl a))
    rw [show D.extendTarget o (Sum.inl a) = o a by rfl]
    exact hassign.symm.trans hbase'
  have hsumEq :
      (∑ τ ∈ T, D.law.pr (E τ)) =
        D.law.pr (fun ξ => ∃ τ ∈ T, E τ ξ) := by
    unfold FinProb.pr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ξ hξ
    letI : DecidablePred (fun τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out => E τ ξ) :=
      fun τ => Classical.propDecidable _
    by_cases hex : ∃ τ ∈ T, E τ ξ
    · rcases hex with ⟨τ₀, hτ₀, hE₀⟩
      have hpoint : (∑ τ ∈ T, if E τ ξ then D.law.w ξ else 0) = D.law.w ξ := by
        calc
          (∑ τ ∈ T, if E τ ξ then D.law.w ξ else 0) =
              ∑ τ ∈ T, if τ = τ₀ then D.law.w ξ else 0 := by
                apply Finset.sum_congr rfl
                intro τ hτ
                by_cases hE : E τ ξ
                · have heq : τ = τ₀ := by
                    by_contra hne
                    exact hdisjoint τ₀ τ hτ₀ hτ (Ne.symm hne) ξ ⟨hE₀, hE⟩
                  have hE₀' : E τ₀ ξ := by simpa [heq] using hE
                  simp [hE, heq, hE₀']
                · have hne : τ ≠ τ₀ := by
                    intro heq
                    subst τ
                    exact hE hE₀
                  simp [hE, hne]
          _ = D.law.w ξ := by simp [hτ₀]
      have hex' : ∃ τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out, τ ∈ T ∧ E τ ξ :=
        ⟨τ₀, hτ₀, hE₀⟩
      simpa only [if_pos hex'] using hpoint
    · have hnone : ∀ τ ∈ T, ¬ E τ ξ := by
        intro τ hτ hE
        exact hex ⟨τ, hτ, hE⟩
      have hsum0 : (∑ τ ∈ T, if E τ ξ then D.law.w ξ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro τ hτ
        simp [hnone τ hτ]
      simpa only [if_neg hex] using hsum0
  calc
    ∑ τ ∈ T, D.law.pr (E τ) = D.law.pr (fun ξ => ∃ τ ∈ T, E τ ξ) := hsumEq
    _ ≤ D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) :=
      finProb_pr_mono D.law (by
        intro ξ hξ
        rcases hξ with ⟨τ, hτ, hev⟩
        exact hsubset τ hτ ξ hev)

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
  classical
  let kconst : ℝ := clockK₀ B
  let q : ℝ := kconst / 100
  let gap : ℝ := kconst / 100 - kconst / 250
  let qTail : ℝ := 9 * kconst / 100
  let pref : ℝ := 1 + 2 * (kconst + 1) ^ 2
  let cTail : ℝ := 36000 * pref
  have hkform : kconst = 20 * B + 20 := by simp [kconst, clockK₀]
  have hk : 40 ≤ kconst := by rw [hkform]; linarith [hB]
  have hkpos : 0 < kconst := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hgap : 0 < gap := by dsimp [gap]; linarith [hkpos]
  have hqTail : 2 ≤ qTail := by dsimp [qTail]; linarith [hk]
  have htailExponent : B - gap < qTail := by
    dsimp [gap, qTail]
    rw [hkform]
    nlinarith [hB]
  have hnLargeSmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-q) < 1 / 2 ∧ (n : ℝ) ^ (-gap) < 1 / 72000 := by
    have hqLim := HypercubeRamsey.Lane_q_clock_sampler.rpow_neg_tendsto_zero q hq
    have hgapLim := HypercubeRamsey.Lane_q_clock_sampler.rpow_neg_tendsto_zero gap hgap
    filter_upwards
      [(tendsto_order.1 hqLim).2 (1 / 2) (by norm_num),
       (tendsto_order.1 hgapLim).2 (1 / 72000) (by norm_num)] with n hnq hngap
    exact ⟨hnq, hngap⟩
  have hnLargeMesh : ∀ᶠ n : ℕ in atTop, kconst / 125 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (kconst / 125)
  have hnLargeTail : ∀ᶠ n : ℕ in atTop, 8 * kconst ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (8 * kconst)
  have hnLargeRatio : ∀ᶠ n : ℕ in atTop,
      2 * cTail < (n : ℝ) ^ (qTail - (B - gap)) := by
    have hexp := HypercubeRamsey.Lane_q_clock_sampler.rpow_tendsto_top
      (qTail - (B - gap)) (sub_pos.mpr htailExponent)
    exact hexp.eventually_gt_atTop (2 * cTail)
  have hLarge : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ kconst / 125 ≤ (n : ℝ) ∧ 8 * kconst ≤ (n : ℝ) ∧
        (n : ℝ) ^ (-q) < 1 / 2 ∧ (n : ℝ) ^ (-gap) < 1 / 72000 ∧
        2 * cTail < (n : ℝ) ^ (qTail - (B - gap)) := by
    filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩,
      hnLargeMesh, hnLargeTail, hnLargeSmall, hnLargeRatio] with n hn2 hmesh htail hsmall hratio
    exact ⟨hn2, hmesh, htail, hsmall.1, hsmall.2, hratio⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hLarge
  refine ⟨n₀, ?_⟩
  intro n hn g R K _ _ _ Ω _ _ _ D roots hroots ins hins
  have hn2 : 2 ≤ n := hn₀ n hn |>.1
  have hnmesh : kconst / 125 ≤ (n : ℝ) := (hn₀ n hn).2.1
  have hntail : 8 * kconst ≤ (n : ℝ) := (hn₀ n hn).2.2.1
  have hsmallPow : (n : ℝ) ^ (-q) < 1 / 2 := (hn₀ n hn).2.2.2.1
  have hgapPow : (n : ℝ) ^ (-gap) < 1 / 72000 := (hn₀ n hn).2.2.2.2.1
  have hratio : 2 * cTail < (n : ℝ) ^ (qTail - (B - gap)) :=
    (hn₀ n hn).2.2.2.2.2
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlogle : Real.log (n : ℝ) ≤ n := Real.log_le_self (by positivity)
  have hkA : 20 ≤ clockA B := by unfold clockA clockK₀; linarith [hB]
  have hpow20 : (10 : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (20 : ℝ) := by norm_num
      _ ≤ (n : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow (by norm_num) hnreal (by norm_num)
  have hpowA : (n : ℝ) ^ (20 : ℝ) ≤ (n : ℝ) ^ clockA B :=
    Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hnreal) hkA
  have hgnum : (10 : ℝ) ^ 6 ≤ g :=
    le_trans (le_trans hpow20 hpowA) (D.card_labels_ge (by omega))
  have htheta := D.completed_theta_bounds hgnum
  have hthetaPos : 0 < D.C.theta := lt_of_lt_of_le (by norm_num) htheta.1
  have hsqrtTheta : 0 < Real.sqrt D.C.theta := Real.sqrt_pos.2 hthetaPos
  have hsqrtThetaNonneg : 0 ≤ Real.sqrt D.C.theta := Real.sqrt_nonneg _
  have hsqrtUpper : Real.sqrt D.C.theta ≤ 1 / 500 := by
    have hsquare := Real.sq_sqrt (le_of_lt hthetaPos)
    norm_num at htheta
    nlinarith [hsquare]
  have hinvSqrt : (Real.sqrt D.C.theta)⁻¹ ≤ 1000 := by
    have hs := Real.sq_sqrt (le_of_lt hthetaPos)
    have hlower : 1 / 1000 ≤ Real.sqrt D.C.theta := by nlinarith [hs, htheta.1]
    have hdiv : 1 / Real.sqrt D.C.theta ≤ 1000 := by
      apply (div_le_iff₀ hsqrtTheta).2
      nlinarith [hlower]
    simpa [one_div] using hdiv
  have hdelta : D.mesh.δ ≤ 1 := D.mesh.δ_le_one
  have hdeltaNonneg : 0 ≤ D.mesh.δ := D.mesh.δ_nonneg
  have hTdelta : (D.mesh.ticks : ℝ) * D.mesh.δ ≤
      kconst * Real.log (n : ℝ) + 1 := by
    have hcover := D.mesh.least_cover
    rw [D.mesh.horizon_eq] at hcover
    have hcover' : (D.mesh.ticks : ℝ) * D.mesh.δ <
        kconst * Real.log (n : ℝ) + D.mesh.δ := by simpa [kconst] using hcover
    linarith [hdelta]
  have hTdeltaNonneg : 0 ≤ (D.mesh.ticks : ℝ) * D.mesh.δ :=
    mul_nonneg (Nat.cast_nonneg _) hdeltaNonneg
  have hargDelta : 2 * Real.sqrt D.C.theta * D.mesh.δ ≤ 1 / 250 := by
    calc
      2 * Real.sqrt D.C.theta * D.mesh.δ ≤ 2 * (1 / 500) * 1 := by
        gcongr
      _ = 1 / 250 := by norm_num
  have hargTime : 2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ) ≤
      kconst / 250 * Real.log (n : ℝ) + 1 / 250 := by
    calc
      2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ) ≤
          (1 / 250) * (kconst * Real.log (n : ℝ) + 1) := by
        have hcoeff : 2 * Real.sqrt D.C.theta ≤ 1 / 250 := by linarith [hsqrtUpper]
        calc
          _ ≤ (1 / 250) * ((D.mesh.ticks : ℝ) * D.mesh.δ) :=
            mul_le_mul_of_nonneg_right hcoeff hTdeltaNonneg
          _ ≤ (1 / 250) * (kconst * Real.log (n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hTdelta (by norm_num)
      _ = kconst / 250 * Real.log (n : ℝ) + 1 / 250 := by ring
  have hexpTiny : Real.exp (1 / 125) ≤ 3 := by
    exact le_trans (Real.exp_le_exp.mpr (by norm_num : (1 / 125 : ℝ) ≤ 1))
      (le_of_lt Real.exp_one_lt_three)
  have hexpOne : Real.exp (1 / 250) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1 / 250 : ℝ) ≤ 1 / 125)).trans hexpTiny
  have hexpDelta : Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) ≤ 3 := by
    exact le_trans (Real.exp_le_exp.mpr hargDelta) hexpOne
  have hexpTime : Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) ≤
      Real.exp (1 / 250) * (n : ℝ) ^ (kconst / 250) := by
    calc
      _ ≤ Real.exp (kconst / 250 * Real.log (n : ℝ) + 1 / 250) :=
        Real.exp_le_exp.mpr hargTime
      _ = Real.exp (1 / 250) * (n : ℝ) ^ (kconst / 250) := by
        rw [Real.exp_add]
        have hp : Real.exp (kconst / 250 * Real.log (n : ℝ)) =
            (n : ℝ) ^ (kconst / 250) := by
          rw [Real.rpow_def_of_pos hnpos]
          congr 1
          ring
        rw [hp]
        ring
  have hpowGap : (n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250) =
      (n : ℝ) ^ (-gap) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    dsimp [q, gap]
    ring
  have hsmall : (n : ℝ) ^ (-q) + 2 * (n : ℝ) ^ (-q) *
      Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) *
      Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
      Real.sqrt D.C.theta ≤ 1 := by
    have hsecond : 2 * (n : ℝ) ^ (-q) *
        Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) *
        Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
        Real.sqrt D.C.theta ≤ 18000 * (n : ℝ) ^ (-gap) := by
      calc
        _ = (2 * (n : ℝ) ^ (-q) *
            Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) *
            Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ))) *
            (Real.sqrt D.C.theta)⁻¹ := by ring
        _ ≤ (2 * (n : ℝ) ^ (-q) * 3 *
            (Real.exp (1 / 250) * (n : ℝ) ^ (kconst / 250))) * 1000 := by
          gcongr
        _ ≤ 18000 * ((n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250)) := by
          calc
            _ ≤ (2 * (n : ℝ) ^ (-q) * 3 *
                (3 * (n : ℝ) ^ (kconst / 250))) * 1000 := by gcongr
            _ = 18000 * ((n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250)) := by ring
        _ = 18000 * (n : ℝ) ^ (-gap) := by rw [hpowGap]
    calc
      (n : ℝ) ^ (-q) + _ ≤ 1 / 2 + 18000 * (n : ℝ) ^ (-gap) := by
        exact add_le_add (le_of_lt hsmallPow) hsecond
      _ ≤ 1 := by nlinarith [hgapPow]
  have hmesh :
      (Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) - 1) *
        Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) ≤ 1 / 2 := by
    have hsumArg : 2 * Real.sqrt D.C.theta * D.mesh.δ +
        2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ) ≤
        kconst / 250 * Real.log (n : ℝ) + 1 / 125 := by
      calc
        _ = 2 * Real.sqrt D.C.theta *
            (D.mesh.δ + (D.mesh.ticks : ℝ) * D.mesh.δ) := by ring
        _ ≤ (1 / 250) * (kconst * Real.log (n : ℝ) + 2) := by
          have hsum : D.mesh.δ + (D.mesh.ticks : ℝ) * D.mesh.δ ≤
              kconst * Real.log (n : ℝ) + 2 := by linarith [hdelta, hTdelta]
          have hsumNonneg : 0 ≤ D.mesh.δ + (D.mesh.ticks : ℝ) * D.mesh.δ :=
            add_nonneg hdeltaNonneg hTdeltaNonneg
          have hcoeff : 2 * Real.sqrt D.C.theta ≤ 1 / 250 := by linarith [hsqrtUpper]
          calc
            _ ≤ (1 / 250) * (D.mesh.δ + (D.mesh.ticks : ℝ) * D.mesh.δ) :=
              mul_le_mul_of_nonneg_right hcoeff hsumNonneg
            _ ≤ (1 / 250) * (kconst * Real.log (n : ℝ) + 2) :=
              mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = kconst / 250 * Real.log (n : ℝ) + 1 / 125 := by ring
    have hexpSum : Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ +
        2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) ≤
        Real.exp (1 / 125) * (n : ℝ) ^ (kconst / 250) := by
      calc
        _ ≤ Real.exp (kconst / 250 * Real.log (n : ℝ) + 1 / 125) :=
          Real.exp_le_exp.mpr hsumArg
        _ = Real.exp (1 / 125) * (n : ℝ) ^ (kconst / 250) := by
          rw [Real.exp_add]
          have hp : Real.exp (kconst / 250 * Real.log (n : ℝ)) =
              (n : ℝ) ^ (kconst / 250) := by
            rw [Real.rpow_def_of_pos hnpos]
            congr 1
            ring
          rw [hp]
          ring
    have hdeltaPow : D.mesh.δ * (n : ℝ) ^ (kconst / 250) ≤ 1 := by
      rw [D.mesh.δ_eq]
      have hlogExp : Real.exp (kconst / 250 * Real.log (n : ℝ)) =
          (n : ℝ) ^ (kconst / 250) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
      have hprod : Real.exp (-((n : ℝ) ^ 2)) * (n : ℝ) ^ (kconst / 250) =
          Real.exp (-((n : ℝ) ^ 2) + kconst / 250 * Real.log (n : ℝ)) := by
        rw [← hlogExp, ← Real.exp_add]
      rw [hprod, Real.exp_le_one_iff]
      have hnlarge : kconst / 250 * Real.log (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hbase : kconst / 125 ≤ (n : ℝ) := hnmesh
        have hmul' : (kconst / 125) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
        have hmul : kconst / 125 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          simpa [pow_two] using hmul'
        calc
          kconst / 250 * Real.log (n : ℝ) ≤ kconst / 250 * n :=
            mul_le_mul_of_nonneg_left hlogle (by positivity)
          _ ≤ (n : ℝ) ^ 2 := by nlinarith [hmul]
      nlinarith
    have hexpSub := HypercubeRamsey.Lane_q_clock_sampler.exp_sub_one_le_mul_exp
      (2 * Real.sqrt D.C.theta * D.mesh.δ) (by positivity)
    have hsmallProduct : (Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) - 1) *
        Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) ≤
        (1 / 250) * Real.exp (1 / 125) *
          (D.mesh.δ * (n : ℝ) ^ (kconst / 250)) := by
      calc
        _ ≤ (2 * Real.sqrt D.C.theta * D.mesh.δ *
            Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ)) *
            Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) :=
          mul_le_mul_of_nonneg_right hexpSub (Real.exp_nonneg _)
        _ = (2 * Real.sqrt D.C.theta * D.mesh.δ) *
            Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ +
              2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) := by
            calc
              _ = (2 * Real.sqrt D.C.theta * D.mesh.δ) *
                  (Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ) *
                    Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ))) := by ring
              _ = _ := by rw [← Real.exp_add]
        _ ≤ (1 / 250) * D.mesh.δ *
            (Real.exp (1 / 125) * (n : ℝ) ^ (kconst / 250)) := by
          have hcoeff : 2 * Real.sqrt D.C.theta ≤ 1 / 250 := by linarith [hsqrtUpper]
          have hleft : 2 * Real.sqrt D.C.theta * D.mesh.δ ≤ (1 / 250) * D.mesh.δ :=
            mul_le_mul_of_nonneg_right hcoeff hdeltaNonneg
          calc
            _ ≤ ((1 / 250) * D.mesh.δ) *
                Real.exp (2 * Real.sqrt D.C.theta * D.mesh.δ +
                  2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) :=
                  mul_le_mul_of_nonneg_right hleft (Real.exp_nonneg _)
            _ ≤ ((1 / 250) * D.mesh.δ) *
                (Real.exp (1 / 125) * (n : ℝ) ^ (kconst / 250)) :=
                  mul_le_mul_of_nonneg_left hexpSum (by positivity)
        _ = (1 / 250) * Real.exp (1 / 125) *
            (D.mesh.δ * (n : ℝ) ^ (kconst / 250)) := by ring
    calc
      _ ≤ (1 / 250) * Real.exp (1 / 125) := by
        calc
          _ ≤ ((1 / 250) * Real.exp (1 / 125)) * 1 :=
            hsmallProduct.trans (mul_le_mul_of_nonneg_left hdeltaPow (by positivity))
          _ = (1 / 250) * Real.exp (1 / 125) := by ring
      _ ≤ 3 / 250 := by
        calc
          (1 / 250) * Real.exp (1 / 125) ≤ (1 / 250) * 3 :=
            mul_le_mul_of_nonneg_left hexpTiny (by norm_num)
          _ = 3 / 250 := by ring
      _ ≤ 1 / 2 := by norm_num
  have hnb : (n : ℝ) ≤ (n : ℝ) ^ B := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le (by linarith [hnreal]) hB
  have hpref : ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) ≤
      pref * (n : ℝ) ^ B := by
    have hinsR : (insertionSize ins : ℝ) ≤ (kconst + 1) ^ 2 * Real.log (n : ℝ) := hins
    have hcast : ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) =
        (roots.card : ℝ) + 2 * (insertionSize ins : ℝ) := by norm_num
    rw [hcast]
    calc
      (roots.card : ℝ) + 2 * (insertionSize ins : ℝ) ≤
          (n : ℝ) ^ B + 2 * (kconst + 1) ^ 2 * Real.log (n : ℝ) := by
            have hinsR' : 2 * (insertionSize ins : ℝ) ≤
                2 * ((kconst + 1) ^ 2 * Real.log (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hinsR (by norm_num)
            nlinarith [hroots, hinsR']
      _ ≤ (n : ℝ) ^ B + 2 * (kconst + 1) ^ 2 * n := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hlogle (by positivity))
      _ ≤ pref * (n : ℝ) ^ B := by
            dsimp [pref]
            nlinarith [hnb]
  have hrate : 4 * (n : ℝ) ^ (-q) *
      Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
        Real.sqrt D.C.theta ≤ 36000 * (n : ℝ) ^ (-gap) := by
    have hleft : 0 ≤ (n : ℝ) ^ (-q) := Real.rpow_nonneg (le_of_lt hnpos) _
    have hpow : (n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250) =
        (n : ℝ) ^ (-gap) := hpowGap
    calc
      _ = (4 * (n : ℝ) ^ (-q) *
          Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ))) *
          (Real.sqrt D.C.theta)⁻¹ := by ring
      _ ≤ (4 * (n : ℝ) ^ (-q) *
          (Real.exp (1 / 250) * (n : ℝ) ^ (kconst / 250))) * 1000 := by
            gcongr
      _ ≤ 36000 * ((n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250)) := by
            calc
              _ ≤ (4 * (n : ℝ) ^ (-q) *
                  (3 * (n : ℝ) ^ (kconst / 250))) * 1000 := by gcongr
              _ = 12000 * ((n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250)) := by ring
              _ ≤ 36000 * ((n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 250)) := by
                exact mul_le_mul_of_nonneg_right (by norm_num)
                  (mul_nonneg (Real.rpow_nonneg (le_of_lt hnpos) _)
                    (Real.rpow_nonneg (le_of_lt hnpos) _))
      _ = 36000 * (n : ℝ) ^ (-gap) := by rw [hpow]
  have heta : ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) *
      (4 * (n : ℝ) ^ (-q) *
        Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
        Real.sqrt D.C.theta) ≤ cTail * (n : ℝ) ^ (B - gap) := by
    calc
      _ ≤ (pref * (n : ℝ) ^ B) * (36000 * (n : ℝ) ^ (-gap)) :=
          mul_le_mul hpref hrate (by positivity) (by positivity)
      _ = cTail * (n : ℝ) ^ (B - gap) := by
          calc
            _ = (36000 * pref) * ((n : ℝ) ^ B * (n : ℝ) ^ (-gap)) := by ring
            _ = (36000 * pref) * (n : ℝ) ^ (B - gap) := by
              rw [← Real.rpow_add hnpos]
              rw [show B + -gap = B - gap by ring]
            _ = cTail * (n : ℝ) ^ (B - gap) := by rfl
  have hratio' : cTail ≤ (1 / 2) * (n : ℝ) ^ (qTail - (B - gap)) := by
    have : 0 < (n : ℝ) ^ (qTail - (B - gap)) :=
      Real.rpow_pos_of_pos hnpos _
    linarith [hratio]
  have heta' : ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) *
      (4 * (n : ℝ) ^ (-q) *
        Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
        Real.sqrt D.C.theta) ≤ (1 / 2) * (n : ℝ) ^ qTail := by
    calc
      _ ≤ cTail * (n : ℝ) ^ (B - gap) := heta
      _ ≤ ((1 / 2) * (n : ℝ) ^ (qTail - (B - gap))) *
          (n : ℝ) ^ (B - gap) :=
          mul_le_mul_of_nonneg_right hratio' (Real.rpow_nonneg (le_of_lt hnpos) _)
      _ = (1 / 2) * (n : ℝ) ^ qTail := by
          calc
            _ = (1 / 2) * ((n : ℝ) ^ (qTail - (B - gap)) * (n : ℝ) ^ (B - gap)) := by ring
            _ = (1 / 2) * (n : ℝ) ^ ((qTail - (B - gap)) + (B - gap)) := by
              rw [← Real.rpow_add hnpos]
            _ = (1 / 2) * (n : ℝ) ^ qTail := by
              rw [show qTail - (B - gap) + (B - gap) = qTail by ring]
  have hL : (n : ℝ) ^ (kconst / 10) ≤ (clockLnat B n : ℝ) := by
    simpa [clockLnat, kconst] using Nat.le_ceil ((n : ℝ) ^ (clockK₀ B / 10))
  have hdeltaL : (n : ℝ) ^ (-q) * (clockLnat B n : ℝ) ≥ (n : ℝ) ^ qTail := by
    calc
      (n : ℝ) ^ (-q) * (clockLnat B n : ℝ) ≥
          (n : ℝ) ^ (-q) * (n : ℝ) ^ (kconst / 10) :=
            mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg (le_of_lt hnpos) _)
      _ = (n : ℝ) ^ qTail := by
            rw [← Real.rpow_add hnpos]
            congr 1
            dsimp [q, qTail]
            ring
  have hpowTailLower : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ qTail :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hnreal]) hqTail
  have hlogDominated : 2 * kconst * Real.log (n : ℝ) + 1 ≤
      (n : ℝ) ^ qTail / 2 := by
    have hquadratic : 2 * kconst * Real.log (n : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
      calc
        2 * kconst * Real.log (n : ℝ) ≤ 2 * kconst * n :=
          mul_le_mul_of_nonneg_left hlogle (by positivity)
        _ ≤ (n : ℝ) ^ 2 / 4 := by
          have hmul : (8 * kconst) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right hntail (by positivity)
          nlinarith [hmul]
    have hnatpow : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by norm_num [Real.rpow_natCast]
    rw [hnatpow] at hquadratic
    have hnSq : 4 ≤ (n : ℝ) ^ (2 : ℝ) := by
      calc
        4 ≤ (n : ℝ) ^ 2 := by nlinarith [hnreal]
        _ = (n : ℝ) ^ (2 : ℝ) := hnatpow
    nlinarith [hpowTailLower, hquadratic, hnSq]
  have htailBound := giant_tail_under_insertion D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one
    D.law' D.lab' D.C.theta ((n : ℝ) ^ (-q)) hthetaPos
    (by
      have ht : D.C.theta ≤ 1 := le_trans htheta.2 (by norm_num)
      exact ht)
    (Real.rpow_pos_of_pos hnpos (-q))
    (fun a => (D.completed_rows_eq a).le)
    (fun y => (D.completed_columns_eq y).le)
    hsmall hmesh roots ins (clockLnat B n)
  have prEq {A B : ClockField D.mesh.ticks D.Row g D.Out → Prop}
      (hAB : ∀ ξ, A ξ ↔ B ξ) : D.law.pr A = D.law.pr B := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro ξ hξ
    by_cases hA : A ξ
    · have hB := (hAB ξ).mp hA
      simp [hA, hB]
    · have hB : ¬ B ξ := by
        intro h
        exact hA ((hAB ξ).mpr h)
      simp [hA, hB]
  have hcastEvent (ξ : ClockField D.mesh.ticks D.Row g D.Out) :
      (clockLnat B n ≤ (closureFrom (insertArrivals ins ξ) roots).card) ↔
        ((clockLnat B n : ℝ) ≤ ((closureFrom (insertArrivals ins ξ) roots).card : ℝ)) := by
    constructor <;> intro h <;> exact_mod_cast h
  have hprCast := prEq hcastEvent
  have hexpEst :
      Real.exp (-(n : ℝ) ^ qTail / 2) ≤ (n : ℝ) ^ (-(2 * kconst)) := by
    have hpowExp : Real.exp (-(2 * kconst * Real.log (n : ℝ))) =
        (n : ℝ) ^ (-(2 * kconst)) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring
    rw [← hpowExp]
    exact Real.exp_le_exp.mpr (by nlinarith [hlogDominated])
  calc
    D.law.pr (fun ξ => clockLnat B n ≤ (closureFrom (insertArrivals ins ξ) roots).card) =
        D.law.pr (fun ξ => (clockLnat B n : ℝ) ≤
          ((closureFrom (insertArrivals ins ξ) roots).card : ℝ)) := hprCast
    _ ≤
        Real.exp (-(n : ℝ) ^ qTail / 2) := by
          calc
            _ ≤ Real.exp (-((n : ℝ) ^ (-q)) * (clockLnat B n : ℝ) +
              ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) *
                (4 * (n : ℝ) ^ (-q) *
                  Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
                  Real.sqrt D.C.theta)) := htailBound
            _ ≤ Real.exp (-(n : ℝ) ^ qTail +
                ((roots.card + 2 * insertionSize ins : ℕ) : ℝ) *
                  (4 * (n : ℝ) ^ (-q) *
                    Real.exp (2 * Real.sqrt D.C.theta * ((D.mesh.ticks : ℝ) * D.mesh.δ)) /
                    Real.sqrt D.C.theta)) := by
              apply Real.exp_le_exp.mpr
              nlinarith [hdeltaL]
            _ ≤ Real.exp (-(n : ℝ) ^ qTail / 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith [heta']
    _ ≤ (n : ℝ) ^ (-(2 * kconst)) := hexpEst
    _ = (n : ℝ) ^ (-(2 * clockK₀ B)) := by simp [kconst]

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
  classical
  let kconst : ℝ := clockK₀ B
  have hkpos : 0 < clockK₀ B := by unfold clockK₀; linarith [hB]
  have hA : 10 * (B + clockK₀ B) < clockA B - 1 := by
    unfold clockA
    nlinarith
  obtain ⟨n₁, hstep⟩ := step7_target_product_bound B (clockA B - 1) C_g
    (clockK₀ B) hB hkpos hA
  refine ⟨max n₁ 2, ?_⟩
  intro n hn g hg R K _ _ _ Ω _ _ _ D k a₀ ins hins hinsPos hinsScope
  let fac : ℝ := 1 + (n : ℝ)⁻¹
  let pn : ℝ := (n : ℝ) ^ (-(clockP B / 3))
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn₂
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hA20 : 20 ≤ clockA B := by unfold clockA clockK₀; linarith [hB]
  have hpow20 : (10 : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (20 : ℝ) := by norm_num
      _ ≤ (n : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow (by norm_num) hnreal (by norm_num)
  have hpowA : (n : ℝ) ^ (20 : ℝ) ≤ (n : ℝ) ^ clockA B :=
    Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hnreal) hA20
  have hgnum : (10 : ℝ) ^ 6 ≤ g :=
    le_trans (le_trans hpow20 hpowA) (D.card_labels_ge (by omega))
  have htheta := D.completed_theta_bounds hgnum
  have hthetaAtom := D.completed_atom_le hn₂
  have hSbound : ((D.scope' k).card : ℝ) ≤ (n : ℝ) ^ B := by
    simpa [ClockData.scope'] using D.admissible.2.2.2.1 k
  have hstepAt := hstep n hn₁ D.mesh D.mesh.δ_nonneg D.mesh.δ_le_one
    D.law' D.lab' D.C.theta hg
    (fun y => D.completed_columns_eq y) htheta.2
    (fun a y => hthetaAtom a y) ins hins
  have hinvalid : D.law.pr
      (fun ξ => ∃ e t o, ξ e = MeshClockValue.tick t o ∧ D.lab' e.1 o ≠ e.2) = 0 := by
    simpa [ClockData.law, ClockData.edgeLaw] using
      (invalid_marks_null D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one D.law' D.lab')
  have hOrdinaryBound (S : Finset D.Row) (o : ∀ a : D.Row, D.Out a)
      (hScard : (S.card : ℝ) ≤ (n : ℝ) ^ B) :
      D.law.pr (fun ξ => matchesTargetsOrdinarily ins ξ S o) ≤
        fac * ∏ a ∈ S, (D.law' a).w (o a) := by
    by_cases hinj : Set.InjOn (fun a => D.lab' a (o a)) S
    · have h := hstepAt S o hinj hScard
      simpa [fac, ClockData.law, ClockData.edgeLaw] using h
    · have hcollision : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
          D.lab' a (o a) = D.lab' b (o b) := by
        by_contra hc
        apply hinj
        intro a ha b hb hab
        by_contra hne
        exact hc ⟨a, ha, b, hb, hne, hab⟩
      have hsub : ∀ ξ, matchesTargetsOrdinarily ins ξ S o →
          ∃ e t x, ξ e = MeshClockValue.tick t x ∧ D.lab' e.1 x ≠ e.2 := by
        intro ξ hξ
        rcases hcollision with ⟨a, ha, b, hb, hab, hlab⟩
        rcases hξ a ha with ⟨ya, hya, hyaIns⟩
        rcases hξ b hb with ⟨yb, hyb, hybIns⟩
        obtain ⟨ta, hta⟩ := greedyMatching_assignment_origin
          (insertArrivals ins ξ) a ya (o a) hya
        obtain ⟨tb, htb⟩ := greedyMatching_assignment_origin
          (insertArrivals ins ξ) b yb (o b) hyb
        have htaRaw : ξ (a, ya) = MeshClockValue.tick ta (o a) := by
          simpa [insertArrivals, hyaIns] using hta
        have htbRaw : ξ (b, yb) = MeshClockValue.tick tb (o b) := by
          simpa [insertArrivals, hybIns] using htb
        by_cases hmarkA : D.lab' a (o a) = ya
        · by_cases hmarkB : D.lab' b (o b) = yb
          · have hyEq : ya = yb := hmarkA.symm.trans (hlab.trans hmarkB)
            have hyb' : (greedyMatching (insertArrivals ins ξ)).assignment b =
                some (ya, o b) := by simpa [hyEq.symm] using hyb
            have hab' := greedyMatching_label_injective (insertArrivals ins ξ)
              a b ya (o a) (o b) hya hyb'
            exact False.elim (hab hab')
          · exact ⟨(b, yb), tb, o b, htbRaw, hmarkB⟩
        · exact ⟨(a, ya), ta, o a, htaRaw, hmarkA⟩
      have hz : D.law.pr (fun ξ => matchesTargetsOrdinarily ins ξ S o) = 0 := by
        apply le_antisymm
        · calc
            _ ≤ D.law.pr
                (fun ξ => ∃ e t x, ξ e = MeshClockValue.tick t x ∧ D.lab' e.1 x ≠ e.2) :=
                  finProb_pr_mono D.law hsub
            _ = 0 := hinvalid
        · exact finProb_pr_nonneg D.law _
      rw [hz]
      have hfacNonneg : 0 ≤ fac := by dsimp [fac]; positivity
      have hprodNonneg : 0 ≤ ∏ a ∈ S, (D.law' a).w (o a) := by
        apply Finset.prod_nonneg
        intro a ha
        exact (D.law' a).nonneg (o a)
      exact mul_nonneg hfacNonneg hprodNonneg
  let Sreal : Finset R := D.I.scope k
  let Scomp : Finset D.Row := D.scope' k
  let base : ∀ a : R, Ω a := fun a =>
    Classical.choice (finProb_nonempty (D.C.trimmed a))
  let lift : (∀ a : ↥Sreal, Ω a.1) → ∀ a : R, Ω a := fun u =>
    (Equiv.piEquivPiSubtypeProd (fun a => a ∈ Sreal) Ω).symm
      (u, fun a => base a.1)
  let failTuple : (∀ a : ↥Sreal, Ω a.1) → Prop := fun u =>
    D.I.failure k (lift u)
  let failTuples : Finset (∀ a : ↥Sreal, Ω a.1) :=
    Finset.univ.filter failTuple
  let outTuple (u : ∀ a : ↥Sreal, Ω a.1) : ∀ a : D.Row, D.Out a :=
    D.extendTarget (lift u)
  let ordinary (u : ∀ a : ↥Sreal, Ω a.1) :
      ClockField D.mesh.ticks D.Row g D.Out → Prop :=
    fun ξ => matchesTargetsOrdinarily ins ξ Scomp (outTuple u)
  have htupleCard : (Scomp.card : ℝ) ≤ (n : ℝ) ^ B := hSbound
  have htupleWeight (u : ∀ a : ↥Sreal, Ω a.1) :
      (∏ a ∈ Scomp, (D.law' a).w (outTuple u a)) =
        ∏ a : ↥Sreal, (D.C.trimmed a.1).w (u a) := by
    dsimp [Scomp, ClockData.scope', outTuple]
    rw [Finset.prod_map, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro a ha
    change (D.C.trimmed a.1).w (lift u a.1) = (D.C.trimmed a.1).w (u a)
    rw [show lift u a.1 = u a by simp [lift]]
  have hordinaryBound (u : ∀ a : ↥Sreal, Ω a.1) :
      D.law.pr (ordinary u) ≤ fac * ∏ a : ↥Sreal, (D.C.trimmed a.1).w (u a) := by
    rw [← htupleWeight u]
    exact hOrdinaryBound Scomp (outTuple u) htupleCard
  have hfailWeightSum :
      (∑ u ∈ failTuples, ∏ a : ↥Sreal, (D.C.trimmed a.1).w (u a)) =
        (FinProb.pi D.C.trimmed).pr (D.I.failure k) := by
    have hsubsum :
      (∑ u ∈ failTuples, ∏ a : ↥Sreal, (D.C.trimmed a.1).w (u a)) =
          (FinProb.pi (fun a : ↥Sreal => D.C.trimmed a.1)).pr failTuple := by
      unfold FinProb.pr
      rw [show failTuples = Finset.univ.filter failTuple by rfl, Finset.sum_filter]
      simp [FinProb.pi, failTuple]
    have hdep : FinProb.DependsOn (D.I.failure k) Sreal := D.admissible.2.2.1 k
    have hproj := HypercubeRamsey.Lane_q_clock_sampler.pi_pr_depends_eq_subtype
      D.C.trimmed Sreal (D.I.failure k) hdep base
    calc
      _ = (FinProb.pi (fun a : ↥Sreal => D.C.trimmed a.1)).pr failTuple := hsubsum
      _ = (FinProb.pi D.C.trimmed).pr (D.I.failure k) := by simpa [lift, failTuple] using hproj
  have hordinaryUnion :
      D.law.pr (fun ξ => ∃ u ∈ failTuples, ordinary u ξ) ≤ fac * pn := by
    calc
      _ ≤ ∑ u ∈ failTuples, D.law.pr (ordinary u) :=
        finProb_pr_biUnion_le_sum D.law failTuples ordinary
      _ ≤ ∑ u ∈ failTuples,
            fac * ∏ a : ↥Sreal, (D.C.trimmed a.1).w (u a) :=
        Finset.sum_le_sum fun u hu => hordinaryBound u
      _ = fac * ∑ u ∈ failTuples,
            ∏ a : ↥Sreal, (D.C.trimmed a.1).w (u a) := by rw [Finset.mul_sum]
      _ ≤ fac * pn := by
        rw [hfailWeightSum]
        have htrim := D.C.trimmed_failure k
        rw [show (n : ℝ) ^ (-clockP B / 3) = pn by
          dsimp [pn]
          congr 1
          ring] at htrim
        exact mul_le_mul_of_nonneg_left htrim (by positivity)
  by_cases ha₀ : a₀ ∈ Sreal
  · -- exceptional inserted matches are charged by the pinned trimmed failure bound
    let iScope : ↥Sreal := ⟨a₀, ha₀⟩
    let Sother : Type := {b : ↥Sreal // b ≠ iScope}
    let embOther : Sother ↪ D.Row := {
      toFun := fun b => Sum.inl b.1.1
      inj' := by
        intro b c h
        apply Subtype.ext
        apply Subtype.ext
        exact Sum.inl.inj h }
    let SotherComp : Finset D.Row := Finset.univ.map embOther
    have hotherSubset : SotherComp ⊆ Scomp := by
      intro r hr
      rcases Finset.mem_map.mp hr with ⟨b, hb, rfl⟩
      apply Finset.mem_map.mpr
      exact ⟨b.1.1, b.1.2, rfl⟩
    have hotherCard : (SotherComp.card : ℝ) ≤ (n : ℝ) ^ B := by
      have hnat : SotherComp.card ≤ Scomp.card := Finset.card_le_card hotherSubset
      exact (Nat.cast_le.mpr hnat).trans hSbound
    let pinScope (o : Ω a₀) (u : ∀ b : Sother, Ω b.1.1) :
        ∀ b : ↥Sreal, Ω b.1 :=
      HypercubeRamsey.Lane_q_clock_sampler.pinCoordinateRest iScope o u
    let pinReal (o : Ω a₀) (u : ∀ b : Sother, Ω b.1.1) : ∀ a : R, Ω a :=
      lift (pinScope o u)
    let pinOut (o : Ω a₀) (u : ∀ b : Sother, Ω b.1.1) :
        ∀ a : D.Row, D.Out a := D.extendTarget (pinReal o u)
    have hpinCoord (o : Ω a₀) (u : ∀ b : Sother, Ω b.1.1) (b : Sother) :
        pinReal o u b.1.1 = u b := by
      rcases b with ⟨a, hne⟩
      simp [pinReal, pinScope, lift,
        HypercubeRamsey.Lane_q_clock_sampler.pinCoordinateRest, hne]
    have hpinProduct (o : Ω a₀) (u : ∀ b : Sother, Ω b.1.1) :
        (∏ r ∈ SotherComp, (D.law' r).w (pinOut o u r)) =
          ∏ b : Sother, (D.C.trimmed b.1.1).w (u b) := by
      dsimp [SotherComp, pinOut]
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro b hb
      change (D.C.trimmed b.1.1).w (pinReal o u b.1.1) =
        (D.C.trimmed b.1.1).w (u b)
      rw [hpinCoord o u b]
    have htrimPosOfTick (y : Fin g) (t : Fin D.mesh.ticks) (o : Ω a₀)
        (htick : ins (Sum.inl a₀, y) = some (MeshClockValue.tick t o)) :
        0 < (D.C.trimmed a₀).w o := by
      have hpositive := hinsPos (Sum.inl a₀, y) (MeshClockValue.tick t o) htick
      by_contra hnot
      have hzero : (D.C.trimmed a₀).w o = 0 := by
        linarith [(D.C.trimmed a₀).nonneg o]
      have hweightZero :
          (D.edgeLaw (Sum.inl a₀, y)).w (MeshClockValue.tick t o) = 0 := by
        simp [ClockData.edgeLaw, samplingEdgeClockLaw, outputEdgeClockLaw,
          markedClockLaw, markedClockWeight, outputMarkMass, ClockData.law',
          ClockData.lab', hzero]
      linarith
    have hkeepOfTick (y : Fin g) (t : Fin D.mesh.ticks) (o : Ω a₀)
        (htick : ins (Sum.inl a₀, y) = some (MeshClockValue.tick t o)) :
        o ∈ D.C.keep a₀ := by
      by_contra hnot
      have hz := D.C.trimmed_supported a₀ o hnot
      have hp := htrimPosOfTick y t o htick
      linarith
    have hdepFailure : FinProb.DependsOn (D.I.failure k) Sreal := D.admissible.2.2.1 k
    let G : ∀ o : Ω a₀, (∀ a : R, Ω a) → Prop :=
      fun o ω => D.I.failure k ω ∧ ω a₀ = o
    have hGdepends (o : Ω a₀) : FinProb.DependsOn (G o) Sreal := by
      intro ω ω' hagree
      have hF := hdepFailure ω ω' hagree
      have ha := hagree a₀ ha₀
      apply propext
      constructor
      · rintro ⟨hf, hpin⟩
        exact ⟨hF.mp hf, by rw [← ha]; exact hpin⟩
      · rintro ⟨hf, hpin⟩
        exact ⟨hF.mpr hf, by rw [ha]; exact hpin⟩
    have hprojG (o : Ω a₀) :=
      HypercubeRamsey.Lane_q_clock_sampler.pi_pr_depends_eq_subtype
        D.C.trimmed Sreal (G o) (hGdepends o) base
    have hGscope (o : Ω a₀) (u : ∀ a : ↥Sreal, Ω a.1) :
        G o (lift u) ↔ failTuple u ∧ u iScope = o := by
      change (D.I.failure k (lift u) ∧ (lift u) a₀ = o) ↔
        (D.I.failure k (lift u) ∧ u iScope = o)
      rw [show (lift u) a₀ = u iScope by simp [lift, iScope, ha₀]]
    have hscopeJoint (o : Ω a₀) :
        (FinProb.pi (fun a : ↥Sreal => D.C.trimmed a.1)).pr
          (fun u => failTuple u ∧ u iScope = o) =
        (FinProb.pi D.C.trimmed).pr (G o) := by
      calc
        _ = (FinProb.pi (fun a : ↥Sreal => D.C.trimmed a.1)).pr (fun u => G o (lift u)) := by
          apply HypercubeRamsey.Lane_q_clock_sampler.finProb_pr_congr
          intro u
          exact (hGscope o u).symm
        _ = (FinProb.pi D.C.trimmed).pr (G o) := by simpa [lift] using hprojG o
    have hpinEq (o : Ω a₀) (hpos : 0 < (D.C.trimmed a₀).w o) :
        (FinProb.pi (fun b : Sother => D.C.trimmed b.1.1)).pr
            (fun v => D.I.failure k (pinReal o v)) =
          pinnedFailureProb D.C.trimmed D.I.failure k a₀ o := by
      have hratio := HypercubeRamsey.Lane_q_clock_sampler.pi_pr_pinned_eq_rest
        (fun a : ↥Sreal => D.C.trimmed a.1) failTuple iScope o hpos
      have hratio' :
          (FinProb.pi (fun a : ↥Sreal => D.C.trimmed a.1)).pr
            (fun u => failTuple u ∧ u iScope = o) / (D.C.trimmed a₀).w o =
          (FinProb.pi (fun b : Sother => D.C.trimmed b.1.1)).pr
            (fun v => D.I.failure k (pinReal o v)) := by
        simpa [pinReal, pinScope, failTuple, iScope] using hratio
      unfold pinnedFailureProb
      calc
        _ = (FinProb.pi (fun a : ↥Sreal => D.C.trimmed a.1)).pr
              (fun u => failTuple u ∧ u iScope = o) / (D.C.trimmed a₀).w o := hratio'.symm
        _ = (FinProb.pi D.C.trimmed).pr
              (G o) / (D.C.trimmed a₀).w o := by rw [hscopeJoint o]
        _ = (FinProb.pi D.C.trimmed).pr
              (fun ω => D.I.failure k ω ∧ ω a₀ = o) / (D.C.trimmed a₀).w o := by
                simp [G]
    let pinFailure (o : Ω a₀) (u : ∀ b : Sother, Ω b.1.1) : Prop :=
      D.I.failure k (pinReal o u)
    let pinFailSet (o : Ω a₀) : Finset (∀ b : Sother, Ω b.1.1) :=
      Finset.univ.filter (pinFailure o)
    have hpinWeightSum (o : Ω a₀) :
        (∑ u ∈ pinFailSet o, ∏ b : Sother, (D.C.trimmed b.1.1).w (u b)) =
          (FinProb.pi (fun b : Sother => D.C.trimmed b.1.1)).pr (pinFailure o) := by
      unfold FinProb.pr
      rw [show pinFailSet o = Finset.univ.filter (pinFailure o) by rfl, Finset.sum_filter]
      simp [FinProb.pi, pinFailure]
    have hpinProbabilityBound (o : Ω a₀) (hpos : 0 < (D.C.trimmed a₀).w o)
        (hkeep : o ∈ D.C.keep a₀) :
        (FinProb.pi (fun b : Sother => D.C.trimmed b.1.1)).pr (pinFailure o) ≤ pn := by
      rw [hpinEq o hpos]
      have hcert := D.C.trimmed_pinned_failure k a₀ ha₀ o hkeep
      have hpn : (n : ℝ) ^ (-clockP B / 3) = pn := by
        dsimp [pn]
        congr 1
        ring
      rw [hpn] at hcert
      exact hcert
    have hpinWeightBound (o : Ω a₀) (hpos : 0 < (D.C.trimmed a₀).w o)
        (hkeep : o ∈ D.C.keep a₀) :
        (∑ u ∈ pinFailSet o, ∏ b : Sother, (D.C.trimmed b.1.1).w (u b)) ≤ pn := by
      rw [hpinWeightSum o]
      exact hpinProbabilityBound o hpos hkeep
    let insertedLabels : Finset (Fin g) :=
      Finset.univ.filter fun y => (ins (Sum.inl a₀, y)).isSome
    let insertedEdges : Finset (RowLabel D.Row g) :=
      Finset.univ.filter fun e => (ins e).isSome
    let edgeEmb : Fin g ↪ RowLabel D.Row g := {
      toFun := fun y => (Sum.inl a₀, y)
      inj' := by intro y z h; exact congrArg Prod.snd h }
    have hInsertedSubset : insertedLabels.map edgeEmb ⊆ insertedEdges := by
      intro e he
      rcases Finset.mem_map.mp he with ⟨y, hy, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
    have hInsertedCount : (insertedLabels.card : ℝ) ≤ (insertionSize ins : ℝ) := by
      have hcard : insertedLabels.card ≤ insertedEdges.card := by
        calc
          insertedLabels.card = (insertedLabels.map edgeEmb).card := by simp
          _ ≤ insertedEdges.card := Finset.card_le_card hInsertedSubset
      have hsize : insertedEdges.card = insertionSize ins := by
        simp [insertedEdges, insertionSize]
      exact_mod_cast (hsize ▸ hcard)
    let outMark (y : Fin g) : Option (Ω a₀) :=
      match ins (Sum.inl a₀, y) with
      | some (.tick _ o) => some o
      | _ => none
    let pinTuples (y : Fin g) : Finset (∀ b : Sother, Ω b.1.1) :=
      match outMark y with
      | some o => pinFailSet o
      | none => ∅
    let pinEvent (y : Fin g) (u : ∀ b : Sother, Ω b.1.1) :
        ClockField D.mesh.ticks D.Row g D.Out → Prop := fun ξ =>
      match outMark y with
      | some o => matchesTargetsOrdinarily ins ξ SotherComp (pinOut o u)
      | none => False
    have hpinEventBound (y : Fin g) :
        (∑ u ∈ pinTuples y, D.law.pr (pinEvent y u)) ≤ fac * pn := by
      cases hval : ins (Sum.inl a₀, y) with
      | none =>
          simp [pinTuples, pinEvent, outMark, hval]
          positivity
      | some x =>
          cases x with
          | noArrival =>
              simp [pinTuples, pinEvent, outMark, hval]
              positivity
          | tick t o =>
              have htick : ins (Sum.inl a₀, y) =
                  some (MeshClockValue.tick t o) := hval
              have hpos := htrimPosOfTick y t o htick
              have hkeep := hkeepOfTick y t o htick
              have hmark : outMark y = some o := by simp [outMark, hval]; rfl
              have hset : pinTuples y = pinFailSet o := by simp [pinTuples, hmark]
              have hevent (u : ∀ b : Sother, Ω b.1.1) :
                  pinEvent y u = fun ξ => matchesTargetsOrdinarily ins ξ SotherComp (pinOut o u) := by
                simp [pinEvent, hmark]
              rw [hset]
              calc
                _ ≤ ∑ u ∈ pinFailSet o,
                      fac * ∏ b : Sother, (D.C.trimmed b.1.1).w (u b) := by
                    apply Finset.sum_le_sum
                    intro u hu
                    have hbound := hOrdinaryBound SotherComp (pinOut o u) hotherCard
                    rw [hpinProduct o u] at hbound
                    calc
                      D.law.pr (pinEvent y u) =
                          D.law.pr (fun ξ => matchesTargetsOrdinarily ins ξ SotherComp (pinOut o u)) :=
                            congrArg (fun E => D.law.pr E) (hevent u)
                      _ ≤ fac * ∏ b : Sother, (D.C.trimmed b.1.1).w (u b) := hbound
                _ = fac * ∑ u ∈ pinFailSet o,
                      ∏ b : Sother, (D.C.trimmed b.1.1).w (u b) := by
                    rw [Finset.mul_sum]
                _ ≤ fac * pn := by
                    exact mul_le_mul_of_nonneg_left (hpinWeightBound o hpos hkeep)
                      (by positivity)
    let pinUnion : ClockField D.mesh.ticks D.Row g D.Out → Prop := fun ξ =>
      ∃ y ∈ insertedLabels, ∃ u ∈ pinTuples y, pinEvent y u ξ
    have hpinUnionBound : D.law.pr pinUnion ≤
        (insertionSize ins : ℝ) * fac * pn := by
      calc
        _ ≤ ∑ y ∈ insertedLabels,
              D.law.pr (fun ξ => ∃ u ∈ pinTuples y, pinEvent y u ξ) :=
          finProb_pr_biUnion_le_sum D.law insertedLabels
            (fun y ξ => ∃ u ∈ pinTuples y, pinEvent y u ξ)
        _ ≤ ∑ y ∈ insertedLabels, ∑ u ∈ pinTuples y, D.law.pr (pinEvent y u) := by
          apply Finset.sum_le_sum
          intro y hy
          exact finProb_pr_biUnion_le_sum D.law (pinTuples y) (pinEvent y)
        _ ≤ ∑ _y ∈ insertedLabels, fac * pn := by
          apply Finset.sum_le_sum
          intro y hy
          exact hpinEventBound y
        _ = (insertedLabels.card : ℝ) * (fac * pn) := by simp
        _ ≤ (insertionSize ins : ℝ) * (fac * pn) :=
          mul_le_mul_of_nonneg_right hInsertedCount (by positivity)
        _ = (insertionSize ins : ℝ) * fac * pn := by ring
    have hcoverBoth : ∀ ξ,
        testFails D.failure' D.scope' (greedyMatching (insertArrivals ins ξ)) (.predicate k) →
          (∃ u ∈ failTuples, ordinary u ξ) ∨ pinUnion ξ := by
      intro ξ hbad
      rcases hbad with ⟨ω, hω, hassign⟩
      let realOut : ∀ a : R, Ω a := fun a => ω (Sum.inl a)
      let u : ∀ a : ↥Sreal, Ω a.1 := fun a => realOut a.1
      have hagree : ∀ a ∈ Sreal, lift u a = realOut a := by
        intro a ha
        simp [lift, u, realOut, ha]
        rfl
      have hdep := D.admissible.2.2.1 k (lift u) realOut hagree
      have hfail : failTuple u := by
        dsimp [failTuple]
        exact hdep.mpr (by simpa [realOut, ClockData.failure'] using hω)
      have huMem : u ∈ failTuples := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfail⟩
      let hasInsertedScopeMatch : Prop :=
        ∃ a ∈ Sreal, ∃ y,
          (greedyMatching (insertArrivals ins ξ)).assignment (Sum.inl a) =
            some (y, realOut a) ∧ ins (Sum.inl a, y) ≠ none
      by_cases hordinary : hasInsertedScopeMatch
      · rcases hordinary with ⟨a, ha, y, hassignA, hnotNone⟩
        have hscopeComp : Sum.inl a ∈ Scomp := by
          change Sum.inl a ∈ (D.I.scope k).map Function.Embedding.inl
          exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
        obtain ⟨x, hval⟩ := Option.ne_none_iff_exists'.mp hnotNone
        have hrow := hinsScope (Sum.inl a, y) x hval hscopeComp
        have haa : a = a₀ := Sum.inl.inj hrow
        subst a
        cases hvalue : ins (Sum.inl a₀, y) with
        | none => exact False.elim (hnotNone hvalue)
        | some x =>
            obtain ⟨t, harr⟩ := greedyMatching_assignment_origin
              (insertArrivals ins ξ) (Sum.inl a₀) y (realOut a₀) hassignA
            have hx : x = MeshClockValue.tick t (realOut a₀) := by
              change (ins (Sum.inl a₀, y)).getD (ξ (Sum.inl a₀, y)) =
                MeshClockValue.tick t (realOut a₀) at harr
              rw [hvalue] at harr
              simpa using harr
            have htick : ins (Sum.inl a₀, y) =
                some (MeshClockValue.tick t (realOut a₀)) := by rw [hvalue, hx]; rfl
            have hmark : outMark y = some (realOut a₀) := by
              simp [outMark, htick]
            have hlabelMem : y ∈ insertedLabels := by
              apply Finset.mem_filter.mpr
              constructor
              · exact Finset.mem_univ _
              · simp [insertedLabels, htick]
                rfl
            let otherOut : ∀ b : Sother, Ω b.1.1 := fun b => realOut b.1.1
            have hpinAgree : ∀ a ∈ Sreal, pinReal (realOut a₀) otherOut a = realOut a := by
              intro a ha
              by_cases haa : a = a₀
              · subst a
                have hvalue : pinReal (realOut a₀) otherOut a₀ = realOut a₀ := by
                  simp [pinReal, pinScope, lift, iScope, ha₀,
                    HypercubeRamsey.Lane_q_clock_sampler.pinCoordinateRest]
                exact hvalue
              · let b : Sother := ⟨⟨a, ha⟩, by
                    intro heq
                    exact haa (congrArg Subtype.val heq)⟩
                calc
                  pinReal (realOut a₀) otherOut a =
                      pinReal (realOut a₀) otherOut b.1.1 := by rfl
                  _ = otherOut b := hpinCoord (realOut a₀) otherOut b
                  _ = realOut a := rfl
            have hrealFailure : D.I.failure k realOut := by
              simpa [realOut, ClockData.failure'] using hω
            have hpinFailureHere : pinFailure (realOut a₀) otherOut := by
              have hdepPin := D.admissible.2.2.1 k
                (pinReal (realOut a₀) otherOut) realOut hpinAgree
              exact hdepPin.mpr hrealFailure
            have hpinMem : otherOut ∈ pinTuples y := by
              rw [show pinTuples y = pinFailSet (realOut a₀) by simp [pinTuples, hmark]]
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpinFailureHere⟩
            have hordinaryOther :
                matchesTargetsOrdinarily ins ξ SotherComp
                  (pinOut (realOut a₀) otherOut) := by
              intro r hr
              rcases Finset.mem_map.mp hr with ⟨b, hb, rfl⟩
              let a : R := b.1.1
              have ha : a ∈ Sreal := b.1.2
              rcases hassign (Sum.inl a) (by
                change Sum.inl a ∈ (D.I.scope k).map Function.Embedding.inl
                exact Finset.mem_map.mpr ⟨a, ha, rfl⟩) with ⟨y', hy'⟩
              have hnone : ins (Sum.inl a, y') = none := by
                cases hyIns : ins (Sum.inl a, y') with
                | none => rfl
                | some x' =>
                    have hsc : Sum.inl a ∈ Scomp := by
                      change Sum.inl a ∈ (D.I.scope k).map Function.Embedding.inl
                      exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
                    have hrow' := hinsScope (Sum.inl a, y') x' hyIns hsc
                    have hEqA : a = a₀ := Sum.inl.inj hrow'
                    have hneA : a ≠ a₀ := by
                      intro heq
                      have heqSubtype : b.1 = iScope := by
                        apply Subtype.ext
                        exact heq
                      exact b.2 heqSubtype
                    exact False.elim (hneA hEqA)
              have hout : pinOut (realOut a₀) otherOut (embOther b) = realOut a := by
                change pinReal (realOut a₀) otherOut a = realOut a
                calc
                  pinReal (realOut a₀) otherOut a = pinReal (realOut a₀) otherOut b.1.1 := by rfl
                  _ = otherOut b := hpinCoord (realOut a₀) otherOut b
                  _ = realOut a := rfl
              refine ⟨y', ?_, hnone⟩
              rw [hout]
              exact hy'
            refine Or.inr ?_
            refine ⟨y, hlabelMem, otherOut, hpinMem, ?_⟩
            simpa [pinEvent, hmark] using hordinaryOther
      · exact Or.inl ⟨u, huMem, by
          intro r hr
          rcases Finset.mem_map.mp hr with ⟨a, ha, rfl⟩
          have hscopeComp : Sum.inl a ∈ Scomp := by
            change Sum.inl a ∈ (D.I.scope k).map Function.Embedding.inl
            exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
          rcases hassign (Sum.inl a) hscopeComp with ⟨y, hy⟩
          have hnone : ins (Sum.inl a, y) = none := by
            by_contra h
            exact hordinary ⟨a, ha, y, hy, h⟩
          refine ⟨y, ?_, hnone⟩
          have hout : outTuple u (Sum.inl a) = realOut a := by
            change lift u a = realOut a
            exact hagree a ha
          have hout' : outTuple u (Function.Embedding.inl a) = realOut a := by
            change outTuple u (Sum.inl a) = realOut a
            exact hout
          rw [hout']
          exact hy⟩
    have hbadPr : D.law.pr
        (fun ξ => testFails D.failure' D.scope' (greedyMatching (insertArrivals ins ξ)) (.predicate k)) ≤
          D.law.pr (fun ξ => (∃ u ∈ failTuples, ordinary u ξ) ∨ pinUnion ξ) := by
      apply finProb_pr_mono D.law
      intro ξ hξ
      exact hcoverBoth ξ hξ
    calc
      _ ≤ D.law.pr (fun ξ => (∃ u ∈ failTuples, ordinary u ξ) ∨ pinUnion ξ) := hbadPr
      _ ≤ D.law.pr (fun ξ => ∃ u ∈ failTuples, ordinary u ξ) + D.law.pr pinUnion :=
        FinProb.pr_union D.law _ _
      _ ≤ fac * pn + (insertionSize ins : ℝ) * fac * pn :=
        add_le_add hordinaryUnion hpinUnionBound
      _ = ((insertionSize ins : ℝ) + 1) * fac * pn := by ring
  · -- no inserted edge can match a row in the predicate scope
    have hnoInsScope : ∀ a ∈ Sreal, ∀ y, ins (Sum.inl a, y) = none := by
      intro a ha y
      cases hval : ins (Sum.inl a, y) with
      | none => rfl
      | some x =>
          have hscopeComp : Sum.inl a ∈ Scomp := by
            change Sum.inl a ∈ (D.I.scope k).map Function.Embedding.inl
            exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
          have hrow := hinsScope (Sum.inl a, y) x hval hscopeComp
          have haa : a = a₀ := Sum.inl.inj hrow
          exact False.elim (ha₀ (haa ▸ ha))
    have hcover : ∀ ξ,
        testFails D.failure' D.scope' (greedyMatching (insertArrivals ins ξ)) (.predicate k) →
          ∃ u ∈ failTuples, ordinary u ξ := by
      intro ξ hbad
      rcases hbad with ⟨ω, hω, hassign⟩
      let u : ∀ a : ↥Sreal, Ω a.1 := fun a => ω (Sum.inl a.1)
      have hagree : ∀ a ∈ Sreal, lift u a = ω (Sum.inl a) := by
        intro a ha
        simp [lift, u, ha]
        rfl
      have hdep := D.admissible.2.2.1 k (lift u) (fun a => ω (Sum.inl a)) hagree
      have hfail : failTuple u := by
        dsimp [failTuple]
        exact hdep.mpr (by simpa [ClockData.failure'] using hω)
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfail⟩, ?_⟩
      intro r hr
      rcases Finset.mem_map.mp hr with ⟨a, ha, rfl⟩
      have hscopeComp : Sum.inl a ∈ Scomp := by
        change Sum.inl a ∈ (D.I.scope k).map Function.Embedding.inl
        exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
      rcases hassign (Sum.inl a) hscopeComp with ⟨y, hy⟩
      refine ⟨y, ?_, hnoInsScope a ha y⟩
      have hout : outTuple u (Sum.inl a) = ω (Sum.inl a) := by
        change lift u a = ω (Sum.inl a)
        exact hagree a ha
      have hout' : outTuple u (Function.Embedding.inl a) = ω (Sum.inl a) := by
        change outTuple u (Sum.inl a) = ω (Sum.inl a)
        exact hout
      rw [hout']
      exact hy
    calc
      D.law.pr (fun ξ => testFails D.failure' D.scope'
          (greedyMatching (insertArrivals ins ξ)) (.predicate k)) ≤
          D.law.pr (fun ξ => ∃ u ∈ failTuples, ordinary u ξ) :=
        finProb_pr_mono D.law (by intro ξ hξ; exact hcover ξ hξ)
      _ ≤ fac * pn := hordinaryUnion
      _ ≤ ((insertionSize ins : ℝ) + 1) * fac * pn := by
        have hcast : 0 ≤ (insertionSize ins : ℝ) := Nat.cast_nonneg _
        have hsize : 1 ≤ (insertionSize ins : ℝ) + 1 := by linarith
        have hfacpn : 0 ≤ fac * pn := by positivity
        calc
          fac * pn = 1 * (fac * pn) := by ring
          _ ≤ ((insertionSize ins : ℝ) + 1) * (fac * pn) :=
            mul_le_mul_of_nonneg_right hsize hfacpn
          _ = ((insertionSize ins : ℝ) + 1) * fac * pn := by ring

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
  classical
  let kconst : ℝ := clockK₀ B
  have hkpos : 0 < clockK₀ B := by unfold clockK₀; linarith [hB]
  have hA : 10 * (B + clockK₀ B) < clockA B - 1 := by
    unfold clockA
    nlinarith
  obtain ⟨n₁, hgiant⟩ := clock_giant_tail B hB
  obtain ⟨n₂, hpred⟩ := predicate_failure_under_insertion B C_g hB
  obtain ⟨n₃, hunmatched⟩ := step7_unmatched_singleton B (clockA B - 1) C_g
    (clockK₀ B) hB hkpos hA
  refine ⟨max n₁ (max n₂ (max n₃ 2)), ?_⟩
  intro n hn g hg R K _ _ _ Ω _ _ _ D t r hr v j hj π hπ havoid hweight
  let fac : ℝ := 1 + (n : ℝ)⁻¹
  let pn : ℝ := (n : ℝ) ^ (-(clockP B / 3))
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hnOuter : max n₂ (max n₃ 2) ≤ n := le_trans (le_max_right _ _) hn
  have hnInner : max n₃ 2 ≤ n := le_trans (le_max_right _ _) hnOuter
  have hn₃ : n₃ ≤ n := le_trans (le_max_left _ _) hnInner
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hnInner
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hA20 : 20 ≤ clockA B := by unfold clockA clockK₀; linarith [hB]
  have hpow20 : (10 : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (20 : ℝ) := by norm_num
      _ ≤ (n : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow (by norm_num) hnreal (by norm_num)
  have hpowA : (n : ℝ) ^ (20 : ℝ) ≤ (n : ℝ) ^ clockA B :=
    Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hnreal) hA20
  have hgnum : (10 : ℝ) ^ 6 ≤ g :=
    le_trans (le_trans hpow20 hpowA) (D.card_labels_ge (by omega))
  have htheta := D.completed_theta_bounds hgnum
  have hthetaAtom := D.completed_atom_le hn2
  let roots : Finset (Endpoint D.Row g) := testRootEndpoints (g := g) D.scope' (D.test' t)
  have hrootsSource :
      ((testRootEndpoints (g := g) D.scope' (D.test' t)).card : ℝ) ≤ (n : ℝ) ^ B := by
    cases t with
    | predicate k =>
        change ((testRootEndpoints (g := g) D.scope' (.predicate k)).card : ℝ) ≤
          (n : ℝ) ^ B
        calc
          ((testRootEndpoints (g := g) D.scope' (.predicate k)).card : ℝ) ≤
              ((D.scope' k).card : ℝ) := by exact_mod_cast (Finset.card_image_le)
          _ = ((D.I.scope k).card : ℝ) := by simp [ClockData.scope']
          _ ≤ (n : ℝ) ^ B := D.admissible.2.2.2.1 k
    | singleton a =>
        have hpow : (1 : ℝ) ≤ (n : ℝ) ^ B := by
          calc
            1 = (n : ℝ) ^ (0 : ℝ) := by simp
            _ ≤ (n : ℝ) ^ B :=
              Real.rpow_le_rpow_of_exponent_le (by linarith [hnreal]) (by linarith [hB])
        have hcard : (testRootEndpoints (g := g) D.scope' (.singleton (Sum.inl a))).card ≤ 1 := by
          simpa [testRootEndpoints, testRoots, ClockData.test'] using
            (Finset.card_image_le (s := ({Sum.inl a} : Finset D.Row)) (f := Sum.inl))
        have hcardReal : ((testRootEndpoints (g := g) D.scope' (.singleton (Sum.inl a))).card : ℝ) ≤ 1 :=
          by exact_mod_cast hcard
        exact hcardReal.trans hpow
  have hroots : (roots.card : ℝ) ≤ (n : ℝ) ^ B := by simpa [roots] using hrootsSource
  have hJupper : (clockJ B n : ℝ) ≤ kconst ^ 2 * Real.log (n : ℝ) := by
    change (Nat.floor (kconst ^ 2 * Real.log (n : ℝ)) : ℝ) ≤ _
    exact Nat.floor_le (by positivity)
  have hpathSizeNat := insertionSize_pathInsertion_le
    (Sum.inl (Sum.inl r)) v π hπ
  have hpathSizeReal : (insertionSize (pathInsertion π) : ℝ) ≤ j := by exact_mod_cast hpathSizeNat
  have hjReal : (j : ℝ) ≤ (clockJ B n : ℝ) := by exact_mod_cast hj
  have hInsSize : (insertionSize (pathInsertion π) : ℝ) ≤
      (kconst + 1) ^ 2 * Real.log (n : ℝ) := by
    calc
      (insertionSize (pathInsertion π) : ℝ) ≤ j := hpathSizeReal
      _ ≤ clockJ B n := hjReal
      _ ≤ kconst ^ 2 * Real.log (n : ℝ) := hJupper
      _ ≤ (kconst + 1) ^ 2 * Real.log (n : ℝ) := by
        gcongr
        dsimp [kconst, clockK₀]
        nlinarith [hB]
  have hInsPos : ∀ e x, pathInsertion π e = some x → 0 < (D.edgeLaw e).w x := by
    intro e x hx
    exact HypercubeRamsey.Lane_q_clock_sampler.pathInsertion_value_pos
      D.edgeLaw π hweight e x hx
  have hinvalidRaw : D.law.pr
      (fun ξ => ∃ e t o, ξ e = MeshClockValue.tick t o ∧ D.lab' e.1 o ≠ e.2) = 0 := by
    simpa [ClockData.law, ClockData.edgeLaw] using
      (invalid_marks_null D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one D.law' D.lab')
  let invalidInserted : ClockField D.mesh.ticks D.Row g D.Out → Prop := fun ξ =>
    ∃ e t o, (insertArrivals (pathInsertion π) ξ) e = MeshClockValue.tick t o ∧
      D.lab' e.1 o ≠ e.2
  have hinvalidInsertedSubset : ∀ ξ, invalidInserted ξ →
      ∃ e t o, ξ e = MeshClockValue.tick t o ∧ D.lab' e.1 o ≠ e.2 := by
    intro ξ hbad
    rcases hbad with ⟨e, t, o, hfield, hlabel⟩
    by_cases hnone : pathInsertion π e = none
    · refine ⟨e, t, o, ?_, hlabel⟩
      simpa [insertArrivals, hnone] using hfield
    · obtain ⟨x, hsome⟩ := Option.ne_none_iff_exists'.mp hnone
      have hx : x = MeshClockValue.tick t o := by
        simpa [insertArrivals, hsome] using hfield
      have hpositive := hInsPos e x hsome
      have hvalid : D.lab' e.1 o = e.2 := by
        by_contra hne
        have hzero : (D.edgeLaw e).w (MeshClockValue.tick t o) = 0 := by
          simp [ClockData.edgeLaw, samplingEdgeClockLaw, outputEdgeClockLaw,
            markedClockLaw, markedClockWeight, outputMarkMass, hne]
        rw [hx, hzero] at hpositive
        norm_num at hpositive
      exact False.elim (hlabel hvalid)
  have hinvalidInsertedProb : D.law.pr invalidInserted = 0 := by
    apply le_antisymm
    · calc
        _ ≤ D.law.pr
            (fun ξ => ∃ e t o, ξ e = MeshClockValue.tick t o ∧ D.lab' e.1 o ≠ e.2) :=
              finProb_pr_mono D.law hinvalidInsertedSubset
        _ = 0 := hinvalidRaw
    · exact finProb_pr_nonneg D.law _
  have hactiveEq (ξ : ClockField D.mesh.ticks D.Row g D.Out) :
      activeEndpoints ξ D.scope' (D.test' t) = closureFrom ξ roots := by
    exact activeEndpoints_eq_closureFrom ξ D.scope' (D.test' t)
  have hgiantClosure : D.law.pr
      (fun ξ => clockLnat B n ≤ (closureFrom (insertArrivals (pathInsertion π) ξ) roots).card) ≤
      (n : ℝ) ^ (-(2 * kconst)) := by
    have h := hgiant n hn₁ D roots hroots (pathInsertion π) hInsSize
    simpa [kconst] using h
  have hgiantActive : D.law.pr
      (fun ξ => clockLnat B n ≤ (activeEndpoints (insertArrivals (pathInsertion π) ξ)
        D.scope' (D.test' t)).card) ≤ (n : ℝ) ^ (-(2 * kconst)) := by
    calc
      _ = D.law.pr (fun ξ => clockLnat B n ≤
          (closureFrom (insertArrivals (pathInsertion π) ξ) roots).card) := by
            apply HypercubeRamsey.Lane_q_clock_sampler.finProb_pr_congr
            intro ξ
            rw [hactiveEq]
      _ ≤ (n : ℝ) ^ (-(2 * kconst)) := hgiantClosure
  have hUnmatchedAt := hunmatched n hn₃ D.mesh D.mesh.δ_nonneg D.mesh.δ_le_one
    D.law' D.lab' D.C.theta hg
    (fun y => D.completed_columns_eq y) htheta.2 (fun a y => hthetaAtom a y)
    (pathInsertion π) hInsSize (Sum.inl r)
  cases t with
  | predicate k' =>
      have hrootscope : r ∈ D.I.scope k' := by simpa [testRoots] using hr
      have hscopeIns : ∀ e x, pathInsertion π e = some x → e.1 ∈ D.scope' k' →
          e.1 = Sum.inl r := by
        intro e x hins hmem
        rcases HypercubeRamsey.Lane_q_clock_sampler.pathInsertion_row_origin π e x hins with
          ⟨i, hrow⟩
        have hiScope : (π i).1 ∈ D.scope' k' := by rw [hrow]; exact hmem
        have hnotOther := havoid k' rfl
        by_contra hne
        exact hnotOther ⟨i, hiScope, by
          intro heq
          exact hne (hrow.symm.trans heq)⟩
      have hpredBound := hpred n hn₂ g hg D k' r (pathInsertion π)
        hInsSize hInsPos hscopeIns
      have hpredBound' : D.law.pr
          (fun ξ => testFails D.failure' D.scope' (greedyMatching (insertArrivals (pathInsertion π) ξ))
            (.predicate k')) ≤
          ((insertionSize (pathInsertion π) : ℝ) + 1) * fac * pn := by
        simpa [fac, pn] using hpredBound
      have hpredicateEvent : ∀ ξ,
          closureBad D.lab' D.failure' D.scope' (clockLnat B n)
            (insertArrivals (pathInsertion π) ξ) (.predicate k') ↔
              (clockLnat B n ≤ (activeEndpoints (insertArrivals (pathInsertion π) ξ)
                D.scope' (.predicate k')).card) ∨
                testFails D.failure' D.scope' (greedyMatching (insertArrivals (pathInsertion π) ξ))
                  (.predicate k') := by
        intro ξ
        simp [closureBad, sampleTestBad]
      have hbound : D.law.pr
          (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n)
            (insertArrivals (pathInsertion π) ξ) (.predicate k')) ≤
          (n : ℝ) ^ (-(2 * kconst)) +
            ((insertionSize (pathInsertion π) : ℝ) + 1) * fac * pn := by
        calc
          _ ≤ D.law.pr (fun ξ => (clockLnat B n ≤
                (activeEndpoints (insertArrivals (pathInsertion π) ξ)
                  D.scope' (.predicate k')).card) ∨
                testFails D.failure' D.scope' (greedyMatching (insertArrivals (pathInsertion π) ξ))
                  (.predicate k')) :=
              finProb_pr_mono D.law (by intro ξ hξ; exact (hpredicateEvent ξ).mp hξ)
          _ ≤ D.law.pr (fun ξ => clockLnat B n ≤
                (activeEndpoints (insertArrivals (pathInsertion π) ξ)
                  D.scope' (.predicate k')).card) +
              D.law.pr (fun ξ => testFails D.failure' D.scope'
                (greedyMatching (insertArrivals (pathInsertion π) ξ)) (.predicate k')) :=
              FinProb.pr_union D.law _ _
          _ ≤ (n : ℝ) ^ (-(2 * kconst)) +
              ((insertionSize (pathInsertion π) : ℝ) + 1) * fac * pn :=
              add_le_add hgiantActive hpredBound'
      have hsizeplus : (insertionSize (pathInsertion π) : ℝ) + 1 ≤
          (clockJ B n : ℝ) + 1 := by linarith [hInsSize, hjReal]
      have hshort : (n : ℝ) ^ (-(2 * kconst)) +
          ((insertionSize (pathInsertion π) : ℝ) + 1) * fac * pn ≤ clockShortBound B n := by
        unfold clockShortBound
        dsimp [fac, pn]
        have hterm : ((insertionSize (pathInsertion π) : ℝ) + 1) *
            (1 + (n : ℝ)⁻¹) * (n : ℝ) ^ (-(clockP B / 3)) ≤
          ((clockJ B n : ℝ) + 1) * (1 + (n : ℝ)⁻¹) * (n : ℝ) ^ (-(clockP B / 3)) := by
          have hbase : 0 ≤ (1 + (n : ℝ)⁻¹) * (n : ℝ) ^ (-(clockP B / 3)) := by positivity
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hsizeplus hbase
        have hunmatchedNonneg : 0 ≤ 2 * (n : ℝ) ^ (-(99 / 100 * kconst)) := by positivity
        nlinarith [hterm, hunmatchedNonneg]
      calc
        _ = D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n)
            (insertArrivals (pathInsertion π) ξ) (.predicate k')) := rfl
        _ ≤ (n : ℝ) ^ (-(2 * kconst)) +
              ((insertionSize (pathInsertion π) : ℝ) + 1) * fac * pn := hbound
        _ ≤ clockShortBound B n := hshort
  | singleton a =>
      have hrSingle : r ∈ ({a} : Finset R) := by change r ∈ testRoots D.I.scope (.singleton a) at hr; simpa [testRoots] using hr
      have hra : a = r := (Finset.mem_singleton.mp hrSingle).symm
      subst a
      have hbadSingleton : ∀ ξ,
          sampleTestBad D.lab' D.failure' D.scope' (greedyMatching (insertArrivals (pathInsertion π) ξ))
            (.singleton (Sum.inl r)) →
            ((greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) = none) ∨
              invalidInserted ξ := by
        intro ξ hbad
        by_cases hnone :
            (greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) = none
        · exact Or.inl hnone
        · right
          cases hstate : (greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) with
          | none => exact False.elim (hnone hstate)
          | some pair =>
              rcases pair with ⟨y, o⟩
              have hwrong : D.lab' (Sum.inl r) o ≠ y := by
                intro heq
                exact hbad ⟨y, o, hstate, heq⟩
              obtain ⟨τ, harr⟩ := greedyMatching_assignment_origin
                (insertArrivals (pathInsertion π) ξ) (Sum.inl r) y o hstate
              by_cases hnoneIns : pathInsertion π (Sum.inl r, y) = none
              · refine ⟨(Sum.inl r, y), τ, o, ?_, hwrong⟩
                simpa [insertArrivals, hnoneIns] using harr
              · obtain ⟨x, hxIns⟩ := Option.ne_none_iff_exists'.mp hnoneIns
                have hx : x = MeshClockValue.tick τ o := by
                  simpa [insertArrivals, hxIns] using harr
                have hpositive := hInsPos (Sum.inl r, y) x hxIns
                have hvalid : D.lab' (Sum.inl r) o = y := by
                  by_contra hneq
                  have hzero : (D.edgeLaw (Sum.inl r, y)).w (MeshClockValue.tick τ o) = 0 := by
                    simp [ClockData.edgeLaw, samplingEdgeClockLaw, outputEdgeClockLaw,
                      markedClockLaw, markedClockWeight, outputMarkMass, hneq]
                  rw [hx, hzero] at hpositive
                  norm_num at hpositive
                exact False.elim (hwrong hvalid)
      have hunmatchedBound : D.law.pr
          (fun ξ => (greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) = none) ≤
          2 * (n : ℝ) ^ (-((1 - D.C.theta) * kconst)) := by
        simpa [ClockData.law, ClockData.edgeLaw] using hUnmatchedAt
      have hthetaSmall : D.C.theta ≤ 1 / 100 := by norm_num at htheta ⊢; linarith
      have hExp : -((1 - D.C.theta) * kconst) ≤ -(99 / 100 * kconst) := by
        nlinarith [hthetaSmall, hkpos]
      have hpowUnmatched : (n : ℝ) ^ (-((1 - D.C.theta) * kconst)) ≤
          (n : ℝ) ^ (-(99 / 100 * kconst)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hnreal]) hExp
      have hOutcome : D.law.pr
          (fun ξ => sampleTestBad D.lab' D.failure' D.scope'
            (greedyMatching (insertArrivals (pathInsertion π) ξ)) (.singleton (Sum.inl r))) ≤
          2 * (n : ℝ) ^ (-(99 / 100 * kconst)) := by
        calc
          _ ≤ D.law.pr (fun ξ =>
              ((greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) = none) ∨
                invalidInserted ξ) := finProb_pr_mono D.law (by intro ξ hξ; exact hbadSingleton ξ hξ)
          _ ≤ D.law.pr (fun ξ =>
              (greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) = none) +
                D.law.pr invalidInserted := FinProb.pr_union D.law _ _
          _ = D.law.pr (fun ξ =>
              (greedyMatching (insertArrivals (pathInsertion π) ξ)).assignment (Sum.inl r) = none) := by
                rw [hinvalidInsertedProb]
                ring
          _ ≤ 2 * (n : ℝ) ^ (-(99 / 100 * kconst)) :=
                calc
                  _ ≤ (2 : ℝ) * (n : ℝ) ^ (-((1 - D.C.theta) * kconst)) := hunmatchedBound
                  _ ≤ (2 : ℝ) * (n : ℝ) ^ (-(99 / 100 * kconst)) :=
                    mul_le_mul_of_nonneg_left hpowUnmatched (by norm_num)
      have hbound : D.law.pr
          (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n)
            (insertArrivals (pathInsertion π) ξ) (.singleton (Sum.inl r))) ≤
          (n : ℝ) ^ (-(2 * kconst)) + 2 * (n : ℝ) ^ (-(99 / 100 * kconst)) := by
        have hgiant' : D.law.pr
            (fun ξ => clockLnat B n ≤ (activeEndpoints (insertArrivals (pathInsertion π) ξ)
              D.scope' (.singleton (Sum.inl r))).card) ≤ (n : ℝ) ^ (-(2 * kconst)) := hgiantActive
        calc
          _ ≤ D.law.pr (fun ξ =>
              (clockLnat B n ≤ (activeEndpoints (insertArrivals (pathInsertion π) ξ)
                D.scope' (.singleton (Sum.inl r))).card) ∨
                sampleTestBad D.lab' D.failure' D.scope'
                  (greedyMatching (insertArrivals (pathInsertion π) ξ)) (.singleton (Sum.inl r))) :=
              finProb_pr_mono D.law (by intro ξ hξ; simpa [closureBad] using hξ)
          _ ≤ D.law.pr (fun ξ => clockLnat B n ≤
                (activeEndpoints (insertArrivals (pathInsertion π) ξ)
                  D.scope' (.singleton (Sum.inl r))).card) +
              D.law.pr (fun ξ => sampleTestBad D.lab' D.failure' D.scope'
                (greedyMatching (insertArrivals (pathInsertion π) ξ)) (.singleton (Sum.inl r))) :=
              FinProb.pr_union D.law _ _
          _ ≤ (n : ℝ) ^ (-(2 * kconst)) + 2 * (n : ℝ) ^ (-(99 / 100 * kconst)) :=
              add_le_add hgiant' hOutcome
      have hshort :
          (n : ℝ) ^ (-(2 * kconst)) + 2 * (n : ℝ) ^ (-(99 / 100 * kconst)) ≤
            clockShortBound B n := by
        have hthird : 0 ≤ ((clockJ B n : ℝ) + 1) * (1 + (n : ℝ)⁻¹) *
            (n : ℝ) ^ (-(clockP B / 3)) := by positivity
        unfold clockShortBound
        nlinarith [hthird]
      calc
        _ ≤ (n : ℝ) ^ (-(2 * kconst)) + 2 * (n : ℝ) ^ (-(99 / 100 * kconst)) := hbound
        _ ≤ clockShortBound B n := hshort

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
  classical
  let K := clockK₀ B
  let d₁ := B + K / 250 - 2 * K + 3 * K / 5
  let d₂ := B + K / 250 - 99 * K / 100 + 3 * K / 5
  let d₃ := B + K / 250 + 1 - clockP B / 3 + 3 * K / 5
  let d₄ := 2 * B - (clockA B - 1) + K / 250 + 2 + 3 * K / 5
  let d₅ := B - K ^ 2 + 3 * K / 5
  let C₁ := 4000 * Real.exp (1 / 250) * (K ^ 2 + 1)
  let C₂ := 1000000000 * Real.exp (1 / 250) * K ^ 4
  let C₃ := 2 * Real.exp 1
  have hKform : K = 20 * B + 20 := by simp [K, clockK₀]
  have hBeq : B = K / 20 - 1 := by rw [hKform]; ring
  have hK : 40 ≤ K := by rw [hKform]; linarith
  have hKpos : 0 < K := by linarith
  have hd₁ : d₁ < 0 := by dsimp [d₁]; rw [hBeq]; nlinarith [hK]
  have hd₂ : d₂ < 0 := by dsimp [d₂]; rw [hBeq]; nlinarith [hK]
  have hd₃ : d₃ < 0 := by dsimp [d₃, clockP, clockK₀]; nlinarith [hB]
  have hd₄ : d₄ < 0 := by dsimp [d₄, clockA, clockK₀]; nlinarith [hB]
  have hd₅ : d₅ < 0 := by dsimp [d₅]; nlinarith [hK, hBeq]
  have hC₁ : 0 < C₁ := by positivity
  have hC₂ : 0 < C₂ := by positivity
  have hC₃ : 0 < C₃ := by positivity
  have rpowNegTendsto (d : ℝ) (hd : d < 0) :
      Tendsto (fun n : ℕ => (n : ℝ) ^ d) atTop (nhds 0) := by
    have hp : 0 < -d := neg_pos.mpr hd
    have h := (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(-d))) atTop (nhds 0) :=
      h.congr (fun _ => rfl)
    have heq : ∀ n : ℕ, (n : ℝ) ^ (-(-d)) = (n : ℝ) ^ d := by
      intro n
      congr 1
      ring
    exact h'.congr heq
  have hNlim : Tendsto (fun n : ℕ =>
      C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
        C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅) atTop (nhds 0) := by
    have h₁ := (rpowNegTendsto d₁ hd₁).const_mul C₁
    have h₂ := (rpowNegTendsto d₂ hd₂).const_mul C₁
    have h₃ := (rpowNegTendsto d₃ hd₃).const_mul C₁
    have h₄ := (rpowNegTendsto d₄ hd₄).const_mul C₂
    have h₅ := (rpowNegTendsto d₅ hd₅).const_mul C₃
    simpa [mul_comm, add_assoc] using (((h₁.add h₂).add h₃).add h₄).add h₅
  have hNsmall : ∀ᶠ n : ℕ in atTop,
      C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
        C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅ < 1 :=
    (tendsto_order.1 hNlim).2 1 (by norm_num)
  rcases Filter.eventually_atTop.1 hNsmall with ⟨n₁, hn₁⟩
  refine ⟨max n₁ 3, ?_⟩
  intro n hn θ hθlo hθhi
  have hn₁' : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : 2 ≤ n := le_trans (by norm_num) hn3
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have hlog1 : 1 ≤ Real.log n := by
    calc 1 ≤ Real.log 3 := le_of_lt hlog3
      _ ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
  have hsqrt0 : 0 ≤ Real.sqrt θ := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt θ) ^ 2 = θ := Real.sq_sqrt (by linarith : 0 ≤ θ)
  have hsqrtLo : 1 / 1000 ≤ Real.sqrt θ := by nlinarith [hsqrtSq]
  have hsqrtHi : Real.sqrt θ ≤ 1 / 500 := by nlinarith [hsqrtSq]
  have hinvSqrt : (Real.sqrt θ)⁻¹ ≤ 1000 := by
    have hs : 1 ≤ 1000 * Real.sqrt θ := by nlinarith [hsqrtLo]
    have hdiv : 1 / Real.sqrt θ ≤ 1000 :=
      (div_le_iff₀ (by linarith : 0 < Real.sqrt θ)).2 (by nlinarith [hs])
    simpa [one_div] using hdiv
  have hinvTheta : θ⁻¹ ≤ 1000000 := by
    have hs : 1 ≤ 1000000 * θ := by nlinarith [hθlo]
    have hdiv : 1 / θ ≤ 1000000 :=
      (div_le_iff₀ (by linarith : 0 < θ)).2 (by nlinarith [hs])
    simpa [one_div] using hdiv
  have hpowBge : 1 ≤ (n : ℝ) ^ B := by
    calc
      1 = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ B := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hNB : (n : ℝ) ^ B + 1 ≤ 2 * (n : ℝ) ^ B := by nlinarith [hpowBge]
  have hInvN : 1 + (n : ℝ)⁻¹ ≤ 2 := by
    have hInv : (n : ℝ)⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ (by linarith)
    linarith
  have hJupper : (clockJ B n : ℝ) ≤ K ^ 2 * Real.log n := by
    change (Nat.floor (K ^ 2 * Real.log n) : ℝ) ≤ _
    exact Nat.floor_le (by positivity)
  have hJupper' : (clockJ B n : ℝ) ≤ K ^ 2 * n := by
    calc
      (clockJ B n : ℝ) ≤ K ^ 2 * Real.log n := hJupper
      _ ≤ K ^ 2 * n := mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity)) (by positivity)
  have hJlower : K ^ 2 * Real.log n - 1 < (clockJ B n : ℝ) := by
    have h := Nat.lt_floor_add_one (K ^ 2 * Real.log n)
    change K ^ 2 * Real.log n < (clockJ B n : ℝ) + 1 at h
    linarith
  have hExp2 : Real.exp 2 ≤ 9 := by
    have he := Real.exp_one_lt_three
    have he' := mul_lt_mul_of_pos_left he (Real.exp_pos 1)
    have he'' := mul_lt_mul_of_pos_right he (by norm_num : (0 : ℝ) < 3)
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [heq]
    linarith
  have hJnumeric : Real.exp 2 * (K * Real.log n + 2) ≤ (clockJ B n : ℝ) := by
    have hKgap : 1240 ≤ K ^ 2 - 9 * K := by nlinarith [sq_nonneg (K - 40), hK]
    have hgap : 19 ≤ (K ^ 2 - 9 * K) * Real.log n := by
      calc
        19 ≤ 1240 := by norm_num
        _ ≤ 1240 * Real.log n := by nlinarith [hlog1]
        _ ≤ (K ^ 2 - 9 * K) * Real.log n :=
          mul_le_mul_of_nonneg_right hKgap hlog0
    have hKx : 9 * (K * Real.log n + 2) ≤ K ^ 2 * Real.log n - 1 := by nlinarith [hgap]
    calc
      Real.exp 2 * (K * Real.log n + 2) ≤ 9 * (K * Real.log n + 2) :=
        mul_le_mul_of_nonneg_right hExp2 (by positivity)
      _ ≤ K ^ 2 * Real.log n - 1 := hKx
      _ ≤ (clockJ B n : ℝ) := le_of_lt hJlower
  have hExpFactor :
      Real.exp (Real.sqrt θ * (K * Real.log n + 2)) ≤
        Real.exp (1 / 250) * (n : ℝ) ^ (K / 250) := by
    have harg : Real.sqrt θ * (K * Real.log n + 2) ≤ K / 250 * Real.log n + 1 / 250 := by
      have hKx : 0 ≤ K * Real.log n + 2 := by positivity
      calc
        Real.sqrt θ * (K * Real.log n + 2) ≤ (1 / 500) * (K * Real.log n + 2) :=
          mul_le_mul_of_nonneg_right hsqrtHi hKx
        _ = K / 500 * Real.log n + 1 / 250 := by ring
        _ ≤ K / 250 * Real.log n + 1 / 250 := by
          gcongr
          norm_num
    calc
      Real.exp (Real.sqrt θ * (K * Real.log n + 2)) ≤
          Real.exp (K / 250 * Real.log n + 1 / 250) := Real.exp_le_exp.mpr harg
      _ = Real.exp (1 / 250) * (n : ℝ) ^ (K / 250) := by
        rw [Real.exp_add]
        have hp : Real.exp (K / 250 * Real.log n) = (n : ℝ) ^ (K / 250) := by
          rw [Real.rpow_def_of_pos hnpos]
          congr 1
          ring
        rw [hp]
        ring
  have hQ :
      Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ ≤
        1000 * Real.exp (1 / 250) * (n : ℝ) ^ (K / 250) := by
    calc
      _ = Real.exp (Real.sqrt θ * (K * Real.log n + 2)) * (Real.sqrt θ)⁻¹ := by ring
      _ ≤ (Real.exp (1 / 250) * (n : ℝ) ^ (K / 250)) * 1000 :=
        mul_le_mul hExpFactor hinvSqrt (by positivity) (by positivity)
      _ = 1000 * Real.exp (1 / 250) * (n : ℝ) ^ (K / 250) := by ring
  have hJplus : (clockJ B n : ℝ) + 1 ≤ (K ^ 2 + 1) * n := by
    calc
      (clockJ B n : ℝ) + 1 ≤ K ^ 2 * n + 1 := by linarith [hJupper']
      _ ≤ (K ^ 2 + 1) * n := by nlinarith [hKpos, hnR]
  have hJsq : (clockJ B n : ℝ) ^ 2 ≤ K ^ 4 * n ^ 2 := by
    have hnonneg : 0 ≤ (clockJ B n : ℝ) := Nat.cast_nonneg _
    have hupperProd := mul_le_mul_of_nonneg_right hJupper' hnonneg
    have hupperProd' := mul_le_mul_of_nonneg_left hJupper' (by positivity : 0 ≤ K ^ 2 * n)
    nlinarith [hupperProd, hupperProd']
  have hpowMul (a b : ℝ) :
      (n : ℝ) ^ a * (n : ℝ) ^ b = (n : ℝ) ^ (a + b) :=
    (Real.rpow_add hnpos a b).symm
  have hpowThree (a b c : ℝ) :
      (n : ℝ) ^ a * (n : ℝ) ^ b * (n : ℝ) ^ c = (n : ℝ) ^ (a + b + c) := by
    rw [hpowMul a b, hpowMul (a + b) c]
  have htermOne :
      ((n : ℝ) ^ B + 1) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) *
          clockShortBound B n ≤
        C₁ * ((n : ℝ) ^ (d₁ - 3 * K / 5) + (n : ℝ) ^ (d₂ - 3 * K / 5) +
          (n : ℝ) ^ (d₃ - 3 * K / 5)) := by
    have hF :
        ((n : ℝ) ^ B + 1) *
            (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) ≤
          2000 * Real.exp (1 / 250) * (n : ℝ) ^ (B + K / 250) := by
      calc
        _ ≤ (2 * (n : ℝ) ^ B) *
            (1000 * Real.exp (1 / 250) * (n : ℝ) ^ (K / 250)) :=
          mul_le_mul hNB hQ (by positivity) (by positivity)
        _ = 2000 * Real.exp (1 / 250) *
            ((n : ℝ) ^ B * (n : ℝ) ^ (K / 250)) := by ring
        _ = 2000 * Real.exp (1 / 250) * (n : ℝ) ^ (B + K / 250) := by
          rw [hpowMul B (K / 250)]
    have hFnonneg : 0 ≤ ((n : ℝ) ^ B + 1) *
        (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) := by positivity
    have hJplus2 : ((clockJ B n : ℝ) + 1) * (1 + (n : ℝ)⁻¹) ≤
        2 * (K ^ 2 + 1) * n := by
      exact le_trans (mul_le_mul_of_nonneg_left hInvN (by positivity)) (by nlinarith [hJplus])
    have h1 : (n : ℝ) ^ (B + K / 250) * (n : ℝ) ^ (-(2 * K)) =
        (n : ℝ) ^ (d₁ - 3 * K / 5) := by
      rw [hpowMul (B + K / 250) (-(2 * K))]
      congr 1
      dsimp [d₁]
      ring
    have h2 : (n : ℝ) ^ (B + K / 250) * (n : ℝ) ^ (-(99 / 100 * K)) =
        (n : ℝ) ^ (d₂ - 3 * K / 5) := by
      rw [hpowMul (B + K / 250) (-(99 / 100 * K))]
      congr 1
      dsimp [d₂]
      ring
    have h3 : (n : ℝ) ^ (B + K / 250) * (n : ℝ) ^ (1 - clockP B / 3) =
        (n : ℝ) ^ (d₃ - 3 * K / 5) := by
      rw [hpowMul (B + K / 250) (1 - clockP B / 3)]
      congr 1
      dsimp [d₃]
      ring
    have hninv : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hpownonneg (a : ℝ) : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) _
    have hshort : clockShortBound B n ≤
        (n : ℝ) ^ (-(2 * K)) + 2 * (n : ℝ) ^ (-(99 / 100 * K)) +
          2 * (K ^ 2 + 1) * n * (n : ℝ) ^ (-(clockP B / 3)) := by
      unfold clockShortBound
      apply add_le_add (add_le_add le_rfl le_rfl) ?_
      exact mul_le_mul_of_nonneg_right hJplus2 (by positivity)
    have hshortNonneg : 0 ≤ clockShortBound B n := by
      unfold clockShortBound
      positivity
    calc
      ((n : ℝ) ^ B + 1) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) *
          clockShortBound B n ≤
        (2000 * Real.exp (1 / 250) * (n : ℝ) ^ (B + K / 250)) *
          ((n : ℝ) ^ (-(2 * K)) + 2 * (n : ℝ) ^ (-(99 / 100 * K)) +
            2 * (K ^ 2 + 1) * n * (n : ℝ) ^ (-(clockP B / 3))) := by
        exact mul_le_mul hF hshort hshortNonneg (by positivity)
      _ ≤ C₁ * ((n : ℝ) ^ (d₁ - 3 * K / 5) + (n : ℝ) ^ (d₂ - 3 * K / 5) +
          (n : ℝ) ^ (d₃ - 3 * K / 5)) := by
        have hmulOne : (n : ℝ) ^ (B + K / 250) * n =
            (n : ℝ) ^ (B + K / 250) * (n : ℝ) ^ (1 : ℝ) := by
          exact congrArg (fun x : ℝ => (n : ℝ) ^ (B + K / 250) * x) (by simp)
        have hthird : (n : ℝ) ^ (B + K / 250) * n *
            (n : ℝ) ^ (-(clockP B / 3)) = (n : ℝ) ^ (d₃ - 3 * K / 5) := by
          rw [hmulOne]
          rw [hpowThree (B + K / 250) 1 (-(clockP B / 3))]
          congr 1 <;> dsimp [d₃] <;> ring
        have hcoef : 2000 * Real.exp (1 / 250) ≤ C₁ := by
          dsimp [C₁]
          nlinarith [sq_nonneg K, Real.exp_pos (1 / 250),
            mul_nonneg (sq_nonneg K) (Real.exp_pos (1 / 250)).le]
        have hcoef2 : 4000 * Real.exp (1 / 250) ≤ C₁ := by
          dsimp [C₁]
          nlinarith [sq_nonneg K, Real.exp_pos (1 / 250),
            mul_nonneg (sq_nonneg K) (Real.exp_pos (1 / 250)).le]
        have hcoef3 : 4000 * Real.exp (1 / 250) * (K ^ 2 + 1) ≤ C₁ := by
          dsimp [C₁]
          exact le_rfl
        have hp1 := hpownonneg (d₁ - 3 * K / 5)
        have hp2 := hpownonneg (d₂ - 3 * K / 5)
        have hp3 := hpownonneg (d₃ - 3 * K / 5)
        have hc1 := mul_le_mul_of_nonneg_right hcoef hp1
        have hc2 := mul_le_mul_of_nonneg_right hcoef2 hp2
        have hc3 := mul_le_mul_of_nonneg_right hcoef3 hp3
        calc
          (2000 * Real.exp (1 / 250) * (n : ℝ) ^ (B + K / 250)) *
              ((n : ℝ) ^ (-(2 * K)) + 2 * (n : ℝ) ^ (-(99 / 100 * K)) +
                2 * (K ^ 2 + 1) * n * (n : ℝ) ^ (-(clockP B / 3))) =
            2000 * Real.exp (1 / 250) *
              ((n : ℝ) ^ (B + K / 250) * (n : ℝ) ^ (-(2 * K)) +
                2 * ((n : ℝ) ^ (B + K / 250) * (n : ℝ) ^ (-(99 / 100 * K))) +
                2 * (K ^ 2 + 1) * ((n : ℝ) ^ (B + K / 250) * n *
                  (n : ℝ) ^ (-(clockP B / 3)))) := by ring
          _ = 2000 * Real.exp (1 / 250) *
              ((n : ℝ) ^ (d₁ - 3 * K / 5) + 2 * (n : ℝ) ^ (d₂ - 3 * K / 5) +
                2 * (K ^ 2 + 1) * (n : ℝ) ^ (d₃ - 3 * K / 5)) := by
            rw [h1, h2, hthird]
          _ ≤ C₁ * ((n : ℝ) ^ (d₁ - 3 * K / 5) + (n : ℝ) ^ (d₂ - 3 * K / 5) +
              (n : ℝ) ^ (d₃ - 3 * K / 5)) := by nlinarith [hc1, hc2, hc3]
  have htermTwo :
      (clockJ B n : ℝ) ^ 2 * (n : ℝ) ^ B *
          ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) ≤
        C₂ * (n : ℝ) ^ (d₄ - 3 * K / 5) := by
    have hpow : (n : ℝ) ^ B * (n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) =
        (n : ℝ) ^ (2 * B - (clockA B - 1)) := by
      rw [hpowThree B B (-(clockA B - 1))]
      congr 1
      ring
    have hratio : (n : ℝ) ^ B *
        ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ) ≤
          1000000 * (n : ℝ) ^ (2 * B - (clockA B - 1)) := by
      rw [div_eq_mul_inv]
      calc
        (n : ℝ) ^ B *
            ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) * θ⁻¹) =
          ((n : ℝ) ^ B * (n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1))) * θ⁻¹ := by ring
        _ = (n : ℝ) ^ (2 * B - (clockA B - 1)) * θ⁻¹ := by rw [hpow]
        _ ≤ (n : ℝ) ^ (2 * B - (clockA B - 1)) * 1000000 :=
          mul_le_mul_of_nonneg_left hinvTheta (by positivity)
        _ = 1000000 * (n : ℝ) ^ (2 * B - (clockA B - 1)) := by ring
    have hpair :
        (clockJ B n : ℝ) ^ 2 *
            ((n : ℝ) ^ B * ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ)) ≤
          (K ^ 4 * n ^ 2) *
            (1000000 * (n : ℝ) ^ (2 * B - (clockA B - 1))) := by
      have h := mul_le_mul hJsq hratio (by positivity) (by positivity)
      exact h
    calc
      _ ≤ (K ^ 4 * n ^ 2) *
          (1000000 * (n : ℝ) ^ (2 * B - (clockA B - 1))) *
          (1000 * Real.exp (1 / 250) * (n : ℝ) ^ (K / 250)) := by
        rw [show (clockJ B n : ℝ) ^ 2 * (n : ℝ) ^ B *
            ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ) =
          (clockJ B n : ℝ) ^ 2 *
            ((n : ℝ) ^ B * ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ)) by ring]
        exact mul_le_mul hpair hQ (by positivity) (by positivity)
      _ = C₂ * (n : ℝ) ^ (d₄ - 3 * K / 5) := by
        have hnSq : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by simp
        have hp : (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * B - (clockA B - 1)) *
            (n : ℝ) ^ (K / 250) =
              (n : ℝ) ^ (2 + 2 * B - (clockA B - 1) + K / 250) := by
          rw [hnSq]
          rw [hpowThree 2 (2 * B - (clockA B - 1)) (K / 250)]
          congr 1 <;> ring
        rw [show (K ^ 4 * n ^ 2) *
            (1000000 * (n : ℝ) ^ (2 * B - (clockA B - 1))) *
            (1000 * Real.exp (1 / 250) * (n : ℝ) ^ (K / 250)) =
              C₂ * ((n : ℝ) ^ 2 * (n : ℝ) ^ (2 * B - (clockA B - 1)) *
                (n : ℝ) ^ (K / 250)) by dsimp [C₂]; rw [hnSq]; ring]
        rw [hp]
        congr 2
        dsimp [d₄]
        ring
  have htermThree :
      ((n : ℝ) ^ B + 1) * Real.exp (-(clockJ B n : ℝ)) ≤
        C₃ * (n : ℝ) ^ (d₅ - 3 * K / 5) := by
    have hfloor : K ^ 2 * Real.log n - 1 < (clockJ B n : ℝ) := hJlower
    have hexp : Real.exp (-(clockJ B n : ℝ)) ≤
        Real.exp 1 * (n : ℝ) ^ (-K ^ 2) := by
      have hexp' : Real.exp (-(clockJ B n : ℝ)) ≤
          Real.exp (1 - K ^ 2 * Real.log n) :=
        Real.exp_le_exp.mpr (by linarith [hfloor])
      calc
        Real.exp (-(clockJ B n : ℝ)) ≤ Real.exp (1 - K ^ 2 * Real.log n) := hexp'
        _ = Real.exp 1 * Real.exp (-(K ^ 2 * Real.log n)) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        _ = Real.exp 1 * (n : ℝ) ^ (-K ^ 2) := by
          rw [Real.rpow_def_of_pos hnpos]
          congr 2 <;> ring
    calc
      _ ≤ (2 * (n : ℝ) ^ B) *
          (Real.exp 1 * (n : ℝ) ^ (-K ^ 2)) :=
        mul_le_mul hNB hexp (by positivity) (by positivity)
      _ = 2 * Real.exp 1 * ((n : ℝ) ^ B * (n : ℝ) ^ (-K ^ 2)) := by ring
      _ = C₃ * (n : ℝ) ^ (B - K ^ 2) := by
        rw [hpowMul B (-K ^ 2)]
        dsimp [C₃]
        congr 2 <;> ring
      _ = C₃ * (n : ℝ) ^ (d₅ - 3 * K / 5) := by
        congr 2 <;> (dsimp [d₅] <;> ring)
  have hNsmallAt :
      C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
        C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅ < 1 := hn₁' |> hn₁ n
  have htarget : 0 ≤ (n : ℝ) ^ (-(3 * K / 5)) := Real.rpow_nonneg (by positivity) _
  have htermOne' :
      ((n : ℝ) ^ B + 1) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) *
          clockShortBound B n ≤
        C₁ * (n : ℝ) ^ (d₁ - 3 * K / 5) +
          C₁ * (n : ℝ) ^ (d₂ - 3 * K / 5) + C₁ * (n : ℝ) ^ (d₃ - 3 * K / 5) := by
    calc
      _ ≤ C₁ * ((n : ℝ) ^ (d₁ - 3 * K / 5) + (n : ℝ) ^ (d₂ - 3 * K / 5) +
          (n : ℝ) ^ (d₃ - 3 * K / 5)) := htermOne
      _ = _ := by ring
  have hmajor :
      ((n : ℝ) ^ B + 1) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) *
          clockShortBound B n +
        (clockJ B n : ℝ) ^ 2 * (n : ℝ) ^ B *
          ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) +
        ((n : ℝ) ^ B + 1) * Real.exp (-(clockJ B n : ℝ)) ≤
      (n : ℝ) ^ (-(3 * K / 5)) *
        (C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
          C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅) := by
    have hfactor (d : ℝ) :
        (n : ℝ) ^ (-(3 * K / 5)) * (n : ℝ) ^ d =
          (n : ℝ) ^ (d - 3 * K / 5) := by
      rw [hpowMul (-(3 * K / 5)) d]
      congr 1
      ring
    calc
      _ ≤ C₁ * (n : ℝ) ^ (d₁ - 3 * K / 5) + C₁ * (n : ℝ) ^ (d₂ - 3 * K / 5) +
          C₁ * (n : ℝ) ^ (d₃ - 3 * K / 5) + C₂ * (n : ℝ) ^ (d₄ - 3 * K / 5) +
          C₃ * (n : ℝ) ^ (d₅ - 3 * K / 5) :=
        add_le_add (add_le_add htermOne' htermTwo) htermThree
      _ = (n : ℝ) ^ (-(3 * K / 5)) *
          (C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
            C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅) := by
        rw [← hfactor d₁, ← hfactor d₂, ← hfactor d₃, ← hfactor d₄, ← hfactor d₅]
        ring
  have hN :
      C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
        C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅ ≤ 1 := le_of_lt hNsmallAt
  have hfinal :
      ((n : ℝ) ^ B + 1) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) *
          clockShortBound B n +
        (clockJ B n : ℝ) ^ 2 * (n : ℝ) ^ B *
          ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / θ) *
          (Real.exp (Real.sqrt θ * (K * Real.log n + 2)) / Real.sqrt θ) +
        ((n : ℝ) ^ B + 1) * Real.exp (-(clockJ B n : ℝ)) ≤
      (n : ℝ) ^ (-(3 * K / 5)) := by
    calc
      _ ≤ (n : ℝ) ^ (-(3 * K / 5)) *
          (C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
            C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅) := hmajor
      _ ≤ (n : ℝ) ^ (-(3 * K / 5)) := by
        calc
          (n : ℝ) ^ (-(3 * K / 5)) *
              (C₁ * (n : ℝ) ^ d₁ + C₁ * (n : ℝ) ^ d₂ + C₁ * (n : ℝ) ^ d₃ +
                C₂ * (n : ℝ) ^ d₄ + C₃ * (n : ℝ) ^ d₅) ≤
            (n : ℝ) ^ (-(3 * K / 5)) * 1 := mul_le_mul_of_nonneg_left hN htarget
          _ = (n : ℝ) ^ (-(3 * K / 5)) := by ring
  constructor
  · simpa [K, clockK₀] using hJnumeric
  · simpa [K, clockκ, clockK₀] using hfinal

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
  classical
  obtain ⟨nShort, hshort⟩ := short_path_bad_bound B C_g hB
  obtain ⟨nNum, hnum⟩ := incidence_numerics B hB
  let nMesh : ℕ := ⌈2 * max C_g 0⌉₊
  refine ⟨max nShort (max nNum (max nMesh 3)), ?_⟩
  intro n hn g hg R K _ _ _ Ω _ _ _ D v
  have hnShort : nShort ≤ n := le_trans (le_max_left _ _) hn
  have hnNum : nNum ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hnOuter : max nMesh 3 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  have hnMesh : nMesh ≤ n := le_trans (le_max_left _ _) hnOuter
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hnOuter
  have hn2 : 2 ≤ n := by omega
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hKpos : 0 < clockK₀ B := by unfold clockK₀; linarith [hB]
  have hB20 : 20 ≤ clockA B := by unfold clockA clockK₀; linarith [hB]
  have hpow20 : (10 : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (20 : ℝ) := by norm_num
      _ ≤ (n : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow (by norm_num) hnreal (by norm_num)
  have hpowA : (n : ℝ) ^ (20 : ℝ) ≤ (n : ℝ) ^ clockA B :=
    Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hnreal) hB20
  have hgnum : (10 : ℝ) ^ 6 ≤ g := le_trans hpow20 (le_trans hpowA (D.card_labels_ge (by omega)))
  have htheta := D.completed_theta_bounds hgnum
  have hthetaLeOne : D.C.theta ≤ 1 := le_trans htheta.2 (by norm_num)
  have hgPos : 0 < (g : ℝ) := by
    have hgReal : (1 : ℝ) ≤ (g : ℝ) :=
      (show (1 : ℝ) ≤ (10 : ℝ) ^ 6 by norm_num).trans hgnum
    have hgNat : 1 ≤ g := by exact_mod_cast hgReal
    exact_mod_cast (show 0 < g by omega)
  have hgNonneg : 0 ≤ (g : ℝ) := le_of_lt hgPos
  have hrowCardEq : (Fintype.card D.Row : ℝ) = D.C.theta * (g : ℝ) := by
    have h := D.C.completed_card
    change (Fintype.card (R ⊕ Fin D.C.dummyRows) : ℝ) = _
    rw [Fintype.card_sum, Fintype.card_fin]
    exact_mod_cast h.symm
  have hrowCard : (Fintype.card D.Row : ℝ) ≤ (g : ℝ) := by
    rw [hrowCardEq]
    nlinarith [hthetaLeOne, hgNonneg]
  have hEdgeCard : (Fintype.card (RowLabel D.Row g) : ℝ) ≤ (g : ℝ) ^ 2 := by
    simp only [RowLabel, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    nlinarith [hrowCard, hgNonneg]
  have hCgNonneg : 0 ≤ C_g := by
    have hgNat : 1 ≤ g := by
      have h : (1 : ℝ) ≤ (g : ℝ) := (by norm_num : (1 : ℝ) ≤ (10 : ℝ) ^ 6).trans hgnum
      exact_mod_cast h
    have hlog : 0 ≤ Real.log (g : ℝ) := Real.log_nonneg (by exact_mod_cast hgNat)
    have hnCg : 0 ≤ C_g * (n : ℝ) := le_trans hlog hg
    nlinarith [hnpos]
  have hnCg : 2 * C_g ≤ (n : ℝ) := by
    have hnMeshCast : (⌈2 * max C_g 0⌉₊ : ℝ) ≤ n := by exact_mod_cast hnMesh
    have hceil : 2 * max C_g 0 ≤ (⌈2 * max C_g 0⌉₊ : ℝ) := Nat.le_ceil _
    have hmax : 2 * C_g ≤ 2 * max C_g 0 := by
      exact mul_le_mul_of_nonneg_left (le_max_left C_g 0) (by norm_num)
    exact hmax.trans (hceil.trans hnMeshCast)
  have hdeltaBig : (g : ℝ) ^ 2 * D.mesh.δ ≤ 1 := by
    rw [D.mesh.δ_eq]
    have hpowExp : (g : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ 2)) =
        Real.exp (2 * Real.log (g : ℝ) - (n : ℝ) ^ 2) := by
      have hgalias : (g : ℝ) = Real.exp (Real.log (g : ℝ)) := (Real.exp_log hgPos).symm
      have hgaliasSq : (g : ℝ) ^ 2 = Real.exp (Real.log (g : ℝ)) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hgalias
      calc
        (g : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ 2)) =
            Real.exp (Real.log (g : ℝ)) ^ 2 * Real.exp (-((n : ℝ) ^ 2)) := by rw [hgaliasSq]
        _ = Real.exp (Real.log (g : ℝ)) * Real.exp (Real.log (g : ℝ)) *
              Real.exp (-((n : ℝ) ^ 2)) := by rw [pow_two]
        _ = Real.exp (Real.log (g : ℝ) + Real.log (g : ℝ)) *
              Real.exp (-((n : ℝ) ^ 2)) := by rw [← Real.exp_add]
        _ = Real.exp (Real.log (g : ℝ) + Real.log (g : ℝ) - (n : ℝ) ^ 2) := by
          rw [← Real.exp_add]
          congr 1 <;> ring
        _ = Real.exp (2 * Real.log (g : ℝ) - (n : ℝ) ^ 2) := by congr 1 <;> ring
    rw [hpowExp]
    apply (Real.exp_le_one_iff).2
    nlinarith [hg, hnCg]
  have hmeshTime : (D.mesh.ticks : ℝ) * D.mesh.δ ≤
      clockK₀ B * Real.log (n : ℝ) + 1 := by
    have hcover := D.mesh.least_cover
    rw [D.mesh.horizon_eq] at hcover
    linarith [D.mesh.δ_le_one]
  have hdeltaNonneg : 0 ≤ D.mesh.δ := D.mesh.δ_nonneg
  let M : ℕ := Fintype.card (RowLabel D.Row g) + 1
  have htime (j : ℕ) (hj : j ∈ Finset.range M) :
      ((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ ≤ clockK₀ B * Real.log (n : ℝ) + 2 := by
    have hjle : j ≤ Fintype.card (RowLabel D.Row g) := by
      have := Finset.mem_range.mp hj
      dsimp [M] at this
      omega
    have hjdelta : (j : ℝ) * D.mesh.δ ≤ 1 := by
      calc
        (j : ℝ) * D.mesh.δ ≤ (Fintype.card (RowLabel D.Row g) : ℝ) * D.mesh.δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hjle) hdeltaNonneg
        _ ≤ (g : ℝ) ^ 2 * D.mesh.δ :=
          mul_le_mul_of_nonneg_right hEdgeCard hdeltaNonneg
        _ ≤ 1 := hdeltaBig
    rw [Nat.cast_add]
    calc
      ((D.mesh.ticks : ℝ) + (j : ℝ)) * D.mesh.δ =
          (D.mesh.ticks : ℝ) * D.mesh.δ + (j : ℝ) * D.mesh.δ := by ring
      _ ≤ clockK₀ B * Real.log (n : ℝ) + 1 + 1 := add_le_add hmeshTime hjdelta
      _ = clockK₀ B * Real.log (n : ℝ) + 2 := by ring
  have hdegree (r : D.Row) :
      ((Finset.univ.filter fun k : K => r ∈ D.scope' k).card : ℝ) ≤ (n : ℝ) ^ B := by
    cases r with
    | inl a =>
        have hsrc := D.admissible.2.2.2.2.1 a
        have hcard :
            (Finset.univ.filter fun k : K => Sum.inl a ∈ D.scope' k) =
              Finset.univ.filter fun k : K => a ∈ D.I.scope k := by
          ext k
          simp [ClockData.scope']
        rw [hcard]
        exact hsrc
    | inr i =>
        have hempty :
            (Finset.univ.filter fun k : K => Sum.inr i ∈ D.scope' k) = ∅ := by
          ext k
          simp [ClockData.scope']
        rw [hempty]
        simp
        positivity
  have rootMultiplicity (f : D.Row → ℝ) (hf : ∀ r, 0 ≤ f r) :
      (∑ t : SamplingTest R K, ∑ r ∈ testRoots D.scope' (D.test' t), f r) ≤
        ((n : ℝ) ^ B + 1) * ∑ r : D.Row, f r := by
    let e : K ⊕ R ≃ SamplingTest R K := {
      toFun := Sum.elim SamplingTest.predicate SamplingTest.singleton
      invFun := fun t => match t with
        | .predicate k => Sum.inl k
        | .singleton r => Sum.inr r
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro t; cases t <;> rfl }
    have hsplit := Fintype.sum_equiv e
      (fun x : K ⊕ R => ∑ r ∈ testRoots D.scope' (D.test' (e x)), f r)
      (fun t : SamplingTest R K => ∑ r ∈ testRoots D.scope' (D.test' t), f r)
      (by intro x; rfl)
    have hsumType :
        (∑ t : SamplingTest R K, ∑ r ∈ testRoots D.scope' (D.test' t), f r) =
          (∑ k : K, ∑ r ∈ D.scope' k, f r) + ∑ r : R, f (Sum.inl r) := by
      calc
        _ = ∑ x : K ⊕ R, ∑ r ∈ testRoots D.scope' (D.test' (e x)), f r := hsplit.symm
        _ = _ := by simp [e, testRoots, ClockData.test', Fintype.sum_sum_type]
    have hscopeIndicator (k : K) :
        (∑ r ∈ D.scope' k, f r) = ∑ r : D.Row, if r ∈ D.scope' k then f r else 0 := by
      calc
        (∑ r ∈ D.scope' k, f r) =
            ∑ r ∈ D.scope' k, if r ∈ D.scope' k then f r else 0 := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [hr]
        _ = ∑ r : D.Row, if r ∈ D.scope' k then f r else 0 := by
              apply Finset.sum_subset (Finset.subset_univ _)
              intro r hr hnot
              simp [hnot]
    have hdegreeSum :
        (∑ k : K, ∑ r ∈ D.scope' k, f r) =
          ∑ r : D.Row, ∑ k ∈ Finset.univ.filter (fun k : K => r ∈ D.scope' k), f r := by
      simp_rw [hscopeIndicator]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_filter]
    have hdegreeBound :
        (∑ k : K, ∑ r ∈ D.scope' k, f r) ≤ (n : ℝ) ^ B * ∑ r : D.Row, f r := by
      rw [hdegreeSum]
      calc
        _ = ∑ r : D.Row,
            ((Finset.univ.filter (fun k : K => r ∈ D.scope' k)).card : ℝ) * f r := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ r : D.Row, (n : ℝ) ^ B * f r := by
              apply Finset.sum_le_sum
              intro r hr
              exact mul_le_mul_of_nonneg_right (hdegree r) (hf r)
        _ = (n : ℝ) ^ B * ∑ r : D.Row, f r := by rw [Finset.mul_sum]
    have hrealSum : ∑ r : R, f (Sum.inl r) ≤ ∑ r : D.Row, f r := by
      have hsplitRows : (∑ r : D.Row, f r) =
          (∑ r : R, f (Sum.inl r)) + ∑ i : Fin D.C.dummyRows, f (Sum.inr i) := by
        simp [ClockData.Row, Fintype.sum_sum_type]
      have hdummy : 0 ≤ ∑ i : Fin D.C.dummyRows, f (Sum.inr i) :=
        Finset.sum_nonneg fun i hi => hf (Sum.inr i)
      rw [hsplitRows]
      linarith
    rw [hsumType]
    calc
      (∑ k : K, ∑ r ∈ D.scope' k, f r) + ∑ r : R, f (Sum.inl r) ≤
          (n : ℝ) ^ B * ∑ r : D.Row, f r + ∑ r : D.Row, f r :=
        add_le_add hdegreeBound hrealSum
      _ = ((n : ℝ) ^ B + 1) * ∑ r : D.Row, f r := by ring
  have hthetaPos : 0 < D.C.theta := lt_of_lt_of_le (by norm_num) htheta.1
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith [hnreal])
  let x : ℝ := clockK₀ B * Real.log (n : ℝ) + 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hincidence := hnum n hnNum D.C.theta htheta.1 htheta.2
  have hJnumeric : Real.exp 2 * x ≤ (clockJ B n : ℝ) := by simpa [x] using hincidence.1
  have hnumerics := hincidence.2
  let pathMass (u : Endpoint D.Row g) (j : ℕ) : ℝ :=
    ∑ π ∈ decPaths u v j, pathWeight D.edgeLaw π
  let fullMass (j : ℕ) : ℝ := ∑ u : Endpoint D.Row g, pathMass u j
  let rootRows (t : SamplingTest R K) : Finset D.Row := testRoots D.scope' (D.test' t)
  let rootMass (j : ℕ) : ℝ :=
    ∑ t : SamplingTest R K, ∑ r ∈ rootRows t, pathMass (Sum.inl r) j
  let pathBadProb (t : SamplingTest R K) (j : ℕ)
      (π : Fin j → ClockCandidate D.mesh.ticks D.Row g D.Out) : ℝ :=
    D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n)
      (insertArrivals (pathInsertion π) ξ) (D.test' t))
  let pathException (t : SamplingTest R K) (r : D.Row) (j : ℕ)
      (π : Fin j → ClockCandidate D.mesh.ticks D.Row g D.Out) : Prop :=
    match t with
    | .predicate k => pathMeetsOtherRow π (D.scope' k) r
    | .singleton _ => False
  let exceptionMass (j : ℕ) : ℝ :=
    ∑ t : SamplingTest R K, ∑ r ∈ rootRows t,
      ∑ π ∈ decPaths (Sum.inl r) v j,
        if pathException t r j π then pathWeight D.edgeLaw π else 0
  let eventMass (j : ℕ) : ℝ :=
    ∑ t : SamplingTest R K, ∑ r ∈ rootRows t,
      ∑ π ∈ decPaths (Sum.inl r) v j,
        pathWeight D.edgeLaw π * pathBadProb t j π
  let seriesTerm (j : ℕ) : ℝ :=
    D.C.theta ^ (j / 2) * x ^ j / (j.factorial : ℝ)
  let rootCoeff : ℝ := (n : ℝ) ^ B + 1
  let meshSeries : ℝ := Real.exp (Real.sqrt D.C.theta * x) / Real.sqrt D.C.theta
  have hshortNonneg : 0 ≤ clockShortBound B n := by
    unfold clockShortBound
    positivity
  have hpathWeightNonneg (j : ℕ) (π : Fin j → ClockCandidate D.mesh.ticks D.Row g D.Out) :
      0 ≤ pathWeight D.edgeLaw π := by
    unfold pathWeight
    apply Finset.prod_nonneg
    intro i hi
    exact (D.edgeLaw ((π i).1, (π i).2.1)).nonneg _
  have hpathMassNonneg (u : Endpoint D.Row g) (j : ℕ) : 0 ≤ pathMass u j := by
    unfold pathMass
    apply Finset.sum_nonneg
    intro π hπ
    exact hpathWeightNonneg j π
  have hfullSplit (j : ℕ) :
      fullMass j = (∑ r : D.Row, pathMass (Sum.inl r) j) +
        ∑ y : Fin g, pathMass (Sum.inr y) j := by
    simp [fullMass, pathMass, Endpoint, Fintype.sum_sum_type]
  have hrowMassLeFull (j : ℕ) :
      (∑ r : D.Row, pathMass (Sum.inl r) j) ≤ fullMass j := by
    have hy : 0 ≤ ∑ y : Fin g, pathMass (Sum.inr y) j :=
      Finset.sum_nonneg fun y hy => hpathMassNonneg (Sum.inr y) j
    rw [hfullSplit]
    linarith
  have hrootMassBound (j : ℕ) : rootMass j ≤ rootCoeff * fullMass j := by
    calc
      rootMass j =
          ∑ t : SamplingTest R K, ∑ r ∈ rootRows t, pathMass (Sum.inl r) j := rfl
      _ ≤ rootCoeff * ∑ r : D.Row, pathMass (Sum.inl r) j := by
        simpa [rootRows, rootCoeff] using
          (rootMultiplicity (fun r : D.Row => pathMass (Sum.inl r) j)
            (fun r => hpathMassNonneg (Sum.inl r) j))
      _ ≤ rootCoeff * fullMass j := by
        apply mul_le_mul_of_nonneg_left (hrowMassLeFull j)
        dsimp [rootCoeff]
        positivity
  have hrootMassSum :
      (∑ j ∈ Finset.range M, rootMass j) ≤
        rootCoeff * ∑ j ∈ Finset.range M, fullMass j := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, rootCoeff * fullMass j :=
        Finset.sum_le_sum fun j hj => hrootMassBound j
      _ = rootCoeff * ∑ j ∈ Finset.range M, fullMass j := by rw [Finset.mul_sum]
  have hprobLeOne (A : ClockField D.mesh.ticks D.Row g D.Out → Prop) :
      D.law.pr A ≤ 1 := by
    have hc := finProb_pr_compl D.law A
    have hnc := finProb_pr_nonneg D.law (fun ξ => ¬ A ξ)
    linarith
  have hscopeCard (k : K) : ((D.scope' k).card : ℝ) ≤ (n : ℝ) ^ B := by
    have hs := D.admissible.2.2.2.1 k
    simpa [ClockData.scope'] using hs
  have hthetaUpperOne : D.C.theta ≤ 1 := hthetaLeOne
  have hlambda : 0 ≤ (n : ℝ) ^ (-(clockA B - 1)) := by positivity
  have hTwoRow (j : ℕ) : exceptionMass j ≤
      (j : ℝ) ^ 2 * (n : ℝ) ^ B *
        ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta) *
          (D.C.theta ^ (j / 2) * (((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ) ^ j /
            (j.factorial : ℝ)) := by
    let e : K ⊕ R ≃ SamplingTest R K := {
      toFun := Sum.elim SamplingTest.predicate SamplingTest.singleton
      invFun := fun t => match t with
        | .predicate k => Sum.inl k
        | .singleton r => Sum.inr r
      left_inv := by intro x; cases x <;> rfl
      right_inv := by intro t; cases t <;> rfl }
    have hfilter (k : K) (r : D.Row) :
        (∑ π ∈ decPaths (Sum.inl r) v j,
          if pathMeetsOtherRow π (D.scope' k) r then pathWeight D.edgeLaw π else 0) =
        ∑ π ∈ (decPaths (Sum.inl r) v j).filter
          (fun π => pathMeetsOtherRow π (D.scope' k) r), pathWeight D.edgeLaw π := by
      symm
      exact Finset.sum_filter (s := decPaths (Sum.inl r) v j)
        (fun π => pathMeetsOtherRow π (D.scope' k) r) (fun π => pathWeight D.edgeLaw π)
    have hindicator : exceptionMass j =
        ∑ k : K, ∑ r ∈ D.scope' k,
          ∑ π ∈ decPaths (Sum.inl r) v j,
            if pathMeetsOtherRow π (D.scope' k) r then pathWeight D.edgeLaw π else 0 := by
      dsimp [exceptionMass]
      have hEquiv := Fintype.sum_equiv e
        (fun y : K ⊕ R =>
          ∑ r ∈ rootRows (e y), ∑ π ∈ decPaths (Sum.inl r) v j,
            if pathException (e y) r j π then pathWeight D.edgeLaw π else 0)
        (fun t : SamplingTest R K =>
          ∑ r ∈ rootRows t, ∑ π ∈ decPaths (Sum.inl r) v j,
            if pathException t r j π then pathWeight D.edgeLaw π else 0)
        (by intro y; rfl)
      calc
        _ = ∑ y : K ⊕ R,
            ∑ r ∈ rootRows (e y), ∑ π ∈ decPaths (Sum.inl r) v j,
              if pathException (e y) r j π then pathWeight D.edgeLaw π else 0 := hEquiv.symm
        _ = _ := by
          simp [e, rootRows, pathException, ClockData.test', testRoots, Fintype.sum_sum_type]
          rfl
    rw [hindicator]
    simp_rw [hfilter]
    have hbound := two_row_weight_sum (T := D.mesh.ticks)
      D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one
      D.law' D.lab' D.C.theta D.completed_rows_eq D.completed_columns_eq
      hthetaPos hthetaUpperOne D.scope' ((n : ℝ) ^ B)
      ((n : ℝ) ^ (-(clockA B - 1))) (by positivity) hlambda hscopeCard hdegree
      (fun r y => D.completed_atom_le hn2 r y) v j
    simpa [ClockData.edgeLaw] using hbound
  have hrootEndpointSum (t : SamplingTest R K) (f : Endpoint D.Row g → ℝ) :
      (∑ e ∈ testRootEndpoints (g := g) D.scope' (D.test' t), f e) =
        ∑ r ∈ rootRows t, f (Sum.inl r) := by
    simpa [rootRows, testRootEndpoints] using
      (Finset.sum_image (s := rootRows t) (g := Sum.inl) (f := f)
        (by
          intro a ha b hb hab
          exact Sum.inl.inj hab))
  have hclosurePaths (t : SamplingTest R K) :
      D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) ∧
          v ∈ activeEndpoints ξ D.scope' (D.test' t)) ≤
        ∑ r ∈ rootRows t, ∑ j ∈ Finset.range M,
          ∑ π ∈ decPaths (Sum.inl r) v j,
            pathWeight D.edgeLaw π * pathBadProb t j π := by
    have h := closure_path_union D.edgeLaw
      (testRootEndpoints (g := g) D.scope' (D.test' t)) v
      (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t))
    calc
      _ ≤ ∑ e ∈ testRootEndpoints (g := g) D.scope' (D.test' t),
          ∑ j ∈ Finset.range M, ∑ π ∈ decPaths e v j,
            pathWeight D.edgeLaw π * pathBadProb t j π := by
          simpa [ClockData.law, activeEndpoints_eq_closureFrom, M, pathBadProb] using h
      _ = ∑ r ∈ rootRows t, ∑ j ∈ Finset.range M,
          ∑ π ∈ decPaths (Sum.inl r) v j,
            pathWeight D.edgeLaw π * pathBadProb t j π := by
          rw [hrootEndpointSum]
  have htotalPath :
      (∑ t : SamplingTest R K,
          D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) ∧
            v ∈ activeEndpoints ξ D.scope' (D.test' t))) ≤
        ∑ j ∈ Finset.range M, eventMass j := by
    calc
      _ ≤ ∑ t : SamplingTest R K,
          ∑ r ∈ rootRows t, ∑ j ∈ Finset.range M,
            ∑ π ∈ decPaths (Sum.inl r) v j,
              pathWeight D.edgeLaw π * pathBadProb t j π :=
        Finset.sum_le_sum fun t ht => hclosurePaths t
      _ = ∑ t : SamplingTest R K,
          ∑ j ∈ Finset.range M, ∑ r ∈ rootRows t,
            ∑ π ∈ decPaths (Sum.inl r) v j,
              pathWeight D.edgeLaw π * pathBadProb t j π := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range M,
          ∑ t : SamplingTest R K, ∑ r ∈ rootRows t,
            ∑ π ∈ decPaths (Sum.inl r) v j,
              pathWeight D.edgeLaw π * pathBadProb t j π := by
        rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range M, eventMass j := rfl
  have hshortTerm (j : ℕ) (hj : j ≤ clockJ B n)
      (t : SamplingTest R K) (r : D.Row) (hr : r ∈ rootRows t)
      (π : Fin j → ClockCandidate D.mesh.ticks D.Row g D.Out)
      (hπ : π ∈ decPaths (Sum.inl r) v j) :
      pathWeight D.edgeLaw π * pathBadProb t j π ≤
        clockShortBound B n * pathWeight D.edgeLaw π +
          if pathException t r j π then pathWeight D.edgeLaw π else 0 := by
    have hw := hpathWeightNonneg j π
    cases t with
    | predicate k =>
        change r ∈ D.scope' k at hr
        rcases Finset.mem_map.mp hr with ⟨a, ha, hrow⟩
        have hrow' : r = Sum.inl a := hrow.symm
        subst r
        by_cases hother : pathMeetsOtherRow π (D.scope' k) (Sum.inl a)
        · have hp : pathBadProb (.predicate k) j π ≤ 1 := by
            apply hprobLeOne
          have hmul := mul_le_mul_of_nonneg_left hp hw
          have hshortAdd :
              pathWeight D.edgeLaw π * pathBadProb (.predicate k) j π ≤
                clockShortBound B n * pathWeight D.edgeLaw π + pathWeight D.edgeLaw π := by
            nlinarith [hmul, mul_nonneg hshortNonneg hw]
          simpa [pathException, hother] using hshortAdd
        · by_cases hwpos : 0 < pathWeight D.edgeLaw π
          · have hav : ∀ k' : K,
                (SamplingTest.predicate k : SamplingTest R K) = SamplingTest.predicate k' →
                  ¬ pathMeetsOtherRow π (D.scope' k') (Sum.inl a) := by
              intro k' hk'
              have hkk' : k = k' := by injection hk'
              subst k'
              exact hother
            have hp : pathBadProb (.predicate k) j π ≤ clockShortBound B n := by
              simpa [pathBadProb] using
                hshort n hnShort g hg D (.predicate k) a ha v j hj π hπ hav hwpos
            have hmul := mul_le_mul_of_nonneg_left hp hw
            have hmul' : pathWeight D.edgeLaw π * pathBadProb (.predicate k) j π ≤
                clockShortBound B n * pathWeight D.edgeLaw π := by nlinarith [hmul]
            simpa [pathException, hother] using hmul'
          · have hwzero : pathWeight D.edgeLaw π = 0 := by linarith
            simp [pathException, hother, hwzero]
    | singleton a =>
        have hr' : r ∈ ({Sum.inl a} : Finset D.Row) := by
          simpa [rootRows, ClockData.test', testRoots] using hr
        have hrow : r = Sum.inl a := Finset.mem_singleton.mp hr'
        subst r
        have ha : a ∈ testRoots D.I.scope (.singleton a) := by simp [testRoots]
        by_cases hwpos : 0 < pathWeight D.edgeLaw π
        · have hav : ∀ k' : K,
              (SamplingTest.singleton a : SamplingTest R K) = SamplingTest.predicate k' →
                ¬ pathMeetsOtherRow π (D.scope' k') (Sum.inl a) := by
            intro k' hk'
            cases hk'
          have hp : pathBadProb (.singleton a) j π ≤ clockShortBound B n := by
            simpa [pathBadProb] using
              hshort n hnShort g hg D (.singleton a) a ha v j hj π hπ hav hwpos
          have hmul := mul_le_mul_of_nonneg_left hp hw
          have hmul' : pathWeight D.edgeLaw π * pathBadProb (.singleton a) j π ≤
              clockShortBound B n * pathWeight D.edgeLaw π := by nlinarith [hmul]
          simpa [pathException] using hmul'
        · have hwzero : pathWeight D.edgeLaw π = 0 := by linarith
          simp [pathException, hwzero]
  have hshortEvent (j : ℕ) (hj : j ≤ clockJ B n) :
      eventMass j ≤ clockShortBound B n * rootMass j + exceptionMass j := by
    calc
      eventMass j ≤
          ∑ t : SamplingTest R K, ∑ r ∈ rootRows t,
            ∑ π ∈ decPaths (Sum.inl r) v j,
              (clockShortBound B n * pathWeight D.edgeLaw π +
                if pathException t r j π then pathWeight D.edgeLaw π else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro π hπ
        exact hshortTerm j hj t r hr π hπ
      _ = clockShortBound B n * rootMass j + exceptionMass j := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
  have hlongEvent (j : ℕ) : eventMass j ≤ rootMass j := by
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro π hπ
    have hp := hprobLeOne (fun ξ =>
      closureBad D.lab' D.failure' D.scope' (clockLnat B n)
        (insertArrivals (pathInsertion π) ξ) (D.test' t))
    have hmul := mul_le_mul_of_nonneg_left hp (hpathWeightNonneg j π)
    simpa [pathBadProb, pathMass] using hmul
  let shortSet : Finset ℕ := (Finset.range M).filter (fun j => j ≤ clockJ B n)
  let longSet : Finset ℕ := (Finset.range M).filter (fun j => clockJ B n < j)
  have hrootMassNonneg (j : ℕ) : 0 ≤ rootMass j := by
    unfold rootMass
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro r hr
    exact hpathMassNonneg (Sum.inl r) j
  have hseriesTermNonneg (j : ℕ) : 0 ≤ seriesTerm j := by
    positivity
  have hthetaPowLeOne (j : ℕ) : D.C.theta ^ (j / 2) ≤ 1 :=
    pow_le_one₀ (le_of_lt hthetaPos) hthetaUpperOne
  have hmeshTerm (j : ℕ) (hj : j ∈ Finset.range M) :
      D.C.theta ^ (j / 2) * (((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ) ^ j /
          (j.factorial : ℝ) ≤ seriesTerm j := by
    have htimej : ((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ ≤ x := by
      simpa [x] using htime j hj
    have hpow : (((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ) ^ j ≤ x ^ j := by
      exact pow_le_pow_left₀ (by positivity) htimej j
    have hmul : D.C.theta ^ (j / 2) *
          (((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ) ^ j ≤
        D.C.theta ^ (j / 2) * x ^ j :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    dsimp [seriesTerm]
    exact div_le_div_of_nonneg_right hmul (by positivity)
  have hfullBound (j : ℕ) (hj : j ∈ Finset.range M) : fullMass j ≤ seriesTerm j := by
    have hpaths := decPath_weight_sum (T := D.mesh.ticks)
      D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one D.law' D.lab' D.C.theta
      D.completed_rows_eq D.completed_columns_eq hthetaPos.le hthetaUpperOne v j
    calc
      fullMass j ≤
          D.C.theta ^ (j / 2) * (((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ) ^ j /
            (j.factorial : ℝ) := by
        simpa [fullMass, pathMass, ClockData.edgeLaw] using hpaths
      _ ≤ seriesTerm j := hmeshTerm j hj
  have hfullSeries :
      (∑ j ∈ Finset.range M, fullMass j) ≤ meshSeries := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, seriesTerm j :=
        Finset.sum_le_sum fun j hj => hfullBound j hj
      _ ≤ meshSeries := by
        simpa [seriesTerm, meshSeries, x] using
          (walk_series_bound D.C.theta x hthetaPos hthetaUpperOne hx M)
  have hseriesLong :
      (∑ j ∈ longSet, seriesTerm j) ≤ Real.exp (-(clockJ B n : ℝ)) := by
    have hsubset : longSet ⊆ Finset.Ico (clockJ B n + 1) M := by
      intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hjM, hjLong⟩
      exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt hjLong, Finset.mem_range.mp hjM⟩
    calc
      _ ≤ ∑ j ∈ longSet, (x ^ j / (j.factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hpow := hthetaPowLeOne j
        have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hx j)
        have hmul' : D.C.theta ^ (j / 2) * x ^ j ≤ x ^ j := by simpa using hmul
        have hden : 0 ≤ (j.factorial : ℝ) := by positivity
        have hterm : D.C.theta ^ (j / 2) * x ^ j / (j.factorial : ℝ) ≤
            x ^ j / (j.factorial : ℝ) := div_le_div_of_nonneg_right hmul' hden
        simpa [seriesTerm] using hterm
      _ ≤ ∑ j ∈ Finset.Ico (clockJ B n + 1) M, x ^ j / (j.factorial : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro j hj hnot
          exact div_nonneg (pow_nonneg hx _) (by positivity))
      _ ≤ Real.exp (-(clockJ B n : ℝ)) :=
        walk_series_tail x hx (clockJ B n) hJnumeric M
  have hfullLong :
      (∑ j ∈ longSet, fullMass j) ≤ Real.exp (-(clockJ B n : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ longSet, seriesTerm j := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfullBound j (Finset.mem_filter.mp hj).1
      _ ≤ Real.exp (-(clockJ B n : ℝ)) := hseriesLong
  have hrootAll : (∑ j ∈ Finset.range M, rootMass j) ≤ rootCoeff * meshSeries := by
    calc
      _ ≤ rootCoeff * ∑ j ∈ Finset.range M, fullMass j := hrootMassSum
      _ ≤ rootCoeff * meshSeries :=
        mul_le_mul_of_nonneg_left hfullSeries (by positivity)
  have hrootLong : (∑ j ∈ longSet, rootMass j) ≤
      rootCoeff * Real.exp (-(clockJ B n : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ longSet, rootCoeff * fullMass j :=
        Finset.sum_le_sum fun j hj => hrootMassBound j
      _ = rootCoeff * ∑ j ∈ longSet, fullMass j := by rw [Finset.mul_sum]
      _ ≤ rootCoeff * Real.exp (-(clockJ B n : ℝ)) :=
        mul_le_mul_of_nonneg_left hfullLong (by positivity)
  have hseriesShort : (∑ j ∈ shortSet, seriesTerm j) ≤ meshSeries := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, seriesTerm j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
          intro j hj hnot
          exact hseriesTermNonneg j)
      _ ≤ meshSeries := by
        simpa [seriesTerm, meshSeries, x] using
          (walk_series_bound D.C.theta x hthetaPos hthetaUpperOne hx M)
  let twoCoeff : ℝ := (clockJ B n : ℝ) ^ 2 * (n : ℝ) ^ B *
    ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta)
  have htwoCoeffNonneg : 0 ≤ twoCoeff := by
    dsimp [twoCoeff]
    positivity
  have htwoRowX (j : ℕ) (hj : j ∈ shortSet) :
      exceptionMass j ≤
        (j : ℝ) ^ 2 * (n : ℝ) ^ B *
          ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta) * seriesTerm j := by
    have hjrange : j ∈ Finset.range M := (Finset.mem_filter.mp hj).1
    have hbound := hTwoRow j
    calc
      exceptionMass j ≤
          (j : ℝ) ^ 2 * (n : ℝ) ^ B *
            ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta) *
              (D.C.theta ^ (j / 2) *
                (((D.mesh.ticks + j : ℕ) : ℝ) * D.mesh.δ) ^ j /
                  (j.factorial : ℝ)) := hbound
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left (hmeshTerm j hjrange) (by positivity)
  have hexceptionShort :
      (∑ j ∈ shortSet, exceptionMass j) ≤ twoCoeff * meshSeries := by
    calc
      _ ≤ ∑ j ∈ shortSet, twoCoeff * seriesTerm j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : (j : ℝ) ≤ (clockJ B n : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp hj).2
        have hjsq : (j : ℝ) ^ 2 ≤ (clockJ B n : ℝ) ^ 2 := by
          have hdiff : 0 ≤ (clockJ B n : ℝ) - j := by linarith
          nlinarith [mul_nonneg hdiff (by positivity : 0 ≤ (clockJ B n : ℝ) + j)]
        have hrest : 0 ≤ (n : ℝ) ^ B *
            ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta) := by
          positivity
        have hcoeff :
            (j : ℝ) ^ 2 * (n : ℝ) ^ B *
                ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta) ≤ twoCoeff := by
          dsimp [twoCoeff]
          calc
            (j : ℝ) ^ 2 * (n : ℝ) ^ B *
                ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta) =
              (j : ℝ) ^ 2 * ((n : ℝ) ^ B *
                ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta)) := by ring
            _ ≤ (clockJ B n : ℝ) ^ 2 * ((n : ℝ) ^ B *
                ((n : ℝ) ^ B * (n : ℝ) ^ (-(clockA B - 1)) / D.C.theta)) :=
              mul_le_mul_of_nonneg_right hjsq hrest
            _ = _ := by ring
        exact (htwoRowX j hj).trans
          (mul_le_mul_of_nonneg_right hcoeff (hseriesTermNonneg j))
      _ = twoCoeff * ∑ j ∈ shortSet, seriesTerm j := by rw [Finset.mul_sum]
      _ ≤ twoCoeff * meshSeries :=
        mul_le_mul_of_nonneg_left hseriesShort htwoCoeffNonneg
  have hshortLongSplit :
      (∑ j ∈ Finset.range M, eventMass j) ≤
        clockShortBound B n * (∑ j ∈ Finset.range M, rootMass j) +
          (∑ j ∈ longSet, rootMass j) +
          ∑ j ∈ shortSet, exceptionMass j := by
    calc
      _ ≤ ∑ j ∈ Finset.range M,
          (clockShortBound B n * rootMass j +
            (if clockJ B n < j then rootMass j else 0) +
            (if j ≤ clockJ B n then exceptionMass j else 0)) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hs : j ≤ clockJ B n
        · have hnot : ¬ clockJ B n < j := Nat.not_lt.mpr hs
          simpa [hs, hnot] using hshortEvent j hs
        · have hlt : clockJ B n < j := Nat.lt_of_not_ge hs
          have hbase : 0 ≤ clockShortBound B n * rootMass j :=
            mul_nonneg hshortNonneg (hrootMassNonneg j)
          simp [hs, hlt]
          linarith [hlongEvent j, hbase]
      _ = clockShortBound B n * (∑ j ∈ Finset.range M, rootMass j) +
          (∑ j ∈ longSet, rootMass j) +
          ∑ j ∈ shortSet, exceptionMass j := by
        dsimp [longSet, shortSet]
        rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hderived :
      (∑ t : SamplingTest R K,
          D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) ∧
            v ∈ activeEndpoints ξ D.scope' (D.test' t))) ≤
        rootCoeff * meshSeries * clockShortBound B n +
          twoCoeff * meshSeries + rootCoeff * Real.exp (-(clockJ B n : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range M, eventMass j := htotalPath
      _ ≤ clockShortBound B n * (∑ j ∈ Finset.range M, rootMass j) +
            (∑ j ∈ longSet, rootMass j) +
            ∑ j ∈ shortSet, exceptionMass j := hshortLongSplit
      _ ≤ clockShortBound B n * (rootCoeff * meshSeries) +
            rootCoeff * Real.exp (-(clockJ B n : ℝ)) + twoCoeff * meshSeries := by
          gcongr
      _ = rootCoeff * meshSeries * clockShortBound B n +
            twoCoeff * meshSeries + rootCoeff * Real.exp (-(clockJ B n : ℝ)) := by ring
  have hnumericFinal :
      rootCoeff * meshSeries * clockShortBound B n +
        twoCoeff * meshSeries + rootCoeff * Real.exp (-(clockJ B n : ℝ)) ≤ clockκ B n := by
    simpa [rootCoeff, meshSeries, twoCoeff, x] using hnumerics
  exact hderived.trans hnumericFinal

/-- L3.10h-inc' (03:897–902): the incidence field of the raw sampler, from `badLeaves_incidence_le` and
`closure_incidence_bound`. -/
theorem clockBad_incidence (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (v : Endpoint D.Row g),
      ∑ i ∈ Finset.univ.filter (fun i : D.Bad => v ∈ D.badAct i), D.law.pr (D.badEvent i) ≤
        clockκ B n := by
  classical
  obtain ⟨n₀, hclosure⟩ := closure_incidence_bound B C_g hB
  refine ⟨n₀, ?_⟩
  intro n hn g hg R K _ _ _ Ω _ _ _ D v
  have hgroup :
      (∑ i ∈ Finset.univ.filter (fun i : D.Bad => v ∈ D.badAct i), D.law.pr (D.badEvent i)) =
        ∑ t : SamplingTest R K,
          ∑ ℓ ∈ (D.badLeaves' t).filter (fun ℓ => v ∈ ℓ.active), D.law.pr ℓ.Event := by
    rw [Finset.sum_filter]
    change (∑ i : D.Bad, if v ∈ D.badAct i then D.law.pr (D.badEvent i) else 0) = _
    change (∑ i : (Σ t : SamplingTest R K, ↥(D.badLeaves' t)),
        if v ∈ (i.2.1).active then D.law.pr (i.2.1).Event else 0) = _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    change (∑ ℓ ∈ (Finset.univ : Finset (↥(D.badLeaves' t))),
        if v ∈ ℓ.1.active then D.law.pr ℓ.1.Event else 0) = _
    rw [Finset.univ_eq_attach]
    calc
      (∑ ℓ ∈ (D.badLeaves' t).attach,
          if v ∈ ℓ.1.active then D.law.pr ℓ.1.Event else 0) =
          ∑ ℓ ∈ D.badLeaves' t, if v ∈ ℓ.active then D.law.pr ℓ.Event else 0 :=
        Finset.sum_attach (D.badLeaves' t)
          (fun ℓ => if v ∈ ℓ.active then D.law.pr ℓ.Event else 0)
      _ = ∑ ℓ ∈ (D.badLeaves' t).filter (fun ℓ => v ∈ ℓ.active), D.law.pr ℓ.Event := by
        rw [Finset.sum_filter]
  have hle (t : SamplingTest R K) :
      ∑ ℓ ∈ (D.badLeaves' t).filter (fun ℓ => v ∈ ℓ.active), D.law.pr ℓ.Event ≤
        D.law.pr (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) ∧
          v ∈ activeEndpoints ξ D.scope' (D.test' t)) := by
    simpa [ClockData.badLeaves', ClockData.law, ClockData.edgeLaw] using
      (badLeaves_incidence_le D.edgeLaw D.lab' D.failure' D.scope' (clockLnat B n) (D.test' t) v)
  calc
    (∑ i ∈ Finset.univ.filter (fun i : D.Bad => v ∈ D.badAct i), D.law.pr (D.badEvent i)) =
        ∑ t : SamplingTest R K,
          ∑ ℓ ∈ (D.badLeaves' t).filter (fun ℓ => v ∈ ℓ.active), D.law.pr ℓ.Event := hgroup
    _ ≤ ∑ t : SamplingTest R K, D.law.pr
        (fun ξ => closureBad D.lab' D.failure' D.scope' (clockLnat B n) ξ (D.test' t) ∧
          v ∈ activeEndpoints ξ D.scope' (D.test' t)) :=
      Finset.sum_le_sum fun t _ => hle t
    _ ≤ clockκ B n := hclosure n hn g hg D v

/-- L3.10g-raw (03:1109–1110, 03:1127–1128): the raw joint target bound, Step 7 with the empty insertion
(noninjective targets have probability zero, the marks carrying their labels). -/
theorem target_raw_bound (B C_g : ℝ) (hB : 1 ≤ B) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] [Nonempty R] (D : ClockData B n g R K Ω) (S : Finset R) (o : ∀ a, Ω a),
      (S.card : ℝ) ≤ (n : ℝ) ^ B →
      D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) ≤
        (1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (D.C.trimmed a).w (o a) := by
  classical
  have hK₀ : 0 < clockK₀ B := by unfold clockK₀; linarith
  have hA : 10 * (B + clockK₀ B) < clockA B - 1 := by unfold clockA; linarith
  obtain ⟨n₁, hstep⟩ := step7_target_product_bound B (clockA B - 1) C_g (clockK₀ B) hB hK₀ hA
  refine ⟨max n₁ 2, ?_⟩
  intro n hn g hg R K _ _ _ Ω _ _ _ D S o hS
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn₂
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnreal
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hA20 : 20 ≤ clockA B := by unfold clockA clockK₀; linarith
  have hpow20 : (10 : ℝ) ^ 6 ≤ (n : ℝ) ^ (20 : ℝ) := by
    calc
      (10 : ℝ) ^ 6 ≤ (2 : ℝ) ^ (20 : ℝ) := by norm_num
      _ ≤ (n : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow (by norm_num) hnreal (by norm_num)
  have hpowA : (n : ℝ) ^ (20 : ℝ) ≤ (n : ℝ) ^ clockA B :=
    Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) hnreal) hA20
  have hgnum : (10 : ℝ) ^ 6 ≤ g := by
    exact le_trans (le_trans hpow20 hpowA) (D.card_labels_ge (by omega))
  have htheta := D.completed_theta_bounds hgnum
  have hatom := D.completed_atom_le hn₂
  let S' : Finset D.Row := S.map Function.Embedding.inl
  have hS' : (S'.card : ℝ) ≤ (n : ℝ) ^ B := by simpa [S'] using hS
  let ins : ∀ e : RowLabel D.Row g, Option (MeshClockValue D.mesh.ticks (D.Out e.1)) := fun _ => none
  have hins : insertionSize ins = 0 := by simp [ins, insertionSize]
  have hinsle : (insertionSize ins : ℝ) ≤ (clockK₀ B + 1) ^ 2 * Real.log (n : ℝ) := by
    simpa [hins] using mul_nonneg (sq_nonneg (clockK₀ B + 1)) hlog
  by_cases hlabels : Set.InjOn (fun a : R => D.I.lab a (o a)) S
  · have hinj : Set.InjOn (fun a : D.Row => D.lab' a (D.extendTarget o a)) S' := by
      intro r hr s hs hlabels'
      rcases Finset.mem_map.mp hr with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.mp hs with ⟨b, hb, rfl⟩
      change D.I.lab a (o a) = D.I.lab b (o b) at hlabels'
      exact congrArg Sum.inl (hlabels ha hb hlabels')
    have hstep' := hstep n hn₁ D.mesh D.mesh.δ_nonneg D.mesh.δ_le_one
      D.law' D.lab' D.C.theta hg D.completed_columns_eq htheta.2 hatom ins hinsle S'
      (D.extendTarget o) hinj hS'
    have hIns (ξ : ClockField D.mesh.ticks D.Row g D.Out) : insertArrivals ins ξ = ξ := by
      funext e
      simp [insertArrivals, ins]
    have hevent : (fun ξ => matchesTargetsOrdinarily ins ξ S' (D.extendTarget o)) =
        (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) := by
      funext ξ
      apply propext
      unfold matchesTargetsOrdinarily matchesTargets
      constructor
      · intro h r hr
        rcases h r hr with ⟨y, hassign, hins⟩
        have hassignEq :
            (greedyMatching (insertArrivals ins ξ)).assignment r =
              (greedyMatching ξ).assignment r := by rw [hIns ξ]
        exact ⟨y, hassignEq.symm.trans hassign⟩
      · intro h r hr
        rcases h r hr with ⟨y, hassign⟩
        have hassignEq :
            (greedyMatching (insertArrivals ins ξ)).assignment r =
              (greedyMatching ξ).assignment r := by rw [hIns ξ]
        exact ⟨y, hassignEq.trans hassign, by simp [ins]⟩
    have hprod : (∏ r ∈ S', (D.law' r).w (D.extendTarget o r)) =
        ∏ a ∈ S, (D.C.trimmed a).w (o a) := by
      dsimp [S']
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro a ha
      change (D.C.trimmed a).w (o a) = (D.C.trimmed a).w (o a)
      rfl
    change D.law.pr (fun ξ => matchesTargetsOrdinarily ins ξ S' (D.extendTarget o)) ≤
      (1 + (n : ℝ)⁻¹) * ∏ r ∈ S', (D.law' r).w (D.extendTarget o r) at hstep'
    rw [hevent, hprod] at hstep'
    exact hstep'
  · have hcollision : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ D.I.lab a (o a) = D.I.lab b (o b) := by
      classical
      by_contra hcoll
      apply hlabels
      intro a ha b hb hEq
      by_contra hne
      exact hcoll ⟨a, ha, b, hb, hne, hEq⟩
    let emb : R ↪ D.Row := Function.Embedding.inl
    let invalidMarks : ClockField D.mesh.ticks D.Row g D.Out → Prop := fun ξ =>
      ∃ e : RowLabel D.Row g, ∃ t : Fin D.mesh.ticks, ∃ v : D.Out e.1,
        ξ e = MeshClockValue.tick t v ∧ D.lab' e.1 v ≠ e.2
    have hmatchesValidFalse (ξ : ClockField D.mesh.ticks D.Row g D.Out)
        (hξ : matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o))
        (hvalid : ¬ invalidMarks ξ) : False := by
      rcases hcollision with ⟨a, ha, b, hb, hab, hlab⟩
      have hma : emb a ∈ S.map emb := Finset.mem_map.mpr ⟨a, ha, rfl⟩
      have hmb : emb b ∈ S.map emb := Finset.mem_map.mpr ⟨b, hb, rfl⟩
      rcases hξ (emb a) hma with ⟨ya, hya⟩
      rcases hξ (emb b) hmb with ⟨yb, hyb⟩
      change (greedyMatching ξ).assignment (emb a) = some (ya, o a) at hya
      change (greedyMatching ξ).assignment (emb b) = some (yb, o b) at hyb
      rcases greedyMatching_assignment_origin ξ (emb a) ya (o a) hya with ⟨ta, hta⟩
      rcases greedyMatching_assignment_origin ξ (emb b) yb (o b) hyb with ⟨tb, htb⟩
      have hla : D.lab' (emb a) (o a) = ya := by
        by_contra hne
        exact hvalid ⟨(emb a, ya), ta, o a, hta, hne⟩
      have hlb : D.lab' (emb b) (o b) = yb := by
        by_contra hne
        exact hvalid ⟨(emb b, yb), tb, o b, htb, hne⟩
      have hla' : D.I.lab a (o a) = ya := by
        change D.I.lab a (o a) = ya at hla
        exact hla
      have hlb' : D.I.lab b (o b) = yb := by
        change D.I.lab b (o b) = yb at hlb
        exact hlb
      have hyaEq : ya = yb := by
        calc
          ya = D.I.lab a (o a) := hla'.symm
          _ = D.I.lab b (o b) := hlab
          _ = yb := hlb'
      have hab' := greedyMatching_label_injective ξ (emb a) (emb b) ya (o a) (o b)
        hya (by rw [← hyaEq] at hyb; exact hyb)
      exact hab (emb.injective hab')
    have hsubsetInvalid : ∀ ξ,
        matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o) →
          invalidMarks ξ := by
      intro ξ hξ
      by_contra hnot
      exact hmatchesValidFalse ξ hξ hnot
    have hnull : D.law.pr
        invalidMarks = 0 := by
      simpa [invalidMarks, ClockData.law, ClockData.edgeLaw] using
        (invalid_marks_null (T := D.mesh.ticks) D.mesh.δ D.mesh.δ_nonneg D.mesh.δ_le_one
          D.law' D.lab')
    have hle : D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) ≤ 0 := by
      calc
        D.law.pr (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) ≤
            D.law.pr invalidMarks :=
          finProb_pr_mono D.law (by intro ξ hξ; exact hsubsetInvalid ξ hξ)
        _ = 0 := hnull
    have hnonneg := finProb_pr_nonneg D.law
      (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o))
    have hzero : D.law.pr
        (fun ξ => matchesTargets ξ (S.map Function.Embedding.inl) (D.extendTarget o)) = 0 :=
      le_antisymm hle hnonneg
    have hprod : 0 ≤ ∏ a ∈ S, (D.C.trimmed a).w (o a) :=
      Finset.prod_nonneg fun a ha => (D.C.trimmed a).nonneg (o a)
    rw [hzero]
    positivity

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
  classical
  rcases clock_constants B hB with ⟨_, n₁, hconst⟩
  obtain ⟨n₂, htarget⟩ := target_raw_bound B C_g hB
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn g hg R K _ _ _ Ω _ _ _ D S o hS
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hnreal, _, _, hLone⟩ := hconst n hn₁
  let T := D.targetRects S o
  let m := Fintype.card (↥T)
  let e : Fin m ≃ ↥T := (Fintype.equivFin (↥T)).symm
  let rect : Fin m → ClockField D.mesh.ticks D.Row g D.Out → Prop :=
    fun r ξ => ∀ a : S, ((e r).1 a).Event ξ
  let actR : Fin m → Finset (Endpoint D.Row g) :=
    fun r => Finset.univ.biUnion fun a : S => ((e r).1 a).active
  have hleafCard (τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out) (hτ : τ ∈ T) (a : S) :
      (τ a).active.card ≤ clockLnat B n := by
    change τ ∈ D.targetRects S o at hτ
    unfold ClockData.targetRects at hτ
    rcases Finset.mem_image.mp hτ with ⟨z, hz, hEq⟩
    have hgood := (Finset.mem_filter.mp hz).2
    have hgiant :
        (testExploration z D.scope' (D.test' (.singleton a.1)) (clockLnat B n)).giant = false :=
      (hgood a).1
    let roots := testRootEndpoints (g := g) D.scope' (D.test' (.singleton a.1))
    have hgiant' : (truncatedExploration z roots (clockLnat B n)).giant = false := by
      simpa [roots, testExploration, ClockData.test'] using hgiant
    have hcard := (truncatedExploration_card z roots (clockLnat B n)).2.1 hgiant'
    have hle : (testLeaf z D.scope' (D.test' (.singleton a.1)) (clockLnat B n)).active.card ≤
        clockLnat B n := by
      exact Nat.le_of_lt (by simpa [testLeaf, roots, explorationLeaf] using hcard)
    rw [← congrFun hEq a]
    exact hle
  have hactCard : ∀ r, ((actR r).card : ℝ) ≤ (n : ℝ) ^ B * clockL B n := by
    intro r
    have hcard : (actR r).card ≤ ∑ a : S, ((e r).1 a).active.card := by
      dsimp [actR]
      exact Finset.card_biUnion_le
    have hcard' : (actR r).card ≤ S.card * clockLnat B n := by
      calc
        (actR r).card ≤ ∑ a : S, ((e r).1 a).active.card := hcard
        _ ≤ ∑ _a : S, clockLnat B n := Finset.sum_le_sum fun a _ => hleafCard (e r).1 ((e r).2) a
        _ = S.card * clockLnat B n := by simp
    have hcardReal : ((actR r).card : ℝ) ≤ (S.card : ℝ) * (clockLnat B n : ℝ) := by
      exact_mod_cast hcard'
    calc
      ((actR r).card : ℝ) ≤ (S.card : ℝ) * clockL B n := by simpa [clockL] using hcardReal
      _ ≤ (n : ℝ) ^ B * clockL B n :=
        mul_le_mul_of_nonneg_right hS (Nat.cast_nonneg _)
  have prEq {A B : ClockField D.mesh.ticks D.Row g D.Out → Prop}
      (hAB : ∀ x, A x ↔ B x) : D.law.pr A = D.law.pr B := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hA : A x
    · have hB := (hAB x).mp hA
      simp [hA, hB]
    · have hB : ¬ B x := by intro h; exact hA ((hAB x).mpr h)
      simp [hA, hB]
  have hforcing : ∀ r (S' : Finset D.Bad),
      (∀ j ∈ S', Disjoint (actR r) (D.badAct j)) →
        D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) ≤
          D.law.pr (rect r) * D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x) := by
    intro r S' hdis
    change D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) ≤
      D.law.pr (rect r) * D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x)
    by_cases hp0 : D.law.pr (rect r) = 0
    · calc
        D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) ≤ D.law.pr (rect r) :=
          finProb_pr_mono D.law (by intro x hx; exact hx.1)
        _ = 0 := hp0
        _ = D.law.pr (rect r) * D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x) := by rw [hp0]; ring
    · have hpos : 0 < D.law.pr (rect r) := by
        have hnonneg := finProb_pr_nonneg D.law (rect r)
        by_contra h
        exact hp0 (le_antisymm (le_of_not_gt h) hnonneg)
      have hex : ∃ ξ₀, rect r ξ₀ := by
        by_contra h
        have hall : ∀ x, ¬ rect r x := by simpa using h
        have hz : D.law.pr (rect r) = 0 := by
          unfold FinProb.pr
          simp [hall]
        exact hp0 hz
      obtain ⟨ξ₀, hξ₀⟩ := hex
      let τ := (e r).1
      have h₀ : ∀ a : S, (τ a).Event ξ₀ := hξ₀
      obtain ⟨M, hM, hMact⟩ := clockLeaf_meet (fun a : S => τ a) ξ₀ h₀
      have hME : ∀ x, M.Event x ↔ rect r x := by
        intro x
        simpa [rect, τ] using hM x
      have hMpositive : 0 < D.law.pr M.Event := by
        have hpr : D.law.pr (rect r) = D.law.pr M.Event :=
          prEq (fun x => (hME x).symm)
        rw [← hpr]
        exact hpos
      let badList : List (ClockLeaf D.mesh.ticks D.Row g D.Out) := S'.toList.map fun j => j.2.1
      have hnonneighbor : ∀ L ∈ badList, M.Nonneighbor L := by
        intro L hL
        simp only [badList, List.mem_map] at hL
        rcases hL with ⟨j, hj, rfl⟩
        change Disjoint M.active (j.2.1).active
        apply Finset.disjoint_left.mpr
        intro v hvM hvj
        have hactEq : actR r = M.active := by
          dsimp [actR]
          simpa [τ] using hMact.symm
        have hvR : v ∈ actR r := by rw [hactEq]; exact hvM
        have hvBad : v ∈ D.badAct j := by change v ∈ (j.2.1).active; exact hvj
        exact Finset.disjoint_left.mp (hdis j (Finset.mem_toList.mp hj)) hvR hvBad
      have havoid (x : ClockField D.mesh.ticks D.Row g D.Out) :
          avoidsLeaves badList x ↔ ∀ j ∈ S', ¬ D.badEvent j x := by
        constructor
        · intro h j hj
          apply h (j.2.1)
          apply List.mem_map.mpr
          exact ⟨j, Finset.mem_toList.mpr hj, rfl⟩
        · intro h L hL
          simp only [badList, List.mem_map] at hL
          rcases hL with ⟨j, hj, rfl⟩
          exact h j (Finset.mem_toList.mp hj)
      have hforce := leaf_forcing_coupling D.edgeLaw M badList hMpositive hnonneighbor
      change D.law.pr (fun x => M.Event x ∧ avoidsLeaves badList x) / D.law.pr M.Event ≤
        D.law.pr (avoidsLeaves badList) at hforce
      have hmul := (div_le_iff₀ hMpositive).mp hforce
      have havoidEq : D.law.pr (avoidsLeaves badList) =
          D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x) := by
        apply prEq
        intro x
        exact havoid x
      have hrectEq : D.law.pr (fun x => M.Event x ∧ avoidsLeaves badList x) =
          D.law.pr (fun x => rect r x ∧ avoidsLeaves badList x) := by
        apply prEq
        intro x
        constructor
        · intro h
          exact ⟨(hME x).mp h.1, h.2⟩
        · intro h
          exact ⟨(hME x).mpr h.1, h.2⟩
      have hrectAvoidEq : D.law.pr (fun x => rect r x ∧ avoidsLeaves badList x) =
          D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) := by
        apply prEq
        intro x
        constructor
        · intro h
          exact ⟨h.1, (havoid x).mp h.2⟩
        · intro h
          exact ⟨h.1, (havoid x).mpr h.2⟩
      have hpr := prEq (fun x => (hME x).symm)
      rw [hrectEq, hrectAvoidEq, havoidEq, ← hpr] at hmul
      change D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) ≤
        D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x) * D.law.pr (rect r) at hmul
      calc
        D.law.pr (fun x => rect r x ∧ ∀ j ∈ S', ¬ D.badEvent j x) ≤
            D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x) * D.law.pr (rect r) := hmul
        _ = D.law.pr (rect r) * D.law.pr (fun x => ∀ j ∈ S', ¬ D.badEvent j x) := mul_comm _ _
  have hcover : ∀ x, (∀ i, ¬ D.badEvent i x) → (∀ a ∈ S, D.out x a = o a) →
      ∃ r, rect r x := by
    intro x hx ho
    let τ : S → ClockLeaf D.mesh.ticks D.Row g D.Out :=
      fun a => testLeaf x D.scope' (D.test' (.singleton a.1)) (clockLnat B n)
    have hτ : τ ∈ T := D.targetRect_cover S o x hx ho
    let r : Fin m := e.symm ⟨τ, hτ⟩
    refine ⟨r, ?_⟩
    intro a
    change ((e r).1 a).Event x
    have her : e r = ⟨τ, hτ⟩ := e.apply_symm_apply ⟨τ, hτ⟩
    rw [her]
    have hself : (τ a).Event x := by
      dsimp [τ]
      exact (explorationLeaf_event_iff x x
        (testRootEndpoints (g := g) D.scope' (D.test' (.singleton a.1))) (clockLnat B n)).2 ⟨rfl, rfl⟩
    exact hself
  have hsumEq : (∑ r : Fin m, D.law.pr (rect r)) =
      ∑ τ ∈ T, D.law.pr (fun x => ∀ a, (τ a).Event x) := by
    have hsum := Fintype.sum_equiv e (fun r => D.law.pr (rect r))
      (fun τ : ↥T => D.law.pr (fun x => ∀ a, (τ.1 a).Event x)) (by intro r; simp [rect])
    calc
      (∑ r : Fin m, D.law.pr (rect r)) =
          ∑ τ : ↥T, D.law.pr (fun x => ∀ a, (τ.1 a).Event x) := by simpa using hsum
      _ = ∑ τ ∈ T, D.law.pr (fun x => ∀ a, (τ a).Event x) := by
          simpa using (Finset.sum_attach T (fun τ => D.law.pr (fun x => ∀ a, (τ a).Event x)))
  have hraw := htarget n hn₂ g hg D S o hS
  refine ⟨m, rect, actR, hactCard, hforcing, hcover, ?_⟩
  calc
    ∑ r : Fin m, D.law.pr (rect r) =
        ∑ τ ∈ T, D.law.pr (fun x => ∀ a, (τ a).Event x) := hsumEq
    _ ≤ D.law.pr (fun x => matchesTargets x (S.map Function.Embedding.inl) (D.extendTarget o)) :=
      D.targetRects_sum_le S o
    _ ≤ (1 + (n : ℝ)⁻¹) * ∏ a ∈ S, (D.C.trimmed a).w (o a) := hraw

/-- L3.10h-empty (TeX 03:797, "an empty assignment may be ignored"): with no real rows the one-point space is a
raw sampler (no bad events; every predicate has empty scope and is unsatisfiable). -/
theorem rawSampler_of_isEmpty {n g : ℕ} {R K : Type} [Fintype R] [DecidableEq R] [Fintype K]
    {Ω : R → Type} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)] [IsEmpty R]
    (I : SamplingInstance n g R K Ω) (q : ∀ a, FinProb (Ω a)) (B A P L κ η : ℝ)
    (hn : 2 ≤ n) (hP : 0 < P) (hI : I.Admissible B A P) (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hη : 0 ≤ η) :
    Nonempty (RawSampler I q B L κ η) := by
  classical
  refine ⟨{
    Space := Unit
    law := ⟨fun _ => 1, (by intro; norm_num), (by simp)⟩
    out := fun _ a => isEmptyElim a
    Vertex := Empty
    Bad := Empty
    bad := fun i _ => Empty.elim i
    act := fun i => Empty.elim i
    act_nonempty := by intro i; exact Empty.elim i
    act_card := by intro i; exact Empty.elim i
    incidence := by intro v; cases v
    forcing := by intro i; exact Empty.elim i
    good := by
      intro x hx
      constructor
      · intro a
        exact isEmptyElim a
      · intro k
        have hscope : I.scope k = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          exact isEmptyElim a
        exact empty_scope_failure_false I B A P hI hn hP k hscope (fun a => isEmptyElim a)
    target := by
      intro S o hS
      have hSempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact isEmptyElim a
      subst S
      refine ⟨1, (fun _ _ => True), (fun _ => ∅), ?_, ?_, ?_, ?_⟩
      · intro r
        simpa using (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) B) hL)
      · intro r S' hdis
        simp [FinProb.pr]
      · intro x hbad ho
        exact ⟨0, trivial⟩
      · simp [FinProb.pr]
        linarith
  }⟩

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
