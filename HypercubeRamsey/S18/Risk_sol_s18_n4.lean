import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

/-- Restore the closure exception before charging the truncated replay integral. -/
theorem truncatedMarkov {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (gate closure : Ω → Prop) (f : Ω → ℝ)
    (η : ℝ) (hη : 0 < η) (hf : ∀ x, 0 ≤ f x) :
    P.pr (fun x => gate x ∧ η < f x) ≤ P.pr (fun x => gate x ∧ closure x) +
      η⁻¹ * P.E (fun x => if gate x ∧ ¬ closure x then f x else 0) := by
  have hpoint : ∀ x, (if gate x ∧ η < f x then (1 : ℝ) else 0) ≤
      (if gate x ∧ closure x then 1 else 0) +
        η⁻¹ * (if gate x ∧ ¬ closure x then f x else 0) := by
    intro x
    by_cases hg : gate x
    · by_cases hc : closure x
      · simp only [hg, hc, and_self, not_true_eq_false, and_false, ite_true, ite_false, mul_zero, add_zero]
        split_ifs <;> norm_num
      · simp only [hg, hc, true_and, ite_false, not_false_eq_true, and_self, ite_true, zero_add]
        by_cases hfx : η < f x
        · simp only [hfx, ite_true]
          calc
            (1 : ℝ) ≤ f x / η := (le_div_iff₀ hη).2 (by simpa using hfx.le)
            _ = η⁻¹ * f x := by ring
        · simp only [hfx, ite_false]
          exact mul_nonneg (inv_nonneg.mpr hη.le) (hf x)
    · simp [hg]
  unfold FinLaw.pr FinLaw.E
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  have h := mul_le_mul_of_nonneg_left (hpoint x) (P.nonneg x)
  by_cases hg : gate x <;> by_cases hc : closure x <;> by_cases hfx : η < f x <;>
    simpa [hg, hc, hfx, mul_add, mul_assoc, mul_left_comm] using h

/-- A cover by bounded replay patterns controls the whole truncated integral. -/
theorem patternCoverExpectation {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (patterns : Finset I) (truncated : Ω → Prop)
    (consistent : I → Ω → Prop) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hcover : ∀ x, truncated x → ∃ i ∈ patterns, consistent i x)
    (cost : ℝ) (hcost : ∀ i ∈ patterns,
      P.E (fun x => if consistent i x then f x else 0) ≤ cost) :
    P.E (fun x => if truncated x then f x else 0) ≤ (patterns.card : ℝ) * cost := by
  have hpoint : ∀ x, (if truncated x then f x else 0) ≤
      ∑ i ∈ patterns, if consistent i x then f x else 0 := by
    intro x
    by_cases ht : truncated x
    · obtain ⟨i, hi, hx⟩ := hcover x ht
      simp only [ht, ite_true]
      have h := Finset.single_le_sum (f := fun j => if consistent j x then f x else 0)
        (fun j _ => by split_ifs <;> simp [hf]) hi
      simpa [hx] using h
    · simp only [ht, ite_false]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hf])
  calc
    P.E (fun x => if truncated x then f x else 0) ≤
        P.E (fun x => ∑ i ∈ patterns, if consistent i x then f x else 0) := by
      unfold FinLaw.E
      exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (P.nonneg x))
    _ = ∑ i ∈ patterns, P.E (fun x => if consistent i x then f x else 0) := by
      unfold FinLaw.E
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ patterns, cost := Finset.sum_le_sum hcost
    _ = (patterns.card : ℝ) * cost := by simp

 theorem riskBoundFromReplayPatterns {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (gate closure : Ω → Prop) (patterns : Finset I)
    (consistent : I → Ω → Prop) (f : Ω → ℝ) (η : ℝ)
    (hη : 0 < η) (hf : ∀ x, 0 ≤ f x)
    (hcover : ∀ x, gate x ∧ ¬ closure x → ∃ i ∈ patterns, consistent i x)
    (closureCost patternCost bound : ℝ)
    (hclosure : P.pr (fun x => gate x ∧ closure x) ≤ closureCost)
    (hpattern : ∀ i ∈ patterns, P.E (fun x => if consistent i x then f x else 0) ≤ patternCost)
    (hbudget : closureCost + η⁻¹ * ((patterns.card : ℝ) * patternCost) ≤ bound) :
    P.pr (fun x => gate x ∧ η < f x) ≤ bound := by
  have he : P.E (fun x => if gate x ∧ ¬ closure x then f x else 0) ≤
      (patterns.card : ℝ) * patternCost := by
    convert patternCoverExpectation P patterns (fun x => gate x ∧ ¬ closure x)
      consistent f hf hcover patternCost hpattern using 1
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hg : gate x <;> by_cases hc : closure x <;> simp [hg, hc]
  exact (truncatedMarkov P gate closure f η hη hf).trans
    ((add_le_add hclosure (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hη.le))).trans hbudget)

theorem initialProbabilityZeroOfImpossible
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (pin : Option (S18.SlotPin D))
    (F : D.encoding.InitInput → Prop) (hF : ∀ x, ¬ F x) :
    S18.initialProbability D pin F = 0 := by
  cases pin with
  | none => simp [S18.initialProbability, FinLaw.pr, hF]
  | some p => simp [S18.initialProbability, FinLaw.pr, hF]

 theorem invalidPrefixTerminalPinnedBound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (F : S18.LateEvent D) (hkind : F.1.val = 1) (hvalid : ¬ D.prefixValid F.2)
    (pin : Option (S18.SlotPin D)) :
    S18.initialProbability D pin (S18.terminalFailure D δ (.inr (.inr F))) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  have hfailure : S18.lateFailure D F = fun _ => False := by
    funext full
    apply propext
    simp [S18.lateFailure, S18.LateData.prefixFailure, hkind, hvalid]
  have hfalse : ∀ x, ¬ S18.terminalFailure D δ (.inr (.inr F)) x := by
    intro x hbad
    have hp : D.pLate F x = 0 := by
      simp [S18.LateData.pLate, hfailure, FinLaw.pr]
    exact (not_lt_of_ge (Real.exp_pos _).le) (hp ▸ hbad.2)
  rw [initialProbabilityZeroOfImpossible D pin _ hfalse]
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem replayRounds_prefix_eq
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (marked : Finset (Pos T k))
    (pattern pattern' : ℕ → Finset (Pos T k)) (x : D.encoding.InitInput)
    (t : ℕ) (hpattern : ∀ s < t, pattern s = pattern' s) :
    S18.replayRounds D marked pattern x t = S18.replayRounds D marked pattern' x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprev := ih (fun s hs => hpattern s (Nat.lt_succ_of_lt hs))
      simp only [S18.replayRounds, hprev, hpattern t (Nat.lt_succ_self t)]

noncomputable def forcedReplayRisk
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (critical : Finset D.geom.Cell)
    (pattern : ℕ → Finset (Pos T k)) (F : S18.LateEvent D) (x : D.encoding.InitInput) : ℝ :=
  (D.encoding.kernels.refRun
    (S18.replayRounds D (S18.replayMarked D critical) pattern x D.encoding.Ts).1).pr
      (S18.lateFailure D F)

/-- A finite occurrence list identifies the actual risk with the total forced replay. -/
theorem lateRisk_eq_forcedReplay
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (hReplay : S18.ReplayFacts D)
    (critical : Finset D.geom.Cell) (pattern : ℕ → Finset (Pos T k))
    (F : S18.LateEvent D) (x : D.encoding.InitInput)
    (hpattern : ∀ s < D.encoding.Ts,
      pattern s = S18.actualPattern D (S18.replayMarked D critical) x s) :
    D.pLate F x = forcedReplayRisk D critical pattern F x := by
  have he := replayRounds_prefix_eq D (S18.replayMarked D critical) pattern
    (S18.actualPattern D (S18.replayMarked D critical) x) x D.encoding.Ts hpattern
  rw [hReplay.1] at he
  unfold S18.LateData.pLate forcedReplayRisk LateEncoding.initialState ListEvent.resample
  rw [he]

/-- Enlarge a fixed-pattern integral only after replacing its state by the total replay.
Typicality can then be retained without imposing the pattern on the replay inputs. -/
theorem forcedReplayIntegralEnlargement
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (hReplay : S18.ReplayFacts D)
    (P : FinLaw D.encoding.InitInput) (critical : Finset D.geom.Cell)
    (pattern : ℕ → Finset (Pos T k)) (F : S18.LateEvent D)
    (consistent retained : D.encoding.InitInput → Prop)
    (hpattern : ∀ x, consistent x → ∀ s < D.encoding.Ts,
      pattern s = S18.actualPattern D (S18.replayMarked D critical) x s)
    (hretain : ∀ x, consistent x → retained x) :
    P.E (fun x => if consistent x then D.pLate F x else 0) ≤
      P.E (fun x => if retained x then forcedReplayRisk D critical pattern F x else 0) := by
  unfold FinLaw.E
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (P.nonneg x)
  by_cases hc : consistent x
  · simp only [hc, hretain x hc, ite_true]
    exact (lateRisk_eq_forcedReplay D hReplay critical pattern F x (hpattern x hc)).le
  · simp only [hc, ite_false]
    split_ifs
    · unfold forcedReplayRisk FinLaw.pr
      exact Finset.sum_nonneg (fun full _ => by split_ifs <;> simp [FinLaw.nonneg])
    · exact le_rfl

end HypercubeRamsey.Lane_sol_s18_n4
