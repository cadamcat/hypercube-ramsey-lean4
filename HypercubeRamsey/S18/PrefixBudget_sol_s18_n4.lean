import HypercubeRamsey.S18.Prefix_sol_s18_n4
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical Filter
open scoped BigOperators Topology

/-- The exponent available after replay dominates both its pattern count
and the terminal Markov factor. The horizon is the prescribed log-square
number of rounds. -/
theorem prefixExponentBudgetEventually (T : Stage) (P M c δ : ℝ)
    (hP : 0 ≤ P) (hM : 0 ≤ M) (hc : 0 < c) (hδ : δ < c) :
    ∀ᶠ k in atTop,
      let n : ℝ := T.S.n k
      let Ts : ℝ := initialResamplingRounds T k
      Real.rpow n δ + M * (Ts + 1) * Real.log n +
        P * Ts / 3 * Real.log n + Real.log 4 ≤ Real.rpow n c := by
  let A : ℝ := 3 * M + 2 * P / 3 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hlog : ∀ᶠ k in atTop, 1 ≤ Real.log (T.S.n k : ℝ) :=
    (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1
  have hgap : ∀ᶠ k in atTop, 4 ≤ Real.rpow (T.S.n k : ℝ) (c - δ) :=
    ((tendsto_rpow_atTop (by linarith : 0 < c - δ)).comp hn).eventually_ge_atTop 4
  have hconst : ∀ᶠ k in atTop, 4 * Real.log 4 ≤ Real.rpow (T.S.n k : ℝ) c :=
    ((tendsto_rpow_atTop hc).comp hn).eventually_ge_atTop _
  have hsmall := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hc).def
    (by positivity : 0 < 1 / (4 * A))
  have hpoly := hn.eventually hsmall
  filter_upwards [hlog, hgap, hconst, hpoly, T.S.n_tendsto.eventually_ge_atTop 1]
    with k hlog hgap hconst hpoly hn1
  dsimp only
  let n : ℝ := T.S.n k
  let L : ℝ := Real.log n
  let Ts : ℝ := initialResamplingRounds T k
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast (show 0 < T.S.n k by omega)
  have hL : 1 ≤ L := hlog
  have hTs : Ts ≤ L ^ 2 + 1 := by
    exact (Nat.ceil_lt_add_one (sq_nonneg L)).le
  have hTs1 : Ts + 1 ≤ 3 * L ^ 2 := by nlinarith
  have hTs2 : Ts ≤ 2 * L ^ 2 := by nlinarith
  have hδcost : Real.rpow n δ ≤ Real.rpow n c / 4 := by
    have hmul : Real.rpow n δ * 4 ≤ Real.rpow n δ * Real.rpow n (c - δ) :=
      mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hnpos.le δ)
    simp only [Real.rpow_eq_pow] at hmul
    rw [← Real.rpow_add hnpos] at hmul
    have he : δ + (c - δ) = c := by ring
    rw [he] at hmul
    simp only [Real.rpow_eq_pow]
    linarith
  have hpolycost : A * L ^ 3 ≤ Real.rpow n c / 4 := by
    have hp : L ^ 3 ≤ (1 / (4 * A)) * Real.rpow n c := by
      change ‖L ^ (3 : ℝ)‖ ≤ (1 / (4 * A)) * ‖n ^ c‖ at hpoly
      simpa only [Real.rpow_ofNat, Real.norm_of_nonneg (by positivity : 0 ≤ L ^ 3),
        Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le c), Real.rpow_eq_pow] using hpoly
    have hh := mul_le_mul_of_nonneg_left hp hA.le
    have he : A * (1 / (4 * A)) = 1 / 4 := by field_simp
    rw [← mul_assoc, he] at hh
    nlinarith
  have hrest : M * (Ts + 1) * L + P * Ts / 3 * L ≤ A * L ^ 3 := by
    have hLm : 0 ≤ L := by linarith
    have hm := mul_le_mul_of_nonneg_right hTs1 (mul_nonneg hM hLm)
    have hp := mul_le_mul_of_nonneg_right hTs2 (mul_nonneg hP hLm)
    dsimp [A]
    nlinarith [pow_nonneg hLm 3]
  have hconst' : Real.log 4 ≤ Real.rpow n c / 4 := by linarith
  have hnonneg : 0 ≤ Real.rpow n c := Real.rpow_nonneg hnpos.le c
  change Real.rpow n δ + M * (Ts + 1) * L + P * Ts / 3 * L + Real.log 4 ≤ Real.rpow n c
  linarith

/-- A replay count bounded by n^(M(Ts+1)) pays the exponential transfer
cost, including the Markov factor, within half the terminal budget. -/
theorem prefixPatternBudget (n : ℝ) (hn : 0 < n) (P M Ts c δ count : ℝ)
    (hcount : count ≤ Real.rpow n (M * (Ts + 1)))
    (hbudget : Real.rpow n δ + M * (Ts + 1) * Real.log n +
      P * Ts / 3 * Real.log n + Real.log 4 ≤ Real.rpow n c) :
    (Real.exp (-Real.rpow n δ))⁻¹ * (count * (2 * Real.exp (-Real.rpow n c))) ≤
      Real.rpow n (-(P * Ts / 3)) / 2 := by
  have hleft : (Real.exp (-Real.rpow n δ))⁻¹ *
      (count * (2 * Real.exp (-Real.rpow n c))) ≤
      2 * Real.exp (Real.rpow n δ + M * (Ts + 1) * Real.log n - Real.rpow n c) := by
    calc
      _ ≤ (Real.exp (-Real.rpow n δ))⁻¹ *
          (Real.rpow n (M * (Ts + 1)) * (2 * Real.exp (-Real.rpow n c))) := by
        gcongr
      _ = _ := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_def_of_pos hn (M * (Ts + 1)), ← Real.exp_neg, neg_neg]
        rw [mul_comm (Real.log n) (M * (Ts + 1))]
        simp only [Real.exp_add, Real.exp_sub, Real.exp_neg]
        ring
  have he : Real.rpow n δ + M * (Ts + 1) * Real.log n - Real.rpow n c ≤
      -(P * Ts / 3) * Real.log n - Real.log 4 := by linarith
  calc
    _ ≤ 2 * Real.exp (Real.rpow n δ + M * (Ts + 1) * Real.log n - Real.rpow n c) := hleft
    _ ≤ 2 * Real.exp (-(P * Ts / 3) * Real.log n - Real.log 4) := by gcongr
    _ = Real.rpow n (-(P * Ts / 3)) / 2 := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_def_of_pos hn (-(P * Ts / 3)), Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      rw [mul_comm (Real.log n) (-(P * Ts / 3))]
      ring

theorem closureHalfBudget (n P Ts : ℝ) (hn : 2 ≤ n) (hP : 6 ≤ P) (hTs : 1 ≤ Ts) :
    Real.rpow n (-(P * Ts / 2)) ≤ Real.rpow n (-(P * Ts / 3)) / 2 := by
  have hnpos : 0 < n := by linarith
  have hPT : 6 ≤ P * Ts := by nlinarith
  have hexp : -(P * Ts / 6) ≤ (-1 : ℝ) := by linarith
  have hsmall : Real.rpow n (-(P * Ts / 6)) ≤ 1 / 2 := by
    calc
      _ ≤ Real.rpow n (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
      _ = n⁻¹ := by simpa only [Real.rpow_eq_pow] using Real.rpow_neg_one n
      _ ≤ 1 / 2 := by
        rw [← one_div]
        exact (div_le_iff₀ hnpos).2 (by linarith)
  have heq : -(P * Ts / 2) = -(P * Ts / 3) + -(P * Ts / 6) := by ring
  simp only [Real.rpow_eq_pow]
  rw [heq, Real.rpow_add hnpos]
  exact (mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnpos.le _)).trans_eq (by ring)

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem replayMarked_polynomial (D : S18.LateData hPT) (hD : D.Spec)
    (X : S18.CriticalTransferData D) (hn : 2 ≤ T.S.n k) :
    (S18.replayMarked D X.criticalCells).card ≤ T.S.n k ^ (2 * κ.Ac + 8) := by
  let n := T.S.n k
  let d := n ^ (κ.Ac + 4)
  have hd : ∀ v, (Finset.univ.filter fun w => D.encoding.events.Adjacent w v).card ≤ d := by
    intro v
    have he : (Finset.univ.filter fun w => D.encoding.events.Adjacent w v) =
        Finset.univ.filter fun w => D.encoding.events.Adjacent v w := by
      apply Finset.ext
      intro w
      constructor <;> intro hw <;> apply Finset.mem_filter.mpr <;>
        refine ⟨Finset.mem_univ _, ?_⟩
      · rcases (Finset.mem_filter.mp hw).2 with ⟨hne, hdis⟩
        exact ⟨hne.symm, fun h => hdis (disjoint_comm.mp h)⟩
      · rcases (Finset.mem_filter.mp hw).2 with ⟨hne, hdis⟩
        exact ⟨hne.symm, fun h => hdis (disjoint_comm.mp h)⟩
    rw [he]
    exact eventDegreeBound D hD hn v
  have hn2 : n + 1 ≤ n ^ 2 := by dsimp [n]; nlinarith
  have hpow : 1 ≤ n ^ (κ.Ac + 4) := Nat.one_le_pow _ _ (by omega)
  have hd1 : d + 1 ≤ n ^ (κ.Ac + 5) := by
    rw [show κ.Ac + 5 = (κ.Ac + 4) + 1 by omega, pow_succ]
    dsimp [d]
    nlinarith
  calc
    _ ≤ X.criticalCells.card * (n ^ κ.Ac * (n + 1)) * (d + 1) := replayMarked_card_le D hD _ d hd
    _ ≤ n * (n ^ κ.Ac * n ^ 2) * n ^ (κ.Ac + 5) :=
      Nat.mul_le_mul (Nat.mul_le_mul (criticalCells_card_le D X) (Nat.mul_le_mul_left _ hn2)) hd1
    _ = n ^ (2 * κ.Ac + 8) := by
      simp only [pow_add, pow_mul]
      ring

theorem replayPatternCount_polynomial (D : S18.LateData hPT) (hD : D.Spec)
    (X : S18.CriticalTransferData D) (hn : 2 ≤ T.S.n k) (hTs : D.encoding.Ts ≤ T.S.n k) :
    (boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts).card ≤
      T.S.n k ^ ((2 * κ.Ac + 11) * (D.encoding.Ts + 1)) := by
  let n := T.S.n k
  let Ts := D.encoding.Ts
  have hbase : max 1 ((S18.replayMarked D X.criticalCells).card * Ts) ≤ n ^ (2 * κ.Ac + 9) := by
    apply max_le
    · exact Nat.one_le_pow _ _ (by omega)
    · calc
        _ ≤ n ^ (2 * κ.Ac + 8) * n := Nat.mul_le_mul (replayMarked_polynomial D hD X hn) hTs
        _ = _ := by rw [← pow_succ]
  have hTs1 : Ts + 1 ≤ n ^ 2 := by
    have hnplus : n + 1 ≤ n ^ 2 := by dsimp [n]; nlinarith
    exact (Nat.add_le_add_right hTs 1).trans hnplus
  calc
    _ ≤ (Ts + 1) * (max 1 ((S18.replayMarked D X.criticalCells).card * Ts)) ^ Ts :=
      boundedOccurrencePatterns_card _ _
    _ ≤ n ^ 2 * (n ^ (2 * κ.Ac + 9)) ^ Ts := Nat.mul_le_mul hTs1 (Nat.pow_le_pow_left hbase Ts)
    _ = n ^ (2 + (2 * κ.Ac + 9) * Ts) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem resamplingRounds_le_n (T : Stage) :
    ∀ᶠ k in atTop, initialResamplingRounds T k ≤ T.S.n k := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).def (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hn.eventually hsmall, T.S.n_tendsto.eventually_ge_atTop 2] with k hs hk
  have hn0 : 0 ≤ (T.S.n k : ℝ) := Nat.cast_nonneg _
  have hlog : Real.log (T.S.n k : ℝ) ^ 2 ≤ (T.S.n k : ℝ) / 2 := by
    simpa [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hn0, div_eq_mul_inv, mul_comm] using hs
  apply Nat.ceil_le.mpr
  nlinarith

theorem validPrefixReplayBudgetEventually (hκ : κ.Admissible) (T : Stage) (c δ : ℝ)
    (hc : 0 < c) (hδ : δ < c) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → ∀ X : S18.CriticalTransferData D,
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 2)) +
        (Real.exp (-Real.rpow (T.S.n k : ℝ) δ))⁻¹ *
          ((boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts).card *
            (2 * Real.exp (-Real.rpow (T.S.n k : ℝ) c))) ≤
              Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  have hP : 6 ≤ (κ.P : ℝ) := by exact_mod_cast (show 6 ≤ κ.P by have := hκ.P_big.2; omega)
  filter_upwards [prefixExponentBudgetEventually T κ.P (2 * κ.Ac + 11) c δ
      (Nat.cast_nonneg _) (by positivity) hc hδ,
    resamplingRounds_le_n T, T.S.n_tendsto.eventually_ge_atTop 8] with k hb hTs hn
  intro PT hPT D hD X
  have hnR : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast (show 2 ≤ T.S.n k by omega)
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hlog : 1 ≤ Real.log (T.S.n k : ℝ) := by
    have hlog8 : 1 ≤ Real.log (8 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num at h ⊢
      linarith
    exact hlog8.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hTs1 : 1 ≤ (D.encoding.Ts : ℝ) := by
    have hceil : Real.log (T.S.n k : ℝ) ^ 2 ≤ (D.encoding.Ts : ℝ) := by
      rw [D.encoding.Ts_eq]; exact Nat.le_ceil _
    nlinarith
  have hcount := replayPatternCount_polynomial D hD X (by omega)
    (by simpa only [D.encoding.Ts_eq, initialResamplingRounds] using hTs)
  have hcountR : ((boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts).card : ℝ) ≤
      Real.rpow (T.S.n k : ℝ) ((2 * (κ.Ac : ℝ) + 11) * ((D.encoding.Ts : ℝ) + 1)) := by
    have hc' : ((boundedOccurrencePatterns (S18.replayMarked D X.criticalCells) D.encoding.Ts).card : ℝ) ≤
        (T.S.n k : ℝ) ^ ((2 * κ.Ac + 11) * (D.encoding.Ts + 1)) := by exact_mod_cast hcount
    have he : ((2 * (κ.Ac : ℝ) + 11) * ((D.encoding.Ts : ℝ) + 1)) =
        (((2 * κ.Ac + 11) * (D.encoding.Ts + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_eq_pow, Real.rpow_natCast]
    exact hc'
  have hbudget := hb
  change Real.rpow (T.S.n k : ℝ) δ + (2 * (κ.Ac : ℝ) + 11) *
      ((initialResamplingRounds T k : ℝ) + 1) * Real.log (T.S.n k : ℝ) +
      (κ.P : ℝ) * initialResamplingRounds T k / 3 * Real.log (T.S.n k : ℝ) + Real.log 4 ≤
        Real.rpow (T.S.n k : ℝ) c at hbudget
  have hround : D.encoding.Ts = initialResamplingRounds T k := D.encoding.Ts_eq
  rw [← hround] at hbudget
  have hp := prefixPatternBudget (T.S.n k : ℝ) hnpos κ.P (2 * (κ.Ac : ℝ) + 11)
    D.encoding.Ts c δ _ hcountR hbudget
  have hcl := closureHalfBudget (T.S.n k : ℝ) κ.P D.encoding.Ts hnR hP hTs1
  linarith

end HypercubeRamsey.Lane_sol_s18_n4
