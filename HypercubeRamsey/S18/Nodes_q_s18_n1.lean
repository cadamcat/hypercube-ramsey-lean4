import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.Lane_q_s18_n1

open scoped BigOperators

private theorem law_eq_of_weights {N : ℕ} {μ ν : Law N}
    (h : ∀ x, μ.w x = ν.w x) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

private theorem normalize_indicator_eq_cond {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : HypercubeRamsey.S18.LateData hPT)
    (μ : Law (T.S.N k)) (A : Finset (Fin (T.S.N k)))
    (hA : 0 < ∑ x ∈ A, μ.w x) :
    D.normalize (fun x => μ.w x * (if x ∈ A then (1 : ℝ) else 0)) = μ.cond A hA := by
  classical
  have hmass : (∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0)) =
      ∑ x ∈ A, μ.w x := by
    simp [Finset.sum_ite_mem]
  have hnonneg : ∀ x, 0 ≤ μ.w x * (if x ∈ A then (1 : ℝ) else 0) := by
    intro x
    split_ifs with hx
    · exact mul_nonneg (μ.nonneg x) (by norm_num)
    · simp
  have hpos : 0 < ∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0) := by
    rw [hmass]
    exact hA
  have hbranch :
      (∀ x, 0 ≤ μ.w x * (if x ∈ A then (1 : ℝ) else 0)) ∧
        0 < ∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0) := ⟨hnonneg, hpos⟩
  apply law_eq_of_weights
  intro x
  simp only [HypercubeRamsey.S18.LateData.normalize, dif_pos hbranch]
  simp only [Law.cond, Law.restrict]
  by_cases hx : x ∈ A <;> simp [hx]

/-- The finite reverse geometric sum is bounded by the infinite geometric sum. -/
theorem finite_reverse_geometric_sum_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (r : ℕ) :
    (∑ j : Fin r, q ^ (r - j.val)) ≤ 1 / (1 - q) := by
  let S : ℕ → ℝ := fun r => ∑ j : Fin r, q ^ (r - j.val)
  have hform : ∀ r, S r * (1 - q) = q - q ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [S]
    | succ r ih =>
      have hrec : S (r + 1) = q ^ (r + 1) + S r := by
        dsimp [S]
        rw [Fin.sum_univ_succ]
        simp
      rw [hrec]
      calc
        (q ^ (r + 1) + S r) * (1 - q) =
            q ^ (r + 1) * (1 - q) + (q - q ^ (r + 1)) := by rw [add_mul, ih]
        _ = q - q ^ (r + 1) * q := by ring
        _ = q - q ^ (r + 2) := by
          congr 2
  have hden : 0 < 1 - q := by linarith
  have hnum : q - q ^ (r + 1) ≤ 1 := by
    have hp : 0 ≤ q ^ (r + 1) := pow_nonneg hq0.le _
    linarith
  apply (le_div_iff₀ hden).2
  change S r * (1 - q) ≤ 1
  rw [hform r]
  exact hnum

/-- The losses from successive hit conditioning are bounded by twice the
corresponding power of two when their total error is at most `log 2 / 12`. -/
theorem reciprocal_survival_product_le {r : ℕ} (e : Fin r → ℝ)
    (he0 : ∀ i, 0 ≤ e i) (he12 : ∀ i, e i ≤ 1 / 12)
    (hsum : (∑ i, e i) ≤ Real.log 2 / 12) :
    (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤ 2 * (2 : ℝ) ^ r := by
  have hfactor (i : Fin r) : (1 / 2 - 3 * e i)⁻¹ ≤ 2 * Real.exp (12 * e i) := by
    let x : ℝ := 6 * e i
    have hx0 : 0 ≤ x := by dsimp [x]; exact mul_nonneg (by norm_num) (he0 i)
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      nlinarith [he12 i]
    have hden : 0 < 1 - x := by linarith
    have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      apply (inv_le_iff_one_le_mul₀ hden).2
      nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)]
    have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
      have := Real.add_one_le_exp (2 * x)
      linarith
    have hrewrite : 1 / 2 - 3 * e i = (1 - x) / 2 := by
      dsimp [x]
      ring
    rw [hrewrite]
    have hInv : ((1 - x) / 2)⁻¹ = 2 * (1 - x)⁻¹ := by
      field_simp [hden.ne']
    rw [hInv]
    have htwox : 2 * x = 12 * e i := by dsimp [x]; ring
    rw [← htwox]
    exact mul_le_mul_of_nonneg_left (le_trans hinv hexp) (by norm_num)
  have hprod : (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤
      ∏ i : Fin r, (2 * Real.exp (12 * e i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have hi' := he12 i
      have hpos : 0 < 1 / 2 - 3 * e i := by nlinarith [hi']
      exact inv_nonneg.mpr hpos.le
    · intro i hi
      exact hfactor i
  have hprodEq : (∏ i : Fin r, (2 * Real.exp (12 * e i))) =
      (2 : ℝ) ^ r * Real.exp (12 * ∑ i, e i) := by
    rw [Finset.prod_mul_distrib]
    have hconst : (∏ i : Fin r, (2 : ℝ)) = (2 : ℝ) ^ r := by simp
    rw [hconst]
    congr 1
    have hExp : ∀ s : Finset (Fin r),
        (∏ i ∈ s, Real.exp (12 * e i)) = Real.exp (12 * ∑ i ∈ s, e i) := by
      intro s
      classical
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← Real.exp_add]
          congr 1
          ring
    simpa using hExp Finset.univ
  have hexpsum : Real.exp (12 * ∑ i, e i) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
    calc
      12 * ∑ i, e i ≤ 12 * (Real.log 2 / 12) := by nlinarith
      _ = Real.log 2 := by field_simp
  rw [hprodEq] at hprod
  have hpow : 0 ≤ (2 : ℝ) ^ r := pow_nonneg (by norm_num) _
  calc
    (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤ (2 : ℝ) ^ r * Real.exp (12 * ∑ i, e i) := hprod
    _ ≤ (2 : ℝ) ^ r * 2 := mul_le_mul_of_nonneg_left hexpsum hpow
    _ = 2 * (2 : ℝ) ^ r := by ring

end HypercubeRamsey.Lane_q_s18_n1
