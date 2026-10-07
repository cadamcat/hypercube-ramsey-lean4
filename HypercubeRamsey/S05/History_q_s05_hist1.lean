import HypercubeRamsey.S05.Experiment

namespace HypercubeRamsey

open scoped BigOperators

/-- If all normalized weights vanish, `normalize5` uses its fixed fallback atom. -/
theorem normalize5_w_zero_sum5 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (ω₀ : Ω) (hzero : ∑ ω, max 0 (f ω) = 0) :
    ∀ ω, (normalize5 f ω₀).w ω = if ω = ω₀ then 1 else 0 := by
  classical
  intro ω
  unfold normalize5
  have hnot : ¬ 0 < ∑ ω, max 0 (f ω) := by rw [hzero]; norm_num
  simp [hnot]

/-- A law supported on one label per coordinate cannot obey a cap whose total mass is below one. -/
theorem FinProb.no_capped_singleton_support5 {s N : ℕ} (D : ℝ) (y₀ : Fin N)
    (P : FinProb (Fin s × Fin N)) (hs : 0 < s) (hN : 0 < N)
    (hsmall : 2 * Real.exp D < (N : ℝ))
    (hcap : ∀ h y, P.w (h, y) ≤ 2 * Real.exp D / ((s : ℝ) * N))
    (hsupport : ∀ h y, P.w (h, y) ≠ 0 → y = y₀) : False := by
  classical
  have hrow : ∀ h : Fin s, ∑ y : Fin N, P.w (h, y) ≤ 2 * Real.exp D / ((s : ℝ) * N) := by
    intro h
    calc
      ∑ y : Fin N, P.w (h, y) = P.w (h, y₀) := by
        rw [Finset.sum_eq_single y₀]
        · simp
        · intro y hy hne
          have hz : P.w (h, y) = 0 := by
            by_contra hne0
            exact hne (hsupport h y hne0)
          simp [hz]
        · simp
      _ ≤ 2 * Real.exp D / ((s : ℝ) * N) := hcap h y₀
  have hsum : (∑ h : Fin s, ∑ y : Fin N, P.w (h, y)) = 1 := by
    rw [← Fintype.sum_prod_type]
    exact P.sum_eq_one
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have htotal : (1 : ℝ) ≤ 2 * Real.exp D / N := by
    rw [← hsum]
    calc
      (∑ h : Fin s, ∑ y : Fin N, P.w (h, y)) ≤
          ∑ h : Fin s, (2 * Real.exp D / ((s : ℝ) * N)) :=
        Finset.sum_le_sum fun h hh => hrow h
      _ = 2 * Real.exp D / N := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hsR, ne_of_gt hNR]
  have hlt : 2 * Real.exp D / N < 1 := by
    apply (div_lt_one hNR).2
    nlinarith
  linarith

end HypercubeRamsey
