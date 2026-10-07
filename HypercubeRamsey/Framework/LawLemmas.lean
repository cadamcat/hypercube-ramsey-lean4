import HypercubeRamsey.Framework.Law

namespace HypercubeRamsey

open scoped BigOperators

theorem Law.WidthLE.mono {N : ℕ} {μ : Law N} {t u : ℝ}
    (h : μ.WidthLE t) (htu : t ≤ u) : μ.WidthLE u := by
  intro x
  exact le_trans (h x) (div_le_div_of_nonneg_right
    (Real.exp_le_exp.mpr htu) (by positivity))

theorem Law.WidthLE.mix {N : ℕ} {ι : Type*} [Fintype ι]
    (ρ : FinProb ι) (μ : ι → Law N) (t : ℝ)
    (h : ∀ i, (μ i).WidthLE t) : (Law.mix ρ μ).WidthLE t := by
  intro x
  change (∑ i, ρ.w i * (μ i).w x) ≤ Real.exp t / N
  calc
    (∑ i, ρ.w i * (μ i).w x) ≤ ∑ i, ρ.w i * (Real.exp t / N) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (h i x) (ρ.nonneg i)
    _ = Real.exp t / N := by
      change Finset.univ.sum (fun i => ρ.w i * (Real.exp t / N)) = _
      rw [← Finset.sum_mul]
      simp [ρ.sum_eq_one]

theorem Law.WidthLE.restrict {N : ℕ} {μ : Law N} {A : Finset (Fin N)} {t : ℝ}
    (hwidth : μ.WidthLE t) (hm : 0 < ∑ x ∈ A, μ.w x) :
    (Law.restrict μ A hm).WidthLE (t - Real.log (∑ x ∈ A, μ.w x)) := by
  let m : ℝ := ∑ x ∈ A, μ.w x
  have hm' : 0 < m := hm
  have hN : (N : ℝ) ≠ 0 := by
    by_contra hN
    have hN' : N = 0 := Nat.cast_eq_zero.mp hN
    subst N
    have hA : A = ∅ := by
      ext x
      exact Fin.elim0 x
    simp [hA] at hm
  intro x
  by_cases hx : x ∈ A
  · simp [Law.restrict, hx]
    have hle : μ.w x ≤ (Real.exp t / N) := hwidth x
    calc
      μ.w x / m ≤ (Real.exp t / N) / m := by
        exact div_le_div_of_nonneg_right hle (le_of_lt hm')
      _ = Real.exp (t - Real.log m) / N := by
        rw [Real.exp_sub, Real.exp_log hm']
        field_simp [hN, ne_of_gt hm']
  · simp [Law.restrict, hx]
    have hNpos : (0 : ℝ) < N := lt_of_le_of_ne (Nat.cast_nonneg N) (Ne.symm hN)
    positivity

theorem Law.uniform_width {N : ℕ} (s : Finset (Fin N)) (hs : s.Nonempty) :
    Law.WidthLE (FinProb.uniform s hs) (Real.log ((N : ℝ) / (s.card : ℝ))) := by
  classical
  have hN : (0 : ℝ) < N := by
    obtain ⟨x, hx⟩ := hs
    exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le x.val) x.isLt
  have hcard : (0 : ℝ) < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  intro x
  change (if x ∈ s then (s.card : ℝ)⁻¹ else 0) ≤ _
  by_cases hx : x ∈ s
  · rw [if_pos hx]
    rw [Real.exp_log (div_pos hN hcard)]
    field_simp [ne_of_gt hN, ne_of_gt hcard]
    norm_num
  · rw [if_neg hx]
    positivity

end HypercubeRamsey
