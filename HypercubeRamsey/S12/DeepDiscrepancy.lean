import HypercubeRamsey.S12.Defs

/-!
# Section 12 deep discrepancy
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter

/-- C12.1m: shrinking either width budget and enlarging the error preserves two-budget discrepancy. -/
theorem TwoBudgetDisc.mono {T : Stage} {k : ℕ} {wS wL err wS' wL' err' : ℝ}
    (h : HypercubeRamsey.TwoBudgetDisc T k wS wL err)
    (h1 : wS' ≤ wS) (h2 : wL' ≤ wL) (h3 : err ≤ err') :
    HypercubeRamsey.TwoBudgetDisc T k wS' wL' err' := by
  intro c μ ν hμ hν hbudget
  have width_mono {N : ℕ} (p : Law N) {a b : ℝ}
      (hab : a ≤ b) (hp : p.WidthLE a) : p.WidthLE b := by
    intro x
    exact le_trans (hp x) (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hab) (by positivity))
  rcases hbudget with ⟨hμw, hνw⟩ | ⟨hμw, hνw⟩
  · exact le_trans (h c μ ν hμ hν
      (Or.inl ⟨width_mono μ h2 hμw, width_mono ν h1 hνw⟩)) h3
  · exact le_trans (h c μ ν hμ hν
      (Or.inr ⟨width_mono μ h1 hμw, width_mono ν h2 hνw⟩)) h3

/-- C12.1m: smaller exponents and linear budgets, and a larger error slack, preserve deep discrepancy. -/
theorem DeepDisc.mono {T : Stage} {x α ε x' α' ε' : ℝ}
    (h : HypercubeRamsey.DeepDisc T x α ε)
    (hx : x' ≤ x) (hα : α' ≤ α) (hε : ε ≤ ε') :
    HypercubeRamsey.DeepDisc T x' α' ε' := by
  unfold HypercubeRamsey.DeepDisc at h ⊢
  have hn : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    exact (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [h, hn] with k hk hnk
  have hsmall : (T.S.n k : ℝ) ^ x' ≤ (T.S.n k : ℝ) ^ x :=
    Real.rpow_le_rpow_of_exponent_le hnk hx
  have hlarge : α' * (T.S.n k : ℝ) ≤ α * (T.S.n k : ℝ) :=
    mul_le_mul_of_nonneg_right hα (by positivity)
  have herr : (T.S.n k : ℝ) ^ (-1 + ε) ≤
      (T.S.n k : ℝ) ^ (-1 + ε') :=
    Real.rpow_le_rpow_of_exponent_le hnk (by linarith)
  exact TwoBudgetDisc.mono hk hsmall hlarge herr

/-- C12.1: from the two-orientation deep regime, choose both positive budgets below `.01`. -/
theorem deepDisc_small (T : Stage)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ,
      0 < x ∧ 0 < α ∧ HypercubeRamsey.DeepDisc T x α ε) :
    ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ,
      0 < x ∧ x < 0.01 ∧ 0 < α ∧ α < 0.01 ∧ HypercubeRamsey.DeepDisc T x α ε := by
  intro ε hε
  obtain ⟨x, α, hx, hα, hD⟩ := hDeep ε hε
  let x' := min x (1 / 200 : ℝ)
  let α' := min α (1 / 200 : ℝ)
  have hx' : 0 < x' := by dsimp [x']; exact lt_min hx (by norm_num)
  have hα' : 0 < α' := by dsimp [α']; exact lt_min hα (by norm_num)
  have hx'lt : x' < 0.01 := by
    dsimp [x']
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hα'lt : α' < 0.01 := by
    dsimp [α']
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨x', α', hx', hx'lt, hα', hα'lt, ?_⟩
  exact DeepDisc.mono hD (min_le_left _ _) (min_le_left _ _) le_rfl

end HypercubeRamsey.S12
