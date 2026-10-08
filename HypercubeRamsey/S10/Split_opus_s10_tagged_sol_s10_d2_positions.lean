import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_probability

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- The relative position estimates hold simultaneously in every slice and at
every residual site, with the full cube-size union factor. -/
theorem global_positions_bad_bound (n m : ℕ) (δ : ℝ)
    (hlam : 0 < (p10_1kHeightParams n m δ).lam)
    (hV : 0 < (p10_1kHeightParams n m δ).V)
    (hprob : (p10_1kHeightParams n m δ).lam /
      ((p10_1kHeightParams n m δ).V : ℝ) ≤ 1) :
    (p10_1kGlobalPositionLaw n m δ).pr (fun P =>
      ∃ z : Fin m → Bool, ∃ v : CubeVertex (n - m),
        ∃ j : Fin ((p10_1kHeightParams n m δ).H + 1),
          positionBad (p10_1kHeightParams n m δ) (fun loc => P (z, loc)) v j) ≤
      (2 : ℝ) ^ m * (2 * (2 : ℝ) ^ (n - m) *
        (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) *
          Real.exp (-(p10_1kHeightParams n m δ).lam / 2000000)) := by
  classical
  let p := p10_1kHeightParams n m δ
  let Bad (P : p.Loc → Bool) : Prop := ∃ v : CubeVertex p.d, ∃ j, positionBad p P v j
  have heq :
      (p10_1kGlobalPositionLaw n m δ).pr (fun P => ∃ z : Fin m → Bool, Bad (fun loc => P (z, loc))) =
      (FinProb.pi (fun _ : Fin m → Bool => p.posLaw)).pr (fun P => ∃ z, Bad (P z)) := by
    rw [pr_indicator, pr_indicator]
    convert pi_curry_expect
      (fun _ : (Fin m → Bool) × p.Loc => FinProb.bernoulli (p.lam / (p.V : ℝ)))
      (fun P => if ∃ z, Bad (P z) then (1 : ℝ) else 0) using 1 <;>
      (congr 1; funext P; simp)
  change (p10_1kGlobalPositionLaw n m δ).pr (fun P => ∃ z : Fin m → Bool, Bad (fun loc => P (z, loc))) ≤ _
  rw [heq]
  have hp : p.posLaw.pr Bad ≤ 2 * (2 : ℝ) ^ (n - m) *
      ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 2000000) := by
    have hc : (Finset.univ : Finset (CubeVertex p.d)).card = 2 ^ (n - m) := by
      change (Finset.univ : Finset (Fin (n - m) → Bool)).card = 2 ^ (n - m)
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simpa only [Bad, Finset.mem_univ, true_and, hc, Nat.cast_pow, Nat.cast_ofNat] using
      position_counts_union p Finset.univ hlam hV hprob
  calc
    (FinProb.pi (fun _ : Fin m → Bool => p.posLaw)).pr (fun P => ∃ z, Bad (P z)) ≤
        ∑ z : Fin m → Bool, (FinProb.pi (fun _ : Fin m → Bool => p.posLaw)).pr
          (fun P => Bad (P z)) := p10_1k_FinProb_pr_exists_le _ _
    _ = ∑ _z : Fin m → Bool, p.posLaw.pr Bad := by
      apply Finset.sum_congr rfl
      intro z _
      exact pi_coordinate_pr _ z Bad
    _ ≤ ∑ _z : Fin m → Bool,
        2 * (2 : ℝ) ^ (n - m) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 2000000) :=
      Finset.sum_le_sum fun _ _ => hp
    _ = _ := by simp [p]

end HypercubeRamsey.Lane_sol_s10_d2
