import HypercubeRamsey.S06.OddRows

namespace HypercubeRamsey.S06.Lane_sol_s06_ev_d

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- A shared success gate cannot be removed from first moments before multiplying them. -/
theorem shared_gate_counterexample :
    let P : FinProb Bool := FinProb.bernoulli (1 / 16)
    let f : Bool → ℝ := fun b => if b then 1 else 0
    P.expect (fun b => f b * f b) > 4 * P.expect f * P.expect f := by
  norm_num [FinProb.expect, FinProb.bernoulli, Fintype.sum_bool]

end
end HypercubeRamsey.S06.Lane_sol_s06_ev_d
