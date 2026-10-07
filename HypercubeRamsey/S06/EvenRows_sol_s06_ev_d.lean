import HypercubeRamsey.S06.OddRows

namespace HypercubeRamsey.S06.Lane_sol_s06_ev_d

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- Auxiliary odd sampling uses a probability filler on an invalid row. -/
def oddLaw (H : X.Hist) (C : X.Centre) (u : CubeVertex n) : Law N :=
  if X.OddValid H C X.Rlong (X.g.L.stateOf u) then
    match X.stMode (X.g.L.stateOf u) with
    | .low => X.lowRow H (X.pos C) (X.g.L.stateOf u)
        (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)
    | .high => X.s3Post H (X.g.L.stateOf u)
        (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)
  else normalize6 (fun _ => 1) X.y₀

theorem oddLaw_eq_row (H : X.Hist) (C : X.Centre) (u : CubeVertex n)
    (hu : X.OddValid H C X.Rlong (X.g.L.stateOf u)) (a : Fin N) :
    (oddLaw X H C u).w a = X.oddRow H C u a := by
  unfold oddLaw Ctx6.oddRow Ctx6.oddRowAt
  rw [if_pos hu, if_pos hu]
  cases X.stMode (X.g.L.stateOf u) <;> rfl

/-- A shared success gate cannot be removed from first moments before multiplying them. -/
theorem shared_gate_counterexample :
    let P : FinProb Bool := FinProb.bernoulli (1 / 16)
    let f : Bool → ℝ := fun b => if b then 1 else 0
    P.expect (fun b => f b * f b) > 4 * P.expect f * P.expect f := by
  norm_num [FinProb.expect, FinProb.bernoulli, Fintype.sum_bool]

end
end HypercubeRamsey.S06.Lane_sol_s06_ev_d
