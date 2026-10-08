import HypercubeRamsey.S05.History_sol_s05_h23_apply
import HypercubeRamsey.S05.History_sol_s05_h3

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical Filter OAI.HypercubeRamsey Lane_q_s05_h23
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

/-- The Stage 3 Markov exponents are the Stage 2 budgets with half the gap. -/
def halfDelta (p : Params5 γ K' χ) : Params5 γ K' χ :=
  { p with
    delta := p.delta / 2
    hdelta := by
      constructor
      · exact div_pos p.hdelta.1 (by norm_num)
      · have hp := p.hdelta
        linarith
    hdelta_a := by
      intro i j hij
      have h := p.hdelta_a i j hij
      have hp := p.hdelta.1
      linarith
    hKpp_budget := by
      apply max_le
      · exact (le_max_left _ _).trans p.hKpp_budget
      · have h := (le_max_right _ _).trans p.hKpp_budget
        have hp := p.hdelta.1
        linarith }

/-- Geometry, priors and array dimensions are unchanged when the gap is halved. -/
def halfDeltaSetup (X : Setup5 γ K' χ n N E G) : Setup5 γ K' χ n N E G :=
  { X with p := halfDelta X.p }

theorem stage3PatternBudget_tendsto (p : Params5 γ K' χ) :
    Tendsto (stage2GroupBudgetVanishing5 (halfDelta p)) atTop (𝓝 0) :=
  stage2Budget_tendsto (halfDelta p)

theorem halfDelta_K1 (p : Params5 γ K' χ) (hp : 16 / p.delta ≤ p.K1) :
    8 / (halfDelta p).delta ≤ (halfDelta p).K1 := by
  change 8 / (p.delta / 2) ≤ p.K1
  have heq : 8 / (p.delta / 2) = 16 / p.delta := by
    field_simp [p.hdelta.1.ne']
    <;> ring
  rw [heq]
  exact hp

end
end HypercubeRamsey.Lane_sol_s05_h23
