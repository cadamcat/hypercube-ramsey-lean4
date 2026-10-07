import HypercubeRamsey.S07.InitialDiscrepancy

/-! Local acceptance probe for the frozen Section 7 exports. -/

open HypercubeRamsey

example :
    ∃ η₀ > (0 : ℝ), ∀ T : Stage, StabilizedOn T FamB →
      DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀)) :=
  HypercubeRamsey.S07.initial_discrepancy_proof

#print axioms HypercubeRamsey.S07.small_grid_purity
#print axioms HypercubeRamsey.S07.initial_discrepancy_proof
