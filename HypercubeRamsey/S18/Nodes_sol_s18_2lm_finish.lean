import HypercubeRamsey.S18.Nodes_sol_s18_2lm_raw
import HypercubeRamsey.S18.Nodes_sol_s18_2lm_exceptions

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- The actual raw cylinder estimate supplies both stopped moment and tilted
exception-stop bounds, with the exponent fixed before the stage and data. -/
theorem eventual_stop_facts {κ : CConsts} (hκ : κ.Admissible) (T : Stage)
    (hDisc : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
      TransferGeometry X → SurvivalFacts X → ∀ P : TransferProtocol X,
      ReplyRangeBound P → CylinderFacts P → StopFacts P (κ.xs / 8) := by
  have hc : 0 < κ.xs / 8 := div_pos hκ.xs_rng.1 (by norm_num)
  have hcd : κ.xs / 8 < κ.xs / 4 := by linarith [hκ.xs_rng.1]
  filter_upwards [hDisc, Parameters.valid_eventually hκ T, regular_budgets_eventually hκ T,
    second_moment_eventually_of_exception_budget hκ T (κ.xs / 8) (κ.xs / 4) hc hcd,
    exception_stop_budget_eventually hκ T (κ.xs / 8) (κ.xs / 4) hc hcd]
    with k hdisc hp hreg hmom hexc
  intro PT hPT D hD X hgeom hsurv P hR _hCylinder
  have hd : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k) := by
    simpa only [Real.rpow_eq_pow, bstar] using hdisc
  let δ := RawExceptions.multiplierTolerance X
  have hδdef : δ = κ.KB * (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) *
      (D.geom.r : ℝ)) * bstar T k := by
    simp only [δ, RawExceptions.multiplierTolerance, RawExceptions.maxSize, Nat.cast_mul, mul_assoc]
  have hr := hreg PT hPT D (D.geom.patchOf X.target)
  have hr' : 0 ≤ δ ∧ δ < 1 ∧ (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) * δ ≤ 1 / 2 ∧
      (T.S.n k : ℝ) * Real.log (T.S.n k : ℝ) ^ 20 * (2 * δ ^ 2) ≤ 1 / 2 := by
    simpa only [δ, RawExceptions.multiplierTolerance, RawExceptions.maxSize, Nat.cast_mul, mul_assoc] using hr
  obtain ⟨hδ0, hδ1, hcall, _hsquare⟩ := hr'
  have hraw : ∀ seed pair t, t < P.steps → witnessMean X pair (fun x z => if X.allowed x z then
      X.rawLaw.pr (fun s => factorException P seed x z s (t + 1)) else 0) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 4)) := by
    intro seed pair t ht
    exact RawExceptions.raw_exception_bound hκ hD hgeom hsurv hp hd hδ1 P hR seed pair t ht
  intro seed pair
  constructor
  · exact hmom PT hPT D X hgeom hsurv P hraw seed pair
  · have h := stopped_exception_of_raw hgeom hsurv P (κ.xs / 8) δ
      (Real.exp (-Real.rpow (T.S.n k : ℝ) (κ.xs / 4))) seed pair hδdef hδ0 hδ1 hcall (hraw seed pair)
    exact h.trans (hexc PT hPT D (D.geom.patchOf X.target) P.steps P.steps_bound)

end HypercubeRamsey.S18.Lane_sol_s18_2lm
