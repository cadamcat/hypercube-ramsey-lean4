import HypercubeRamsey.S09.Defs
import HypercubeRamsey.S09.Regime
import HypercubeRamsey.S09.Needs
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Framework.Hall
import HypercubeRamsey.Framework.Minimax
import HypercubeRamsey.S09.Nodes_p_s09_select

/-!
# Proposition 9.2 nodes

Parameter selection, patch preparation, the height/ID maps, and the one-shot
boundary are stated separately.  The remaining anchor, filter, gain, and
assignment argument is represented by the core one-shot node.
-/

namespace HypercubeRamsey

open Filter OAI.HypercubeRamsey Classical

/-- P9.2-selS (09:43–49): select the shallow and deep sublinear budgets. -/
theorem p92_select_sublinear (T : Stage) (hT : StabilizedOn T FamB)
    (hH : HdagLtOne T) :
    ∃ P : Params9, P.Valid ∧ P.IsSublinear ∧ P.SubSelection T := by
  exact p92_select_sublinear_impl T hT hH

/-- P9.2-selL (09:51–59): select the shallow and deep linear budgets and broad test. -/
theorem p92_select_linear (T : Stage) (hT : StabilizedOn T FamB)
    (hNoH : ¬ HdagLtOne T) (hHL : HLdagLtOne T) (hNotZero : ¬ HLdagZero T) :
    ∃ P : Params9, P.Valid ∧ P.IsLinear ∧ P.LinearSelection T := by
  exact p92_select_linear_impl T hT hNoH hHL hNotZero

/-- P9.2-prep (09:61): balanced tag mixture with a colour and surplus rows. -/
theorem p92_patch_preparation {P : Params9} {κ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hP : P.Valid) (hκ : 0 < κ) (hN : 0 < N)
    (hAvail : AvailableAt κ P.BiasProperty n N E X Y) :
    ∃ G : Colour, ∃ M : TagMix N,
      M.Balanced (8 / κ) ∧
      (∀ i, 0 < M.Λ i → (M.μ i).SupportedIn X ∧ (M.ν i).SupportedIn Y ∧
        (M.μ i).WidthLE ((n : ℝ) ^ (P.xS : ℝ) +
          (P.hPlus : ℝ) * Real.log (n : ℝ) + 1) ∧
        (M.ν i).WidthLE (P.Ss (n : ℝ)) ∧
        ∀ x, (M.μ i).w x ≠ 0 →
          1 / 2 + (n : ℝ) ^ (-(P.hPlus : ℝ)) / 2 ≤ rowDeg E G x (M.ν i)) := by
  exact p92_patch_preparation_impl hP hκ hN hAvail

/-- P9.2-map1 (09:63–102): good heights with distance-two regularity.  The
`HeightGood9` predicate records active eligibility and all three crowd tests. -/
theorem p92_map1 (P : Params9) (hP : P.Valid) :
    ∃ n₀, ∀ n, n₀ ≤ n → Nonempty (HeightWitness9 P n) := by
  exact height_general9 P hP

/-- P9.2-map2 (09:102–118): the ID records a special slice, residual location,
and selected height level. -/
theorem p92_map2 (P : Params9) (hP : P.Valid) {n r : ℕ}
    (W : HeightWitness9 P n) (hr : W.radius = r) :
    ∃ T : ℕ, (n : ℝ) ^ (1 - (P.σ : ℝ) + W.ε) ≤ T ∧
      ∃ c : CubeVertex n → CenterID9 W.specialBits n W.levels,
        (∀ v, (c v).slice = specialWord9 W.specialBits_le v ∧
          residualDistance9 W.specialBits (c v).location v ≤ r ∧
          (c v).level = W.height v ∧ c v ∈ W.active) ∧
        (∀ b : CubeVertex n, ¬ IsEvenRole b →
          (seenIDs9 c b).card ≤ T + W.specialBits) ∧
        (∀ v : CubeVertex n, IsEvenRole v →
          ∃ C : Finset (CenterID9 W.specialBits n W.levels), c v ∈ C ∧
            (C.card : ℝ) ≤ (n : ℝ) ^ (P.χ : ℝ) ∧
            ∀ id, id ∉ C →
              ((Finset.univ.filter (fun b : CubeVertex n =>
                ¬ IsEvenRole b ∧ (cube n).Adj v b ∧ id ∈ seenIDs9 c b)).card : ℕ) ≤ r + 3) := by
  sorry

/-- P9.2-tags through P9.2-assignC (09:120–350): the fixed tag, anchor, mask,
regularity, conditional-mean, erasure, covariance, gain and assignment
certificates compose to the one-shot embedding.  This assembly interface
includes the broad test only in the linear case. -/
theorem intermediate_core (P : Params9) (hP : P.Valid) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N → P.DeepAt n N E X Y → P.BroadAt n N E X Y →
      AvailableAt κ P.BiasProperty n N E X Y → CubeAt n N E := by
  sorry

end HypercubeRamsey
