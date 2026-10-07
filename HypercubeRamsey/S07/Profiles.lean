import HypercubeRamsey.S07.FilterNodes
import HypercubeRamsey.S03.Mixtures

/-!
# L7.1, Step 1: the finite menu and the tag profiles

Source: `sections/07-…tex`, lines 51–53 and 116–134.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- L7.1, Step 1 (07:51–53): availability of one-colour grid purity gives a finite menu retaining availability:
index the menu by the support pairs carrying a witness inside `(X, Y)` and choose one witness for each. -/
theorem menu7_of_available {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
    {d p κ : ℝ} (hκ : 0 ≤ κ) (h : AvailableAt κ (PGridPure G d p).toPatch n N E X Y) :
    Nonempty (Menu7 n N E G X Y d p κ) := by
  sorry

/-- Lemma 3.3, first assertion, with subprobability second outputs (TeX 03, Lemma 3.3; used at 07:126–132): the
separation argument of `balanced_mixture`, where each second output is a subprobability vanishing on the
removed labels. -/
theorem balanced_mixture_sub : BalancedSub := by
  sorry

/-- L7.1c (07:116–134): tag profiles with constant `K' = 4/κ`.  One player per grid key in Lemma 3.3's
simultaneous-profile part; player `g`'s outputs are `μ_{i_g}` and the raw mean of its odd rows averaged over the
auxiliary words.  Against fixed profiles of the other players these outputs are a law supported where `μ_i` is
and a subprobability supported where `ν_i` is (`RowLaw`), so `BalancedSub` gives a best response; the output
rule does not use the profile probabilities. -/
theorem grid_profiles (hBS : BalancedSub) {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : GridGeom d n s ℓ q)
    (M : Menu7 n N E G X Y d p κ) (hκ : 0 < κ) (hN : 0 < N) (hrow : RowLaw Γ M) :
    Nonempty (Profiles7 Γ M (4 / κ)) := by
  sorry

end HypercubeRamsey.S07
