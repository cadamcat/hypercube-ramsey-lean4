import HypercubeRamsey.S05.Even_load_scopes_sol_s05_even
import HypercubeRamsey.Tools.ScatteredUnion

/-!
# Lane opus-s05-even: generic sub-lemmas for L5.1o

The even-load node `L5_1o` (05:1209–1282) is assembled in `Even.lean` from the sub-lemmas stated there
(they read the even-row definitions of that file) and from the generic clock comparison below.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_even

open Classical
open scoped BigOperators

noncomputable section

/-- SUB-LEMMA D1 (05:1266–1270, clock comparison on finitely many outputs): if a law on assignments has
cylinder probabilities on `S` at most `(1 + ε)` times a product law, then it integrates every nonnegative
function of the `S`-coordinates to at most `(1 + ε)` times the product-law mean. Group assignments by their
restriction to `S`; the product law of a cylinder is `∏_{b ∈ S} P_b(o_b)` since the other factors sum to one. -/
theorem clock_expect_le {B A : Type*} [Fintype B] [DecidableEq B] [Fintype A] [DecidableEq A]
    (Q : FinProb (B → A)) (P : B → FinProb A) (S : Finset B) (ε : ℝ) (hε : 0 ≤ ε)
    (hcyl : ∀ o : B → A, Q.pr (fun O => ∀ b ∈ S, O b = o b) ≤ (1 + ε) * ∏ b ∈ S, (P b).w (o b))
    (F : (B → A) → ℝ) (hF : ∀ O, 0 ≤ F O) (hS : FinProb.DependsOn F S) :
    Q.expect F ≤ (1 + ε) * (FinProb.pi P).expect F := by
  sorry

end

end HypercubeRamsey.Setup5.Lane_opus_s05_even
