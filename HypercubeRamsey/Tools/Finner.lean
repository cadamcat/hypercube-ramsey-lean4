import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.S09.Needs

/-!
# Finite Finner inequality

This is the product-space Hölder inequality of Finner in the finite-weight form used by P9.2-gain. Each
test reads only its declared coordinate scope, and each input coordinate belongs to at most `d` scopes.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- X-Finner: for nonnegative scoped functions on independent finite coordinates,
`E ∏ f_b ≤ ∏ (E f_b^d)^(1/d)`. -/
theorem xFinner {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (Q : ∀ i, FinProb (Ω i)) (S : B → Finset ι) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ i, (Finset.univ.filter (fun b => i ∈ S b)).card ≤ d)
    (f : B → (∀ i, Ω i) → ℝ)
    (hnonneg : ∀ b ω, 0 ≤ f b ω)
    (hscope : ∀ b, FinProb.DependsOn (f b) (S b)) :
    (FinProb.pi Q).expect (fun ω => ∏ b, f b ω) ≤
      ∏ b, Real.rpow
        ((FinProb.pi Q).expect (fun ω => (f b ω) ^ d)) ((d : ℝ)⁻¹) := by
  classical
  have h := HypercubeRamsey.finner_product Q S f d hd hdegree hscope hnonneg
  simpa [FinProb.expect, one_div] using h

end HypercubeRamsey
