import HypercubeRamsey.Framework.FinProb

/-!
# Lemma 3.9: calibrated near-product injections

Source: `sections/03-…tex`, Lemma 3.9 (`lem:near-product-injection`, lines 586–769). Rows `i : R` carry full
outputs `Ω i` with labels `lab i : Ω i → Fin d`; the injection assigns distinct labels, keeps every row's
marginal exactly, and bounds joint probabilities of at most `d^{0.025}` specified outputs by the product of their
probabilities times `exp (d^{-0.04} · #rows)`. Blueprint: `research/blueprint/PART-A.md`, node L3.9.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- Label marginal of a row law. -/
noncomputable def labMarg {Ω : Type*} [Fintype Ω] {d : ℕ} (p : FinProb Ω) (lab : Ω → Fin d)
    (y : Fin d) : ℝ := by
  classical exact ∑ o, if lab o = y then p.w o else 0

theorem near_product_injection : ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ {R : Type} [Fintype R] [DecidableEq R]
    {Ω : R → Type} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (lab : ∀ i, Ω i → Fin d) (p : ∀ i, FinProb (Ω i)),
    (∀ i y, labMarg (p i) (lab i) y ≤ (d : ℝ) ^ (-(0.95 : ℝ))) →
    (∀ y, ∑ i, labMarg (p i) (lab i) y ≤ 0.4) →
    ∃ J : FinProb (∀ i, Ω i),
      (∀ ω, J.w ω ≠ 0 → Function.Injective (fun i => lab i (ω i))) ∧
      (∀ i o, J.pr (fun ω => ω i = o) = (p i).w o) ∧
      (∀ (S : Finset R) (o : ∀ i, Ω i), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
          Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, (p i).w (o i)) := sorry

end HypercubeRamsey
