import HypercubeRamsey.S05.Centres

/-!
# L5.1m: actual odd outputs by clock sampling (05:1063–1084)

Given probability rows for the odd roles with column sums at most `θ₀` and small atoms, and per even role a
budget of bounded nonnegative costs on its star with small total mean, the clock lemma (L3.10, scope exponent
`B = 2`) gives an injective assignment satisfying every budget whose joint law is at most `(1 + o(1))` times the
product of the rows on at most `n²` queried rows; each budget fails under the product with probability
`exp(-Ω((t₁ - t₀)² / (n M²)))` by bounded-summand concentration.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey Filter

/-- L5.1m (05:1063–1084). -/
theorem L5_1m : ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧ (∀ k, 0 ≤ ε k) ∧
    ∀ n ≥ n₀, ∀ (N : ℕ), 2 ^ n ≤ N → N ≤ n * 2 ^ n →
    ∀ {O : Type} [Fintype O] [DecidableEq O] (lab : O → Fin N) (row : OddRole5 n → FinProb O)
      (cost : EvenRole5 n → OddRole5 n → O → ℝ) (M t₀ t₁ : ℝ),
      (∀ x, ∑ b, labMarg (row b) lab x ≤ 1e-8) →
      (∀ b x, labMarg (row b) lab x ≤ (n : ℝ) ^ (-A)) →
      (∀ v b o, 0 ≤ cost v b o ∧ cost v b o ≤ M) →
      (∀ v b o, ¬ (cube n).Adj v.1 b.1 → cost v b o = 0) →
      (∀ v, ∑ b, (row b).expect (cost v b) ≤ t₀) →
      t₀ ≤ t₁ →
      Real.exp (-(2 * (t₁ - t₀) ^ 2 / ((n : ℝ) * M ^ 2))) ≤ (n : ℝ) ^ (-P) →
      ∃ J : FinProb (OddRole5 n → O),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun b => lab (ω b)) ∧ ∀ v, ∑ b, cost v b (ω b) ≤ t₁) ∧
        (∀ (S : Finset (OddRole5 n)) (o : OddRole5 n → O), S.card ≤ n ^ 2 →
          J.pr (fun ω => ∀ b ∈ S, ω b = o b) ≤ (1 + ε n) * ∏ b ∈ S, (row b).w (o b)) := by
  sorry

end HypercubeRamsey
