import HypercubeRamsey.S03.Clock.Sampler

/-!
# Lemma 3.10: clock sampling

Source: `sections/03-…tex`, Lemma 3.10 (`lem:clock-sampling`, lines 771–1131). An injective sampler that also
avoids specified local failures (predicates `F k` with scopes `sc k`) and keeps a joint upper bound
`(1 + ε n) ∏ p̂` on at most `n^B` specified outputs. `θ₀ = 10^{-8}`.
-/

namespace HypercubeRamsey

open Filter
open scoped BigOperators

theorem clock_sampling (B C_g : ℝ) (hB : 1 ≤ B) : ∃ A P : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (nhds 0) ∧ ∀ n ≥ n₀, ∀ g : ℕ, Real.log g ≤ C_g * n →
    ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K] {Ω : R → Type} [∀ a, Fintype (Ω a)]
      [∀ a, DecidableEq (Ω a)] (lab : ∀ a, Ω a → Fin g) (p : ∀ a, FinProb (Ω a))
      (F : K → (∀ a, Ω a) → Prop) (sc : K → Finset R),
      (∀ y, ∑ a, labMarg (p a) (lab a) y ≤ 1e-8) →
      (∀ a y, labMarg (p a) (lab a) y ≤ (n : ℝ) ^ (-A)) →
      (∀ k, FinProb.DependsOn (F k) (sc k)) → (∀ k, ((sc k).card : ℝ) ≤ (n : ℝ) ^ B) →
      (∀ a, ((Finset.univ.filter (fun k => a ∈ sc k)).card : ℝ) ≤ (n : ℝ) ^ B) →
      (∀ k, (FinProb.pi p).pr (F k) ≤ (n : ℝ) ^ (-P)) →
      ∃ J : FinProb (∀ a, Ω a),
        (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => lab a (ω a)) ∧ ∀ k, ¬ F k ω) ∧
        (∀ (S : Finset R) (o : ∀ a, Ω a), ((S.card : ℝ) ≤ (n : ℝ) ^ B) →
          J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤ (1 + ε n) * ∏ a ∈ S, (p a).w (o a)) := by
  exact Clock.step8_bad_leaf_avoidance B C_g hB

end HypercubeRamsey
