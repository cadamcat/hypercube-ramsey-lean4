import HypercubeRamsey.Framework.FinProb

/-!
# Finite likelihood-ratio martingales

For two laws on a finite path space, the ratio of prefix probabilities is a martingale under the reference
law when the target law is absolutely continuous with respect to it. Bounded prefix stopping times preserve
its expectation.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- The length-`m` prefix of a path of length `n`. -/
def pathPrefix {α : Type*} {n m : ℕ} (hm : m ≤ n) (ω : Fin n → α) : Fin m → α :=
  fun i => ω ⟨i.val, lt_of_lt_of_le i.isLt hm⟩

/-- Probability of a specified prefix under a finite path law. -/
noncomputable def prefixProbability {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (m : ℕ) (hm : m ≤ n) (h : Fin m → α) : ℝ :=
  P.pr (fun ω => pathPrefix hm ω = h)

/-- Prefix likelihood ratio `dP/dQ`, set to zero on a `Q`-null prefix. -/
noncomputable def prefixLikelihoodRatio {α : Type*} [Fintype α] {n : ℕ}
    (P Q : FinProb (Fin n → α)) (m : ℕ) (hm : m ≤ n) (h : Fin m → α) : ℝ :=
  if prefixProbability Q m hm h = 0 then 0 else
    prefixProbability P m hm h / prefixProbability Q m hm h

/-- A stopping time for the prefix filtration: whether it has stopped by `m` depends only on the first `m`
coordinates. -/
def IsPrefixStoppingTime {α : Type*} {n : ℕ} (τ : (Fin n → α) → Fin (n + 1)) : Prop :=
  ∀ (m : ℕ) (hm : m ≤ n) (ω ω' : Fin n → α),
    (∀ i : Fin m, pathPrefix hm ω i = pathPrefix hm ω' i) →
      ((τ ω).val ≤ m ↔ (τ ω').val ≤ m)

/-- X-Martingale: likelihood ratios of finite adaptive prefixes form a martingale under `Q`; bounded
prefix stopping preserves expectation one. -/
theorem xLikelihoodRatioMartingale {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (P Q : FinProb (Fin n → α))
    (habsolutelyContinuous : ∀ ω, P.w ω > 0 → Q.w ω > 0)
    (m : ℕ) (hm : m < n) (h : Fin m → α) :
    (∑ a : α,
      prefixProbability Q (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a) *
        prefixLikelihoodRatio P Q (m + 1) (Nat.succ_le_of_lt hm) (Fin.snoc h a)) =
      prefixProbability Q m (Nat.le_of_lt hm) h *
        prefixLikelihoodRatio P Q m (Nat.le_of_lt hm) h ∧
    (∀ τ : (Fin n → α) → Fin (n + 1), IsPrefixStoppingTime τ →
      Q.expect (fun ω =>
        prefixLikelihoodRatio P Q (τ ω).val (Nat.le_of_lt_succ (τ ω).isLt)
          (pathPrefix (Nat.le_of_lt_succ (τ ω).isLt) ω)) = 1) := by
  classical
  sorry

end HypercubeRamsey
