import HypercubeRamsey.Framework.FinProb

/-!
# Binomial and entropy estimates

Finite statements for central binomial atoms, consecutive half-binomial bins, binomial tails, and binary
entropy volume bounds. `Real.binEntropy` is Mathlib's natural-log binary entropy.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- Mass at `k` for a `Binomial(ell, 1/2)` random variable. -/
noncomputable def halfBinomialMass (ell : ℕ) (k : Fin (ell + 1)) : ℝ :=
  (Nat.choose ell k.val : ℝ) / (2 : ℝ) ^ ell

/-- X-Binomial: binomial coefficients are symmetric about the middle. -/
theorem binomial_choose_symm (ell k : ℕ) (hk : k ≤ ell) :
    Nat.choose ell k = Nat.choose ell (ell - k) := by
  sorry

/-- X-Binomial: the largest binomial coefficient is central. -/
theorem binomial_choose_le_central (ell k : ℕ) (hk : k ≤ ell) :
    Nat.choose ell k ≤ Nat.choose ell (ell / 2) := by
  sorry

/-- X-CentralBinomUpper: every atom of `Binomial(ell, 1/2)` is at most `2 / sqrt(ell)`. -/
theorem centralBinomialUpper (ell : ℕ) (hell : 0 < ell) (k : ℕ) (hk : k ≤ ell) :
    (Nat.choose ell k : ℝ) / (2 : ℝ) ^ ell ≤ 2 / Real.sqrt ell := by
  sorry

/-- X-BinomEntropy: the lower binomial layers have total size at most `exp(n H_bin(rho))`. -/
theorem binomialEntropyBound (n : ℕ) (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho : rho ≤ 1 / 2) :
    ∑ k ∈ (Finset.univ.filter (fun k : Fin (n + 1) => (k.val : ℝ) ≤ rho * n)),
      (Nat.choose n k.val : ℝ) ≤ Real.exp (Real.binEntropy rho * n) := by
  sorry

/-- F-BinomTail: upper additive tail of a finite `Binomial(m,p)` law. -/
noncomputable def binomialMass (m : ℕ) (p : ℝ) (k : Fin (m + 1)) : ℝ :=
  (Nat.choose m k.val : ℝ) * p ^ k.val * (1 - p) ^ (m - k.val)

/-- F-BinomTail: Hoeffding's upper-tail bound for a binomial count. -/
theorem binomialTailUpper (m : ℕ) (hm : 0 < m) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ (Finset.univ.filter
      (fun k : Fin (m + 1) => (m : ℝ) * p + t ≤ k.val)), binomialMass m p k ≤
        Real.exp (-2 * t ^ 2 / m) := by
  sorry

/-- F-BinomTail: Hoeffding's lower-tail bound for a finite binomial count. -/
theorem binomialTailLower (m : ℕ) (hm : 0 < m) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∑ k ∈ (Finset.univ.filter
      (fun k : Fin (m + 1) => (k.val : ℝ) ≤ (m : ℝ) * p - t)), binomialMass m p k ≤
        Real.exp (-2 * t ^ 2 / m) := by
  sorry

/-- F-Bins: a consecutive interval of binomial weights used as one coarse bin. -/
def IsConsecutiveBin {ell : ℕ} (B : Finset (Fin (ell + 1))) : Prop :=
  ∃ a b : ℕ, ∀ k, k ∈ B ↔ a ≤ k.val ∧ k.val ≤ b

/-- F-Bins: partition `{0,…,ell}` into consecutive intervals, each of half-binomial mass at most `2ε`;
the greedy packing can be chosen with at most `ε⁻¹+1` intervals. -/
theorem exists_consecutive_bin_partition (ell : ℕ) (hell : 0 < ell) (ε : ℝ)
    (hε : 2 / Real.sqrt ell ≤ ε) :
    ∃ bins : Finset (Finset (Fin (ell + 1))),
      (∀ k, ∃! B, B ∈ bins ∧ k ∈ B) ∧
      (∀ B, B ∈ bins → IsConsecutiveBin B ∧
        ∑ k ∈ B, halfBinomialMass ell k ≤ 2 * ε) ∧
      (bins.card : ℝ) ≤ ε⁻¹ + 1 := by
  sorry

end HypercubeRamsey
