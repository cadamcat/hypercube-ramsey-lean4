import Mathlib

/-!
Shared Section 6 tool interfaces not yet present in this worktree.  These are
requests for the shared tools lane; the Section 6 geometry node currently
records the resulting bounds directly.
-/

namespace HypercubeRamsey.S06.Needs

open scoped BigOperators

/-- SHARED: X-Bins (L6.1b). Consecutive bins for `Bin(ell, 1/2)` with small mass. -/
theorem shared_consecutive_bin_map6 (ell n : ℕ) (hn : 0 < n)
    (hEll : ell = Nat.floor ((n : ℝ) ^ (1 / 5 : ℝ))) :
    ∃ bin : ℕ → Fin (ell + 1),
      (∀ a b, a ≤ b → (bin a).val ≤ (bin b).val) ∧
      (∀ a b c, a ≤ b → b ≤ c → bin a = bin c → bin a = bin b) ∧
      (∀ j, (∑ q ∈ Finset.range (ell + 1),
        if bin q = j then (Nat.choose ell q : ℝ) else 0) ≤
          2 * (n : ℝ) ^ (-0.04 : ℝ) * (2 : ℝ) ^ ell) := by
  sorry

def nearMidCount6 (ell q : ℕ) : Bool := decide (Nat.dist (2 * q) ell ≤ 11)

/--
SHARED: X-BinomTail (L6.1b).  Joint near-mid tail for `m` independent odd
chunks, with the `5.5` cutoff and Section 6's `J=floor(m^.04)` regime.
-/
theorem shared_fine_severity_tail6 (n m ell : ℕ) (hn : 0 < n)
    (hellOdd : Odd ell)
    (hellLower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ ell)
    (hellUpper : (ell : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ))
    (hm : (m : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)) :
    ∀ q, 1 ≤ q → q ≤ m →
      (∑ s : (Fin m → Fin (ell + 1)),
        if q ≤ (Finset.univ.filter fun i => nearMidCount6 ell (s i).val = true).card then
          ∏ i, (Nat.choose ell (s i) : ℝ) / (2 : ℝ) ^ ell else 0) ≤
        (2 : ℝ) ^ m * (n : ℝ) ^ (-(0.13 : ℝ) * q) := by
  sorry

end HypercubeRamsey.S06.Needs
