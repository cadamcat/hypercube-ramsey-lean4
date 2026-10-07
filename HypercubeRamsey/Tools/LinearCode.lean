import Mathlib

/-!
# Binary random-linear-code bound

X-Varshamov is the finite Gilbert--Varshamov counting step used to choose a surjective syndrome map whose
kernel contains no nonzero low-weight word.
-/

namespace HypercubeRamsey

/-- Hamming weight of a binary vector represented over `ZMod 2`. -/
def binaryWeight {h : ℕ} (x : Fin h → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ 0)).card

/-- X-Varshamov: if the radius-`w` binary ball has fewer than `2^m` words and `m ≤ h`, there is a
surjective linear map to `m` syndrome bits with no nonzero kernel word of weight at most `w`. -/
theorem xVarshamov (h m w : ℕ) (hmh : m ≤ h) (wh : w ≤ h)
    (hvolume : (∑ j ∈ Finset.range (w + 1), Nat.choose h j) < 2 ^ m) :
    ∃ L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      Function.Surjective L ∧
      ∀ x, L x = 0 → x ≠ 0 → w < binaryWeight x := by
  classical
  sorry

end HypercubeRamsey
