import HypercubeRamsey.Framework.Stage
import HypercubeRamsey.Tools.Binomial

/-!
# Cube geometry and Hamming-ball bounds

F-Cube provides explicit finite-cube operations, parity classes, prefix leaves, internal coordinates, slices,
and the stage-level `CubeIn` predicate. X-HammingBall supplies entropy volume, layer ratios, and the
hypergeometric intersection tail used by the height argument.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- Flip one coordinate of a Boolean cube vertex. -/
def cubeFlip {n : ℕ} (v : CubeVertex n) (i : Fin n) : CubeVertex n :=
  Function.update v i (!v i)

/-- Hamming distance on the Boolean cube. -/
def hammingDist {n : ℕ} (u v : CubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card

/-- The radius-`r` Hamming ball around `v`. -/
def hammingBall {n : ℕ} (v : CubeVertex n) (r : ℕ) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun u => hammingDist v u ≤ r)

/-- Finset of even-role cube vertices. -/
noncomputable def evenRoleSet (n : ℕ) : Finset (CubeVertex n) :=
  by classical exact Finset.univ.filter (fun v => IsEvenRole v)

/-- A prefix leaf fixes the first `ell` coordinates to the word `w`. -/
def cubeLeaf {n ell : ℕ} (hle : ell ≤ n) (w : Fin ell → Bool) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun v => ∀ j : Fin ell, v (Fin.castLE hle j) = w j)

/-- The final `h` coordinates, used as an internal coordinate set. -/
def topCoordinates (n h : ℕ) (_hle : h ≤ n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => n - h ≤ j.val)

/-- A slice of a prefix leaf fixes all coordinates outside the supplied internal set. -/
def cubeSlice {n ell : ℕ} (hle : ell ≤ n) (w : Fin ell → Bool)
    (internal : Finset (Fin n)) (outside : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun v =>
    (∀ j : Fin ell, v (Fin.castLE hle j) = w j) ∧
    (∀ j, j ∉ internal → v j = outside j))

/-- `CubeIn` is the stage-level monochromatic cube predicate from Part C §3.15. -/
def CubeIn (T : Stage) (k : ℕ) (c : Colour) : Prop :=
  Nonempty ((cube (T.S.n k)).Copy (crossGraph (Hits (T.S.E k) c)))

/-- F-Cube: flipping one coordinate gives adjacent cube vertices. -/
theorem cubeFlip_adj {n : ℕ} (v : CubeVertex n) (i : Fin n) :
    (cube n).Adj v (cubeFlip v i) := by
  sorry

/-- F-Cube: one-coordinate flips exchange the two parity classes. -/
theorem cubeFlip_parity {n : ℕ} (v : CubeVertex n) (i : Fin n) :
    IsEvenRole (cubeFlip v i) ↔ ¬ IsEvenRole v := by
  sorry

/-- F-Cube: Hamming distance satisfies the triangle inequality. -/
theorem hammingDist_triangle {n : ℕ} (u v w : CubeVertex n) :
    hammingDist u w ≤ hammingDist u v + hammingDist v w := by
  sorry

/-- F-Cube: for positive dimension, each parity class has exactly half the vertices. -/
theorem parity_class_card {n : ℕ} (hn : 0 < n) :
    (evenRoleSet n).card = 2 ^ (n - 1) ∧
    (Finset.univ \ evenRoleSet n).card = 2 ^ (n - 1) := by
  sorry

/-- F-Cube: fixing a proper coordinate set leaves equally many even-role completions for every assignment. -/
theorem parity_projection_uniform {n : ℕ} (S : Finset (Fin n)) (hS : S.card < n)
    (z : ∀ i : S, Bool) :
    ((evenRoleSet n).filter (fun v : CubeVertex n => ∀ i : S, v i.1 = z i)).card =
      2 ^ (n - S.card - 1) := by
  sorry

/-- X-HammingBall: the Hamming-ball volume is at most `exp(n H_bin(r/n))` for `r ≤ n/2`. -/
theorem hammingBall_volume_bound {n r : ℕ} (hn : 0 < n) (hr : r ≤ n / 2) (v : CubeVertex n) :
    (hammingBall v r).card ≤
      Real.exp (Real.binEntropy ((r : ℝ) / n) * n) := by
  sorry

/-- X-HammingBall: adjacent binomial layers have the exact ratio `r/(d-r+1)`. -/
theorem hammingLayer_ratio (d r : ℕ) (hr : 0 < r) (hrd : r ≤ d) :
    (Nat.choose d (r - 1) : ℝ) * (d - r + 1 : ℕ) =
      (Nat.choose d r : ℝ) * r := by
  sorry

/-- X-HammingBall: a uniform `s`-subset has a sub-Gaussian upper tail for its intersection with a fixed
subset (the hypergeometric tail used in ball-intersection estimates). -/
theorem hypergeometric_intersection_tail (d s : ℕ) (hd : 0 < d) (hs : 0 < s) (hsd : s ≤ d)
    (A : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun B : Finset (Fin d) =>
      B.card = s ∧ ((B ∩ A).card : ℝ) ≥
        (s : ℝ) * A.card / d + t)).card : ℝ) / Nat.choose d s ≤
      Real.exp (-2 * t ^ 2 / s) := by
  sorry

end HypercubeRamsey
