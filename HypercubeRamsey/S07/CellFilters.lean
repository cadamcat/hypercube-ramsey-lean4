import HypercubeRamsey.Framework.Law

/-!
# L7.1b: cell filters and deletion comparisons
-/

namespace HypercubeRamsey.S07

open Classical

/-- A second-side label passes a finite list of first-side anchors in colour `G`. -/
def passesAnchors {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : List (Fin N)) (y : Fin N) : Prop := ∀ x ∈ L, Hits E G x y

/-- Unnormalized mass remaining after restricting to labels that hit every listed anchor. -/
noncomputable def filterMass {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) : ℝ :=
  ∑ y, if passesAnchors E G L y then ν.w y else 0

/-- The law filtered to common neighbours of a list, with zero fallback at zero mass. -/
noncomputable def filt {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (y : Fin N) : ℝ :=
  if _h : 0 < filterMass E G ν L then
    if passesAnchors E G L y then ν.w y / filterMass E G ν L else 0
  else 0

/-- L7.1b (07:70–114): a positive-mass filter is a probability supported on labels passing its list. -/
theorem filt_probability_and_support {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (hL : 0 < filterMass E G ν L) :
    (∀ y, 0 ≤ filt E G ν L y) ∧
    (∑ y, filt E G ν L y = 1) ∧
    (∀ y, filt E G ν L y ≠ 0 → passesAnchors E G L y) := by
  sorry

/-- Deleting one anchor changes the normalized filtered law by at most the inverse retained fraction. -/
theorem filt_delete_bound {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (w : Fin N) (θ : ℝ)
    (hθ : 0 < θ) (hw : w ∈ L)
    (hDel : 0 < filterMass E G ν (L.erase w))
    (hFull : 0 < filterMass E G ν L)
    (hretained : θ * filterMass E G ν (L.erase w) ≤ filterMass E G ν L) :
    ∀ y, filt E G ν L y ≤ θ⁻¹ * filt E G ν (L.erase w) y := by
  sorry

/-- L7.1b's cap consequence for a valid cell row; `L` is the ordered cross-and-own anchor list. -/
theorem cell_row_cap_of_retention {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (n s : ℕ) (d c : ℝ)
    (hn : 2 ≤ n) (hN : 0 < N)
    (hraw : ∀ y, ν.w y ≤ Real.exp ((n : ℝ) ^ (d / 2)) / N)
    (hretained : (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(2 * c * (s : ℝ))) ≤
      filterMass E G ν L) :
    ∀ y, filt E G ν L y ≤
      Real.exp ((n : ℝ) ^ (d / 2) + 2 * c * (s : ℝ) * Real.log (n : ℝ) + 1) / N := by
  sorry

end HypercubeRamsey.S07
