import HypercubeRamsey.S07.Needs

/-! Small finite-support facts used in the Section 7 availability-to-absence conversions. -/

namespace HypercubeRamsey.S07

open Classical

/-- The positive support of a finite law. -/
noncomputable def lawSupport {N : ℕ} (μ : Law N) : Finset (Fin N) :=
  Finset.univ.filter fun x => 0 < μ.w x

theorem law_supportedIn_support {N : ℕ} (μ : Law N) : μ.SupportedIn (lawSupport μ) := by
  classical
  intro x hx
  have hnot : ¬ 0 < μ.w x := by
    intro hpos
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
  have hzero : μ.w x = 0 := le_antisymm (not_lt.mp hnot) (μ.nonneg x)
  exact hzero

theorem law_support_subset {N : ℕ} {μ : Law N} {A : Finset (Fin N)}
    (hμ : μ.SupportedIn A) : lawSupport μ ⊆ A := by
  classical
  intro x hx
  by_contra hnot
  have hzero := hμ x hnot
  have hpos := (Finset.mem_filter.mp hx).2
  rw [hzero] at hpos
  norm_num at hpos

end HypercubeRamsey.S07
