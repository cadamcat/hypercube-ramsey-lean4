import HypercubeRamsey.Tools.Concentration

/-!
# Random-order concentration

X-PermConc is the finite permutation bounded-differences estimate, obtained from the reveal martingale and
the finite Azuma tool. A transposition changes at most two images.
-/

namespace HypercubeRamsey

/-- Uniform finite law on permutations of a finite type. -/
noncomputable def uniformPermutationLaw {ι : Type*} [Fintype ι] [DecidableEq ι] :
    FinProb (Equiv.Perm ι) := by
  classical
  exact FinProb.uniform Finset.univ ⟨Equiv.refl ι, by simp⟩

/-- X-PermConc: a statistic changing by at most `c` under any transposition has a sub-Gaussian tail under
the uniform random order. -/
theorem xPermConc {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Equiv.Perm ι → ℝ)
    (c t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hlip : ∀ σ τ : Equiv.Perm ι,
      (Finset.univ.filter (fun i : ι => σ i ≠ τ i)).card ≤ 2 → |f σ - f τ| ≤ c) :
    (uniformPermutationLaw (ι := ι)).pr
        (fun σ => t ≤ |f σ - (uniformPermutationLaw (ι := ι)).expect f|) ≤
      2 * Real.exp (-2 * t ^ 2 / ((Fintype.card ι : ℝ) * c ^ 2)) := by
  classical
  sorry

end HypercubeRamsey
