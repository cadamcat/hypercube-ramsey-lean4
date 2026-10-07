import HypercubeRamsey.S16.Producers_sol_s16_prod1
namespace HypercubeRamsey.S16.Lane_sol_s16_prod1
open Classical
open scoped BigOperators

theorem solver_star_trimmed_any_pin_mean7 {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯} [Nonempty (Bin 𝒯 i)]
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (v : EvenRole 𝒯 i) (hW : S.Hgood v W)
    (hEps : 0 < sliceEps κ (𝒯.P i).h ∧ sliceEps κ (𝒯.P i).h ≤ 1)
    (P : Group 𝒯 i → FinLaw (Bin 𝒯 i)) (c : ℝ) (hc : 1 ≤ c)
    (hP : ∀ g ∈ solver_star_group_scope S v, ∀ D, (P g).w D ≤ c * S.q g W D)
    (g : Group 𝒯 i) (D : Bin 𝒯 i) (hD : D ∈ S.pretrimBins W g) :
    (FinLaw.pi (coordinatePin P g D)).E (solver_star_bin_failure S W v) ≤
      c ^ (solver_star_group_scope S v).card * Real.sqrt (sliceEps κ (𝒯.P i).h) := by
  classical
  by_cases hg : g ∈ solver_star_group_scope S v
  · have hvg : SliceSolver.Incident v g := by
      obtain ⟨j, _, heq⟩ := Finset.mem_image.mp hg
      rw [← heq]
      refine ⟨j, S.groupOf_spec _ ?_⟩
      rw [flip_parity]
      exact not_not.mpr v.2
    exact solver_star_trimmed_pin_mean S W v P c hc hP g D hD hvg
  · have hEq : (FinLaw.pi (coordinatePin P g D)).E (solver_star_bin_failure S W v) =
        (FinLaw.pi P).E (solver_star_bin_failure S W v) := by
      apply pi_E_local _ _ (solver_star_group_scope S v) _ (solver_star_bin_failure_local S W v)
      intro j hj
      have hjg : j ≠ g := by intro h; exact hg (h ▸ hj)
      simp only [coordinatePin, if_neg hjg]
    rw [hEq]
    have hroot : sliceEps κ (𝒯.P i).h ≤ Real.sqrt (sliceEps κ (𝒯.P i).h) := by
      apply (Real.le_sqrt hEps.1.le hEps.1.le).mpr
      nlinarith [sq_nonneg (sliceEps κ (𝒯.P i).h)]
    exact (solver_star_trimmed_mean S W v hW P c (le_trans (by norm_num) hc) hP).trans
      (mul_le_mul_of_nonneg_left hroot (pow_nonneg (le_trans (by norm_num) hc) _))

end HypercubeRamsey.S16.Lane_sol_s16_prod1
