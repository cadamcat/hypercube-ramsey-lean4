import HypercubeRamsey.S17.Needs

namespace HypercubeRamsey.S18.Lane_sol_d18l_up

open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

/-- The current profile validity supplies exactly the inequality defining
S18.ProfileCornerMass. The explicit form avoids importing the S18 producers. -/
theorem profileCornerMass_of_valid (hPT : PT.Valid) :
    ∀ i q, q ∈ PT.activeVertices →
      ((PT.tiling.P i).M : ℝ) ≤ 2 * (PT.mesh.corner q i).card := by
  intro i q hq
  have h := (hPT.corner_clean i q hq).card_lower
  linarith

/-- The two numerical mass contracts are different even with integral sizes.
This is an interface counterexample, not a counterexample to a pool tail. -/
theorem half_mass_does_not_imply_strong (a : ℝ) (ha : a < 1 / 2) :
    ∃ M c : ℕ, 0 < M ∧ 0 < c ∧ (M : ℝ) ≤ 2 * c ∧
      (c : ℝ) < (1 - a) * M := by
  refine ⟨2, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num
  linarith

/-- Every legacy S17 certificate still demands the stronger corner contract. -/
theorem no_legacy_certificate_at_small_corner
    (D : ListGateContext κ T k PT) (K : ℝ) (i : Fin PT.tiling.m)
    (q : PT.mesh.V) (hq : q ∈ PT.activeVertices)
    (hsmall : ((PT.mesh.corner q i).card : ℝ) <
      (1 - κ.a) * (PT.tiling.P i).M) :
    ¬ Nonempty (D.L16QuantitativeValidity K) := by
  rintro ⟨h⟩
  exact (not_lt_of_ge (h.corner_size i q hq)) hsmall

/-- Half-mass cleaning supplies the direct-prior atom cap used in the paper. -/
theorem uniform_corner_atom_cap (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (q : PT.mesh.V) (hq : q ∈ PT.activeVertices)
    (x : Fin (T.S.N k)) :
    (if x ∈ PT.mesh.corner q i then
      1 / ((PT.mesh.corner q i).card : ℝ) else 0) ≤
        2 / ((PT.tiling.P i).M : ℝ) := by
  have hMnat : 0 < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by exact_mod_cast hMnat
  have hhalf := (hPT.corner_clean i q hq).card_lower
  have hc : 0 < ((PT.mesh.corner q i).card : ℝ) := by linarith
  split_ifs
  · calc
      1 / ((PT.mesh.corner q i).card : ℝ) ≤
          1 / (((PT.tiling.P i).M : ℝ) / 2) :=
        one_div_le_one_div_of_le (by positivity) hhalf
      _ = 2 / ((PT.tiling.P i).M : ℝ) := by field_simp
  · exact div_nonneg (by norm_num) hM.le

end HypercubeRamsey.S18.Lane_sol_d18l_up
