import HypercubeRamsey.S18.ProducerInputs
import HypercubeRamsey.S18.ProfileBridge_q_s18_bridge

namespace HypercubeRamsey.S18

open Classical Filter
open scoped BigOperators
open S16.Lane_sol_fix2_s16

/-- D14.M (14:9–14): triangulate the capped law/price polytope, clean at
its vertices using L13.4, and use stability at every positively weighted
parameter. This constructs mesh geometry, not a profile fixed point. -/
theorem cleaned_profile_mesh_exists {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (h𝒯 : 𝒯.Valid) (hcluster : 𝒯.mode.isCluster)
    (hclean : ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
      ∃ C : Finset (Fin (T.S.N k)),
        ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧ CleanProps 𝒯 i π C ∧
        (𝒯.mode.isCluster → ∀ π',
          NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C)) :
    ∃ mesh : Mesh 𝒯, S14.MeshCleaned mesh ∧ Nonempty (S14.MeshProfileDomain mesh) ∧
      S14.MeshReady mesh := by
  exact Lane_q_s18_bridge.cleaned_profile_mesh_exists_helper 𝒯 h𝒯 hcluster hclean

private def zeroGroup {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) : Group 𝒯 i :=
  ⟨fun _ => false, by simp [IsEvenRole], by funext j; simp [wordSyndrome]⟩

private noncomputable def binMeanLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r) : Law (T.S.N k) where
  w y := S.oddMarginal g W y
  nonneg y := Finset.sum_nonneg fun D _ => mul_nonneg (S.q_nonneg g W D) (S.U_nonneg g W D y)
  sum_eq_one := by
    dsimp [SliceSolver.oddMarginal]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, S.U_sum, mul_one]
    exact S.q_sum g W

/-- The unrestricted odd mean is a law, with the same weights at every group. -/
noncomputable def rawMeanLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) : Law (T.S.N k) where
  w y := S.oddMean p (zeroGroup 𝒯 i) y
  nonneg y := Finset.sum_nonneg fun W _ =>
    mul_nonneg ((S.recLaw p).nonneg W) ((binMeanLaw S (zeroGroup 𝒯 i) W).nonneg y)
  sum_eq_one := by
    dsimp [SliceSolver.oddMean, FinLaw.E]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hm : ∀ W, ∑ y, S.oddMarginal (zeroGroup 𝒯 i) W y = 1 :=
      fun W => (binMeanLaw S (zeroGroup 𝒯 i) W).sum_eq_one
    simp_rw [hm, mul_one]
    exact (S.recLaw p).sum_one

theorem rawMeanLaw_weight {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i) (y : Fin (T.S.N k)) :
    (rawMeanLaw S p).w y = S.oddMean p g y :=
  S.averaged_marginal_invariant p (zeroGroup 𝒯 i) g y

private theorem law_eq_of_weights {N : ℕ} {μ ν : Law N}
    (h : ∀ y, μ.w y = ν.w y) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

/-- Read out P14.2's selected parameter and solver family as D14.P. -/
noncomputable def clusterProfile {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} {hclean : S14.MeshCleaned mesh}
    (B : S14.BalancedProfile hclean) : ProfiledTiling κ T k where
  tiling := 𝒯
  mesh := mesh
  parameter := B.fixedPoint.point
  π := mesh.paramLaw B.fixedPoint.point
  πraw i := rawMeanLaw (B.solvers.solverAt i).solver B.fixedPoint.point
  envelope := S14.profileEnvelope B.fixedPoint.point
  solver i := some (B.solvers.solverAt i).solver
  tvError i := (1 / 2 : ℝ) * ∑ y,
    |(rawMeanLaw (B.solvers.solverAt i).solver B.fixedPoint.point).w y -
      (mesh.paramLaw B.fixedPoint.point i).w y|

/-- Every shared D14.P field is a projection or equality transport from P14.2. -/
theorem clusterProfile_valid {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} {hclean : S14.MeshCleaned mesh}
    (h𝒯 : 𝒯.Valid) (hc : 𝒯.mode.isCluster) (B : S14.BalancedProfile hclean) :
    (clusterProfile B).Valid := by
  refine {
    tiling_valid := h𝒯
    param_law := fun _ => rfl
    law_supported := mesh.paramLaw_supp B.fixedPoint.point
    law_uniform_direct := Or.inl hc
    law_cap := B.cap
    tv_error_eq := fun _ => rfl
    envelope_eq := fun _ => rfl
    corner_clean := fun i v hv => B.corner_clean v i hv
    direct_single_corner := fun hn => (hn hc).elim
    envelope_subset := B.envelope_subset
    envelope_degree := B.envelope_degree
    envelope_other_degree := B.envelope_other_degree
    envelope_row_tail := B.envelope_row_tail
    cluster_solver := fun _ i => ⟨(B.solvers.solverAt i).solver, rfl⟩
    raw_profile := ?_
    raw_direct := fun hn => (hn hc).elim
    high_profile := ?_
    low_profile := ?_
    tv_error_nonneg := ?_
    low_profile_tv := ?_ }
  · intro _ i S hs g y
    have he : (B.solvers.solverAt i).solver = S := Option.some.inj hs
    subst S
    exact rawMeanLaw_weight _ _ g y
  · intro hm i
    change 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge at hm
    apply law_eq_of_weights
    intro y
    change (mesh.paramLaw B.fixedPoint.point i).w y =
      (rawMeanLaw (B.solvers.solverAt i).solver B.fixedPoint.point).w y
    rw [B.fixedPoint.fixed_profile i (zeroGroup 𝒯 i) y]
    have hn : 𝒯.mode ≠ .lowCluster := by rcases hm with hm | hm <;> simp [hm]
    simp [S14.outputWeight, hn, S14.rawWeight, rawMeanLaw]
  · intro hm i S hs g y
    change 𝒯.mode = .lowCluster at hm
    have he : (B.solvers.solverAt i).solver = S := Option.some.inj hs
    subst S
    change (mesh.paramLaw B.fixedPoint.point i).w y =
      (B.solvers.solverAt i).solver.lowOut B.fixedPoint.point g y
    simpa [S14.outputWeight, hm] using B.fixedPoint.fixed_profile i g y
  · intro i
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · intro hm i
    exact B.low_tv i hm (zeroGroup 𝒯 i)

/-- Preserve the uniform-subset output of the actual S14 solver constructor. -/
theorem clusterProfile_uniform {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {mesh : Mesh 𝒯} {hclean : S14.MeshCleaned mesh}
    (B : S14.BalancedProfile hclean) : SolverLabelsUniform (clusterProfile B) := by
  intro _ i S hs
  have he : (B.solvers.solverAt i).solver = S := Option.some.inj hs
  subst S
  exact (B.solvers.solverAt i).labels_uniform

/-- In direct and bounded modes use the one cleaned corner and fixed
uniform second law (14:229). There is no internal solver. -/
noncomputable def directMesh {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (h𝒯 : 𝒯.Valid)
    (corners : Fin 𝒯.m → Finset (Fin (T.S.N k))) : Mesh 𝒯 where
  V := Unit
  Param := Unit
  paramLaw _ i := Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2
  paramPrice _ i := (Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2).w
  paramLaw_supp := by intro p i y hy; simp [Law.unifCore, hy]
  paramLaw_cap := by
    intro p i y
    have hM : 0 < ((𝒯.P i).M : ℝ) := by
      exact_mod_cast (h𝒯.patch_nonempty i).2.card_pos.trans_eq (𝒯.P i).cardY
    have he : 1 ≤ Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i) := by
      apply Real.one_le_exp_iff.mpr
      positivity
    simp only [Law.unifCore]
    split_ifs
    · rw [(𝒯.P i).cardY, mul_inv_cancel₀ hM.ne']
      exact he
    · simpa using (Real.exp_pos (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)).le
  paramPrice_simplex := by
    intro p i
    refine ⟨(Law.unifCore _ _).nonneg, ?_, (Law.unifCore _ _).sum_eq_one⟩
    intro y hy
    simp [Law.unifCore, hy]
  base _ := ()
  wt _ _ := 1
  corner _ := corners
  wt_cont _ := continuous_const
  wt_nonneg _ _ := by norm_num
  wt_sum_one _ := by simp
  local_law := by intro v p hv i; simp
  local_price := by intro v p hv i y; simp; positivity
  active_bound _ := by simp

noncomputable def directProfile {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (h𝒯 : 𝒯.Valid)
    (corners : Fin 𝒯.m → Finset (Fin (T.S.N k))) : ProfiledTiling κ T k where
  tiling := 𝒯
  mesh := directMesh 𝒯 h𝒯 corners
  parameter := ()
  π i := Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2
  πraw i := Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2
  envelope := corners
  solver _ := none
  tvError _ := 0

theorem directProfile_valid {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (h𝒯 : 𝒯.Valid) (hn : ¬ 𝒯.mode.isCluster)
    (corners : Fin 𝒯.m → Finset (Fin (T.S.N k)))
    (hclean : ∀ i, CleanProps 𝒯 i
      (fun j => Law.unifCore (𝒯.P j).Y (h𝒯.patch_nonempty j).2) (corners i)) :
    (directProfile 𝒯 h𝒯 corners).Valid := by
  refine {
    tiling_valid := h𝒯
    param_law := fun _ => rfl
    law_supported := ?_
    law_uniform_direct := Or.inr (fun _ => rfl)
    law_cap := ?_
    tv_error_eq := by intro i; simp [directProfile]
    envelope_eq := by
      intro i
      change corners i = ((Finset.univ : Finset Unit).filter (fun _ => 0 < (1 : ℝ))).biUnion (fun _ => corners i)
      simp
    corner_clean := fun i v _ => hclean i
    direct_single_corner := by
      intro _
      change ((Finset.univ : Finset Unit).filter (fun _ => 0 < (1 : ℝ))).card = 1
      simp
    envelope_subset := fun i => (hclean i).sub
    envelope_degree := fun i => (hclean i).degOwn
    envelope_other_degree := fun i => (hclean i).degOther
    envelope_row_tail := fun i => (hclean i).rowTail
    cluster_solver := fun hc => (hn hc).elim
    raw_profile := fun hc => (hn hc).elim
    raw_direct := fun _ _ => rfl
    high_profile := ?_
    low_profile := ?_
    tv_error_nonneg := fun _ => le_rfl
    low_profile_tv := by intro _ i; dsimp [directProfile]; positivity }
  · intro i y hy
    change y ∉ (𝒯.P i).Y at hy
    change (Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2).w y = 0
    simp [Law.unifCore, hy]
  · intro i y
    have hM : 0 < ((𝒯.P i).M : ℝ) := by
      exact_mod_cast (h𝒯.patch_nonempty i).2.card_pos.trans_eq (𝒯.P i).cardY
    change (if y ∈ (𝒯.P i).Y then ((𝒯.P i).Y.card : ℝ)⁻¹ else 0) ≤ 11 / (𝒯.P i).M
    rw [(𝒯.P i).cardY]
    split_ifs <;> (simp only [div_eq_mul_inv]; nlinarith [inv_pos.mpr hM])
  · intro _ i; rfl
  · intro hm
    change 𝒯.mode = .lowCluster at hm
    exact (hn (by simp [hm, Mode.isCluster])).elim

/-- C14.F assembly: S13 allocation and cleaning, then the mesh and P14.2,
or the direct one-corner construction. Both orientations use the same constants. -/
theorem producer_profiled_tiling_exists {κ : CConsts} (hκ : κ.Admissible)
    (hconst : S14.HeightConstantContract κ) (T : Stage) (hInit : InitDisc T κ.η0)
    (hDisc : DeepDisc T κ.xs κ.α 0.04)
    (hDiscι : DeepDisc T κ.xι κ.αι (κ.ι / 2)) (hClu : S13.ClusterAbsenceInput κ T) :
    ∀ᶠ k in atTop, ∃ o : Bool, ∃ PT : ProfiledTiling κ (T.orient o) k,
      PT.Valid ∧ SolverLabelsUniform PT := by
  have ha := S13.extraction_allocation κ hκ T hInit hDisc hDiscι hClu
  have hc0 := S13.stable_cleaning κ hκ T hInit hDiscι hDisc
  have hc1 := S13.stable_cleaning κ hκ T.swap
    (orient_init hInit true) (orient_deep_budget hDiscι true) (orient_deep_budget hDisc true)
  have hb0 := S14.balanced_profiles κ hκ hconst T hInit
  have hb1 := S14.balanced_profiles κ hκ hconst T.swap (orient_init hInit true)
  filter_upwards [ha, hc0, hc1, hb0, hb1] with k ha hc0 hc1 hb0 hb1
  obtain ⟨o, 𝒯, h𝒯⟩ := ha
  have hclean : ∀ i (π : Fin 𝒯.m → Law ((T.orient o).S.N k)), InputOK 𝒯 h𝒯 π →
      ∃ C : Finset (Fin ((T.orient o).S.N k)),
        ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧ CleanProps 𝒯 i π C ∧
        (𝒯.mode.isCluster → ∀ π',
          NearInput π π' (((T.orient o).S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C) := by
    cases o with
    | false => exact hc0 𝒯 h𝒯
    | true => exact hc1 𝒯 h𝒯
  by_cases hcluster : 𝒯.mode.isCluster
  · obtain ⟨mesh, hmesh, ⟨domain⟩, ready⟩ := cleaned_profile_mesh_exists 𝒯 h𝒯 hcluster hclean
    have hb : Nonempty (S14.BalancedProfile (𝒯 := 𝒯) (mesh := mesh) hmesh) := by
      cases o with
      | false => exact hb0 𝒯 h𝒯 hcluster mesh hmesh domain ready
      | true => exact hb1 𝒯 h𝒯 hcluster mesh hmesh domain ready
    obtain ⟨B⟩ := hb
    exact ⟨o, clusterProfile B, clusterProfile_valid h𝒯 hcluster B, clusterProfile_uniform B⟩
  · let π i := Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2
    have hπ : InputOK 𝒯 h𝒯 π := by
      intro i
      refine ⟨?_, ?_⟩
      · intro y hy; simp [π, Law.unifCore, hy]
      · simp [hcluster, π]
    have hc : ∀ i, ∃ C, CleanProps 𝒯 i π C := by
      intro i
      obtain ⟨C, _, hC, _⟩ := hclean i π hπ
      exact ⟨C, hC⟩
    choose corners hcorners using hc
    exact ⟨o, directProfile 𝒯 h𝒯 corners, directProfile_valid 𝒯 h𝒯 hcluster corners hcorners,
      fun hc => (hcluster hc).elim⟩

end HypercubeRamsey.S18
