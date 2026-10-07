import HypercubeRamsey.S18.Pools_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem scopedPatchSlots_card_le (D : LateData hPT) (region : Finset D.geom.Cell)
    (m : ℕ) (hm : ∀ C ∈ region, D.geom.nslot C ≤ m) (i : Fin PT.tiling.m) :
    (scopedPatchSlots D region i).card ≤ region.card * m := by
  classical
  let J := region.biUnion (fun C => (Finset.univ : Finset (Fin (D.geom.nslot C))).image
    (fun t => (⟨C, t⟩ : S16.CellSlot D.geom)))
  have hsub : scopedPatchSlots D region i ⊆ J := by
    intro s hs
    exact Finset.mem_biUnion.mpr ⟨s.1, (Finset.mem_filter.mp hs).2.1,
      Finset.mem_image.mpr ⟨s.2, Finset.mem_univ _, rfl⟩⟩
  calc
    (scopedPatchSlots D region i).card ≤ J.card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ region, ((Finset.univ : Finset (Fin (D.geom.nslot C))).image
        (fun t => (⟨C, t⟩ : S16.CellSlot D.geom))).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ region, D.geom.nslot C := by
      apply Finset.sum_le_sum
      intro C _
      exact (Finset.card_image_le).trans (by simp)
    _ ≤ ∑ _C ∈ region, m := Finset.sum_le_sum (fun C hC => hm C hC)
    _ = region.card * m := by simp

theorem slot_count_le_uniform (hκ : κ.Admissible) (D : LateData hPT) (C : D.geom.Cell) :
    D.geom.nslot C ≤ ⌈κ.Kcell * (T.S.n k : ℝ) ^ κ.Ac⌉₊ := by
  let i := D.geom.cellPatch C
  obtain ⟨y, hy⟩ := (hPT.tiling_valid.patch_nonempty i).2
  obtain ⟨B, hB, hyB⟩ := (PT.tiling.P i).bins.exists_mem hy
  have hd : 0 < (PT.tiling.P i).d :=
    (Finset.card_pos.mpr ⟨y, hyB⟩).trans_eq (hPT.tiling_valid.bins_card i B hB)
  have hd' : (1 : ℝ) ≤ (PT.tiling.P i).d := by exact_mod_cast hd
  have hθ : 0 < κ.θstar := hκ.bucket.2.2.2.2
  have hKcell : 0 < κ.Kcell := lt_of_lt_of_le (by positivity) hκ.Kcell_big
  have hX : 0 ≤ κ.Kcell * (T.S.n k : ℝ) ^ κ.Ac := by positivity
  rw [D.l16_valid.slot_eq C]
  apply Nat.ceil_mono
  simp only [Real.rpow_eq_pow, Real.rpow_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr
  nlinarith

theorem scopedPatchSlots_card_polynomial (hκ : κ.Admissible) (D : LateData hPT)
    (region : Finset D.geom.Cell) (hregion : region.card ≤ T.S.n k * (T.S.n k + 1))
    (hn : 2 ≤ T.S.n k) (hK : κ.Kcell ≤ (T.S.n k : ℝ)) (i : Fin PT.tiling.m) :
    (scopedPatchSlots D region i).card ≤ T.S.n k ^ (κ.Ac + 4) := by
  have hnR : 0 ≤ (T.S.n k : ℝ) := Nat.cast_nonneg _
  have hceil : ⌈κ.Kcell * (T.S.n k : ℝ) ^ κ.Ac⌉₊ ≤ T.S.n k ^ (κ.Ac + 1) := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_pow, pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hK (pow_nonneg hnR κ.Ac)
  calc
    (scopedPatchSlots D region i).card ≤ region.card * ⌈κ.Kcell * (T.S.n k : ℝ) ^ κ.Ac⌉₊ :=
      scopedPatchSlots_card_le D region _ (fun C _ => slot_count_le_uniform hκ D C) i
    _ ≤ (T.S.n k * (T.S.n k + 1)) * T.S.n k ^ (κ.Ac + 1) := Nat.mul_le_mul hregion hceil
    _ ≤ (T.S.n k * T.S.n k ^ 2) * T.S.n k ^ (κ.Ac + 1) := by
      have hb : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)
    _ = T.S.n k ^ (κ.Ac + 4) := by ring

theorem pool_cost_product_le_two (D : LateData hPT) (region : Finset D.geom.Cell)
    (n : ℕ) (M E : ℝ) (hM : 0 ≤ M) (hE : 0 < E)
    (hregion : (region.card : ℝ) ≤ n * (n + 1))
    (hslots : ∀ i, ((scopedPatchSlots D region i).card : ℝ) ≤ M)
    (hbins : ∀ i, 2 * (E + 1) ^ 2 ≤ Fintype.card (Bin PT.tiling i))
    (hbudget : M * (n + 1) ≤ E) :
    (∏ i : Fin PT.tiling.m, (1 + ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
      Fintype.card (Bin PT.tiling i))) ≤ 2 := by
  classical
  let W := region.image D.geom.cellPatch
  let u := fun i : Fin PT.tiling.m => ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
    Fintype.card (Bin PT.tiling i)
  have hu : ∀ i, 0 ≤ u i := by intro i; dsimp [u]; positivity
  have houtside : ∀ i, i ∉ W → u i = 0 := by
    intro i hi
    have hEmpty : scopedPatchSlots D region i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro slot hs
      obtain ⟨hC, hpatch⟩ := (Finset.mem_filter.mp hs).2
      exact hi (Finset.mem_image.mpr ⟨slot.1, hC, hpatch⟩)
    simp only [u, hEmpty, Finset.card_empty, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
  have hbound : ∀ i, u i ≤ M ^ 2 / (2 * E ^ 2) := by
    intro i
    have hb : 2 * E ^ 2 ≤ (Fintype.card (Bin PT.tiling i) : ℝ) := by
      nlinarith [hbins i]
    have hbinPos : 0 < (Fintype.card (Bin PT.tiling i) : ℝ) :=
      lt_of_lt_of_le (by positivity) hb
    have hs0 : 0 ≤ ((scopedPatchSlots D region i).card : ℝ) := Nat.cast_nonneg _
    dsimp [u]
    calc
      _ ≤ M ^ 2 / (Fintype.card (Bin PT.tiling i) : ℝ) := by gcongr; exact hslots i
      _ ≤ M ^ 2 / (2 * E ^ 2) := by gcongr
  have hsum : (∑ i ∈ W, u i) ≤ 1 / 2 := by
    have hcard : (W.card : ℝ) ≤ region.card := by
      exact_mod_cast (Finset.card_image_le : W.card ≤ region.card)
    have ha : 0 ≤ M ^ 2 / (2 * E ^ 2) := by positivity
    have hregion' : (region.card : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hmul : (region.card : ℝ) * M ^ 2 ≤ (M * (n + 1)) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right hregion' (sq_nonneg M)
      nlinarith
    have hsquare : (M * (n + 1)) ^ 2 ≤ E ^ 2 := by gcongr
    calc
      (∑ i ∈ W, u i) ≤ ∑ _i ∈ W, M ^ 2 / (2 * E ^ 2) :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = (W.card : ℝ) * (M ^ 2 / (2 * E ^ 2)) := by simp
      _ ≤ region.card * (M ^ 2 / (2 * E ^ 2)) := mul_le_mul_of_nonneg_right hcard ha
      _ = ((region.card : ℝ) * M ^ 2) / (2 * E ^ 2) := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ (by positivity : 0 < 2 * E ^ 2)).mpr (by linarith [hmul.trans hsquare])
  have hprod : (∏ i ∈ W, (1 + u i)) = ∏ i : Fin PT.tiling.m, (1 + u i) := by
    apply Finset.prod_subset (Finset.subset_univ W)
    intro i _ hi
    rw [houtside i hi, add_zero]
  change (∏ i : Fin PT.tiling.m, (1 + u i)) ≤ 2
  rw [← hprod]
  calc
    (∏ i ∈ W, (1 + u i)) ≤ ∏ i ∈ W, Real.exp (u i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        linarith [hu i]
      · intro i _
        simpa only [add_comm] using Real.add_one_le_exp (u i)
    _ = Real.exp (∑ i ∈ W, u i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hsum
    _ ≤ 2 := by
      have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at hh
        linarith
      exact (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (by norm_num))

theorem polynomial_pool_budget {b n : ℕ} (hn : 2 ≤ n)
    (hlog : (b + 2 : ℝ) ≤ Real.log (n : ℝ)) :
    (n : ℝ) ^ b * (n + 1) ≤ Real.exp (Real.log (n : ℝ) ^ 10) := by
  let y := Real.log (n : ℝ)
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hy1 : 1 ≤ y := by dsimp [y]; linarith
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnplus : (n + 1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hy2 : y ^ 2 ≤ y ^ 10 := pow_le_pow_right₀ hy1 (by norm_num)
  have hby : (b + 2 : ℝ) * y ≤ y ^ 2 := by
    dsimp [y] at hy1 ⊢
    nlinarith
  calc
    (n : ℝ) ^ b * (n + 1) ≤ (n : ℝ) ^ b * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hnplus (pow_nonneg hnPos.le b)
    _ = (n : ℝ) ^ (b + 2) := (pow_add _ _ _).symm
    _ = Real.exp ((b + 2 : ℕ) * y) := by
      rw [Real.exp_nat_mul, show Real.exp y = (n : ℝ) from Real.exp_log hnPos]
    _ ≤ Real.exp (y ^ 10) := Real.exp_le_exp.mpr (by exact_mod_cast hby.trans hy2)

theorem eventually_pool_budget (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      ∀ region : Finset D.geom.Cell, region.card ≤ T.S.n k * (T.S.n k + 1) →
      (∀ i, ((scopedPatchSlots D region i).card : ℝ) ≤ Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10)) ∧
      (∀ i, 2 * (((scopedPatchSlots D region i).card : ℝ) + 1) ^ 2 ≤ Fintype.card (Bin PT.tiling i)) ∧
      (∏ i : Fin PT.tiling.m, (1 + ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
        Fintype.card (Bin PT.tiling i))) ≤ 2 := by
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hlog := (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop (κ.Ac + 6 : ℝ)
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2, hnR.eventually_ge_atTop κ.Kcell, hlog]
    with k hn hK hl
  intro PT hPT D region hregion
  let M : ℝ := (T.S.n k : ℝ) ^ (κ.Ac + 4)
  let E : ℝ := Real.exp (Real.log (T.S.n k : ℝ) ^ 10)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hslots : ∀ i, ((scopedPatchSlots D region i).card : ℝ) ≤ M := by
    intro i
    dsimp [M]
    exact_mod_cast scopedPatchSlots_card_polynomial hκ D region hregion hn hK i
  have hb : M * (T.S.n k + 1) ≤ E := by
    exact polynomial_pool_budget hn (by exact_mod_cast hl)
  have hMle : M ≤ E := by
    have hn' : (0 : ℝ) ≤ T.S.n k := Nat.cast_nonneg _
    nlinarith
  obtain ⟨p⟩ := D.l16_valid.physical
  have hbins : ∀ i, 2 * (E + 1) ^ 2 ≤ Fintype.card (Bin PT.tiling i) := by
    intro i
    simpa only [E, Real.rpow_eq_pow, Real.rpow_ofNat] using p.geometry.scale.comparison_room i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [E, Real.rpow_eq_pow, Real.rpow_ofNat] using (hslots i).trans hMle
  · intro i
    apply le_trans _ (hbins i)
    have hs0 : 0 ≤ ((scopedPatchSlots D region i).card : ℝ) := Nat.cast_nonneg _
    have hs := (hslots i).trans hMle
    nlinarith
  · exact pool_cost_product_le_two D region (T.S.n k) M E hM hE
      (by exact_mod_cast hregion) hslots hbins hb

theorem perm_iid_fresh_comparison (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid, ∀ D : LateData hPT,
      D.Spec → ∀ A : InitialPairData D, ∀ assignment,
        A.permFreshTest assignment ≤ 2 * A.iidFreshTest assignment := by
  filter_upwards [eventually_pool_budget hκ T] with k hbudget
  intro PT hPT D hD A assignment
  obtain ⟨hsize, hroom, hcost⟩ := hbudget PT hPT D A.scope (scope_card D A)
  apply permFresh_comparison_of_scoped_pool D A assignment
  exact scoped_pool_comparison D A.scope hsize hroom hcost (scopedFreshPoolTest D A assignment)
    (scopedFreshPoolTest_nonneg D A assignment) (scopedFreshPoolTest_local D hD A assignment)

end HypercubeRamsey.S18.Lane_sol_s18_n5
