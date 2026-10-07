import HypercubeRamsey.S18.Nodes_sol_s18_3f
import HypercubeRamsey.S18.ReferenceProduct_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- The whole resampling horizon, including every prescribed slot, has
subexponential size uniformly over the queried seed. -/
theorem horizon_tokens_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), D.Spec → ∀ seed : Finset D.geom.Cell,
      (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
      ((D.expandCells seed).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 4) ∧
      ∀ i, ((scopedPatchSlots D (D.expandCells seed) i).card : ℝ) ≤
        Real.exp (Real.log (T.S.n k) ^ 4) := by
  let C : ℝ := 2 * κ.A0 / Real.log 2
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hl := (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop
    (max 2 (20 * (κ.Ac + 4) + 10 * C))
  filter_upwards [HypercubeRamsey.Lane_sol_s18_3f.testTokensEventually hκ T, hl,
    T.S.n_tendsto.eventually_ge_atTop 2] with k ht hl hn
  intro PT hPT D hD seed hseed
  let y := Real.log (T.S.n k : ℝ)
  have hy : 2 ≤ y := (le_max_left _ _).trans hl
  have hyC : 20 * (κ.Ac + 4) + 10 * C ≤ y := (le_max_right _ _).trans hl
  have hTs : (D.encoding.Ts : ℝ) ≤ y ^ 2 + 1 := by
    rw [D.encoding.Ts_eq]
    exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hr : (D.geom.r : ℝ) ≤ C * y := by
    dsimp [C, y]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr D.l16_valid.r_upper
  have hy2 : 1 ≤ y ^ 2 := by nlinarith
  have hyy : y ≤ y ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := by
    nlinarith [show (0 : ℝ) ≤ D.geom.r from Nat.cast_nonneg _]
  have hexp : 10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) ≤ y ^ 3 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hTs (show (0 : ℝ) ≤ κ.Ac + 4 by positivity)
    have hCr := mul_le_mul_of_nonneg_left hyy hC0
    have hlim := mul_le_mul_of_nonneg_right hyC (sq_nonneg y)
    nlinarith
  have hpower : Real.rpow (T.S.n k : ℝ)
      (10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ)) ≤ Real.exp (y ^ 4) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos (show (0 : ℝ) < T.S.n k by exact_mod_cast (by omega : 0 < T.S.n k))]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hexp (by linarith : 0 ≤ y)
    dsimp [y] at hm ⊢
    nlinarith
  have ht' := (ht D hD seed hseed D.encoding.pools_nonempty.choose).trans hpower
  have hregion : ((D.expandCells seed).card : ℝ) ≤ Real.exp (y ^ 4) := by
    apply le_trans _ ht'
    exact_mod_cast (show (D.expandCells seed).card ≤
      (HypercubeRamsey.Lane_sol_s18_3f.testDomains D (D.expandCells seed)).card +
      (HypercubeRamsey.Lane_sol_s18_3f.testImages D (D.expandCells seed)
        D.encoding.pools_nonempty.choose).card + (D.expandCells seed).card by omega)
  refine ⟨hregion, ?_⟩
  intro i
  have hs : scopedPatchSlots D (D.expandCells seed) i ⊆
      HypercubeRamsey.Lane_sol_s18_3f.testDomains D (D.expandCells seed) := by
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2.1⟩
  apply le_trans _ ht'
  exact_mod_cast ((Finset.card_le_card hs).trans
    (show (HypercubeRamsey.Lane_sol_s18_3f.testDomains D (D.expandCells seed)).card ≤
      (HypercubeRamsey.Lane_sol_s18_3f.testDomains D (D.expandCells seed)).card +
      (HypercubeRamsey.Lane_sol_s18_3f.testImages D (D.expandCells seed)
        D.encoding.pools_nonempty.choose).card + (D.expandCells seed).card by omega))

private theorem horizon_room {y : ℝ} (hy : 2 ≤ y) :
    Real.exp (y ^ 4) * (Real.exp (y ^ 4) + 1) ≤ Real.exp (y ^ 10) := by
  have hpow : 3 * y ^ 4 ≤ y ^ 10 := by
    have h2 : 4 ≤ y ^ 2 := by nlinarith
    have h6 : 3 ≤ y ^ 6 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hy 6
      norm_num at hh
      linarith
    have hm := mul_le_mul_of_nonneg_left h6 (pow_nonneg (by linarith : 0 ≤ y) 4)
    simpa only [← pow_add, mul_comm] using hm
  have hM : 2 ≤ Real.exp (y ^ 4) := by
    have hh := Real.add_one_le_exp (y ^ 4)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hy 4
    norm_num at hp
    linarith
  calc
    _ ≤ Real.exp (y ^ 4) * Real.exp (y ^ 4) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      nlinarith
    _ = Real.exp (y ^ 4) ^ 3 := by ring
    _ = Real.exp (3 * y ^ 4) := (Real.exp_nat_mul _ 3).symm
    _ ≤ _ := Real.exp_le_exp.mpr hpow

/-- The physical comparison room accommodates growing complete horizons,
with a total cost of two across all patches. -/
theorem horizon_pool_budget_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), D.Spec → ∀ seed : Finset D.geom.Cell,
      (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
      (∀ i, ((scopedPatchSlots D (D.expandCells seed) i).card : ℝ) ≤
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10)) ∧
      (∀ i, 2 * (((scopedPatchSlots D (D.expandCells seed) i).card : ℝ) + 1) ^ 2 ≤
        Fintype.card (Bin PT.tiling i)) ∧
      (∏ i : Fin PT.tiling.m, (1 + ((scopedPatchSlots D (D.expandCells seed) i).card : ℝ) ^ 2 /
        Fintype.card (Bin PT.tiling i))) ≤ 2 := by
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  filter_upwards [horizon_tokens_eventually hκ T,
    (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop 2] with k ht hl
  intro PT hPT D hD seed hseed
  obtain ⟨hregion, hslots⟩ := ht D hD seed hseed
  let region := D.expandCells seed
  let M := Real.exp (Real.log (T.S.n k) ^ 4)
  let E := Real.exp (Real.log (T.S.n k) ^ 10)
  have hb : M * ((region.card : ℝ) + 1) ≤ E := by
    apply le_trans _ (horizon_room hl)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    change (region.card : ℝ) + 1 ≤ M + 1
    linarith
  have hMle : M ≤ E := by
    have hh : M ≤ M * ((region.card : ℝ) + 1) := by
      have hm : 0 ≤ M := (Real.exp_pos _).le
      have hc : (0 : ℝ) ≤ region.card := Nat.cast_nonneg _
      nlinarith
    exact hh.trans hb
  obtain ⟨p⟩ := D.l16_valid.physical
  have hbins : ∀ i, 2 * (E + 1) ^ 2 ≤ Fintype.card (Bin PT.tiling i) := by
    intro i
    simpa only [E, Real.rpow_eq_pow, Real.rpow_ofNat] using p.geometry.scale.comparison_room i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [E, Real.rpow_eq_pow, Real.rpow_ofNat] using (hslots i).trans hMle
  · intro i
    have hs := (hslots i).trans hMle
    have hs0 : 0 ≤ ((scopedPatchSlots D region i).card : ℝ) := Nat.cast_nonneg _
    exact (by nlinarith : 2 * (((scopedPatchSlots D region i).card : ℝ) + 1) ^ 2 ≤
      2 * (E + 1) ^ 2).trans (hbins i)
  · apply pool_cost_product_le_two D region region.card M E (Real.exp_pos _).le
      (Real.exp_pos _) _ hslots hbins hb
    have hc : (0 : ℝ) ≤ region.card := Nat.cast_nonneg _
    nlinarith

theorem perm_iid_horizon_comparison_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), D.Spec → ∀ seed : Finset D.geom.Cell,
      (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
      ∀ Ψ : D.encoding.InitInput → ℝ, (∀ x, 0 ≤ Ψ x) →
      (∀ x x', (∀ C ∈ D.expandCells seed, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) → Ψ x = Ψ x') →
      D.encoding.permLaw.E Ψ ≤ 2 * (D.encoding.initialLaw D.encoding.iidLaw).E Ψ := by
  filter_upwards [horizon_pool_budget_eventually hκ T] with k hk
  intro PT hPT D hD seed hseed Ψ hΨ hlocal
  obtain ⟨hsize, hroom, hcost⟩ := hk D hD seed hseed
  change (FinLaw.bind D.encoding.poolLaw (fun _ => tapeLaw D.fresh D.encoding.Ts)).E Ψ ≤
    2 * (FinLaw.bind D.encoding.iidLaw (fun _ => tapeLaw D.fresh D.encoding.Ts)).E Ψ
  rw [bind_E, bind_E]
  apply scoped_pool_comparison D (D.expandCells seed) hsize hroom hcost
  · intro P
    exact Finset.sum_nonneg fun tapes _ => mul_nonneg ((tapeLaw D.fresh D.encoding.Ts).nonneg tapes) (hΨ _)
  · intro P Q hpq
    apply congrArg (tapeLaw D.fresh D.encoding.Ts).E
    funext tapes
    exact hlocal (P, tapes) (Q, tapes) (fun C hC => ⟨hpq C hC, rfl⟩)

end HypercubeRamsey.S18.Lane_sol_s18_n5
