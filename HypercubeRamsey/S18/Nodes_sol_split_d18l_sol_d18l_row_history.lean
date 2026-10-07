import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_pal
import HypercubeRamsey.S18.Nodes_sol_d18l_up_pool

namespace HypercubeRamsey.S18.Lane_sol_d18l_row

open Classical Filter
open S16 S16.Lane_sol_fix2_s16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

/-- The prior family is fixed before the label colouring. Only one solver
record and the internal star enter the own-cell prior readout. -/
noncomputable def physical_prior_histories (hPT : PT.Valid)
    (physical : PhysicalFreshCertificate G F) (v : Pos T k) :
    Finset (Fin (T.S.N k) → ℝ) :=
  if hc : PT.tiling.mode.isCluster then
    let S := Classical.choose (hPT.cluster_solver hc (G.patchOf v))
    (Lane_sol_d18l_pal.cluster_family hPT G S).image Law.w
  else {fun x => if x ∈ PT.envelope (G.patchOf v) then
    1 / ((PT.envelope (G.patchOf v)).card : ℝ) else 0}

theorem physical_prior_history_cover (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (he : IsEvenRole v)
    (hσ : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).ValidInitialPrior v σ) :
    σ ∈ physical_prior_histories hPT physical v := by
  unfold physical_prior_histories
  split_ifs with hc
  · let S := Classical.choose (hPT.cluster_solver hc (G.patchOf v))
    have hS := Classical.choose_spec (hPT.cluster_solver hc (G.patchOf v))
    have hm : PT.tiling.mode = .lowCluster := by
      cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Mode.isCluster]
    obtain ⟨μ, hμ, hμσ⟩ := Lane_sol_d18l_pal.cluster_family_prior_capture
      hPT hLow physical hm S hS v (G.patchOf_leaf v) he σ hσ
    exact Finset.mem_image.mpr ⟨μ, hμ, hμσ⟩
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (hPT.direct_single_corner hc)
    obtain ⟨a, ha, hsupport, hcap, hshape⟩ := hσ.1.2.2
    have haq : a = q := by simpa only [hq, Finset.mem_singleton] using ha
    have henv : PT.envelope (G.patchOf v) = PT.mesh.corner q (G.patchOf v) := by
      rw [hPT.envelope_eq, hq]
      simp
    apply Finset.mem_singleton.mpr
    funext x
    rw [(hshape hc).2 x, haq, henv]

/-- A coarse count is enough: the eventual n^2.01 budget pays for the fixed
factor and for every external neighbour label. -/
theorem physical_prior_history_card (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) (hn : (100 : ℝ) ≤ T.S.n k)
    (hh : ((PT.tiling.P (G.patchOf v)).h : ℝ) ≤ T.S.n k)
    (hN : Real.log (T.S.N k : ℝ) ≤ 2 * T.S.n k) :
    ((physical_prior_histories hPT physical v).card : ℝ) ≤
      3 * Real.exp (6 * (T.S.n k : ℝ) ^ 2) := by
  unfold physical_prior_histories
  split_ifs with hc
  · have hm : PT.tiling.mode = .lowCluster := by
      cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Mode.isCluster]
    apply (Nat.cast_le.mpr Finset.card_image_le).trans
    exact Lane_sol_d18l_pal.cluster_family_card_bound hPT G _ hm hn hh hN
  · simp only [Finset.card_singleton, Nat.cast_one]
    have he : 1 ≤ Real.exp (6 * (T.S.n k : ℝ) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
    linarith

noncomputable def physical_local_histories (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (v : Pos T k) :
    Finset ((Lane_sol_s18_dl.physical_list_context hPT hLow physical).LocalReadout v) :=
  (physical_prior_histories hPT physical v).product Finset.univ

theorem physical_local_history_cover (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (v : Pos T k)
    (pools : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).PoolAssignment)
    (s : Config F) (he : IsEvenRole v)
    (ht : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).LocalPoolsTypical v pools)
    (hs : ∀ C ∈ (Lane_sol_s18_dl.physical_list_context hPT hLow physical).scopeCells v,
      (Lane_sol_s18_dl.physical_list_context hPT hLow physical).stateValid C (pools C) (s C)) :
    let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
    (D.prior s v, fun w => D.label s w.1) ∈ physical_local_histories hPT hLow physical v := by
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  have hown : G.cellOf v ∈ D.scopeCells v :=
    Finset.mem_union_left _ (Finset.mem_singleton_self _)
  have ht' := ht (G.cellOf v) hown
  have hs' := hs (G.cellOf v) hown
  have hprior : D.ValidInitialPrior v (D.prior s v) :=
    ⟨Lane_sol_d18l_up.physical_clean_prior hPT hLow physical v _ _ he ht' hs',
      pools (G.cellOf v), s (G.cellOf v), ht', hs', fun _ => rfl⟩
  exact Finset.mem_product.mpr
    ⟨physical_prior_history_cover hPT hLow physical v _ he hprior, Finset.mem_univ _⟩

theorem physical_history_log_bounds (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (v : Pos T k)
    (hn : (100 : ℝ) ≤ T.S.n k)
    (hh : ((PT.tiling.P (G.patchOf v)).h : ℝ) ≤ T.S.n k)
    (hN : Real.log (T.S.N k : ℝ) ≤ 2 * T.S.n k) :
    Real.log (max 1 ((physical_prior_histories hPT physical v).card : ℝ)) ≤
      Real.log 3 + 8 * (T.S.n k : ℝ) ^ 2 ∧
    Real.log (max 1 ((physical_local_histories hPT hLow physical v).card : ℝ)) ≤
      Real.log 3 + 8 * (T.S.n k : ℝ) ^ 2 := by
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  let B := 3 * Real.exp (6 * (T.S.n k : ℝ) ^ 2)
  have hB : 1 ≤ B := by
    have he : 1 ≤ Real.exp (6 * (T.S.n k : ℝ) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp [B]
    linarith
  have hcard := physical_prior_history_card hPT hLow physical v hn hh hN
  have hNp : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hNone : 1 ≤ (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hext : Fintype.card {w : Pos T k // w ∈ D.externalEarly v} ≤ T.S.n k := by
    simpa using Lane_q_s17_pool.externalEarly_card_le D v
  have hlocal : ((physical_local_histories hPT hLow physical v).card : ℝ) ≤
      B * (T.S.N k : ℝ) ^ T.S.n k := by
    simp only [physical_local_histories, Finset.card_product, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    exact mul_le_mul hcard (pow_le_pow_right₀ hNone hext) (by positivity) (by positivity)
  constructor
  · have hmax : max 1 ((physical_prior_histories hPT physical v).card : ℝ) ≤ B :=
      max_le hB hcard
    have hlog := Real.log_le_log (by positivity) hmax
    simp only [B, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] at hlog
    nlinarith [sq_nonneg (T.S.n k : ℝ)]
  · have hpow : 1 ≤ (T.S.N k : ℝ) ^ T.S.n k := one_le_pow₀ hNone
    have hmax : max 1 ((physical_local_histories hPT hLow physical v).card : ℝ) ≤
        B * (T.S.N k : ℝ) ^ T.S.n k := max_le (by nlinarith) hlocal
    have hlog := Real.log_le_log (by positivity) hmax
    rw [Real.log_mul (by dsimp [B]; positivity) (by positivity), Real.log_pow] at hlog
    simp only [B, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp] at hlog
    have hprod := mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg (T.S.n k))
    nlinarith

theorem eventually_history_budget (T : Stage) :
    ∀ᶠ k in atTop, Real.log 3 + 8 * (T.S.n k : ℝ) ^ 2 ≤
      Real.rpow (T.S.n k : ℝ) 2.01 := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [hn.eventually_ge_atTop 1,
    (Real.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.01) |>.comp hn).eventually_ge_atTop 10]
    with k hk hp
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hlog : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  rw [show (2.01 : ℝ) = 2 + 0.01 by norm_num, Real.rpow_add hnpos,
    Real.rpow_two]
  have hmul := mul_le_mul_of_nonneg_left hp (sq_nonneg (T.S.n k : ℝ))
  nlinarith

end HypercubeRamsey.S18.Lane_sol_d18l_row
