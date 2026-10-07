import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_stages

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators
open S16 S16.Lane_sol_fix2_s16 S16.Lane_q_s16_comp2
set_option backward.isDefEq.respectTransparency false

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

theorem physical_cell_query_bound (P : PhysicalFreshCertificate G F) (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    {q : ℕ} (hq0 : 0 < q) (hq : q ≤ T.S.n k ^ 2)
    (r : Fin q → OddCellRole G C) (hr : Function.Injective r)
    (hg : Function.Injective (fun a => P.raw.groupOf C (r a)))
    (hHeight : PT.tiling.mode.isCluster → 1 ≤ (PT.tiling.P (G.cellPatch C)).h)
    (hSmall : ¬ PT.tiling.mode.isCluster → (q : ℝ) ≤ Real.rpow (G.nslot C : ℝ) 0.025)
    (hMargin : PT.tiling.mode.isCluster → 2 < 20 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ))
    (hn : 100 ≤ T.S.n k) (hroom : 32 * ((PT.tiling.P (G.cellPatch C)).d : ℝ) ^ 2 ≤ T.S.n k)
    (hd : 0 < (PT.tiling.P (G.cellPatch C)).d)
    (hslot : (T.S.n k : ℝ) ^ (200 : ℕ) ≤ (G.nslot C : ℝ) * (PT.tiling.P (G.cellPatch C)).d)
    (hRate : cell_query_rate G C ≤ 0.001)
    (f : Fin q → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y ∧ f a y ≤ 1) :
    (S16.iidCellPoolLaw (G := G) C hBins).E (fun pool => if F.typical C pool then
      (F.fresh C pool).E (fun s => ∏ a, f a (F.label C s (r a).1)) else 0) ≤
      Real.exp (0.002 * q) *
        ∏ a, ((∑ y, (PT.πraw (G.cellPatch C)).w y * f a y) +
          Real.rpow (T.S.n k : ℝ) (-197)) := by
  classical
  let β := 1 + (T.S.n k : ℝ) ^ (-3 : ℝ)
  let pre := (1 - (0.00001 : ℝ))⁻¹
  let δ := Real.rpow (T.S.n k : ℝ) (-197)
  let μ := fun a => ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y
  let M := ∏ a, (μ a + δ)
  let PoolLaw := S16.iidCellPoolLaw (G := G) C hBins
  let Score := fun pool => if F.typical C pool then
    (P.raw.history C).E (fun W =>
      (FinLaw.pi fun a => P.kernels.qtilde C pool W (P.raw.groupOf C (r a))).E
        (retainedQueryWeight (fun a b => (P.raw.U C W (P.raw.groupOf C (r a)) b).E (f a)))) else 0
  have hn2 : 2 ≤ T.S.n k := by omega
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hβ : 1 ≤ β := by
    dsimp [β]
    have he : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
    linarith
  have hpre : 0 ≤ pre := by dsimp [pre]; norm_num
  have hM : 0 ≤ M := by
    apply Finset.prod_nonneg
    intro a _
    exact add_nonneg (Finset.sum_nonneg (fun y _ =>
      mul_nonneg ((PT.πraw _).nonneg y) (hf a y).1)) hδ
  have hScore : ∀ pool, 0 ≤ Score pool := by
    intro pool
    dsimp [Score]
    split_ifs
    · apply expect_nonneg
      intro W
      apply expect_nonneg
      exact retainedQueryWeight_nonneg _ (fun a b => expect_nonneg _ _ (fun y => (hf a y).1))
    · exact le_rfl
  have hallow := repeat_atom_allowance (T.S.n k) q (PT.tiling.P (G.cellPatch C)).d
    (G.nslot C : ℝ) hn2 hq hd (by exact_mod_cast P.calibration.slot_pos C) hroom hslot
  have hAvg := physical_pool_record_bound P C hBins r f (fun a y => (hf a y).1)
    hMargin hSep δ hδ hallow
  have hPrice : β ^ (q + 1) ≤ β ^ (2 * q) := pow_le_pow_right₀ hβ (by omega)
  have hε0 : 0 ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by positivity
  have hε : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 0.00001 := by
    have hnR : (100 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
    have h := Real.rpow_le_rpow_of_nonpos (x := (100 : ℝ)) (y := (T.S.n k : ℝ))
      (z := (-3 : ℝ)) (by norm_num) hnR (by norm_num)
    have hh : (100 : ℝ) ^ (-3 : ℝ) = 0.000001 := by norm_num
    rw [hh] at h
    linarith
  have hCost := calibration_cost_bound q (cell_query_rate G C)
    ((T.S.n k : ℝ) ^ (-3 : ℝ)) hRate hε0 hε
  calc
    _ ≤ (Real.exp (cell_query_rate G C * q) * β) * PoolLaw.E Score := by
      rw [← expect_const_mul]
      apply expect_le
      intro pool
      by_cases ht : F.typical C pool
      · simp only [if_pos ht]
        simpa only [Score, β, if_pos ht] using
          physical_fresh_query_comparison P C pool ht r hr hg hHeight hSmall hBins.choose f hf
      · simp [ht, Score]
    _ ≤ (Real.exp (cell_query_rate G C * q) * β) * ((β * pre) ^ q * pre ^ q * M) :=
      mul_le_mul_of_nonneg_left hAvg (mul_nonneg (Real.exp_pos _).le (by linarith))
    _ = (Real.exp (cell_query_rate G C * q) * β ^ (q + 1) * pre ^ q * pre ^ q) * M := by
      rw [mul_pow, pow_succ]
      ring
    _ ≤ (Real.exp (cell_query_rate G C * q) * β ^ (2 * q) * pre ^ q * pre ^ q) * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hpre _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hpre _)
      exact mul_le_mul_of_nonneg_left hPrice (Real.exp_pos _).le
    _ ≤ Real.exp (0.002 * q) * M := mul_le_mul_of_nonneg_right hCost hM

end HypercubeRamsey.S18.Lane_sol_d18l_cal
