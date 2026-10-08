import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_query

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators
open S16 S16.Lane_q_s16_comp2
open S16.Lane_sol_fix2_s16
set_option backward.isDefEq.respectTransparency false

-- These existing proof constants have numeric private-name components.
-- Resolve the constant names during elaboration; their original proof terms
-- remain dependencies of the wrappers and are checked by the kernel.
elab "sol_d18l_existing" modName:ident declName:ident : term => do
  Lean.Meta.mkConstWithFreshMVarLevels (Lean.mkPrivateNameCore modName.getId declName.getId)

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

theorem source_supported_history (R : CellRawData G) (C : G.Cell) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0) :
    ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
  exact (sol_d18l_existing HypercubeRamsey.S16.Producers
    HypercubeRamsey.S16.Lane_sol_fix2_s16.supported_history) R C W hW

theorem source_bin_count (hκ : κ.Admissible) {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (i : Fin PT.tiling.m) :
    (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d = (PT.tiling.P i).M := by
  exact (sol_d18l_existing HypercubeRamsey.S16.Producers
    HypercubeRamsey.S16.Lane_sol_fix2_s16.physical_bin_count) hκ Q i

theorem source_cluster_cap (hκ : κ.Admissible) {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (R : CellRawData G)
    (hR : R.SourceValid) (hCal : CellCalibrationScale PT) (hc : PT.tiling.mode.isCluster)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w b ≤ 8 * (PT.tiling.P (G.cellPatch C)).d /
      Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
  exact (sol_d18l_existing HypercubeRamsey.S16.Producers
    HypercubeRamsey.S16.Lane_sol_fix2_s16.cluster_incoming_cap) hκ Q R hR hCal hc C W hW g b

theorem source_direct_uniform (R : CellRawData G) (hR : R.SourceValid)
    (hc : ¬ PT.tiling.mode.isCluster) (C : G.Cell) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0) (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w b = 1 / (Fintype.card (Bin PT.tiling (G.cellPatch C)) : ℝ) := by
  exact (sol_d18l_existing HypercubeRamsey.S16.Producers
    HypercubeRamsey.S16.Lane_sol_fix2_s16.direct_incoming_uniform)
      R hR hc C W (source_supported_history R C W hW) g b

theorem solver_pretrim_mass {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (W : ∀ r, S.Val r) (g : Group 𝒯 i) (hGood : S.AllGood W) :
    1 - (𝒯.P i).h ^ 2 * Real.sqrt (sliceEps κ (𝒯.P i).h) ≤
      ∑ b ∈ S.pretrimBins W g, S.q g W b := by
  exact (sol_d18l_existing HypercubeRamsey.S14.Profiles
    HypercubeRamsey.S14.retained_bin_mass) S W g hGood

/-- The permission and pool denominators turn an incoming atom cap A/B
into a restricted cap (1+n⁻³)A/L, with its pool-support indicator retained. -/
theorem restricted_atom_bound (Cal : FreshLabelCalibration F) (hn : 2 ≤ T.S.n k)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool) (W : Cal.Hist C)
    (hW : (Cal.history C).w W ≠ 0) (g : Cal.Group C) (A : ℝ) (hA : 0 ≤ A)
    (b : Bin PT.tiling (G.cellPatch C))
    (hcap : (Cal.qin C W g).w b ≤ A / Fintype.card (Bin PT.tiling (G.cellPatch C))) :
    (Cal.qtilde C pool W g).w b ≤
      if b ∈ Finset.univ.image pool then
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * A / G.nslot C else 0 := by
  classical
  let B : ℝ := Fintype.card (Bin PT.tiling (G.cellPatch C))
  let L : ℝ := G.nslot C
  let e : ℝ := (T.S.n k : ℝ) ^ (-4 : ℝ)
  let mperm := ∑ b ∈ Cal.permitted C g, (Cal.qin C W g).w b
  let mpool := ∑ b ∈ Cal.permitted C g ∩ Finset.univ.image pool, (Cal.qin C W g).w b
  have hB : 0 < B := by
    letI := nonempty_of_finLaw (Cal.qin C W g)
    dsimp [B]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Bin PT.tiling (G.cellPatch C)))
  have hL : 0 < L := by dsimp [L]; exact_mod_cast Cal.slot_pos C
  have hnR : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have heBound : e ≤ 1 / 16 := by
    have h := Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ))
      (y := (T.S.n k : ℝ)) (z := (-4 : ℝ)) (by norm_num) hnR (by norm_num)
    have htwo : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
    rw [htwo] at h
    exact h
  have hePos : 0 < 1 - e := by linarith
  have hpPos : 0 < 1 - Cal.δperm := by linarith [Cal.perm_range.2]
  have hgPos : 0 < 1 - Cal.δgate := by linarith [Cal.gate_range.2]
  have hperm : 1 - Cal.δperm ≤ mperm := Cal.permission_mass C W g hW
  have hmPos : 0 < mperm := hpPos.trans_le hperm
  have hnorm : (L / B) * (1 - e) ≤ mpool / mperm :=
    Cal.pool_normalizer C pool W g ht hW
  have hnorm' : (L / B) * (1 - e) * mperm ≤ mpool :=
    (le_div_iff₀ hmPos).mp hnorm
  have hlower : (L / B) * (1 - e) * (1 - Cal.δperm) ≤ mpool :=
    (mul_le_mul_of_nonneg_left hperm (mul_nonneg (div_nonneg hL.le hB.le) hePos.le)).trans hnorm'
  have hpoolPos : 0 < mpool := lt_of_lt_of_le (by positivity) hlower
  have hgateInv : 1 ≤ (1 - Cal.δgate)⁻¹ := by
    have hcancel := mul_inv_cancel₀ (ne_of_gt hgPos)
    nlinarith [mul_nonneg Cal.gate_range.1 (inv_nonneg.mpr hgPos.le)]
  have hsmall : (1 - Cal.δperm)⁻¹ * (1 - e)⁻¹ ≤
      1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
    calc
      _ ≤ (1 - Cal.δgate)⁻¹ * ((1 - Cal.δperm)⁻¹ * (1 - e)⁻¹) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hgateInv
          (mul_nonneg (inv_nonneg.mpr hpPos.le) (inv_nonneg.mpr hePos.le))
      _ ≤ _ := by simpa only [mul_assoc] using Cal.cost_budget
  by_cases hb : b ∈ Finset.univ.image pool
  · rw [if_pos hb, Cal.qtilde_eq C pool W g b ht hW]
    have hnum : (if b ∈ Cal.permitted C g ∧ b ∈ Finset.univ.image pool then
        (Cal.qin C W g).w b else 0) ≤ A / B := by
      split_ifs
      · exact hcap
      · exact div_nonneg hA hB.le
    calc
      _ ≤ (A / B) / mpool := div_le_div_of_nonneg_right hnum hpoolPos.le
      _ ≤ (A / B) / ((L / B) * (1 - e) * (1 - Cal.δperm)) :=
        div_le_div_of_nonneg_left (div_nonneg hA hB.le) (by positivity) hlower
      _ = (A / L) * ((1 - Cal.δperm)⁻¹ * (1 - e)⁻¹) := by
        field_simp
        <;> ring
      _ ≤ (A / L) * (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (div_nonneg hA hL.le)
      _ = _ := by ring
  · rw [if_neg hb, Cal.qtilde_eq C pool W g b ht hW]
    simp [hb]

theorem restricted_atom_cap (Cal : FreshLabelCalibration F) (hn : 2 ≤ T.S.n k)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool) (W : Cal.Hist C)
    (hW : (Cal.history C).w W ≠ 0) (g : Cal.Group C) (A : ℝ) (hA : 0 ≤ A)
    (hcap : ∀ b, (Cal.qin C W g).w b ≤ A / Fintype.card (Bin PT.tiling (G.cellPatch C)))
    (b : Bin PT.tiling (G.cellPatch C)) :
    (Cal.qtilde C pool W g).w b ≤
      if b ∈ Finset.univ.image pool then
        (1 + (T.S.n k : ℝ) ^ (-3 : ℝ)) * A / G.nslot C else 0 :=
  restricted_atom_bound Cal hn C pool ht W hW g A hA b (hcap b)

theorem Kcell_ge_one (hκ : κ.Admissible) : 1 ≤ κ.Kcell := by
  have ht := hκ.clock.2.1
  have hb := hκ.bucket.2.2.1
  rw [ht] at hb
  have hp : (40 : ℝ) ≤ κ.Kp := by exact_mod_cast hκ.bucket.1
  have hs : κ.θstar ≤ 1 / 10 := by
    nlinarith [mul_le_mul_of_nonneg_right hp hκ.bucket.2.2.2.2.le]
  have hdiv : (1 : ℝ) ≤ 100 / κ.θstar :=
    (le_div_iff₀ hκ.bucket.2.2.2.2).mpr (by linarith)
  exact hdiv.trans hκ.Kcell_big

theorem bin_square_room (n d : ℕ) (hn : Real.exp 100 ≤ (n : ℝ))
    (hd : (d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (n : ℝ)))) :
    32 * (d : ℝ) ^ 2 ≤ (n : ℝ) := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 100).trans_le hn
  have ht : (100 : ℝ) ≤ Real.log (n : ℝ) := by
    simpa using Real.log_le_log (Real.exp_pos 100) hn
  have hs : (10 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
    have h := Real.sqrt_le_sqrt ht
    norm_num at h
    exact h
  have hs2 : 2 * Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) / 2 := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log (n : ℝ) by linarith)
    nlinarith [mul_nonneg (Real.sqrt_nonneg (Real.log (n : ℝ)))
      (show 0 ≤ Real.sqrt (Real.log (n : ℝ)) - 4 by linarith)]
  have hl : Real.log 32 ≤ 31 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)
    norm_num at h
    exact h
  have hd2 : (d : ℝ) ^ 2 ≤ Real.exp (2 * Real.sqrt (Real.log (n : ℝ))) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg d) hd 2
    have he : Real.exp (Real.sqrt (Real.log (n : ℝ))) ^ 2 =
        Real.exp (2 * Real.sqrt (Real.log (n : ℝ))) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    exact h.trans_eq he
  calc
    _ ≤ 32 * Real.exp (2 * Real.sqrt (Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hd2 (by norm_num)
    _ = Real.exp (Real.log 32 + 2 * Real.sqrt (Real.log (n : ℝ))) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 32)]
    _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := Real.exp_log hnPos

theorem repeat_atom_allowance (n q d : ℕ) (L : ℝ)
    (hn : 2 ≤ n) (hq : q ≤ n ^ 2) (hd : 0 < d) (hL : 0 < L)
    (hroom : 32 * (d : ℝ) ^ 2 ≤ (n : ℝ))
    (hslot : (n : ℝ) ^ (200 : ℕ) ≤ L * d) :
    (q : ℝ) * ((1 + (n : ℝ) ^ (-3 : ℝ)) * (8 * d) / L) ≤
      Real.rpow (n : ℝ) (-197) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hdPos : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (q : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by exact_mod_cast hq
  have he : (n : ℝ) ^ (-3 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_nonpos (x := (1 : ℝ)) (y := (n : ℝ))
      (z := (-3 : ℝ)) (by norm_num) (by linarith) (by norm_num)
    simpa using h
  have he0 : 0 ≤ 1 + (n : ℝ) ^ (-3 : ℝ) := by positivity
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul hqR (show 1 + (n : ℝ) ^ (-3 : ℝ) ≤ 2 by linarith) he0 (by positivity))
    (show (0 : ℝ) ≤ 8 * d by positivity)
  have hfirst : (q : ℝ) * ((1 + (n : ℝ) ^ (-3 : ℝ)) * (8 * d) / L) ≤
      16 * (n : ℝ) ^ (2 : ℕ) * d / L := by
    convert div_le_div_of_nonneg_right hnum hL.le using 1 <;> ring
  have hroom' : (d : ℝ) ^ 2 ≤ (n : ℝ) / 32 := by linarith
  have hb : (16 * (n : ℝ) ^ (2 : ℕ) * d * (n : ℝ) ^ (197 : ℕ)) * d ≤ L * d := by
    calc
      _ = 16 * (n : ℝ) ^ (199 : ℕ) * (d : ℝ) ^ 2 := by ring
      _ ≤ 16 * (n : ℝ) ^ (199 : ℕ) * ((n : ℝ) / 32) :=
        mul_le_mul_of_nonneg_left hroom' (by positivity)
      _ = (1 / 2 : ℝ) * (n : ℝ) ^ (200 : ℕ) := by ring
      _ ≤ (n : ℝ) ^ (200 : ℕ) := by nlinarith [pow_nonneg hnPos.le 200]
      _ ≤ _ := hslot
  have hb' : 16 * (n : ℝ) ^ (2 : ℕ) * d * (n : ℝ) ^ (197 : ℕ) ≤ L :=
    (mul_le_mul_iff_right₀ hdPos).mp (by simpa only [mul_comm] using hb)
  have hlast : 16 * (n : ℝ) ^ (2 : ℕ) * d / L ≤ 1 / (n : ℝ) ^ (197 : ℕ) :=
    (div_le_div_iff₀ hL (by positivity)).mpr (by simpa only [one_mul] using hb')
  have hδ : Real.rpow (n : ℝ) (-197) = 1 / (n : ℝ) ^ (197 : ℕ) := by
    norm_num [Real.rpow_eq_pow, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, one_div]
  rw [hδ]
  exact hfirst.trans hlast

/-- Restore the raw bin kernels after pretrim on charged slice histories.
The fixed Q0 contract bounds the lost mass uniformly in the patch. -/
theorem source_pretrim_relative_cap (hκ : κ.Admissible) (hPT : PT.Valid)
    (R : CellRawData G) (hR : R.SourceValid) (C : G.Cell) (W : R.Hist C)
    (hW : (R.history C).w W ≠ 0) (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w b ≤ (1 - (0.00001 : ℝ))⁻¹ * (R.qraw C W g).w b := by
  classical
  rcases hR with ⟨hm, hUniform, hSource⟩ | ⟨hc, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨⟨s, g'⟩, rfl⟩ := groups.surjective g
    have hgood := (hPass s (W s)).mp (source_supported_history R C W hW s).1
    have hmass := solver_pretrim_mass S (records s (W s)) g' hgood
    have herr := (patch_rate_and_error hκ hPT hm (G.cellPatch C)).2
    have hsmall : ((PT.tiling.P (G.cellPatch C)).h : ℝ) ^ 2 *
        Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) ≤ 0.00001 := by
      nlinarith [Real.exp_pos (-Real.rpow ((PT.tiling.P (G.cellPatch C)).h : ℝ) (1 + κ.c14)),
        show (0 : ℝ) ≤ ((PT.tiling.P (G.cellPatch C)).h : ℝ) ^ 2 *
          Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) by positivity]
    have hden : 1 - (0.00001 : ℝ) ≤
        ∑ D ∈ R.pretrim C W (groups (s, g')), (R.qraw C W (groups (s, g'))).w D := by
      simp only [hTrim, hQ]
      linarith
    have hdenPos : 0 < ∑ D ∈ R.pretrim C W (groups (s, g')),
        (R.qraw C W (groups (s, g'))).w D := lt_of_lt_of_le (by norm_num) hden
    rw [R.qin_eq C W (groups (s, g')) b (source_supported_history R C W hW)]
    calc
      _ ≤ (R.qraw C W (groups (s, g'))).w b /
          (∑ D ∈ R.pretrim C W (groups (s, g')), (R.qraw C W (groups (s, g'))).w D) := by
        apply div_le_div_of_nonneg_right _ hdenPos.le
        split_ifs
        · exact le_rfl
        · exact (R.qraw C W _).nonneg b
      _ ≤ (R.qraw C W (groups (s, g'))).w b / (1 - (0.00001 : ℝ)) :=
        div_le_div_of_nonneg_left ((R.qraw C W _).nonneg b) (by norm_num) hden
      _ = _ := by ring
  · have hu := (hSource C).2.2.2.1 W g b
    have hin := source_direct_uniform R (Or.inr ⟨hc, hSource⟩) hc C W hW g b
    have heq : (R.qin C W g).w b = (R.qraw C W g).w b := hin.trans hu.symm
    rw [heq]
    exact le_mul_of_one_le_left ((R.qraw C W g).nonneg b) (by norm_num)

theorem exp_pow (a : ℝ) (q : ℕ) : Real.exp a ^ q = Real.exp (a * q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, ih, ← Real.exp_add]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- Fixed sampler costs plus two slice/pretrim prices fit inside .002q. -/
theorem calibration_cost_bound (q : ℕ) (rate ε : ℝ)
    (hr : rate ≤ 0.001) (hε0 : 0 ≤ ε) (hε : ε ≤ 0.00001) :
    Real.exp (rate * q) * (1 + ε) ^ (2 * q) *
      (1 - (0.00001 : ℝ))⁻¹ ^ q * (1 - (0.00001 : ℝ))⁻¹ ^ q ≤
        Real.exp (0.002 * q) := by
  have hSmall : 1 + ε ≤ Real.exp (0.00001 : ℝ) := by
    have h := Real.add_one_le_exp (0.00001 : ℝ)
    linarith
  have hInv : (1 - (0.00001 : ℝ))⁻¹ ≤ Real.exp (0.00002 : ℝ) := by
    have hh : (1 - (0.00001 : ℝ))⁻¹ ≤ 1 + 0.00002 := by norm_num
    have he := Real.add_one_le_exp (0.00002 : ℝ)
    linarith
  have hRate : Real.exp (rate * q) ≤ Real.exp (0.001 * q) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _))
  have hPrice := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + ε by linarith) hSmall (2 * q)
  have hPre := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 - (0.00001 : ℝ))⁻¹) hInv q
  calc
    _ ≤ Real.exp (0.001 * q) * Real.exp (0.00001 : ℝ) ^ (2 * q) *
        Real.exp (0.00002 : ℝ) ^ q * Real.exp (0.00002 : ℝ) ^ q := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul hRate hPrice (by positivity) (by positivity)
        · exact hPre
        · positivity
        · positivity
      · exact hPre
      · positivity
      · positivity
    _ = Real.exp (0.00106 * q) := by
      simp_rw [exp_pow]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ (q : ℝ) from Nat.cast_nonneg q])

theorem inv_one_sub_ge_one (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ < 1) : 1 ≤ (1 - δ)⁻¹ := by
  have hp : 0 < 1 - δ := by linarith
  have hc := mul_inv_cancel₀ (ne_of_gt hp)
  nlinarith [mul_nonneg h0 (inv_nonneg.mpr hp.le)]

theorem calibration_gate_price (Cal : FreshLabelCalibration F) (hn : 2 ≤ T.S.n k) :
    (1 - Cal.δgate)⁻¹ ≤ 1 + (T.S.n k : ℝ) ^ (-3 : ℝ) := by
  have hnR : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have he : (T.S.n k : ℝ) ^ (-4 : ℝ) < 1 := by
    have h := Real.rpow_le_rpow_of_nonpos (x := (2 : ℝ)) (y := (T.S.n k : ℝ))
      (z := (-4 : ℝ)) (by norm_num) hnR (by norm_num)
    have htwo : (2 : ℝ) ^ (-4 : ℝ) = 1 / 16 := by norm_num
    rw [htwo] at h
    linarith
  have hPerm := inv_one_sub_ge_one Cal.δperm Cal.perm_range.1 Cal.perm_range.2
  have hEps := inv_one_sub_ge_one ((T.S.n k : ℝ) ^ (-4 : ℝ)) (by positivity) he
  have hProd : (1 : ℝ) ≤ (1 - Cal.δperm)⁻¹ * (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hPerm) (sub_nonneg.mpr hEps)]
  have hG0 : 0 ≤ (1 - Cal.δgate)⁻¹ := by
    exact inv_nonneg.mpr (by linarith [Cal.gate_range.2])
  calc
    _ ≤ (1 - Cal.δgate)⁻¹ * ((1 - Cal.δperm)⁻¹ * (1 - (T.S.n k : ℝ) ^ (-4 : ℝ))⁻¹) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hProd hG0
    _ ≤ _ := by simpa only [mul_assoc] using Cal.cost_budget

theorem source_direct_bin_size (hκ : κ.Admissible) {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (hc : ¬ PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) : (PT.tiling.P i).d = 1 := by
  exact (sol_d18l_existing HypercubeRamsey.S16.Producers
    HypercubeRamsey.S16.Lane_sol_fix2_s16.direct_bin_size) hκ Q hc i

theorem direct_slot_query_room (n q : ℕ) (L : ℝ) (hn : 10 ≤ n)
    (hq : q ≤ n ^ 2) (hL : (n : ℝ) ^ (200 : ℕ) ≤ L) :
    (q : ℝ) ≤ Real.rpow L 0.025 ∧ Real.rpow L (-0.04) ≤ 0.001 := by
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hqR : (q : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by exact_mod_cast hq
  have hp : Real.rpow ((n : ℝ) ^ (200 : ℕ)) 0.025 = (n : ℝ) ^ (5 : ℕ) := by
    have h := Real.rpow_mul hnPos.le (200 : ℝ) (0.025 : ℝ)
    norm_num at h
    norm_num [Real.rpow_eq_pow]
    exact h.symm
  have hm : Real.rpow ((n : ℝ) ^ (200 : ℕ)) (-0.04) = Real.rpow (n : ℝ) (-8) := by
    have h := Real.rpow_mul hnPos.le (200 : ℝ) (-0.04 : ℝ)
    norm_num at h
    norm_num [Real.rpow_eq_pow]
    exact h.symm
  constructor
  · calc
      _ ≤ (n : ℝ) ^ (5 : ℕ) := hqR.trans (pow_le_pow_right₀ hn1 (by norm_num))
      _ = Real.rpow ((n : ℝ) ^ (200 : ℕ)) 0.025 := hp.symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hL (by norm_num)
  · calc
      Real.rpow L (-0.04) ≤ Real.rpow ((n : ℝ) ^ (200 : ℕ)) (-0.04) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hL (by norm_num)
      _ = Real.rpow (n : ℝ) (-8) := hm
      _ ≤ Real.rpow 10 (-8) := Real.rpow_le_rpow_of_nonpos (by norm_num) hnR (by norm_num)
      _ ≤ 0.001 := by norm_num

end HypercubeRamsey.S18.Lane_sol_d18l_cal
