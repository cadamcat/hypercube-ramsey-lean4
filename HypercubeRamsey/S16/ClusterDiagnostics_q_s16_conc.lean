import HypercubeRamsey.S16.ProducersDefs

namespace HypercubeRamsey.Lane_q_s16_conc

open Classical
open HypercubeRamsey.S16
open HypercubeRamsey.S16.Lane_sol_fix2_s16
open scoped BigOperators

theorem cluster_supported_value_count {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (s : R.Slice C) :
    (Fintype.card {z : R.Value C s // z ∈ R.slicePass C s ∧
      (R.sliceLaw C s).w z ≠ 0} : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  classical
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let A := {z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0}
    let B := {W : (∀ r, S.Val r) // 0 < (S.recLaw PT.parameter).w W}
    let f : A → B := fun z => ⟨records s z.1, by
      have hw := congrArg (fun law : FinLaw (R.Value C s) => law.w z.1) (hLaw s)
      simp only [Lane_sol_s16_prod1.map_equiv_weight, Equiv.symm_symm] at hw
      have hn : (S.recLaw PT.parameter).w (records s z.1) ≠ 0 := by
        intro hz
        exact z.2.2 (hw.trans hz)
      exact lt_of_le_of_ne ((S.recLaw PT.parameter).nonneg _) (Ne.symm hn)⟩
    have hinj : Function.Injective f := by
      intro z z' h
      apply Subtype.ext
      exact (records s).injective (congrArg Subtype.val h)
    have hcount : (Fintype.card A : ℝ) ≤ Fintype.card B := by
      exact_mod_cast Fintype.card_le_of_injective f hinj
    apply hcount.trans
    have hcard : Fintype.card B =
        (Finset.univ.filter fun W : ∀ r, S.Val r => 0 < (S.recLaw PT.parameter).w W).card :=
      Fintype.card_subtype (fun W : ∀ r, S.Val r => 0 < (S.recLaw PT.parameter).w W)
    rw [hcard]
    exact S.low_support hMode PT.parameter
  · exact (hDirect hc).elim

abbrev ClusterStarCheckCountShape {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G) (C : G.Cell) :=
  Σ s : R.Slice C,
    ({z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0} ×
      (EvenRole PT.tiling (G.cellPatch C) ×
        Option (Group PT.tiling (G.cellPatch C) × Bin PT.tiling (G.cellPatch C))))

set_option maxHeartbeats 1600000 in
theorem total_check_count {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom), R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      ∀ (C : H.geom.Cell) (NormalizerCheck : Type) [Fintype NormalizerCheck],
        (Fintype.card NormalizerCheck : ℝ) ≤
          (T.S.n k : ℝ) ^ (200 : ℕ) * Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) →
        (Fintype.card (NormalizerCheck ⊕ ClusterStarCheckCountShape R C) : ℝ) ≤
          Real.exp (3 * (T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  classical
  obtain ⟨nAmp, hAmp⟩ := Lane_sol_s16_prod1.cluster_slice_amplitude_room hκ
  obtain ⟨nStar, hStar⟩ := Lane_sol_s16_prod1.logarithmic_room
    (1.01 : ℝ) (1 / 10) 0 204 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨nNormalizer, hNormalizer⟩ := Lane_sol_s16_prod1.logarithmic_room
    (1.01 : ℝ) 1 0 200 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max nAmp (max nStar nNormalizer), ?_⟩
  intro T k PT K16 Q H R hR hc hn C NormalizerCheck instNormalizer hrowCount
  letI := instNormalizer
  let n := T.S.n k
  let x : ℝ := n
  let X : ℝ := Real.rpow x (1.01 : ℝ)
  let i : Fin PT.tiling.m := H.geom.cellPatch C
  let h := (PT.tiling.P i).h
  have hnAmp : nAmp ≤ n := (le_max_left _ _).trans hn
  have hnStar : nStar ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnNormalizer : nNormalizer ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hxpos : 0 < x := by
    dsimp [x, n]
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hxone : 1 ≤ x := by
    dsimp [x, n]
    exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) Q.n_large
  have hxlarge : (2 : ℝ) ≤ x := by
    dsimp [x, n]
    exact_mod_cast Q.n_large
  have hXeq : X = x * Real.rpow x (1 / 100 : ℝ) := by
    dsimp [X]
    rw [show (1.01 : ℝ) = 1 + 1 / 100 by norm_num, Real.rpow_add hxpos]
    simp
  have hXlower : x ≤ X := by
    rw [hXeq]
    have hp : 1 ≤ Real.rpow x (1 / 100 : ℝ) :=
      Real.one_le_rpow hxone (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hp (le_of_lt hxpos)]
  have hAmpCell := hAmp n h hnAmp Q.n_large (Q.height_bound i)
  have hbase : (2 : ℝ) ≤ 16 * Real.exp
      (2 * (sliceK κ h : ℝ) * sliceT κ h) := by
    have he : 1 ≤ Real.exp (2 * (sliceK κ h : ℝ) * sliceT κ h) :=
      Real.one_le_exp_iff.mpr (by positivity)
    nlinarith
  have hwordR : (2 : ℝ) ^ h ≤ x := by
    calc
      (2 : ℝ) ^ h ≤ (16 * Real.exp
          (2 * (sliceK κ h : ℝ) * sliceT κ h)) ^ h :=
        pow_le_pow_left₀ (by norm_num) hbase h
      _ ≤ x := by simpa [x, n] using hAmpCell.1
  have hwordN : 2 ^ h ≤ n := by
    have hwordRCast : ((2 ^ h : ℕ) : ℝ) ≤ (n : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hwordR
    exact_mod_cast hwordRCast
  have hIcard : Fintype.card (IWord PT.tiling i) = 2 ^ h := by
    simp [IWord, CubePos, h]
  have hRoleNat : Fintype.card (EvenRole PT.tiling i) ≤ n := by
    calc
      Fintype.card (EvenRole PT.tiling i) ≤ Fintype.card (IWord PT.tiling i) :=
        Fintype.card_le_of_injective (fun w : EvenRole PT.tiling i => w.1)
          (fun a b hab => Subtype.ext hab)
      _ = 2 ^ h := hIcard
      _ ≤ n := hwordN
  have hGroupNat : Fintype.card (Group PT.tiling i) ≤ n := by
    calc
      Fintype.card (Group PT.tiling i) ≤ Fintype.card (IWord PT.tiling i) :=
        Fintype.card_le_of_injective (fun g : Group PT.tiling i => g.1)
          (fun a b hab => Subtype.ext hab)
      _ = 2 ^ h := hIcard
      _ ≤ n := hwordN
  have hSliceCardEq :
      (Fintype.card (R.Slice C) : ℝ) * (2 : ℝ) ^ h =
        (H.data.cells.positions C).card := by
    have heq := Fintype.card_congr (R.cellWords C)
    rw [Fintype.card_prod, hIcard] at heq
    have hsub : Fintype.card {v : Pos T k // H.geom.cellOf v = C} =
        (H.data.cells.positions C).card :=
      Fintype.card_subtype (fun v : Pos T k => H.geom.cellOf v = C)
    rw [hsub] at heq
    exact_mod_cast heq
  have hcellBound : (H.data.cells.positions C).card ≤ x ^ (200 : ℕ) := by
    have hcellNat := H.cell_partition.cell_size C
    have hcellR : ((H.data.cells.positions C).card : ℝ) ≤
        (⌊Real.rpow x κ.Ac⌋₊ : ℝ) := by
      exact_mod_cast hcellNat
    calc
      ((H.data.cells.positions C).card : ℝ) ≤ Real.rpow x κ.Ac :=
        hcellR.trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = x ^ (200 : ℕ) := by
        rw [hκ.Ac_eq]
        exact Real.rpow_natCast x 200
  have hSliceNat : (Fintype.card (R.Slice C) : ℝ) ≤ x ^ (200 : ℕ) := by
    have hwordOne : (1 : ℝ) ≤ (2 : ℝ) ^ h := one_le_pow₀ (by norm_num)
    have hcardNonneg : 0 ≤ (Fintype.card (R.Slice C) : ℝ) := by positivity
    calc
      (Fintype.card (R.Slice C) : ℝ) ≤
          (Fintype.card (R.Slice C) : ℝ) * (2 : ℝ) ^ h := by
        simpa using mul_le_mul_of_nonneg_left hwordOne hcardNonneg
      _ = (H.data.cells.positions C).card := hSliceCardEq
      _ ≤ x ^ (200 : ℕ) := hcellBound
  let patch := PT.tiling.P i
  obtain ⟨b, hb⟩ := patch.bins.parts_nonempty
    (Finset.nonempty_iff_ne_empty.mp (Q.profiled_valid.tiling_valid.patch_nonempty i).2)
  have hbn : b.Nonempty := Finset.nonempty_iff_ne_empty.mpr (patch.bins.ne_bot hb)
  have hd : 1 ≤ patch.d := by
    calc
      1 ≤ b.card := Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr hbn)
      _ = patch.d := Q.profiled_valid.tiling_valid.bins_card i b hb
  have hpartsEq : patch.bins.parts.card * patch.d = patch.Y.card := by
    calc
      patch.bins.parts.card * patch.d = ∑ b ∈ patch.bins.parts, patch.d := by simp
      _ = ∑ b ∈ patch.bins.parts, b.card := by
        apply Finset.sum_congr rfl
        intro b hb
        exact (Q.profiled_valid.tiling_valid.bins_card i b hb).symm
      _ = patch.Y.card := patch.bins.sum_card_parts
  have hYle : patch.Y.card ≤ T.S.N k := by
    calc
      patch.Y.card ≤ (Finset.univ : Finset (Fin (T.S.N k))).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = T.S.N k := by simp
  have hBinParts : Fintype.card (Bin PT.tiling i) = patch.bins.parts.card := by
    change Fintype.card {b : Finset (Fin (T.S.N k)) // b ∈ patch.bins.parts} = _
    simpa using (Fintype.card_subtype
      (fun b : Finset (Fin (T.S.N k)) => b ∈ patch.bins.parts))
  have hBinNat : Fintype.card (Bin PT.tiling i) ≤ T.S.N k := by
    rw [hBinParts]
    calc
      patch.bins.parts.card = patch.bins.parts.card * 1 := by simp
      _ ≤ patch.bins.parts.card * patch.d := Nat.mul_le_mul_left _ hd
      _ = patch.Y.card := hpartsEq
      _ ≤ T.S.N k := hYle
  have hGroupReal : (Fintype.card (Group PT.tiling i) : ℝ) ≤ x := by
    simpa [x, n] using (show Fintype.card (Group PT.tiling i) ≤ n from hGroupNat)
  have hBinReal : (Fintype.card (Bin PT.tiling i) : ℝ) ≤ (T.S.N k : ℝ) := by
    exact_mod_cast hBinNat
  have hNle : (T.S.N k : ℝ) ≤ x * (2 : ℝ) ^ n := by
    dsimp [x, n]
    exact_mod_cast T.S.N_le k
  have hGroupBin :
      (Fintype.card (Group PT.tiling i × Bin PT.tiling i) : ℝ) ≤
        x ^ 2 * (2 : ℝ) ^ n := by
    rw [Fintype.card_prod, Nat.cast_mul]
    calc
      (Fintype.card (Group PT.tiling i) : ℝ) *
          (Fintype.card (Bin PT.tiling i) : ℝ) ≤
        x * (Fintype.card (Bin PT.tiling i) : ℝ) :=
          mul_le_mul_of_nonneg_right hGroupReal (by positivity)
      _ ≤ x * (T.S.N k : ℝ) := mul_le_mul_of_nonneg_left hBinReal (by positivity)
      _ ≤ x * (x * (2 : ℝ) ^ n) := mul_le_mul_of_nonneg_left hNle (by positivity)
      _ = x ^ 2 * (2 : ℝ) ^ n := by ring
  have hfactor : (1 : ℝ) ≤ x ^ 2 * (x - 1) * (2 : ℝ) ^ n := by
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    have hxminus : 1 ≤ x - 1 := by linarith
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    calc
      1 = (1 : ℝ) ^ 2 * 1 * 1 := by norm_num
      _ ≤ x ^ 2 * 1 * 1 := by nlinarith [hx2]
      _ = x ^ 2 * 1 := by ring
      _ ≤ x ^ 2 * (x - 1) := mul_le_mul_of_nonneg_left hxminus (sq_nonneg x)
      _ = x ^ 2 * (x - 1) * 1 := by ring
      _ ≤ x ^ 2 * (x - 1) * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  have hOptionReal :
      (Fintype.card (Option (Group PT.tiling i × Bin PT.tiling i)) : ℝ) ≤
        x ^ 3 * (2 : ℝ) ^ n := by
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    nlinarith [hGroupBin, hfactor]
  have hXlogStar := hStar n hnStar
  have hlogStar : (204 : ℝ) * Real.log x ≤ (1 / 10 : ℝ) * X := by
    simpa [x, X] using hXlogStar
  have hlog2 : Real.log (2 : ℝ) ≤ (9 / 10 : ℝ) := by
    have h := Real.log_two_lt_d9
    norm_num at h ⊢
    linarith
  have hlogLinear : x * Real.log (2 : ℝ) ≤ (9 / 10 : ℝ) * x := by
    calc
      x * Real.log (2 : ℝ) ≤ x * (9 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog2 (le_of_lt hxpos)
      _ = (9 / 10 : ℝ) * x := by ring
  have hoverLog : (204 : ℝ) * Real.log x + x * Real.log (2 : ℝ) ≤ X := by
    have hscaled : (9 / 10 : ℝ) * x ≤ (9 / 10 : ℝ) * X :=
      mul_le_mul_of_nonneg_left hXlower (by norm_num : (0 : ℝ) ≤ 9 / 10)
    calc
      _ ≤ (1 / 10 : ℝ) * X + (9 / 10 : ℝ) * x := add_le_add hlogStar hlogLinear
      _ ≤ (1 / 10 : ℝ) * X + (9 / 10 : ℝ) * X :=
        by nlinarith [hscaled]
      _ = X := by ring
  have hexp204 : Real.exp ((204 : ℝ) * Real.log x) = x ^ (204 : ℕ) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hxpos] using
      Real.exp_nat_mul (Real.log x) 204
  have hexpN : Real.exp (x * Real.log (2 : ℝ)) = (2 : ℝ) ^ n := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      Real.exp_nat_mul (Real.log (2 : ℝ)) n
  have hpolyStar : x ^ (204 : ℕ) * (2 : ℝ) ^ n ≤ Real.exp X := by
    calc
      x ^ (204 : ℕ) * (2 : ℝ) ^ n =
          Real.exp ((204 : ℝ) * Real.log x + x * Real.log (2 : ℝ)) := by
            rw [Real.exp_add, hexp204, hexpN]
      _ ≤ Real.exp X := Real.exp_le_exp.mpr hoverLog
  have hStarCard :
      (Fintype.card (ClusterStarCheckCountShape R C) : ℝ) ≤
        x ^ (204 : ℕ) * (2 : ℝ) ^ n * Real.exp X := by
    have hstarEq : Fintype.card (ClusterStarCheckCountShape R C) =
        ∑ s : R.Slice C,
          Fintype.card {z : R.Value C s // z ∈ R.slicePass C s ∧
            (R.sliceLaw C s).w z ≠ 0} * Fintype.card (EvenRole PT.tiling i) *
              Fintype.card (Option (Group PT.tiling i × Bin PT.tiling i)) := by
      simp [ClusterStarCheckCountShape, Fintype.card_sigma, Fintype.card_prod,
        Fintype.card_option, Nat.mul_assoc, i]
    have hterm (s : R.Slice C) :
        (Fintype.card {z : R.Value C s // z ∈ R.slicePass C s ∧
          (R.sliceLaw C s).w z ≠ 0} : ℝ) *
          (Fintype.card (EvenRole PT.tiling i) : ℝ) *
            (Fintype.card (Option (Group PT.tiling i × Bin PT.tiling i)) : ℝ) ≤
          Real.exp X * x ^ 4 * (2 : ℝ) ^ n := by
      have hval := cluster_supported_value_count R hR hc C s
      have hrole : (Fintype.card (EvenRole PT.tiling i) : ℝ) ≤ x := by
        simpa [x, n] using (show Fintype.card (EvenRole PT.tiling i) ≤ n from hRoleNat)
      have hprod := mul_le_mul hval hrole (by positivity) (Real.exp_nonneg X)
      calc
        _ ≤ (Real.exp X * x) *
              (Fintype.card (Option (Group PT.tiling i × Bin PT.tiling i)) : ℝ) :=
          mul_le_mul_of_nonneg_right hprod (by positivity)
        _ ≤ (Real.exp X * x) * (x ^ 3 * (2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hOptionReal (by positivity)
        _ = Real.exp X * x ^ 4 * (2 : ℝ) ^ n := by ring
    rw [hstarEq]
    push_cast
    calc
      (∑ s : R.Slice C,
          (Fintype.card {z : R.Value C s // z ∈ R.slicePass C s ∧
            (R.sliceLaw C s).w z ≠ 0} : ℝ) *
            (Fintype.card (EvenRole PT.tiling i) : ℝ) *
            (Fintype.card (Option (Group PT.tiling i × Bin PT.tiling i)) : ℝ)) ≤
          ∑ _s : R.Slice C, Real.exp X * x ^ 4 * (2 : ℝ) ^ n :=
        Finset.sum_le_sum (fun s _ => hterm s)
      _ = (Fintype.card (R.Slice C) : ℝ) * (Real.exp X * x ^ 4 * (2 : ℝ) ^ n) := by simp
      _ ≤ x ^ (200 : ℕ) * (Real.exp X * x ^ 4 * (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_right hSliceNat (by positivity)
      _ = x ^ (204 : ℕ) * (2 : ℝ) ^ n * Real.exp X := by ring
  have hStarFinal :
      (Fintype.card (ClusterStarCheckCountShape R C) : ℝ) ≤ Real.exp (2 * X) := by
    calc
      (Fintype.card (ClusterStarCheckCountShape R C) : ℝ) ≤
          x ^ (204 : ℕ) * (2 : ℝ) ^ n * Real.exp X := hStarCard
      _ ≤ Real.exp X * Real.exp X :=
        mul_le_mul_of_nonneg_right hpolyStar (Real.exp_nonneg X)
      _ = Real.exp (2 * X) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hXlogNorm := hNormalizer n hnNormalizer
  have hlogNorm : (200 : ℝ) * Real.log x ≤ X := by
    simpa [x, X] using hXlogNorm
  have hexp200 : Real.exp ((200 : ℝ) * Real.log x) = x ^ (200 : ℕ) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hxpos] using
      Real.exp_nat_mul (Real.log x) 200
  have hpolyNorm : x ^ (200 : ℕ) ≤ Real.exp X := by
    calc
      x ^ (200 : ℕ) = Real.exp ((200 : ℝ) * Real.log x) := hexp200.symm
      _ ≤ Real.exp X := Real.exp_le_exp.mpr hlogNorm
  have hrowCount' : (Fintype.card NormalizerCheck : ℝ) ≤
      x ^ (200 : ℕ) * Real.exp X := by simpa [x, n, X] using hrowCount
  have hNormalizerFinal : (Fintype.card NormalizerCheck : ℝ) ≤ Real.exp (2 * X) := by
    calc
      (Fintype.card NormalizerCheck : ℝ) ≤ x ^ (200 : ℕ) * Real.exp X := hrowCount'
      _ ≤ Real.exp X * Real.exp X :=
        mul_le_mul_of_nonneg_right hpolyNorm (Real.exp_nonneg X)
      _ = Real.exp (2 * X) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsum : (Fintype.card NormalizerCheck : ℝ) +
      (Fintype.card (ClusterStarCheckCountShape R C) : ℝ) ≤ Real.exp (3 * X) := by
    have htwo : (2 : ℝ) ≤ Real.exp X := by
      have h := Real.add_one_le_exp X
      linarith [hXlower, hxlarge]
    calc
      _ ≤ Real.exp (2 * X) + Real.exp (2 * X) :=
        add_le_add hNormalizerFinal hStarFinal
      _ = 2 * Real.exp (2 * X) := by ring
      _ ≤ Real.exp X * Real.exp (2 * X) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (3 * X) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsumCard :
      (Fintype.card (NormalizerCheck ⊕ ClusterStarCheckCountShape R C) : ℝ) =
        (Fintype.card NormalizerCheck : ℝ) +
          (Fintype.card (ClusterStarCheckCountShape R C) : ℝ) := by
    rw [Fintype.card_sum, Nat.cast_add]
  rw [hsumCard]
  simpa [X, x, n] using hsum

end HypercubeRamsey.Lane_q_s16_conc
