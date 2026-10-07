import HypercubeRamsey.S15.ClusterNodes_q_s15_c2
import HypercubeRamsey.S15.ClusterNodes_sol_s15_load

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 OAI.HypercubeRamsey Filter Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem adjacent_eq_flip {T : Stage} {k : ℕ}
    {a : EvenPosition T k} {b : OddPosition T k} (hab : Adjacent a b) :
    ∃ j : Fin (T.S.n k), b.1 = flipPos a.1 j := by
  have hdiff : (Finset.univ.filter fun j : Fin (T.S.n k) => a.1 j ≠ b.1 j).card = 1 := hab
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hdiff
  have hdiffj : a.1 j ≠ b.1 j := by
    have hmem : j ∈ Finset.univ.filter fun j : Fin (T.S.n k) => a.1 j ≠ b.1 j := by
      rw [hj]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hsame : ∀ t : Fin (T.S.n k), t ≠ j → a.1 t = b.1 t := by
    intro t ht
    by_contra hne
    have hmem : t ∈ Finset.univ.filter (fun j : Fin (T.S.n k) => a.1 j ≠ b.1 j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ t, hne⟩
    rw [hj] at hmem
    exact ht (Finset.mem_singleton.mp hmem)
  refine ⟨j, ?_⟩
  funext t
  by_cases ht : t = j
  · subst t
    cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [flipPos]
  · simp [flipPos, ht, hsame t ht]

theorem external_neighbours_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    (clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a).card ≤
      T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h := by
  let E := clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a
  have hcoord (b : OddPosition T k) (hb : b ∈ E) :
      ∃ j : Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h),
        b.1 = flipPos a.1 ⟨j.val, by have := j.isLt; omega⟩ := by
    have hadj : Adjacent a b := by
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_filter.mp hb).2.1
      · exact (Finset.mem_filter.mp hb).2.1
    obtain ⟨j, hj⟩ := adjacent_eq_flip hadj
    have hlt : j.val < T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h := by
      by_contra hnot
      have hge := Nat.le_of_not_gt hnot
      have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1)
      let l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h := ⟨j.val -
        (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h), by have := j.isLt; omega⟩
      have hj' : j = ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
        by have := l.isLt; omega⟩ := by apply Fin.ext; dsimp [l]; omega
      have hs : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1 := by
        rw [hj, hj']
        exact Lane_q_s15_c2.clusterSliceAt_flip_internal PT hPT a.1 l
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_filter.mp hb).2.2.2 hs
      · exact (Finset.mem_filter.mp hb).2.2 (congrArg Sigma.fst hs)
    exact ⟨⟨j.val, hlt⟩, hj⟩
  let f : {b // b ∈ E} → Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h) :=
    fun b => Classical.choose (hcoord b.1 b.2)
  have hf : Function.Injective f := by
    intro b c hbc
    apply Subtype.ext
    apply Subtype.ext
    have hb := Classical.choose_spec (hcoord b.1 b.2)
    have hc := Classical.choose_spec (hcoord c.1 c.2)
    change f b = f c at hbc
    change b.1.1 = flipPos a.1 ⟨(f b).val, _⟩ at hb
    change c.1.1 = flipPos a.1 ⟨(f c).val, _⟩ at hc
    rw [hb, hc]
    congr 1
    apply Fin.ext
    exact congrArg (fun j : Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h) => j.val) hbc
  have hcard := Fintype.card_le_of_injective f hf
  have hdom : Fintype.card {b : OddPosition T k // b ∈ E} = E.card :=
    Fintype.card_of_subtype E (fun _ => Iff.rfl)
  rw [hdom, Fintype.card_fin] at hcard
  exact hcard

theorem inverse_degree_le {e d : ℝ} (he : 0 ≤ e) (hes : e ≤ 1 / 6)
    (hd : |d - 1 / 2| ≤ e) : 0 < d ∧ 1 / d ≤ 2 * Real.exp (6 * e) := by
  have hl := (abs_le.mp hd).1
  have hdpos : 0 < d := by linarith
  refine ⟨hdpos, ?_⟩
  have he2 : e * e ≤ e / 6 := by nlinarith [mul_le_mul_of_nonneg_right hes he]
  have hprod : 1 ≤ (2 * (1 + 6 * e)) * d := by
    have := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * (1 + 6 * e))
    nlinarith
  have hlin : 1 / d ≤ 2 * (1 + 6 * e) := (div_le_iff₀ hdpos).2 hprod
  exact hlin.trans (mul_le_mul_of_nonneg_left
    (by simpa [add_comm] using Real.add_one_le_exp (6 * e)) (by norm_num))

theorem crossing_degree_ratio_le {b t d : ℝ} (hb : 0 ≤ b) (hsmall : b ≤ 1 / 100)
    (ht : |t - 1 / 2| ≤ 2 * b) (hd : |d - 1 / 2| ≤ 3 * b) :
    0 < t ∧ 0 < d ∧ d / t ≤ Real.exp (20 * b) := by
  have ht' := abs_le.mp ht
  have hd' := abs_le.mp hd
  have htpos : 0 < t := by linarith
  have hdpos : 0 < d := by linarith
  refine ⟨htpos, hdpos, ?_⟩
  have hb2 : b * b ≤ b / 100 := by nlinarith [mul_le_mul_of_nonneg_right hsmall hb]
  have hlin : d / t ≤ 1 + 20 * b := by
    apply (div_le_iff₀ htpos).2
    have := mul_le_mul_of_nonneg_left ht'.1 (by positivity : 0 ≤ 1 + 20 * b)
    nlinarith
  exact hlin.trans (by simpa [add_comm] using Real.add_one_le_exp (20 * b))

theorem bulk_product_gate_le {α : Type*} [DecidableEq α]
    (S : Finset α) (H D : α → ℝ) (d : ℝ) (hd : 0 < d)
    (hH : ∀ b ∈ S, 0 ≤ H b) (hD : ∀ b ∈ S, 0 < D b)
    (hgate : (1 / 2 : ℝ) ≤ (∏ b ∈ S, D b) / d ^ S.card) :
    (∏ b ∈ S, H b / D b) ≤ 2 * ∏ b ∈ S, H b / d := by
  have hprodD : 0 < ∏ b ∈ S, D b := Finset.prod_pos hD
  have hprodH : 0 ≤ ∏ b ∈ S, H b := Finset.prod_nonneg hH
  have hpow : 0 < d ^ S.card := pow_pos hd _
  have hden : d ^ S.card ≤ 2 * ∏ b ∈ S, D b := by
    have h := (le_div_iff₀ hpow).mp hgate
    nlinarith
  simp only [Finset.prod_div_distrib, Finset.prod_const]
  apply (div_le_iff₀ hprodD).2
  have h := mul_le_mul_of_nonneg_left hden (div_nonneg hprodH hpow.le)
  have heq : (∏ b ∈ S, H b) / d ^ S.card * d ^ S.card = ∏ b ∈ S, H b :=
    div_mul_cancel₀ _ hpow.ne'
  nlinarith

theorem external_neighbours_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Disjoint (clusterBulkNeighbours PT hPT a) (clusterCrossingNeighbours PT hPT a) := by
  apply Finset.disjoint_left.mpr
  intro b hb hc
  exact (Finset.mem_filter.mp hc).2.2 (Finset.mem_filter.mp hb).2.2.1

theorem row_le_nominal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (ω : CS.Outcome)
    (hω : CS.law.w ω ≠ 0) (hload : CS.historyLoad ω)
    (hb : 0 ≤ bstar T k) (hbs : bstar T k ≤ 1 / 100)
    (hell : ∀ i, 20 * ((PT.tiling.P i).ℓ : ℝ) * bstar T k ≤ 1 / 10)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    CS.row ω a x ≤ 4 * clusterSigma PT hPT hm (CS.history ω) (CS.internal ω) a x *
      ∏ b ∈ clusterBulkNeighbours PT hPT a ∪ clusterCrossingNeighbours PT hPT a,
        normalizedHit (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)) x (CS.label ω b) := by
  let W := CS.history ω
  let I := CS.internal ω
  let B := clusterBulkNeighbours PT hPT a
  let C := clusterCrossingNeighbours PT hPT a
  let t := fun b => clusterDegree PT hPT hm W b x
  let H := fun b => hit (T.S.E k) PT.tiling.c x (CS.label ω b)
  let f := fun b => normalizedHit (T.S.E k) PT.tiling.c
    (PT.π (patchAt PT hPT b.1)) x (CS.label ω b)
  have hH0 (b) : 0 ≤ H b := by dsimp [H]; unfold hit; split_ifs <;> norm_num
  have hf0 (b) : 0 ≤ f b := by
    dsimp [f, normalizedHit]
    split_ifs with hd
    · exact div_nonneg (hH0 b) hd.le
    · exact le_rfl
  have hσ0 := Lane_sol_s15_load.clusterSigma_nonneg PT hPT hm W I a x
  by_cases hzero : CS.row ω a x = 0
  · rw [hzero]
    exact mul_nonneg (mul_nonneg (by positivity) hσ0) (Finset.prod_nonneg fun b _ => hf0 b)
  have hx := CS.row_support ω hω hload a x hzero
  have hJ : clusterJ PT hPT hm W a x := by
    by_contra hnot
    apply hzero
    rw [CS.row_eq]
    simp [clusterRowWeight, W, hnot]
  let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w x
  have hd : 0 < d := hJ.1.2.2.1
  have ht (b) (hmem : b ∈ B ∪ C) : 0 < t b := by
    have hdeg : |t b - 1 / 2| ≤ 2 * bstar T k := by
      rcases Finset.mem_union.mp hmem with hB | hC
      · exact hJ.1.2.1 b hB
      · exact hJ.2 b hC
    have := (abs_le.mp hdeg).1
    linarith
  have hfactor (b) (hmem : b ∈ B ∪ C) :
      clusterFactor PT hPT hm W I a b x = H b / t b := by
    have hpos := ht b hmem
    dsimp [clusterFactor]
    rw [if_pos hpos]
    dsimp [H, t, I]
    rw [CS.label_eq]
  have hbulkEq (b) (hmem : b ∈ B) : f b = H b / d := by
    have hp := (Finset.mem_filter.mp hmem).2.2.1
    dsimp [f, normalizedHit]
    rw [hp, if_pos hd]
  have hbulk : (∏ b ∈ B, clusterFactor PT hPT hm W I a b x) ≤
      2 * ∏ b ∈ B, f b := by
    have hgate : (1 / 2 : ℝ) ≤ (∏ b ∈ B, t b) / d ^ B.card := hJ.1.2.2.2.1
    have h := bulk_product_gate_le B H t d hd
      (fun b _ => by dsimp [H]; unfold hit; split_ifs <;> norm_num)
      (fun b hb => ht b (Finset.mem_union_left C hb)) hgate
    convert h using 1
    · apply Finset.prod_congr rfl
      intro b hb
      exact hfactor b (Finset.mem_union_left C hb)
    · congr 1
      apply Finset.prod_congr rfl
      intro b hb
      exact hbulkEq b hb
  have hcrossFactor (b) (hmem : b ∈ C) :
      clusterFactor PT hPT hm W I a b x ≤ Real.exp (20 * bstar T k) * f b := by
    let db := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)).w x
    have hnpatch := (Finset.mem_filter.mp hmem).2.2
    have hdb : |db - 1 / 2| ≤ 3 * bstar T k :=
      hPT.envelope_other_degree (patchAt PT hPT a.1) (patchAt PT hPT b.1) hnpatch x hx
    have htb : |t b - 1 / 2| ≤ 2 * bstar T k := hJ.2 b hmem
    obtain ⟨htbpos, hdbpos, hratio⟩ := crossing_degree_ratio_le hb hbs htb hdb
    have hf : f b = H b / db := by
      change (if 0 < db then H b / db else 0) = H b / db
      rw [if_pos hdbpos]
    rw [hfactor b (Finset.mem_union_right B hmem), hf]
    calc
      H b / t b = (H b / db) * (db / t b) := by field_simp
      _ ≤ (H b / db) * Real.exp (20 * bstar T k) := by
        apply mul_le_mul_of_nonneg_left hratio
        exact div_nonneg (hH0 b) hdbpos.le
      _ = _ := by ring
  have hcross : (∏ b ∈ C, clusterFactor PT hPT hm W I a b x) ≤
      2 * ∏ b ∈ C, f b := by
    have hcount : C.card ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ := by
      apply Lane_q_s15_c2.clusterCrossingNeighbours_card_le_prefix PT hPT
        (patchAt PT hPT a.1) a
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).1⟩
    have hexp : (Real.exp (20 * bstar T k)) ^ C.card ≤ 2 := by
      rw [← Real.exp_nat_mul]
      have hcardR : (C.card : ℝ) ≤ (PT.tiling.P (patchAt PT hPT a.1)).ℓ := by exact_mod_cast hcount
      have he : (C.card : ℝ) * (20 * bstar T k) ≤ 1 / 10 := by
        nlinarith [mul_le_mul_of_nonneg_right hcardR hb, hell (patchAt PT hPT a.1)]
      calc
        _ ≤ Real.exp (1 / 10) := Real.exp_le_exp.mpr he
        _ ≤ 2 := by
          have h := Real.exp_bound_div_one_sub_of_interval (by norm_num : (0 : ℝ) ≤ 1 / 10)
            (by norm_num : (1 / 10 : ℝ) < 1)
          norm_num at h ⊢
          linarith
    calc
      _ ≤ ∏ b ∈ C, Real.exp (20 * bstar T k) * f b := by
        apply Finset.prod_le_prod₀
        · intro b hb
          rw [hfactor b (Finset.mem_union_right B hb)]
          exact div_nonneg (hH0 b) (ht b (Finset.mem_union_right B hb)).le
        · exact hcrossFactor
      _ = (Real.exp (20 * bstar T k)) ^ C.card * ∏ b ∈ C, f b := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 2 * ∏ b ∈ C, f b := mul_le_mul_of_nonneg_right hexp (Finset.prod_nonneg fun b _ => hf0 b)
  have hdisj := external_neighbours_disjoint PT hPT a
  rw [CS.row_eq]
  change clusterSigma PT hPT hm W I a x * (if clusterJ PT hPT hm W a x then 1 else 0) * _ ≤ _
  rw [if_pos hJ, mul_one, Finset.prod_union hdisj, Finset.prod_union hdisj]
  have hprod0 : 0 ≤ ∏ b ∈ B, clusterFactor PT hPT hm W I a b x := by
    apply Finset.prod_nonneg
    intro b hb
    rw [hfactor b (Finset.mem_union_left C hb)]
    exact div_nonneg (hH0 b) (ht b (Finset.mem_union_left C hb)).le
  have hprod := mul_le_mul hbulk hcross
    (Finset.prod_nonneg fun b hb => by
      rw [hfactor b (Finset.mem_union_right B hb)]
      exact div_nonneg (hH0 b) (ht b (Finset.mem_union_right B hb)).le)
    (mul_nonneg (by norm_num) (Finset.prod_nonneg fun b _ => hf0 b))
  have h := mul_le_mul_of_nonneg_left hprod hσ0
  dsimp [B, C, f] at h
  nlinarith

theorem high_gain_scales (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) → ∀ i,
        1 ≤ PT.tiling.gain i ∧ ((PT.tiling.P i).q : ℝ) ^ κ.Cb ≤ PT.tiling.gain i ∧
          ((PT.tiling.P i).ℓ : ℝ) ≤ PT.tiling.gain i := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hCb : 0 ≤ κ.Cb := by
    have hbound : 100 * (κ.aC / κ.aB) + 100 < κ.Cb := by
      convert hκ.Cb_big using 1 <;> ring
    have hratio : 0 < κ.aC / κ.aB := div_pos hκ.aC_rng.1 hκ.aB_rng.1
    linarith only [hbound, hratio]
  have hMhi : κ.Cb + 1 ≤ (κ.Mhi : ℝ) := by
    have h := hκ.Mhi_big.1
    have hpos := div_pos (by norm_num : (0 : ℝ) < 10) hκ.cq_rng.1
    linarith [hκ.Mlo_big]
  have hu : 1 ≤ κ.u := by have := hκ.u_rng.2; omega
  have hcq : κ.cq ≤ 2 := by
    have hMlo : 1 ≤ (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big]
    have hfrac : 1 / (20 * (κ.Mlo : ℝ)) ≤ (1 / 20 : ℝ) := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith
    linarith [hκ.cq_rng.2]
  let t := fun k => Real.log (T.S.n k : ℝ)
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hq : Tendsto (fun k => (t k) ^ κ.cq) atTop atTop :=
    (tendsto_rpow_atTop hκ.cq_rng.1).comp ht
  filter_upwards [ht.eventually_ge_atTop 1, hq.eventually_ge_atTop (max 1 (10 ^ 6 / κ.a))]
    with k ht1 hqbig
  intro PT hPT hm i
  have hdata := hPT.tiling_valid.cluster_data (Or.inr hm) i
  have hqlo : (t k) ^ κ.cq ≤ (PT.tiling.P i).q := by
    rcases hm with hs | hl
    · exact (hdata.2.2.2.2.2.2.2.2.2.2.1.mp hs).1.le
    · have hlarge := hdata.2.2.2.2.2.2.2.2.2.2.2.mp hl
      calc
        (t k) ^ κ.cq ≤ (t k) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hcq
        _ = (t k) ^ (2 : ℕ) := Real.rpow_natCast _ _
        _ ≤ _ := hlarge.le
  have hq1 : (1 : ℝ) ≤ (PT.tiling.P i).q := (le_max_left _ _).trans (hqbig.trans hqlo)
  have hqA : 10 ^ 6 / κ.a ≤ ((PT.tiling.P i).q : ℝ) :=
    (le_max_right _ _).trans (hqbig.trans hqlo)
  have hgain : PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
    rcases hm with hs | hl
    · simp [Tiling.gain, hs]
    · simp [Tiling.gain, hl]
  have hh : ((PT.tiling.P i).q : ℝ) ^ (κ.Mhi : ℝ) ≤ (PT.tiling.P i).h := by
    rcases hm with hs | hl
    · simpa [hs] using hdata.2.2.2.2.2.2.2.1
    · simpa [hl] using hdata.2.2.2.2.2.2.2.1
  have hqpow : ((PT.tiling.P i).q : ℝ) ^ κ.Cb * (PT.tiling.P i).q ≤ (PT.tiling.P i).h := by
    calc
      _ = ((PT.tiling.P i).q : ℝ) ^ (κ.Cb + 1) := by
        rw [Real.rpow_add (by linarith : (0 : ℝ) < (PT.tiling.P i).q), Real.rpow_one]
      _ ≤ ((PT.tiling.P i).q : ℝ) ^ (κ.Mhi : ℝ) := Real.rpow_le_rpow_of_exponent_le hq1 hMhi
      _ ≤ _ := hh
  have hp0 : 0 ≤ ((PT.tiling.P i).q : ℝ) ^ κ.Cb := Real.rpow_nonneg (by positivity) _
  have hscale : ((PT.tiling.P i).q : ℝ) ^ κ.Cb ≤ PT.tiling.gain i := by
    rw [hgain]
    have hqmul := (div_le_iff₀ ha).mp hqA
    have hmul := mul_le_mul_of_nonneg_left hqmul hp0
    have hmul2 := mul_le_mul_of_nonneg_left hqpow ha.le
    nlinarith
  have hs1 : 1 ≤ PT.tiling.gain i := (Real.one_le_rpow hq1 hCb).trans hscale
  refine ⟨hs1, hscale, ?_⟩
  rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | halloc
  · rcases hm with hs | hl
    · simp [hb] at hs
    · simp [hb] at hl
  · have huR : 1 ≤ (κ.u : ℝ) := by exact_mod_cast hu
    exact halloc.1.trans (by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * κ.u)).2
      nlinarith)

theorem row_cap {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (CS : ClusterSample PT hPT hm) (ω : CS.Outcome)
    (hω : CS.law.w ω ≠ 0) (hload : CS.historyLoad ω)
    (hn : 0 < T.S.n k)
    (hb : 0 ≤ bstar T k) (hbs : bstar T k ≤ 1 / 100)
    (hell : ∀ i, 20 * ((PT.tiling.P i).ℓ : ℝ) * bstar T k ≤ 1 / 10)
    (hwindow : ∀ i, 10 * ((PT.tiling.P i).q : ℝ) ^ κ.Cb / (T.S.n k : ℝ) ≤ 1 / 6)
    (hscales : ∀ i, 1 ≤ PT.tiling.gain i ∧
      ((PT.tiling.P i).q : ℝ) ^ κ.Cb ≤ PT.tiling.gain i ∧
      ((PT.tiling.P i).ℓ : ℝ) ≤ PT.tiling.gain i)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) :
    (PT.tiling.P (patchAt PT hPT a.1)).M * CS.row ω a x ≤
      2 ^ (T.S.n k) * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  by_cases hzero : CS.row ω a x = 0
  · rw [hzero, mul_zero]; positivity
  let i := patchAt PT hPT a.1
  let B := clusterBulkNeighbours PT hPT a
  let C := clusterCrossingNeighbours PT hPT a
  let f := fun b => normalizedHit (T.S.E k) PT.tiling.c
    (PT.π (patchAt PT hPT b.1)) x (CS.label ω b)
  let Q : ℝ := ((PT.tiling.P i).q : ℝ) ^ κ.Cb
  let e : ℝ := 10 * Q / (T.S.n k : ℝ)
  let s : ℝ := PT.tiling.gain i
  let σ : ℝ := clusterSigma PT hPT hm (CS.history ω) (CS.internal ω) a x
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast hn
  have hx := CS.row_support ω hω hload a x hzero
  have hf0 (b) : 0 ≤ f b := by
    dsimp [f, normalizedHit]
    split_ifs with hd
    · exact div_nonneg (by unfold hit; split_ifs <;> norm_num) hd.le
    · exact le_rfl
  have he0 : 0 ≤ e := by dsimp [e, Q]; positivity
  have hσ0 : 0 ≤ σ := Lane_sol_s15_load.clusterSigma_nonneg PT hPT hm _ _ a x
  have hbulk (b) (hmem : b ∈ B) : f b ≤ 2 * Real.exp (6 * e) := by
    have hp := (Finset.mem_filter.mp hmem).2.2.1
    let d := deg (T.S.E k) PT.tiling.c (PT.π i).w x
    have hd : |d - 1 / 2| ≤ e := by
      have h := hPT.envelope_degree i x hx
      rcases hm with hs | hl
      · simpa [OwnDegOK, hs, e, Q, d] using h
      · simpa [OwnDegOK, hl, e, Q, d] using h
    obtain ⟨hdpos, hinv⟩ := inverse_degree_le he0 (hwindow i) hd
    dsimp [f, normalizedHit]
    rw [hp, if_pos hdpos]
    have hhit : hit (T.S.E k) PT.tiling.c x (CS.label ω b) ≤ 1 := by
      unfold hit; split_ifs <;> norm_num
    exact (div_le_div_of_nonneg_right hhit hdpos.le).trans hinv
  have hcross (b) (hmem : b ∈ C) : f b ≤ 2 * Real.exp (18 * bstar T k) := by
    have hp := (Finset.mem_filter.mp hmem).2.2
    let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)).w x
    have hd : |d - 1 / 2| ≤ 3 * bstar T k := hPT.envelope_other_degree i _ hp x hx
    obtain ⟨hdpos, hinv⟩ := inverse_degree_le (by positivity : 0 ≤ 3 * bstar T k)
      (by linarith : 3 * bstar T k ≤ 1 / 6) hd
    dsimp [f, normalizedHit]
    rw [if_pos hdpos]
    have hhit : hit (T.S.E k) PT.tiling.c x (CS.label ω b) ≤ 1 := by
      unfold hit; split_ifs <;> norm_num
    have h := (div_le_div_of_nonneg_right hhit hdpos.le).trans hinv
    convert h using 1 <;> ring
  have hBcard : B.card ≤ T.S.n k := by
    have hE := external_neighbours_card_le PT hPT a
    have hsub : B ⊆ B ∪ C := Finset.subset_union_left
    exact (Finset.card_le_card hsub).trans (hE.trans (Nat.sub_le _ _))
  have hCcard : C.card ≤ (PT.tiling.P i).ℓ := by
    apply Lane_q_s15_c2.clusterCrossingNeighbours_card_le_prefix PT hPT i a
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).1⟩
  have hBexp : 6 * e * (B.card : ℝ) ≤ 60 * Q := by
    have hcardR : (B.card : ℝ) ≤ T.S.n k := by exact_mod_cast hBcard
    dsimp [e]
    have h := mul_le_mul_of_nonneg_left hcardR (by positivity : 0 ≤ 6 * (10 * Q / (T.S.n k : ℝ)))
    have heq : 6 * (10 * Q / (T.S.n k : ℝ)) * (T.S.n k : ℝ) = 60 * Q := by
      field_simp; ring
    exact h.trans_eq heq
  have hCexp : 18 * bstar T k * (C.card : ℝ) ≤ 18 * bstar T k * (PT.tiling.P i).ℓ := by
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast hCcard)
    positivity
  have hprodB : (∏ b ∈ B, f b) ≤ (2 : ℝ) ^ B.card * Real.exp (60 * Q) := by
    calc
      _ ≤ ∏ b ∈ B, 2 * Real.exp (6 * e) := Finset.prod_le_prod₀ (fun b _ => hf0 b) hbulk
      _ = (2 : ℝ) ^ B.card * Real.exp (6 * e * (B.card : ℝ)) := by
        rw [Finset.prod_const, mul_pow, ← Real.exp_nat_mul]; congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hBexp) (by positivity)
  have hprodC : (∏ b ∈ C, f b) ≤ (2 : ℝ) ^ C.card *
      Real.exp (18 * bstar T k * (PT.tiling.P i).ℓ) := by
    calc
      _ ≤ ∏ b ∈ C, 2 * Real.exp (18 * bstar T k) := Finset.prod_le_prod₀ (fun b _ => hf0 b) hcross
      _ = (2 : ℝ) ^ C.card * Real.exp (18 * bstar T k * (C.card : ℝ)) := by
        rw [Finset.prod_const, mul_pow, ← Real.exp_nat_mul]; congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hCexp) (by positivity)
  have hdisj := external_neighbours_disjoint PT hPT a
  have hEcard : (PT.tiling.P i).h + (B.card + C.card) ≤ T.S.n k := by
    have hE := external_neighbours_card_le PT hPT a
    rw [Finset.card_union_of_disjoint hdisj] at hE
    have hh := clusterHeight_le PT hPT i
    dsimp [i, B, C] at *
    omega
  have hM : (PT.tiling.P i).M ≤ T.S.N k := by
    rw [← (PT.tiling.P i).cardX]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have hMσ : (PT.tiling.P i).M * σ ≤
      (2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (-500 * s) := by
    have hcap := (clusterSolver PT hPT hm i).σ_cap (clusterCenterRole PT hPT hm a)
      (historyOnSlice (CS.history ω) (clusterSliceAt PT hPT a.1))
      (nbrLabels (clusterCenterRole PT hPT hm a).1 (CS.internal ω (clusterSliceAt PT hPT a.1)).2) x
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hM) hσ0).trans hcap
  have herror : 60 * Q + 18 * bstar T k * (PT.tiling.P i).ℓ ≤ 61 * s := by
    have hs := hscales i
    have hmul := mul_le_mul_of_nonneg_right hbs (Nat.cast_nonneg (PT.tiling.P i).ℓ)
    dsimp [Q, s] at *
    nlinarith
  have hfinal : 4 * Real.exp (-500 * s + (60 * Q + 18 * bstar T k * (PT.tiling.P i).ℓ)) ≤
      Real.exp (-200 * s) := by
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 2 ≤ Real.exp 1)
      rw [← Real.exp_add] at hsq
      norm_num at hsq
      exact hsq
    calc
      _ ≤ Real.exp 2 * Real.exp (-500 * s + (60 * Q + 18 * bstar T k * (PT.tiling.P i).ℓ)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = Real.exp (2 + (-500 * s + (60 * Q + 18 * bstar T k * (PT.tiling.P i).ℓ))) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [(hscales i).1])
  have hrow := row_le_nominal PT hPT hm CS ω hω hload hb hbs hell a x
  change CS.row ω a x ≤ 4 * σ * ∏ b ∈ B ∪ C, f b at hrow
  rw [Finset.prod_union hdisj] at hrow
  have hprod := mul_le_mul hprodB hprodC (Finset.prod_nonneg fun b _ => hf0 b) (by positivity)
  calc
    (PT.tiling.P i).M * CS.row ω a x ≤
      4 * ((PT.tiling.P i).M * σ) * ((∏ b ∈ B, f b) * ∏ b ∈ C, f b) := by
        have h := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg (PT.tiling.P i).M)
        nlinarith
    _ ≤ 4 * ((2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (-500 * s)) *
      (((2 : ℝ) ^ B.card * Real.exp (60 * Q)) *
        ((2 : ℝ) ^ C.card * Real.exp (18 * bstar T k * (PT.tiling.P i).ℓ))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hMσ (by norm_num)
        · exact hprod
        · exact mul_nonneg (Finset.prod_nonneg fun b _ => hf0 b) (Finset.prod_nonneg fun b _ => hf0 b)
        · positivity
    _ = (2 : ℝ) ^ ((PT.tiling.P i).h + (B.card + C.card)) *
        (4 * Real.exp (-500 * s + (60 * Q + 18 * bstar T k * (PT.tiling.P i).ℓ))) := by
        rw [pow_add, pow_add, Real.exp_add, Real.exp_add]; ring
    _ ≤ (2 : ℝ) ^ (T.S.n k) * Real.exp (-200 * s) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num) hEcard) hfinal (by positivity) (by positivity)

end HypercubeRamsey.Lane_sol_s15_c2
