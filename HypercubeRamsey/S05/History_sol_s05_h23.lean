import HypercubeRamsey.S05.History_q_s05_h23

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical Filter OAI.HypercubeRamsey Lane_q_s05_h23
open scoped BigOperators Topology

set_option synthInstance.maxSize 1024
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

noncomputable section
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

theorem pr_exists_le_sum5 {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinProb Ω) (A : I → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) :=
  FinProb.pr_exists_le_sum5 P A

theorem signShiftType5_keys_card (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    (signShiftType5 X t K).2.1.card = K.2.1.card := by
  change (K.2.1.image (signShiftKey5 X t)).card = K.2.1.card
  exact Finset.card_image_of_injective _ (signShiftKey5 X t).injective

theorem gateKeys_signShiftLow5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    X.gateKeys (signShiftType5 X t K) =
      (X.gateKeys K).image (signShiftKey5 X t) := by
  simp [Setup5.gateKeys, signShiftType5, hlevel]

theorem binNeighborVal5_dist_le {n : ℕ} (w : Fin (n + 1)) (d : Fin 3) :
    Nat.dist w.val (binNeighborVal5 w d).val ≤ 1 := by
  by_cases h0 : d.val = 0
  · simp [binNeighborVal5, h0]
    rw [Nat.dist_eq_sub_of_le_right (Nat.sub_le _ _)]
    omega
  · by_cases h1 : d.val = 1
    · simp [binNeighborVal5, h0, h1]
    · have h2 : d.val = 2 := by omega
      have hw : w.val ≤ n := by omega
      by_cases htop : w.val = n
      · simp [binNeighborVal5, h0, h1, h2, htop]
      · have hplus : w.val + 1 ≤ n := by omega
        have hmin : min n (w.val + 1) = w.val + 1 := Nat.min_eq_right hplus
        simp [binNeighborVal5, h0, h1, h2, hmin]
        rw [Nat.dist_eq_sub_of_le (by omega)]
        omega

theorem binAdjacent_mem_nearBinVectors5 {n : ℕ} (w z : BinVector5 n)
    (h : binAdjacent5 w z) : z ∈ nearBinVectors5 w := by
  apply mem_nearBinVectors5_of_coords
  intro i
  have hd : Nat.dist (w i).val (z i).val ≤ 1 := h.2 i
  have hb : (w i).val ≤ (z i).val + 1 ∧ (z i).val ≤ (w i).val + 1 := by
    rcases Nat.le_total (w i).val (z i).val with hle | hge
    · rw [Nat.dist_eq_sub_of_le hle] at hd
      omega
    · rw [Nat.dist_eq_sub_of_le_right hge] at hd
      omega
  obtain ⟨d, hEq⟩ := exists_binNeighborVal5 (w i) (z i) hb.1 hb.2
  unfold binNeighborVals5
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hEq.symm⟩

theorem binList_mem_nearBinVectors5 {n : ℕ} (q : CoarseKey5 n) (w : BinVector5 n)
    (hw : w ∈ binList5 q) : w ∈ nearBinVectors5 q.1 := by
  by_cases hb : q.2
  · simp only [binList5, if_pos hb, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with rfl | hadj
    · exact binVector_self_mem_near5 q.1
    · exact binAdjacent_mem_nearBinVectors5 q.1 w hadj
  · simp [binList5, hb] at hw
    subst w
    exact binVector_self_mem_near5 q.1

theorem nearBinVectors_coord_dist5 {n : ℕ} (w z : BinVector5 n)
    (hz : z ∈ nearBinVectors5 w) :
    ∀ i, Nat.dist (w i).val (z i).val ≤ 1 := by
  classical
  unfold nearBinVectors5 at hz
  obtain ⟨f, hf, hEq⟩ := Finset.mem_image.mp hz
  intro i
  have hpi : f i (Finset.mem_univ i) ∈ binNeighborVals5 w i :=
    (Finset.mem_pi.mp hf) i (Finset.mem_univ i)
  obtain ⟨d, hd, hval⟩ := Finset.mem_image.mp hpi
  have hval' : binNeighborVal5 (w i) d = z i := by
    calc
      binNeighborVal5 (w i) d = f i (Finset.mem_univ i) := hval
      _ = z i := congrFun hEq i
  rw [← hval']
  exact binNeighborVal5_dist_le (w i) d

theorem nearBinVectors_mem_symm5 {n : ℕ} (w z : BinVector5 n)
    (hz : z ∈ nearBinVectors5 w) : w ∈ nearBinVectors5 z := by
  apply mem_nearBinVectors5_of_coords
  intro i
  have hd := nearBinVectors_coord_dist5 w z hz i
  have hb : (z i).val ≤ (w i).val + 1 ∧ (w i).val ≤ (z i).val + 1 := by
    rcases Nat.le_total (w i).val (z i).val with hle | hge
    · rw [Nat.dist_eq_sub_of_le hle] at hd
      omega
    · rw [Nat.dist_eq_sub_of_le_right hge] at hd
      omega
  obtain ⟨d, hEq⟩ := exists_binNeighborVal5 (z i) (w i) hb.1 hb.2
  unfold binNeighborVals5
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hEq.symm⟩

def nearBinVectors2_5 {n : ℕ} (w : BinVector5 n) : Finset (BinVector5 n) :=
  (nearBinVectors5 w).biUnion nearBinVectors5

def nearCoarseKeys2_5 {n : ℕ} (w : BinVector5 n) : Finset (CoarseKey5 n) :=
  (nearBinVectors2_5 w).product (Finset.univ : Finset Bool)

theorem nearBinVectors2_card_le5 {n : ℕ} (w : BinVector5 n) :
    (nearBinVectors2_5 w).card ≤ (3 ^ coarseChunkCount5) ^ 2 := by
  classical
  calc
    (nearBinVectors2_5 w).card ≤
        ∑ z ∈ nearBinVectors5 w, (nearBinVectors5 z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ nearBinVectors5 w, 3 ^ coarseChunkCount5 := by
      apply Finset.sum_le_sum
      intro z hz
      exact nearBinVectors5_card_le z
    _ = (nearBinVectors5 w).card * 3 ^ coarseChunkCount5 := by simp
    _ ≤ 3 ^ coarseChunkCount5 * 3 ^ coarseChunkCount5 :=
      Nat.mul_le_mul_right _ (nearBinVectors5_card_le w)
    _ = (3 ^ coarseChunkCount5) ^ 2 := by ring

theorem nearCoarseKeys2_card_le5 {n : ℕ} (w : BinVector5 n) :
    (nearCoarseKeys2_5 w).card ≤ 2 * (3 ^ coarseChunkCount5) ^ 2 := by
  classical
  calc
    (nearCoarseKeys2_5 w).card =
        (nearBinVectors2_5 w).card * (Finset.univ : Finset Bool).card :=
      Finset.card_product _ _
    _ ≤ (3 ^ coarseChunkCount5) ^ 2 * 2 :=
      Nat.mul_le_mul_right _ (nearBinVectors2_card_le5 w)
    _ = 2 * (3 ^ coarseChunkCount5) ^ 2 := by omega


theorem nearBinVectors2_mem_symm5 {n : ℕ} (w z : BinVector5 n)
    (hz : z ∈ nearBinVectors2_5 w) : w ∈ nearBinVectors2_5 z := by
  obtain ⟨u, huw, hzu⟩ := Finset.mem_biUnion.mp hz
  change w ∈ (nearBinVectors5 z).biUnion nearBinVectors5
  apply Finset.mem_biUnion.mpr
  refine ⟨u, ?_, ?_⟩
  · exact nearBinVectors_mem_symm5 u z hzu
  · exact nearBinVectors_mem_symm5 w u huw

theorem nearBinVectors2_self5 {n : ℕ} (w : BinVector5 n) : w ∈ nearBinVectors2_5 w := by
  apply Finset.mem_biUnion.mpr
  exact ⟨w, binVector_self_mem_near5 w, binVector_self_mem_near5 w⟩

theorem stage2LowPatternAt_gateKeys_coarse5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j) :
    ∀ ℓ ∈ X.gateKeys p.1, ℓ.coarse ∈ nearCoarseKeys5 q.1 := by
  have hgate : X.gateKeys p.1 = p.1.2.1 := by
    simp [Setup5.gateKeys, p.2.2.2.1]
  rw [hgate]
  exact lowTypeCandidates_keys_coarse5 X q default j p.1 p.2.1

theorem stage2HighPatternAt_gateKeys_coarse5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (p : Stage2HighPatternAt5 X q) :
    ∀ ℓ ∈ X.gateKeys p.1, ℓ.coarse ∈ nearCoarseKeys5 q.1 := by
  have hkeys := highTypeCandidates_keys_coarse5 X q p.1 p.2.1
  have hlevel : p.1.2.2 = none := p.2.2.2.1
  intro ℓ hℓ
  simp only [Setup5.gateKeys, hlevel, if_pos, Finset.mem_union, Finset.mem_singleton] at hℓ
  rcases hℓ with hmem | heq
  · exact hkeys ℓ hmem
  · subst ℓ
    simpa [Setup5.optKeyOf, HiddenKey5.coarse, p.2.2.1] using coarseKey_mem_nearKeys5 q

private theorem stage2CoarseBound_exists :
    ∃ D : ℕ, ∀ {n : ℕ} (w : BinVector5 n), (nearCoarseKeys5 w).card ≤ D :=
  ⟨2 * 3 ^ coarseChunkCount5, by intro n w; exact nearCoarseKeys5_card_le w⟩

noncomputable def stage2CoarseCountBase5 : ℕ := Classical.choose stage2CoarseBound_exists

theorem nearCoarseKeys5_card_le_stage2Base5 {n : ℕ} (w : BinVector5 n) :
    (nearCoarseKeys5 w).card ≤ stage2CoarseCountBase5 :=
  Classical.choose_spec stage2CoarseBound_exists w

def lowKeysBase5 : ℕ := coarseChunkCount5 * 4 + 3

@[irreducible] def stage2TypeCountBase5 : ℕ := 2 ^ (stage2CoarseCountBase5)


theorem tendsto_m_atTop_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ) :
    Tendsto (fun n : ℕ => (p.m n : ℝ)) atTop atTop := by
  have hmle (n : ℕ) : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
    dsimp [Params5.m]
    exact Nat.le_ceil _
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
    (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono hmle hpow

theorem J_le_m_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ) (n : ℕ)
    (hm : 1 ≤ p.m n) : p.J n ≤ p.m n := by
  have hmreal : 1 ≤ (p.m n : ℝ) := by exact_mod_cast hm
  have hrpow : (p.m n : ℝ) ^ (1 / 20 : ℝ) ≤ (p.m n : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hmreal (by norm_num : (1 / 20 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hfloor : (Nat.floor ((p.m n : ℝ) ^ (1 / 20 : ℝ)) : ℝ) ≤
      (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (by positivity)
  have hcast : (p.J n : ℝ) ≤ (p.m n : ℝ) := by
    simpa [Params5.J] using hfloor.trans hrpow
  exact_mod_cast hcast

theorem q0_uSeg_lower_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) :
    p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) ≤
      (p.q0 : ℝ) * (p.uSeg n j : ℝ) := by
  have hq : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
  have hceil :
      p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤
        (p.uSeg n j : ℝ) := by
    dsimp [Params5.uSeg]
    exact Nat.le_ceil _
  calc
    p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) =
        (p.q0 : ℝ) *
          (p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by
            field_simp [ne_of_gt hq]
    _ ≤ (p.q0 : ℝ) * (p.uSeg n j : ℝ) :=
      mul_le_mul_of_nonneg_left hceil hq.le

theorem q0_uStarSeg_lower_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n : ℕ) :
    p.eta * Real.log (p.m n : ℝ) ≤ (p.q0 : ℝ) * (p.uStarSeg n : ℝ) := by
  have hq : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
  have hceil : p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤
      (p.uStarSeg n : ℝ) := by
    dsimp [Params5.uStarSeg]
    exact Nat.le_ceil _
  calc
    p.eta * Real.log (p.m n : ℝ) =
        (p.q0 : ℝ) * (p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by
          field_simp [ne_of_gt hq]
    _ ≤ (p.q0 : ℝ) * (p.uStarSeg n : ℝ) :=
      mul_le_mul_of_nonneg_left hceil hq.le

theorem capBudget_le_mpow_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n k : ℕ) (hm : 1 ≤ p.m n) (hK1 : 8 / p.delta ≤ p.K1) :
    Real.exp (-(p.delta * (p.q0 * p.uSeg n (k + 1))) / 2) ≤
      Real.exp (-20 * Real.log (p.m n : ℝ)) := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have ht : 0 ≤ ((k : ℝ) + 5) * Real.log (p.m n : ℝ) :=
    mul_nonneg (by positivity) hlog
  have hseg := q0_uSeg_lower_h23 p n (k + 1)
  have hk : 8 ≤ p.delta * p.K1 := by
    simpa only [mul_comm] using (div_le_iff₀ p.hdelta.1).mp hK1
  have hcoef : 4 ≤ p.delta * p.K1 / 2 := by nlinarith [hk]
  have hlow : 20 * Real.log (p.m n : ℝ) ≤
      (p.delta * p.K1 / 2) * (((k : ℝ) + 5) * Real.log (p.m n : ℝ)) := by
    have hj : (5 : ℝ) ≤ (k : ℝ) + 5 := by exact_mod_cast Nat.le_add_left 5 k
    nlinarith [mul_le_mul_of_nonneg_right hj hlog]
  have hscale :
      (p.delta * p.K1 / 2) * (((k : ℝ) + 5) * Real.log (p.m n : ℝ)) ≤
        p.delta * ((p.q0 : ℝ) * p.uSeg n (k + 1) : ℝ) / 2 := by
    have hs := mul_le_mul_of_nonneg_left hseg (div_nonneg p.hdelta.1.le (by norm_num : (0 : ℝ) ≤ 2))
    convert hs using 1 <;> push_cast <;> ring
  apply Real.exp_le_exp.mpr
  nlinarith [hlow.trans hscale]

theorem lowAlarmExp_le5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) (hK1 : 8 / p.delta ≤ p.K1) :
    Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 4) ≤
      Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have ht : 0 ≤ ((j : ℝ) + 4) * Real.log (p.m n : ℝ) := mul_nonneg (by positivity) hlog
  have hseg := q0_uSeg_lower_h23 p n j
  have hk : 8 ≤ p.delta * p.K1 := by
    have h := (div_le_iff₀ p.hdelta.1).mp hK1
    nlinarith [h]
  have hcoef : 2 ≤ p.delta * p.K1 / 4 := by nlinarith [hk]
  have hscaled :
      (p.delta / 4) * (p.K1 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ))) ≤
        (p.delta / 4) * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) :=
    by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hseg
        (div_nonneg p.hdelta.1.le (by norm_num : (0 : ℝ) ≤ 4))
  have hrate : 2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
      p.delta * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) / 4 := by
    calc
      2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
          (p.delta * p.K1 / 4) * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef ht
      _ = (p.delta / 4) *
            (p.K1 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ))) := by ring
      _ ≤ (p.delta / 4) * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) := hscaled
      _ = p.delta * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) / 4 := by ring
  exact Real.exp_le_exp.mpr (by nlinarith [hrate])

theorem lowAlarmExpStep1_le5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) (hK1 : 8 / p.delta ≤ p.K1) :
    Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 2) ≤
      Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by
  refine le_trans ?_ (lowAlarmExp_le5 p n j hm hK1)
  apply Real.exp_le_exp.mpr
  have hpos : 0 ≤ p.delta * (p.q0 * p.uSeg n j : ℝ) :=
    mul_nonneg p.hdelta.1.le (by positivity)
  nlinarith [hpos]

theorem highAlarmExp_le5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n : ℕ) :
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) ≤
      Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ)) := by
  have hseg := q0_uStarSeg_lower_h23 p n
  have hscaled := mul_le_mul_of_nonneg_left hseg
    (div_nonneg p.hdelta.1.le (by norm_num : (0 : ℝ) ≤ 4))
  apply Real.exp_le_exp.mpr
  nlinarith [hscaled]

theorem natPow_mul_exp_decay5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ j : ℝ) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
      Real.exp (-8 * Real.log (p.m n : ℝ)) := by
  have hmpos : 0 < (p.m n : ℝ) := by exact_mod_cast (by omega : 0 < p.m n)
  have hpow : ((p.m n) ^ j : ℝ) =
      Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) := by
    calc
      ((p.m n) ^ j : ℝ) = (p.m n : ℝ) ^ j := by norm_cast
      _ = (p.m n : ℝ) ^ (j : ℝ) := by rw [← Real.rpow_natCast]
      _ = Real.exp (Real.log (p.m n : ℝ) * (j : ℝ)) :=
        Real.rpow_def_of_pos hmpos _
      _ = Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) := by congr 1; ring
  calc
    ((p.m n) ^ j : ℝ) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) =
      Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by rw [hpow]
    _ = Real.exp (-((j : ℝ) + 8) * Real.log (p.m n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-8 * Real.log (p.m n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
      nlinarith [hlog]

theorem natPow_eq_exp_log_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n k : ℕ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ k : ℝ) = Real.exp ((k : ℝ) * Real.log (p.m n : ℝ)) := by
  have hmpos : 0 < (p.m n : ℝ) := by exact_mod_cast (by omega : 0 < p.m n)
  calc
    ((p.m n) ^ k : ℝ) = (p.m n : ℝ) ^ k := by norm_cast
    _ = (p.m n : ℝ) ^ (k : ℝ) := by rw [← Real.rpow_natCast]
    _ = Real.exp (Real.log (p.m n : ℝ) * (k : ℝ)) :=
      Real.rpow_def_of_pos hmpos _
    _ = Real.exp ((k : ℝ) * Real.log (p.m n : ℝ)) := by congr 1; ring

theorem natPow_exp_cancel_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n k : ℕ) (a : ℝ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ k : ℝ) * Real.exp (-a * Real.log (p.m n : ℝ)) =
      Real.exp (((k : ℝ) - a) * Real.log (p.m n : ℝ)) := by
  rw [natPow_eq_exp_log_h23 p n k hm, ← Real.exp_add]
  congr 1
  ring

theorem stage2LowPatternAt_keys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j) :
    p.1.2.1.card ≤ lowKeysBase5 + j.val := by
  rcases p.2.2.2.2 with ⟨x, hx, hK⟩
  let K0 := X.g.evenType (X.p.J n) x
  have hlevel0 : K0.2.2 = some j := by
    have h := p.2.2.2.1
    rw [hK, signShiftType5_level] at h
    exact h
  have hlow : X.g.severity x ≤ X.p.J n := by
    by_contra hnot
    have hnone : K0.2.2 = none := by
      simp [K0, ChunkGeometry5.evenType, hnot]
    rw [hnone] at hlevel0
    cases hlevel0
  have hfin : (⟨X.g.severity x, Nat.lt_succ_of_le hlow⟩ : Fin (X.p.J n + 1)) = j := by
    have hsome : some (⟨X.g.severity x, Nat.lt_succ_of_le hlow⟩ : Fin (X.p.J n + 1)) = some j := by
      simpa [K0, ChunkGeometry5.evenType, hlow] using hlevel0
    exact Option.some.inj hsome
  have hseverity : X.g.severity x = j.val := congrArg Fin.val hfin
  have hcard := typeKeys_card_le_severity5 X x
  calc
    p.1.2.1.card = (X.g.typeKeys (X.p.J n) x).card := by
      rw [hK, signShiftType5_keys_card]
      simp [K0, ChunkGeometry5.evenType]
    _ ≤ coarseChunkCount5 * 4 + 1 + X.g.severity x + 2 := hcard
    _ = lowKeysBase5 + j.val := by rw [hseverity, lowKeysBase5]; omega

theorem stage2LowPatternAt_gateKeys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j) :
    (X.gateKeys p.1).card ≤ lowKeysBase5 + j.val := by
  have hgate : X.gateKeys p.1 = p.1.2.1 := by
    simp [Setup5.gateKeys, p.2.2.2.1]
  rw [hgate]
  exact stage2LowPatternAt_keys_card_le5 X q j p

theorem highTypeCandidates_keys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hK : K ∈ highTypeCandidates5 X q) :
    K.2.1.card ≤ (nearCoarseKeys5 q.1).card := by
  classical
  obtain ⟨C, hC, hEq⟩ := Finset.mem_image.mp hK
  rw [← hEq]
  dsimp [highTypeFromData5]
  calc
    (C.image fun i => (Sum.inr i : X.Key)).card ≤ C.card := Finset.card_image_le
    _ ≤ (nearCoarseKeys5 q.1).card := Finset.card_le_card (Finset.mem_powerset.mp hC)

theorem stage2HighPatternAt_gateKeys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (p : Stage2HighPatternAt5 X q) (D : ℕ)
    (hD : (nearCoarseKeys5 q.1).card ≤ D) :
    (X.gateKeys p.1).card ≤ D + 1 := by
  have hkeys : p.1.2.1.card ≤ D :=
    (highTypeCandidates_keys_card_le5 X q p.1 p.2.1).trans hD
  have hlevel : p.1.2.2 = none := p.2.2.2.1
  have hgate : X.gateKeys p.1 = p.1.2.1 ∪ {X.optKeyOf p.1 default} := by
    simp [Setup5.gateKeys, Setup5.optKeyOf, hlevel]
  rw [hgate]
  calc
    (p.1.2.1 ∪ {X.optKeyOf p.1 default}).card ≤ p.1.2.1.card + 1 := by
      exact (Finset.card_union_le _ _).trans (by simp)
    _ ≤ D + 1 := Nat.add_le_add_right hkeys 1

abbrev Stage2LowStep1Data5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :=
  Σ p : Stage2LowPatternAt5 X q j, {ℓ : X.Key // ℓ ∈ X.gateKeys p.1}

noncomputable instance stage2LowStep1DataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) : Fintype (Stage2LowStep1Data5 X q j) := by
  classical
  infer_instance

theorem stage2LowStep1Data_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :
    Fintype.card (Stage2LowStep1Data5 X q j) ≤
      (lowTypeCandidates5 X q default j).card * (lowKeysBase5 + j.val) := by
  classical
  calc
    Fintype.card (Stage2LowStep1Data5 X q j) =
        ∑ p : Stage2LowPatternAt5 X q j,
          Fintype.card {ℓ : X.Key // ℓ ∈ X.gateKeys p.1} := Fintype.card_sigma
    _ ≤ ∑ _p : Stage2LowPatternAt5 X q j, (lowKeysBase5 + j.val) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Fintype.card_coe]
      exact stage2LowPatternAt_gateKeys_card_le5 X q j p
    _ = Fintype.card (Stage2LowPatternAt5 X q j) * (lowKeysBase5 + j.val) := by simp
    _ ≤ (lowTypeCandidates5 X q default j).card * (lowKeysBase5 + j.val) := by
      exact Nat.mul_le_mul_right _ (stage2LowPatternAt_card_le5 X q j)

abbrev Stage2HighStep1Data5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  Σ p : Stage2HighPatternAt5 X q, {ℓ : X.Key // ℓ ∈ X.gateKeys p.1}

noncomputable instance stage2HighStep1DataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighStep1Data5 X q) := by
  classical
  infer_instance

theorem stage2HighStep1Data_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (D : ℕ) (hD : (nearCoarseKeys5 q.1).card ≤ D) :
    Fintype.card (Stage2HighStep1Data5 X q) ≤ 2 ^ D * (D + 1) := by
  classical
  calc
    Fintype.card (Stage2HighStep1Data5 X q) =
        ∑ p : Stage2HighPatternAt5 X q,
          Fintype.card {ℓ : X.Key // ℓ ∈ X.gateKeys p.1} := Fintype.card_sigma
    _ ≤ ∑ _p : Stage2HighPatternAt5 X q, (D + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Fintype.card_coe]
      exact stage2HighPatternAt_gateKeys_card_le5 X q p D hD
    _ = Fintype.card (Stage2HighPatternAt5 X q) * (D + 1) := by simp
    _ ≤ (highTypeCandidates5 X q).card * (D + 1) :=
      Nat.mul_le_mul_right _ (stage2HighPatternAt_card_le5 X q)
    _ ≤ 2 ^ D * (D + 1) := Nat.mul_le_mul_right _ (highTypeCandidates_card5 X q D hD)

def stage2LowCapOccurs5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) : Prop :=
  ∃ ℓ : X.Key, X.KeyOccurs ℓ ∧
    ∃ t : CubeVertex (X.p.m n),
      signShiftKey5 X t ℓ = .inl (q, default, j)

noncomputable instance stage2LowCapOccursDecidable5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) : Decidable (stage2LowCapOccurs5 X q j) :=
  Classical.propDecidable _

abbrev Stage2LowCapData5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {j : Fin (X.p.J n + 1) // stage2LowCapOccurs5 X q j}

noncomputable instance stage2LowCapDataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2LowCapData5 X q) := by
  classical
  infer_instance

theorem stage2LowCapData_card_le5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    Fintype.card (Stage2LowCapData5 X q) ≤ X.p.J n + 1 := by
  classical
  calc
    Fintype.card (Stage2LowCapData5 X q) ≤ Fintype.card (Fin (X.p.J n + 1)) :=
      Fintype.card_le_of_injective (fun j : Stage2LowCapData5 X q => j.1) (by
        intro a b h
        exact Subtype.ext h)
    _ = X.p.J n + 1 := Fintype.card_fin _

abbrev Stage2HighOptPatternAt5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {p : Stage2HighPatternAt5 X q // ∃ t, X.OptOccurs p.1 t}

noncomputable instance stage2HighOptPatternAtFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighOptPatternAt5 X q) := by
  classical
  infer_instance

theorem stage2HighOptPatternAt_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    Fintype.card (Stage2HighOptPatternAt5 X q) ≤ (highTypeCandidates5 X q).card := by
  classical
  apply le_trans (Fintype.card_le_of_injective
    (fun p : Stage2HighOptPatternAt5 X q => p.1) (by
      intro a b h
      exact Subtype.ext h))
  exact stage2HighPatternAt_card_le5 X q

abbrev Stage2HighCapData5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {u : Unit // X.KeyOccurs (.inr q)}

noncomputable instance stage2HighCapDataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighCapData5 X q) := by
  classical
  infer_instance

theorem stage2HighCapData_card_le5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    Fintype.card (Stage2HighCapData5 X q) ≤ 1 := by
  classical
  calc
    Fintype.card (Stage2HighCapData5 X q) ≤ Fintype.card Unit :=
      Fintype.card_le_of_injective (fun u : Stage2HighCapData5 X q => u.1) (by
        intro a b h
        exact Subtype.ext h)
    _ = 1 := Fintype.card_unit

set_option maxHeartbeats 2000000 in
inductive Stage2GroupAlarm5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) where
  | lowStep1 (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j)
      (ℓ : {ℓ : X.Key // ℓ ∈ X.gateKeys p.1})
  | highStep1 (p : Stage2HighPatternAt5 X q)
      (ℓ : {ℓ : X.Key // ℓ ∈ X.gateKeys p.1})
  | lowCap (j : Fin (X.p.J n + 1)) (h : stage2LowCapOccurs5 X q j)
  | highCap (h : X.KeyOccurs (.inr q))
  | lowStep2 (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j)
  | highStep2 (p : Stage2HighPatternAt5 X q)
  | highOptional (p : Stage2HighOptPatternAt5 X q)

abbrev Stage2LowStep2Data5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  Σ j : Fin (X.p.J n + 1), Stage2LowPatternAt5 X q j

abbrev Stage2GroupAlarmFlat5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  (Σ j : Fin (X.p.J n + 1), Stage2LowStep1Data5 X q j) ⊕
    (Stage2HighStep1Data5 X q ⊕
      (Stage2LowCapData5 X q ⊕
        (Stage2HighCapData5 X q ⊕
          (Stage2LowStep2Data5 X q ⊕
            (Stage2HighPatternAt5 X q ⊕ Stage2HighOptPatternAt5 X q)))))

noncomputable instance stage2GroupAlarmFlatFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2GroupAlarmFlat5 X q) := by
  classical
  infer_instance

noncomputable def stage2GroupAlarmEquiv5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Stage2GroupAlarm5 X q ≃ Stage2GroupAlarmFlat5 X q where
  toFun := fun i => match i with
    | .lowStep1 j p ℓ => Sum.inl ⟨j, ⟨p, ℓ⟩⟩
    | .highStep1 p ℓ => Sum.inr (Sum.inl ⟨p, ℓ⟩)
    | .lowCap j h => Sum.inr (Sum.inr (Sum.inl ⟨j, h⟩))
    | .highCap h => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(), h⟩)))
    | .lowStep2 j p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩))))
    | .highStep2 p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))
    | .highOptional p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))))
  invFun := fun a => match a with
    | Sum.inl ⟨j, ⟨p, ℓ⟩⟩ => .lowStep1 j p ℓ
    | Sum.inr (Sum.inl ⟨p, ℓ⟩) => .highStep1 p ℓ
    | Sum.inr (Sum.inr (Sum.inl ⟨j, h⟩)) => .lowCap j h
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨u, h⟩))) => .highCap h
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))) => .lowStep2 j p
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) => .highStep2 p
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) => .highOptional p
  left_inv := by intro i; cases i <;> rfl
  right_inv := by
    intro a
    cases a with
    | inl a => cases a with | mk j d => cases d with | mk p ℓ => rfl
    | inr r =>
      cases r with
      | inl d => cases d with | mk p ℓ => rfl
      | inr r =>
        cases r with
        | inl d => cases d with | mk j h => rfl
        | inr r =>
          cases r with
          | inl d => cases d with | mk u h => rfl
          | inr r =>
          cases r with
          | inl d => cases d with | mk j p => rfl
          | inr r =>
            cases r with
            | inl p => rfl
            | inr p => rfl

noncomputable instance stage2GroupAlarmFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2GroupAlarm5 X q) := by
  classical
  exact Fintype.ofEquiv (Stage2GroupAlarmFlat5 X q) (stage2GroupAlarmEquiv5 X q).symm

noncomputable def stage2GroupAlarmBad5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) (c : X.Coarse) : Prop :=
  match i with
  | .lowStep1 _ p ℓ =>
      X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
  | .highStep1 p ℓ =>
      X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
  | .lowCap j _ => X.capFail (v, c) (.inl (q, default, j))
  | .highCap _ => X.capFail (v, c) (.inr q)
  | .lowStep2 _ p =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)
  | .highStep2 p =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)
  | .highOptional p =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U =>
          X.optFail ((v, c), U) p.1.1 (default : CubeVertex (X.p.m n)))

noncomputable def stage2GroupAlarmScope5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) : Finset (BinVector5 n) :=
  match i with
  | .lowStep1 _ _ ℓ => binList5 ℓ.1.coarse
  | .highStep1 _ ℓ => binList5 ℓ.1.coarse
  | .lowCap _ _ => binList5 q
  | .highCap _ => binList5 q
  | .lowStep2 _ p => blockLocalBins5 X p.1 p.1.2.1
  | .highStep2 p => blockLocalBins5 X p.1 p.1.2.1
  | .highOptional p =>
      blockLocalBins5 X p.1.1 (insert (X.optKeyOf p.1.1 default) p.1.1.2.1)

noncomputable def stage2GroupAlarmBudget5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) : ℝ :=
  match i with
  | .lowStep1 _ p _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | .highStep1 p _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | .lowCap j _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (j.val + 1))) / 2)
  | .highCap _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (X.p.J n + 1))) / 2)
  | .lowStep2 _ p =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | .highStep2 p =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | .highOptional _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)

noncomputable def stage2GroupAlarmFlatBudget5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (a : Stage2GroupAlarmFlat5 X q) : ℝ :=
  match a with
  | Sum.inl ⟨j, ⟨p, ℓ⟩⟩ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | Sum.inr (Sum.inl ⟨p, ℓ⟩) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | Sum.inr (Sum.inr (Sum.inl ⟨j, h⟩)) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (j.val + 1))) / 2)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨u, h⟩))) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (X.p.J n + 1))) / 2)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))) =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)

theorem stage2GroupAlarmBudget_sum_eq_flat5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    (∑ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBudget5 X q i) =
      ∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a := by
  calc
    (∑ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBudget5 X q i) =
        ∑ i : Stage2GroupAlarm5 X q,
          stage2GroupAlarmFlatBudget5 X q (stage2GroupAlarmEquiv5 X q i) := by
            apply Finset.sum_congr rfl
            intro i hi
            cases i <;> rfl
    _ = ∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a :=
      Equiv.sum_comp (stage2GroupAlarmEquiv5 X q) _

noncomputable def stage2GroupBudgetParam5 (p : Params5 γ K' χ) (n D : ℕ) : ℝ :=
  (∑ j : Fin (p.J n + 1),
    (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val * (lowKeysBase5 + j.val) : ℕ) : ℝ) *
      Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2) +
    ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val * (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
      Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4))) +
  ((p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (p.m n : ℝ)) +
  ((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) +
  ((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) +
  (stage2TypeCountBase5 : ℝ) * Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) +
  Real.exp (-20 * Real.log (p.m n : ℝ))

noncomputable def stage2GroupBudgetBound5 (X : Setup5 γ K' χ n N E G) (D : ℕ) : ℝ :=
  stage2GroupBudgetParam5 X.p n D

noncomputable def stage2GroupBudgetVanishing5 {γ K' χ : ℝ}
    (p : Params5 γ K' χ) (n : ℕ) : ℝ :=
  8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
      Real.exp (-5 * Real.log (p.m n : ℝ)) +
    3 * Real.exp (-19 * Real.log (p.m n : ℝ)) +
    (((stage2TypeCountBase5 * (2 * (stage2CoarseCountBase5) + 3) : ℕ) : ℝ) *
      Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ)))

theorem stage2GroupAlarmFlatBudget_decomp5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    (∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a) =
      (∑ j : Fin (X.p.J n + 1),
        ∑ a : Stage2LowStep1Data5 X q j,
          stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) +
      (∑ a : Stage2HighStep1Data5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inl a))) +
      (∑ a : Stage2LowCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inl a)))) +
      (∑ a : Stage2HighCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))) +
      (∑ j : Fin (X.p.J n + 1),
        ∑ p : Stage2LowPatternAt5 X q j,
          stage2GroupAlarmFlatBudget5 X q
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) +
      (∑ p : Stage2HighPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))) +
      ∑ p : Stage2HighOptPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))))) := by
  classical
  simp only [Stage2GroupAlarmFlat5, Fintype.sum_sum_type, Fintype.sum_sigma, add_assoc]

theorem stage2GroupAlarmFlatBudget_sum_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (hm : 1 ≤ X.p.m n) (hJ : X.p.J n ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1) :
    (∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a) ≤
      stage2GroupBudgetBound5 X (stage2CoarseCountBase5) := by
  classical
  let D0 : ℕ := stage2CoarseCountBase5
  have hD0 : (nearCoarseKeys5 q.1).card ≤ D0 := by
    simpa [D0] using nearCoarseKeys5_card_le_stage2Base5 q.1
  let D : ℕ := D0
  have hD : (nearCoarseKeys5 q.1).card ≤ D := by simpa [D] using hD0
  have hmPos : 0 < X.p.m n := by omega
  have hCandidate (j : Fin (X.p.J n + 1)) :
      (lowTypeCandidates5 X q default j).card ≤
        stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val := by
    have hjJ : j.val ≤ X.p.J n := Nat.le_of_lt_succ j.isLt
    have hjm : j.val ≤ X.p.m n := le_trans hjJ hJ
    simpa only [stage2TypeCountBase5, D0] using
      lowTypeCandidates_card5 X q default j hjm hmPos D0 hD0
  have hS1const (j : Fin (X.p.J n + 1)) (a : Stage2LowStep1Data5 X q j) :
      stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩) =
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2) := by
    rcases a with ⟨p, ℓ⟩
    simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
  have hS1j (j : Fin (X.p.J n + 1)) :
      (∑ a : Stage2LowStep1Data5 X q j,
        stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) ≤
      (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2)) := by
    have hsum : (∑ a : Stage2LowStep1Data5 X q j,
        stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) =
        (Fintype.card (Stage2LowStep1Data5 X q j) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2) := by
      simp [hS1const]
    rw [hsum]
    apply mul_le_mul_of_nonneg_right
    · have hcard := stage2LowStep1Data_card_le5 X q j
      have hcount : Fintype.card (Stage2LowStep1Data5 X q j) ≤
          stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
            (lowKeysBase5 + j.val) := by
        calc
          Fintype.card (Stage2LowStep1Data5 X q j) ≤
              (lowTypeCandidates5 X q default j).card * (lowKeysBase5 + j.val) := hcard
          _ ≤ (stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val) *
                (lowKeysBase5 + j.val) := Nat.mul_le_mul_right _ (hCandidate j)
      exact_mod_cast hcount
    · exact (Real.exp_pos _).le
  have hS1all :
      (∑ j : Fin (X.p.J n + 1),
        ∑ a : Stage2LowStep1Data5 X q j,
          stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) ≤
      ∑ j : Fin (X.p.J n + 1),
        (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2)) := by
    exact Finset.sum_le_sum fun j hj => hS1j j
  have hS2j (j : Fin (X.p.J n + 1)) :
      (∑ p : Stage2LowPatternAt5 X q j,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) ≤
      (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by
    have hterm (p : Stage2LowPatternAt5 X q j) :
        stage2GroupAlarmFlatBudget5 X q
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩))))) ≤
          ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4) := by
      have hkeys := stage2LowPatternAt_keys_card_le5 X q j p
      have hkeys' : (p.1.2.1.card : ℝ) + 1 ≤
          ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hkeys 1
      have hbudget : stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩))))) =
          ((p.1.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4) := by
        simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
      rw [hbudget]
      exact mul_le_mul_of_nonneg_right hkeys' (Real.exp_pos _).le
    have hsum : (∑ p : Stage2LowPatternAt5 X q j,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) ≤
        (Fintype.card (Stage2LowPatternAt5 X q j) : ℝ) *
          (((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by
      calc
        _ ≤ ∑ _p : Stage2LowPatternAt5 X q j,
              ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
                Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4) :=
          Finset.sum_le_sum fun p hp => hterm p
        _ = _ := by simp
    calc
      _ ≤ (Fintype.card (Stage2LowPatternAt5 X q j) : ℝ) *
            (((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := hsum
      _ ≤ ((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val : ℕ) : ℝ) *
            (((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast (stage2LowPatternAt_card_le5 X q j).trans (hCandidate j)
          · exact mul_nonneg (by positivity) (Real.exp_pos _).le
      _ = (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
            (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by push_cast; ring
  have hS2all :
      (∑ j : Fin (X.p.J n + 1),
        ∑ p : Stage2LowPatternAt5 X q j,
          stage2GroupAlarmFlatBudget5 X q
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) ≤
      ∑ j : Fin (X.p.J n + 1),
        (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) :=
    Finset.sum_le_sum fun j hj => hS2j j
  have hcapTerm (a : Stage2LowCapData5 X q) :
      stage2GroupAlarmFlatBudget5 X q
        (Sum.inr (Sum.inr (Sum.inl a))) ≤ Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    simpa [stage2GroupAlarmFlatBudget5] using
      capBudget_le_mpow_h23 X.p n a.1.val hm hK1
  have hcap :
      (∑ a : Stage2LowCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inl a)))) ≤
        ((X.p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    calc
      _ ≤ (Fintype.card (Stage2LowCapData5 X q) : ℝ) *
          Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
        calc
          _ ≤ ∑ _a : Stage2LowCapData5 X q, Real.exp (-20 * Real.log (X.p.m n : ℝ)) :=
            Finset.sum_le_sum fun a ha => hcapTerm a
          _ = _ := by simp
      _ ≤ ((X.p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (X.p.m n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast stage2LowCapData_card_le5 X q)
          (Real.exp_pos _).le
  have hhigh1const (a : Stage2HighStep1Data5 X q) :
      stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inl a)) =
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2) := by
    rcases a with ⟨p, ℓ⟩
    simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
  have hhigh1 :
      (∑ a : Stage2HighStep1Data5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inl a))) ≤
        (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)) := by
    calc
      _ = (Fintype.card (Stage2HighStep1Data5 X q) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2) := by simp [hhigh1const]
      _ ≤ (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)) := by
        apply mul_le_mul_of_nonneg_right
        · have hc : Fintype.card (Stage2HighStep1Data5 X q) ≤
              stage2TypeCountBase5 * (D + 1) := by
            simpa only [stage2TypeCountBase5, D, D0] using stage2HighStep1Data_card_le5 X q D hD
          exact_mod_cast hc
        · exact (Real.exp_pos _).le
  have hhighKeys (p : Stage2HighPatternAt5 X q) : p.1.2.1.card ≤ D :=
    (highTypeCandidates_keys_card_le5 X q p.1 p.2.1).trans hD
  have hhigh2term (p : Stage2HighPatternAt5 X q) :
      stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))) ≤
        ((D + 1 : ℕ) : ℝ) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
    have hplus : (p.1.2.1.card : ℝ) + 1 ≤ ((D + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (hhighKeys p) 1
    have hbud : stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))) =
        ((p.1.2.1.card : ℝ) + 1) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
      simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
    rw [hbud]
    exact mul_le_mul_of_nonneg_right hplus (Real.exp_pos _).le
  have hhigh2 :
      (∑ p : Stage2HighPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))) ≤
        (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by
    calc
      _ ≤ ∑ _p : Stage2HighPatternAt5 X q,
          ((D + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) :=
        Finset.sum_le_sum fun p hp => hhigh2term p
      _ = (Fintype.card (Stage2HighPatternAt5 X q) : ℝ) *
          (((D + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by simp
      _ ≤ (((stage2TypeCountBase5 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by
        have hc : Fintype.card (Stage2HighPatternAt5 X q) ≤ stage2TypeCountBase5 := by
          calc
            Fintype.card (Stage2HighPatternAt5 X q) ≤ (highTypeCandidates5 X q).card :=
              stage2HighPatternAt_card_le5 X q
            _ ≤ stage2TypeCountBase5 := by
              simpa only [stage2TypeCountBase5, D] using highTypeCandidates_card5 X q D hD
        have hcR : (Fintype.card (Stage2HighPatternAt5 X q) : ℝ) ≤
            (stage2TypeCountBase5 : ℝ) := by exact_mod_cast hc
        have h := mul_le_mul_of_nonneg_right hcR
          (mul_nonneg (Nat.cast_nonneg (D + 1))
            (Real.exp_pos (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)).le)
        simpa only [mul_assoc] using h
      _ = (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by push_cast; ring
  have hhighOpt :
      (∑ p : Stage2HighOptPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))))) ≤
        (stage2TypeCountBase5 : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
    calc
      _ = (Fintype.card (Stage2HighOptPatternAt5 X q) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by simp [stage2GroupAlarmFlatBudget5]
      _ ≤ (stage2TypeCountBase5 : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (stage2HighOptPatternAt_card_le5 X q).trans (by
            calc
              (highTypeCandidates5 X q).card ≤ 2 ^ D := highTypeCandidates_card5 X q D hD
              _ = stage2TypeCountBase5 := by simp only [stage2TypeCountBase5, D, D0])
        · exact (Real.exp_pos _).le
  have hhighCapTerm (a : Stage2HighCapData5 X q) :
      stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) ≤
        Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    simpa [stage2GroupAlarmFlatBudget5] using
      capBudget_le_mpow_h23 X.p n (X.p.J n) hm hK1
  have hhighCap :
      (∑ a : Stage2HighCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) ) ≤
        Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    calc
      _ ≤ ∑ _a : Stage2HighCapData5 X q, Real.exp (-20 * Real.log (X.p.m n : ℝ)) :=
        Finset.sum_le_sum fun a ha => hhighCapTerm a
      _ = (Fintype.card (Stage2HighCapData5 X q) : ℝ) *
          Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by simp
      _ ≤ 1 * Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast stage2HighCapData_card_le5 X q)
          (Real.exp_pos _).le
      _ = Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by ring
  have hcapAll :
      (∑ a : Stage2LowCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inl a)))) +
      (∑ a : Stage2HighCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))) ≤
      ((X.p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (X.p.m n : ℝ)) +
        Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    exact add_le_add hcap hhighCap
  rw [stage2GroupAlarmFlatBudget_decomp5]
  dsimp only [stage2GroupBudgetBound5, stage2GroupBudgetParam5, D, D0] at *
  simp only [Finset.sum_add_distrib] at *
  linarith [hS1all, hS2all, hhigh1, hhigh2, hhighOpt, hcapAll]

theorem lowPatternPolyBound5 (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ m) :
    ((j : ℝ) + 1) * ((lowKeysBase5 : ℝ) + j + 1) ≤
      2 * ((lowKeysBase5 : ℝ) + 2) * (m : ℝ) ^ 2 := by
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hjR : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
  have hL : 0 ≤ (lowKeysBase5 : ℝ) := Nat.cast_nonneg _
  have hLprod : 0 ≤ (lowKeysBase5 : ℝ) * ((m : ℝ) - 1) :=
    mul_nonneg hL (by linarith)
  have hA : (j : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
  have hB : (lowKeysBase5 : ℝ) + j + 1 ≤
      ((lowKeysBase5 : ℝ) + 2) * (m : ℝ) := by nlinarith [hLprod]
  calc
    _ ≤ (2 * (m : ℝ)) * (((lowKeysBase5 : ℝ) + 2) * (m : ℝ)) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := by ring

theorem stage2GroupBudgetBound_le_vanishing5 (X : Setup5 γ K' χ n N E G)
    (hm : 1 ≤ X.p.m n) (hJ : X.p.J n ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1) :
    stage2GroupBudgetBound5 X (stage2CoarseCountBase5) ≤
      stage2GroupBudgetVanishing5 X.p n := by
  classical
  let p := X.p
  change 1 ≤ p.m n at hm
  change p.J n ≤ p.m n at hJ
  change 8 / p.delta ≤ p.K1 at hK1
  let m : ℝ := p.m n
  let L : ℝ := Real.log m
  have hmPos : 0 < m := by
    dsimp [m, p]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hlog : 0 ≤ L := by dsimp [L, m]; exact Real.log_nonneg (by exact_mod_cast hm)
  have hscale6 : m * Real.exp (-6 * L) = Real.exp (-5 * L) := by
    dsimp [m, L]
    simpa only [pow_one, Nat.cast_one, show (1 : ℝ) - 6 = -5 by norm_num] using
      natPow_exp_cancel_h23 p n 1 6 hm
  have hscale20 : m * Real.exp (-20 * L) = Real.exp (-19 * L) := by
    dsimp [m, L]
    simpa only [pow_one, Nat.cast_one, show (1 : ℝ) - 20 = -19 by norm_num] using
      natPow_exp_cancel_h23 p n 1 20 hm
  have hscale2 : (p.m n : ℝ) ^ 2 * Real.exp (-8 * L) = Real.exp (-6 * L) := by
    simpa only [Nat.cast_ofNat, show (2 : ℝ) - 8 = -6 by norm_num] using
      natPow_exp_cancel_h23 p n 2 8 hm
  have hlowPer (j : Fin (p.J n + 1)) :
      (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2)) +
      (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4)) ≤
      4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
        Real.exp (-6 * L) := by
    have hjJ : j.val ≤ p.J n := Nat.le_of_lt_succ j.isLt
    have hjm : j.val ≤ p.m n := le_trans hjJ hJ
    have hpoly := lowPatternPolyBound5 (p.m n) j.val (by omega) hjm
    have hdecay := natPow_mul_exp_decay5 p n j.val hm
    have hExp1 := lowAlarmExpStep1_le5 p n j.val hm hK1
    have hExp2 := lowAlarmExp_le5 p n j.val hm hK1
    have hcoeff1 :
        ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) ≤
        ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left
        (stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val) (Nat.le_succ _)
    have hpolyExp :
        ((j.val + 1 : ℕ) : ℝ) *
          ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
          (((p.m n) ^ j.val : ℕ) : ℝ) *
          Real.exp (-2 * ((j.val : ℝ) + 4) * L) ≤
        2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2 *
          Real.exp (-8 * L) := by
      calc
        _ = (((j.val + 1 : ℕ) : ℝ) *
              ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ)) *
              ((((p.m n) ^ j.val : ℕ) : ℝ) *
                Real.exp (-2 * ((j.val : ℝ) + 4) * L)) := by ring
        _ ≤ (2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2) *
              Real.exp (-8 * L) := by
          simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Nat.cast_pow, L, m] using
            mul_le_mul (lowPatternPolyBound5 (p.m n) j.val (by omega) hjm)
              hdecay (by positivity) (by positivity)
    have hterm1 :
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2)) ≤
        2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-6 * L) := by
      calc
        _ ≤ (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
            (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
            Real.exp (-2 * ((j.val : ℝ) + 4) * L)) :=
              mul_le_mul hcoeff1 hExp1 (by positivity) (by positivity)
        _ ≤ (stage2TypeCountBase5 : ℝ) *
              (2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2) *
              Real.exp (-8 * L) := by
          have h := mul_le_mul_of_nonneg_left hpolyExp (Nat.cast_nonneg stage2TypeCountBase5)
          convert h using 1 <;> push_cast <;> ring
        _ = 2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              Real.exp (-6 * L) := by
          rw [← hscale2]
          ring
    have hterm2 :
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4)) ≤
        2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-6 * L) := by
      calc
        _ ≤ (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
            (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
            Real.exp (-2 * ((j.val : ℝ) + 4) * L)) :=
              mul_le_mul_of_nonneg_left hExp2 (by positivity)
        _ ≤ (stage2TypeCountBase5 : ℝ) *
              (2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2) *
              Real.exp (-8 * L) := by
          have h := mul_le_mul_of_nonneg_left hpolyExp (Nat.cast_nonneg stage2TypeCountBase5)
          convert h using 1 <;> push_cast <;> ring
        _ = 2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              Real.exp (-6 * L) := by
          rw [← hscale2]
          ring
    linarith
  have hlowSum :
      (∑ j : Fin (p.J n + 1),
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2) +
        ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4))) ≤
      8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
        Real.exp (-5 * L) := by
    calc
      _ ≤ ∑ _j : Fin (p.J n + 1),
          4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
            Real.exp (-6 * L) := Finset.sum_le_sum fun j hj => hlowPer j
      _ = ((p.J n + 1 : ℕ) : ℝ) *
          (4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
            Real.exp (-6 * L)) := by simp
      _ ≤ (2 * (p.m n : ℝ)) *
          (4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
            Real.exp (-6 * L)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hNat : p.J n + 1 ≤ 2 * p.m n := by omega
        exact_mod_cast hNat
      _ = 8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-5 * L) := by
        calc
          (2 * (p.m n : ℝ)) *
              (4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                Real.exp (-6 * L)) =
            8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              ((p.m n) ^ 1 : ℝ) * Real.exp (-6 * L) := by simp [pow_one]; ring
          _ = 8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              Real.exp (-5 * L) := by
            rw [← hscale6]
            dsimp only [m]
            ring
  have hcapAll : ((p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * L) +
      Real.exp (-20 * L) ≤ 3 * Real.exp (-19 * L) := by
    have hNat : p.J n + 2 ≤ 3 * p.m n := by omega
    have hCast : ((p.J n + 1 : ℕ) : ℝ) + 1 ≤ 3 * (p.m n : ℝ) := by
      exact_mod_cast hNat
    calc
      _ = (((p.J n + 1 : ℕ) : ℝ) + 1) * Real.exp (-20 * L) := by ring
      _ ≤ (3 * (p.m n : ℝ)) * Real.exp (-20 * L) :=
        mul_le_mul_of_nonneg_right hCast (Real.exp_pos _).le
      _ = 3 * Real.exp (-19 * L) := by
        calc
          (3 * (p.m n : ℝ)) * Real.exp (-20 * L) =
              3 * ((p.m n) ^ 1 : ℝ) * Real.exp (-20 * L) := by simp [pow_one]
          _ = 3 * Real.exp (-19 * L) := by
            rw [← hscale20]
            dsimp only [m]
            ring
  have hstar := highAlarmExp_le5 p n
  have hstarHalf :
      Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) ≤
        Real.exp (-(p.delta * p.eta / 4) * L) := by
    have hpos : 0 ≤ p.delta * ((p.q0 : ℝ) * p.uStarSeg n) :=
      mul_nonneg p.hdelta.1.le (by positivity)
    calc
      Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) ≤
          Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hpos]
      _ ≤ Real.exp (-(p.delta * p.eta / 4) * L) := by
            simpa [L, m] using hstar
  have hhigh :
      (((stage2TypeCountBase5 * ((stage2CoarseCountBase5) + 1) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2)) +
      (((stage2TypeCountBase5 * ((stage2CoarseCountBase5) + 1) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4)) +
      (stage2TypeCountBase5 : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) ≤
      (((stage2TypeCountBase5 * (2 * (stage2CoarseCountBase5) + 3) : ℕ) : ℝ) *
        Real.exp (-(p.delta * p.eta / 4) * L)) := by
    have hRate := highAlarmExp_le5 p n
    have hCoef :
        (stage2TypeCountBase5 : ℝ) * (2 * (stage2CoarseCountBase5) + 3 : ℕ) =
          ((stage2TypeCountBase5 * (2 * (stage2CoarseCountBase5) + 3) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [← hCoef]
    have h1 : Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) ≤
        Real.exp (-(p.delta * p.eta / 4) * L) := hstarHalf
    have h2 : Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) ≤
        Real.exp (-(p.delta * p.eta / 4) * L) := by simpa [L, m] using hRate
    have hC : 0 ≤ (stage2TypeCountBase5 : ℝ) *
        (2 * (stage2CoarseCountBase5) + 3 : ℕ) := by positivity
    have hc0 : (0 : ℝ) ≤ stage2TypeCountBase5 := Nat.cast_nonneg _
    have hd0 : (0 : ℝ) ≤ (stage2CoarseCountBase5 : ℕ) := Nat.cast_nonneg _
    push_cast at hC ⊢
    have hm1 := mul_le_mul_of_nonneg_left h1
      (mul_nonneg hc0 (by positivity : (0 : ℝ) ≤ (stage2CoarseCountBase5 : ℝ) + 1))
    have hm2 := mul_le_mul_of_nonneg_left h2
      (mul_nonneg hc0 (by positivity : (0 : ℝ) ≤ (stage2CoarseCountBase5 : ℝ) + 1))
    have hm3 := mul_le_mul_of_nonneg_left h2 hc0
    nlinarith [hm1, hm2, hm3]
  have hparam : stage2GroupBudgetParam5 p n (stage2CoarseCountBase5) ≤
      8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-5 * Real.log (p.m n : ℝ)) +
        3 * Real.exp (-19 * Real.log (p.m n : ℝ)) +
        (((stage2TypeCountBase5 * (2 * (stage2CoarseCountBase5) + 3) : ℕ) : ℝ) *
          Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ))) := by
    unfold stage2GroupBudgetParam5
    dsimp [p, L, m] at hlowSum hcapAll hhigh ⊢
    nlinarith [hlowSum, hcapAll, hhigh]
  calc
    stage2GroupBudgetBound5 X (stage2CoarseCountBase5) =
        stage2GroupBudgetParam5 p n (stage2CoarseCountBase5) := rfl
    _ ≤ 8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-5 * Real.log (p.m n : ℝ)) +
        3 * Real.exp (-19 * Real.log (p.m n : ℝ)) +
        (((stage2TypeCountBase5 * (2 * (stage2CoarseCountBase5) + 3) : ℕ) : ℝ) *
          Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ))) := hparam
    _ = stage2GroupBudgetVanishing5 p n := by rfl

theorem stage2GroupAlarmBad_ext5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) (c c' : X.Coarse)
    (h : ∀ w ∈ stage2GroupAlarmScope5 X q i,
      c.1 w = c'.1 w ∧ c.2 w = c'.2 w) :
    stage2GroupAlarmBad5 X v q i c ↔ stage2GroupAlarmBad5 X v q i c' := by
  cases i with
  | lowStep1 j p ℓ =>
      have hp : ∀ w ∈ binList5 ℓ.1.coarse, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 ℓ.1.coarse, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1) ↔
        X.step1Fail (v, c') ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
      exact step1Fail_ext_bins5 X (v, c) (v, c') ℓ.1 p.1.1.1
        (X.p.typeSegs n p.1) rfl hp hW
  | highStep1 p ℓ =>
      have hp : ∀ w ∈ binList5 ℓ.1.coarse, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 ℓ.1.coarse, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1) ↔
        X.step1Fail (v, c') ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
      exact step1Fail_ext_bins5 X (v, c) (v, c') ℓ.1 p.1.1.1
        (X.p.typeSegs n p.1) rfl hp hW
  | lowCap j hKey =>
      have hp : ∀ w ∈ binList5 q, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 q, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.capFail (v, c) (.inl (q, default, j)) ↔
        X.capFail (v, c') (.inl (q, default, j))
      exact capFail_ext_bins5 X (v, c) (v, c') (.inl (q, default, j)) rfl hp hW
  | highCap hKey =>
      have hp : ∀ w ∈ binList5 q, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 q, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.capFail (v, c) (.inr q) ↔ X.capFail (v, c') (.inr q)
      exact capFail_ext_bins5 X (v, c) (v, c') (.inr q) rfl hp hW
  | lowStep2 j p =>
      have hp : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.1 w = c'.1 w :=
        fun w hw => (h w hw).1
      have hW : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.2 w = c'.2 w :=
        fun w hw => (h w hw).2
      have hprob := step2FailPr_ext_bins5 X (v, c) (v, c') p.1 rfl hp hW
      change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) ↔
        (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c')).pr (fun U => X.step2Fail ((v, c'), U) p.1))
      rw [hprob]
  | highStep2 p =>
      have hp : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.1 w = c'.1 w :=
        fun w hw => (h w hw).1
      have hW : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.2 w = c'.2 w :=
        fun w hw => (h w hw).2
      have hprob := step2FailPr_ext_bins5 X (v, c) (v, c') p.1 rfl hp hW
      change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) ↔
        (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c')).pr (fun U => X.step2Fail ((v, c'), U) p.1))
      rw [hprob]
  | highOptional p =>
      have hp : ∀ w ∈ blockLocalBins5 X p.1.1 (insert (X.optKeyOf p.1.1 default) p.1.1.2.1),
          c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ blockLocalBins5 X p.1.1 (insert (X.optKeyOf p.1.1 default) p.1.1.2.1),
          c.2 w = c'.2 w := fun w hw => (h w hw).2
      have hprob := optFailPr_ext_bins5 X (v, c) (v, c') p.1.1 default rfl hp hW
      change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) p.1.1 default)) ↔
        (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
          (X.hiddenLaw (v, c')).pr (fun U => X.optFail ((v, c'), U) p.1.1 default))
      rw [hprob]

noncomputable def stage2GroupBad5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (c : X.Coarse) : Prop :=
  ∃ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBad5 X v q i c

noncomputable def stage2GroupBadOnPairs5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (ω : BinVector5 n → Fin N × X.Stream) : Prop :=
  stage2GroupBad5 X v q (coarsePairEquiv5 X ω)

theorem stage2LowPatternAt_of_role5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (heven : IsEvenRole x) (hlow : X.g.severity x ≤ X.p.J n) :
    ∃ j : Fin (X.p.J n + 1), ∃ p : Stage2LowPatternAt5 X (X.g.key x) j,
      p.1 = signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x) := by
  classical
  obtain ⟨p, hq, hj, hK⟩ := stage2LowPattern_exists5 X x heven hlow
  let j := p.2.1
  let pAt : Stage2LowPatternAt5 X (X.g.key x) j := by
    refine ⟨p.2.2.1, ?_⟩
    simpa [j, hq] using p.2.2.2
  refine ⟨j, pAt, ?_⟩
  simpa [pAt] using hK

theorem stage2HighPatternAt_of_role5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (heven : IsEvenRole x) (hhigh : ¬ X.g.severity x ≤ X.p.J n) :
    ∃ p : Stage2HighPatternAt5 X (X.g.key x),
      p.1 = X.g.evenType (X.p.J n) x := by
  classical
  obtain ⟨p, hq, hK⟩ := stage2HighPattern_exists5 X x heven hhigh
  let pAt : Stage2HighPatternAt5 X (X.g.key x) := by
    refine ⟨p.2.1, ?_⟩
    simpa [hq] using p.2.2
  exact ⟨pAt, by simpa [pAt] using hK⟩

theorem hiddenLawPr_hiddenSignShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (A : X.Hidden → Prop) :
    (X.hiddenLaw b).pr (fun U => A (hiddenSignShift5 X t U)) =
      (X.hiddenLaw b).pr A := by
  classical
  let P := X.hiddenLaw b
  have hmap := map_pr_equiv5 P (hiddenSignShift5 X t) A
  rw [hiddenLaw_map_signShift5 X b t] at hmap
  exact hmap.symm

theorem step2FailPr_signShiftLowSimple5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) (signShiftType5 X t K)) =
      (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) := by
  calc
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) (signShiftType5 X t K)) =
      (X.hiddenLaw b).pr (fun U => X.step2Fail (b, hiddenSignShift5 X t U)
        (signShiftType5 X t K)) := by
          symm
          exact hiddenLawPr_hiddenSignShift5 X b t
            (fun U => X.step2Fail (b, U) (signShiftType5 X t K))
    _ = (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) :=
      step2FailPr_signShiftLow5 X b t K hlevel

theorem optFailPr_signShiftHighSimple5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t₀ t : CubeVertex (X.p.m n)) (K : X.Ty) (hnone : K.2.2 = none)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    (X.hiddenLaw b).pr (fun U => X.optFail (b, U) (signShiftType5 X t₀ K)
      (shiftSignVector5 t₀ t)) =
      (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) := by
  calc
    (X.hiddenLaw b).pr (fun U => X.optFail (b, U) (signShiftType5 X t₀ K)
        (shiftSignVector5 t₀ t)) =
      (X.hiddenLaw b).pr (fun U => X.optFail (b, hiddenSignShift5 X t₀ U)
        (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) := by
          symm
          exact hiddenLawPr_hiddenSignShift5 X b t₀
            (fun U => X.optFail (b, U) (signShiftType5 X t₀ K)
              (shiftSignVector5 t₀ t))
    _ = (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) :=
      optFailPr_signShiftHigh5 X b t₀ t K hnone hHigh

theorem stage2GroupGood_conclusions5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (c : X.Coarse) (hgood : ∀ q : CoarseKey5 n, ¬ stage2GroupBad5 X v q c) :
    (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K,
      ¬ X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K)) ∧
    (∀ ℓ, X.KeyOccurs ℓ → ¬ X.capFail (v, c) ℓ) ∧
    (∀ K, X.TypeOccurs K →
      (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
        ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)) ∧
    ∀ K t, X.OptOccurs K t →
      (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) ≤
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
  classical
  have good (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) :
      ¬ stage2GroupAlarmBad5 X v q i c := fun h => hgood q ⟨i, h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK ℓ hℓ
    rcases hK with ⟨x, hx, rfl⟩
    by_cases hlow : X.g.severity x ≤ X.p.J n
    · obtain ⟨j, p, hpK⟩ := stage2LowPatternAt_of_role5 X x hx hlow
      have hlevel : (X.g.evenType (X.p.J n) x).2.2 = some j := by
        have h := p.2.2.2.1
        rw [hpK, signShiftType5_level] at h
        exact h
      have hmem : signShiftKey5 X (X.g.sign x) ℓ ∈ X.gateKeys p.1 := by
        rw [hpK, gateKeys_signShiftLow5 X _ _ hlevel]
        exact Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
      have h := good (X.g.key x) (.lowStep1 j p ⟨_, hmem⟩)
      change ¬ X.step1Fail (v, c) (signShiftKey5 X (X.g.sign x) ℓ)
        p.1.1.1 (X.p.typeSegs n p.1) at h
      rw [hpK] at h
      exact fun hf => h ((step1Fail_signShift5 X (v, c) (X.g.sign x) _ ℓ).mpr hf)
    · obtain ⟨p, hpK⟩ := stage2HighPatternAt_of_role5 X x hx hlow
      have hmem : ℓ ∈ X.gateKeys p.1 := by rw [hpK]; exact hℓ
      have h := good (X.g.key x) (.highStep1 p ⟨ℓ, hmem⟩)
      change ¬ X.step1Fail (v, c) ℓ p.1.1.1 (X.p.typeSegs n p.1) at h
      simpa only [hpK] using h
  · intro ℓ hℓ
    cases ℓ with
    | inl k =>
      rcases k with ⟨q, t, j⟩
      have he : signShiftKey5 X t (.inl (q, t, j)) = .inl (q, default, j) := by
        simp only [signShiftKey5, Equiv.coe_fn_mk, shiftSignVector_self5]
      have ho : stage2LowCapOccurs5 X q j := ⟨_, hℓ, t, he⟩
      have h := good q (.lowCap j ho)
      change ¬ X.capFail (v, c) (.inl (q, default, j)) at h
      rw [← he] at h
      exact fun hf => h ((capFail_signShift5 X (v, c) t (.inl (q, t, j))).mpr hf)
    | inr q => exact good q (.highCap hℓ)
  · intro K hK
    rcases hK with ⟨x, hx, rfl⟩
    have hle : (X.hiddenLaw (v, c)).pr
        (fun U => X.step2Fail ((v, c), U) (X.g.evenType (X.p.J n) x)) ≤
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n (X.g.evenType (X.p.J n) x))) / 4) := by
      by_cases hlow : X.g.severity x ≤ X.p.J n
      · obtain ⟨j, p, hpK⟩ := stage2LowPatternAt_of_role5 X x hx hlow
        have hlevel : (X.g.evenType (X.p.J n) x).2.2 = some j := by
          have h := p.2.2.2.1
          rw [hpK, signShiftType5_level] at h
          exact h
        have h := good (X.g.key x) (.lowStep2 j p)
        change ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) at h
        rw [hpK, signShiftType5_segs,
          step2FailPr_signShiftLowSimple5 X (v, c) (X.g.sign x) _ hlevel] at h
        exact le_of_not_gt h
      · obtain ⟨p, hpK⟩ := stage2HighPatternAt_of_role5 X x hx hlow
        have h := good (X.g.key x) (.highStep2 p)
        change ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) at h
        rw [hpK] at h
        exact le_of_not_gt h
    exact hle.trans (le_mul_of_one_le_left (Real.exp_pos _).le (by
      have h : (0 : ℝ) ≤ (X.g.evenType (X.p.J n) x).2.1.card := Nat.cast_nonneg _
      linarith))
  · intro K t hOpt
    have hwitness := hOpt
    rcases hwitness with ⟨x, hx, hK, hoptional⟩
    have hnone : K.2.2 = none := optOccurs_high5 X K t hOpt
    have hType : X.TypeOccurs K := ⟨x, hx, hK⟩
    have hHigh := typeOccurs_highKeys5 X K hType hnone
    have hhigh : ¬ X.g.severity x ≤ X.p.J n := by
      intro hl
      have h := hnone
      rw [← hK] at h
      simp [ChunkGeometry5.evenType, hl] at h
    obtain ⟨p, hpK⟩ := stage2HighPatternAt_of_role5 X x hx hhigh
    have hpEq : p.1 = K := by rw [hpK]; exact hK
    have ho : ∃ t, X.OptOccurs p.1 t := ⟨t, by rw [hpEq]; exact hOpt⟩
    have h := good (X.g.key x) (.highOptional ⟨p, ho⟩)
    change ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
      (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) p.1 default)) at h
    rw [hpEq] at h
    have hpr : (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K default) =
        (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) := by
      simpa only [shiftSignVector_self5, signShiftType5_eq_of_highKeys X t K hHigh] using
        optFailPr_signShiftHighSimple5 X (v, c) t t K hnone hHigh
    rw [hpr] at h
    exact le_of_not_gt h


def stage2GroupScope5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    Finset (BinVector5 n) :=
  nearBinVectors2_5 q.1

def stage2GroupIndicesTouching5 (X : Setup5 γ K' χ n N E G)
    (B : Finset (BinVector5 n)) : Finset (CoarseKey5 n) :=
  Finset.univ.filter fun q => ¬ Disjoint (stage2GroupScope5 X q) B

theorem stage2GroupIndicesTouching_card_le5 (X : Setup5 γ K' χ n N E G)
    (B : Finset (BinVector5 n)) :
    (stage2GroupIndicesTouching5 X B).card ≤
      B.card * (2 * (3 ^ coarseChunkCount5) ^ 2) := by
  classical
  let F : BinVector5 n → Finset (CoarseKey5 n) := nearCoarseKeys2_5
  have hsubset : stage2GroupIndicesTouching5 X B ⊆ B.biUnion F := by
    intro q hq
    have hnot : ¬ Disjoint (stage2GroupScope5 X q) B :=
      (Finset.mem_filter.mp hq).2
    rw [Finset.disjoint_left] at hnot
    push_neg at hnot
    obtain ⟨w, hwq, hwB⟩ := hnot
    have hcenter : q ∈ nearCoarseKeys2_5 w := by
      exact Finset.mem_product.mpr
        ⟨nearBinVectors2_mem_symm5 q.1 w (by simpa [stage2GroupScope5] using hwq),
          Finset.mem_univ _⟩
    exact Finset.mem_biUnion.mpr ⟨w, hwB, by simpa [F] using hcenter⟩
  calc
    (stage2GroupIndicesTouching5 X B).card ≤ (B.biUnion F).card := Finset.card_le_card hsubset
    _ ≤ ∑ w ∈ B, (F w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ B, 2 * (3 ^ coarseChunkCount5) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      exact nearCoarseKeys2_card_le5 w
    _ = B.card * (2 * (3 ^ coarseChunkCount5) ^ 2) := by simp

def stage2GroupScopeCardBound5 : ℕ := (3 ^ coarseChunkCount5) ^ 2

def stage2GroupTouchPerBin5 : ℕ := 2 * stage2GroupScopeCardBound5

def stage2GroupDegreeBound5 : ℕ := stage2GroupScopeCardBound5 * stage2GroupTouchPerBin5

theorem stage2GroupScope_card_le5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    (stage2GroupScope5 X q).card ≤ stage2GroupScopeCardBound5 := by
  simpa [stage2GroupScope5, stage2GroupScopeCardBound5] using nearBinVectors2_card_le5 q.1

theorem stage2GroupNeighbors_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    (Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q)).card ≤
      stage2GroupDegreeBound5 := by
  classical
  let B := stage2GroupScope5 X q
  have hsubset : Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q) ⊆
      stage2GroupIndicesTouching5 X B := by
    intro q' hq'
    have hAdj := (Finset.mem_filter.mp hq').2
    have htouch : ¬ Disjoint (stage2GroupScope5 X q') B := by
      intro hd
      exact hAdj.2 hd.symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch⟩
  calc
    (Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q)).card ≤
        (stage2GroupIndicesTouching5 X B).card := Finset.card_le_card hsubset
    _ ≤ B.card * stage2GroupTouchPerBin5 := by
      simpa only [B, stage2GroupTouchPerBin5, stage2GroupScopeCardBound5] using stage2GroupIndicesTouching_card_le5 X B
    _ ≤ stage2GroupDegreeBound5 := by
      exact Nat.mul_le_mul_right _ (stage2GroupScope_card_le5 X q)

theorem exp_neg_two_mul_le_one_sub5 (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hden : 0 < 1 + 2 * x := by positivity
  have hExp : 1 + 2 * x ≤ Real.exp (2 * x) := by simpa only [add_comm] using Real.add_one_le_exp (2 * x)
  have hInv : (Real.exp (2 * x))⁻¹ ≤ (1 + 2 * x)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hden hExp
  have hpoly : 1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
  have hfrac : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    rw [← one_div]
    exact (div_le_iff₀ hden).2 hpoly
  calc
    Real.exp (-2 * x) = (Real.exp (2 * x))⁻¹ := by
      simpa only [neg_mul] using Real.exp_neg (2 * x)
    _ ≤ (1 + 2 * x)⁻¹ := hInv
    _ ≤ 1 - x := hfrac

theorem stage2GroupFactor_le5 (X : Setup5 γ K' χ n N E G)
    (B : Finset (BinVector5 n)) (b : ℝ) (hb0 : 0 ≤ b)
    (hbsmall : 2 * b ≤ Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ))) :
    (∏ q ∈ Finset.univ.filter (fun q : CoarseKey5 n =>
      ¬ Disjoint (stage2GroupScope5 X q) B), (1 - 2 * b))⁻¹ ≤ (2 : ℝ) ^ B.card := by
  classical
  let S := Finset.univ.filter (fun q : CoarseKey5 n =>
    ¬ Disjoint (stage2GroupScope5 X q) B)
  let x := 2 * b
  have hCpos : 0 < (stage2GroupTouchPerBin5 : ℝ) := by
    dsimp [stage2GroupTouchPerBin5, stage2GroupScopeCardBound5]
    positivity
  have hCge : (2 : ℝ) ≤ (stage2GroupTouchPerBin5 : ℝ) := by
    have hn : 1 ≤ stage2GroupScopeCardBound5 := by
      unfold stage2GroupScopeCardBound5
      exact Nat.one_le_pow _ _ (by positivity)
    have hR : (1 : ℝ) ≤ stage2GroupScopeCardBound5 := by exact_mod_cast hn
    change 2 ≤ ((2 * stage2GroupScopeCardBound5 : ℕ) : ℝ)
    push_cast
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hmaxhalf : Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (stage2GroupTouchPerBin5 : ℝ))).2
    nlinarith [hlog2le, hCge]
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    linarith [hbsmall, hmaxhalf]
  have htouch : S.card ≤ B.card * stage2GroupTouchPerBin5 := by
    simpa only [S, stage2GroupIndicesTouching5, stage2GroupTouchPerBin5,
      stage2GroupScopeCardBound5] using stage2GroupIndicesTouching_card_le5 X B
  have htouchR : (S.card : ℝ) ≤ (B.card * stage2GroupTouchPerBin5 : ℕ) := by
    exact_mod_cast htouch
  have hlogbound : 2 * x ≤ Real.log 2 / (stage2GroupTouchPerBin5 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hbsmall (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [x] at hmul ⊢
    calc
      2 * (2 * b) ≤ 2 * (Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ))) := hmul
      _ = Real.log 2 / (stage2GroupTouchPerBin5 : ℝ) := by
        field_simp [ne_of_gt hCpos]
  have hsumx : 2 * x * (S.card : ℝ) ≤ Real.log 2 * (B.card : ℝ) := by
    have hfirst := mul_le_mul_of_nonneg_right hlogbound (Nat.cast_nonneg S.card)
    have hsecond := mul_le_mul_of_nonneg_left htouchR
      (div_nonneg hlog2.le hCpos.le)
    calc
      2 * x * (S.card : ℝ) ≤
          (Real.log 2 / (stage2GroupTouchPerBin5 : ℝ)) * (S.card : ℝ) := hfirst
      _ ≤ (Real.log 2 / (stage2GroupTouchPerBin5 : ℝ)) *
            (B.card * stage2GroupTouchPerBin5 : ℕ) := hsecond
      _ = Real.log 2 * (B.card : ℝ) := by
        push_cast
        field_simp [ne_of_gt hCpos]
        <;> ring
  have hsingle : Real.exp (-2 * x) ≤ 1 - x := exp_neg_two_mul_le_one_sub5 x hx0 hxhalf
  have hpow : (Real.exp (-2 * x)) ^ S.card ≤ (1 - x) ^ S.card :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hsingle _
  have hexpPow : (Real.exp (-2 * x)) ^ S.card =
      Real.exp (-2 * x * (S.card : ℝ)) := by
    calc
      (Real.exp (-2 * x)) ^ S.card = (Real.exp (-2 * x)) ^ (S.card : ℝ) := by
        rw [Real.rpow_natCast]
      _ = Real.exp ((-2 * x) * (S.card : ℝ)) := (Real.exp_mul _ _).symm
  have hprod : Real.exp (-2 * x * (S.card : ℝ)) ≤
      ∏ q ∈ S, (1 - 2 * b) := by
    calc
      Real.exp (-2 * x * (S.card : ℝ)) = (Real.exp (-2 * x)) ^ S.card := hexpPow.symm
      _ ≤ (1 - x) ^ S.card := hpow
      _ = ∏ q ∈ S, (1 - 2 * b) := by simp [S, x]
  have hExpPow : Real.exp (-Real.log 2 * (B.card : ℝ)) =
      1 / (2 : ℝ) ^ B.card := by
    calc
      Real.exp (-Real.log 2 * (B.card : ℝ)) =
          Real.exp ((B.card : ℝ) * (-Real.log 2)) := by congr 1; ring
      _ = (Real.exp (-Real.log 2)) ^ B.card := by
        simpa only [Real.rpow_natCast, mul_comm] using (Real.exp_mul (-Real.log 2) (B.card : ℝ))
      _ = 1 / (2 : ℝ) ^ B.card := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        simp [one_div, inv_pow]
  have hProdLower : 1 / (2 : ℝ) ^ B.card ≤ ∏ q ∈ S, (1 - 2 * b) := by
    calc
      1 / (2 : ℝ) ^ B.card = Real.exp (-Real.log 2 * (B.card : ℝ)) := hExpPow.symm
      _ ≤ Real.exp (-2 * x * (S.card : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [hsumx])
      _ ≤ ∏ q ∈ S, (1 - 2 * b) := hprod
  have hprodPos : 0 < ∏ q ∈ S, (1 - 2 * b) :=
    lt_of_lt_of_le (by positivity) hProdLower
  have hmul : 1 ≤ (∏ q ∈ S, (1 - 2 * b)) * (2 : ℝ) ^ B.card := by
    calc
      1 = (1 / (2 : ℝ) ^ B.card) * (2 : ℝ) ^ B.card := by field_simp
      _ ≤ (∏ q ∈ S, (1 - 2 * b)) * (2 : ℝ) ^ B.card :=
        mul_le_mul_of_nonneg_right hProdLower (by positivity)
  have hinv : (∏ q ∈ S, (1 - 2 * b))⁻¹ ≤ (2 : ℝ) ^ B.card :=
    (inv_le_iff_one_le_mul₀' hprodPos).2 hmul
  simpa [S] using hinv

theorem binList_subset_stage2GroupScope5 (X : Setup5 γ K' χ n N E G)
    (q i : CoarseKey5 n) (hi : i ∈ nearCoarseKeys5 q.1) :
    binList5 i ⊆ stage2GroupScope5 X q := by
  intro w hw
  have hvec : i.1 ∈ nearBinVectors5 q.1 := by
    have hi' : i ∈ (nearBinVectors5 q.1).product Finset.univ := by
      simpa [nearCoarseKeys5] using hi
    exact (Finset.mem_product.mp hi').1
  exact Finset.mem_biUnion.mpr ⟨i.1, hvec, binList_mem_nearBinVectors5 i w hw⟩

theorem blockLocalBins_subset_stage2GroupScope5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hcenter : K.1 = q)
    (hkeys : ∀ ℓ ∈ K.2.1 ∪ X.gateKeys K, ℓ.coarse ∈ nearCoarseKeys5 q.1) :
    blockLocalBins5 X K K.2.1 ⊆ stage2GroupScope5 X q := by
  intro w hw
  simp only [blockLocalBins5, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_union] at hw
  rcases hw with hw | ⟨ℓ, hℓ, hw⟩
  · have hW : w = q.1 := by simpa [hcenter] using hw
    simpa [stage2GroupScope5, hW] using nearBinVectors2_self5 q.1
  · exact binList_subset_stage2GroupScope5 X q ℓ.coarse
      (hkeys ℓ (Finset.mem_union.mpr hℓ)) hw

theorem blockLocalBinsInsert_subset_stage2GroupScope5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hcenter : K.1 = q)
    (S : Finset X.Key)
    (hkeys : ∀ ℓ ∈ S ∪ X.gateKeys K, ℓ.coarse ∈ nearCoarseKeys5 q.1) :
    blockLocalBins5 X K S ⊆ stage2GroupScope5 X q := by
  intro w hw
  simp only [blockLocalBins5, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_union] at hw
  rcases hw with hw | ⟨ℓ, hℓ, hw⟩
  · have hW : w = q.1 := by simpa [hcenter] using hw
    simpa [stage2GroupScope5, hW] using nearBinVectors2_self5 q.1
  · exact binList_subset_stage2GroupScope5 X q ℓ.coarse
      (hkeys ℓ (Finset.mem_union.mpr hℓ)) hw

theorem stage2GroupAlarmScope_subset5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) :
    stage2GroupAlarmScope5 X q i ⊆ stage2GroupScope5 X q := by
  cases i with
  | lowStep1 j p ℓ =>
      exact binList_subset_stage2GroupScope5 X q ℓ.1.coarse
        (stage2LowPatternAt_gateKeys_coarse5 X q j p ℓ.1 ℓ.2)
  | highStep1 p ℓ =>
      exact binList_subset_stage2GroupScope5 X q ℓ.1.coarse
        (stage2HighPatternAt_gateKeys_coarse5 X q p ℓ.1 ℓ.2)
  | lowCap j h =>
      exact binList_subset_stage2GroupScope5 X q q (coarseKey_mem_nearKeys5 q)
  | highCap h =>
      exact binList_subset_stage2GroupScope5 X q q (coarseKey_mem_nearKeys5 q)
  | lowStep2 j p =>
      apply blockLocalBins_subset_stage2GroupScope5 X q p.1 p.2.2.1
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hkey | hgate
      · exact lowTypeCandidates_keys_coarse5 X q default j p.1 p.2.1 ℓ hkey
      · exact stage2LowPatternAt_gateKeys_coarse5 X q j p ℓ hgate
  | highStep2 p =>
      apply blockLocalBins_subset_stage2GroupScope5 X q p.1 p.2.2.1
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hkey | hgate
      · exact highTypeCandidates_keys_coarse5 X q p.1 p.2.1 ℓ hkey
      · exact stage2HighPatternAt_gateKeys_coarse5 X q p ℓ hgate
  | highOptional p =>
      apply blockLocalBinsInsert_subset_stage2GroupScope5 X q p.1.1 p.1.2.2.1
        (insert (X.optKeyOf p.1.1 default) p.1.1.2.1)
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hS | hgate
      · rcases Finset.mem_insert.mp hS with hopt | hkey
        · subst ℓ
          simpa [Setup5.optKeyOf, HiddenKey5.coarse, p.1.2.2.1] using coarseKey_mem_nearKeys5 q
        · exact highTypeCandidates_keys_coarse5 X q p.1.1 p.1.2.1 ℓ hkey
      · exact stage2HighPatternAt_gateKeys_coarse5 X q p.1 ℓ hgate

theorem stage2GroupBadOnPairs_depends5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) :
    FinProb.DependsOn (stage2GroupBadOnPairs5 X v q) (stage2GroupScope5 X q) := by
  classical
  intro ω ω' hω
  let e := coarsePairEquiv5 X
  let c := e ω
  let c' := e ω'
  have hpair : ∀ w ∈ stage2GroupScope5 X q,
      c.1 w = c'.1 w ∧ c.2 w = c'.2 w := by
    intro w hw
    change (ω w).1 = (ω' w).1 ∧ (ω w).2 = (ω' w).2
    have hp := hω w hw
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  have hbad (i : Stage2GroupAlarm5 X q) :
      stage2GroupAlarmBad5 X v q i c ↔ stage2GroupAlarmBad5 X v q i c' := by
    apply stage2GroupAlarmBad_ext5
    intro w hw
    exact hpair w (stage2GroupAlarmScope_subset5 X q i hw)
  apply propext
  change (∃ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBad5 X v q i c) ↔
    (∃ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBad5 X v q i c')
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hbad i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hbad i).mpr hi⟩

theorem stage2GroupAlarmPr_bound5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (hraw : Stage2RawBounds5 X v) (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) :
    (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q i) ≤ stage2GroupAlarmBudget5 X q i := by
  classical
  cases i with
  | lowStep1 j p a =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      let K0 : X.Ty := X.g.evenType (X.p.J n) x
      let t : CubeVertex (X.p.m n) := X.g.sign x
      have hlevel0 : K0.2.2 = some j := by
        have h := p.2.2.2.1
        rw [hK, signShiftType5_level] at h
        exact h
      have hType : X.TypeOccurs K0 := ⟨x, hx, rfl⟩
      have hmemCanon : a.1 ∈ X.gateKeys (signShiftType5 X t K0) := by
        simpa [hK, K0, t] using a.2
      have hGate := gateKeys_signShiftLow5 X t K0 hlevel0
      rw [hGate] at hmemCanon
      obtain ⟨ℓ0, hℓ0, hℓ⟩ := Finset.mem_image.mp hmemCanon
      have hpr : (X.coarseLaw v).pr (fun c =>
          X.step1Fail (v, c) a.1 p.1.1.1 (X.p.typeSegs n p.1)) =
          (X.coarseLaw v).pr (fun c =>
            X.step1Fail (v, c) ℓ0 K0.1.1 (X.p.typeSegs n K0)) := by
        simpa [hK, K0, t, hℓ.symm, signShiftType5_segs] using
          step1AlarmPr_signShift5 X v t K0 ℓ0
      calc
        (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q (.lowStep1 j p a)) =
            (X.coarseLaw v).pr (fun c =>
              X.step1Fail (v, c) a.1 p.1.1.1 (X.p.typeSegs n p.1)) := rfl
        _ = (X.coarseLaw v).pr (fun c =>
              X.step1Fail (v, c) ℓ0 K0.1.1 (X.p.typeSegs n K0)) := hpr
        _ ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K0)) / 2) :=
          hraw.step1 K0 hType ℓ0 hℓ0
        _ = stage2GroupAlarmBudget5 X q (.lowStep1 j p a) := by
          simp [stage2GroupAlarmBudget5, hK, K0, signShiftType5_segs]
  | highStep1 p a =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      have hType : X.TypeOccurs p.1 := ⟨x, hx, hK.symm⟩
      exact hraw.step1 p.1 hType a.1 a.2
  | lowCap j hocc =>
      have hcopy := hocc
      rcases hcopy with ⟨ℓ, hℓ, t, hKey⟩
      have hlevel : ℓ.level = j.val := by
        calc
          ℓ.level = (signShiftKey5 X t ℓ).level := (signShiftKey5_level X t ℓ).symm
          _ = HiddenKey5.level (.inl (q, default, j) : X.Key) := congrArg (fun k : X.Key => k.level) hKey
          _ = j.val := rfl
      have hpr : (X.coarseLaw v).pr (fun c => X.capFail (v, c) (.inl (q, default, j))) =
          (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := by
        have h := capAlarmPr_signShift5 X v t ℓ
        rw [hKey] at h
        exact h
      calc
        (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q (.lowCap j hocc)) =
            (X.coarseLaw v).pr (fun c => X.capFail (v, c) (.inl (q, default, j))) := rfl
        _ = (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := hpr
        _ ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) / 2) :=
          hraw.cap ℓ hℓ
        _ = stage2GroupAlarmBudget5 X q (.lowCap j hocc) := by
          simp [stage2GroupAlarmBudget5, hlevel]
  | highCap hKey =>
      exact hraw.cap (.inr q) hKey
  | lowStep2 j p =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      let K0 : X.Ty := X.g.evenType (X.p.J n) x
      let t : CubeVertex (X.p.m n) := X.g.sign x
      have hlevel0 : K0.2.2 = some j := by
        have h := p.2.2.2.1
        rw [hK, signShiftType5_level] at h
        exact h
      have hType : X.TypeOccurs K0 := ⟨x, hx, rfl⟩
      have hEqPr := step2KeyLawPr_signShiftLowSimple5 X v t K0 hlevel0
      have hRawCanon : (X.keyLawAt v).pr (fun cu =>
          X.step2Fail ((v, cu.1), cu.2) p.1) ≤
          ((p.1.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2) := by
        calc
          (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) p.1) =
              (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K0) := by
                simpa [hK, K0, t] using hEqPr
          _ ≤ ((K0.2.1.card : ℝ) + 1) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K0)) / 2) :=
                hraw.step2 K0 hType
          _ = ((p.1.2.1.card : ℝ) + 1) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2) := by
                simp [hK, K0, signShiftType5_keys_card, signShiftType5_segs]
      exact step2AlarmProb_bound5 X v p.1 hRawCanon
  | highStep2 p =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      have hType : X.TypeOccurs p.1 := ⟨x, hx, hK.symm⟩
      exact step2AlarmProb_bound5 X v p.1 (hraw.step2 p.1 hType)
  | highOptional p =>
      rcases p.1.2.2.2.2 with ⟨x, hx, hK⟩
      rcases p.2 with ⟨t₀, hOpt⟩
      let K0 : X.Ty := p.1.1
      have hType : X.TypeOccurs K0 := ⟨x, hx, hK.symm⟩
      have hnone : K0.2.2 = none := optOccurs_high5 X K0 t₀ hOpt
      have hHigh := typeOccurs_highKeys5 X K0 hType hnone
      have hRawCanon : (X.keyLawAt v).pr (fun cu =>
          X.optFail ((v, cu.1), cu.2) K0 (default : CubeVertex (X.p.m n))) ≤
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2) := by
        have hKfixed : signShiftType5 X t₀ K0 = K0 :=
          signShiftType5_eq_of_highKeys X t₀ K0 hHigh
        have hEqPr : (X.keyLawAt v).pr (fun cu =>
            X.optFail ((v, cu.1), cu.2) K0 (default : CubeVertex (X.p.m n))) =
            (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K0 t₀) := by
          simpa [hKfixed, shiftSignVector_self5] using
            optKeyLawPr_signShiftHighSimple5 X v t₀ t₀ K0 hnone hHigh
        rw [hEqPr]
        exact hraw.optional K0 t₀ hOpt
      exact optAlarmProb_bound5 X v K0 default hRawCanon

theorem stage2GroupBad_pr_le_budget5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (hraw : Stage2RawBounds5 X v) (q : CoarseKey5 n)
    (hm : 1 ≤ X.p.m n) (hJ : X.p.J n ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1) :
    (X.coarseLaw v).pr (stage2GroupBad5 X v q) ≤
      stage2GroupBudgetBound5 X (stage2CoarseCountBase5) := by
  classical
  calc
    (X.coarseLaw v).pr (stage2GroupBad5 X v q) ≤
        ∑ i : Stage2GroupAlarm5 X q,
          (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q i) := by
      have heq : (X.coarseLaw v).pr (stage2GroupBad5 X v q) =
          (X.coarseLaw v).pr (fun c => ∃ i : Stage2GroupAlarm5 X q,
            stage2GroupAlarmBad5 X v q i c) :=
        pr_congr5 _ _ _ (fun _ => Iff.rfl)
      rw [heq]
      exact pr_exists_le_sum5 (X.coarseLaw v) (stage2GroupAlarmBad5 X v q)
    _ ≤ ∑ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBudget5 X q i := by
      apply Finset.sum_le_sum
      intro i hi
      exact stage2GroupAlarmPr_bound5 X v hraw q i
    _ = ∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a :=
      stage2GroupAlarmBudget_sum_eq_flat5 X q
    _ ≤ stage2GroupBudgetBound5 X (stage2CoarseCountBase5) :=
      stage2GroupAlarmFlatBudget_sum_le5 X q hm hJ hK1

theorem stage2GroupBadOnPairs_pr5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) :
    (FinProb.pi (CoarsePairLaw5 X v)).pr (stage2GroupBadOnPairs5 X v q) =
      (X.coarseLaw v).pr (stage2GroupBad5 X v q) := by
  classical
  let P := FinProb.pi (CoarsePairLaw5 X v)
  let e := coarsePairEquiv5 X
  have hmap := map_pr_equiv5 P e (stage2GroupBad5 X v q)
  have hcoarse : X.coarseLaw v = FinProb.map P e := by
    simpa [P, e] using coarseLaw_eq_map_pi5 X v
  calc
    P.pr (stage2GroupBadOnPairs5 X v q) = (FinProb.map P e).pr (stage2GroupBad5 X v q) := by
      calc
        P.pr (stage2GroupBadOnPairs5 X v q) =
            P.pr (fun ω => stage2GroupBad5 X v q (e ω)) :=
          pr_congr5 P _ _ (fun _ => Iff.rfl)
        _ = _ := hmap.symm
    _ = (X.coarseLaw v).pr (stage2GroupBad5 X v q) := by rw [← hcoarse]

end
end HypercubeRamsey.Lane_sol_s05_h23
