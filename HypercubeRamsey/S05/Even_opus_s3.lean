import HypercubeRamsey.S05.Even_setup_dom_sol_s05_even
import HypercubeRamsey.S05.Even_setup_counts_sol_s05_even
import HypercubeRamsey.S05.Even_refs_sol_s05_even
import HypercubeRamsey.S05.Even_density_scales_sol_s05_even
import HypercubeRamsey.S05.Clock_q_s05_even

/-!
# S3 helpers: the product reference of L5.1n (05:1103–1164)

The reference at a star neighbour `b` of an even role `v` with selected reference `c` is Sol's
`localReferenceQ`: the uniform mixture of deleted components over the possible records at same-mode
neighbours, uniform at opposite-mode neighbours.  This file proves the per-neighbour domination with an explicit
log cost (`nbrCost`), the count of opposite-mode neighbours (at most `n^{1/2}`: only fine-chunk flips change the
severity), the reference lengths, and the eventual scale inequalities that make the total cost at most `a₆ k n`.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_s3

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- The cost of an opposite-mode neighbour against the uniform law: `D_L + D_H + log 4 + log (s + 1)`. -/
def oppCost : ℝ := X.p.DL n + X.p.DH n + Real.log 4 + Real.log ((X.p.s n : ℝ) + 1)

/-- The per-neighbour log cost of the product reference (05:1137–1162). -/
def nbrCost (C : ℝ) {L : X.CentreLayer5} (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (c : X.CRef L.ht) (b : OddRole5 n) (o : X.OddOut) : ℝ :=
  if X.g.low (X.p.J n) v.1 ∧ X.g.low (X.p.J n) b.1 then
    X.p.a 4 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) +
      (Lane_sol_s05_even.lowRecordCost X C b + 15 * (X.p.T n : ℝ) * Real.log (n : ℝ))
  else if ¬ X.g.low (X.p.J n) v.1 ∧ ¬ X.g.low (X.p.J n) b.1 then
    X.highCost H (X.actualRecord (L.elig H) H ω b) (arraysOf ω)
        (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) o +
      617 * (X.p.T n : ℝ) * Real.log (n : ℝ)
  else oppCost X

theorem DH_nonneg (hm : 1 ≤ X.p.m n) : 0 ≤ X.p.DH n := by
  unfold Params5.DH
  apply mul_nonneg (mul_nonneg X.p.hKD.le (Nat.cast_nonneg _))
  exact Real.log_nonneg (by exact_mod_cast hm)

theorem DL_nonneg : 0 ≤ X.p.DL n := Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Opposite-mode neighbours cost `oppCost` against the uniform law. -/
theorem opposite_dominates {L : X.CentreLayer5} {cL cH : ℝ} (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
    (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n) (hm : 1 ≤ X.p.m n) (hs : 0 < X.p.s n)
    (o : X.OddOut) :
    X.oddRow LR HR H ω b o ≤ Real.exp (oppCost X) * (Lane_sol_s05_even.uniformOdd X).w o := by
  have hN : (0 : ℝ) < N := by exact_mod_cast X.y₀.pos
  have hsR : (1 : ℝ) ≤ X.p.s n := by exact_mod_cast hs
  have hDH := DH_nonneg X hm
  have hDL := DL_nonneg X
  have heDH : 1 ≤ Real.exp (X.p.DH n) := Real.one_le_exp hDH
  have heDL : 1 ≤ Real.exp (X.p.DL n) := Real.one_le_exp hDL
  have hrhs : Real.exp (oppCost X) * (Lane_sol_s05_even.uniformOdd X).w o =
      4 * Real.exp (X.p.DL n) * Real.exp (X.p.DH n) / N := by
    have hcard : (Fintype.card X.OddOut : ℝ) = ((X.p.s n : ℝ) + 1) * N := by
      simp [Setup5.OddOut, Fintype.card_prod, Fintype.card_fin]
    simp only [Lane_sol_s05_even.uniformOdd, FinProb.uniformAll, hcard, oppCost]
    have hs1 : (X.p.s n : ℝ) + 1 ≠ 0 := by positivity
    have hN' : (N : ℝ) ≠ 0 := hN.ne'
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
    field_simp
    ring
  rw [hrhs]
  unfold Setup5.oddRow
  by_cases hbl : X.g.low (X.p.J n) b.1
  · rw [HR.row_low H ω b o hbl, add_zero]
    have hcap := LR.row_cap H ω b o
    rw [le_div_iff₀ hN]
    have h1 : Real.exp (X.p.DL n) ≤ 4 * Real.exp (X.p.DL n) * Real.exp (X.p.DH n) := by nlinarith
    linarith
  · rw [LR.row_high H ω b o hbl, zero_add]
    have hcap := HR.row_cap H ω b o
    refine hcap.trans ?_
    rw [div_le_div_iff₀ (mul_pos (by linarith) hN) hN]
    have h1 : 2 * Real.exp (X.p.DH n) * N ≤ 4 * Real.exp (X.p.DL n) * Real.exp (X.p.DH n) * N := by
      have : 2 * Real.exp (X.p.DH n) ≤ 4 * Real.exp (X.p.DL n) * Real.exp (X.p.DH n) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hN.le
    calc 2 * Real.exp (X.p.DH n) * N ≤ 4 * Real.exp (X.p.DL n) * Real.exp (X.p.DH n) * N := h1
      _ ≤ 4 * Real.exp (X.p.DL n) * Real.exp (X.p.DH n) * ((X.p.s n : ℝ) * N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

/-- Per-neighbour domination of the odd row by the product reference (05:1137–1162). -/
theorem nbr_dominates (C : ℝ) (hC : X.RecordCount C) {L : X.CentreLayer5} {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (c : X.CRef L.ht) (b : OddRole5 n) (hadj : (cube n).Adj v.1 b.1)
    (hb : L.valid H ω b) (hc : X.evenRefOf (L.elig H) H ω v = some c)
    (hn : 7 ≤ n) (hm : 2 ≤ X.p.m n) (o : X.OddOut) :
    X.oddRow LR HR H ω b o ≤
      Real.exp (nbrCost X C HR H ω v c b o) * (Lane_sol_s05_even.localReferenceQ X L H ω v b c).w o := by
  have hv : v ∈ Setup5.evenNbrs b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
  obtain ⟨hs, _⟩ := Lane_sol_s05_even.high_lengths_positive X.p n hm
  unfold Lane_sol_s05_even.localReferenceQ nbrCost
  rw [if_pos hadj]
  by_cases hl : X.g.low (X.p.J n) v.1 ∧ X.g.low (X.p.J n) b.1
  · rw [if_pos hl, if_pos hl]
    have h1 := Lane_sol_s05_even.lowMixture_dominates_row X L LR HR H ω v b c hv hb hl.1 hl.2 hc o
    have h2 := Lane_sol_s05_even.lowConfig_cost X C hC L H ω b hb hn
    refine h1.trans ?_
    rw [Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ ((Lane_sol_s05_even.lowMixture X L H ω v b c).nonneg o)
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  · rw [if_neg hl, if_neg hl]
    by_cases hh : ¬ X.g.low (X.p.J n) v.1 ∧ ¬ X.g.low (X.p.J n) b.1
    · rw [if_pos hh, if_pos hh]
      have h1 := Lane_sol_s05_even.highMixture_dominates_row X L LR HR H ω v b c hv hb hh.2 hs hc o
      have h2 := Lane_sol_s05_even.highConfig_cost X L H ω b hb hh.2 hn (by omega)
      refine h1.trans ?_
      rw [Real.exp_add]
      apply mul_le_mul_of_nonneg_right _ ((Lane_sol_s05_even.highMixture X L H ω v b c).nonneg o)
      exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    · rw [if_neg hh, if_neg hh]
      exact opposite_dominates X LR HR H ω b (by omega) hs o

/-- The product of the star rows is dominated by `exp (Σ costs)` times the product reference. -/
theorem prod_dominates (C : ℝ) (hC : X.RecordCount C) {L : X.CentreLayer5} {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (c : X.CRef L.ht) (hc : X.evenRefOf (L.elig H) H ω v = some c)
    (hn : 7 ≤ n) (hm : 2 ≤ X.p.m n) (O : OddRole5 n → X.OddOut)
    (hval : ∀ b ∈ Finset.univ.filter (fun b : OddRole5 n => (cube n).Adj v.1 b.1), L.valid H ω b) :
    ∏ b ∈ Finset.univ.filter (fun b : OddRole5 n => (cube n).Adj v.1 b.1), X.oddRow LR HR H ω b (O b) ≤
      Real.exp (∑ b ∈ Finset.univ.filter (fun b : OddRole5 n => (cube n).Adj v.1 b.1),
          nbrCost X C HR H ω v c b (O b)) *
        ∏ b ∈ Finset.univ.filter (fun b : OddRole5 n => (cube n).Adj v.1 b.1),
          (Lane_sol_s05_even.localReferenceQ X L H ω v b c).w (O b) := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro b _
    exact X.oddRow_nonneg LR HR H ω b (O b)
  · intro b hb
    exact nbr_dominates X C hC LR HR H ω v c b (Finset.mem_filter.mp hb).2 (hval b hb) hc hn hm (O b)

/-- The constant request of S3: `K₂ ≥ 2(C + 1)/(a₆ - a₄)`, where `C` is the record-count constant of L5.1e,
so that the low record overhead `C (j + 1) log m` fits the gap `(a₆ - a₄) k / 2` (05:1149, 05:762–783). -/
def s3Request (C : ℝ) : ParamReq5 where
  Kcap _ := 0
  Kpp _ := 0
  Kh _ := 0
  K1 _ := 0
  K2 x := 2 * (C + 1) / (x.1.1.1 6 - x.1.1.1 4)
  KD _ := 0
  Ks _ := 0
  KB _ := 0
  alpha _ := 1
  alpha_pos _ := one_pos

theorem s3Request_K2 (C : ℝ) {p : Params5 γ K' χ} (hp : (s3Request C).Holds p) :
    2 * (C + 1) / (p.a 6 - p.a 4) ≤ p.K2 := hp.2.2.2.2.1

/-! ### Opposite-mode neighbours (05:1158–1160)

Adjacent roles differ in one coordinate; a flip outside the fine chunks keeps every fine count, hence the
severity and the mode.  So the opposite-mode neighbours inject into the fine coordinates, at most `n^{1/2}`. -/

theorem opposite_card_le (v : EvenRole5 n) :
    ((((Finset.univ.filter fun b : OddRole5 n => (cube n).Adj v.1 b.1).filter fun b =>
        ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1)).card : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  set S := ((Finset.univ.filter fun b : OddRole5 n => (cube n).Adj v.1 b.1).filter fun b =>
        ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1)) with hS
  let F : Finset (Fin n) := Finset.univ.biUnion X.g.fineChunks
  have hsub : S.map (Function.Embedding.subtype _) ⊆ F.image (flipVertex5 v.1) := by
    intro y hy
    obtain ⟨b, hbS, rfl⟩ := Finset.mem_map.mp hy
    have hb1 := Finset.mem_filter.mp hbS
    have hadj := (Finset.mem_filter.mp hb1.1).2
    have hopp := hb1.2
    obtain ⟨a, ha⟩ := Lane_sol_s05_h5l.adjacent_flip v.1 b.1 hadj
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, ha.symm⟩
    by_contra haF
    apply hopp
    have hcounts (i : Fin (X.p.m n)) : X.g.fineCount b.1 i = X.g.fineCount v.1 i := by
      rw [ha]
      exact Lane_sol_s05_h5l.fineCount_flip_outside X.g v.1 a i
        (fun hi => haF (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩))
    have hsev : X.g.severity b.1 = X.g.severity v.1 := by
      unfold ChunkGeometry5.severity
      simp_rw [hcounts]
    simp only [ChunkGeometry5.low, hsev]
  have hcard : S.card ≤ F.card := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_map] at h1
    exact h1.trans Finset.card_image_le
  have hF : (F.card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hocc := X.g.occupied_sublinear
    have hle : F.card ≤ ((Finset.univ.biUnion X.g.coarseChunks) ∪ F).card :=
      Finset.card_le_card Finset.subset_union_right
    have hle' : (F.card : ℝ) ≤ (((Finset.univ.biUnion X.g.coarseChunks) ∪
        (Finset.univ.biUnion X.g.fineChunks)).card : ℝ) := by exact_mod_cast hle
    exact hle'.trans hocc
  exact (by exact_mod_cast hcard : (S.card : ℝ) ≤ F.card).trans hF

/-! ### Reference lengths -/

theorem low_ref_length {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (elig : X.CΩ h → h.hp.EligMap) (v : EvenRole5 n) (c : X.CRef h)
    (hc : X.evenRefOf elig H ω v = some c) (hv : X.g.low (X.p.J n) v.1) (hm : 2 ≤ X.p.m n) :
    X.p.K2 * (((X.g.severity v.1 : ℝ) + 4) * Real.log (X.p.m n : ℝ) + (X.p.m n : ℝ) ^ (1 / 50 : ℝ)) ≤
      (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) := by
  obtain ⟨_, hcard⟩ := Lane_sol_s05_even.selected_ref_props X H ω elig v c hc
  have hsev : X.g.severity v.1 ≤ X.p.J n := hv
  have htype : (X.g.evenType (X.p.J n) v.1).2.2 = some ⟨X.g.severity v.1, Nat.lt_succ_of_le hsev⟩ := by
    simp [ChunkGeometry5.evenType, hsev]
  rw [htype] at hcard
  unfold Setup5.refLen Params5.typeSegs
  rw [htype]
  simp only at hcard ⊢
  rw [hcard]
  have hl := Lane_sol_s05_h5l.low_length_lower X.p n (X.g.severity v.1) (by omega)
  have heq : X.p.lowBlocks n (X.g.severity v.1) * (X.p.q0 * X.p.uSeg n (X.g.severity v.1)) =
      X.p.q0 * X.p.uSeg n (X.g.severity v.1) * X.p.lowBlocks n (X.g.severity v.1) := by ring
  rw [heq]
  exact hl

theorem high_ref_length {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (elig : X.CΩ h → h.hp.EligMap) (v : EvenRole5 n) (c : X.CRef h)
    (hc : X.evenRefOf elig H ω v = some c) (hv : ¬ X.g.low (X.p.J n) v.1) :
    X.refLen (X.g.evenType (X.p.J n) v.1) c.2 = X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n := by
  obtain ⟨_, hcard⟩ := Lane_sol_s05_even.selected_ref_props X H ω elig v c hc
  have hsev : ¬ X.g.severity v.1 ≤ X.p.J n := hv
  have htype : (X.g.evenType (X.p.J n) v.1).2.2 = none := by
    simp [ChunkGeometry5.evenType, hsev]
  rw [htype] at hcard
  unfold Setup5.refLen Params5.typeSegs
  rw [htype]
  simp only at hcard ⊢
  rw [hcard]
  ring

/-! ### Scales -/

theorem log_n_le (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n : ℝ) ≤ Real.log (p.m n : ℝ) / p.alpha := by
  have hα := p.halpha.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ^ p.alpha ≤ p.m n := Nat.le_ceil _
  have hpos : 0 < (n : ℝ) ^ p.alpha := Real.rpow_pos_of_pos hnR _
  have h := Real.log_le_log hpos hle
  rw [Real.log_rpow hnR] at h
  rw [le_div_iff₀ hα]
  linarith

theorem T_log_n_le (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ p.m n) :
    (p.T n : ℝ) * Real.log (n : ℝ) ≤ (2000 / p.alpha) * (p.m n : ℝ) ^ (1 / 500 : ℝ) := by
  have hmR : (1 : ℝ) ≤ p.m n := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < p.m n := by linarith
  have hT := Lane_sol_s05_h5l.T_upper p n hmR
  have hα := p.halpha.1
  have hlogn := log_n_le p n hn
  have hlogm : Real.log (p.m n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 1000 : ℝ) / (1 / 1000) :=
    Real.log_le_rpow_div hmpos.le (by norm_num)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hpow : (p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (1 / 1000 : ℝ) =
      (p.m n : ℝ) ^ (1 / 500 : ℝ) := by
    rw [← Real.rpow_add hmpos]
    norm_num
  have h2 : Real.log (n : ℝ) ≤ 1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) / p.alpha := by
    calc Real.log (n : ℝ) ≤ Real.log (p.m n : ℝ) / p.alpha := hlogn
      _ ≤ ((p.m n : ℝ) ^ (1 / 1000 : ℝ) / (1 / 1000)) / p.alpha :=
        div_le_div_of_nonneg_right hlogm hα.le
      _ = 1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) / p.alpha := by ring
  calc (p.T n : ℝ) * Real.log (n : ℝ) ≤
        (2 * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) * (1000 * (p.m n : ℝ) ^ (1 / 1000 : ℝ) / p.alpha) :=
        mul_le_mul hT h2 hlogn0 (by positivity)
    _ = (2000 / p.alpha) * ((p.m n : ℝ) ^ (1 / 1000 : ℝ) * (p.m n : ℝ) ^ (1 / 1000 : ℝ)) := by ring
    _ = _ := by rw [hpow]

/-- The eventual scale inequalities used by the cost sum: the low record overhead fits `(C+1) m^{1/50}`,
the high mixture overhead `617 T log n` fits the gap `(a₆ - a₅)/2` of `k_*`, and the `n^{1/2}` opposite-mode
neighbours fit the gap of `n`. -/
theorem eventual_costs (p : Params5 γ K' χ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, 7 ≤ n ∧ 2 ≤ p.m n ∧
      C * ((p.T n : ℝ) * Real.log (p.T n) +
          (p.T n : ℝ) * (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ)) +
        15 * (p.T n : ℝ) * Real.log (n : ℝ) ≤ (C + 1) * (p.m n : ℝ) ^ (1 / 50 : ℝ) ∧
      617 * (p.T n : ℝ) * Real.log (n : ℝ) ≤
        (p.a 6 - p.a 5) / 2 * min 1 p.K2 * (p.m n : ℝ) ^ (1 / 200 : ℝ) ∧
      (n : ℝ) ^ (1 / 2 : ℝ) * (p.DL n + p.DH n + Real.log 4 + Real.log ((p.s n : ℝ) + 1)) ≤
        (p.a 6 - p.a 5) / 2 * min 1 p.K2 * n := by
  have hα := p.halpha.1
  have h56 : 0 < p.a 6 - p.a 5 := sub_pos.mpr (p.ha_order 5 6 (by decide))
  have hmin : 0 < min 1 p.K2 := lt_min (by norm_num) p.hK2
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (p.a 6 - p.a 5) / 2 * min 1 p.K2 := ⟨_, rfl⟩
  rw [← hε]
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεne : ε ≠ 0 := hεpos.ne'
  have hαne : p.alpha ≠ 0 := hα.ne'
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * Lane_sol_s05_even.capCoeff p + 10 * p.Ks + 1 := ⟨_, rfl⟩
  have hm := Lane_sol_s05_h1.tendsto_m p
  have hq : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 7, hm.eventually_ge_atTop 2,
    Lane_sol_s05_h5l.low_pattern_overhead_eventually p,
    Lane_sol_s05_h5l.fixed_power_margin p (15 * (2000 / p.alpha)) (1 / 500) (1 / 50) (by norm_num),
    Lane_sol_s05_h5l.fixed_power_margin p (617 * (2000 / p.alpha) / ε) (1 / 500) (1 / 200) (by norm_num),
    hq.eventually_ge_atTop (B / ε)] with n hn7 hm2 hlow h15 h617 hquart
  have hm2' : 2 ≤ p.m n := by exact_mod_cast hm2
  have hn1 : 1 ≤ n := by omega
  have hTL := T_log_n_le p n hn1 (by omega)
  have hmR : (1 : ℝ) ≤ p.m n := by exact_mod_cast (show 1 ≤ p.m n by omega)
  have hpow0 : 0 ≤ (p.m n : ℝ) ^ (1 / 500 : ℝ) := Real.rpow_nonneg (by positivity) _
  refine ⟨hn7, hm2', ?_, ?_, ?_⟩
  · have h1 : 15 * (p.T n : ℝ) * Real.log (n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 50 : ℝ) := by
      calc 15 * (p.T n : ℝ) * Real.log (n : ℝ) = 15 * ((p.T n : ℝ) * Real.log (n : ℝ)) := by ring
        _ ≤ 15 * ((2000 / p.alpha) * (p.m n : ℝ) ^ (1 / 500 : ℝ)) := by linarith
        _ = 15 * (2000 / p.alpha) * (p.m n : ℝ) ^ (1 / 500 : ℝ) := by ring
        _ ≤ _ := h15
    have h2 := mul_le_mul_of_nonneg_left hlow hC
    linarith
  · have h1 : 617 * (p.T n : ℝ) * Real.log (n : ℝ) ≤
        ε * (617 * (2000 / p.alpha) / ε * (p.m n : ℝ) ^ (1 / 500 : ℝ)) := by
      have he : ε * (617 * (2000 / p.alpha) / ε * (p.m n : ℝ) ^ (1 / 500 : ℝ)) =
          617 * ((2000 / p.alpha) * (p.m n : ℝ) ^ (1 / 500 : ℝ)) := by
        field_simp
      rw [he]
      linarith
    calc 617 * (p.T n : ℝ) * Real.log (n : ℝ) ≤
        ε * (617 * (2000 / p.alpha) / ε * (p.m n : ℝ) ^ (1 / 500 : ℝ)) := h1
      _ ≤ ε * (p.m n : ℝ) ^ (1 / 200 : ℝ) := mul_le_mul_of_nonneg_left h617 hεpos.le
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < n := by linarith
    obtain ⟨hDL, hDH⟩ := Lane_sol_s05_even.capCoeff_bounds p n hn1 (by omega)
    have hs := Lane_sol_s05_even.history_length_upper p n hn1 (by omega)
    have hlogs : Real.log ((p.s n : ℝ) + 1) ≤ p.s n := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (p.s n : ℝ) + 1)
      linarith
    have hsum : p.DL n + p.DH n + Real.log 4 + Real.log ((p.s n : ℝ) + 1) ≤
        B * (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [hB]
      linarith
    have hq0 : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hn0.le _
    have hh0 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hn0.le _
    have hp34 : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = (n : ℝ) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hn0]
      norm_num
    have hp1 : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = n := by
      rw [← Real.rpow_add hn0]
      norm_num
    have hB' : B ≤ ε * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have := (div_le_iff₀ hεpos).mp hquart
      linarith
    have h34 : 0 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hn0.le _
    calc (n : ℝ) ^ (1 / 2 : ℝ) * (p.DL n + p.DH n + Real.log 4 + Real.log ((p.s n : ℝ) + 1)) ≤
        (n : ℝ) ^ (1 / 2 : ℝ) * (B * (n : ℝ) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hsum hh0
      _ = B * (n : ℝ) ^ (3 / 4 : ℝ) := by rw [← hp34]; ring
      _ ≤ (ε * (n : ℝ) ^ (1 / 4 : ℝ)) * (n : ℝ) ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right hB' h34
      _ = ε * n := by rw [mul_assoc, hp1]

/-! ### The total cost (05:1158–1162) -/

/-- The star costs sum to at most `a₆ k n`: same-mode low neighbours cost `a₄ k` plus a record overhead
within `(a₆ - a₄) k / 2` (the level of a neighbour is at most one above the role's), same-mode high neighbours
cost the imposed budget `a₅ k_* n` plus `617 T log n` each, and the opposite-mode ones `oppCost` each. -/
theorem cost_sum_le (C : ℝ) (hC0 : 0 ≤ C) {L : X.CentreLayer5} (HR : X.HighRows5 L) (H : X.KeyHist)
    (ω : X.CΩ L.ht) (v : EvenRole5 n) (c : X.CRef L.ht) (hc : X.evenRefOf (L.elig H) H ω v = some c)
    (O : OddRole5 n → X.OddOut) (hm : 2 ≤ X.p.m n)
    (hK2 : 2 * (C + 1) / (X.p.a 6 - X.p.a 4) ≤ X.p.K2)
    (hA : C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ)) +
        15 * (X.p.T n : ℝ) * Real.log (n : ℝ) ≤ (C + 1) * (X.p.m n : ℝ) ^ (1 / 50 : ℝ))
    (hB : 617 * (X.p.T n : ℝ) * Real.log (n : ℝ) ≤
        (X.p.a 6 - X.p.a 5) / 2 * min 1 X.p.K2 * (X.p.m n : ℝ) ^ (1 / 200 : ℝ))
    (hD : (n : ℝ) ^ (1 / 2 : ℝ) * oppCost X ≤ (X.p.a 6 - X.p.a 5) / 2 * min 1 X.p.K2 * n)
    (hbudget : ¬ X.g.low (X.p.J n) v.1 →
      ∑ b ∈ (Finset.univ.filter fun b : OddRole5 n => (cube n).Adj v.1 b.1).filter
          (fun b => ¬ X.g.low (X.p.J n) b.1),
        X.highCost H (X.actualRecord (L.elig H) H ω b) (arraysOf ω)
          (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) (O b) ≤
        X.p.a 5 * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ) * n) :
    ∑ b ∈ Finset.univ.filter (fun b : OddRole5 n => (cube n).Adj v.1 b.1), nbrCost X C HR H ω v c b (O b) ≤
      X.p.a 6 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) * n := by
  set S := Finset.univ.filter (fun b : OddRole5 n => (cube n).Adj v.1 b.1) with hS
  obtain ⟨k, hk⟩ : ∃ k : ℝ, (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) = k := ⟨_, rfl⟩
  rw [hk]
  have h04 : X.p.a 0 < X.p.a 4 := X.p.ha_order 0 4 (by decide)
  have h45 : X.p.a 4 < X.p.a 5 := X.p.ha_order 4 5 (by decide)
  have h56 : X.p.a 5 < X.p.a 6 := X.p.ha_order 5 6 (by decide)
  have ha4 : 0 < X.p.a 4 := by rw [X.p.ha0] at h04; linarith
  have hmR : (1 : ℝ) ≤ X.p.m n := by exact_mod_cast (show 1 ≤ X.p.m n by omega)
  have hk0 : 0 ≤ k := by rw [← hk]; exact Nat.cast_nonneg _
  have hkmin : min 1 X.p.K2 * (X.p.m n : ℝ) ^ (1 / 200 : ℝ) ≤ k := by
    rw [← hk]
    exact Lane_sol_s05_even.selected_ref_length_lower X H ω (L.elig H) v c hc hm
  have hmin0 : 0 ≤ min 1 X.p.K2 := le_min (by norm_num) X.p.hK2.le
  have hp1 : (1 : ℝ) ≤ (X.p.m n : ℝ) ^ (1 / 200 : ℝ) := Real.one_le_rpow hmR (by norm_num)
  have hkmin' : min 1 X.p.K2 ≤ k := by nlinarith
  have hScard : (S.card : ℝ) ≤ n := by exact_mod_cast oddAdjSet5_card_le v
  have hopp0 : 0 ≤ oppCost X := by
    have hDH := DH_nonneg X (by omega)
    have hDL := DL_nonneg X
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hs1 : 0 ≤ Real.log ((X.p.s n : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg (X.p.s n) : (0 : ℝ) ≤ _)])
    unfold oppCost
    linarith
  have hoppSum : ∑ b ∈ S, (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0) ≤
      (X.p.a 6 - X.p.a 5) / 2 * k * n := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard' := opposite_card_le X v
    calc ((S.filter fun b => ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1)).card : ℝ) * oppCost X ≤ (n : ℝ) ^ (1 / 2 : ℝ) * oppCost X :=
          mul_le_mul_of_nonneg_right hcard' hopp0
      _ ≤ (X.p.a 6 - X.p.a 5) / 2 * min 1 X.p.K2 * n := hD
      _ ≤ (X.p.a 6 - X.p.a 5) / 2 * k * n := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
        exact mul_le_mul_of_nonneg_left hkmin' (by linarith)
  by_cases hv : X.g.low (X.p.J n) v.1
  · -- a low role: same-mode neighbours cost at most `(a₄ + a₆)/2 · k`
    have hlowlen := low_ref_length X H ω (L.elig H) v c hc hv hm
    rw [hk] at hlowlen
    have hpoint : ∀ b ∈ S, nbrCost X C HR H ω v c b (O b) ≤
        (X.p.a 4 + X.p.a 6) / 2 * k + (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0) := by
      intro b hb
      have hadj := (Finset.mem_filter.mp hb).2
      unfold nbrCost
      by_cases hbl : X.g.low (X.p.J n) b.1
      · have hiff : (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) := ⟨fun _ => hbl, fun _ => hv⟩
        rw [if_pos (And.intro hv hbl), if_neg (not_not.mpr hiff), add_zero, hk]
        -- the record overhead
        have hsevb : X.g.severity b.1 ≤ X.g.severity v.1 + 1 :=
          (Lane_sol_s05_h5l.adjacent_severity X.g v.1 b.1 hadj).2
        have hbsev : X.g.severity b.1 ≤ X.p.J n := hbl
        have hlev : ((X.g.roleKey (X.p.J n) b.1).level : ℝ) = X.g.severity b.1 := by
          simp [ChunkGeometry5.roleKey, hbsev, HiddenKey5.level]
        have hite : (if (X.g.roleKey (X.p.J n) b.1).isLeft ∧ (X.g.roleKey (X.p.J n) b.1).level = X.p.J n then
            (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0) ≤
            (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) := by
          split_ifs
          · exact le_rfl
          · positivity
        have hlogm : 0 ≤ Real.log (X.p.m n : ℝ) := Real.log_nonneg hmR
        have hlevle : ((X.g.roleKey (X.p.J n) b.1).level : ℝ) + 1 ≤ (X.g.severity v.1 : ℝ) + 4 := by
          rw [hlev]
          have : (X.g.severity b.1 : ℝ) ≤ X.g.severity v.1 + 1 := by exact_mod_cast hsevb
          linarith
        have hrec : Lane_sol_s05_even.lowRecordCost X C b + 15 * (X.p.T n : ℝ) * Real.log (n : ℝ) ≤
            (C + 1) * (((X.g.severity v.1 : ℝ) + 4) * Real.log (X.p.m n : ℝ) +
              (X.p.m n : ℝ) ^ (1 / 50 : ℝ)) := by
          unfold Lane_sol_s05_even.lowRecordCost
          have h1 := mul_le_mul_of_nonneg_right hlevle hlogm
          have h2 := mul_le_mul_of_nonneg_left h1 hC0
          have h3 := mul_le_mul_of_nonneg_left hite hC0
          have h4 : 0 ≤ ((X.g.severity v.1 : ℝ) + 4) * Real.log (X.p.m n : ℝ) := by positivity
          linarith
        have hK2' : C + 1 ≤ (X.p.a 6 - X.p.a 4) / 2 * X.p.K2 := by
          have hpos : 0 < X.p.a 6 - X.p.a 4 := by linarith
          have := (div_le_iff₀ hpos).mp hK2
          linarith
        have hX0 : 0 ≤ ((X.g.severity v.1 : ℝ) + 4) * Real.log (X.p.m n : ℝ) +
            (X.p.m n : ℝ) ^ (1 / 50 : ℝ) := by positivity
        have h5 := mul_le_mul_of_nonneg_right hK2' hX0
        have h6 : (X.p.a 6 - X.p.a 4) / 2 * X.p.K2 * (((X.g.severity v.1 : ℝ) + 4) *
            Real.log (X.p.m n : ℝ) + (X.p.m n : ℝ) ^ (1 / 50 : ℝ)) ≤ (X.p.a 6 - X.p.a 4) / 2 * k := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hlowlen (by linarith)
        linarith
      · have hiff : ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) := fun h => hbl (h.mp hv)
        have n1 : ¬ (X.g.low (X.p.J n) v.1 ∧ X.g.low (X.p.J n) b.1) := fun h => hbl h.2
        have n2 : ¬ (¬ X.g.low (X.p.J n) v.1 ∧ ¬ X.g.low (X.p.J n) b.1) := fun h => h.1 hv
        rw [if_neg n1, if_neg n2, if_pos hiff]
        have : 0 ≤ (X.p.a 4 + X.p.a 6) / 2 * k := by
          apply mul_nonneg _ hk0
          linarith
        linarith
    calc ∑ b ∈ S, nbrCost X C HR H ω v c b (O b) ≤
        ∑ b ∈ S, ((X.p.a 4 + X.p.a 6) / 2 * k +
          (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0)) := Finset.sum_le_sum hpoint
      _ = (S.card : ℝ) * ((X.p.a 4 + X.p.a 6) / 2 * k) +
          ∑ b ∈ S, (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * ((X.p.a 4 + X.p.a 6) / 2 * k) + (X.p.a 6 - X.p.a 5) / 2 * k * n := by
        refine add_le_add ?_ hoppSum
        apply mul_le_mul_of_nonneg_right hScard
        apply mul_nonneg _ hk0
        linarith
      _ ≤ X.p.a 6 * k * n := by
        have hkn : 0 ≤ k * n := mul_nonneg hk0 (Nat.cast_nonneg n)
        have h' := mul_le_mul_of_nonneg_right h45.le hkn
        linarith
  · -- a high role: the imposed budget plus `617 T log n` per same-mode neighbour
    have hkeq : k = ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ) := by
      rw [← hk, high_ref_length X H ω (L.elig H) v c hc hv]
    have hBk : 617 * (X.p.T n : ℝ) * Real.log (n : ℝ) ≤ (X.p.a 6 - X.p.a 5) / 2 * k := by
      refine hB.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hkmin (by linarith)
    have hpoint : ∀ b ∈ S, nbrCost X C HR H ω v c b (O b) ≤
        (if ¬ X.g.low (X.p.J n) b.1 then X.highCost H (X.actualRecord (L.elig H) H ω b) (arraysOf ω)
          (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) (O b) else 0) +
        (X.p.a 6 - X.p.a 5) / 2 * k + (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0) := by
      intro b _
      unfold nbrCost
      by_cases hbl : X.g.low (X.p.J n) b.1
      · have hiff : ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) := fun h => hv (h.mpr hbl)
        have n1 : ¬ (X.g.low (X.p.J n) v.1 ∧ X.g.low (X.p.J n) b.1) := fun h => hv h.1
        have n2 : ¬ (¬ X.g.low (X.p.J n) v.1 ∧ ¬ X.g.low (X.p.J n) b.1) := fun h => h.2 hbl
        rw [if_neg n1, if_neg n2, if_neg (not_not.mpr hbl), if_pos hiff]
        have : 0 ≤ (X.p.a 6 - X.p.a 5) / 2 * k := mul_nonneg (by linarith) hk0
        linarith
      · have hiff : (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) := ⟨fun h => (hv h).elim, fun h => (hbl h).elim⟩
        have n1 : ¬ (X.g.low (X.p.J n) v.1 ∧ X.g.low (X.p.J n) b.1) := fun h => hv h.1
        rw [if_neg n1, if_pos (And.intro hv hbl), if_pos hbl, if_neg (not_not.mpr hiff), add_zero]
        linarith
    have hhigh := hbudget hv
    calc ∑ b ∈ S, nbrCost X C HR H ω v c b (O b) ≤
        ∑ b ∈ S, ((if ¬ X.g.low (X.p.J n) b.1 then X.highCost H (X.actualRecord (L.elig H) H ω b)
          (arraysOf ω) (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) (O b) else 0) +
          (X.p.a 6 - X.p.a 5) / 2 * k + (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0)) :=
        Finset.sum_le_sum hpoint
      _ = ∑ b ∈ S.filter (fun b => ¬ X.g.low (X.p.J n) b.1), X.highCost H
            (X.actualRecord (L.elig H) H ω b) (arraysOf ω) (c.1, X.g.evenType (X.p.J n) v.1, c.2)
            (HR.row H ω b) (O b) + (S.card : ℝ) * ((X.p.a 6 - X.p.a 5) / 2 * k) +
          ∑ b ∈ S, (if ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1) then oppCost X else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          Finset.sum_filter]
      _ ≤ X.p.a 5 * k * n + (n : ℝ) * ((X.p.a 6 - X.p.a 5) / 2 * k) +
          (X.p.a 6 - X.p.a 5) / 2 * k * n := by
        rw [hkeq] at hoppSum ⊢
        refine add_le_add (add_le_add hhigh ?_) hoppSum
        apply mul_le_mul_of_nonneg_right hScard
        exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
      _ = X.p.a 6 * k * n := by ring

end
end HypercubeRamsey.Setup5.Lane_opus_s05_s3
