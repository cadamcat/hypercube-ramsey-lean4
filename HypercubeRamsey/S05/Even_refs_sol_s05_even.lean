import HypercubeRamsey.S05.Even_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem card_fin_prefix {k t : ℕ} (h : k ≤ t) :
    (Finset.univ.filter (fun i : Fin t => (i : ℕ) < k)).card = k := by
  let A := Finset.univ.filter (fun i : Fin t => (i : ℕ) < k)
  let e : Fin k ≃ A := {
    toFun i := ⟨Fin.castLE h i, by simp [A, i.isLt]⟩
    invFun i := ⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; rfl
    right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr e).symm

theorem poolIdx_card : X.poolIdx.card = X.p.poolBlocks n := by
  exact card_fin_prefix (Nat.le_max_left _ _)

theorem usedBlocks_le_poolBlocks : X.p.usedBlocks n ≤ X.p.poolBlocks n := by
  have hU : 0 ≤ X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n) := by
    exact mul_nonneg X.p.hKh.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hExp : 1 ≤ Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) :=
    Real.one_le_exp_iff.mpr hU
  have hceil : Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) * X.p.usedBlocks n ≤
      (X.p.poolBlocks n : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hExp (Nat.cast_nonneg (X.p.usedBlocks n) : (0 : ℝ) ≤ _)
  exact_mod_cast (by simpa using hmul.trans hceil)

theorem refSubsetOn_props {Id : Type} (H : X.KeyHist) (a : X.ArraysOn Id)
    (c : Id × X.Ty) (opt : Option X.Key) :
    (∀ j ∈ X.refSubsetOn H a c opt, (j : ℕ) < X.p.typeBlocks n c.2) ∧
      (X.refSubsetOn H a c opt).card =
        match c.2.2.2 with
        | some j => X.p.lowBlocks n j
        | none => X.p.usedBlocks n := by
  cases htype : c.2.2.2 with
  | some j =>
    simp only [Setup5.refSubsetOn, htype, Params5.typeBlocks]
    refine ⟨fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
    exact card_fin_prefix (by
      simpa [Params5.typeBlocks, htype] using Lane_sol_s05_hist1b.typeBlocks_le_blockBound X c.2)
  | none =>
    let hits := match opt with
      | some (.inl k) => X.hitSet a c (X.lowCol H.2 k)
      | _ => X.poolIdx
    have hhit : hits ⊆ X.poolIdx := by
      cases opt with
      | none => exact fun i hi => hi
      | some key =>
        cases key with
        | inr k => exact fun i hi => hi
        | inl k => exact Finset.filter_subset _ _
    let S := if X.p.usedBlocks n ≤ hits.card then hits else X.poolIdx
    have hS : S ⊆ X.poolIdx := by
      dsimp [S]
      split_ifs
      · exact hhit
      · exact fun i hi => hi
    have hlen : X.p.usedBlocks n ≤ S.card := by
      dsimp [S]
      split_ifs with h
      · exact h
      · rw [poolIdx_card]
        exact usedBlocks_le_poolBlocks X
    simp only [Setup5.refSubsetOn, htype]
    change (∀ j ∈ X.firstK S (X.p.usedBlocks n), (j : ℕ) < X.p.typeBlocks n c.2) ∧
      (X.firstK S (X.p.usedBlocks n)).card = X.p.usedBlocks n
    constructor
    · intro i hi
      have hipool := hS (Finset.mem_filter.mp hi).1
      have hibound := (Finset.mem_filter.mp hipool).2
      simpa [Params5.typeBlocks, htype] using hibound
    · rw [Lane_sol_s05_1f.firstK_card, Nat.min_eq_left hlen]

theorem blockIdx_some_iff (K : X.Ty) (j : Fin X.blockBound) (i : Fin (X.p.typeBlocks n K)) :
    X.blockIdx K j = some i ↔ j.val = i.val := by
  unfold Setup5.blockIdx
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
  · have hne : j.val ≠ i.val := by omega
    simp [hne]

theorem reference_indices_card (K : X.Ty) (M : Finset (Fin X.blockBound))
    (hM : ∀ j ∈ M, (j : ℕ) < X.p.typeBlocks n K) :
    (Finset.univ.filter fun i : Fin (X.p.typeBlocks n K) => ∃ j ∈ M, X.blockIdx K j = some i).card =
      M.card := by
  let A := Finset.univ.filter fun i : Fin (X.p.typeBlocks n K) => ∃ j ∈ M, X.blockIdx K j = some i
  let e : M ≃ A := {
    toFun j := ⟨⟨j.1.val, hM j.1 j.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      j.1, j.2, (blockIdx_some_iff X K j.1 _).mpr rfl⟩⟩
    invFun i := ⟨⟨i.1.val,
      (by obtain ⟨j, hj, he⟩ := (Finset.mem_filter.mp i.2).2
          have hev := (blockIdx_some_iff X K j i.1).mp he
          omega)⟩,
      (by obtain ⟨j, hj, he⟩ := (Finset.mem_filter.mp i.2).2
          have hev := (blockIdx_some_iff X K j i.1).mp he
          have heq : (⟨i.1.val, (by omega)⟩ : Fin X.blockBound) = j := Fin.ext hev.symm
          exact heq.symm ▸ hj)⟩
    left_inv := by intro j; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl }
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

theorem selected_ref_props {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (elig : X.CΩ h → h.hp.EligMap) (v : EvenRole5 n) (c : X.CRef h)
    (hc : X.evenRefOf elig H ω v = some c) :
    (∀ j ∈ c.2, (j : ℕ) < X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) ∧
      c.2.card = match (X.g.evenType (X.p.J n) v.1).2.2 with
        | some j => X.p.lowBlocks n j
        | none => X.p.usedBlocks n := by
  unfold Setup5.evenRefOf at hc
  obtain ⟨l, hl, he⟩ := Option.map_eq_some_iff.mp hc
  have heM : X.refSubset H ω v l = c.2 := congrArg Prod.snd he
  rw [← heM]
  exact refSubsetOn_props X H (Setup5.arraysOf ω)
    (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)

theorem high_used_length_lower (p : Params5 γ K' χ) (n : ℕ) (hm : 2 ≤ p.m n) :
    (p.m n : ℝ) ^ (1 / 200 : ℝ) ≤ (p.q0 * p.uStarSeg n * p.usedBlocks n : ℕ) := by
  have hu : 0 < p.uStarSeg n := Lane_sol_s05_h5l.uStarSeg_positive p n (by omega)
  have hd : 0 < (p.q0 : ℝ) * p.uStarSeg n := by exact_mod_cast Nat.mul_pos p.hq0.1 hu
  have hh : (p.m n : ℝ) ^ (1 / 200 : ℝ) / ((p.q0 : ℝ) * p.uStarSeg n) ≤ (p.usedBlocks n : ℝ) :=
    Nat.le_ceil _
  have hb := (div_le_iff₀ hd).mp hh
  push_cast
  nlinarith

theorem selected_ref_length_lower {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (elig : X.CΩ h → h.hp.EligMap) (v : EvenRole5 n) (c : X.CRef h)
    (hc : X.evenRefOf elig H ω v = some c) (hm : 2 ≤ X.p.m n) :
    min 1 X.p.K2 * (X.p.m n : ℝ) ^ (1 / 200 : ℝ) ≤
      (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) := by
  obtain ⟨_, hcard⟩ := selected_ref_props X H ω elig v c hc
  have hmR : (1 : ℝ) ≤ X.p.m n := by exact_mod_cast (show 1 ≤ X.p.m n by omega)
  have hpow : (X.p.m n : ℝ) ^ (1 / 200 : ℝ) ≤ (X.p.m n : ℝ) ^ (1 / 50 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  unfold Setup5.refLen Params5.typeSegs
  cases htype : (X.g.evenType (X.p.J n) v.1).2.2 with
  | none =>
    rw [htype] at hcard
    simp only at hcard
    rw [hcard]
    have hl := high_used_length_lower X.p n hm
    have heq : X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) =
        X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n := by ring
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (min_le_left 1 X.p.K2) (Real.rpow_nonneg (by positivity) _)).trans
      (by simpa using hl)
  | some j =>
    rw [htype] at hcard
    simp only at hcard
    rw [hcard]
    have hl := Lane_sol_s05_h5l.low_length_lower X.p n j.val (by omega)
    have hlog : 0 ≤ Real.log (X.p.m n : ℝ) := Real.log_nonneg hmR
    have hmin0 : 0 ≤ min 1 X.p.K2 := le_min (by norm_num) X.p.hK2.le
    have h1 := mul_le_mul_of_nonneg_right (min_le_right 1 X.p.K2)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ X.p.m n) (1 / 200 : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hpow X.p.hK2.le
    have heq : X.p.lowBlocks n j * (X.p.q0 * X.p.uSeg n j) =
        X.p.q0 * X.p.uSeg n j * X.p.lowBlocks n j := by ring
    rw [heq]
    exact (h1.trans h2).trans (by
      have hpos : 0 ≤ X.p.K2 * (((j.val : ℝ) + 4) * Real.log (X.p.m n : ℝ)) :=
        mul_nonneg X.p.hK2.le (mul_nonneg (by positivity) hlog)
      nlinarith)

theorem eventual_ref_length_threshold (p : Params5 γ K' χ) (C : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ p.m n ∧ C ≤ min 1 p.K2 * (p.m n : ℝ) ^ (1 / 200 : ℝ) := by
  have hcoef : 0 < min 1 p.K2 := lt_min (by norm_num) p.hK2
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
    (Lane_sol_s05_h1.tendsto_m p)
  have hlarge := (hp.const_mul_atTop hcoef).eventually_ge_atTop C
  filter_upwards [(Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2, hlarge] with n hm hn
  exact ⟨by exact_mod_cast hm, hn⟩

end
end HypercubeRamsey.Lane_sol_s05_even
