import HypercubeRamsey.S05.Even_scales_sol_s05_even
import HypercubeRamsey.S05.History_sol_s05_1f

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem highCost_nonneg {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (R : X.OddOut → ℝ) (o : X.OddOut) :
    0 ≤ X.highCost H r a c R o := by
  unfold Setup5.highCost
  split <;> simp only [le_max_left, le_refl]

theorem smooth_lower (Q : Law N) (y : Fin N) :
    1 / (2 * (N : ℝ)) ≤ (X.smooth Q).w y := by
  change 1 / (2 * (N : ℝ)) ≤ (Q.w y + (N : ℝ)⁻¹) / 2
  rw [show 1 / (2 * (N : ℝ)) = (N : ℝ)⁻¹ / 2 by ring]
  gcongr
  exact le_add_of_nonneg_left (Q.nonneg y)

theorem highCost_upper {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (R : X.OddOut → ℝ)
    (hs : 0 < X.p.s n) (hD : 0 ≤ X.p.DH n)
    (hR : ∀ o, 0 ≤ R o)
    (hcap : ∀ o, R o ≤ 2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N))
    (o : X.OddOut) : X.highCost H r a c R o ≤ X.p.DH n + Real.log 4 := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos X.y₀
  have hsR : 0 < (X.p.s n : ℝ) := by exact_mod_cast hs
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  unfold Setup5.highCost
  split
  · rename_i h hi
    apply max_le (by linarith)
    by_cases hzero : R o = 0
    · simp only [hzero, zero_div, Real.log_zero]
      linarith
    · have hRpos : 0 < R o := lt_of_le_of_ne (hR o) (Ne.symm hzero)
      have hQ := smooth_lower X
        (X.condCoord (X.step3PostOn H r a (some c)) (H.2 r.1) h) o.2
      change 1 / (2 * (N : ℝ)) ≤ (X.highDeleted H r a c h).w o.2 at hQ
      have hQpos : 0 < (X.highDeleted H r a c h).w o.2 :=
        lt_of_lt_of_le (by positivity) hQ
      have hden : 0 < (X.highDeleted H r a c h).w o.2 / (X.p.s n : ℝ) :=
        div_pos hQpos hsR
      have hratio : R o / ((X.highDeleted H r a c h).w o.2 / (X.p.s n : ℝ)) ≤
          4 * Real.exp (X.p.DH n) := by
        apply (div_le_iff₀ hden).mpr
        refine (hcap o).trans ?_
        have hmult := mul_le_mul_of_nonneg_left hQ (by positivity : 0 ≤ 4 * Real.exp (X.p.DH n))
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hsR).mpr
        calc
          2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N) * (X.p.s n : ℝ) =
              4 * Real.exp (X.p.DH n) * (1 / (2 * (N : ℝ))) := by
                field_simp
                <;> ring
          _ ≤ 4 * Real.exp (X.p.DH n) * (X.highDeleted H r a c h).w o.2 := hmult
      calc
        Real.log (R o / ((X.highDeleted H r a c h).w o.2 / (X.p.s n : ℝ))) ≤
            Real.log (4 * Real.exp (X.p.DH n)) :=
              Real.log_le_log (div_pos hRpos hden) hratio
        _ = X.p.DH n + Real.log 4 := by
          rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
          ring
  · linarith

theorem high_ref_length_le {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (v : EvenRole5 n) (c : X.CRef h) (elig : X.CΩ h → h.hp.EligMap)
    (hv : ¬ X.g.low (X.p.J n) v.1)
    (hc : X.evenRefOf elig H ω v = some c) :
    X.refLen (X.g.evenType (X.p.J n) v.1) c.2 ≤
      X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n := by
  have htype : (X.g.evenType (X.p.J n) v.1).2.2 = none := by
    simp [ChunkGeometry5.evenType, ChunkGeometry5.low] at hv ⊢
    simp [hv]
  unfold Setup5.evenRefOf at hc
  obtain ⟨l, hl, he⟩ := Option.map_eq_some_iff.mp hc
  have heM : X.refSubset H ω v l = c.2 := congrArg Prod.snd he
  rw [← heM]
  unfold Setup5.refLen Setup5.refSubset Setup5.refSubsetOn
  rw [htype]
  simp only [Params5.typeSegs, htype]
  rw [Lane_sol_s05_1f.firstK_card]
  calc
    min (X.p.usedBlocks n) _ * (X.p.q0 * X.p.uStarSeg n) ≤
        X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) :=
          Nat.mul_le_mul_right _ (Nat.min_le_left _ _)
    _ = _ := by simp [Nat.mul_comm, Nat.mul_assoc]

theorem selected_ref_mem {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h)
    (elig : X.CΩ h → h.hp.EligMap)
    (hadj : (cube n).Adj v.1 b.1)
    (hv : ¬ X.g.low (X.p.J n) v.1) (hb : ¬ X.g.low (X.p.J n) b.1)
    (hcover : X.g.roleKey (X.p.J n) b.1 ∈ X.g.typeKeys (X.p.J n) v.1 ∨
      X.g.optionalKey (X.p.J n) v.1 = some (X.g.roleKey (X.p.J n) b.1))
    (hc : X.evenRefOf elig H ω v = some c) :
    (c.1, X.g.evenType (X.p.J n) v.1, c.2) ∈
      X.refsOn H (X.actualRecord elig H ω b) (Setup5.arraysOf ω) := by
  letI : DecidableEq (X.Ty × Finset (Fin X.blockBound)) := Classical.decEq _
  simp only [ChunkGeometry5.low] at hv hb
  have hmode : (X.g.roleKey (X.p.J n) b.1).isLeft =
      (X.g.evenType (X.p.J n) v.1).2.2.isSome := by
    simp [ChunkGeometry5.roleKey, ChunkGeometry5.evenType, hv, hb]
  have hkey : X.g.roleKey (X.p.J n) b.1 ∈ (X.g.evenType (X.p.J n) v.1).2.1 := by
    rcases hcover with hkey | hopt
    · exact hkey
    · have hrole : X.g.roleKey (X.p.J n) b.1 = .inr (X.g.key b.1) := by
        simp only [ChunkGeometry5.roleKey, dif_neg hb]
      rw [hrole] at hopt
      unfold ChunkGeometry5.optionalKey at hopt
      split at hopt <;> simp at hopt
  unfold Setup5.evenRefOf at hc
  obtain ⟨l, hl, he⟩ := Option.map_eq_some_iff.mp hc
  have hsel : X.selAt elig ω h.hp.Rlong v = some l := hl
  have hnb : v ∈ Setup5.evenNbrs b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
  unfold Setup5.refsOn
  apply Finset.mem_image.mpr
  refine ⟨(l, X.g.evenType (X.p.J n) v.1, X.g.optionalKey (X.p.J n) v.1), ?_, ?_⟩
  · change _ ∈ (Setup5.evenNbrs b).biUnion _
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hnb, ?_⟩
    simp [hsel, hkey, hmode]
  · rw [← he]
    rfl

theorem odd_label_cap {L : X.CentreLayer5} {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
    (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n) (hb : L.valid H ω b)
    (hs : 0 < X.p.s n) (x : Fin N) :
    labMarg (X.oddRowFP LR HR H ω b) Prod.snd x ≤
      (Real.exp (X.p.DL n) + 2 * Real.exp (X.p.DH n)) / (N : ℝ) := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos X.y₀
  have hsR : 0 < (X.p.s n : ℝ) := by exact_mod_cast hs
  have hLR : (∑ i : Fin (X.p.s n + 1), LR.row H ω b (i, x)) = LR.row H ω b (0, x) := by
    apply Finset.sum_eq_single 0
    · intro i hi hi0
      exact LR.row_index H ω b (i, x) (by simpa using hi0)
    · simp
  have hHR : (∑ i : Fin (X.p.s n + 1), HR.row H ω b (i, x)) ≤
      2 * Real.exp (X.p.DH n) / (N : ℝ) := by
    rw [Fin.sum_univ_castSucc]
    have hlast := HR.row_index H ω b (Fin.last (X.p.s n), x) (by simp)
    rw [hlast, add_zero]
    calc
      (∑ i : Fin (X.p.s n), HR.row H ω b (i.castSucc, x)) ≤
          ∑ _i : Fin (X.p.s n), 2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N) :=
        Finset.sum_le_sum fun i _ => HR.row_cap H ω b (i.castSucc, x)
      _ = 2 * Real.exp (X.p.DH n) / (N : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  unfold labMarg
  simp only [Setup5.oddRowFP, dif_pos hb]
  rw [Fintype.sum_prod_type]
  simp only [Prod.snd, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Setup5.oddRow, Finset.sum_add_distrib]
  rw [hLR]
  have hlow : LR.row H ω b (0, x) ≤ Real.exp (X.p.DL n) / (N : ℝ) :=
    (le_div_iff₀ hN).mpr (by simpa [mul_comm] using LR.row_cap H ω b (0, x))
  calc
    _ ≤ Real.exp (X.p.DL n) / (N : ℝ) + 2 * Real.exp (X.p.DH n) / (N : ℝ) := add_le_add hlow hHR
    _ = _ := by ring

theorem odd_atom_bound {L : X.CentreLayer5} {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
    (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n) (hb : L.valid H ω b)
    (A : ℝ) (hn : 1 ≤ n) (hm : 2 ≤ X.p.m n) (hNlow : 2 ^ n ≤ N)
    (hexp : Real.log 3 + capCoeff X.p * (n : ℝ) ^ (1 / 4 : ℝ) + A * Real.log (n : ℝ) ≤
      (n : ℝ) * Real.log 2) (x : Fin N) :
    labMarg (X.oddRowFP LR HR H ω b) Prod.snd x ≤ (n : ℝ) ^ (-A) := by
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos X.y₀
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hs, hk⟩ := high_lengths_positive X.p n hm
  obtain ⟨hDL, hDH⟩ := capCoeff_bounds X.p n hn (by omega)
  have hlog4 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  have hDH' : X.p.DH n ≤ capCoeff X.p * (n : ℝ) ^ (1 / 4 : ℝ) := by linarith
  have hpow : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine (odd_label_cap X LR HR H ω b hb hs x).trans ?_
  apply (div_le_iff₀ hN).mpr
  calc
    Real.exp (X.p.DL n) + 2 * Real.exp (X.p.DH n) ≤
        3 * Real.exp (capCoeff X.p * (n : ℝ) ^ (1 / 4 : ℝ)) := by
      have h1 := Real.exp_le_exp.mpr hDL
      have h2 := Real.exp_le_exp.mpr hDH'
      linarith
    _ = Real.exp (Real.log 3 + capCoeff X.p * (n : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ Real.exp ((n : ℝ) * Real.log 2 - A * Real.log (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = (n : ℝ) ^ (-A) * (2 : ℝ) ^ n := by
      rw [sub_eq_add_neg, Real.exp_add, hpow, Real.rpow_def_of_pos hn0]
      rw [mul_comm]
      congr 1
      congr 1
      ring
    _ ≤ (n : ℝ) ^ (-A) * (N : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
      exact_mod_cast hNlow

end
end HypercubeRamsey.Lane_sol_s05_even
