import HypercubeRamsey.S05.Even_setup_geometry_sol_s05_even
import HypercubeRamsey.S05.Even_setup_laws_sol_s05_even
import HypercubeRamsey.S05.Even_scales_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def oppositeStar (v : EvenRole5 n) : Finset (OddRole5 n) :=
  (oddAdjSet5 v).filter fun b => ¬ (X.g.low (X.p.J n) v.1 ↔ X.g.low (X.p.J n) b.1)

theorem oppositeStar_card (v : EvenRole5 n) :
    ((oppositeStar X v).card : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
  let D := (Finset.univ.biUnion X.g.coarseChunks) ∪ (Finset.univ.biUnion X.g.fineChunks)
  have hsub : (oppositeStar X v).image (fun b => b.1) ⊆ D.image (flipVertex5 v.1) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hmode⟩ := Finset.mem_filter.mp hb
    have hadj := (Finset.mem_filter.mp ha).2
    obtain ⟨i, hi⟩ := Lane_sol_s05_h5l.adjacent_flip v.1 b.1 hadj
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi.symm⟩
    by_contra hnot
    have hnotfine (j : Fin (X.p.m n)) : i ∉ X.g.fineChunks j := by
      intro hj
      apply hnot
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
    have hcounts (j : Fin (X.p.m n)) : X.g.fineCount b.1 j = X.g.fineCount v.1 j := by
      rw [hi]
      exact Lane_sol_s05_h5l.fineCount_flip_outside X.g v.1 i j (hnotfine j)
    have hsev : X.g.severity b.1 = X.g.severity v.1 := by
      unfold ChunkGeometry5.severity
      simp_rw [hcounts]
    apply hmode
    change X.g.severity v.1 ≤ X.p.J n ↔ X.g.severity b.1 ≤ X.p.J n
    rw [hsev]
  have hinj : Function.Injective (fun b : OddRole5 n => b.1) := Subtype.val_injective
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ hinj] at hcard
  exact (by exact_mod_cast hcard : ((oppositeStar X v).card : ℝ) ≤ D.card).trans X.g.occupied_sublinear

def oppositeCost : ℝ := X.p.DL n + X.p.DH n + (X.p.s n + 1 : ℕ) + Real.log 4

theorem uniformOdd_weight (o : X.OddOut) :
    (uniformOdd X).w o = ((X.p.s n + 1 : ℕ) * (N : ℝ))⁻¹ := by
  simp [uniformOdd, FinProb.uniformAll, Fintype.card_prod]

theorem uniformOdd_dominates_row (L : X.CentreLayer5) {cL cH : ℝ} (LR : X.LowRows5 L cL cH)
    (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n)
    (hs : 0 < X.p.s n) (hD : 0 ≤ X.p.DH n) (o : X.OddOut) :
    X.oddRow LR HR H ω b o ≤ Real.exp (oppositeCost X) * (uniformOdd X).w o := by
  have hN : (0 : ℝ) < N := by
    have hy := X.y₀.isLt
    exact_mod_cast (show 0 < N by omega)
  have hs1 : (1 : ℝ) ≤ X.p.s n := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < (X.p.s n + 1 : ℕ) := by positivity
  have hDL : 0 ≤ X.p.DL n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hexp : 4 * (X.p.s n + 1 : ℕ) * Real.exp (X.p.DL n + X.p.DH n) ≤
      Real.exp (oppositeCost X) := by
    have he : Real.exp (oppositeCost X) =
        Real.exp (X.p.DL n + X.p.DH n) * Real.exp ((X.p.s n + 1 : ℕ) : ℝ) * 4 := by
      unfold oppositeCost
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      rw [Real.exp_add]
    rw [he]
    have hS : ((X.p.s n + 1 : ℕ) : ℝ) ≤ Real.exp ((X.p.s n + 1 : ℕ) : ℝ) :=
      (by linarith [Real.add_one_le_exp ((X.p.s n + 1 : ℕ) : ℝ)])
    convert mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 4 * Real.exp (X.p.DL n + X.p.DH n)) using 1 <;> ring
  have hlabel : X.oddRow LR HR H ω b o ≤ 4 * Real.exp (X.p.DL n + X.p.DH n) / N := by
    by_cases hl : X.g.low (X.p.J n) b.1
    · rw [Setup5.oddRow, HR.row_low H ω b o hl, add_zero]
      apply (le_div_iff₀ hN).mpr
      have hcap := LR.row_cap H ω b o
      have he : Real.exp (X.p.DL n) ≤ Real.exp (X.p.DL n + X.p.DH n) := Real.exp_le_exp.mpr (by linarith)
      nlinarith [Real.exp_pos (X.p.DL n + X.p.DH n)]
    · rw [Setup5.oddRow, LR.row_high H ω b o hl, zero_add]
      calc
        _ ≤ 2 * Real.exp (X.p.DH n) / ((X.p.s n : ℝ) * N) := HR.row_cap H ω b o
        _ ≤ 2 * Real.exp (X.p.DH n) / N := by
          apply div_le_div_of_nonneg_left (by positivity) hN
          nlinarith
        _ ≤ 4 * Real.exp (X.p.DL n + X.p.DH n) / N := by
          apply div_le_div_of_nonneg_right _ hN.le
          have he : Real.exp (X.p.DH n) ≤ Real.exp (X.p.DL n + X.p.DH n) :=
            Real.exp_le_exp.mpr (by linarith)
          nlinarith [Real.exp_pos (X.p.DL n + X.p.DH n)]
  rw [uniformOdd_weight]
  apply hlabel.trans
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (mul_pos hs0 hN)).mpr
  have heq : 4 * Real.exp (X.p.DL n + X.p.DH n) / (N : ℝ) *
      ((X.p.s n + 1 : ℕ) * (N : ℝ)) = 4 * (X.p.s n + 1 : ℕ) * Real.exp (X.p.DL n + X.p.DH n) := by
    field_simp
    <;> ring
  rw [heq]
  exact hexp

end
end HypercubeRamsey.Lane_sol_s05_even
