import HypercubeRamsey.S16.Producers_sol_s16_prod1
namespace HypercubeRamsey.S16.Lane_sol_s16_prod1
open Classical
open scoped BigOperators

/-- Counting each image once is dominated by counting every slot. -/
theorem image_product_le_slot_product7 {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    [Fintype Bin] [DecidableEq Bin] (P : Index → FinLaw Bin)
    (F : (Index → Bin) → ℝ) (hF : ∀ a, 0 ≤ F a) (pool : Slot → Bin) :
    (∑ a : Index → Bin, F a * ∏ i,
      if a i ∈ Finset.univ.image pool then (P i).w (a i) else 0) ≤
    ∑ indices : Index → Slot, F (fun i => pool (indices i)) * ∏ i, (P i).w (pool (indices i)) := by
  classical
  let A : Finset (Index → Bin) := Finset.univ.filter fun a => ∀ i, a i ∈ Finset.univ.image pool
  let pick : Bin → Slot := fun b => if hb : b ∈ Finset.univ.image pool then
    Classical.choose (Finset.mem_image.mp hb) else Classical.choice inferInstance
  have hpick : ∀ b ∈ Finset.univ.image pool, pool (pick b) = b := by
    intro b hb
    simp only [pick, dif_pos hb]
    exact (Classical.choose_spec (Finset.mem_image.mp hb)).2
  let lift : (Index → Bin) → (Index → Slot) := fun a i => pick (a i)
  have hlift : ∀ a ∈ A, (fun i => pool (lift a i)) = a := by
    intro a ha
    funext i
    exact hpick (a i) ((Finset.mem_filter.mp ha).2 i)
  have hinj : Set.InjOn lift A := by
    intro a ha b hb heq
    calc
      a = (fun i => pool (lift a i)) := (hlift a ha).symm
      _ = (fun i => pool (lift b i)) := by rw [heq]
      _ = b := hlift b hb
  have hzero : ∀ a, (∏ i, if a i ∈ Finset.univ.image pool then (P i).w (a i) else 0) =
      if a ∈ A then ∏ i, (P i).w (a i) else 0 := by
    intro a
    by_cases ha : a ∈ A
    · rw [if_pos ha]
      apply Finset.prod_congr rfl
      intro i _
      exact if_pos ((Finset.mem_filter.mp ha).2 i)
    · rw [if_neg ha]
      have hex : ∃ i, a i ∉ Finset.univ.image pool := by simpa [A, not_forall] using ha
      obtain ⟨i, hi⟩ := hex
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simp_rw [hzero, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun a : Index → Bin => a ∈ A) = A := by
    ext a
    simp
  rw [hfilter]
  apply Finset.sum_le_sum_of_injOn lift hinj (Finset.subset_univ _)
  · intro a ha
    have hh : ∀ i, pool (lift a i) = a i := fun i => congrFun (hlift a ha) i
    simp_rw [hh]
    exact le_rfl
  · intro indices _ _
    exact mul_nonneg (hF _) (Finset.prod_nonneg fun i _ => (P i).nonneg _)

/-- The weighted slot polynomial controls the image integral even for repetitions. -/
theorem image_product_le_empirical7 {Index Slot Bin : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Slot] [DecidableEq Slot] [Nonempty Slot]
    [Fintype Bin] [DecidableEq Bin] (P : Index → FinLaw Bin) (B : ℝ) (hB : 0 < B)
    (F : (Index → Bin) → ℝ) (hF : ∀ a, 0 ≤ F a) (pool : Slot → Bin) :
    (∑ a : Index → Bin, F a * ∏ i,
      if a i ∈ Finset.univ.image pool then (P i).w (a i) else 0) ≤
    ((Fintype.card Slot : ℝ) / B) ^ Fintype.card Index *
      empirical_statistic (empirical_weighted_kernel P B F) pool := by
  classical
  have hL : (0 : ℝ) < Fintype.card Slot := by exact_mod_cast Fintype.card_pos
  have heq : ((Fintype.card Slot : ℝ) / B) ^ Fintype.card Index *
      empirical_statistic (empirical_weighted_kernel P B F) pool =
      ∑ indices : Index → Slot, F (fun i => pool (indices i)) * ∏ i, (P i).w (pool (indices i)) := by
    unfold empirical_statistic empirical_weighted_kernel FinLaw.E FinLaw.pi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro indices _
    simp only [FinLaw.uniform, Finset.mem_univ, if_true, Finset.card_univ]
    have hprod : (∏ _i : Index, (1 / (Fintype.card Slot : ℝ))) *
        (∏ i : Index, B * (P i).w (pool (indices i))) =
        (B / (Fintype.card Slot : ℝ)) ^ Fintype.card Index * ∏ i, (P i).w (pool (indices i)) := by
      rw [← Finset.prod_mul_distrib]
      simp_rw [show ∀ i : Index, (1 / (Fintype.card Slot : ℝ)) *
        (B * (P i).w (pool (indices i))) = (B / (Fintype.card Slot : ℝ)) * (P i).w (pool (indices i)) by
          intro i; ring]
      rw [Finset.prod_mul_distrib]
      simp [div_pow]
    have hcancel : ((Fintype.card Slot : ℝ) / B) ^ Fintype.card Index *
        (B / (Fintype.card Slot : ℝ)) ^ Fintype.card Index = 1 := by
      rw [← mul_pow]
      have hh : ((Fintype.card Slot : ℝ) / B) * (B / (Fintype.card Slot : ℝ)) = 1 := by
        field_simp
      rw [hh, one_pow]
    rw [mul_left_comm (∏ _i : Index, 1 / (Fintype.card Slot : ℝ)), hprod]
    calc
      _ = (((Fintype.card Slot : ℝ) / B) ^ Fintype.card Index *
          (B / (Fintype.card Slot : ℝ)) ^ Fintype.card Index) *
          (F (fun i => pool (indices i)) * ∏ i, (P i).w (pool (indices i))) := by ring
      _ = _ := by rw [hcancel, one_mul]
  rw [heq]
  exact image_product_le_slot_product7 P F hF pool

end HypercubeRamsey.S16.Lane_sol_s16_prod1
