import Mathlib

namespace HypercubeRamsey.Lane_sol_s15_mask

open Classical
open scoped BigOperators

theorem sum_split_coordinate {ι U : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype U] (r : ι) (F : (ι → U) → ℝ) :
    (∑ vs, F vs) = ∑ zs : ({t : ι // t ≠ r} → U),
      ∑ u : U, F ((Equiv.funSplitAt r U).symm (u, zs)) := by
  calc
    (∑ vs, F vs) = ∑ p : U × ({t : ι // t ≠ r} → U),
        F ((Equiv.funSplitAt r U).symm p) :=
      Fintype.sum_equiv (Equiv.funSplitAt r U) _ _
        (fun vs => congrArg F ((Equiv.funSplitAt r U).symm_apply_apply vs).symm)
    _ = ∑ u : U, ∑ zs : ({t : ι // t ≠ r} → U),
        F ((Equiv.funSplitAt r U).symm (u, zs)) := Fintype.sum_prod_type _
    _ = _ := Finset.sum_comm

theorem split_coordinate_update {ι U : Type*} [DecidableEq ι]
    (r : ι) (zs : {t : ι // t ≠ r} → U) (u u₀ : U) :
    (Equiv.funSplitAt r U).symm (u, zs) =
      Function.update ((Equiv.funSplitAt r U).symm (u₀, zs)) r u := by
  funext t
  by_cases ht : t = r <;> simp [Equiv.funSplitAt, Equiv.piSplitAt, ht]

theorem restrict_one_coordinate {ι U : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype U] [Nonempty U] (r : ι) (A : (ι → U) → Prop)
    (F : (ι → U) → ℝ) (hF0 : ∀ vs, 0 ≤ F vs)
    (hF : ∀ vs u, F (Function.update vs r u) = F vs)
    (p : ℝ)
    (hA : ∀ vs, ((Finset.univ.filter fun u => A (Function.update vs r u)).card : ℝ) ≤
      p * Fintype.card U) :
    (∑ vs, if A vs then F vs else 0) ≤ p * ∑ vs, F vs := by
  let u₀ : U := Classical.choice inferInstance
  rw [sum_split_coordinate r, sum_split_coordinate r, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro zs hzs
  let vs := (Equiv.funSplitAt r U).symm (u₀, zs)
  have heq (u : U) : (Equiv.funSplitAt r U).symm (u, zs) = Function.update vs r u :=
    split_coordinate_update r zs u u₀
  simp only [heq, hF]
  calc
    (∑ u : U, if A (Function.update vs r u) then F vs else 0) =
        ((Finset.univ.filter fun u => A (Function.update vs r u)).card : ℝ) * F vs := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (p * Fintype.card U) * F vs := mul_le_mul_of_nonneg_right (hA vs) (hF0 vs)
    _ = p * ∑ _u : U, F vs := by simp; ring

def EarlierNear {U : Type*} {n : ℕ} (near : U → U → Prop)
    (vs : Fin n → U) (r : Fin n) : Prop :=
  ∃ t, t < r ∧ near (vs t) (vs r)

def NecessaryNear {U : Type*} {n : ℕ} (near : U → U → Prop)
    (G : Finset (Fin n)) (vs : Fin n → U) : Prop :=
  ∀ r ∈ G, EarlierNear near vs r

theorem necessaryNear_erase_max_update {U : Type*} {n : ℕ}
    (near : U → U → Prop) (G : Finset (Fin n)) (r : Fin n)
    (hmax : ∀ t ∈ G, t ≤ r) (vs : Fin n → U) (u : U) :
    NecessaryNear near (G.erase r) (Function.update vs r u) ↔
      NecessaryNear near (G.erase r) vs := by
  have htne : ∀ t ∈ G.erase r, t ≠ r := fun t ht => (Finset.mem_erase.mp ht).1
  have hpred : ∀ t ∈ G.erase r, ∀ j, j < t → j ≠ r := by
    intro t ht j hj hjeq
    subst j
    exact (not_lt_of_ge (hmax t (Finset.mem_erase.mp ht).2)) hj
  constructor <;> intro h t ht <;> obtain ⟨j, hj, hn⟩ := h t ht <;>
    refine ⟨j, hj, ?_⟩
  · simpa only [Function.update_of_ne (htne t ht), Function.update_of_ne (hpred t ht j hj)] using hn
  · simpa only [Function.update_of_ne (htne t ht), Function.update_of_ne (hpred t ht j hj)] using hn

theorem necessaryNear_split {U : Type*} {n : ℕ} (near : U → U → Prop)
    (G : Finset (Fin n)) (r : Fin n) (hr : r ∈ G) (vs : Fin n → U) :
    NecessaryNear near G vs ↔
      NecessaryNear near (G.erase r) vs ∧ EarlierNear near vs r := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (Finset.mem_erase.mp ht).2, h r hr⟩
  · rintro ⟨h, hh⟩ t ht
    by_cases heq : t = r
    · simpa [heq] using hh
    · exact h t (Finset.mem_erase.mpr ⟨heq, ht⟩)

theorem earlier_near_count {U : Type*} [Fintype U] {n : ℕ}
    (near : U → U → Prop) (r : Fin n) (vs : Fin n → U)
    (f : ℝ) (hf : 0 ≤ f)
    (hnear : ∀ v, ((Finset.univ.filter (near v)).card : ℝ) ≤ f * Fintype.card U) :
    ((Finset.univ.filter fun u => EarlierNear near (Function.update vs r u) r).card : ℝ) ≤
        ((n : ℝ) * f) * Fintype.card U := by
  let I := Finset.univ.filter fun t : Fin n => t < r
  have hsub : (Finset.univ.filter fun u => EarlierNear near (Function.update vs r u) r) ⊆
      I.biUnion (fun t => Finset.univ.filter (near (vs t))) := by
    intro u hu
    obtain ⟨t, ht, hnear⟩ := (Finset.mem_filter.mp hu).2
    have htne : t ≠ r := ne_of_lt ht
    simp only [Function.update_of_ne htne, Function.update_self] at hnear
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩⟩
  calc
    _ ≤ ((I.biUnion (fun t => Finset.univ.filter (near (vs t)))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ t ∈ I, ((Finset.univ.filter (near (vs t))).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ I, f * Fintype.card U := Finset.sum_le_sum fun t ht => hnear (vs t)
    _ = (I.card : ℝ) * (f * Fintype.card U) := by simp
    _ ≤ (n : ℝ) * (f * Fintype.card U) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hf (Nat.cast_nonneg _))
      have hh : I.card ≤ n := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Finset.card_le_card (Finset.filter_subset (fun t : Fin n => t < r) Finset.univ))
      exact_mod_cast hh
    _ = _ := by ring

theorem reverse_near_sum {U : Type*} [Fintype U] [Nonempty U] {n : ℕ}
    (near : U → U → Prop) (G : Finset (Fin n))
    (F : (Fin n → U) → ℝ) (hF0 : ∀ vs, 0 ≤ F vs)
    (hF : ∀ r ∈ G, ∀ vs u, F (Function.update vs r u) = F vs)
    (f : ℝ) (hf : 0 ≤ f)
    (hnear : ∀ v, ((Finset.univ.filter (near v)).card : ℝ) ≤ f * Fintype.card U) :
    (∑ vs, if NecessaryNear near G vs then F vs else 0) ≤
      ((n : ℝ) * f) ^ G.card * ∑ vs, F vs := by
  classical
  revert F
  refine Finset.strongInductionOn G ?_
  intro G ih
  intro F hF0 hF
  by_cases hG : G.Nonempty
  · let r := G.max' hG
    have hr : r ∈ G := Finset.max'_mem _ _
    have hmax : ∀ t ∈ G, t ≤ r := fun t ht => Finset.le_max' _ t ht
    let F' := fun vs => if NecessaryNear near (G.erase r) vs then F vs else 0
    have hF'0 : ∀ vs, 0 ≤ F' vs := by intro vs; dsimp [F']; split_ifs <;> simp [hF0]
    have hF' : ∀ vs u, F' (Function.update vs r u) = F' vs := by
      intro vs u
      simp only [F', necessaryNear_erase_max_update near G r hmax, hF r hr]
    have hstep := restrict_one_coordinate r
      (fun vs => EarlierNear near vs r) F' hF'0 hF'
      ((n : ℝ) * f) (fun vs => earlier_near_count near r vs f hf hnear)
    have hprev := ih (G.erase r) (Finset.erase_ssubset hr) F hF0
      (fun t ht => hF t (Finset.mem_erase.mp ht).2)
    calc
      _ = ∑ vs, if EarlierNear near vs r then F' vs else 0 := by
        apply Finset.sum_congr rfl
        intro vs hvs
        rw [necessaryNear_split near G r hr]
        dsimp [F']
        split_ifs <;> simp_all
      _ ≤ ((n : ℝ) * f) * ∑ vs, F' vs := hstep
      _ ≤ ((n : ℝ) * f) * (((n : ℝ) * f) ^ (G.erase r).card * ∑ vs, F vs) :=
        mul_le_mul_of_nonneg_left hprev (mul_nonneg (Nat.cast_nonneg _) hf)
      _ = _ := by
        rw [Finset.card_erase_of_mem hr, ← mul_assoc, ← pow_succ']
        have hcard : G.card - 1 + 1 = G.card := Nat.sub_add_cancel (Finset.card_pos.mpr hG)
        rw [hcard]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hG, NecessaryNear]

theorem weighted_rank_moment {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (r : Ω → ℕ) (n : ℕ)
    (hr : ∀ ω, r ω ≤ n) (a t : ℝ) (ha : 0 ≤ a)
    (htail : ∀ j ≤ n, (∑ ω, w ω * (if j ≤ r ω then 1 else 0)) ≤ t ^ j) :
    (∑ ω, w ω * a ^ r ω) ≤ ∑ j ∈ Finset.range (n + 1), (a * t) ^ j := by
  have hpoint (ω : Ω) : a ^ r ω ≤
      ∑ j ∈ Finset.range (n + 1), a ^ j * (if j ≤ r ω then 1 else 0) := by
    have hh := Finset.single_le_sum (f := fun j => a ^ j * (if j ≤ r ω then (1 : ℝ) else 0))
      (fun j hj => mul_nonneg (pow_nonneg ha _) (by split_ifs <;> norm_num))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hr ω)))
    simpa using hh
  calc
    (∑ ω, w ω * a ^ r ω) ≤
        ∑ ω, w ω * ∑ j ∈ Finset.range (n + 1), a ^ j * (if j ≤ r ω then 1 else 0) :=
      Finset.sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left (hpoint ω) (hw ω)
    _ = ∑ j ∈ Finset.range (n + 1), a ^ j *
        ∑ ω, w ω * (if j ≤ r ω then 1 else 0) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), a ^ j * t ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (htail j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        (pow_nonneg ha _)
    _ = _ := by simp only [mul_pow]

theorem geometric_sum_le_two (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ j) ≤ 2 := by
  have hstrong : ∀ m : ℕ, (∑ j ∈ Finset.range m, q ^ j) ≤ 2 * (1 - q ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hh := mul_le_mul_of_nonneg_right hq (pow_nonneg hq0 m)
      nlinarith
  have hn := hstrong n
  have hpow := pow_nonneg hq0 n
  linarith

end HypercubeRamsey.Lane_sol_s15_mask
