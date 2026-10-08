import HypercubeRamsey.S15.ClusterProductAvoid_sol_s15_c2
import HypercubeRamsey.S15.ClusterNodes_q_s15_c1

namespace HypercubeRamsey.Lane_sol_s15_c2

open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem touching_charge_sum_le {R I : Type*} [DecidableEq R] [Fintype I] [DecidableEq I]
    (scope : I → Finset R) (x : I → ℝ) (δ : ℝ) (hx : ∀ i, 0 ≤ x i)
    (htouch : ∀ r, (∑ i ∈ Finset.univ.filter (fun i => r ∈ scope i), x i) ≤ δ)
    (S : Finset R) :
    (∑ i ∈ Finset.univ.filter (fun i => ¬ Disjoint S (scope i)), x i) ≤ (S.card : ℝ) * δ := by
  let T := Finset.univ.filter fun i => ¬ Disjoint S (scope i)
  have hpoint (i) (hi : i ∈ T) : x i ≤ ∑ r ∈ S, if r ∈ scope i then x i else 0 := by
    obtain ⟨r, hr, hri⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
    have h := Finset.single_le_sum (s := S) (f := fun r => if r ∈ scope i then x i else 0)
      (fun r _ => by split_ifs; exact hx i; exact le_rfl) hr
    simpa only [if_pos hri] using h
  calc
    _ ≤ ∑ i ∈ T, ∑ r ∈ S, if r ∈ scope i then x i else 0 := Finset.sum_le_sum hpoint
    _ ≤ ∑ i : I, ∑ r ∈ S, if r ∈ scope i then x i else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        (fun i _ _ => Finset.sum_nonneg fun r _ => by split_ifs; exact hx i; exact le_rfl)
    _ = ∑ r ∈ S, ∑ i : I, if r ∈ scope i then x i else 0 := Finset.sum_comm
    _ = ∑ r ∈ S, ∑ i ∈ Finset.univ.filter (fun i => r ∈ scope i), x i := by
      simp_rw [← Finset.sum_filter]
    _ ≤ ∑ _r ∈ S, δ := Finset.sum_le_sum fun r _ => htouch r
    _ = _ := by simp

theorem exp_neg_twice_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hden : 0 < 1 + 2 * x := by linarith
  have hsq : x * x ≤ x / 2 := by nlinarith only [mul_le_mul_of_nonneg_right hx1 hx0]
  have hInv : 1 / (1 + 2 * x) ≤ 1 - x := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hsq, hx0]
  calc
    Real.exp (-2 * x) = 1 / Real.exp (2 * x) := by
      rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, one_div]
    _ ≤ 1 / (1 + 2 * x) := one_div_le_one_div_of_le hden
      (by simpa [add_comm] using Real.add_one_le_exp (2 * x))
    _ ≤ _ := hInv

theorem product_one_sub_exp_lower {I : Type*} [DecidableEq I]
    (S : Finset I) (x : I → ℝ) (hx0 : ∀ i ∈ S, 0 ≤ x i) (hx1 : ∀ i ∈ S, x i ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ S, x i) ≤ ∏ i ∈ S, (1 - x i) := by
  have h := Finset.prod_le_prod₀ (s := S) (f := fun i => Real.exp (-2 * x i))
    (g := fun i => 1 - x i) (fun i _ => (Real.exp_pos _).le)
    (fun i hi => exp_neg_twice_le_one_sub (hx0 i hi) (hx1 i hi))
  rw [← Real.exp_sum] at h
  have hsum : (∑ i ∈ S, -2 * x i) = -2 * ∑ i ∈ S, x i := by rw [Finset.mul_sum]
  rwa [hsum] at h

theorem charge_budget_LLL {R I : Type*} [DecidableEq R] [Fintype I] [DecidableEq I]
    (scope : I → Finset R) (x p : I → ℝ) (δ : ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1 / 2)
    (htouch : ∀ r, (∑ i ∈ Finset.univ.filter (fun i => r ∈ scope i), x i) ≤ δ)
    (hraw : ∀ i, p i ≤ x i * Real.exp (-2 * δ * (scope i).card)) :
    ∀ i, p i ≤ x i *
      ∏ j ∈ Finset.univ.filter (fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)), (1 - x j) := by
  intro i
  let N := Finset.univ.filter fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)
  let T := Finset.univ.filter fun j => ¬ Disjoint (scope i) (scope j)
  have hsub : N ⊆ T := by intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩
  have hsum : (∑ j ∈ N, x j) ≤ (scope i).card * δ :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hx0 j)).trans
      (touching_charge_sum_le scope x δ hx0 htouch (scope i))
  have hprod := product_one_sub_exp_lower N x (fun j _ => hx0 j) (fun j _ => hx1 j)
  calc
    p i ≤ x i * Real.exp (-2 * δ * (scope i).card) := hraw i
    _ ≤ x i * Real.exp (-2 * ∑ j ∈ N, x j) := by
      apply mul_le_mul_of_nonneg_left _ (hx0 i)
      apply Real.exp_le_exp.mpr
      nlinarith only [hsum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (hx0 i)

theorem charge_budget_query_comparison {R I : Type*} [DecidableEq R] [Fintype I] [DecidableEq I]
    (scope : I → Finset R) (x : I → ℝ) (δ n : ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (htouch : ∀ r, (∑ i ∈ Finset.univ.filter (fun i => r ∈ scope i), x i) ≤ δ)
    (hbudget : n ^ 3 * δ ≤ 1 / (2 * n)) :
    ∀ S : Finset R, (S.card : ℝ) ≤ n ^ 3 →
      (∏ i ∈ Finset.univ.filter (fun i => ¬ Disjoint S (scope i)), (1 - x i))⁻¹ ≤ 1 + 1 / n := by
  intro S hS
  let T := Finset.univ.filter fun i => ¬ Disjoint S (scope i)
  have hnpos : 0 < n := by linarith
  have hsum : (∑ i ∈ T, x i) ≤ 1 / (2 * n) :=
    (touching_charge_sum_le scope x δ hx0 htouch S).trans
      ((mul_le_mul_of_nonneg_right hS hδ).trans hbudget)
  have hprod := Lane_q_s15_c1.clusterProd_one_sub_lower T x (fun i _ => hx0 i) (fun i _ => (hx1 i).le)
  have hpos : 0 < ∏ i ∈ T, (1 - x i) := Finset.prod_pos fun i _ => sub_pos.mpr (hx1 i)
  have hC : 0 < 1 + 1 / n := by positivity
  have hsimple : (1 + 1 / n)⁻¹ ≤ 1 - 1 / (2 * n) := by
    field_simp [hnpos.ne', hC.ne']
    nlinarith only [hn]
  have hlow : (1 + 1 / n)⁻¹ ≤ ∏ i ∈ T, (1 - x i) :=
    hsimple.trans ((sub_le_sub_left hsum 1).trans hprod)
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hpos).2
  have hmul := mul_le_mul_of_nonneg_right hlow hC.le
  rw [inv_mul_cancel₀ hC.ne'] at hmul
  simpa only [mul_comm] using hmul

end HypercubeRamsey.Lane_sol_s15_c2
