import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_rates
import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_analysis

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock Classical
open scoped BigOperators

theorem survival_product_le_exp {ι : Type*} [Fintype ι]
    (δ : ℝ) (r : ι → ℝ) (cut : ι → ℕ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    (∏ i, survival δ (r i) (cut i)) ≤ Real.exp (-δ * ∑ i, r i * (cut i : ℝ)) := by
  classical
  have hbase (i : ι) : 0 ≤ 1 - δ * r i :=
    sub_nonneg.mpr (mul_le_one₀ hδ1 (hr0 i) (hr1 i))
  calc
    _ ≤ ∏ i, Real.exp (-δ * r i * (cut i : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact pow_nonneg (hbase i) _
      · intro i _
        exact survival_le_exp hδ0 hδ1 (hr0 i) (hr1 i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem survival_product_le_one {ι : Type*} [Fintype ι]
    (δ : ℝ) (r : ι → ℝ) (cut : ι → ℕ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1) :
    (∏ i, survival δ (r i) (cut i)) ≤ 1 := by
  classical
  have hbase0 (i : ι) : 0 ≤ 1 - δ * r i :=
    sub_nonneg.mpr (mul_le_one₀ hδ1 (hr0 i) (hr1 i))
  have hbase1 (i : ι) : 1 - δ * r i ≤ 1 := sub_le_self _ (mul_nonneg hδ0 (hr0 i))
  calc
    _ ≤ ∏ _i : ι, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact pow_nonneg (hbase0 i) _
      · intro i _
        exact pow_le_one₀ (hbase0 i) (hbase1 i)
    _ = _ := by simp

private theorem finite_hazard_sum {T : ℕ} (q z : ℕ → ℝ) (θ : ℝ) (a : Fin T) :
    (∑ t : Fin T, if t.val < a.val then (q t.val + θ * z t.val) else 0) =
      ∑ t ∈ Finset.range a.val, (q t + θ * z t) := by
  classical
  change (∑ t : Fin T, (fun s : ℕ => if s < a.val then (q s + θ * z s) else 0) t.val) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ => if s < a.val then (q s + θ * z s) else 0) T, ← Finset.sum_filter]
  have hset : (Finset.range T).filter (fun t => t < a.val) = Finset.range a.val := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro ht
      exact ⟨ht.trans a.isLt, ht⟩
  rw [hset]

theorem target_time_hazard_product_bound {I : Type*} [Fintype I] {T : ℕ}
    (q z : ℕ → ℝ) (δ θ : ℝ) (times : I → Fin T)
    (hq0 : q 0 = 1) (hz0 : z 0 = 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq : ∀ t, q (t + 1) = q t * (1 - δ * θ * z t))
    (hz : ∀ t, z (t + 1) = z t * (1 - δ * q t)) :
    Real.exp (-δ * ∑ i : I, ∑ t : Fin T,
      if t.val < (times i).val then (q t.val + θ * z t.val) else 0) ≤
      Real.exp (4 * δ ^ 2 * (Fintype.card I : ℝ) * (T : ℝ)) *
        ∏ i, q (times i).val * z (times i).val := by
  classical
  have hb := euler_background_bounds q z δ θ hq0 hz0 hδ0 (by linarith) hθ0 hθ1 hq hz
  have hp : 0 ≤ ∏ i, q (times i).val * z (times i).val := by
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (hb (times i).val).1 (hb (times i).val).2.2.1
  have htime : (∑ i : I, ((times i).val : ℝ)) ≤ (Fintype.card I : ℝ) * (T : ℝ) := by
    calc
      _ ≤ ∑ _i : I, (T : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact_mod_cast Nat.le_of_lt (times i).isLt
      _ = _ := by simp
  calc
    _ = ∏ i : I, Real.exp (-δ * ∑ t ∈ Finset.range (times i).val, (q t + θ * z t)) := by
      simp_rw [finite_hazard_sum q z θ]
      rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ ∏ i : I, Real.exp (4 * δ ^ 2 * ((times i).val : ℝ)) *
        (q (times i).val * z (times i).val) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Real.exp_nonneg _
      · intro i _
        exact euler_hazard_product_bound q z δ θ hq0 hz0 hδ0 hδ1 hθ0 hθ1 hq hz (times i).val
    _ = Real.exp (4 * δ ^ 2 * ∑ i : I, ((times i).val : ℝ)) *
        ∏ i, q (times i).val * z (times i).val := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hp
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htime (by positivity : 0 ≤ 4 * δ ^ 2)

/-- Tracking the available masses controls the total forbidden ordinary rate. -/
theorem targetCrossCutoff_mass_lower_bound {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) (r : R → Fin g → ℝ)
    (q z : ℕ → ℝ) (θ η : ℝ)
    (hInj : Set.InjOn (fun a => lab a (o a)) S) (hr : ∀ a y, 0 ≤ r a y) (hη : 0 ≤ η)
    (htrack : ∀ a ∈ S, ∀ t : Fin T, q t.val + θ * z t.val ≤
      rowAvailableMass r ins ξ S (S.image fun b => lab b (o b)) a (t.val + 1) +
        columnAvailableMass r ins ξ S (S.image fun b => lab b (o b)) (lab a (o a)) (t.val + 1) + η) :
    (∑ a : S, ∑ t : Fin T, if t.val < (times a.1).val then (q t.val + θ * z t.val) else 0) ≤
      (∑ e : RowLabel R g, r e.1 e.2 * (targetCrossCutoff ins ξ S o lab times e : ℝ)) +
        (S.card : ℝ) * (T : ℝ) * (η + 2 * prescribedRateMass r ins) := by
  classical
  let L := S.image fun b => lab b (o b)
  have hpres : 0 ≤ prescribedRateMass r ins := by
    unfold prescribedRateMass
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact le_rfl
    · exact hr e.1 e.2
  have hE : 0 ≤ η + 2 * prescribedRateMass r ins := by positivity
  have hpoint (a : S) (t : Fin T) :
      (if t.val < (times a.1).val then (q t.val + θ * z t.val) else 0) ≤
        ((if t.val < (times a.1).val then
          ordinaryRowMass r ins ξ S L a.1 (t.val + 1) +
            ordinaryColumnMass r ins ξ S L (lab a.1 (o a.1)) (t.val + 1) else 0) +
          (η + 2 * prescribedRateMass r ins)) := by
    by_cases ht : t.val < (times a.1).val
    · rw [if_pos ht, if_pos ht]
      have hrow := rowAvailableMass_le_ordinary r ins ξ S L a.1 (t.val + 1) hr
      have hcol := columnAvailableMass_le_ordinary r ins ξ S L (lab a.1 (o a.1)) (t.val + 1) hr
      have htr := htrack a.1 a.2 t
      change q t.val + θ * z t.val ≤ rowAvailableMass r ins ξ S L a.1 (t.val + 1) +
        columnAvailableMass r ins ξ S L (lab a.1 (o a.1)) (t.val + 1) + η at htr
      linarith
    · simpa [ht] using hE
  calc
    _ ≤ ∑ a : S, ∑ t : Fin T,
        ((if t.val < (times a.1).val then
          ordinaryRowMass r ins ξ S L a.1 (t.val + 1) +
            ordinaryColumnMass r ins ξ S L (lab a.1 (o a.1)) (t.val + 1) else 0) +
          (η + 2 * prescribedRateMass r ins)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro t _
      exact hpoint a t
    _ = _ := by
      rw [targetCrossCutoff_mass_identity ins ξ S o lab times r hInj]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      ring

/-- On the tracking event, cross survival has a relative product bound in the Euler background. -/
theorem target_cross_survival_product_bound {T : ℕ} {R : Type*}
    [Fintype R] [DecidableEq R] {g : ℕ} {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (ξ : ClockField T R g Ω) (S : Finset R) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (times : R → Fin T) (r : R → Fin g → ℝ)
    (q z : ℕ → ℝ) (δ θ η : ℝ)
    (hInj : Set.InjOn (fun a => lab a (o a)) S)
    (hr0 : ∀ a y, 0 ≤ r a y) (hr1 : ∀ a y, r a y ≤ 1)
    (hη : 0 ≤ η) (hq0 : q 0 = 1) (hz0 : z 0 = 1)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hq : ∀ t, q (t + 1) = q t * (1 - δ * θ * z t))
    (hz : ∀ t, z (t + 1) = z t * (1 - δ * q t))
    (htrack : ∀ a ∈ S, ∀ t : Fin T, q t.val + θ * z t.val ≤
      rowAvailableMass r ins ξ S (S.image fun b => lab b (o b)) a (t.val + 1) +
        columnAvailableMass r ins ξ S (S.image fun b => lab b (o b)) (lab a (o a)) (t.val + 1) + η) :
    (∏ e : RowLabel R g, survival δ (r e.1 e.2) (targetCrossCutoff ins ξ S o lab times e)) ≤
      Real.exp ((S.card : ℝ) * δ * (T : ℝ) * (η + 2 * prescribedRateMass r ins + 4 * δ)) *
        ∏ a : S, q (times a.1).val * z (times a.1).val := by
  classical
  let H := ∑ a : S, ∑ t : Fin T, if t.val < (times a.1).val then (q t.val + θ * z t.val) else 0
  let M := ∑ e : RowLabel R g, r e.1 e.2 * (targetCrossCutoff ins ξ S o lab times e : ℝ)
  let E := η + 2 * prescribedRateMass r ins
  have hmass : H ≤ M + (S.card : ℝ) * (T : ℝ) * E :=
    targetCrossCutoff_mass_lower_bound ins ξ S o lab times r q z θ η hInj hr0 hη htrack
  have hEuler : Real.exp (-δ * H) ≤
      Real.exp (4 * δ ^ 2 * (S.card : ℝ) * (T : ℝ)) *
        ∏ a : S, q (times a.1).val * z (times a.1).val := by
    simpa only [H, Fintype.card_coe] using target_time_hazard_product_bound
      q z δ θ (fun a : S => times a.1) hq0 hz0 hδ0 hδ1 hθ0 hθ1 hq hz
  have hExp : Real.exp (-δ * M) ≤
      Real.exp (δ * (S.card : ℝ) * (T : ℝ) * E) * Real.exp (-δ * H) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left hmass hδ0
    nlinarith
  calc
    _ ≤ Real.exp (-δ * M) := survival_product_le_exp δ (fun e : RowLabel R g => r e.1 e.2)
      (targetCrossCutoff ins ξ S o lab times) hδ0 (by linarith) (fun e => hr0 e.1 e.2) (fun e => hr1 e.1 e.2)
    _ ≤ _ := hExp
    _ ≤ Real.exp (δ * (S.card : ℝ) * (T : ℝ) * E) *
        (Real.exp (4 * δ ^ 2 * (S.card : ℝ) * (T : ℝ)) *
          ∏ a : S, q (times a.1).val * z (times a.1).val) :=
      mul_le_mul_of_nonneg_left hEuler (Real.exp_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      dsimp [E]
      ring

end HypercubeRamsey.Lane_sol_clock_s7
