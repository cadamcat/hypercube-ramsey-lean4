import HypercubeRamsey.S10.FixedList
import HypercubeRamsey.S03.GatedPosterior

/-!
# Section 10 local nodes

Reusable quantitative and finite-probability interfaces for the steps between the
fixed-list test and the tag/embedding construction. -/

namespace HypercubeRamsey.S10

open scoped BigOperators
open Classical Filter

set_option maxHeartbeats 100000000 in
/-- P10.1b (10:43–54): the scale inequalities needed for the tuple-array, fan and
height bounds. The four exponents are those used in the paper's choice of `m`, `k`
and `T`; all inequalities hold eventually under the stated parameter range. -/
theorem p10_1b_scale_separation
    (η₀ ζ δ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ (500 * δ) < (n : ℝ) ^ η₀ ∧
      3 * (n : ℝ) ^ (500 * δ) < (n : ℝ) ^ ζ ∧
      4 * (n : ℝ) ^ (200 * δ) < (n : ℝ) ^ (1 - δ) ∧
      ((n : ℝ) ^ (200 * δ) + (n : ℝ) ^ (141 * δ)) * Real.log n <
        (n : ℝ) ^ (298 * δ) := by
  have hminη : min (min η₀ ζ) 1 ≤ η₀ :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hminζ : min (min η₀ ζ) 1 ≤ ζ :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hmin1 : min (min η₀ ζ) 1 ≤ 1 := min_le_right _ _
  have h500η : 500 * δ < η₀ := by
    have hscaled := mul_lt_mul_of_pos_left hδsmall (by norm_num : (0 : ℝ) < 500)
    nlinarith
  have h500ζ : 500 * δ < ζ := by
    have hscaled := mul_lt_mul_of_pos_left hδsmall (by norm_num : (0 : ℝ) < 500)
    nlinarith
  have h200 : 200 * δ < 1 - δ := by
    have hδone : δ < (1 : ℝ) / 2000 := lt_of_lt_of_le hδsmall (by
      exact div_le_div_of_nonneg_right hmin1 (by norm_num))
    nlinarith
  have hgap (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
      ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
      (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
    have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
      eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
    filter_upwards [hnlarge,
      htend.eventually_gt_atTop c] with n hn hlarge
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    calc
      c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
        mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
      _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnpos]; congr 1 <;> ring
  have hfirst := hgap (500 * δ) η₀ 4 h500η (by norm_num)
  have hsecond := hgap (500 * δ) ζ 3 h500ζ (by norm_num)
  have hthird := hgap (200 * δ) (1 - δ) 4 h200 (by norm_num)
  have hfourth : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ (200 * δ) + (n : ℝ) ^ (141 * δ)) * Real.log n <
        (n : ℝ) ^ (298 * δ) := by
    have h201 : 201 * δ < 298 * δ := by nlinarith
    have h142 : 142 * δ < 298 * δ := by nlinarith
    have hc : 0 < 2 / δ := div_pos (by norm_num) hδ
    have hlarge1 := hgap (201 * δ) (298 * δ) (2 / δ) h201 hc
    have hlarge2 := hgap (142 * δ) (298 * δ) (2 / δ) h142 hc
    have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
      eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
    filter_upwards [hnlarge, hlarge1, hlarge2]
      with n hn hn1 hn2
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlog := Real.log_natCast_le_rpow_div n hδ
    have hterm1 : (n : ℝ) ^ (200 * δ) * Real.log n ≤
        (1 / δ) * (n : ℝ) ^ (201 * δ) := by
      calc
        (n : ℝ) ^ (200 * δ) * Real.log n ≤
            (n : ℝ) ^ (200 * δ) * ((n : ℝ) ^ δ / δ) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnpos.le _)
        _ = (1 / δ) * (n : ℝ) ^ (201 * δ) := by
          rw [show 201 * δ = 200 * δ + δ by ring, Real.rpow_add hnpos]
          ring
    have hterm2 : (n : ℝ) ^ (141 * δ) * Real.log n ≤
        (1 / δ) * (n : ℝ) ^ (142 * δ) := by
      calc
        (n : ℝ) ^ (141 * δ) * Real.log n ≤
            (n : ℝ) ^ (141 * δ) * ((n : ℝ) ^ δ / δ) :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnpos.le _)
        _ = (1 / δ) * (n : ℝ) ^ (142 * δ) := by
          rw [show 142 * δ = 141 * δ + δ by ring, Real.rpow_add hnpos]
          ring
    have hhalf1 : (1 / δ) * (n : ℝ) ^ (201 * δ) <
        (1 / 2 : ℝ) * (n : ℝ) ^ (298 * δ) := by
      have hrewrite : (2 / δ) * (n : ℝ) ^ (201 * δ) =
          2 * ((1 / δ) * (n : ℝ) ^ (201 * δ)) := by ring
      rw [hrewrite] at hn1
      nlinarith
    have hhalf2 : (1 / δ) * (n : ℝ) ^ (142 * δ) <
        (1 / 2 : ℝ) * (n : ℝ) ^ (298 * δ) := by
      have hrewrite : (2 / δ) * (n : ℝ) ^ (142 * δ) =
          2 * ((1 / δ) * (n : ℝ) ^ (142 * δ)) := by ring
      rw [hrewrite] at hn2
      nlinarith
    calc
      ((n : ℝ) ^ (200 * δ) + (n : ℝ) ^ (141 * δ)) * Real.log n =
          (n : ℝ) ^ (200 * δ) * Real.log n +
            (n : ℝ) ^ (141 * δ) * Real.log n := by ring
      _ ≤ (1 / δ) * (n : ℝ) ^ (201 * δ) +
          (1 / δ) * (n : ℝ) ^ (142 * δ) := add_le_add hterm1 hterm2
      _ < (1 / 2 : ℝ) * (n : ℝ) ^ (298 * δ) +
          (1 / 2 : ℝ) * (n : ℝ) ^ (298 * δ) := add_lt_add hhalf1 hhalf2
      _ = (n : ℝ) ^ (298 * δ) := by ring
  filter_upwards [hfirst, hsecond, hthird, hfourth] with n hn1 hn2 hn3 hn4
  exact ⟨hn1, hn2, hn3, hn4⟩

set_option maxHeartbeats 500000 in
/-- P10.1d (10:101–126): generic union bound for `n` disjoint failed lists chosen
from a finite menu. The premise is the product estimate supplied by independence of
the tuple arrays on disjoint lists. -/
theorem p10_1d_disjoint_failure_union_bound
    {Ω : Type*} [Fintype Ω] {L n : ℕ} (P : FinProb Ω)
    (failed : Fin L → Ω → Prop) (p : ℝ)
    (hp : 0 ≤ p)
    (hproduct : ∀ f : Fin n → Fin L,
      P.pr (fun ω => ∀ i, failed (f i) ω) ≤ p ^ n) :
      P.pr (fun ω => ∃ f : Fin n → Fin L, ∀ i, failed (f i) ω) ≤
      (L : ℝ) ^ n * p ^ n := by
  classical
  let indicator (f : Fin n → Fin L) (ω : Ω) : ℝ :=
    @ite ℝ (∀ i, failed (f i) ω) (Classical.propDecidable _) (P.w ω) 0
  let unionIndicator (ω : Ω) : ℝ :=
    @ite ℝ (∃ f : Fin n → Fin L, ∀ i, failed (f i) ω)
      (Classical.propDecidable _) (P.w ω) 0
  have hpoint (ω : Ω) :
      unionIndicator ω ≤
        ∑ f : Fin n → Fin L, indicator f ω := by
    by_cases hex : ∃ f : Fin n → Fin L, ∀ i, failed (f i) ω
    · have hunion : unionIndicator ω = P.w ω := by simp [unionIndicator, hex]
      rw [hunion]
      rcases hex with ⟨f, hf⟩
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun g : Fin n → Fin L => indicator g ω)
        (fun g hg => by
          by_cases h : ∀ i, failed (g i) ω
          · simpa [indicator, h] using P.nonneg ω
          · simp [indicator, h])
        (Finset.mem_univ f)
      simpa [indicator, hf] using hsingle
    · have hunion : unionIndicator ω = 0 := by simp [unionIndicator, hex]
      rw [hunion]
      apply Finset.sum_nonneg
      intro f hf
      by_cases h : ∀ i, failed (f i) ω
      · simpa [indicator, h] using P.nonneg ω
      · simp [indicator, h]
  calc
    P.pr (fun ω => ∃ f : Fin n → Fin L, ∀ i, failed (f i) ω) =
        ∑ ω, unionIndicator ω := by simp only [FinProb.pr, unionIndicator]
    _ ≤ ∑ ω, ∑ f : Fin n → Fin L, indicator f ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact hpoint ω
    _ = ∑ f : Fin n → Fin L, P.pr (fun ω => ∀ i, failed (f i) ω) := by
      simp only [FinProb.pr, indicator]
      exact Finset.sum_comm
    _ ≤ ∑ f : Fin n → Fin L, p ^ n := by
      apply Finset.sum_le_sum
      intro f hf
      exact hproduct f
    _ = (L : ℝ) ^ n * p ^ n := by simp [Fintype.card_fun]

/-- Squared-tilt mass of deletion-ratio failures. -/
noncomputable def squaredTiltBadWeight {q : ℕ} (ρ : FinProb (Fin q))
    (mass massWithout : Fin q → ℝ) (t : ℝ) : ℝ := by
  classical
  exact ∑ j : Fin q,
    if mass j / massWithout j < t then ρ.w j * (mass j) ^ 2 else 0

/-- P10.1e (10:128–149): the squared tilt assigns at most
`t² A(F₋c) / A(F)` mass to clusters whose deletion ratio is below `t`. -/
theorem p10_1e_squared_tilt_tail_bound
    {q : ℕ} (ρ : FinProb (Fin q)) (mass massWithout : Fin q → ℝ) (t : ℝ)
    (hρ : ∀ j, 0 ≤ ρ.w j)
    (hmass : ∀ j, 0 ≤ mass j ∧ 0 ≤ massWithout j ∧ mass j ≤ massWithout j)
    (ht : 0 ≤ t) :
      squaredTiltBadWeight ρ mass massWithout t /
      (∑ j : Fin q, ρ.w j * (mass j) ^ 2) ≤
        t ^ 2 * (∑ j : Fin q, ρ.w j * (massWithout j) ^ 2) /
          (∑ j : Fin q, ρ.w j * (mass j) ^ 2) := by
  classical
  let A : ℝ := ∑ j : Fin q, ρ.w j * (mass j) ^ 2
  let B : ℝ := ∑ j : Fin q, ρ.w j * (massWithout j) ^ 2
  have hnum : squaredTiltBadWeight ρ mass massWithout t ≤ t ^ 2 * B := by
    unfold squaredTiltBadWeight
    calc
      (∑ j : Fin q, if mass j / massWithout j < t then ρ.w j * (mass j) ^ 2 else 0) ≤
          ∑ j : Fin q, ρ.w j * (t * massWithout j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hbad : mass j / massWithout j < t
        · rw [if_pos hbad]
          have hmassLe : mass j ≤ t * massWithout j := by
            by_cases hzero : massWithout j = 0
            · have hmasszero : mass j = 0 :=
                le_antisymm (by simpa [hzero] using (hmass j).2.2) (hmass j).1
              simp [hzero, hmasszero]
            · have hden : 0 < massWithout j :=
                lt_of_le_of_ne (hmass j).2.1 (Ne.symm hzero)
              exact le_of_lt ((div_lt_iff₀ hden).mp hbad)
          have hsquare : mass j ^ 2 ≤ (t * massWithout j) ^ 2 := by
            have hprod := mul_nonneg (sub_nonneg.mpr hmassLe)
              (add_nonneg (hmass j).1 (mul_nonneg ht (hmass j).2.1))
            nlinarith
          exact mul_le_mul_of_nonneg_left hsquare (hρ j)
        · rw [if_neg hbad]
          exact mul_nonneg (hρ j) (sq_nonneg _)
      _ = t ^ 2 * B := by
        dsimp [B]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hρ j) (sq_nonneg _)
  by_cases hA : A = 0
  · simp [A, hA]
  · have hApos : 0 < A := lt_of_le_of_ne hA_nonneg (Ne.symm hA)
    change squaredTiltBadWeight ρ mass massWithout t / A ≤ (t ^ 2 * B) / A
    exact (div_le_div_of_nonneg_right hnum hApos.le)

/-- Sum of all mask prices against a cluster aggregate. -/
def totalMaskPrice {N T : ℕ} (ν : Law N) (price : Fin (T + 1) → Fin N → ℝ) : ℝ :=
  ∑ t : Fin (T + 1), ∑ y : Fin N, ν.w y * price t y

/-- Labels whose total price over all own-list sizes is cheap. -/
noncomputable def cheapMaskLabels {N T : ℕ} (ν : Law N)
    (price : Fin (T + 1) → Fin N → ℝ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter fun y =>
    (∑ t : Fin (T + 1), price t y) ≤ 10 * totalMaskPrice ν price

/-- P10.1f (10:153): a cheap-label mask retains at least nine tenths of the
aggregate and bounds every own-list price. -/
theorem p10_1f_mask_price_separation
    {N T : ℕ} (ν : Law N) (price : Fin (T + 1) → Fin N → ℝ)
    (hprice : ∀ t y, 0 ≤ price t y) :
    9 / 10 ≤ lawMassOn ν (cheapMaskLabels ν price) ∧
    ∀ t : Fin (T + 1),
      (∑ y ∈ cheapMaskLabels ν price, ν.w y * price t y) ≤
        10 * totalMaskPrice ν price := by
  classical
  let cost : Fin N → ℝ := fun y => ∑ t : Fin (T + 1), price t y
  let S : ℝ := totalMaskPrice ν price
  let discarded : ℝ := ∑ y : Fin N,
    if 10 * S < cost y then ν.w y else 0
  have hcost_nonneg (y : Fin N) : 0 ≤ cost y := by
    dsimp [cost]
    apply Finset.sum_nonneg
    intro t ht
    exact hprice t y
  have hS_nonneg : 0 ≤ S := by
    dsimp [S, totalMaskPrice]
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (ν.nonneg y) (hprice t y)
  have hcost_sum : ∑ y : Fin N, ν.w y * cost y = S := by
    calc
      ∑ y : Fin N, ν.w y * cost y =
          ∑ y : Fin N, ∑ t : Fin (T + 1), ν.w y * price t y := by
        apply Finset.sum_congr rfl
        intro y hy
        simp only [cost]
        rw [Finset.mul_sum]
      _ = ∑ t : Fin (T + 1), ∑ y : Fin N, ν.w y * price t y :=
        Finset.sum_comm
      _ = S := by rfl
  have hcheap_eq : lawMassOn ν (cheapMaskLabels ν price) =
      ∑ y : Fin N, if cost y ≤ 10 * S then ν.w y else 0 := by
    unfold lawMassOn cheapMaskLabels
    rw [Finset.sum_filter]
  have hpartition :
      (∑ y : Fin N, if cost y ≤ 10 * S then ν.w y else 0) + discarded = 1 := by
    calc
      (∑ y : Fin N, if cost y ≤ 10 * S then ν.w y else 0) + discarded =
          ∑ y : Fin N,
            ((if cost y ≤ 10 * S then ν.w y else 0) +
              (if 10 * S < cost y then ν.w y else 0)) := by
        rw [← Finset.sum_add_distrib]
      _ = ∑ y : Fin N, ν.w y := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases h : cost y ≤ 10 * S
        · simp [h, not_lt.mpr h]
        · have hlt : 10 * S < cost y := lt_of_not_ge h
          simp [h, hlt]
      _ = 1 := ν.sum_eq_one
  have hdiscard_bound : 10 * S * discarded ≤ S := by
    calc
      10 * S * discarded =
          ∑ y : Fin N, 10 * S * (if 10 * S < cost y then ν.w y else 0) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ y : Fin N, ν.w y * cost y := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases h : 10 * S < cost y
        · rw [if_pos h]
          calc
            10 * S * ν.w y = (10 * S) * ν.w y := by ring
            _ ≤ cost y * ν.w y :=
              mul_le_mul_of_nonneg_right h.le (ν.nonneg y)
            _ = ν.w y * cost y := by ring
        · rw [if_neg h]
          simpa using mul_nonneg (ν.nonneg y) (hcost_nonneg y)
      _ = S := hcost_sum
  have hdiscard_le : discarded ≤ 1 / 10 := by
    by_cases hS : S = 0
    · have hdiscard_zero : discarded = 0 := by
        dsimp [discarded]
        apply Finset.sum_eq_zero
        intro y hy
        by_cases hexp : 10 * S < cost y
        · rw [if_pos hexp]
          have hterm_nonneg : 0 ≤ ν.w y * cost y :=
            mul_nonneg (ν.nonneg y) (hcost_nonneg y)
          have hterm_le : ν.w y * cost y ≤ S := by
            rw [← hcost_sum]
            exact Finset.single_le_sum
              (fun y' hy' => mul_nonneg (ν.nonneg y') (hcost_nonneg y'))
              (Finset.mem_univ y)
          have hterm_zero : ν.w y * cost y = 0 := by
            apply le_antisymm
            · simpa [hS] using hterm_le
            · exact hterm_nonneg
          have hcost_pos : 0 < cost y := by simpa [hS] using hexp
          have hw_zero : ν.w y = 0 := by
            rcases mul_eq_zero.mp hterm_zero with hw | hc
            · exact hw
            · exact False.elim ((ne_of_gt hcost_pos) hc)
          simp [hw_zero]
        · rw [if_neg hexp]
      simpa [hdiscard_zero] using (by norm_num : (0 : ℝ) ≤ 1 / 10)
    · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
      have hden_pos : 0 < 10 * S := by positivity
      have hratio : discarded ≤ S / (10 * S) :=
        (le_div_iff₀ hden_pos).2 (by nlinarith [hdiscard_bound])
      calc
        discarded ≤ S / (10 * S) := hratio
        _ = 1 / 10 := by field_simp
  have hcheap_mass : 9 / 10 ≤ lawMassOn ν (cheapMaskLabels ν price) := by
    rw [hcheap_eq]
    nlinarith [hpartition, hdiscard_le]
  refine ⟨hcheap_mass, ?_⟩
  intro t
  calc
    (∑ y ∈ cheapMaskLabels ν price, ν.w y * price t y) ≤
        ∑ y : Fin N, ν.w y * price t y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro y hy hnot
      exact mul_nonneg (ν.nonneg y) (hprice t y)
    _ ≤ totalMaskPrice ν price := by
      unfold totalMaskPrice
      exact Finset.single_le_sum
        (fun t' ht' => Finset.sum_nonneg fun y hy =>
          mul_nonneg (ν.nonneg y) (hprice t' y))
        (Finset.mem_univ t)
    _ ≤ 10 * totalMaskPrice ν price := by
      have htotal : 0 ≤ totalMaskPrice ν price := hS_nonneg
      nlinarith

/-- P10.1g (10:155–186): transfer a pointwise comparison with the aggregate law to
the required normalized pointwise row cap. -/
theorem p10_1g_prescribed_list_to_selection
    {N : ℕ} (m : ℕ) (ν : Law N) (pHat : Fin N → ℝ) (B : ℝ)
    (hrow : ∀ y, pHat y ≤ B * ν.w y)
    (hcap : ∀ y, (N : ℝ) * B * ν.w y ≤ Real.exp ((1 / 10 : ℝ) * m)) :
    ∀ y, (N : ℝ) * pHat y ≤ Real.exp ((1 / 10 : ℝ) * m) := by
  intro y
  calc
    (N : ℝ) * pHat y ≤ (N : ℝ) * (B * ν.w y) :=
      mul_le_mul_of_nonneg_left (hrow y) (Nat.cast_nonneg N)
    _ = (N : ℝ) * B * ν.w y := by ring
    _ ≤ Real.exp ((1 / 10 : ℝ) * m) := hcap y

/-- P10.1h (10:191–222): multiply per-group likelihood comparisons into a
comparison for the full odd-neighbor star. -/
theorem p10_1h_product_likelihood_comparison
    {A B : Type*} [Fintype A] [Fintype B] {m : ℕ}
    (L Q : Fin m → A → B → ℝ) (s : Fin m → ℝ)
    (hQ : ∀ i a b, 0 ≤ Q i a b)
    (hL : ∀ i a b, 0 ≤ L i a b)
    (hcompare : ∀ i a b, L i a b ≤ Real.exp (s i) * Q i a b) :
    ∀ a b, (∏ i : Fin m, L i a b) ≤
      Real.exp (∑ i : Fin m, s i) * ∏ i : Fin m, Q i a b := by
  intro a b
  calc
    (∏ i : Fin m, L i a b) ≤
        ∏ i : Fin m, (Real.exp (s i) * Q i a b) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hL i a b
      · intro i hi
        exact hcompare i a b
    _ = (∏ i : Fin m, Real.exp (s i)) * ∏ i : Fin m, Q i a b :=
      Finset.prod_mul_distrib
    _ = Real.exp (∑ i : Fin m, s i) * ∏ i : Fin m, Q i a b := by
      rw [← Real.exp_sum]

/-- P10.1i (10:224–262): predictive gated posterior bound, including the small-data
exception, posterior domination and the exact integration identity. -/
theorem p10_1i_predictive_test
    {Zc Dt : Type*} [Fintype Zc] [Fintype Dt] (π : FinProb Zc)
    (F : Zc → Dt → ℝ) (hF0 : ∀ z t, 0 ≤ F z t) (Q : FinProb Dt)
    (ε s : ℝ) (hε : 0 < ε) :
    let m : Dt → ℝ := fun t => ∑ z, π.w z * F z t
    (∑ t, (if m t < ε * Q.w t ∨ m t = 0 then m t else 0)) ≤ ε ∧
    ((∀ z t, F z t ≤ Real.exp s * Q.w t) →
      ∀ t, ¬ (m t < ε * Q.w t ∨ m t = 0) → ∀ z,
        π.w z * F z t / m t ≤ Real.exp s * ε⁻¹ * π.w z) ∧
    (∀ h : Zc → Dt → ℝ,
      ∑ t, m t * ∑ z, h z t * (π.w z * F z t / m t) =
        ∑ z, ∑ t, π.w z * h z t * F z t) := by
  exact HypercubeRamsey.gated_posterior π F hF0 Q ε s hε

end HypercubeRamsey.S10
