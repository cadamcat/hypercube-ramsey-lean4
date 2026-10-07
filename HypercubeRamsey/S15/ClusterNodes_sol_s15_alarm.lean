import HypercubeRamsey.S15.Capacity
import HypercubeRamsey.S12.Exceptional
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_sol_s15_alarm

open HypercubeRamsey HypercubeRamsey.S15 Classical Filter
open scoped BigOperators

set_option maxHeartbeats 400000

/-- Generating-product bound for all fixed-size certificates containing a pinned group. -/
theorem pinned_subset_charge_le {G : Type*} [DecidableEq G]
    (s : Finset G) (q : G → ℝ) (hq : ∀ g, 0 ≤ q g)
    (g : G) (l : ℕ) (hl : 1 ≤ l)
    (hlarge : 20 * (∑ a ∈ s, q a) ≤ (l - 1 : ℕ)) :
    (∑ A ∈ s.powerset, if g ∈ A ∧ A.card = l then
      (2 : ℝ) ^ A.card * (∏ a ∈ A.erase g, q a) else 0) ≤
      6 * Real.exp (-((l - 1 : ℕ) : ℝ) / 3) := by
  let r : G → ℝ := fun a => if a = g then 1 else 4 * q a
  have hr : ∀ a, 0 ≤ r a := by
    intro a
    dsimp [r]
    split_ifs
    · norm_num
    · exact mul_nonneg (by norm_num) (hq a)
  have hm : 0 ≤ ((l - 1 : ℕ) : ℝ) := by positivity
  have hterm (A : Finset G) (hA : A ∈ s.powerset) :
      (if g ∈ A ∧ A.card = l then
        (2 : ℝ) ^ A.card * (∏ a ∈ A.erase g, q a) else 0) ≤
      2 * (1 / 2 : ℝ) ^ (l - 1) * ∏ a ∈ A, r a := by
    have hAs := Finset.mem_powerset.mp hA
    by_cases h : g ∈ A ∧ A.card = l
    · rw [if_pos h]
      have hcard : (A.erase g).card = l - 1 := by simp [Finset.card_erase_of_mem h.1, h.2]
      have hprod : (∏ a ∈ A, r a) = (4 : ℝ) ^ (l - 1) * ∏ a ∈ A.erase g, q a := by
        rw [← Finset.mul_prod_erase A r h.1]
        simp only [r, if_pos rfl, one_mul]
        have heq : (∏ a ∈ A.erase g, if a = g then (1 : ℝ) else 4 * q a) =
            ∏ a ∈ A.erase g, 4 * q a := by
          apply Finset.prod_congr rfl
          intro a ha
          rw [if_neg (Finset.mem_erase.mp ha).1]
        rw [heq, Finset.prod_mul_distrib, Finset.prod_const, hcard]
      rw [hprod, h.2]
      have hl' : l = (l - 1) + 1 := by omega
      have hp : (1 / 2 : ℝ) ^ (l - 1) * 4 ^ (l - 1) = 2 ^ (l - 1) := by
        rw [← mul_pow]
        norm_num
      have hpow : (2 : ℝ) ^ l = 2 ^ (l - 1) * 2 := by
        conv_lhs => rw [hl', pow_succ]
      rw [hpow]
      calc
        (2 : ℝ) ^ (l - 1) * 2 * (∏ a ∈ A.erase g, q a) =
          2 * ((1 / 2 : ℝ) ^ (l - 1) * 4 ^ (l - 1)) *
            (∏ a ∈ A.erase g, q a) := by rw [hp]; ring
        _ = 2 * (1 / 2 : ℝ) ^ (l - 1) *
            (4 ^ (l - 1) * ∏ a ∈ A.erase g, q a) := by ring
        _ ≤ _ := le_rfl
    · rw [if_neg h]
      apply mul_nonneg (by positivity)
      exact Finset.prod_nonneg fun a ha => hr a
  have hsum : (∑ a ∈ s, r a) ≤ 1 + 4 * ∑ a ∈ s, q a := by
    calc
      (∑ a ∈ s, r a) ≤ ∑ a ∈ s, ((if a = g then 1 else 0) + 4 * q a) := by
        apply Finset.sum_le_sum
        intro a ha
        dsimp [r]
        split_ifs with h
        · linarith [hq a]
        · simp
      _ = (∑ a ∈ s, if a = g then (1 : ℝ) else 0) + 4 * ∑ a ∈ s, q a := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 1 + 4 * ∑ a ∈ s, q a := by simp; split_ifs <;> linarith
  calc
    (∑ A ∈ s.powerset, if g ∈ A ∧ A.card = l then
      (2 : ℝ) ^ A.card * (∏ a ∈ A.erase g, q a) else 0) ≤
        ∑ A ∈ s.powerset, 2 * (1 / 2 : ℝ) ^ (l - 1) * ∏ a ∈ A, r a :=
      Finset.sum_le_sum hterm
    _ = 2 * (1 / 2 : ℝ) ^ (l - 1) * ∏ a ∈ s, (1 + r a) := by
      rw [← Finset.mul_sum, ← Finset.prod_one_add]
    _ ≤ 2 * (1 / 2 : ℝ) ^ (l - 1) * Real.exp (∑ a ∈ s, r a) :=
      mul_le_mul_of_nonneg_left (Real.prod_one_add_le_exp_sum s hr) (by positivity)
    _ ≤ 2 * (1 / 2 : ℝ) ^ (l - 1) * Real.exp (1 + 4 * ∑ a ∈ s, q a) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum) (by positivity)
    _ ≤ 6 * Real.exp (-((l - 1 : ℕ) : ℝ) / 3) := by
      have hlog : (3 / 5 : ℝ) ≤ Real.log 2 := by
        linarith [Real.log_two_gt_d9]
      have hp : (1 / 2 : ℝ) ^ (l - 1) =
          Real.exp (-((l - 1 : ℕ) : ℝ) * Real.log 2) := by
        have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          norm_num
        rw [← he, ← Real.exp_nat_mul]
        congr 1
        ring
      rw [hp, mul_assoc, ← Real.exp_add]
      have hex : -((l - 1 : ℕ) : ℝ) * Real.log 2 + (1 + 4 * ∑ a ∈ s, q a) ≤
          1 - ((l - 1 : ℕ) : ℝ) / 3 := by
        nlinarith
      calc
        2 * Real.exp (-((l - 1 : ℕ) : ℝ) * Real.log 2 +
            (1 + 4 * ∑ a ∈ s, q a)) ≤
            2 * Real.exp (1 - ((l - 1 : ℕ) : ℝ) / 3) := by
          gcongr
        _ = (2 * Real.exp 1) * Real.exp (-((l - 1 : ℕ) : ℝ) / 3) := by
          rw [sub_eq_add_neg, Real.exp_add]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          linarith [Real.exp_one_lt_three]


/-- The weighted expected bucket load controls its unweighted bin-choice sum. -/
theorem bucket_probability_sum_le {G : Type*} [DecidableEq G]
    (s : Finset G) (q a : G → ℝ) (hq : ∀ g, 0 ≤ q g)
    (w : ℝ) (hw : 0 < w) (ha : ∀ g ∈ s, w / 2 ≤ a g) :
    (∑ g ∈ s, q g) ≤ 2 * (∑ g ∈ s, q g * a g) / w := by
  have h : w / 2 * (∑ g ∈ s, q g) ≤ ∑ g ∈ s, q g * a g := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro g hg
    nlinarith [mul_le_mul_of_nonneg_left (ha g hg) (hq g)]
  apply (le_div_iff₀ hw).mpr
  nlinarith

/-- The additive allowance pays for the rounding in the certificate size. -/
theorem certificate_floor_bounds (K m t w z : ℝ)
    (hK : 40 ≤ K) (hm : 0 ≤ m) (hw : 0 < w)
    (ht : 2 ≤ t / w) (hz : z ≤ 2 * m / w) :
    20 * z ≤ (⌊(K * m + t) / w⌋₊ : ℝ) ∧
      t / (2 * w) ≤ (⌊(K * m + t) / w⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one ((K * m + t) / w)
  have ht' : 2 * w ≤ t := (le_div_iff₀ hw).mp ht
  have hK' : 40 * m ≤ K * m := mul_le_mul_of_nonneg_right hK hm
  have hf' : K * m + t < ((⌊(K * m + t) / w⌋₊ : ℝ) + 1) * w :=
    (div_lt_iff₀ hw).mp hf
  constructor
  · have hz' : z * w ≤ 2 * m := (le_div_iff₀ hw).mp hz
    apply (mul_le_mul_iff_of_pos_right hw).mp
    nlinarith
  · apply (div_le_iff₀ (by positivity : 0 < 2 * w)).mpr
    have hKm : 0 ≤ K * m := mul_nonneg (by linarith) hm
    nlinarith

/-- Certificate charges decay with the additive allowance, uniformly in the bucket mean. -/
theorem bucket_pinned_charge_le {G : Type*} [DecidableEq G]
    (s : Finset G) (q a : G → ℝ) (hq : ∀ g, 0 ≤ q g)
    (K t w : ℝ) (hK : 40 ≤ K) (hw : 0 < w)
    (ht : 2 ≤ t / w) (ha : ∀ g ∈ s, w / 2 ≤ a g) (g : G) :
    let m := ∑ b ∈ s, q b * a b
    let l := ⌊(K * m + t) / w⌋₊ + 1
    (∑ A ∈ s.powerset, if g ∈ A ∧ A.card = l then
      (2 : ℝ) ^ A.card * (∏ b ∈ A.erase g, q b) else 0) ≤
      6 * Real.exp (-t / (6 * w)) := by
  dsimp only
  let m := ∑ b ∈ s, q b * a b
  have hm : 0 ≤ m := Finset.sum_nonneg fun b hb =>
    mul_nonneg (hq b) (le_trans (by positivity) (ha b hb))
  have hz := bucket_probability_sum_le s q a hq w hw ha
  have hb := certificate_floor_bounds K m t w (∑ b ∈ s, q b) hK hm hw ht hz
  have hc := pinned_subset_charge_le s q hq g (⌊(K * m + t) / w⌋₊ + 1)
    (by omega) (by simpa using hb.1)
  apply hc.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  simp only [Nat.add_sub_cancel] at *
  have hpos : 0 < 2 * w := by positivity
  have hmul : t ≤ (⌊(K * m + t) / w⌋₊ : ℝ) * (2 * w) :=
    (div_le_iff₀ hpos).mp hb.2
  apply (le_div_iff₀ (by positivity : 0 < 6 * w)).mpr
  nlinarith


/-- Every positive atom at or below the bucket scale lies in a dyadic bucket. -/
theorem dyadic_bucket_exists (w a : ℝ) (hw : 0 < w) (ha : 0 < a) (haw : a ≤ w) :
    ∃ j : ℕ, w * (1 / 2 : ℝ) ^ j / 2 < a ∧ a ≤ w * (1 / 2 : ℝ) ^ j := by
  obtain ⟨j, hj0, hj1⟩ := exists_nat_pow_near_of_lt_one
    (div_pos ha hw) ((div_le_one hw).mpr haw)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨j, ?_, ?_⟩
  · rw [pow_succ] at hj0
    have h := (lt_div_iff₀ hw).mp hj0
    nlinarith
  · have h := (div_le_iff₀ hw).mp hj1
    nlinarith

/-- The half-open dyadic intervals are disjoint. -/
theorem dyadic_bucket_unique (w a : ℝ) (hw : 0 < w) (j k : ℕ)
    (hj : w * (1 / 2 : ℝ) ^ j / 2 < a ∧ a ≤ w * (1 / 2 : ℝ) ^ j)
    (hk : w * (1 / 2 : ℝ) ^ k / 2 < a ∧ a ≤ w * (1 / 2 : ℝ) ^ k) : j = k := by
  have hnot (i t : ℕ) (hit : i < t)
      (hi : w * (1 / 2 : ℝ) ^ i / 2 < a)
      (ht : a ≤ w * (1 / 2 : ℝ) ^ t) : False := by
    have hp : (1 / 2 : ℝ) ^ t ≤ (1 / 2 : ℝ) ^ (i + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at hp
    have hmul := mul_le_mul_of_nonneg_left hp hw.le
    nlinarith
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim (hnot j k h hj.1 hk.2)
  · exact h
  · exact False.elim (hnot k j h hk.1 hj.2)


/-- Avoidance of all fixed-size subsets bounds the number of selected groups. -/
theorem selected_card_lt_certificate {G : Type*} [DecidableEq G]
    (s C : Finset G) (l : ℕ)
    (hno : ∀ A : Finset G, A ⊆ s → A.card = l → ¬ A ⊆ C) :
    (s ∩ C).card < l := by
  by_contra h
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq (le_of_not_gt h)
  exact hno A (hA.trans Finset.inter_subset_left) hcard
    (hA.trans Finset.inter_subset_right)

/-- The cardinal certificate enforces its bucket's allowed load. -/
theorem selected_bucket_load_le {G : Type*} [DecidableEq G]
    (s C : Finset G) (a : G → ℝ) (w K m t : ℝ)
    (hw : 0 < w) (hallow : 0 ≤ K * m + t)
    (ha : ∀ g ∈ s, a g ≤ w)
    (hno : ∀ A : Finset G, A ⊆ s →
      A.card = ⌊(K * m + t) / w⌋₊ + 1 → ¬ A ⊆ C) :
    (∑ g ∈ s ∩ C, a g) ≤ K * m + t := by
  have hc := selected_card_lt_certificate s C (⌊(K * m + t) / w⌋₊ + 1) hno
  have hc' : ((s ∩ C).card : ℝ) ≤ (⌊(K * m + t) / w⌋₊ : ℝ) := by
    exact_mod_cast (by omega : (s ∩ C).card ≤ ⌊(K * m + t) / w⌋₊)
  calc
    (∑ g ∈ s ∩ C, a g) ≤ ∑ g ∈ s ∩ C, w :=
      Finset.sum_le_sum fun g hg => ha g (Finset.mem_inter.mp hg).1
    _ = ((s ∩ C).card : ℝ) * w := by simp
    _ ≤ (⌊(K * m + t) / w⌋₊ : ℝ) * w := mul_le_mul_of_nonneg_right hc' hw.le
    _ ≤ ((K * m + t) / w) * w :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg hallow hw.le)) hw.le
    _ = _ := div_mul_cancel₀ _ hw.ne'

/-- A finite collection of disjoint buckets can be summed without counting a group twice. -/
theorem disjoint_bucket_load_le {G I : Type*} [DecidableEq G] [DecidableEq I]
    (univ C : Finset G) (J : Finset I) (S : I → Finset G)
    (a q : G → ℝ) (K : ℝ) (t : I → ℝ)
    (ha : ∀ g, 0 ≤ a g) (hq : ∀ g, 0 ≤ q g) (hK : 0 ≤ K)
    (hdisj : Set.PairwiseDisjoint (↑J : Set I) S)
    (hsub : ∀ j ∈ J, S j ⊆ univ)
    (hcover : C = J.biUnion (fun j => S j ∩ C))
    (hload : ∀ j ∈ J, (∑ g ∈ S j ∩ C, a g) ≤
      K * (∑ g ∈ S j, q g * a g) + t j) :
    (∑ g ∈ C, a g) ≤ K * (∑ g ∈ univ, q g * a g) + ∑ j ∈ J, t j := by
  have hdisj' : Set.PairwiseDisjoint (↑J : Set I) (fun j => S j ∩ C) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  have hmean : (∑ j ∈ J, ∑ g ∈ S j, q g * a g) ≤ ∑ g ∈ univ, q g * a g := by
    rw [← Finset.sum_biUnion hdisj]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.biUnion_subset.mpr hsub
    · intro g _ _
      exact mul_nonneg (hq g) (ha g)
  calc
    (∑ g ∈ C, a g) = ∑ j ∈ J, ∑ g ∈ S j ∩ C, a g := by
      conv_lhs => rw [hcover]
      exact Finset.sum_biUnion hdisj'
    _ ≤ ∑ j ∈ J, (K * (∑ g ∈ S j, q g * a g) + t j) := Finset.sum_le_sum hload
    _ = K * (∑ j ∈ J, ∑ g ∈ S j, q g * a g) + ∑ j ∈ J, t j := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hmean hK) le_rfl


/-- The additive dyadic allowances have total at most four. -/
theorem dyadic_allowance_sum_le (J : Finset ℕ) :
    (∑ j ∈ J, (2 : ℝ) ^ (-(j : ℝ) / 2)) ≤ 4 := by
  let r : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrsq : r ^ 2 = (1 / 2 : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hr : r ≤ 3 / 4 := by nlinarith
  have heq (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ) / 2) = r ^ j := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp_rw [heq]
  calc
    (∑ j ∈ J, r ^ j) ≤ ∑ j ∈ J, (3 / 4 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      exact pow_le_pow_left₀ hr0 hr j
    _ ≤ ∑' j : ℕ, (3 / 4 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num : (3 / 4 : ℝ) < 1)).sum_le_tsum J (fun j _ => by positivity)
    _ = 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num


/-- At most one bucket can charge a fixed pinned group. -/
theorem tsum_pinned_bucket_le {G : Type*} [DecidableEq G]
    (S : ℕ → Finset G) (q : G → ℝ) (l : ℕ → ℕ) (g : G) (M : ℝ)
    (hM : 0 ≤ M)
    (hunique : ∀ j j', g ∈ S j → g ∈ S j' → j = j')
    (hbound : ∀ j,
      (∑ A ∈ (S j).powerset, if g ∈ A ∧ A.card = l j then
        (2 : ℝ) ^ A.card * (∏ b ∈ A.erase g, q b) else 0) ≤ M) :
    (∑' j : ℕ, ∑ A ∈ (S j).powerset, if g ∈ A ∧ A.card = l j then
      (2 : ℝ) ^ A.card * (∏ b ∈ A.erase g, q b) else 0) ≤ M := by
  have hzero (j : ℕ) (hgj : g ∉ S j) :
      (∑ A ∈ (S j).powerset, if g ∈ A ∧ A.card = l j then
        (2 : ℝ) ^ A.card * (∏ b ∈ A.erase g, q b) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    apply if_neg
    intro h
    exact hgj (Finset.mem_powerset.mp hA h.1)
  by_cases hex : ∃ j, g ∈ S j
  · obtain ⟨j, hj⟩ := hex
    rw [tsum_eq_single j]
    · exact hbound j
    · intro j' hj'
      apply hzero
      intro hgj'
      exact hj' (hunique j' j hgj' hj)
  · have hz : ∀ j, (∑ A ∈ (S j).powerset, if g ∈ A ∧ A.card = l j then
        (2 : ℝ) ^ A.card * (∏ b ∈ A.erase g, q b) else 0) = 0 := by
      intro j
      exact hzero j (fun h => hex ⟨j, h⟩)
    simp_rw [hz]
    simpa using hM


private theorem real_eventually_rpow_le_mul {p q c : ℝ} (hpq : p < q) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, t ^ p ≤ c * t ^ q := by
  have hlim : Tendsto (fun t : ℝ => t ^ (-(q - p))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (sub_pos.mpr hpq)
  filter_upwards [hlim.eventually (gt_mem_nhds hc), eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := by linarith
  have hr : t ^ p / t ^ q = t ^ (-(q - p)) := by
    rw [← Real.rpow_sub ht0]
    congr 1
    ring
  rw [← hr] at ht
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos ht0 q)).mp ht).le

/-- Ceiling losses in the internal round scales are absorbed by their power bound. -/
theorem internal_round_product_le (ω h : ℝ) (hω : 0 ≤ ω) (hh : 1 ≤ h) :
    (⌈h ^ (3 * ω)⌉₊ : ℝ) * (⌈h ^ ω⌉₊ : ℝ) ≤ 4 * h ^ (4 * ω) := by
  have hk := (Nat.ceil_lt_add_one (Real.rpow_nonneg (show 0 ≤ h by linarith) (3 * ω))).le
  have ht := (Nat.ceil_lt_add_one (Real.rpow_nonneg (show 0 ≤ h by linarith) ω)).le
  have hk1 : 1 ≤ h ^ (3 * ω) := Real.one_le_rpow hh (by positivity)
  have ht1 : 1 ≤ h ^ ω := Real.one_le_rpow hh hω
  have hk' : (⌈h ^ (3 * ω)⌉₊ : ℝ) ≤ 2 * h ^ (3 * ω) := by linarith
  have ht' : (⌈h ^ ω⌉₊ : ℝ) ≤ 2 * h ^ ω := by linarith
  have hm := mul_le_mul hk' ht' (by positivity) (by positivity : 0 ≤ 2 * h ^ (3 * ω))
  have hp : h ^ (3 * ω) * h ^ ω = h ^ (4 * ω) := by
    rw [← Real.rpow_add (by linarith : 0 < h)]
    congr 1
    ring
  nlinarith only [hm, hp]

/-- Uniform atom-scale estimate for any polynomial bound on the internal height. -/
theorem polynomial_height_atom_scale (ω M : ℝ) (hω : 0 < ω) (hM : 0 < M)
    (hp : 4 * ω * M < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, 1 ≤ h → h ≤ 2 * t ^ M →
      2 * h * Real.exp (1.5 * (⌈h ^ (3 * ω)⌉₊ : ℝ) * (⌈h ^ ω⌉₊ : ℝ)) ≤
        Real.exp (t / 8) := by
  let p := 4 * ω * M
  let C := 1 + M + 6 * (2 : ℝ) ^ (4 * ω)
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog : ∀ᶠ t : ℝ in atTop, |Real.log t| ≤ |t ^ p| := by
    simpa using (isLittleO_log_rpow_atTop hp0).bound (by norm_num : (0 : ℝ) < 1)
  have hconst : ∀ᶠ t : ℝ in atTop, Real.log 4 ≤ t ^ p :=
    (tendsto_rpow_atTop hp0).eventually_ge_atTop _
  have hsmall : ∀ᶠ t : ℝ in atTop, t ^ p ≤ (1 / (8 * C)) * t := by
    simpa only [Real.rpow_one] using
      (real_eventually_rpow_le_mul (p := p) (q := 1) hp (show 0 < 1 / (8 * C) by positivity))
  filter_upwards [hlog, hconst, hsmall, eventually_ge_atTop (1 : ℝ)] with t hlog hconst hsmall ht1
  intro h hh hhupper
  have ht0 : 0 < t := by linarith
  have hh0 : 0 < h := by linarith
  have hlog' : Real.log t ≤ t ^ p := by
    exact (le_abs_self _).trans (hlog.trans_eq (abs_of_nonneg (Real.rpow_nonneg ht0.le _)))
  have hheight : h ^ (4 * ω) ≤ (2 : ℝ) ^ (4 * ω) * t ^ p := by
    have hmono := Real.rpow_le_rpow hh0.le hhupper (by positivity : 0 ≤ 4 * ω)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg ht0.le _),
      ← Real.rpow_mul ht0.le] at hmono
    simpa [p, mul_comm M (4 * ω)] using hmono
  have hlogh : Real.log (2 * h) ≤ Real.log 4 + M * Real.log t := by
    have hmono := Real.log_le_log (by positivity : 0 < 2 * h)
      (show 2 * h ≤ 4 * t ^ M by linarith)
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.rpow_pos_of_pos ht0 M).ne',
      Real.log_rpow ht0] at hmono
    exact hmono
  have hround := internal_round_product_le ω h hω.le hh
  have hlogbound : Real.log (2 * h) +
      1.5 * (⌈h ^ (3 * ω)⌉₊ : ℝ) * (⌈h ^ ω⌉₊ : ℝ) ≤ C * t ^ p := by
    have hMlog := mul_le_mul_of_nonneg_left hlog' hM.le
    dsimp [C]
    nlinarith only [hlogh, hconst, hMlog, hround, hheight]
  have hCt : C * t ^ p ≤ t / 8 := by
    calc
      C * t ^ p ≤ C * ((1 / (8 * C)) * t) := mul_le_mul_of_nonneg_left hsmall hC.le
      _ = t / 8 := by field_simp [hC.ne']
  calc
    2 * h * Real.exp (1.5 * (⌈h ^ (3 * ω)⌉₊ : ℝ) * (⌈h ^ ω⌉₊ : ℝ)) =
        Real.exp (Real.log (2 * h) +
          1.5 * (⌈h ^ (3 * ω)⌉₊ : ℝ) * (⌈h ^ ω⌉₊ : ℝ)) := by
      rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * h)]
    _ ≤ _ := Real.exp_le_exp.mpr (hlogbound.trans hCt)


/-- Rounding the exponentially large bin scale preserves the atom-scale bound. -/
theorem floor_exponential_scale_eventually :
    ∀ᶠ t : ℝ in atTop, Real.exp (t / 8) ≤ (⌊Real.exp (t / 2)⌋₊ : ℝ) ^ (0.5 : ℝ) := by
  have ht : ∀ᶠ t : ℝ in atTop, 2 ≤ Real.exp (t / 4) :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))).eventually_ge_atTop _
  filter_upwards [ht] with t ht
  have hf := Nat.lt_floor_add_one (Real.exp (t / 2))
  have he : Real.exp (t / 4) ^ 2 = Real.exp (t / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hfloor : Real.exp (t / 4) ≤ (⌊Real.exp (t / 2)⌋₊ : ℝ) := by nlinarith
  have hfsq : ((⌊Real.exp (t / 2)⌋₊ : ℝ) ^ (0.5 : ℝ)) ^ 2 = (⌊Real.exp (t / 2)⌋₊ : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ⌊Real.exp (t / 2)⌋₊)]
    norm_num
  have hesq : Real.exp (t / 8) ^ 2 = Real.exp (t / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hnonneg : 0 ≤ (⌊Real.exp (t / 2)⌋₊ : ℝ) ^ (0.5 : ℝ) := by positivity
  nlinarith [Real.exp_pos (t / 8)]

variable {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm)

theorem clusterBinProbability_nonneg (g : ClusterGroupIndex PT)
    (D : Finset (Fin (T.S.N k))) : 0 ≤ clusterBinProbability PT hPT hm W g D := by
  unfold clusterBinProbability
  apply Finset.sum_nonneg
  intro D' _
  split_ifs
  · exact (clusterSolver PT hPT hm g.1.1).q_nonneg g.2 _ D'
  · exact le_rfl

theorem clusterCapacityAtom_nonneg (g : ClusterGroupIndex PT)
    (D : Finset (Fin (T.S.N k))) (y : Fin (T.S.N k)) :
    0 ≤ clusterCapacityAtom PT hPT hm W g D y := by
  unfold clusterCapacityAtom
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro D' _
  split_ifs
  · exact (clusterSolver PT hPT hm g.1.1).U_nonneg g.2 _ D' y
  · exact le_rfl

theorem clusterBinProbability_self (g : ClusterGroupIndex PT) (D : clusterBinType g) :
    clusterBinProbability PT hPT hm W g D.1 =
      (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D := by
  change Bin PT.tiling g.1.1 at D
  unfold clusterBinProbability
  change (∑ D' : Bin PT.tiling g.1.1, if D'.1 = D.1 then
    (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' else 0) = _
  have heq (D' : Bin PT.tiling g.1.1) : D'.1 = D.1 ↔ D' = D := Subtype.ext_iff.symm
  simp_rw [heq]
  simp

theorem clusterCapacityAtom_self (g : ClusterGroupIndex PT) (D : clusterBinType g)
    (y : Fin (T.S.N k)) :
    clusterCapacityAtom PT hPT hm W g D.1 y =
      (PT.tiling.P g.1.1).h *
        (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) D y := by
  unfold clusterCapacityAtom
  have heq (D' : clusterBinType g) : D'.1 = D.1 ↔ D' = D := Subtype.ext_iff.symm
  simp_rw [heq]
  simp

theorem clusterBucketWidth_eq (D : Finset (Fin (T.S.N k))) (j : ℕ) :
    clusterBucketWidth D j = (D.card : ℝ) ^ (-0.5 : ℝ) * (1 / 2 : ℝ) ^ j := by
  simp [clusterBucketWidth, zpow_neg, inv_pow, one_div]

/-- Direct instantiation of the generating-product estimate at a physical-bin bucket. -/
theorem cluster_bucket_pinned_charge_le (hκ : κ.Admissible)
    (D : Finset (Fin (T.S.N k))) (y : Fin (T.S.N k)) (j : ℕ)
    (hD : D.Nonempty)
    (ht : 2 ≤ (κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) / clusterBucketWidth D j)
    (g : ClusterGroupIndex PT) :
    (∑ A ∈ (clusterCapacityBucket PT hPT hm W D y j).powerset,
      if g ∈ A ∧ A.card = clusterCertificateSize PT hPT hm W D y j then
        (2 : ℝ) ^ A.card * (∏ g' ∈ A.erase g, clusterBinProbability PT hPT hm W g' D)
      else 0) ≤
        6 * Real.exp (-(κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) /
          (6 * clusterBucketWidth D j)) := by
  have hw : 0 < clusterBucketWidth D j := by
    rw [clusterBucketWidth_eq]
    have hc : (0 : ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
    positivity
  exact bucket_pinned_charge_le (clusterCapacityBucket PT hPT hm W D y j)
    (fun g => clusterBinProbability PT hPT hm W g D)
    (fun g => clusterCapacityAtom PT hPT hm W g D y)
    (clusterBinProbability_nonneg PT hPT hm W · D)
    (κ.Kp : ℝ) (κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2))
    (clusterBucketWidth D j) (by exact_mod_cast hκ.bucket.1) hw ht
    (fun g hg => (Finset.mem_filter.mp hg).2.1.le) g


/-- Physical bins at different patches, or in the same partition, are disjoint. -/
theorem physical_bins_eq_of_mem (hvalid : PT.Valid) {i i' : Fin PT.tiling.m}
    (D : Bin PT.tiling i) (D' : Bin PT.tiling i')
    (y : Fin (T.S.N k)) (hy : y ∈ D.1) (hy' : y ∈ D'.1) : D.1 = D'.1 := by
  have hY : y ∈ (PT.tiling.P i).Y := (PT.tiling.P i).bins.le D.2 hy
  have hY' : y ∈ (PT.tiling.P i').Y := (PT.tiling.P i').bins.le D'.2 hy'
  have hii : i = i' := by
    by_contra h
    exact Finset.disjoint_left.mp (hvalid.tiling_valid.patch_Y_disjoint i i' h) hY hY'
  subst i'
  exact (PT.tiling.P i).bins.eq_of_mem_parts D.2 D'.2 hy hy'

/-- The expected load into any one physical bin is at most the full history column load. -/
theorem physical_bin_mean_le (D : Finset (Fin (T.S.N k))) (y : Fin (T.S.N k)) :
    (∑ g : ClusterGroupIndex PT,
      clusterBinProbability PT hPT hm W g D * clusterCapacityAtom PT hPT hm W g D y) ≤
    ∑ s : ClusterSlice PT, ∑ g : Group PT.tiling s.1,
      (PT.tiling.P s.1).h *
        (clusterSolver PT hPT hm s.1).oddMarginal g (historyOnSlice W s) y := by
  rw [← Fintype.sum_sigma (fun g : ClusterGroupIndex PT =>
    (PT.tiling.P g.1.1).h * (clusterSolver PT hPT hm g.1.1).oddMarginal g.2 (historyOnSlice W g.1) y)]
  apply Finset.sum_le_sum
  intro g _
  by_cases hex : ∃ D' : clusterBinType g, D'.1 = D
  · obtain ⟨D', rfl⟩ := hex
    rw [clusterBinProbability_self, clusterCapacityAtom_self]
    have hterm :
        (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D' *
          (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) D' y ≤
        (clusterSolver PT hPT hm g.1.1).oddMarginal g.2 (historyOnSlice W g.1) y := by
      unfold SliceSolver.oddMarginal
      exact Finset.single_le_sum (s := Finset.univ) (a := D')
        (f := fun D'' : Bin PT.tiling g.1.1 =>
          (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D'' *
          (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) D'' y)
        (fun D'' _ => mul_nonneg ((clusterSolver PT hPT hm g.1.1).q_nonneg _ _ _)
          ((clusterSolver PT hPT hm g.1.1).U_nonneg _ _ _ _)) (Finset.mem_univ _)
    have hh := mul_le_mul_of_nonneg_left hterm
      (Nat.cast_nonneg (PT.tiling.P g.1.1).h)
    nlinarith only [hh]
  · have hqzero : clusterBinProbability PT hPT hm W g D = 0 := by
      unfold clusterBinProbability
      apply Finset.sum_eq_zero
      intro D' _
      rw [if_neg (fun h => hex ⟨D', h⟩)]
    rw [hqzero, zero_mul]
    apply mul_nonneg (by positivity)
    unfold SliceSolver.oddMarginal
    apply Finset.sum_nonneg
    intro D' _
    exact mul_nonneg ((clusterSolver PT hPT hm g.1.1).q_nonneg _ _ _)
      ((clusterSolver PT hPT hm g.1.1).U_nonneg _ _ _ _)


/-- On a positive independent-bin outcome, every chosen group bin has positive probability. -/
theorem selected_bin_probability_pos (B : ClusterBinAssignment PT)
    (hB : (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0)
    (g : ClusterGroupIndex PT) :
    0 < (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) := by
  have hn : (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) ≠ 0 := by
    have hp : (∏ g : ClusterGroupIndex PT,
        (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g)) ≠ 0 := hB
    exact (Finset.prod_ne_zero_iff.mp hp) g (Finset.mem_univ _)
  exact lt_of_le_of_ne ((clusterSolver PT hPT hm g.1.1).q_nonneg _ _ _) (Ne.symm hn)

/-- Capacity avoidance enforces the label-column cap once selected atoms fit the dyadic scale. -/
theorem capacity_avoided_column_le (hκ : κ.Admissible)
    (hload : clusterHistoryLoad PT hPT hm W)
    (B : ClusterBinAssignment PT)
    (hcap : ∀ (g : ClusterGroupIndex PT) (y : Fin (T.S.N k)), (PT.tiling.P g.1.1).h *
      (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) (B g) y ≤
        ((B g).1.card : ℝ) ^ (-0.5 : ℝ))
    (havoid : clusterCapacityAvoided PT hPT hm W B) (y : Fin (T.S.N k)) :
    clusterGivenBinColumn PT hPT hm W B y ≤ κ.θ0 := by
  by_cases hex : ∃ g : ClusterGroupIndex PT,
      (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) (B g) y ≠ 0
  · obtain ⟨g0, hg0⟩ := hex
    let D := B g0
    have hyD : y ∈ D.1 := (clusterSolver PT hPT hm g0.1.1).U_support _ _ _ _ hg0
    have hD : D.1.Nonempty := ⟨y, hyD⟩
    let a : ClusterGroupIndex PT → ℝ := fun g => clusterCapacityAtom PT hPT hm W g D.1 y
    let q : ClusterGroupIndex PT → ℝ := fun g => clusterBinProbability PT hPT hm W g D.1
    let C := Finset.univ.filter fun g : ClusterGroupIndex PT => (B g).1 = D.1 ∧ 0 < a g
    let S := fun j => clusterCapacityBucket PT hPT hm W D.1 y j
    let w : ℝ := (D.1.card : ℝ) ^ (-0.5 : ℝ)
    have hw : 0 < w := by
      have hc : (0 : ℝ) < D.1.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
      dsimp [w]
      positivity
    have ha : ∀ g, 0 ≤ a g := fun g => clusterCapacityAtom_nonneg PT hPT hm W g D.1 y
    have hq : ∀ g, 0 ≤ q g := fun g => clusterBinProbability_nonneg PT hPT hm W g D.1
    have hcol : clusterGivenBinColumn PT hPT hm W B y = ∑ g ∈ C, a g := by
      rw [Finset.sum_filter]
      unfold clusterGivenBinColumn
      apply Finset.sum_congr rfl
      intro g _
      by_cases hd : (B g).1 = D.1
      · have haeq : a g = (PT.tiling.P g.1.1).h *
            (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) (B g) y := by
          dsimp [a]
          rw [← hd, clusterCapacityAtom_self]
        by_cases hp : 0 < a g
        · rw [if_pos ⟨hd, hp⟩]
          exact haeq.symm
        · rw [if_neg (fun h => hp h.2)]
          have hz : a g = 0 := le_antisymm (le_of_not_gt hp) (ha g)
          rw [← haeq, hz]
      · have hz : (clusterSolver PT hPT hm g.1.1).U g.2
            (historyOnSlice W g.1) (B g) y = 0 := by
          by_contra h
          have hy := (clusterSolver PT hPT hm g.1.1).U_support _ _ _ _ h
          exact hd (physical_bins_eq_of_mem PT hPT (B g) D y hy hyD)
        simp [hd, hz]
    have hcoverExists : ∀ g ∈ C, ∃ j : ℕ, g ∈ S j := by
      intro g hg
      have hg' := (Finset.mem_filter.mp hg).2
      have hacap : a g ≤ w := by
        have heq := clusterCapacityAtom_self PT hPT hm W g (B g) y
        dsimp [a, w]
        rw [← hg'.1, heq]
        exact hcap g y
      obtain ⟨j, hj⟩ := dyadic_bucket_exists w (a g) hw hg'.2 hacap
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      simpa [clusterBucketWidth_eq, w, a] using hj
    let idx : ClusterGroupIndex PT → ℕ := fun g =>
      if hg : g ∈ C then Classical.choose (hcoverExists g hg) else 0
    let J : Finset ℕ := C.image idx
    have hidx : ∀ g ∈ C, g ∈ S (idx g) := by
      intro g hg
      simpa [idx, hg] using Classical.choose_spec (hcoverExists g hg)
    have hcover : C = J.biUnion (fun j => S j ∩ C) := by
      ext g
      constructor
      · intro hg
        exact Finset.mem_biUnion.mpr ⟨idx g,
          Finset.mem_image.mpr ⟨g, hg, rfl⟩, Finset.mem_inter.mpr ⟨hidx g hg, hg⟩⟩
      · intro hg
        obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.mp hg
        exact (Finset.mem_inter.mp hgj).2
    have hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) S := by
      intro j hj j' hj' hne
      apply Finset.disjoint_left.mpr
      intro g hg hg'
      have hg0 := (Finset.mem_filter.mp hg).2
      have hg1 := (Finset.mem_filter.mp hg').2
      apply hne
      apply dyadic_bucket_unique w (a g) hw j j'
      · simpa [S, clusterBucketWidth_eq, w, a] using hg0
      · simpa [S, clusterBucketWidth_eq, w, a] using hg1
    have hK : (0 : ℝ) ≤ κ.Kp := by positivity
    have hcp : 0 < κ.cp := hκ.bucket.2.1
    have hloadBucket : ∀ j ∈ J, (∑ g ∈ S j ∩ C, a g) ≤
        (κ.Kp : ℝ) * (∑ g ∈ S j, q g * a g) + κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2) := by
      intro j hj
      apply selected_bucket_load_le (S j) C a (clusterBucketWidth D.1 j)
        (κ.Kp : ℝ) (clusterBucketMean PT hPT hm W D.1 y j)
        (κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2))
      · rw [clusterBucketWidth_eq]
        exact mul_pos hw (by positivity)
      · apply add_nonneg
        · apply mul_nonneg hK
          exact Finset.sum_nonneg fun g hg => mul_nonneg (hq g) (ha g)
        · positivity
      · intro g hg
        exact (Finset.mem_filter.mp hg).2.2
      · intro A hAs hcard hAC
        apply havoid g0.1.1 D y hyD j A hAs hcard
        intro g hg
        exact (Finset.mem_filter.mp (hAC hg)).2.1
    have hsum := disjoint_bucket_load_le Finset.univ C J S a q (κ.Kp : ℝ)
      (fun j => κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) ha hq hK hdisj
      (fun j _ => Finset.subset_univ _) hcover hloadBucket
    have hmean : (∑ g, q g * a g) < κ.θstar :=
      (physical_bin_mean_le PT hPT hm W D.1 y).trans_lt (hload y)
    have ht : (∑ j ∈ J, κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) ≤ 4 * κ.cp := by
      rw [← Finset.mul_sum]
      have ht := mul_le_mul_of_nonneg_left (dyadic_allowance_sum_le J) hcp.le
      nlinarith only [ht]
    rw [hcol]
    apply hsum.trans
    have hm := mul_le_mul_of_nonneg_left hmean.le hK
    rcases hκ.bucket with ⟨_, _, h1, h2, _⟩
    nlinarith only [hm, ht, h1, h2]
  · have hz : clusterGivenBinColumn PT hPT hm W B y = 0 := by
      unfold clusterGivenBinColumn
      apply Finset.sum_eq_zero
      intro g _
      have h := not_exists.mp hex g
      rw [not_not.mp h, mul_zero]
    rw [hz]
    rcases hκ.clock with ⟨_, hθ0, _⟩
    rw [hθ0]
    norm_num


/-- Bucket allowances divided by their widths grow with the bucket index. -/
theorem bucket_allowance_ratio (hκ : κ.Admissible)
    (D : Finset (Fin (T.S.N k))) (j : ℕ) :
    κ.cp * (D.card : ℝ) ^ (0.5 : ℝ) ≤
      (κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) / clusterBucketWidth D j := by
  have hcp : 0 ≤ κ.cp := hκ.bucket.2.1.le
  by_cases hc : D.card = 0
  · norm_num [hc, clusterBucketWidth, Real.zero_rpow]
  · have hd : (0 : ℝ) < D.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
    have hw : clusterBucketWidth D j =
        (D.card : ℝ) ^ (-0.5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ)) := by
      simp [clusterBucketWidth, Real.rpow_neg_natCast]
    rw [hw]
    have hr : (κ.cp * (2 : ℝ) ^ (-(j : ℝ) / 2)) /
        ((D.card : ℝ) ^ (-0.5 : ℝ) * (2 : ℝ) ^ (-(j : ℝ))) =
        κ.cp * (D.card : ℝ) ^ (0.5 : ℝ) * (2 : ℝ) ^ ((j : ℝ) / 2) := by
      have h2 : (2 : ℝ) ^ (-(j : ℝ) / 2) / (2 : ℝ) ^ (-(j : ℝ)) =
          (2 : ℝ) ^ ((j : ℝ) / 2) := by
        rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring
      rw [mul_comm ((D.card : ℝ) ^ (-0.5 : ℝ)) ((2 : ℝ) ^ (-(j : ℝ))),
        div_mul_eq_div_mul_one_div, mul_div_assoc, h2, Real.rpow_neg hd.le (0.5 : ℝ)]
      simp only [one_div, inv_inv]
      ring
    rw [hr]
    have h2 : 1 ≤ (2 : ℝ) ^ ((j : ℝ) / 2) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h2
      (mul_nonneg hcp (Real.rpow_nonneg hd.le (0.5 : ℝ)))]

/-- Summing all buckets and columns leaves the same square-root bin-size decay. -/
theorem pinned_capacity_charge_le (hκ : κ.Admissible)
    (D : Finset (Fin (T.S.N k))) (hD : D.Nonempty)
    (hlarge : 2 ≤ κ.cp * (D.card : ℝ) ^ (0.5 : ℝ)) (g : ClusterGroupIndex PT) :
    clusterPinnedCapacityCharge PT hPT hm W D g ≤
      6 * (D.card : ℝ) * Real.exp (-κ.cp * (D.card : ℝ) ^ (0.5 : ℝ) / 6) := by
  let M := 6 * Real.exp (-κ.cp * (D.card : ℝ) ^ (0.5 : ℝ) / 6)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  unfold clusterPinnedCapacityCharge
  calc
    (∑ y ∈ D, ∑' j : ℕ,
      ∑ A ∈ (clusterCapacityBucket PT hPT hm W D y j).powerset,
        if g ∈ A ∧ A.card = clusterCertificateSize PT hPT hm W D y j then
          (2 : ℝ) ^ A.card * (∏ g' ∈ A.erase g, clusterBinProbability PT hPT hm W g' D)
        else 0) ≤ ∑ y ∈ D, M := by
      apply Finset.sum_le_sum
      intro y hy
      apply tsum_pinned_bucket_le
        (fun j => clusterCapacityBucket PT hPT hm W D y j)
        (fun g => clusterBinProbability PT hPT hm W g D)
        (fun j => clusterCertificateSize PT hPT hm W D y j) g M hM
      · intro j j' hj hj'
        have hw : 0 < (D.card : ℝ) ^ (-0.5 : ℝ) := by
          have hd : (0 : ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
          positivity
        apply dyadic_bucket_unique ((D.card : ℝ) ^ (-0.5 : ℝ))
          (clusterCapacityAtom PT hPT hm W g D y) hw j j'
        · simpa [clusterBucketWidth_eq] using (Finset.mem_filter.mp hj).2
        · simpa [clusterBucketWidth_eq] using (Finset.mem_filter.mp hj').2
      · intro j
        have hr := bucket_allowance_ratio hκ (T := T) (k := k) D j
        have hcharge := cluster_bucket_pinned_charge_le PT hPT hm W hκ D y j hD
          (hlarge.trans hr) g
        apply hcharge.trans
        dsimp [M]
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
        have hw : 0 < clusterBucketWidth D j := by
          rw [clusterBucketWidth_eq]
          have hd : (0 : ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
          positivity
        apply (div_le_div_iff₀ (by positivity : 0 < 6 * clusterBucketWidth D j)
          (by norm_num : (0 : ℝ) < 6)).mpr
        have hratio := (le_div_iff₀ hw).mp hr
        nlinarith only [hratio]
    _ = _ := by simp [M]; ring


/-- Both high-cluster bin scales tend to infinity uniformly over admitted tilings. -/
theorem cluster_bin_size_eventually_ge (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (d0 : ℕ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i, d0 ≤ (PT.tiling.P i).d := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hq : Tendsto (fun k => (Real.log (T.S.n k : ℝ)) ^ κ.cq) atTop atTop :=
    (tendsto_rpow_atTop hκ.cq_rng.1).comp hlog
  have hq2 : Tendsto (fun k => (Real.log (T.S.n k : ℝ)) ^ (2 : ℕ)) atTop atTop := by
    have ht : Tendsto (fun k => (Real.log (T.S.n k : ℝ)) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp hlog
    simpa only [Real.rpow_two] using ht
  have hsqrt : Tendsto (fun k => Real.sqrt (Real.log (T.S.n k : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have hsmall : ∀ᶠ k in atTop,
      (d0 : ℝ) ≤ Real.exp ((Real.log (T.S.n k : ℝ)) ^ κ.cq / 2) :=
    (Real.tendsto_exp_atTop.comp (hq.atTop_div_const (by norm_num))).eventually_ge_atTop _
  have hlarge : ∀ᶠ k in atTop,
      (d0 : ℝ) ≤ Real.exp ((Real.log (T.S.n k : ℝ)) ^ (2 : ℕ) / 2) :=
    (Real.tendsto_exp_atTop.comp (hq2.atTop_div_const (by norm_num))).eventually_ge_atTop _
  have hcap : ∀ᶠ k in atTop,
      (d0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ))) :=
    (Real.tendsto_exp_atTop.comp hsqrt).eventually_ge_atTop _
  filter_upwards [hsmall, hlarge, hcap] with k hk1 hk2 hk3
  intro PT hPT hm i
  have hc : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨
      PT.tiling.mode = .highLarge := by tauto
  rcases hPT.tiling_valid.cluster_data hc i with
    ⟨_, _, _, hdsmall, hdlarge, _, _, _, _, _, hsmallreg, hlargereg⟩
  rcases hm with hs | hl
  · rw [hdsmall hs]
    apply le_min
    · apply Nat.le_floor
      apply hk1.trans
      apply Real.exp_le_exp.mpr
      have hlow : (Real.log (T.S.n k : ℝ)) ^ κ.cq ≤ (PT.tiling.P i).q := (hsmallreg.mp hs).1.le
      linarith only [hlow]
    · exact Nat.le_floor hk3
  · rw [hdlarge (Or.inr hl)]
    apply Nat.le_floor
    apply hk2.trans
    apply Real.exp_le_exp.mpr
    linarith [hlargereg.mp hl]

/-- The column union factor is absorbed by square-root exponential decay. -/
theorem capacity_charge_decay_eventually (cp : ℝ) (hcp : 0 < cp) :
    ∀ᶠ d : ℝ in atTop,
      2 ≤ cp * d ^ (0.5 : ℝ) ∧
      6 * d * Real.exp (-cp * d ^ (0.5 : ℝ) / 6) ≤
        Real.exp (-(cp / 12) * d ^ (0.4 : ℝ)) := by
  have hp : Tendsto (fun d : ℝ => d ^ (0.5 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hm : ∀ᶠ d : ℝ in atTop, 2 ≤ cp * d ^ (0.5 : ℝ) :=
    (hp.const_mul_atTop hcp).eventually_ge_atTop _
  have hexp : ∀ᶠ t : ℝ in atTop,
      6 ≤ Real.exp ((cp / 12) * t) / t ^ (2 : ℝ) :=
    (tendsto_exp_mul_div_rpow_atTop 2 (cp / 12) (by positivity)).eventually_ge_atTop _
  have hexpd := hp.eventually hexp
  filter_upwards [hm, hexpd, eventually_ge_atTop (1 : ℝ)] with d hd hex hd1
  refine ⟨hd, ?_⟩
  have hdpos : 0 < d := by linarith
  have hsquare : (d ^ (0.5 : ℝ)) ^ (2 : ℝ) = d := by
    rw [← Real.rpow_mul hdpos.le]
    norm_num
  rw [hsquare] at hex
  have hmain : 6 * d ≤ Real.exp ((cp / 12) * d ^ (0.5 : ℝ)) :=
    (le_div_iff₀ hdpos).mp hex
  calc
    6 * d * Real.exp (-cp * d ^ (0.5 : ℝ) / 6) ≤
        Real.exp ((cp / 12) * d ^ (0.5 : ℝ)) *
          Real.exp (-cp * d ^ (0.5 : ℝ) / 6) :=
      mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
    _ = Real.exp (-(cp / 12) * d ^ (0.5 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hp := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num : (0.4 : ℝ) ≤ 0.5)
      nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ cp / 12 by positivity)]


/-- Internal-role atoms fit the physical-bin bucket scale in both high modes. -/
theorem cluster_selected_atom_cap_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, ∀ g : ClusterGroupIndex PT,
      ∀ D : clusterBinType g,
        0 < (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) D →
        ∀ y, (PT.tiling.P g.1.1).h *
          (clusterSolver PT hPT hm g.1.1).U g.2 (historyOnSlice W g.1) D y ≤
            (D.1.card : ℝ) ^ (-0.5 : ℝ) := by
  have hMhi : 0 < (κ.Mhi : ℝ) := by
    have hc := hκ.Mhi_big.2
    by_contra h
    have hz : (κ.Mhi : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz, mul_zero] at hc
    norm_num at hc
  have haC : κ.aC < 1 / 10 ^ 6 :=
    hκ.aC_rng.2.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have hp : 4 * κ.ω * (κ.Mhi : ℝ) < 1 := by nlinarith [hκ.ω_rng.2]
  have hp4 : 4 * κ.ω * (4 * (κ.Mhi : ℝ)) < 1 := by nlinarith [hκ.ω_rng.2]
  have hscaleQ := polynomial_height_atom_scale κ.ω (κ.Mhi : ℝ) hκ.ω_rng.1 hMhi hp
  have hscaleL := polynomial_height_atom_scale κ.ω (4 * (κ.Mhi : ℝ))
    hκ.ω_rng.1 (by positivity) hp4
  obtain ⟨Q, hQ⟩ := (eventually_atTop.1 (hscaleQ.and floor_exponential_scale_eventually))
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hq1 : ∀ᶠ k in atTop, Q ≤ (Real.log (T.S.n k : ℝ)) ^ κ.cq :=
    ((tendsto_rpow_atTop hκ.cq_rng.1).comp hlog).eventually_ge_atTop _
  have hq2 : ∀ᶠ k in atTop, Q ≤ (Real.log (T.S.n k : ℝ)) ^ (2 : ℕ) := by
    have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp hlog).eventually_ge_atTop Q
    simpa only [Function.comp_apply, Real.rpow_two] using ht
  have hlogScale : ∀ᶠ k in atTop,
      (∀ h : ℝ, 1 ≤ h → h ≤ 2 * (Real.sqrt (Real.log (T.S.n k : ℝ))) ^ (4 * (κ.Mhi : ℝ)) →
        2 * h * Real.exp (1.5 * (⌈h ^ (3 * κ.ω)⌉₊ : ℝ) * (⌈h ^ κ.ω⌉₊ : ℝ)) ≤
          Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)) / 8)) ∧
      Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)) / 8) ≤
        (⌊Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)) / 2)⌋₊ : ℝ) ^ (0.5 : ℝ) :=
    (Real.tendsto_sqrt_atTop.comp hlog).eventually (hscaleL.and floor_exponential_scale_eventually)
  filter_upwards [hq1, hq2, hlogScale, hlog.eventually_ge_atTop 1,
      cluster_bin_size_eventually_ge κ hκ T 1] with k hkq1 hkq2 hkl hklog hkbin
  intro PT hPT hm W g D hD y
  let i := g.1.1
  let P := PT.tiling.P i
  have hc : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨
      PT.tiling.mode = .highLarge := by tauto
  rcases hPT.tiling_valid.cluster_data hc i with
    ⟨_, _, _, hdsmall, hdlarge, _, _, _, hhupper, _, hsreg, hlreg⟩
  have hh : 1 ≤ (P.h : ℝ) := by exact_mod_cast clusterHeight_pos PT hPT hm i
  have hhupper' : (P.h : ℝ) ≤ 2 * (P.q : ℝ) ^ (κ.Mhi : ℝ) := by
    rcases hm with hs | hl
    · have hb : (P.h : ℝ) < 2 * (P.q : ℝ) ^ (κ.Mhi : ℝ) := by simpa [hs, P] using hhupper
      exact hb.le
    · have hb : (P.h : ℝ) < 2 * (P.q : ℝ) ^ (κ.Mhi : ℝ) := by simpa [hl, P] using hhupper
      exact hb.le
  have hqQ : Q ≤ (P.q : ℝ) := by
    rcases hm with hs | hl
    · exact hkq1.trans (hsreg.mp hs).1.le
    · exact hkq2.trans (hlreg.mp hl).le
  have hqScale := (hQ (P.q : ℝ) hqQ).1 (P.h : ℝ) hh hhupper'
  have hqFloor := (hQ (P.q : ℝ) hqQ).2
  have hround : 2 * (P.h : ℝ) *
      Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) ≤ (P.d : ℝ) ^ (0.5 : ℝ) := by
    have hqbound : 2 * (P.h : ℝ) *
        Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) ≤
        (⌊Real.exp (P.q / 2)⌋₊ : ℝ) ^ (0.5 : ℝ) := by
      have hb : 2 * (P.h : ℝ) *
          Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) ≤ Real.exp (P.q / 8) := by
        simpa [Tiling.kScale, Tiling.tScale, sliceK, sliceT, P] using hqScale
      exact hb.trans hqFloor
    rcases hm with hs | hl
    · have hL : (P.q : ℝ) ≤ Real.log (T.S.n k : ℝ) ^ 2 := (hsreg.mp hs).2
      have hroot : (Real.sqrt (Real.log (T.S.n k : ℝ))) ^ (4 : ℕ) =
          Real.log (T.S.n k : ℝ) ^ 2 := by
        have he := Real.sq_sqrt (show 0 ≤ Real.log (T.S.n k : ℝ) by linarith)
        nlinarith only [he]
      have hhroot : (P.h : ℝ) ≤
          2 * (Real.sqrt (Real.log (T.S.n k : ℝ))) ^ (4 * (κ.Mhi : ℝ)) := by
        have hb := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ P.q) hL hMhi.le
        rw [← hroot, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ Real.sqrt (Real.log (T.S.n k : ℝ)))] at hb
        norm_num only [Nat.cast_ofNat] at hb
        exact hhupper'.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
      have hLb := (hkl.1 (P.h : ℝ) hh hhroot).trans hkl.2
      have hLb' : 2 * (P.h : ℝ) *
          Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) ≤
          (⌊Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)))⌋₊ : ℝ) ^ (0.5 : ℝ) := by
        have hb : 2 * (P.h : ℝ) *
            Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) ≤
            (⌊Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)) / 2)⌋₊ : ℝ) ^ (0.5 : ℝ) := by
          simpa [Tiling.kScale, Tiling.tScale, sliceK, sliceT, P] using hLb
        have he : Real.sqrt (Real.log (T.S.n k : ℝ)) / 2 ≤ Real.sqrt (Real.log (T.S.n k : ℝ)) := by
          have hn := Real.sqrt_nonneg (Real.log (T.S.n k : ℝ))
          linarith
        have hf := Nat.floor_mono (Real.exp_le_exp.mpr he)
        have hfreal : (⌊Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)) / 2)⌋₊ : ℝ) ≤
            (⌊Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)))⌋₊ : ℝ) := by exact_mod_cast hf
        exact hb.trans (Real.rpow_le_rpow (by positivity) hfreal (by norm_num))
      have hd := hdsmall hs
      change P.d = min _ _ at hd
      rw [hd]
      rcases le_total ⌊Real.exp (P.q / 2)⌋₊
          ⌊Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)))⌋₊ with hmin | hmin
      · rw [Nat.min_eq_left hmin]
        exact hqbound
      · rw [Nat.min_eq_right hmin]
        exact hLb'
    · have hd := hdlarge (Or.inr hl)
      change P.d = _ at hd
      simpa [hd] using hqbound
  have hdpos : (0 : ℝ) < P.d := by exact_mod_cast (hkbin PT hPT hm i)
  have hU := (clusterSolver PT hPT hm i).U_atom_cap g.2 (historyOnSlice W g.1) D y hD
  have hhU := mul_le_mul_of_nonneg_left hU (Nat.cast_nonneg P.h)
  have hdiv : 2 * (P.h : ℝ) * Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * (PT.tiling.tScale i : ℝ)) / P.d ≤
      (P.d : ℝ) ^ (-0.5 : ℝ) := by
    have heq : (P.d : ℝ) ^ (0.5 : ℝ) / P.d = (P.d : ℝ) ^ (-0.5 : ℝ) := by
      calc
        (P.d : ℝ) ^ (0.5 : ℝ) / P.d = (P.d : ℝ) ^ (0.5 : ℝ) / (P.d : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (P.d : ℝ) ^ (-0.5 : ℝ) := by rw [← Real.rpow_sub hdpos]; norm_num
    rw [← heq]
    exact div_le_div_of_nonneg_right hround hdpos.le
  have hcard := hPT.tiling_valid.bins_card i D.1 D.2
  rw [hcard]
  apply le_trans _ hdiv
  convert hhU using 1 <;> ring

/-- The conditional odd marginal packaged as a finite probability law. -/
noncomputable def solver_marginal_law {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r) : Law (T.S.N k) where
  w := S.oddMarginal g W
  nonneg y := Finset.sum_nonneg fun D _ => mul_nonneg (S.q_nonneg g W D) (S.U_nonneg g W D y)
  sum_eq_one := by
    unfold SliceSolver.oddMarginal
    rw [Finset.sum_comm]
    calc
      (∑ D, ∑ y, S.q g W D * S.U g W D y) = ∑ D, S.q g W D * ∑ y, S.U g W D y := by
        apply Finset.sum_congr rfl
        intro D _
        rw [Finset.mul_sum]
      _ = ∑ D, S.q g W D := by simp [S.U_sum]
      _ = 1 := S.q_sum g W

theorem solver_marginal_law_supported {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r) :
    (solver_marginal_law S g W).SupportedIn (𝒯.P i).Y := by
  intro y hy
  unfold solver_marginal_law SliceSolver.oddMarginal
  apply Finset.sum_eq_zero
  intro D _
  have hU : S.U g W D y = 0 := by
    by_contra h
    exact hy ((𝒯.P i).bins.le D.2 (S.U_support g W D y h))
  rw [hU, mul_zero]

private theorem admissible_round_exponent_le (κ : CConsts) (hκ : κ.Admissible) : 4 * κ.ω ≤ 1 := by
  have hMhi : (1 : ℝ) ≤ κ.Mhi := by
    have hpos : 0 < κ.Mhi := by
      by_contra h
      have he : κ.Mhi = 0 := Nat.eq_zero_of_not_pos h
      have hc := hκ.Mhi_big.2
      simp [he] at hc
      norm_num at hc
    exact_mod_cast hpos
  have haC : κ.aC < 1 / 10 ^ 6 :=
    hκ.aC_rng.2.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have hm := mul_le_mul_of_nonneg_left hMhi (show 0 ≤ 5 * κ.ω from mul_nonneg (by norm_num) hκ.ω_rng.1.le)
  nlinarith [hκ.ω_rng.2]

/-- Allocation and round scales give small widths uniformly over all primitive histories. -/
theorem cluster_width_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) ∧
      ∀ μ : Law (T.S.N k),
        (∀ y, μ.w y ≤ 8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) / (PT.tiling.P i).M) →
        μ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
  let A : ℝ := κ.a / 10 ^ 6 / (1000 * κ.u)
  let C : ℝ := 20 + |A|
  have hC : 0 < C := by dsimp [C]; positivity
  have hιxs : κ.ι < κ.xs / 4 := by
    have hι := hκ.ι_rng.2
    have hmin : min κ.xs (min κ.η0 0.01) ≤ κ.xs := min_le_left _ _
    linarith [hκ.xs_rng.1]
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hscale : ∀ᶠ k in atTop, C * (T.S.n k : ℝ) ^ κ.ι ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) := by
    have hs := hn.eventually (real_eventually_rpow_le_mul (p := κ.ι) (q := κ.xs / 4)
      (c := 1 / C) hιxs (by positivity))
    filter_upwards [hs] with k hk
    have hm := mul_le_mul_of_nonneg_left hk hC.le
    simpa [hC.ne', mul_assoc] using hm
  filter_upwards [hscale, hn.eventually_ge_atTop 1] with k hk hn1
  intro PT hPT hm i
  let P := PT.tiling.P i
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hM : (0 : ℝ) < P.M := by
    have hc := Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
    rw [P.cardX] at hc
    exact_mod_cast hc
  have hh : 1 ≤ (P.h : ℝ) := by exact_mod_cast clusterHeight_pos PT hPT hm i
  have hnι : 1 ≤ (T.S.n k : ℝ) ^ κ.ι := Real.one_le_rpow hn1 hκ.ι_rng.1.le
  have hhupper : (P.h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    have hmax := (hPT.tiling_valid.allocation_bounds i).1
    have hhmax : (P.h : ℝ) ≤ (max P.h P.ℓ : ℕ) := by exact_mod_cast Nat.le_max_left P.h P.ℓ
    apply hhmax.trans
    simpa [P, Nat.cast_max] using hmax.le
  have hlog : Real.log ((T.S.N k : ℝ) / P.M) ≤ |A| * P.h := by
    rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | ⟨_, hlog⟩
    · rcases hm with hs | hl
      · simp [hs] at hb
      · simp [hl] at hb
    · have hgain : PT.tiling.gain i / (1000 * κ.u) = A * P.h := by
        rcases hm with hs | hl
        · simp only [Tiling.gain, hs]
          dsimp [A, P]
          ring
        · simp only [Tiling.gain, hl]
          dsimp [A, P]
          ring
      rw [hgain] at hlog
      exact hlog.trans (mul_le_mul_of_nonneg_right (le_abs_self A) (Nat.cast_nonneg P.h))
  have ht := internal_round_product_le κ.ω (P.h : ℝ) hκ.ω_rng.1.le hh
  have hpow : (P.h : ℝ) ^ (4 * κ.ω) ≤ P.h := by
    have hp := Real.rpow_le_rpow_of_exponent_le hh (admissible_round_exponent_le κ hκ)
    simpa only [Real.rpow_one] using hp
  have hround : 2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 8 * P.h := by
    have ht' : (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 4 * (P.h : ℝ) ^ (4 * κ.ω) := by
      simpa [Tiling.kScale, Tiling.tScale, sliceK, sliceT, P] using ht
    nlinarith only [ht', hpow]
  have hexp : Real.log 8 + 2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i +
      Real.log ((T.S.N k : ℝ) / P.M) ≤ C * (T.S.n k : ℝ) ^ κ.ι := by
    have hlog8 : Real.log 8 ≤ 7 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]
    have hA := mul_le_mul_of_nonneg_left hhupper (abs_nonneg A)
    dsimp [C]
    nlinarith only [hlog8, hround, hlog, hA, hhupper, hnι]
  have hlogbd : Real.log ((T.S.N k : ℝ) / P.M) ≤ C * (T.S.n k : ℝ) ^ κ.ι := by
    have hA := mul_le_mul_of_nonneg_left hhupper (abs_nonneg A)
    dsimp [C]
    nlinarith only [hlog, hA, hnι]
  refine ⟨hlogbd.trans hk, ?_⟩
  intro μ hμ y
  apply (hμ y).trans
  have he : 8 * Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) / P.M =
      Real.exp (Real.log 8 + 2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i +
        Real.log ((T.S.N k : ℝ) / P.M)) / T.S.N k := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8), Real.exp_log (div_pos hN hM)]
    field_simp [hN.ne', hM.ne']
  rw [he]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (hexp.trans hk)) hN.le

private theorem weighted_removed_union_le {N : ℕ} {B : Type*} [DecidableEq B]
    (w : Fin N → ℝ) (hw : ∀ x, 0 ≤ w x) (A : Fin N → Prop)
    (s : Finset B) (P : B → Fin N → Prop) (t : ℝ)
    (ht : ∀ b ∈ s, (∑ x, if P b x then w x else 0) ≤ t) :
    (∑ x, if A x ∧ ∃ b ∈ s, P b x then w x else 0) ≤ (s.card : ℝ) * t := by
  calc
    (∑ x, if A x ∧ ∃ b ∈ s, P b x then w x else 0) ≤
        ∑ x, ∑ b ∈ s, if P b x then w x else 0 := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : A x ∧ ∃ b ∈ s, P b x
      · rw [if_pos hx]
        obtain ⟨b, hb, hbx⟩ := hx.2
        have hbnd := Finset.single_le_sum (s := s) (a := b)
          (f := fun b => if P b x then w x else 0)
          (fun b hb => by
            split_ifs
            · exact hw x
            · exact le_rfl) hb
        simpa [hbx] using hbnd
      · rw [if_neg hx]
        exact Finset.sum_nonneg fun b _ => by
          split_ifs
          · exact hw x
          · exact le_rfl
    _ = ∑ b ∈ s, ∑ x, if P b x then w x else 0 := Finset.sum_comm
    _ ≤ ∑ b ∈ s, t := Finset.sum_le_sum ht
    _ = _ := by simp

/-- The crossing degree filter removes exponentially small uniform mass at every history. -/
theorem cluster_crossing_removed_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, ∀ a : EvenPosition T k,
        (∑ x, if clusterJ0 PT hPT hm W a x ∧
          ∃ b ∈ clusterCrossingNeighbours PT hPT a,
            |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k then
          (Law.unifCore (PT.tiling.P (patchAt PT hPT a.1)).X
            (hPT.tiling_valid.patch_nonempty (patchAt PT hPT a.1)).1).w x else 0) ≤
          Real.exp (-(κ.α / 2) * T.S.n k) := by
  have hα : 0 < κ.α := hκ.α_rng.1
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hsmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (κ.α / 4) * T.S.n k := by
    have hx : κ.xs / 4 < 1 := by linarith [hκ.xs_rng.2]
    simpa only [Real.rpow_one] using hn.eventually
      (real_eventually_rpow_le_mul (p := κ.xs / 4) (q := 1) (c := κ.α / 4) hx (by positivity))
  have htail : ∀ᶠ k in atTop, 2 * (T.S.n k : ℝ) ≤ Real.exp ((κ.α / 4) * T.S.n k) := by
    have hlim := (tendsto_exp_mul_div_rpow_atTop 1 (κ.α / 4) (by positivity)).comp hn
    have he := hlim.eventually_ge_atTop (2 : ℝ)
    filter_upwards [he, hn.eventually_ge_atTop 1] with k hk hn1
    have hk' : 2 ≤ Real.exp ((κ.α / 4) * T.S.n k) / (T.S.n k : ℝ) := by
      simpa [Function.comp_def] using hk
    exact (le_div_iff₀ (by linarith : (0 : ℝ) < T.S.n k)).mp hk'
  filter_upwards [hDeep, cluster_width_eventually κ hκ T, hsmall, htail,
    hn.eventually_ge_atTop 1] with k hdisc hwidth hsmall htail hn1
  intro PT hPT hm W a
  let i := patchAt PT hPT a.1
  let μ := Law.unifCore (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
  have hμsupp : μ.SupportedIn (T.X k) := by
    intro x hx
    have hx' : x ∉ (PT.tiling.P i).X := by
      intro h
      exact hx (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1
        ((hPT.tiling_valid.patch_supports i).1 h))).1
    simp [μ, Law.unifCore, hx']
  have hμwidth : μ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
    have hwidthμ := Law.uniform_width (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
    rw [(PT.tiling.P i).cardX] at hwidthμ
    have hμlog : μ.WidthLE (Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) := by
      intro x
      simpa [μ, Law.unifCore, FinProb.uniform, one_div] using hwidthμ x
    exact hμlog.mono (hwidth PT hPT hm i).1
  have hxs : (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (T.S.n k : ℝ) ^ κ.xs :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hκ.xs_rng.1])
  have hbstar : 0 ≤ bstar T k := by unfold bstar; positivity
  have hper (b : OddPosition T k) :
      (∑ x, if |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k then μ.w x else 0) ≤
        2 * Real.exp (-3 * κ.α * T.S.n k / 4) := by
    let s := clusterSliceAt PT hPT b.1
    let S := clusterSolver PT hPT hm s.1
    let g := S.groupOf (solverWordAt PT hPT hm b.1)
    let ν := solver_marginal_law S g (historyOnSlice W s)
    have hνsupp : ν.SupportedIn (T.Y k) := by
      intro y hy
      apply solver_marginal_law_supported S g (historyOnSlice W s) y
      intro h
      exact hy (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports s.1).2.2.2
        ((hPT.tiling_valid.patch_supports s.1).2.2.1 h))).1
    have hνwidth : ν.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) :=
      (hwidth PT hPT hm s.1).2 ν (fun y => S.marginal_cap g (historyOnSlice W s) y)
    have hdeg (x : Fin (T.S.N k)) : deg (T.S.E k) PT.tiling.c ν.w x = clusterDegree PT hPT hm W b x := rfl
    have he := HypercubeRamsey.S12.exceptional_first hdisc PT.tiling.c
      (w₁ := (T.S.n k : ℝ) ^ (κ.xs / 4)) (W₂ := κ.α * T.S.n k)
      (w := (T.S.n k : ℝ) ^ (κ.xs / 4)) (Or.inl ⟨hxs, le_rfl⟩)
      ν hνsupp hνwidth μ hμsupp hμwidth
    have herr : (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ)) = bstar T k := by norm_num [bstar]
    simp_rw [herr, hdeg] at he
    calc
      (∑ x, if |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k then μ.w x else 0) ≤
          ∑ x, if bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2| then μ.w x else 0 := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with h h'
        · exact le_rfl
        · exfalso; apply h'; linarith
        · exact μ.nonneg x
        · exact le_rfl
      _ = ∑ x ∈ Finset.univ.filter (fun x => bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2|), μ.w x := by rw [Finset.sum_filter]
      _ ≤ 2 * Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4) - κ.α * T.S.n k) := he
      _ ≤ _ := by apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num); linarith
  have hc : (clusterCrossingNeighbours PT hPT a).card ≤ T.S.n k := by
    apply le_trans (Finset.card_le_card _) (HypercubeRamsey.Lane_q_s15_direct.star_card_le a)
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hsum := weighted_removed_union_le μ.w μ.nonneg (clusterJ0 PT hPT hm W a)
    (clusterCrossingNeighbours PT hPT a)
    (fun b x => |clusterDegree PT hPT hm W b x - 1 / 2| > 2 * bstar T k)
    (2 * Real.exp (-3 * κ.α * T.S.n k / 4)) (fun b _ => hper b)
  apply hsum.trans
  have hcc : ((clusterCrossingNeighbours PT hPT a).card : ℝ) ≤ T.S.n k := by exact_mod_cast hc
  calc
    ((clusterCrossingNeighbours PT hPT a).card : ℝ) * (2 * Real.exp (-3 * κ.α * T.S.n k / 4)) ≤
        (2 * (T.S.n k : ℝ)) * Real.exp (-3 * κ.α * T.S.n k / 4) := by
      nlinarith [mul_le_mul_of_nonneg_right hcc (Real.exp_pos (-3 * κ.α * T.S.n k / 4)).le]
    _ ≤ Real.exp ((κ.α / 4) * T.S.n k) * Real.exp (-3 * κ.α * T.S.n k / 4) :=
      mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


/-- A fixed-length encoding avoids dependent casts when comparing outside words. -/
private def slice_encoding (PT : ProfiledTiling κ T k) (s : ClusterSlice PT) : Position T k :=
  fun j => if hj : j.val < T.S.n k - (PT.tiling.P s.1).h then s.2.1 ⟨j.val, hj⟩ else false

private theorem slice_eq_gives_outside_coordinate
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v v' : Position T k) (hv : patchAt PT hPT v = i) (hv' : patchAt PT hPT v' = i)
    (hs : clusterSliceAt PT hPT v = clusterSliceAt PT hPT v')
    (j : Fin (T.S.n k)) (hj : j.val < T.S.n k - (PT.tiling.P i).h) : v j = v' j := by
  have he := congrArg (fun s => slice_encoding PT s j) hs
  simpa [slice_encoding, clusterSliceAt, outsideWord, hv, hv', hj] using he

private theorem dependent_apply_heq {A : Type*} {B : A → Type*}
    (f : ∀ a, B a) {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

private theorem slice_eq_of_outside_word_eq
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v v' : Position T k) (hv : patchAt PT hPT v = i) (hv' : patchAt PT hPT v' = i)
    (he : outsideWord PT hPT i v = outsideWord PT hPT i v') :
    clusterSliceAt PT hPT v = clusterSliceAt PT hPT v' := by
  let V := fun i : Fin PT.tiling.m => CubePos (T.S.n k - (PT.tiling.P i).h)
  let p : ∀ i, V i → Prop := fun i o => ∀ j : Fin (T.S.n k - (PT.tiling.P i).h),
    j.val < (PT.tiling.P i).ℓ →
      o j = PT.tiling.w i ⟨j.val, lt_of_lt_of_le j.isLt (Nat.sub_le _ _)⟩
  have hfst := hv.trans hv'.symm
  apply Sigma.ext hfst
  apply (Subtype.heq_iff_coe_heq (congrArg V hfst) (dependent_apply_heq p hfst)).mpr
  have hleft := dependent_apply_heq (fun j => outsideWord PT hPT j v) hv
  have hright := dependent_apply_heq (fun j => outsideWord PT hPT j v') hv'
  exact (hleft.trans (heq_of_eq he)).trans hright.symm

private theorem outsideWord_flip_internal
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v : Position T k) (j : Fin (T.S.n k)) (hj : T.S.n k - (PT.tiling.P i).h ≤ j.val) :
    outsideWord PT hPT i (flipPos v j) = outsideWord PT hPT i v := by
  funext l
  have hne : (⟨l.val, lt_of_lt_of_le l.isLt (Nat.sub_le _ _)⟩ : Fin (T.S.n k)) ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    have hl := l.isLt
    simp only at hv
    omega
  simp [outsideWord, flipPos, Function.update_of_ne hne]

/-- Every odd neighbour is a single-coordinate flip of its even center. -/
theorem adjacent_eq_flip (a : EvenPosition T k) (b : OddPosition T k) (hab : Adjacent a b) :
    ∃ j : Fin (T.S.n k), b.1 = flipPos a.1 j := by
  let D : Finset (Fin (T.S.n k)) := Finset.univ.filter fun j => a.1 j ≠ b.1 j
  have hD : D.card = 1 := by simpa [D, Adjacent, OAI.HypercubeRamsey.cube, _root_.hammingDist] using hab
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hD
  have hdiff : a.1 j ≠ b.1 j := by
    have hmem : j ∈ D := by rw [hj]; simp
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨j, ?_⟩
  funext l
  by_cases hl : l = j
  · subst l
    cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [flipPos]
  · have heq : a.1 l = b.1 l := by
      by_contra h
      have hmem : l ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hj] at hmem
      exact hl (Finset.mem_singleton.mp hmem)
    simp [flipPos, Function.update_of_ne hl, heq]

/-- Bulk neighbours flip an outside coordinate, so their raw slices are pairwise distinct. -/
theorem cluster_bulk_slices_injective
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Set.InjOn (fun b : OddPosition T k => clusterSliceAt PT hPT b.1)
      (↑(clusterBulkNeighbours PT hPT a) : Set (OddPosition T k)) := by
  intro b hb b' hb' hs
  have hb0 := (Finset.mem_filter.mp hb).2
  have hb1 := (Finset.mem_filter.mp hb').2
  obtain ⟨j, hjflip⟩ := adjacent_eq_flip a b hb0.1
  obtain ⟨j', hjflip'⟩ := adjacent_eq_flip a b' hb1.1
  let i := patchAt PT hPT a.1
  have hjout : j.val < T.S.n k - (PT.tiling.P i).h := by
    by_contra h
    have hout : outsideWord PT hPT i b.1 = outsideWord PT hPT i a.1 := by
      rw [hjflip]
      exact outsideWord_flip_internal PT hPT i a.1 j (le_of_not_gt h)
    exact hb0.2.2 (slice_eq_of_outside_word_eq PT hPT i b.1 a.1 hb0.2.1 rfl hout)
  have he := slice_eq_gives_outside_coordinate PT hPT i b.1 b'.1 hb0.2.1 hb1.2.1 hs j hjout
  have hjj : j = j' := by
    by_contra h
    rw [hjflip, hjflip'] at he
    cases ha : a.1 j <;> simp [flipPos, Function.update_of_ne h, ha] at he
  apply Subtype.ext
  rw [hjflip, hjflip', hjj]

end HypercubeRamsey.Lane_sol_s15_alarm
