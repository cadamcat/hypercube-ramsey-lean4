import HypercubeRamsey.S15.Capacity
import HypercubeRamsey.S15.ClusterNodes_q_s15_c1
import HypercubeRamsey.S09.Core.GainStage_sol_s09_conc
import HypercubeRamsey.S12.Exceptional
import HypercubeRamsey.S12.HomogeneousPeeling
import HypercubeRamsey.S12.InteractionTails
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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


/-- All primitive records in one raw slice. -/
noncomputable def raw_slice_scope (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (s : ClusterSlice PT) :
    Finset (ClusterRecordIndex PT hPT hm) := Finset.univ.filter fun r => r.1 = s

/-- The conditional degree reads only the primitive records of the odd position's slice. -/
theorem degree_depends_on_raw_slice (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) (x : Fin (T.S.N k)) :
    ClusterHistoryDependsOn (fun W => clusterDegree PT hPT hm W b x)
      (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1)) := by
  intro W W' h
  have he : historyOnSlice W (clusterSliceAt PT hPT b.1) =
      historyOnSlice W' (clusterSliceAt PT hPT b.1) := by
    funext r
    exact h ⟨clusterSliceAt PT hPT b.1, r⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  unfold clusterDegree clusterMarginal
  dsimp only
  rw [he]

/-- Finite index set of bulk neighbours of one even row. -/
abbrev BulkIndex (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :=
  {b : OddPosition T k // b ∈ clusterBulkNeighbours PT hPT a}

noncomputable instance bulk_index_fintype (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) : Fintype (BulkIndex PT hPT a) :=
  Fintype.subtype (clusterBulkNeighbours PT hPT a) (by intro b; rfl)

/-- Every primitive coordinate is consulted by at most one bulk degree. -/
theorem bulk_raw_scopes_degree_one (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (r : ClusterRecordIndex PT hPT hm) :
    (Finset.univ.filter fun b : BulkIndex PT hPT a =>
      r ∈ raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  have he := (Finset.mem_filter.mp (Finset.mem_filter.mp hb).2).2
  have he' := (Finset.mem_filter.mp (Finset.mem_filter.mp hb').2).2
  apply Subtype.ext
  exact cluster_bulk_slices_injective PT hPT a b.2 b'.2 (he.symm.trans he')


private def as_probability {A : Type*} [Fintype A] (P : FinLaw A) : FinProb A where
  w := P.w
  nonneg := P.nonneg
  sum_eq_one := P.sum_one

private theorem finite_map_expect {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (f : A → B) (g : B → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  change (FinProb.map (as_probability P) f).expect g =
    (as_probability P).expect (fun a => g (f a))
  exact FinProb.map_expect (as_probability P) f g

/-- Expectations of one slice's records have their original solver record law. -/
theorem raw_slice_expect (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (s : ClusterSlice PT)
    (F : (∀ r, (clusterSolver PT hPT hm s.1).Val r) → ℝ) :
    (clusterHistoryLaw PT hPT hm).E (fun W => F (historyOnSlice W s)) =
      ((clusterSolver PT hPT hm s.1).recLaw PT.parameter).E F := by
  let e := HypercubeRamsey.Lane_q_s15_c1.clusterHistoryCurryEquiv PT hPT hm
  calc
    (clusterHistoryLaw PT hPT hm).E (fun W => F (historyOnSlice W s)) =
        (FinLaw.map (clusterHistoryLaw PT hPT hm) e).E (fun H => F (H s)) :=
      (finite_map_expect (clusterHistoryLaw PT hPT hm) e (fun H => F (H s))).symm
    _ = (HypercubeRamsey.Lane_q_s15_c1.clusterSlicedHistoryLaw PT hPT hm).E (fun H => F (H s)) := by
      rw [HypercubeRamsey.Lane_q_s15_c1.clusterHistoryLaw_map_curry]
    _ = ((clusterSolver PT hPT hm s.1).recLaw PT.parameter).E F := by
      change (FinLaw.pi (fun s' : ClusterSlice PT =>
        (clusterSolver PT hPT hm s'.1).recLaw PT.parameter)).E (fun H => F (H s)) = _
      exact HypercubeRamsey.Lane_q_s15_c1.pi_E_coordinate
        (fun s' : ClusterSlice PT => (clusterSolver PT hPT hm s'.1).recLaw PT.parameter) s F

/-- High profiling identifies each raw conditional degree mean with the nominal profile degree. -/
theorem raw_degree_mean (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) (x : Fin (T.S.N k)) :
    (clusterHistoryLaw PT hPT hm).E (fun W => clusterDegree PT hPT hm W b x) =
      deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT b.1)).w x := by
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  let g := S.groupOf (solverWordAt PT hPT hm b.1)
  have hS : PT.solver s.1 = some S :=
    Classical.choose_spec (hPT.cluster_solver (highMode_isCluster PT hm) s.1)
  have hmean (y : Fin (T.S.N k)) :
      (S.recLaw PT.parameter).E (fun W => S.oddMarginal g W y) = (PT.π s.1).w y := by
    rw [hPT.high_profile hm s.1]
    exact (hPT.raw_profile (highMode_isCluster PT hm) s.1 S hS g y).symm
  change (clusterHistoryLaw PT hPT hm).E (fun W =>
    deg (T.S.E k) PT.tiling.c (S.oddMarginal g (historyOnSlice W s)) x) = _
  have hslice := raw_slice_expect PT hPT hm s
    (fun W => deg (T.S.E k) PT.tiling.c (S.oddMarginal g W) x)
  rw [hslice]
  calc
    (S.recLaw PT.parameter).E (fun W => deg (T.S.E k) PT.tiling.c (S.oddMarginal g W) x) =
        ∑ y, (S.recLaw PT.parameter).E (fun W => S.oddMarginal g W y) * hit (T.S.E k) PT.tiling.c x y := by
      unfold FinLaw.E deg
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro W _
      ring
    _ = ∑ y, (PT.π s.1).w y * hit (T.S.E k) PT.tiling.c x y := by simp_rw [hmean]
    _ = _ := rfl

private noncomputable def clip_half (b d : ℝ) : ℝ := max (1 / 2 - 2 * b) (min d (1 / 2 + 2 * b))

private theorem clip_half_bounds (b d : ℝ) (hb : 0 ≤ b) :
    1 / 2 - 2 * b ≤ clip_half b d ∧ clip_half b d ≤ 1 / 2 + 2 * b := by
  constructor
  · exact le_max_left _ _
  · apply max_le
    · linarith
    · exact min_le_right _ _

private theorem clip_half_eq_of_gate (b d : ℝ) (h : |d - 1 / 2| ≤ 2 * b) : clip_half b d = d := by
  rcases abs_le.mp h with ⟨hlo, hhi⟩
  unfold clip_half
  rw [min_eq_left (by linarith), max_eq_right (by linarith)]

/-- Clipping changes a degree mean by at most its raw degree-outlier probability. -/
theorem clip_probability_error_le {A : Type*} [Fintype A]
    (P : FinLaw A) (D : A → ℝ) (hD : ∀ a, 0 ≤ D a ∧ D a ≤ 1)
    (b : ℝ) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 4) :
    |P.E (fun a => clip_half b (D a)) - P.E D| ≤
      P.pr (fun a => 2 * b < |D a - 1 / 2|) := by
  have hval (a : A) : |clip_half b (D a) - D a| ≤
      if 2 * b < |D a - 1 / 2| then 1 else 0 := by
    by_cases h : 2 * b < |D a - 1 / 2|
    · rw [if_pos h]
      have hc := clip_half_bounds b (D a) hb
      apply abs_le.mpr
      constructor <;> linarith [hD a]
    · rw [if_neg h, clip_half_eq_of_gate b (D a) (le_of_not_gt h)]
      simp
  have hdiff : P.E (fun a => clip_half b (D a)) - P.E D =
      P.E (fun a => clip_half b (D a) - D a) := by
    unfold FinLaw.E
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hdiff]
  unfold FinLaw.E FinLaw.pr
  calc
    |∑ a, P.w a * (clip_half b (D a) - D a)| ≤
        ∑ a, |P.w a * (clip_half b (D a) - D a)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, P.w a * |clip_half b (D a) - D a| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (P.nonneg a)]
    _ ≤ ∑ a, if 2 * b < |D a - 1 / 2| then P.w a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      have hv := mul_le_mul_of_nonneg_left (hval a) (P.nonneg a)
      simpa only [mul_ite, mul_one, mul_zero] using hv


/-- Two-sided version of the existing scoped Hoeffding bound. -/
theorem scoped_two_sided_tail {I B : Type*} [Fintype I] [DecidableEq I]
    [Fintype B] [DecidableEq B] {O : I → Type*} [∀ i, Fintype (O i)]
    (Q : ∀ i, FinProb (O i)) (scope : B → Finset I)
    (hdegree : ∀ i, (Finset.univ.filter (fun b => i ∈ scope b)).card ≤ 1)
    (X : B → (∀ i, O i) → ℝ) (hscope : ∀ b, FinProb.DependsOn (X b) (scope b))
    (lo hi t : ℝ) (hlohi : lo < hi) (hX : ∀ b ω, lo ≤ X b ω ∧ X b ω ≤ hi)
    (hB : 0 < Fintype.card B) (ht : 0 < t) :
    (FinProb.pi Q).pr (fun ω => t ≤ |(∑ b, X b ω) - ∑ b, (FinProb.pi Q).expect (X b)|) ≤
      2 * Real.exp (-(2 * t ^ 2 / ((Fintype.card B : ℝ) * (hi - lo) ^ 2))) := by
  let R := FinProb.pi Q
  let L := fun ω => (∑ b, X b ω) ≤ (∑ b, R.expect (X b)) - t
  let U := fun ω => (∑ b, -X b ω) ≤ (∑ b, R.expect (fun ω => -X b ω)) - t
  have hneg (b : B) : R.expect (fun ω => -X b ω) = -R.expect (X b) := by
    unfold FinProb.expect
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  have hL := HypercubeRamsey.Lane_sol_s09_conc.scoped_lower_tail
    Q scope 1 (by norm_num) hdegree X hscope lo hi t hlohi hX hB ht
  have hU := HypercubeRamsey.Lane_sol_s09_conc.scoped_lower_tail
    Q scope 1 (by norm_num) hdegree (fun b ω => -X b ω)
    (fun b ω ω' h => by
      change -X b ω = -X b ω'
      rw [hscope b ω ω' h]) (-hi) (-lo) t
    (by linarith) (fun b ω => by constructor <;> linarith [hX b ω]) hB ht
  have hL' : R.pr L ≤ Real.exp (-(2 * t ^ 2 / ((Fintype.card B : ℝ) * (hi - lo) ^ 2))) := by
    simpa [R, L] using hL
  have hU' : R.pr U ≤ Real.exp (-(2 * t ^ 2 / ((Fintype.card B : ℝ) * (hi - lo) ^ 2))) := by
    simpa [R, U, show -lo - -hi = hi - lo by ring] using hU
  have he : (fun ω => t ≤ |(∑ b, X b ω) - ∑ b, R.expect (X b)|) =
      (fun ω => L ω ∨ U ω) := by
    funext ω
    apply propext
    dsimp [L, U]
    simp_rw [hneg]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    by_cases hz : 0 ≤ (∑ b, X b ω) - ∑ b, R.expect (X b)
    · rw [abs_of_nonneg hz]
      constructor
      · intro h; right; linarith
      · rintro (h | h) <;> linarith
    · rw [abs_of_neg (lt_of_not_ge hz)]
      constructor
      · intro h; left; linarith
      · rintro (h | h) <;> linarith
  change R.pr (fun ω => t ≤ |(∑ b, X b ω) - ∑ b, R.expect (X b)|) ≤ _
  rw [he]
  have hunion := FinProb.pr_union R L U
  exact hunion.trans (by linarith [hL', hU'])

/-- A small centered sum and narrow degree gates control the normalized degree product. -/
theorem degree_product_gate {G : Type*} [DecidableEq G]
    (s : Finset G) (D : G → ℝ) (d b : ℝ)
    (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 1000) (hd : (2 / 5 : ℝ) ≤ d)
    (hdgate : |d - 1 / 2| ≤ 3 * b)
    (hDgate : ∀ a ∈ s, |D a - 1 / 2| ≤ 2 * b)
    (hsize : (s.card : ℝ) * b ^ 2 ≤ 1 / 100000)
    (hsum : |(∑ a ∈ s, D a) - s.card * d| ≤ 1 / 100) :
    (1 / 2 : ℝ) ≤ (∏ a ∈ s, D a) / d ^ s.card ∧
      (∏ a ∈ s, D a) / d ^ s.card ≤ 2 := by
  have hd0 : 0 < d := by linarith
  let r : G → ℝ := fun a => (D a - d) / d
  have hD0 (a : G) (ha : a ∈ s) : 0 < D a := by
    have hlo := (abs_le.mp (hDgate a ha)).1
    linarith
  have hr (a : G) (ha : a ∈ s) : |r a| ≤ 15 * b := by
    have hdiff : |D a - d| ≤ 5 * b := by
      have ht := abs_sub_le (D a) (1 / 2) d
      rw [abs_sub_comm (1 / 2) d] at ht
      linarith [hDgate a ha]
    dsimp [r]
    rw [abs_div, abs_of_pos hd0]
    apply (div_le_iff₀ hd0).mpr
    have hp := mul_le_mul_of_nonneg_left hd (show 0 ≤ 15 * b by positivity)
    nlinarith
  have hrhalf (a : G) (ha : a ∈ s) : |r a| ≤ 1 / 2 := by
    linarith [hr a ha]
  have hrel (a : G) : 1 + r a = D a / d := by
    dsimp [r]
    field_simp [hd0.ne'] <;> ring
  have hlogerr (a : G) (ha : a ∈ s) : |Real.log (D a / d) - r a| ≤ 450 * b ^ 2 := by
    have hx : |-r a| < 1 := by rw [abs_neg]; linarith [hrhalf a ha]
    have ht := Real.abs_log_sub_add_sum_range_le hx 1
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      Nat.cast_one, pow_one, div_one, abs_neg, sub_neg_eq_add] at ht
    rw [hrel] at ht
    have hsq : |r a| ^ 2 = (r a) ^ 2 := sq_abs _
    rw [hsq] at ht
    have hden : 0 < 1 - |r a| := by linarith [hrhalf a ha]
    have hq : (r a) ^ 2 / (1 - |r a|) ≤ 2 * (r a) ^ 2 := by
      apply (div_le_iff₀ hden).mpr
      have hm := mul_le_mul_of_nonneg_left (hrhalf a ha) (sq_nonneg (r a))
      nlinarith
    have hsqb : (r a) ^ 2 ≤ 225 * b ^ 2 := by
      rcases abs_le.mp (hr a ha) with ⟨hl, hu⟩
      have hp := mul_nonneg (show 0 ≤ r a + 15 * b by linarith)
        (show 0 ≤ 15 * b - r a by linarith)
      nlinarith
    have ht' : |Real.log (D a / d) - r a| ≤ (r a) ^ 2 / (1 - |r a|) := by
      convert ht using 1
      congr 1
      ring
    exact ht'.trans (hq.trans (by nlinarith))
  have hsumr : (∑ a ∈ s, r a) = ((∑ a ∈ s, D a) - s.card * d) / d := by
    dsimp [r]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  have hsumrbd : |∑ a ∈ s, r a| ≤ 1 / 40 := by
    rw [hsumr, abs_div, abs_of_pos hd0]
    apply (div_le_iff₀ hd0).mpr
    linarith
  have hsumerr : |(∑ a ∈ s, Real.log (D a / d)) - ∑ a ∈ s, r a| ≤ 1 / 40 := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ a ∈ s, (Real.log (D a / d) - r a)| ≤
          ∑ a ∈ s, |Real.log (D a / d) - r a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ s, 450 * b ^ 2 := Finset.sum_le_sum hlogerr
      _ ≤ 1 / 40 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        nlinarith
  have hlogs : |∑ a ∈ s, Real.log (D a / d)| ≤ Real.log 2 := by
    have ht := abs_add_le ((∑ a ∈ s, Real.log (D a / d)) - ∑ a ∈ s, r a) (∑ a ∈ s, r a)
    rw [sub_add_cancel] at ht
    linarith [Real.log_two_gt_d9]
  have hprod : (∏ a ∈ s, D a) / d ^ s.card =
      Real.exp (∑ a ∈ s, Real.log (D a / d)) := by
    calc
      (∏ a ∈ s, D a) / d ^ s.card = ∏ a ∈ s, D a / d := by
        rw [Finset.prod_div_distrib, Finset.prod_const]
      _ = ∏ a ∈ s, Real.exp (Real.log (D a / d)) := by
        apply Finset.prod_congr rfl
        intro a ha
        rw [Real.exp_log (div_pos (hD0 a ha) hd0)]
      _ = _ := (Real.exp_sum s (fun a => Real.log (D a / d))).symm
  rw [hprod]
  rcases abs_le.mp hlogs with ⟨hl, hu⟩
  constructor
  · have he := Real.exp_le_exp.mpr hl
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he
  · have he := Real.exp_le_exp.mpr hu
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he

/-- Conditional degrees are probability-law hit averages. -/
theorem cluster_degree_bounds (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) (x : Fin (T.S.N k)) :
    0 ≤ clusterDegree PT hPT hm W b x ∧ clusterDegree PT hPT hm W b x ≤ 1 := by
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  let g := S.groupOf (solverWordAt PT hPT hm b.1)
  let ν := solver_marginal_law S g (historyOnSlice W s)
  have hh (y : Fin (T.S.N k)) : 0 ≤ hit (T.S.E k) PT.tiling.c x y ∧ hit (T.S.E k) PT.tiling.c x y ≤ 1 := by
    unfold hit
    split_ifs <;> norm_num
  change 0 ≤ deg (T.S.E k) PT.tiling.c ν.w x ∧ deg (T.S.E k) PT.tiling.c ν.w x ≤ 1
  constructor
  · exact Finset.sum_nonneg fun y _ => mul_nonneg (ν.nonneg y) (hh y).1
  · calc
      (∑ y, ν.w y * hit (T.S.E k) PT.tiling.c x y) ≤ ∑ y, ν.w y :=
        Finset.sum_le_sum fun y _ => by nlinarith [ν.nonneg y, (hh y).2]
      _ = 1 := ν.sum_eq_one

/-- Clipped bulk-degree sum has the independent-slice Hoeffding bound. -/
theorem clipped_bulk_degree_tail (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (x : Fin (T.S.N k))
    (hn : 0 < T.S.n k) (hB : 0 < Fintype.card (BulkIndex PT hPT a))
    (t : ℝ) (ht : 0 < t) :
    (clusterHistoryLaw PT hPT hm).pr (fun W => t ≤
      |(∑ b : BulkIndex PT hPT a, clip_half (bstar T k) (clusterDegree PT hPT hm W b.1 x)) -
        ∑ b : BulkIndex PT hPT a, (clusterHistoryLaw PT hPT hm).E
          (fun W => clip_half (bstar T k) (clusterDegree PT hPT hm W b.1 x))|) ≤
      2 * Real.exp (-(2 * t ^ 2 /
        ((Fintype.card (BulkIndex PT hPT a) : ℝ) * (4 * bstar T k) ^ 2))) := by
  let Q : ∀ r : ClusterRecordIndex PT hPT hm, FinProb (ClusterRecordValue r) := fun r =>
    ⟨(clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_nonneg PT.parameter r.2,
      (clusterSolver PT hPT hm r.1.1).lawRec_sum PT.parameter r.2⟩
  let scope := fun b : BulkIndex PT hPT a => raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1)
  let X := fun (b : BulkIndex PT hPT a) (W : ClusterHistory PT hPT hm) =>
    clip_half (bstar T k) (clusterDegree PT hPT hm W b.1 x)
  have hb : 0 < bstar T k := by
    unfold bstar
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hscope : ∀ b, FinProb.DependsOn (X b) (scope b) := by
    intro b W W' h
    change clip_half (bstar T k) (clusterDegree PT hPT hm W b.1 x) =
      clip_half (bstar T k) (clusterDegree PT hPT hm W' b.1 x)
    have hd : clusterDegree PT hPT hm W b.1 x = clusterDegree PT hPT hm W' b.1 x := by
      simpa only using degree_depends_on_raw_slice PT hPT hm b.1 x W W' h
    rw [hd]
  have hh := scoped_two_sided_tail Q scope
    (bulk_raw_scopes_degree_one PT hPT hm a) X hscope
    (1 / 2 - 2 * bstar T k) (1 / 2 + 2 * bstar T k) t
    (by linarith) (fun b W => clip_half_bounds _ _ hb.le) hB ht
  convert hh using 1
  · rfl
  · congr 3
    ring

/-- Eventually each row has a coordinate outside both its prefix and internal block. -/
theorem bulk_nonempty_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ a : EvenPosition T k, (clusterBulkNeighbours PT hPT a).Nonempty := by
  have hι : κ.ι < 1 := by
    have hm : min κ.xs (min κ.η0 0.01) ≤ κ.xs := min_le_left _ _
    linarith [hκ.ι_rng.2, hκ.xs_rng.2]
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hsmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ κ.ι ≤ (1 / 4) * T.S.n k := by
    simpa only [Real.rpow_one] using hn.eventually
      (real_eventually_rpow_le_mul (p := κ.ι) (q := 1) (c := 1 / 4) hι (by norm_num))
  filter_upwards [hsmall, hn.eventually_ge_atTop 1] with k hk hn1
  intro PT hPT a
  let i := patchAt PT hPT a.1
  let P := PT.tiling.P i
  have hlen : P.ℓ + P.h < T.S.n k := by
    have hm := (hPT.tiling_valid.allocation_bounds i).1
    have hl : (P.ℓ : ℝ) ≤ max (P.h : ℝ) (P.ℓ : ℝ) := le_max_right _ _
    have hh : (P.h : ℝ) ≤ max (P.h : ℝ) (P.ℓ : ℝ) := le_max_left _ _
    have hreal : (P.ℓ : ℝ) + P.h < T.S.n k := by nlinarith
    exact_mod_cast hreal
  let j : Fin (T.S.n k) := ⟨P.ℓ, by omega⟩
  let v := flipPos a.1 j
  have hv : ¬ HypercubeRamsey.IsEvenRole v := by
    intro h
    exact ((evenRole_flipPos a.1 j).mp h) a.2
  let b : OddPosition T k := ⟨v, hv⟩
  have haLeaf : a.1 ∈ PT.tiling.leaf i :=
    (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).1
  have hvLeaf : v ∈ PT.tiling.leaf i := by
    intro l hl
    have hne : l ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      change l.val = P.ℓ at hval
      change l.val < P.ℓ at hl
      omega
    simp only [v, flipPos, Function.update_of_ne hne]
    exact haLeaf l hl
  have hpatch : patchAt PT hPT b.1 = i :=
    HypercubeRamsey.Lane_q_s15_direct.patchAt_eq_of_leaf PT hPT i b.1 hvLeaf
  have hslice : clusterSliceAt PT hPT b.1 ≠ clusterSliceAt PT hPT a.1 := by
    intro h
    have hj : j.val < T.S.n k - (PT.tiling.P i).h := by
      change P.ℓ < T.S.n k - P.h
      omega
    have he := slice_eq_gives_outside_coordinate PT hPT i b.1 a.1 hpatch rfl h j hj
    cases ha : a.1 j <;> simp [b, v, flipPos, ha] at he
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hpatch, hslice⟩⟩
  have hadj := cubeFlip_adj a.1 j
  simpa [Adjacent, b, v, cubeFlip, flipPos] using hadj

/-- Every fixed conditional marginal has exponentially few degree outliers in every patch. -/
theorem cluster_degree_outlier_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, ∀ i, ∀ b : OddPosition T k,
        (∑ x, if 2 * bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2| then
          (Law.unifCore (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1).w x else 0) ≤
          2 * Real.exp (-3 * κ.α * T.S.n k / 4) := by
  have hα : 0 < κ.α := hκ.α_rng.1
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hsmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (κ.α / 4) * T.S.n k := by
    have hx : κ.xs / 4 < 1 := by linarith [hκ.xs_rng.2]
    simpa only [Real.rpow_one] using hn.eventually
      (real_eventually_rpow_le_mul (p := κ.xs / 4) (q := 1) (c := κ.α / 4) hx (by positivity))
  filter_upwards [hDeep, cluster_width_eventually κ hκ T, hsmall,
    hn.eventually_ge_atTop 1] with k hdisc hwidth hsmall hn1
  intro PT hPT hm W i b
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

private theorem finite_probability_bounds {A : Type*} [Fintype A] (P : FinLaw A) (E : A → Prop) :
    0 ≤ P.pr E ∧ P.pr E ≤ 1 := by
  constructor
  · unfold FinLaw.pr
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact P.nonneg a
    · exact le_rfl
  · calc
      P.pr E ≤ ∑ a, P.w a := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs
        · exact le_rfl
        · exact P.nonneg a
      _ = 1 := P.sum_one

private theorem finite_expectation_bounds {A : Type*} [Fintype A]
    (P : FinLaw A) (f : A → ℝ) (lo hi : ℝ) (hf : ∀ a, lo ≤ f a ∧ f a ≤ hi) :
    lo ≤ P.E f ∧ P.E f ≤ hi := by
  have hconst (c : ℝ) : (∑ a, P.w a * c) = c := by rw [← Finset.sum_mul, P.sum_one, one_mul]
  constructor
  · rw [← hconst lo]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a).1 (P.nonneg a)
  · rw [← hconst hi]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a).2 (P.nonneg a)

private theorem finite_fubini_probability {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (Q : FinLaw B) (E : A → B → Prop) :
    Q.E (fun b => P.pr (fun a => E a b)) = P.E (fun a => Q.pr (E a)) := by
  unfold FinLaw.E FinLaw.pr
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

private theorem finite_expectation_sum {A B : Type*} [Fintype A] [DecidableEq B]
    (P : FinLaw A) (s : Finset B) (f : B → A → ℝ) :
    P.E (fun a => ∑ b ∈ s, f b a) = ∑ b ∈ s, P.E (f b) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

private theorem finite_probability_exists_le {A B : Type*} [Fintype A] [DecidableEq B]
    (P : FinLaw A) (s : Finset B) (E : B → A → Prop) :
    P.pr (fun a => ∃ b ∈ s, E b a) ≤ ∑ b ∈ s, P.pr (E b) := by
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : ∃ b ∈ s, E b a
  · rw [if_pos h]
    obtain ⟨b, hb, hba⟩ := h
    have hs := Finset.single_le_sum (s := s) (a := b)
      (f := fun b => if E b a then P.w a else 0)
      (fun b _ => by
        split_ifs
        · exact P.nonneg a
        · exact le_rfl) hb
    simpa [hba] using hs
  · rw [if_neg h]
    exact Finset.sum_nonneg fun b _ => by
      split_ifs
      · exact P.nonneg a
      · exact le_rfl

/-- Pointwise probability bound for the product-of-degrees test. -/
theorem degree_product_failure_le {A G : Type*} [Fintype A] [DecidableEq G]
    (P : FinLaw A) (s : Finset G) (hs : s.Nonempty) (D : G → A → ℝ)
    (d b δ ε : ℝ) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 1000)
    (hδb : δ ≤ b) (hδt : δ ≤ 1 / 200)
    (hD : ∀ g ∈ s, ∀ a, 0 ≤ D g a ∧ D g a ≤ 1)
    (hmean : ∀ g ∈ s, P.E (D g) = d)
    (hbad : (∑ g ∈ s, P.pr (fun a => 2 * b < |D g a - 1 / 2|)) ≤ δ)
    (hsize : (s.card : ℝ) * b ^ 2 ≤ 1 / 100000)
    (htail : P.pr (fun a => (1 / 200 : ℝ) ≤
      |(∑ g ∈ s, clip_half b (D g a)) - ∑ g ∈ s, P.E (fun a => clip_half b (D g a))|) ≤ ε) :
    P.pr (fun a => ¬ ((∀ g ∈ s, |D g a - 1 / 2| ≤ 2 * b) ∧
      0 < d ∧ (1 / 2 : ℝ) ≤ (∏ g ∈ s, D g a) / d ^ s.card ∧
        (∏ g ∈ s, D g a) / d ^ s.card ≤ 2)) ≤ δ + ε := by
  let C := fun g => P.E (fun a => clip_half b (D g a))
  let q := fun g => P.pr (fun a => 2 * b < |D g a - 1 / 2|)
  have hq : ∀ g, 0 ≤ q g := fun g => (finite_probability_bounds P _).1
  have herr (g : G) (hg : g ∈ s) : |C g - d| ≤ q g := by
    have h := clip_probability_error_le P (D g) (hD g hg) b hb (by linarith)
    rw [hmean g hg] at h
    exact h
  have hqle (g : G) (hg : g ∈ s) : q g ≤ δ :=
    (Finset.single_le_sum (fun g _ => hq g) hg).trans hbad
  obtain ⟨g0, hg0⟩ := hs
  have hCrange := finite_expectation_bounds P (fun a => clip_half b (D g0 a))
    (1 / 2 - 2 * b) (1 / 2 + 2 * b) (fun a => clip_half_bounds b (D g0 a) hb)
  have hdgate : |d - 1 / 2| ≤ 3 * b := by
    have herror := (herr g0 hg0).trans (hqle g0 hg0)
    rcases abs_le.mp herror with ⟨hl, hu⟩
    apply abs_le.mpr
    constructor <;> linarith
  have hd : (2 / 5 : ℝ) ≤ d := by
    have hl := (abs_le.mp hdgate).1
    linarith
  have hd0 : 0 < d := by linarith
  have hsumerr : |(∑ g ∈ s, C g) - s.card * d| ≤ δ := by
    have heq : (∑ g ∈ s, C g) - s.card * d = ∑ g ∈ s, (C g - d) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [heq]
    calc
      |∑ g ∈ s, (C g - d)| ≤ ∑ g ∈ s, |C g - d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g ∈ s, q g := Finset.sum_le_sum herr
      _ ≤ δ := hbad
  let O := fun a => ∃ g ∈ s, 2 * b < |D g a - 1 / 2|
  let T := fun a => (1 / 200 : ℝ) ≤ |(∑ g ∈ s, clip_half b (D g a)) - ∑ g ∈ s, C g|
  have hsub (a : A) (h : ¬ ((∀ g ∈ s, |D g a - 1 / 2| ≤ 2 * b) ∧
      0 < d ∧ (1 / 2 : ℝ) ≤ (∏ g ∈ s, D g a) / d ^ s.card ∧
        (∏ g ∈ s, D g a) / d ^ s.card ≤ 2)) : O a ∨ T a := by
    by_cases ho : O a
    · exact Or.inl ho
    · by_cases ht : T a
      · exact Or.inr ht
      · exfalso
        apply h
        have hgates : ∀ g ∈ s, |D g a - 1 / 2| ≤ 2 * b := by
          intro g hg
          by_contra hb
          exact ho ⟨g, hg, lt_of_not_ge hb⟩
        have hclip : (∑ g ∈ s, clip_half b (D g a)) = ∑ g ∈ s, D g a := by
          apply Finset.sum_congr rfl
          intro g hg
          exact clip_half_eq_of_gate b (D g a) (hgates g hg)
        have hdiff : |(∑ g ∈ s, D g a) - ∑ g ∈ s, C g| ≤ 1 / 200 := by
          have hlt := lt_of_not_ge ht
          change |(∑ g ∈ s, clip_half b (D g a)) - ∑ g ∈ s, C g| < 1 / 200 at hlt
          rw [hclip] at hlt
          exact hlt.le
        have hsum : |(∑ g ∈ s, D g a) - s.card * d| ≤ 1 / 100 := by
          have htriangle := abs_add_le ((∑ g ∈ s, D g a) - ∑ g ∈ s, C g)
            ((∑ g ∈ s, C g) - s.card * d)
          rw [sub_add_sub_cancel] at htriangle
          linarith
        have hp := degree_product_gate s (fun g => D g a) d b hb hbsmall hd hdgate hgates hsize hsum
        exact ⟨hgates, hd0, hp.1, hp.2⟩
  calc
    _ ≤ P.pr (fun a => O a ∨ T a) :=
      HypercubeRamsey.Lane_q_s15_direct.finLaw_pr_mono P _ _ hsub
    _ ≤ P.pr O + P.pr T := HypercubeRamsey.Lane_q_s15_direct.finLaw_pr_union P O T
    _ ≤ δ + ε := add_le_add ((finite_probability_exists_le P s (fun g a => 2 * b < |D g a - 1 / 2|)).trans hbad) htail


private theorem bulk_card_le (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    (clusterBulkNeighbours PT hPT a).card ≤ T.S.n k := by
  apply le_trans (Finset.card_le_card _) (HypercubeRamsey.Lane_q_s15_direct.star_card_le a)
  intro b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩

/-- The actual bulk-product failure bound at a first label with small raw outlier probability. -/
theorem raw_J0_failure_bound_at (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (x : Fin (T.S.N k))
    (hn : 0 < T.S.n k) (hs : (clusterBulkNeighbours PT hPT a).Nonempty)
    (hbsmall : bstar T k ≤ 1 / 1000)
    (hsize : (T.S.n k : ℝ) * (bstar T k) ^ 2 ≤ 1 / 100000)
    (δ : ℝ) (hδb : δ ≤ bstar T k) (hδt : δ ≤ 1 / 200)
    (htail : (T.S.n k : ℝ) ^ (0.5 : ℝ) ≤ 1 / (320000 * (T.S.n k : ℝ) * (bstar T k) ^ 2))
    (hx : x ∈ (PT.tiling.P (patchAt PT hPT a.1)).X)
    (hbad : (∑ b ∈ clusterBulkNeighbours PT hPT a,
      (clusterHistoryLaw PT hPT hm).pr
        (fun W => 2 * bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2|)) ≤ δ) :
    (clusterHistoryLaw PT hPT hm).pr (fun W => ¬ clusterJ0 PT hPT hm W a x) ≤
      δ + 2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ)) := by
  let S := clusterBulkNeighbours PT hPT a
  let P := clusterHistoryLaw PT hPT hm
  let d := deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w x
  have hb : 0 < bstar T k := by unfold bstar; exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  have hmc : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hmle : (S.card : ℝ) ≤ T.S.n k := by exact_mod_cast bulk_card_le PT hPT a
  have hB : 0 < Fintype.card (BulkIndex PT hPT a) := by
    simpa [BulkIndex, Fintype.card_coe] using Finset.card_pos.mpr hs
  have hct := clipped_bulk_degree_tail PT hPT hm a x hn hB (1 / 200) (by norm_num)
  have hsum1 (W : ClusterHistory PT hPT hm) :
      (∑ b : BulkIndex PT hPT a, clip_half (bstar T k) (clusterDegree PT hPT hm W b.1 x)) =
      ∑ b ∈ S, clip_half (bstar T k) (clusterDegree PT hPT hm W b x) := by
    exact Finset.sum_coe_sort S
      (fun b : OddPosition T k => clip_half (bstar T k) (clusterDegree PT hPT hm W b x))
  have hsum2 : (∑ b : BulkIndex PT hPT a, P.E
      (fun W => clip_half (bstar T k) (clusterDegree PT hPT hm W b.1 x))) =
      ∑ b ∈ S, P.E (fun W => clip_half (bstar T k) (clusterDegree PT hPT hm W b x)) := by
    exact Finset.sum_coe_sort S
      (fun b : OddPosition T k => P.E (fun W => clip_half (bstar T k) (clusterDegree PT hPT hm W b x)))
  have hcard : Fintype.card (BulkIndex PT hPT a) = S.card := by exact Fintype.card_coe S
  simp_rw [hsum1] at hct
  rw [hcard] at hct
  have hct' : P.pr (fun W => (1 / 200 : ℝ) ≤
      |(∑ b ∈ S, clip_half (bstar T k) (clusterDegree PT hPT hm W b x)) -
      ∑ b ∈ S, P.E (fun W => clip_half (bstar T k) (clusterDegree PT hPT hm W b x))|) ≤
        2 * Real.exp (-(1 / (320000 * (S.card : ℝ) * (bstar T k) ^ 2))) := by
    have heq : 2 * (1 / 200 : ℝ) ^ 2 / ((S.card : ℝ) * (4 * bstar T k) ^ 2) =
        1 / (320000 * (S.card : ℝ) * (bstar T k) ^ 2) := by field_simp <;> ring
    change P.pr _ ≤ _ at hct
    rw [hsum2] at hct
    simpa only [heq] using hct
  have hinv : 1 / (320000 * (T.S.n k : ℝ) * (bstar T k) ^ 2) ≤
      1 / (320000 * (S.card : ℝ) * (bstar T k) ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hmle (sq_nonneg (bstar T k))]
  have hct'' : P.pr (fun W => (1 / 200 : ℝ) ≤
      |(∑ b ∈ S, clip_half (bstar T k) (clusterDegree PT hPT hm W b x)) -
      ∑ b ∈ S, P.E (fun W => clip_half (bstar T k) (clusterDegree PT hPT hm W b x))|) ≤
        2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ)) := by
    apply hct'.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
    linarith [htail.trans hinv]
  have hp := degree_product_failure_le P S hs
    (fun b W => clusterDegree PT hPT hm W b x) d (bstar T k) δ
    (2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ))) hb.le hbsmall hδb hδt
    (fun b hb W => cluster_degree_bounds PT hPT hm W b x)
    (fun b hb => by
      rw [raw_degree_mean]
      have hpatch := (Finset.mem_filter.mp hb).2.2.1
      simp only [d, hpatch]) hbad
    ((mul_le_mul_of_nonneg_right hmle (sq_nonneg (bstar T k))).trans hsize) hct''
  simpa [clusterJ0, hx, S, d, P] using hp

private theorem finite_mean_removed_bound {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (Q : FinLaw B) (E : A → B → Prop) (φ : B → ℝ)
    (hφ : ∀ b, 0 ≤ φ b) (δ η ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hmean : Q.E φ ≤ η)
    (hpoint : ∀ b, Q.w b ≠ 0 → φ b ≤ δ → P.pr (fun a => E a b) ≤ ε) :
    P.E (fun a => Q.pr (E a)) ≤ η / δ + ε := by
  rw [← finite_fubini_probability]
  have hmark := HypercubeRamsey.Lane_q_s15_c1.finLaw_pr_gt_le_E_div Q φ hφ δ hδ
  calc
    Q.E (fun b => P.pr (fun a => E a b)) ≤ Q.pr (fun b => δ < φ b) + ε := by
      have he : Q.pr (fun b => δ < φ b) + ε =
          ∑ b, ((if δ < φ b then Q.w b else 0) + Q.w b * ε) := by
        unfold FinLaw.pr
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Q.sum_one, one_mul]
      rw [he]
      apply Finset.sum_le_sum
      intro b _
      by_cases hw : Q.w b = 0
      · simp [hw]
      · by_cases hbad : δ < φ b
        · rw [if_pos hbad]
          have hp := (finite_probability_bounds P (fun a => E a b)).2
          nlinarith [Q.nonneg b, mul_le_mul_of_nonneg_left hp (Q.nonneg b), mul_nonneg (Q.nonneg b) hε]
        · rw [if_neg hbad, zero_add]
          exact mul_le_mul_of_nonneg_left (hpoint b hw (le_of_not_gt hbad)) (Q.nonneg b)
    _ ≤ Q.E φ / δ + ε := add_le_add hmark le_rfl
    _ ≤ η / δ + ε := add_le_add (div_le_div_of_nonneg_right hmean hδ.le) le_rfl

noncomputable def uniform_first_law (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (i : Fin PT.tiling.m) : FinLaw (Fin (T.S.N k)) where
  w := (Law.unifCore (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1).w
  nonneg := (Law.unifCore (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1).nonneg
  sum_one := (Law.unifCore (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1).sum_eq_one

noncomputable def bulk_outlier_sum (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : ℝ :=
  ∑ b ∈ clusterBulkNeighbours PT hPT a, (clusterHistoryLaw PT hPT hm).pr
    (fun W => 2 * bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2|)

/-- Averaging the per-history uniform outlier bounds controls the first-label exceptional set. -/
theorem mean_bulk_outliers_le (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (η : ℝ) (hη : 0 ≤ η)
    (hout : ∀ W : ClusterHistory PT hPT hm, ∀ b ∈ clusterBulkNeighbours PT hPT a,
      (∑ x, if 2 * bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2| then
        (uniform_first_law PT hPT (patchAt PT hPT a.1)).w x else 0) ≤ η) :
    (uniform_first_law PT hPT (patchAt PT hPT a.1)).E (bulk_outlier_sum PT hPT hm a) ≤
      (T.S.n k : ℝ) * η := by
  let Q := uniform_first_law PT hPT (patchAt PT hPT a.1)
  let P := clusterHistoryLaw PT hPT hm
  let S := clusterBulkNeighbours PT hPT a
  unfold bulk_outlier_sum
  rw [finite_expectation_sum]
  calc
    (∑ b ∈ S, Q.E (fun x => P.pr (fun W => 2 * bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2|))) ≤
        ∑ b ∈ S, η := by
      apply Finset.sum_le_sum
      intro b hb
      rw [finite_fubini_probability]
      exact (finite_expectation_bounds P _ 0 η
        (fun W => ⟨(finite_probability_bounds Q _).1, hout W b hb⟩)).2
    _ = (S.card : ℝ) * η := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast bulk_card_le PT hPT a) hη

/-- The expected uniform mass removed by J0 is small before the final alarm Markov step. -/
theorem mean_J0_removed_le (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (hn : 0 < T.S.n k)
    (hs : (clusterBulkNeighbours PT hPT a).Nonempty)
    (hbsmall : bstar T k ≤ 1 / 1000)
    (hsize : (T.S.n k : ℝ) * (bstar T k) ^ 2 ≤ 1 / 100000)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
    (hδb : δ ≤ bstar T k) (hδt : δ ≤ 1 / 200)
    (htail : (T.S.n k : ℝ) ^ (0.5 : ℝ) ≤ 1 / (320000 * (T.S.n k : ℝ) * (bstar T k) ^ 2))
    (hout : ∀ W : ClusterHistory PT hPT hm, ∀ b ∈ clusterBulkNeighbours PT hPT a,
      (∑ x, if 2 * bstar T k < |clusterDegree PT hPT hm W b x - 1 / 2| then
        (uniform_first_law PT hPT (patchAt PT hPT a.1)).w x else 0) ≤ η) :
    (clusterHistoryLaw PT hPT hm).E (fun W =>
      ∑ x, if clusterJ0 PT hPT hm W a x then 0 else
        (uniform_first_law PT hPT (patchAt PT hPT a.1)).w x) ≤
      (T.S.n k : ℝ) * η / δ + δ + 2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ)) := by
  let P := clusterHistoryLaw PT hPT hm
  let Q := uniform_first_law PT hPT (patchAt PT hPT a.1)
  let φ := bulk_outlier_sum PT hPT hm a
  have hφ : ∀ x, 0 ≤ φ x := by
    intro x
    unfold φ bulk_outlier_sum
    exact Finset.sum_nonneg fun b _ => (finite_probability_bounds P _).1
  have hmass := finite_mean_removed_bound P Q
    (fun W x => ¬ clusterJ0 PT hPT hm W a x) φ hφ δ ((T.S.n k : ℝ) * η)
    (δ + 2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ))) hδ (by positivity)
    (mean_bulk_outliers_le PT hPT hm a η hη hout) (by
      intro x hx hgood
      have hxX : x ∈ (PT.tiling.P (patchAt PT hPT a.1)).X := by
        by_contra h
        apply hx
        simp [Q, uniform_first_law, Law.unifCore, h]
      exact raw_J0_failure_bound_at PT hPT hm a x hn hs hbsmall hsize δ hδb hδt htail hxX hgood)
  have he (W : ClusterHistory PT hPT hm) : Q.pr (fun x => ¬ clusterJ0 PT hPT hm W a x) =
      ∑ x, if clusterJ0 PT hPT hm W a x then 0 else Q.w x := by
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : clusterJ0 PT hPT hm W a x <;> simp [h]
  simp_rw [he] at hmass
  simpa only [add_assoc] using hmass

private theorem degree_bsquare (n : ℝ) (hn : 0 < n) :
    n * (n ^ (-0.96 : ℝ)) ^ 2 = n ^ (-0.92 : ℝ) := by
  have hs : (n ^ (-0.96 : ℝ)) ^ 2 = n ^ (-1.92 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    norm_num
  rw [hs]
  convert (Real.rpow_add hn (1 : ℝ) (-1.92 : ℝ)).symm using 1 <;> norm_num

private theorem degree_removed_decay (α : ℝ) (hα : 0 < α) :
    ∀ᶠ n : ℝ in atTop,
      2 * n * Real.exp (-α * n / 2) + Real.exp (-α * n / 4) +
        2 * Real.exp (-n ^ (0.5 : ℝ)) ≤ Real.exp (-2 * n ^ (0.2 : ℝ)) := by
  have hlin : ∀ᶠ n : ℝ in atTop, 3 * n ≤ Real.exp ((α / 8) * n) := by
    have he := (tendsto_exp_mul_div_rpow_atTop 1 (α / 8) (by positivity)).eventually_ge_atTop (3 : ℝ)
    filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with n hn hn1
    have hn' : 3 ≤ Real.exp ((α / 8) * n) / n := by simpa using hn
    exact (le_div_iff₀ (by linarith)).mp hn'
  have hhalf : ∀ᶠ n : ℝ in atTop, 2 ≤ Real.exp (n ^ (0.5 : ℝ) / 2) :=
    (Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.5)).atTop_div_const (by norm_num))).eventually_ge_atTop _
  have hsmall1 : ∀ᶠ n : ℝ in atTop, n ^ (0.2 : ℝ) ≤ (α / 24) * n := by
    simpa only [Real.rpow_one] using real_eventually_rpow_le_mul
      (p := 0.2) (q := 1) (c := α / 24) (by norm_num) (by positivity)
  have hsmall2 : ∀ᶠ n : ℝ in atTop, n ^ (0.2 : ℝ) ≤ (1 / 6) * n ^ (0.5 : ℝ) :=
    real_eventually_rpow_le_mul (by norm_num) (by norm_num)
  have hfactor : ∀ᶠ n : ℝ in atTop, 2 ≤ Real.exp (n ^ (0.2 : ℝ)) :=
    (Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.2))).eventually_ge_atTop _
  filter_upwards [hlin, hhalf, hsmall1, hsmall2, hfactor, eventually_ge_atTop (1 : ℝ)]
    with n hnlin hnhalf hnsmall1 hnsmall2 hnfactor hn1
  have hpos : 0 < n := by linarith
  have hfirst : 2 * n * Real.exp (-α * n / 2) + Real.exp (-α * n / 4) ≤
      Real.exp (-3 * n ^ (0.2 : ℝ)) := by
    have he : Real.exp (-α * n / 2) ≤ Real.exp (-α * n / 4) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      _ ≤ 3 * n * Real.exp (-α * n / 4) := by
        have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * n by positivity)
        have h1 := mul_le_mul_of_nonneg_right hn1 (Real.exp_pos (-α * n / 4)).le
        nlinarith
      _ ≤ Real.exp ((α / 8) * n) * Real.exp (-α * n / 4) :=
        mul_le_mul_of_nonneg_right hnlin (Real.exp_pos _).le
      _ = Real.exp (-(α / 8) * n) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by apply Real.exp_le_exp.mpr; nlinarith
  have hsecond : 2 * Real.exp (-n ^ (0.5 : ℝ)) ≤ Real.exp (-3 * n ^ (0.2 : ℝ)) := by
    calc
      _ ≤ Real.exp (n ^ (0.5 : ℝ) / 2) * Real.exp (-n ^ (0.5 : ℝ)) :=
        mul_le_mul_of_nonneg_right hnhalf (Real.exp_pos _).le
      _ = Real.exp (-n ^ (0.5 : ℝ) / 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by apply Real.exp_le_exp.mpr; linarith
  calc
    _ ≤ 2 * Real.exp (-3 * n ^ (0.2 : ℝ)) := by linarith
    _ ≤ Real.exp (n ^ (0.2 : ℝ)) * Real.exp (-3 * n ^ (0.2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hnfactor (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Uniform numerical slack for the clipped-degree alarm proof. -/
theorem degree_alarm_numeric_eventually (T : Stage) (α : ℝ) (hα : 0 < α) :
    ∀ᶠ k in atTop,
      0 < T.S.n k ∧ bstar T k ≤ 1 / 1000 ∧
      (T.S.n k : ℝ) * (bstar T k) ^ 2 ≤ 1 / 100000 ∧
      Real.exp (-α * T.S.n k / 4) ≤ bstar T k ∧
      Real.exp (-α * T.S.n k / 4) ≤ 1 / 200 ∧
      (T.S.n k : ℝ) ^ (0.5 : ℝ) ≤ 1 / (320000 * (T.S.n k : ℝ) * (bstar T k) ^ 2) ∧
      2 * (T.S.n k : ℝ) * Real.exp (-α * T.S.n k / 2) +
        Real.exp (-α * T.S.n k / 4) + 2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ)) ≤
          Real.exp (-2 * (T.S.n k : ℝ) ^ (0.2 : ℝ)) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hb : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-0.96 : ℝ) ≤ 1 / 1000 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn).eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 1000))
  have hs : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-0.92 : ℝ) ≤ 1 / 100000 :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.92)).comp hn).eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100000))
  have hδlim : Tendsto (fun k => Real.exp (-α * T.S.n k / 4)) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (α / 4) (by positivity)).comp hn
    convert h using 1
    funext k
    simp only [Function.comp_apply, Real.rpow_zero, one_mul]
    congr 1
    ring
  have hδ : ∀ᶠ k in atTop, Real.exp (-α * T.S.n k / 4) ≤ 1 / 200 :=
    hδlim.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 200))
  have hδratio : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (0.96 : ℝ) * Real.exp (-(α / 4) * T.S.n k) ≤ 1 :=
    ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0.96 (α / 4) (by positivity)).comp hn).eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have htail : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (0.5 : ℝ) ≤ (1 / 320000) * (T.S.n k : ℝ) ^ (0.92 : ℝ) :=
    hn.eventually (real_eventually_rpow_le_mul (by norm_num) (by norm_num))
  filter_upwards [hb, hs, hδ, hδratio, htail, hn.eventually_ge_atTop 1,
    hn.eventually (degree_removed_decay α hα)] with k hbk hsk hδk hδrk htk hnk hdec
  have hn0 : 0 < (T.S.n k : ℝ) := by linarith
  have hbdef : bstar T k = (T.S.n k : ℝ) ^ (-0.96 : ℝ) := by norm_num [bstar]
  have hsq : (T.S.n k : ℝ) * (bstar T k) ^ 2 = (T.S.n k : ℝ) ^ (-0.92 : ℝ) := by
    rw [hbdef]
    exact degree_bsquare _ hn0
  have hδb : Real.exp (-α * T.S.n k / 4) ≤ bstar T k := by
    rw [hbdef, Real.rpow_neg hn0.le (0.96 : ℝ)]
    rw [← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hn0 (0.96 : ℝ))).mpr
    have he : Real.exp (-α * T.S.n k / 4) = Real.exp (-(α / 4) * T.S.n k) := by congr 1; ring
    rw [he, mul_comm]
    exact hδrk
  have heq : 1 / (320000 * (T.S.n k : ℝ) * (bstar T k) ^ 2) =
      (1 / 320000) * (T.S.n k : ℝ) ^ (0.92 : ℝ) := by
    rw [mul_assoc, hsq, Real.rpow_neg hn0.le (0.92 : ℝ)]
    simp [one_div, mul_inv_rev, mul_comm]
  refine ⟨by exact_mod_cast hn0, ?_, ?_, hδb, hδk, ?_, hdec⟩
  · simpa only [hbdef] using hbk
  · simpa only [hsq] using hsk
  · simpa only [heq] using htk


/-- The raw degree alarm probability from clipping, concentration and two finite Markov steps. -/
theorem raw_degree_alarm_probability (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
        (clusterHistoryLaw PT hPT hm).pr (fun W => clusterAlarm1 PT hPT hm W a) ≤
          Real.exp (-(T.S.n k : ℝ) ^ (0.2 : ℝ)) := by
  filter_upwards [cluster_degree_outlier_eventually κ hκ T hDeep,
    bulk_nonempty_eventually κ hκ T, degree_alarm_numeric_eventually T κ.α hκ.α_rng.1]
    with k hout hbulk hnum
  intro PT hPT hm a
  rcases hnum with ⟨hn, hbsmall, hsize, hδb, hδt, htail, hdec⟩
  let P := clusterHistoryLaw PT hPT hm
  let Q := uniform_first_law PT hPT (patchAt PT hPT a.1)
  let δ := Real.exp (-κ.α * T.S.n k / 4)
  let η := 2 * Real.exp (-3 * κ.α * T.S.n k / 4)
  let F := fun W : ClusterHistory PT hPT hm =>
    ∑ x, if clusterJ0 PT hPT hm W a x then 0 else Q.w x
  have hmean := mean_J0_removed_le PT hPT hm a hn (hbulk PT hPT a) hbsmall hsize δ η
    (by dsimp [δ]; positivity) (by dsimp [η]; positivity) hδb hδt htail
    (fun W b hb => hout PT hPT hm W (patchAt PT hPT a.1) b)
  have heq : (T.S.n k : ℝ) * η / δ =
      2 * (T.S.n k : ℝ) * Real.exp (-κ.α * T.S.n k / 2) := by
    have he : Real.exp (-3 * κ.α * T.S.n k / 4) / Real.exp (-κ.α * T.S.n k / 4) =
        Real.exp (-κ.α * T.S.n k / 2) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    dsimp [δ, η]
    calc
      (T.S.n k : ℝ) * (2 * Real.exp (-3 * κ.α * T.S.n k / 4)) /
          Real.exp (-κ.α * T.S.n k / 4) =
          (2 * (T.S.n k : ℝ)) * (Real.exp (-3 * κ.α * T.S.n k / 4) /
            Real.exp (-κ.α * T.S.n k / 4)) := by ring
      _ = _ := by rw [he]
  have hmean' : P.E F ≤ Real.exp (-2 * (T.S.n k : ℝ) ^ (0.2 : ℝ)) := by
    have hm' : P.E F ≤ (T.S.n k : ℝ) * η / δ + δ +
        2 * Real.exp (-(T.S.n k : ℝ) ^ (0.5 : ℝ)) := hmean
    rw [heq] at hm'
    exact hm'.trans hdec
  have hF : ∀ W, 0 ≤ F W := by
    intro W
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact le_rfl
    · exact Q.nonneg x
  have hmark := HypercubeRamsey.Lane_q_s15_c1.finLaw_pr_gt_le_E_div P F hF
    (Real.exp (-(T.S.n k : ℝ) ^ (0.2 : ℝ))) (by positivity)
  have hmark' : P.pr (fun W => clusterAlarm1 PT hPT hm W a) ≤
      P.E F / Real.exp (-(T.S.n k : ℝ) ^ (0.2 : ℝ)) := by
    simpa [clusterAlarm1, F, Q, uniform_first_law] using hmark
  apply hmark'.trans
  calc
    P.E F / Real.exp (-(T.S.n k : ℝ) ^ (0.2 : ℝ)) ≤
      Real.exp (-2 * (T.S.n k : ℝ) ^ (0.2 : ℝ)) /
        Real.exp (-(T.S.n k : ℝ) ^ (0.2 : ℝ)) :=
      div_le_div_of_nonneg_right hmean' (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring


/-- Positive global raw weight gives positive weight to every slice's primitive record vector. -/
theorem raw_slice_weight_pos (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (s : ClusterSlice PT) :
    0 < ((clusterSolver PT hPT hm s.1).recLaw PT.parameter).w (historyOnSlice W s) := by
  have hprod : (∏ r : ClusterRecordIndex PT hPT hm,
      (clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2 (W r)) ≠ 0 := hW.ne'
  have hcoord (r : ClusterRecordIndex PT hPT hm) :
      0 < (clusterSolver PT hPT hm r.1.1).lawRec PT.parameter r.2 (W r) := by
    have hn := (Finset.prod_ne_zero_iff.mp hprod) r (Finset.mem_univ _)
    exact lt_of_le_of_ne ((clusterSolver PT hPT hm r.1.1).lawRec_nonneg _ _ _) hn.symm
  change 0 < ∏ r, (clusterSolver PT hPT hm s.1).lawRec PT.parameter r
    (historyOnSlice W s r)
  exact Finset.prod_pos fun r _ => hcoord ⟨s, r⟩

/-- A nonzero center row at positive raw history weight lies in an active clean corner. -/
theorem center_sigma_clean_corner (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (a : EvenPosition T k) (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0) :
    ∃ v ∈ PT.activeVertices,
      CleanProps PT.tiling (patchAt PT hPT a.1) PT.π (PT.mesh.corner v (patchAt PT hPT a.1)) ∧
      ∀ x, HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y x ≠ 0 →
        x ∈ PT.mesh.corner v (patchAt PT hPT a.1) := by
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  have hσ' : S.σ v (historyOnSlice W s) (nbrLabels v.1 Y.2) ≠ 0 := hσ
  obtain ⟨v', hv', hsup⟩ := S.σ_support v (historyOnSlice W s) (nbrLabels v.1 Y.2) hσ'
  have hactive : v' ∈ PT.activeVertices := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hv' PT.parameter (raw_slice_weight_pos PT hPT hm W hW s)⟩
  refine ⟨v', hactive, hPT.corner_clean (patchAt PT hPT a.1) v' hactive, ?_⟩
  intro x hx
  exact (hsup x hx).1

/-- The nonzero center row as a normalized finite law, for Section 12's interaction estimates. -/
noncomputable def center_sigma_law (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0) :
    Law (T.S.N k) where
  w := HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y
  nonneg x := (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_nonneg
    (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
    (nbrLabels (clusterCenterRole PT hPT hm a).1 Y.2) x
  sum_eq_one := (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_prob
    (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
    (nbrLabels (clusterCenterRole PT hPT hm a).1 Y.2) hσ

/-- Bulk flips are outside the internal block, so h plus their count is at most n. -/
theorem bulk_internal_card_bound (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) :
    (clusterBulkNeighbours PT hPT a).card + (PT.tiling.P (patchAt PT hPT a.1)).h ≤ T.S.n k := by
  let i := patchAt PT hPT a.1
  let J := fun b : BulkIndex PT hPT a => Classical.choose (adjacent_eq_flip a b.1 (Finset.mem_filter.mp b.2).2.1)
  have hflip (b : BulkIndex PT hPT a) : b.1.1 = flipPos a.1 (J b) :=
    Classical.choose_spec (adjacent_eq_flip a b.1 (Finset.mem_filter.mp b.2).2.1)
  have hj (b : BulkIndex PT hPT a) : (J b).val < T.S.n k - (PT.tiling.P i).h := by
    by_contra h
    have he : outsideWord PT hPT i b.1.1 = outsideWord PT hPT i a.1 := by
      rw [hflip]
      exact outsideWord_flip_internal PT hPT i a.1 (J b) (le_of_not_gt h)
    exact (Finset.mem_filter.mp b.2).2.2.2
      (slice_eq_of_outside_word_eq PT hPT i b.1.1 a.1 (Finset.mem_filter.mp b.2).2.2.1 rfl he)
  let f : BulkIndex PT hPT a → Fin (T.S.n k - (PT.tiling.P i).h) := fun b => ⟨(J b).val, hj b⟩
  have hf : Function.Injective f := by
    intro b b' h
    have hval := congrArg Fin.val h
    have hJ : J b = J b' := Fin.ext hval
    apply Subtype.ext
    apply Subtype.ext
    rw [hflip, hflip, hJ]
  have hc := Fintype.card_le_of_injective f hf
  have hcount : (clusterBulkNeighbours PT hPT a).card ≤ T.S.n k - (PT.tiling.P i).h := by
    simpa [BulkIndex, Fintype.card_coe, Fintype.card_fin] using hc
  have hh := clusterHeight_le PT hPT i
  change (clusterBulkNeighbours PT hPT a).card + (PT.tiling.P i).h ≤ T.S.n k
  omega

/-- The high-cluster q scale diverges uniformly over valid tilings. -/
theorem high_q_eventually_ge (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (C : ℝ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i, C ≤ (PT.tiling.P i).q := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hl : Tendsto (fun k => Real.log (T.S.n k : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hs : ∀ᶠ k in atTop, C ≤ (Real.log (T.S.n k : ℝ)) ^ κ.cq :=
    ((tendsto_rpow_atTop hκ.cq_rng.1).comp hl).eventually_ge_atTop _
  have hlarge : ∀ᶠ k in atTop, C ≤ Real.log (T.S.n k : ℝ) ^ (2 : ℕ) := by
    have ht : Tendsto (fun k => Real.log (T.S.n k : ℝ) ^ (2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp hl
    simpa only [Real.rpow_two] using ht.eventually_ge_atTop C
  filter_upwards [hs, hlarge] with k hsk hlk
  intro PT hPT hm i
  have hc : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge := by tauto
  rcases hPT.tiling_valid.cluster_data hc i with ⟨_, _, _, _, _, _, _, _, _, _, hsmallReg, hlargeReg⟩
  rcases hm with hsmall | hlarge
  · exact hsk.trans (hsmallReg.mp hsmall).1.le
  · exact hlk.trans (hlargeReg.mp hlarge).le

/-- The nonzero center first law has the small-width budget needed by Section 12. -/
theorem center_sigma_width_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, ∀ a : EvenPosition T k,
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      ∀ hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0,
      (center_sigma_law PT hPT hm W a Y hσ).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [hn.eventually_ge_atTop 1] with k hn1
  intro PT hPT hm W a Y hσ x
  let i := patchAt PT hPT a.1
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hg : 0 ≤ PT.tiling.gain i := by
    rcases hm with hs | hs <;> simp only [Tiling.gain, hs] <;> positivity
  have hcap := (clusterSolver PT hPT hm i).σ_cap (clusterCenterRole PT hPT hm a)
    (historyOnSlice W (clusterSliceAt PT hPT a.1)) (nbrLabels (clusterCenterRole PT hPT hm a).1 Y.2) x
  have hσcap : (T.S.N k : ℝ) * (center_sigma_law PT hPT hm W a Y hσ).w x ≤ (2 : ℝ) ^ (PT.tiling.P i).h := by
    apply hcap.trans
    have he : Real.exp (-500 * PT.tiling.gain i) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 2 ^ (PT.tiling.P i).h by positivity)]
  have hheight : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    have hh := (hPT.tiling_valid.allocation_bounds i).1
    have hm : ((PT.tiling.P i).h : ℝ) ≤ max ((PT.tiling.P i).h : ℝ) ((PT.tiling.P i).ℓ : ℝ) := le_max_left _ _
    exact hm.trans hh.le
  have hι : κ.ι ≤ κ.xs / 4 := by
    have hm := min_le_left κ.xs (min κ.η0 0.01)
    linarith [hκ.ι_rng.2, hκ.xs_rng.1]
  have hnι : (T.S.n k : ℝ) ^ κ.ι ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hι
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : (2 : ℝ) ^ (PT.tiling.P i).h ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
    have he : (2 : ℝ) ^ (PT.tiling.P i).h = Real.exp (((PT.tiling.P i).h : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [he]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (PT.tiling.P i).h)
    nlinarith [hheight.trans hnι]
  apply (le_div_iff₀ hN).mpr
  nlinarith [hσcap.trans hpow]

/-- A degree near one half has a controlled inverse power. -/
theorem inverse_degree_power_bound {d e : ℝ} (m : ℕ)
    (he : 0 ≤ e) (hes : e ≤ 1 / 4) (hd : |d - 1 / 2| ≤ e) :
    d ^ (-(m : ℝ)) ≤ (2 : ℝ) ^ m * Real.exp (4 * (m : ℝ) * e) := by
  have hdlo : 1 / 2 - e ≤ d := by have h := (abs_le.mp hd).1; linarith
  have hdpos : 0 < d := by linarith
  have ht : 0 < 2 * d := by positivity
  have hinv : (2 * d)⁻¹ ≤ 1 + 4 * e := by
    rw [← one_div]
    apply (div_le_iff₀ ht).mpr
    nlinarith [mul_nonneg he (by linarith : 0 ≤ 1 - 4 * e),
      mul_nonneg (by linarith : 0 ≤ d - (1 / 2 - e)) (by linarith : 0 ≤ 1 + 4 * e)]
  have hlog : -4 * e ≤ Real.log (2 * d) := by
    linarith [Real.one_sub_inv_le_log_of_pos ht]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hdpos.ne'] at hlog
  rw [Real.rpow_def_of_pos hdpos]
  have hp : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)
  nlinarith

/-- The fixed Section 13 slacks control nominal errors and clique factors in high modes. -/
theorem cluster_clean_scales_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      0 < PT.tiling.gain i ∧
      Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ PT.tiling.gain i / 2 ∧
      10 * ((PT.tiling.P i).q : ℝ) ^ κ.Cb / (T.S.n k : ℝ) ≤ bstar T k ∧
      (T.S.n k : ℝ) * (10 * ((PT.tiling.P i).q : ℝ) ^ κ.Cb / (T.S.n k : ℝ)) ≤
        PT.tiling.gain i / (400 * κ.u) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hι : κ.ι < (0.04 : ℝ) := by
    have h := hκ.ι_rng.2
    have hm := min_le_right κ.xs (min κ.η0 0.01)
    have hm' := min_le_right κ.η0 (0.01 : ℝ)
    linarith
  have hscale := hn.eventually (real_eventually_rpow_le_mul (p := κ.ι) (q := 0.04)
    (c := 1 / 10) hι (by norm_num))
  filter_upwards [high_q_eventually_ge κ hκ T (max 1 κ.Q0), hn.eventually_ge_atTop 1, hscale]
    with k hq hn1 hnum
  intro PT hPT hm i
  let P := PT.tiling.P i
  have hq1 : (1 : ℝ) ≤ (P.q : ℝ) := (le_max_left _ _).trans (hq PT hPT hm i)
  have hq0 : κ.Q0 ≤ P.q := (le_max_right _ _).trans (hq PT hPT hm i)
  have hc : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge := by tauto
  have hn0 : 0 < (T.S.n k : ℝ) := by linarith
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hu : (0 : ℝ) < κ.u := by
    have h := hκ.u_rng.2
    have hu : 0 < κ.u := by omega
    exact_mod_cast hu
  have hgain : PT.tiling.gain i = κ.a * P.h / 10 ^ 6 := by
    rcases hm with hs | hs <;> simp [Tiling.gain, hs, P]
  have hheight : 0 < (P.h : ℝ) := by exact_mod_cast clusterHeight_pos PT hPT hm i
  have hg : 0 < PT.tiling.gain i := by rw [hgain]; positivity
  have hM : (κ.Mlo : ℝ) ≤ κ.Mhi := by
    have hp : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
    linarith [hκ.Mhi_big.1]
  have hCb : κ.Cb ≤ (κ.Mhi : ℝ) := by linarith [hκ.Mlo_big]
  have hh : (P.q : ℝ) ^ (κ.Mhi : ℝ) ≤ P.h := by
    have h := (hPT.tiling_valid.cluster_data hc i).2.2.2.2.2.2.2.1
    have hlow : PT.tiling.mode ≠ .lowCluster := by rcases hm with hs | hs <;> simp [hs]
    simpa [hlow, P] using h
  have hlo : (P.q : ℝ) ^ (κ.Mlo : ℝ) ≤ P.h :=
    (Real.rpow_le_rpow_of_exponent_le hq1 hM).trans hh
  have hCbheight : (P.q : ℝ) ^ κ.Cb ≤ P.h :=
    (Real.rpow_le_rpow_of_exponent_le hq1 hCb).trans hh
  have halloc : (P.h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    have hm : (P.h : ℝ) ≤ (max P.h P.ℓ : ℕ) := by exact_mod_cast Nat.le_max_left P.h P.ℓ
    apply hm.trans
    simpa [P, Nat.cast_max] using (hPT.tiling_valid.allocation_bounds i).1.le
  have hcond := hκ.Q0_large P.q hq0
  have hcq : 4 * Cstar κ.u κ.ξ * (P.q : ℝ) ^ 2 ≤ (κ.a / 10 ^ 6) * (P.q : ℝ) ^ (κ.Mlo : ℝ) :=
    hcond.2.2.2.2.2.2.1
  have hce : 40 * (P.q : ℝ) ^ κ.Cb ≤ (κ.a / 10 ^ 6) * (P.q : ℝ) ^ (κ.Mlo : ℝ) / (100 * κ.u) :=
    hcond.2.2.2.2.2.2.2.1
  have hCQ : (PT.tiling.Q i : ℝ) ≤ 2 * (P.q : ℝ) ^ 2 := by
    exact (hPT.tiling_valid.clique_scales i).1 hc |>.2.2.1
  have hCnonneg : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
  have hclique : Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ PT.tiling.gain i / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hlo (show 0 ≤ κ.a / 10 ^ 6 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hCQ hCnonneg
    rw [hgain]
    nlinarith
  have herr : 10 * (P.q : ℝ) ^ κ.Cb / (T.S.n k : ℝ) ≤ bstar T k := by
    apply (div_le_iff₀ hn0).mpr
    have hbstar : bstar T k * (T.S.n k : ℝ) = (T.S.n k : ℝ) ^ (0.04 : ℝ) := by
      calc
        bstar T k * (T.S.n k : ℝ) = (T.S.n k : ℝ) ^ (-0.96 : ℝ) * (T.S.n k : ℝ) ^ (1 : ℝ) := by norm_num [bstar]
        _ = _ := by rw [← Real.rpow_add hn0]; norm_num
    rw [hbstar]
    nlinarith [hCbheight.trans halloc]
  have hne : (T.S.n k : ℝ) * (10 * (P.q : ℝ) ^ κ.Cb / (T.S.n k : ℝ)) ≤
      PT.tiling.gain i / (400 * κ.u) := by
    have h1 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlo (show 0 ≤ κ.a / 10 ^ 6 by positivity)) (by positivity : 0 ≤ 100 * (κ.u : ℝ))
    have h2 : (κ.a / 10 ^ 6) * (P.h : ℝ) / (100 * κ.u) = 4 * (PT.tiling.gain i / (400 * κ.u)) := by
      rw [hgain]; ring
    rw [h2] at h1
    have heq : (T.S.n k : ℝ) * (10 * (P.q : ℝ) ^ κ.Cb / (T.S.n k : ℝ)) = 10 * (P.q : ℝ) ^ κ.Cb := by field_simp <;> ring
    rw [heq]
    linarith
  exact ⟨hg, hclique, herr, hne⟩

/-- The nominal high-cluster laws obey the same width budget as conditional marginals. -/
theorem nominal_cluster_width_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      (PT.π i).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
  filter_upwards [cluster_width_eventually κ hκ T] with k hk
  intro PT hPT hm i
  apply (hk PT hPT hm i).2
  intro y
  apply (hPT.law_cap i y).trans
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    have h := Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
    rw [(PT.tiling.P i).cardX] at h
    exact_mod_cast h
  have hh : (0 : ℝ) < (PT.tiling.P i).h := by exact_mod_cast clusterHeight_pos PT hPT hm i
  have hk0 : 1 ≤ PT.tiling.kScale i := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos hh _
  have ht0 : 1 ≤ PT.tiling.tScale i := by
    apply Nat.ceil_pos.mpr
    exact Real.rpow_pos_of_pos hh _
  have hk1 : (1 : ℝ) ≤ PT.tiling.kScale i := by exact_mod_cast hk0
  have ht1 : (1 : ℝ) ≤ PT.tiling.tScale i := by exact_mod_cast ht0
  have he : 3 ≤ Real.exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) := by
    have hh := Real.add_one_le_exp (2 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i)
    nlinarith [mul_le_mul hk1 ht1 (by norm_num) (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (by linarith) hM.le

/-- A positively weighted center row is supported on the stage's first side. -/
theorem center_sigma_stage_support (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (hW : 0 < (clusterHistoryLaw PT hPT hm).w W)
    (a : EvenPosition T k) (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0) :
    (center_sigma_law PT hPT hm W a Y hσ).SupportedIn (T.X k) := by
  obtain ⟨v, hv, hC, hs⟩ := center_sigma_clean_corner PT hPT hm W hW a Y hσ
  intro x hx
  by_contra hn
  have hX := (hPT.tiling_valid.patch_supports (patchAt PT hPT a.1)).1 (hC.sub (hs x hn))
  exact hx (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports (patchAt PT hPT a.1)).2.1 hX)).1

/-- The conditional odd law, normalized for Section 12. -/
noncomputable def conditional_odd_law (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) : Law (T.S.N k) :=
  solver_marginal_law (clusterSolver PT hPT hm (patchAt PT hPT b.1))
    ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).groupOf (solverWordAt PT hPT hm b.1)) (historyOnSlice W (clusterSliceAt PT hPT b.1))

/-- Conditional cluster interactions use the gated Section 15 interaction convention exactly. -/
theorem conditional_interaction_eq (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k)
    (J : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
    clusterInteraction PT hPT hm W b J xs =
      Needs.inter (T.S.E k) PT.tiling.c (conditional_odd_law PT hPT hm W b).w J xs := rfl

/-- Conditional odd laws are supported on the stage second side. -/
theorem conditional_odd_stage_support (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k) :
    (conditional_odd_law PT hPT hm W b).SupportedIn (T.Y k) := by
  intro y hy
  apply solver_marginal_law_supported
  intro hb
  exact hy ((Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports (patchAt PT hPT b.1)).2.2.2
    ((hPT.tiling_valid.patch_supports (patchAt PT hPT b.1)).2.2.1 hb))).1)

/-- Conditional odd laws have the Section 12 width budget, uniformly in all histories. -/
theorem conditional_odd_width_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, ∀ b : OddPosition T k,
      (conditional_odd_law PT hPT hm W b).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
  filter_upwards [cluster_width_eventually κ hκ T] with k hk
  intro PT hPT hm W b
  let i := patchAt PT hPT b.1
  apply (hk PT hPT hm i).2
  intro y
  exact (clusterSolver PT hPT hm i).marginal_cap ((clusterSolver PT hPT hm (patchAt PT hPT b.1)).groupOf (solverWordAt PT hPT hm b.1))
    (historyOnSlice W (clusterSliceAt PT hPT b.1)) y

/-- Exactly factor finitely many functions reading disjoint primitive record scopes. -/
theorem finite_product_expectation_disjoint
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (s : Finset J) (f : J → (∀ i, Ω i) → ℝ) (A : J → Finset ι)
    (hdep : ∀ j, FinProb.DependsOn (f j) (A j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    (FinLaw.pi P).E (fun x => ∏ j ∈ s, f j x) =
      ∏ j ∈ s, (FinLaw.pi P).E (f j) := by
  induction s using Finset.induction_on with
  | empty => simpa [FinLaw.E] using (FinLaw.pi P).sum_one
  | @insert a s ha ih =>
      have hprodDep : FinProb.DependsOn
          (fun x => ∏ j ∈ s, f j x) (s.biUnion A) := by
        intro x y hxy
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j
        intro i hi
        exact hxy i (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)
      have hdisjUnion : Disjoint (A a) (s.biUnion A) := by
        apply Finset.disjoint_left.mpr
        intro i hi hmem
        rcases Finset.mem_biUnion.mp hmem with ⟨j, hj, hji⟩
        exact (Finset.disjoint_left.mp (hdisj a j (by
          intro h
          subst j
          exact ha hj))) hi hji
      calc
        (FinLaw.pi P).E (fun x => ∏ j ∈ insert a s, f j x) =
            (FinLaw.pi P).E (fun x => f a x * ∏ j ∈ s, f j x) := by
          congr 1; funext x; rw [Finset.prod_insert ha]
        _ = (FinLaw.pi P).E (f a) * (FinLaw.pi P).E (fun x => ∏ j ∈ s, f j x) :=
          HypercubeRamsey.Lane_q_s15_c1.pi_E_mul_of_disjoint P (f a)
            (fun x => ∏ j ∈ s, f j x) (A a) (s.biUnion A) (hdep a) hprodDep hdisjUnion
        _ = _ := by rw [ih, Finset.prod_insert ha]

/-- A uniform bound after freezing all but one coordinate bounds the iid tuple mass. -/
theorem iid_one_free_mass {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (τ : FinLaw X) (j : ι) (x0 : X) (F : (ι → X) → Prop) [DecidablePred F] (M : ℝ)
    (hM : ∀ xs, (∑ z, if F (Function.update xs j z) then τ.w z else 0) ≤ M) :
    (∑ xs : ι → X, if F xs then ∏ i, τ.w (xs i) else 0) ≤ M := by
  let e := Equiv.funSplitAt j X
  have hupdate (xs : {i : ι // i ≠ j} → X) (z : X) :
      Function.update (e.symm (x0, xs)) j z = e.symm (z, xs) := by
    funext i
    by_cases hi : i = j
    · subst i; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hi]
  have hweight (z : X) (xs : {i : ι // i ≠ j} → X) :
      (∏ i, τ.w (e.symm (z, xs) i)) = τ.w z * ∏ i, τ.w (xs i) := by
    have hj : e.symm (z, xs) j = z := by simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    have ho (i : {i : ι // i ≠ j}) : e.symm (z, xs) i.1 = xs i := by
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, i.property]
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j, hj]
    congr 1
    exact Finset.prod_congr rfl (fun i _ => congrArg τ.w (ho i))
  have heq : (∑ xs : ι → X, if F xs then ∏ i, τ.w (xs i) else 0) =
      ∑ xs : {i : ι // i ≠ j} → X,
        (∏ i, τ.w (xs i)) * (∑ z, if F (e.symm (z, xs)) then τ.w z else 0) := by
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xs _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [hweight]
    split_ifs <;> ring
  rw [heq]
  calc
    (∑ xs : {i : ι // i ≠ j} → X,
        (∏ i, τ.w (xs i)) * (∑ z, if F (e.symm (z, xs)) then τ.w z else 0)) ≤
        ∑ xs : {i : ι // i ≠ j} → X, (∏ i, τ.w (xs i)) * M := by
      apply Finset.sum_le_sum
      intro xs _
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => τ.nonneg (xs i))
      simpa only [hupdate] using hM (e.symm (x0, xs))
    _ = M := by
      rw [← Finset.sum_mul]
      have hs : (∑ xs : {i : ι // i ≠ j} → X, ∏ i, τ.w (xs i)) = 1 :=
        (FinLaw.pi (fun _ : {i : ι // i ≠ j} => τ)).sum_one
      rw [hs, one_mul]

/-- Peeling with a pointwise budget, rather than an explicitly constructed supremum. -/
theorem homogeneous_bad_mass_of_budget (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ c : Colour, ∀ d : ℕ, d ≤ T.S.n k →
      ∀ τ π : Law (T.S.N k), ∀ Sp : Finset (Fin (T.S.N k)), ∀ Q Γ : ℝ,
      Sp.Nonempty → Sp ⊆ T.X k → τ.SupportedIn Sp → π.SupportedIn (T.Y k) →
      τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) →
      π.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) →
      (∀ x ∈ Sp, S12.DegGate (T.S.E k) c π.w 2 (bstar T k) x) →
      (∀ x ∈ Sp, 0 < deg (T.S.E k) c π.w x) →
      (Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ Q ∧ 1 ≤ Q) →
      NoClique (T.S.E k) c Sp π.w κ.θ Q → 0 ≤ Γ → Γ < 1 →
      (∀ x ∈ Sp, τ.w x * (deg (T.S.E k) c π.w x) ^ (-(d : ℝ)) *
        Real.exp (Cstar κ.u κ.ξ * Q) ≤ Γ) →
      (∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ S12.Moderate (T.S.E k) c (fun _ : Fin d => π.w) κ.ξ xs then
          S12.prodW τ.w xs * S12.posTerm (T.S.E k) c (fun _ : Fin d => π.w) I xs else 0) ≤
            4 ^ (κ.u + 1) * Γ := by
  have hp (c : Colour) := (S12.homogeneous_peeling_export κ hκ T hDeep c 2 (by norm_num)).peeling
  filter_upwards [hp false, hp true] with k hkf hkt
  intro c d hd τ π Sp Q Γ hSp hsub hτ hπ hτw hπw hgate hpos hQ hno hΓ0 hΓ1 hbudget
  have hk : ∀ H : S12.HomogeneousInput κ hκ T k c 2,
      (∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ S12.Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs then
          S12.prodW H.S.τ.w xs * S12.posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0) ≤
          4 ^ (κ.u + 1) * H.gamma := by
    cases c
    · exact hkf
    · exact hkt
  let S : S12.InterSetting T k (κ.xs / 4) := {
    d := d, d_le := hd, τ := τ, π := fun _ => π,
    τ_supp := fun x hx => hτ x (fun hxSp => hx (hsub hxSp)),
    π_supp := fun _ => hπ, τ_width := hτw, π_width := fun _ => hπw }
  let f := fun x => τ.w x * (deg (T.S.E k) c π.w x) ^ (-(d : ℝ))
  let γ := Real.exp (Cstar κ.u κ.ξ * Q) * Sp.sup' hSp f
  have hγle : γ ≤ Γ := by
    have hsup : Sp.sup' hSp f ≤ Γ / Real.exp (Cstar κ.u κ.ξ * Q) := by
      apply Finset.sup'_le
      intro x hx
      exact (le_div_iff₀ (Real.exp_pos _)).mpr (hbudget x hx)
    dsimp [γ]
    calc
      _ ≤ Real.exp (Cstar κ.u κ.ξ * Q) * (Γ / Real.exp (Cstar κ.u κ.ξ * Q)) :=
        mul_le_mul_of_nonneg_left hsup (Real.exp_nonneg _)
      _ = Γ := by field_simp
  have hγ0 : 0 ≤ γ := by
    obtain ⟨x, hx⟩ := hSp
    have hf : 0 ≤ f x := mul_nonneg (τ.nonneg x) (Real.rpow_nonneg (hpos x hx).le _)
    dsimp [γ]
    exact mul_nonneg (Real.exp_nonneg _) (hf.trans (Finset.le_sup' f hx))
  let H : S12.HomogeneousInput κ hκ T k c 2 := {
    S := S, π := π, homogeneous := fun _ => rfl,
    Sp := Sp, Sp_nonempty := hSp, Sp_subset := hsub,
    τ_supported := hτ, π_supported := hπ, degree_gate := hgate,
    degree_positive := hpos, Q := Q, Q_large := hQ, noClique := hno,
    gamma := γ, gamma_eq := rfl, gamma_nonneg := hγ0,
    gamma_lt_one := hγle.trans_lt hΓ1 }
  have hb := hk H
  exact hb.trans (mul_le_mul_of_nonneg_left hγle (by positivity))

/-- High-cluster gains tend to infinity uniformly over the valid patch data. -/
theorem high_gain_eventually_ge (κ : CConsts) (hκ : κ.Admissible) (T : Stage) (C : ℝ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      C ≤ PT.tiling.gain i := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  filter_upwards [high_q_eventually_ge κ hκ T (max 1 (C * 10 ^ 6 / κ.a))] with k hk
  intro PT hPT hm i
  let P := PT.tiling.P i
  have hq1 : (1 : ℝ) ≤ (P.q : ℝ) := (le_max_left _ _).trans (hk PT hPT hm i)
  have hqc : C * 10 ^ 6 / κ.a ≤ P.q := (le_max_right _ _).trans (hk PT hPT hm i)
  have hM : (1 : ℝ) ≤ κ.Mhi := by
    have hMp : 0 < κ.Mhi := by
      have h := hκ.Mhi_big.2
      by_contra hn
      have he : κ.Mhi = 0 := Nat.eq_zero_of_not_pos hn
      simp [he] at h
      linarith
    exact_mod_cast hMp
  have hc : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge := by tauto
  have hh : (P.q : ℝ) ^ (κ.Mhi : ℝ) ≤ P.h := by
    have h := (hPT.tiling_valid.cluster_data hc i).2.2.2.2.2.2.2.1
    have hlow : PT.tiling.mode ≠ .lowCluster := by rcases hm with hs | hs <;> simp [hs]
    simpa [hlow, P] using h
  have hqhh : (P.q : ℝ) ≤ (P.h : ℝ) := by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hq1 hM).trans hh
  have hbound := mul_le_mul_of_nonneg_left (hqc.trans hqhh) ha.le
  have hgain : PT.tiling.gain i = κ.a * P.h / 10 ^ 6 := by
    rcases hm with hs | hs <;> simp [Tiling.gain, hs, P]
  rw [hgain]
  have heq : κ.a * (C * 10 ^ 6 / κ.a) = C * 10 ^ 6 := by field_simp <;> ring
  rw [heq] at hbound
  linarith

/-- High-cluster clique scales eventually meet the fixed logarithmic peeling threshold. -/
theorem high_Q_eventually_large (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ (PT.tiling.Q i : ℝ) ∧
        1 ≤ (PT.tiling.Q i : ℝ) := by
  let C := Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ)
  filter_upwards [high_q_eventually_ge κ hκ T (max 1 C)] with k hk
  intro PT hPT hm i
  have hq1 : (1 : ℝ) ≤ ((PT.tiling.P i).q : ℝ) := (le_max_left _ _).trans (hk PT hPT hm i)
  have hqC : C ≤ (PT.tiling.P i).q := (le_max_right _ _).trans (hk PT hPT hm i)
  have hc : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge := by tauto
  have hQ : ((PT.tiling.P i).q : ℝ) ^ 2 ≤ (PT.tiling.Q i : ℝ) := by
    exact_mod_cast ((hPT.tiling_valid.clique_scales i).1 hc).2.1
  change C ≤ (PT.tiling.Q i : ℝ) ∧ 1 ≤ (PT.tiling.Q i : ℝ)
  constructor <;> nlinarith

/-- The sigma atom cap absorbs the inverse-degree and clique costs. -/
theorem sigma_inverse_budget {N n h d : ℕ} {τ D e g A : ℝ}
    (hN : (0 : ℝ) < N) (hhost : (2 : ℝ) ^ n ≤ (N : ℝ)) (hhd : h + d ≤ n)
    (hτ : 0 ≤ τ) (hcap : (N : ℝ) * τ ≤ (2 : ℝ) ^ h * Real.exp (-500 * g))
    (he : 0 ≤ e) (hes : e ≤ 1 / 4) (hD : |D - 1 / 2| ≤ e)
    (hg : 0 ≤ g) (hA : A ≤ g / 2) (hne : (n : ℝ) * e ≤ g) :
    τ * D ^ (-(d : ℝ)) * Real.exp A ≤ Real.exp (-450 * g) := by
  have hpow : (2 : ℝ) ^ h * (2 : ℝ) ^ d ≤ (N : ℝ) := by
    rw [← pow_add]
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hhd).trans hhost
  have hτpow : τ * (2 : ℝ) ^ d ≤ Real.exp (-500 * g) := by
    have hb := mul_le_mul_of_nonneg_right hcap (show (0 : ℝ) ≤ 2 ^ d by positivity)
    have hupper := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-500 * g))
    have hm : (N : ℝ) * (τ * (2 : ℝ) ^ d) ≤ (N : ℝ) * Real.exp (-500 * g) := by
      nlinarith only [hb, hupper]
    exact le_of_mul_le_mul_left hm hN
  have hdle : (d : ℝ) ≤ n := by exact_mod_cast (show d ≤ n by omega)
  have hde : (d : ℝ) * e ≤ g := (mul_le_mul_of_nonneg_right hdle he).trans hne
  have hdinv := inverse_degree_power_bound d he hes hD
  calc
    τ * D ^ (-(d : ℝ)) * Real.exp A ≤
        τ * ((2 : ℝ) ^ d * Real.exp (4 * (d : ℝ) * e)) * Real.exp A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdinv hτ) (Real.exp_nonneg A)
    _ = (τ * (2 : ℝ) ^ d) * Real.exp (4 * (d : ℝ) * e + A) := by rw [Real.exp_add]; ring
    _ ≤ Real.exp (-500 * g) * Real.exp (4 * (d : ℝ) * e + A) :=
      mul_le_mul_of_nonneg_right hτpow (Real.exp_nonneg _)
    _ = Real.exp (-500 * g + (4 * (d : ℝ) * e + A)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-450 * g) := Real.exp_le_exp.mpr (by linarith)

/-- The pointwise budget required for homogeneous peeling of a center row. -/
theorem center_sigma_peeling_budget_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k,
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      ∀ hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0,
      ∀ v ∈ PT.activeVertices, ∀ x ∈ PT.mesh.corner v (patchAt PT hPT a.1),
      (center_sigma_law PT hPT hm W a Y hσ).w x *
        (deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w x) ^
          (-((clusterBulkNeighbours PT hPT a).card : ℝ)) *
        Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q (patchAt PT hPT a.1) : ℝ)) ≤
        Real.exp (-450 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hb : ∀ᶠ k in atTop, bstar T k ≤ 1 / 4 := by
    have ht : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
      simpa [bstar, show (-1 + (0.04 : ℝ)) = (-0.96 : ℝ) by norm_num, Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn
    exact (ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono fun _ h => h.le
  filter_upwards [cluster_clean_scales_eventually κ hκ T, T.S.eventually_large 1 1, hb]
    with k hk hhost hb
  intro PT hPT hm W hW a Y hσ v hv x hx
  let i := patchAt PT hPT a.1
  let e := 10 * ((PT.tiling.P i).q : ℝ) ^ κ.Cb / (T.S.n k : ℝ)
  obtain ⟨hg, hA, he, hne⟩ := hk PT hPT hm i
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hn0 : 0 < (T.S.n k : ℝ) := by exact_mod_cast hhost.1
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hdeg : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ e := by
    have h := (hPT.corner_clean i v hv).degOwn x hx
    rcases hm with hs | hs <;> simpa [OwnDegOK, hs, e] using h
  have hu : (1 : ℝ) ≤ κ.u := by
    have h := hκ.u_rng.2
    have hu : 1 ≤ κ.u := by omega
    exact_mod_cast hu
  have hne' : (T.S.n k : ℝ) * e ≤ PT.tiling.gain i := by
    apply hne.trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 400 * κ.u)).mpr
    nlinarith [mul_nonneg hg.le (by linarith : 0 ≤ 400 * (κ.u : ℝ) - 1)]
  apply sigma_inverse_budget hN (by simpa only [one_mul] using hhost.2.1)
    (by simpa [Nat.add_comm] using bulk_internal_card_bound PT hPT a)
    ((center_sigma_law PT hPT hm W a Y hσ).nonneg x)
    ((clusterSolver PT hPT hm i).σ_cap (clusterCenterRole PT hPT hm a)
      (historyOnSlice W (clusterSliceAt PT hPT a.1)) (nbrLabels (clusterCenterRole PT hPT hm a).1 Y.2) x)
    he0 (he.trans hb) hdeg hg.le hA hne'

/-- The degree scale tends to zero. -/
theorem bstar_tendsto_zero (T : Stage) : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  simpa [bstar, show (-1 + (0.04 : ℝ)) = (-0.96 : ℝ) by norm_num, Function.comp_def] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hn

/-- Homogeneous peeling bounds the nominal-large tuples under every supported center law. -/
theorem center_nominal_bad_mass_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k,
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      ∀ hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0,
      (∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ S12.Moderate (T.S.E k) PT.tiling.c
          (fun _ : Fin (clusterBulkNeighbours PT hPT a).card => (PT.π (patchAt PT hPT a.1)).w) κ.ξ xs then
          S12.prodW (center_sigma_law PT hPT hm W a Y hσ).w xs *
            S12.posTerm (T.S.E k) PT.tiling.c
              (fun _ : Fin (clusterBulkNeighbours PT hPT a).card => (PT.π (patchAt PT hPT a.1)).w) I xs else 0) ≤
        4 ^ (κ.u + 1) * Real.exp (-450 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  have hb := (bstar_tendsto_zero T).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [homogeneous_bad_mass_of_budget κ hκ T hDeep,
    nominal_cluster_width_eventually κ hκ T, center_sigma_width_eventually κ hκ T,
    center_sigma_peeling_budget_eventually κ hκ T, cluster_clean_scales_eventually κ hκ T,
    high_Q_eventually_large κ hκ T, hb] with k hpeel hπw hτw hbudget hscale hQ hb
  intro PT hPT hm W hW a Y hσ
  let i := patchAt PT hPT a.1
  let τ := center_sigma_law PT hPT hm W a Y hσ
  obtain ⟨v, hv, hC, hs⟩ := center_sigma_clean_corner PT hPT hm W hW a Y hσ
  have hτ : τ.SupportedIn (PT.mesh.corner v i) := by
    intro x hx
    by_contra hn
    exact hx (hs x hn)
  have hsub : PT.mesh.corner v i ⊆ T.X k := by
    intro x hx
    exact (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1
      ((hPT.tiling_valid.patch_supports i).1 (hC.sub hx)))).1
  have hπ : (PT.π i).SupportedIn (T.Y k) := by
    intro y hy
    apply hPT.law_supported
    intro h
    exact hy (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.2.2
      ((hPT.tiling_valid.patch_supports i).2.2.1 h))).1
  have hb0 : 0 ≤ bstar T k := by unfold bstar; positivity
  have hgate (x : Fin (T.S.N k)) (hx : x ∈ PT.mesh.corner v i) :
      |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ bstar T k := by
    have h := hC.degOwn x hx
    have he := (hscale PT hPT hm i).2.2.1
    apply le_trans _ he
    rcases hm with hmode | hmode <;> simpa [OwnDegOK, hmode, i] using h
  have hpositive (x : Fin (T.S.N k)) (hx : x ∈ PT.mesh.corner v i) :
      0 < deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
    have h := (abs_le.mp (hgate x hx)).1
    linarith
  apply hpeel PT.tiling.c (clusterBulkNeighbours PT hPT a).card (bulk_card_le PT hPT a)
    τ (PT.π i) (PT.mesh.corner v i) (PT.tiling.Q i) (Real.exp (-450 * PT.tiling.gain i))
    hC.nonempty hsub hτ hπ (hτw PT hPT hm W a Y hσ) (hπw PT hPT hm i)
    (fun x hx => (hgate x hx).trans (by linarith)) hpositive (hQ PT hPT hm i) hC.noClique
    (Real.exp_nonneg _) (Real.exp_lt_one_iff.mpr (by linarith [(hscale PT hPT hm i).1]))
    (fun x hx => hbudget PT hPT hm W hW a Y hσ v hv x hx)

/-- The fixed peeling factor is absorbed by the high gain margin. -/
theorem peeling_factor_absorbed_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      (4 : ℝ) ^ (κ.u + 1) * Real.exp (-450 * PT.tiling.gain i) ≤
        (1 / 2) * Real.exp (-300 * PT.tiling.gain i) := by
  let C : ℝ := 4 ^ (κ.u + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [high_gain_eventually_ge κ hκ T (Real.log (2 * C) / 150)] with k hk
  intro PT hPT hm i
  have hlog : Real.log (2 * C) ≤ 150 * PT.tiling.gain i := by linarith [hk PT hPT hm i]
  have he : 2 * C ≤ Real.exp (150 * PT.tiling.gain i) := by
    rw [← Real.exp_log (by positivity : 0 < 2 * C)]
    exact Real.exp_le_exp.mpr hlog
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-450 * PT.tiling.gain i))
  have heq : Real.exp (150 * PT.tiling.gain i) * Real.exp (-450 * PT.tiling.gain i) =
      Real.exp (-300 * PT.tiling.gain i) := by rw [← Real.exp_add]; congr 1; ring
  rw [heq] at hm
  change C * Real.exp (-450 * PT.tiling.gain i) ≤ _
  linarith

/-- Every conditional column's gated anomaly has an exponentially small iid tuple mass. -/
theorem center_conditional_gated_tuple_mass_eventually (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k,
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      ∀ hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0,
      ∀ b : OddPosition T k, ∀ J : Finset (Fin κ.u), 2 ≤ J.card →
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if (∀ j ∈ J, |clusterDegree PT hPT hm W b (xs j) - 1 / 2| ≤ 2 * bstar T k) ∧
          2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs| then
          ∏ j, (center_sigma_law PT hPT hm W a Y hσ).w (xs j) else 0) ≤
        Real.exp (-(κ.α * T.S.n k / 3)) := by
  have hξ : 0 < κ.ξ := hκ.ξ_rng.1
  have ht (c : Colour) := Needs.inter_tail_one κ hκ T hDeep c κ.u 2 (by norm_num)
  have hsmall : ∀ᶠ k in atTop, 100 * (3 : ℝ) ^ κ.u * 2 * bstar T k < 2 * κ.ξ := by
    have hlim := (bstar_tendsto_zero T).const_mul (100 * (3 : ℝ) ^ κ.u * 2)
    have hlim' : Tendsto (fun k => 100 * (3 : ℝ) ^ κ.u * 2 * bstar T k) atTop (nhds 0) := by simpa using hlim
    exact hlim'.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 2 * κ.ξ))
  filter_upwards [ht false, ht true, center_sigma_width_eventually κ hκ T,
    conditional_odd_width_eventually κ hκ T, T.S.n_tendsto.eventually_ge_atTop 1, hsmall]
    with k htf htt hτw hπw hn hs
  intro PT hPT hm W hW a Y hσ b J hJ
  let τ := center_sigma_law PT hPT hm W a Y hσ
  let π := conditional_odd_law PT hPT hm W b
  let S : Needs.InterSetting T k (κ.xs / 4) := {
    d := 1, d_le := hn, τ := τ, π := fun _ => π,
    τ_supported := center_sigma_stage_support PT hPT hm W hW a Y hσ,
    π_supported := fun _ => conditional_odd_stage_support PT hPT hm W b,
    τ_width := hτw PT hPT hm W a Y hσ, π_width := fun _ => hπw PT hPT hm W b }
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i0, hi0⟩ := hJne
  let F : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    (∀ j ∈ J, |clusterDegree PT hPT hm W b (xs j) - 1 / 2| ≤ 2 * bstar T k) ∧
      2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|
  suffices hfinal : (∑ xs : Fin κ.u → Fin (T.S.N k), if F xs then ∏ j, τ.w (xs j) else 0) ≤
      Real.exp (-(κ.α * T.S.n k / 3)) by simpa only [F, τ] using hfinal
  apply iid_one_free_mass ⟨τ.w, τ.nonneg, τ.sum_eq_one⟩ i0 ⟨0, T.S.N_pos k⟩ F
    (Real.exp (-(κ.α * T.S.n k / 3)))
  intro xs
  by_cases hg : ∀ j ∈ J, j ≠ i0 → Needs.DegGate (T.S.E k) PT.tiling.c π.w 2 (bstar T k) (xs j)
  · have htail : (∑ z ∈ Finset.univ.filter (fun z =>
        Needs.DegGate (T.S.E k) PT.tiling.c π.w 2 (bstar T k) z ∧
        100 * (3 : ℝ) ^ κ.u * 2 * bstar T k <
          |Needs.inter (T.S.E k) PT.tiling.c π.w J (Function.update xs i0 z)|), τ.w z) ≤
          Real.exp (-(κ.α * T.S.n k / 3)) := by
      cases hc : PT.tiling.c
      · exact htf S 0 J i0 hi0 hJ xs (by simpa [hc] using hg)
      · exact htt S 0 J i0 hi0 hJ xs (by simpa [hc] using hg)
    apply le_trans _ htail
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro z _
    by_cases hF : F (Function.update xs i0 z)
    · have hz : Needs.DegGate (T.S.E k) PT.tiling.c π.w 2 (bstar T k) z := by
        change |clusterDegree PT hPT hm W b z - 1 / 2| ≤ 2 * bstar T k
        simpa only [Function.update_self] using hF.1 i0 hi0
      have hb : 100 * (3 : ℝ) ^ κ.u * 2 * bstar T k <
          |Needs.inter (T.S.E k) PT.tiling.c π.w J (Function.update xs i0 z)| := by
        rw [← conditional_interaction_eq]
        exact hs.trans hF.2
      simp [hF, hz, hb]
    · simp only [if_neg hF]
      split_ifs
      · exact τ.nonneg z
      · exact le_rfl
  · have hzero : ∀ z, ¬ F (Function.update xs i0 z) := by
      intro z hF
      apply hg
      intro j hj hji
      have hh := hF.1 j hj
      rw [Function.update_of_ne hji] at hh
      exact hh
    simp only [if_neg (hzero _), Finset.sum_const_zero]
    positivity

/-- Record scopes of distinct slices are disjoint. -/
theorem raw_slice_scopes_disjoint (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    {s t : ClusterSlice PT} (hst : s ≠ t) :
    Disjoint (raw_slice_scope PT hPT hm s) (raw_slice_scope PT hPT hm t) := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  exact hst (((Finset.mem_filter.mp hr).2).symm.trans (Finset.mem_filter.mp hs).2)

/-- Any function of one slice's primitive records reads its full raw slice scope. -/
theorem raw_slice_function_depends (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (s : ClusterSlice PT) (F : (∀ r, (clusterSolver PT hPT hm s.1).Val r) → ℝ) :
    ClusterHistoryDependsOn (fun W => F (historyOnSlice W s)) (raw_slice_scope PT hPT hm s) := by
  intro W W' h
  apply congrArg F
  funext r
  exact h ⟨s, r⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- Each raw odd marginal has exactly the high-mode nominal profile mean. -/
theorem raw_marginal_mean (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) (y : Fin (T.S.N k)) :
    (clusterHistoryLaw PT hPT hm).E (fun W => clusterMarginal PT hPT hm W b y) =
      (PT.π (patchAt PT hPT b.1)).w y := by
  let s := clusterSliceAt PT hPT b.1
  let S := clusterSolver PT hPT hm s.1
  let g := S.groupOf (solverWordAt PT hPT hm b.1)
  have hS : PT.solver s.1 = some S :=
    Classical.choose_spec (hPT.cluster_solver (highMode_isCluster PT hm) s.1)
  have hmean : (S.recLaw PT.parameter).E (fun W => S.oddMarginal g W y) = (PT.π s.1).w y := by
    rw [hPT.high_profile hm s.1]
    exact (hPT.raw_profile (highMode_isCluster PT hm) s.1 S hS g y).symm
  exact (raw_slice_expect PT hPT hm s (fun W => S.oddMarginal g W y)).trans hmean

/-- Every linear test of an odd marginal averages to the nominal profile test. -/
theorem raw_marginal_linear_mean (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) (F : Fin (T.S.N k) → ℝ) :
    (clusterHistoryLaw PT hPT hm).E (fun W => ∑ y, clusterMarginal PT hPT hm W b y * F y) =
      ∑ y, (PT.π (patchAt PT hPT b.1)).w y * F y := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (clusterHistoryLaw PT hPT hm).E (fun W => clusterMarginal PT hPT hm W b y) * F y := by
      rw [FinLaw.E, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro W _
      ring
    _ = _ := by rw [raw_marginal_mean]

/-- Independent remaining bulk columns average to their common nominal law. -/
theorem raw_bulk_product_expectation (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (s : Finset (BulkIndex PT hPT a))
    (F : BulkIndex PT hPT a → Fin (T.S.N k) → ℝ)
    (G : ClusterHistory PT hPT hm → ℝ) (A : Finset (ClusterRecordIndex PT hPT hm))
    (hG : ClusterHistoryDependsOn G A)
    (hdisj : ∀ b ∈ s, Disjoint A (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1))) :
    (clusterHistoryLaw PT hPT hm).E (fun W => G W *
      ∏ b ∈ s, ∑ y, clusterMarginal PT hPT hm W b.1 y * F b y) =
      (clusterHistoryLaw PT hPT hm).E G *
        ∏ b ∈ s, ∑ y, (PT.π (patchAt PT hPT a.1)).w y * F b y := by
  let f := fun b : BulkIndex PT hPT a => fun W : ClusterHistory PT hPT hm =>
    ∑ y, clusterMarginal PT hPT hm W b.1 y * F b y
  let B := fun b : BulkIndex PT hPT a => raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1)
  have hf (b : BulkIndex PT hPT a) : ClusterHistoryDependsOn (f b) (B b) := by
    exact raw_slice_function_depends PT hPT hm (clusterSliceAt PT hPT b.1.1)
      (fun W => ∑ y, (clusterSolver PT hPT hm (patchAt PT hPT b.1.1)).oddMarginal
        ((clusterSolver PT hPT hm (patchAt PT hPT b.1.1)).groupOf (solverWordAt PT hPT hm b.1.1)) W y * F b y)
  have hB (b b' : BulkIndex PT hPT a) (hbb : b ≠ b') : Disjoint (B b) (B b') := by
    apply raw_slice_scopes_disjoint
    intro hs
    apply hbb
    apply Subtype.ext
    exact cluster_bulk_slices_injective PT hPT a b.2 b'.2 hs
  have hfprod : ClusterHistoryDependsOn (fun W => ∏ b ∈ s, f b W) (s.biUnion B) := by
    intro W W' h
    apply Finset.prod_congr rfl
    intro b hb
    apply hf b
    intro r hr
    exact h r (Finset.mem_biUnion.mpr ⟨b, hb, hr⟩)
  have hAB : Disjoint A (s.biUnion B) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.mp hs
    exact Finset.disjoint_left.mp (hdisj b hb) hr hrb
  have hmul := HypercubeRamsey.Lane_q_s15_c1.clusterHistory_E_mul_of_disjoint
    PT hPT hm G (fun W => ∏ b ∈ s, f b W) A (s.biUnion B) hG hfprod hAB
  have hprod : (clusterHistoryLaw PT hPT hm).E (fun W => ∏ b ∈ s, f b W) =
      ∏ b ∈ s, (clusterHistoryLaw PT hPT hm).E (f b) := by
    unfold clusterHistoryLaw
    apply finite_product_expectation_disjoint _ s f B hf hB
  rw [hmul, hprod]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  have hpatch := (Finset.mem_filter.mp b.2).2.2.1
  simpa only [f, hpatch] using raw_marginal_linear_mean PT hPT hm b.1 (F b)

/-- One conditional column factor in the positive interaction envelope. -/
noncomputable def raw_column_factor (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (b : OddPosition T k)
    (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) : ℝ :=
  ∑ y, clusterMarginal PT hPT hm W b y * ∏ j ∈ I, clusterNominalRatio PT hPT a (xs j) y

/-- The corresponding nominal column factor. -/
noncomputable def nominal_column_factor (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) : ℝ :=
  ∑ y, (PT.π (patchAt PT hPT a.1)).w y * ∏ j ∈ I, clusterNominalRatio PT hPT a (xs j) y

/-- The nominal moderation predicate with the redundant column index removed. -/
def nominal_tuple_moderate (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) (xs : Fin κ.u → Fin (T.S.N k)) : Prop :=
  ∀ J : Finset (Fin κ.u), 2 ≤ J.card →
    |S12.inter (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w J xs| ≤ κ.ξ

theorem nominal_moderate_replicated (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) {d : ℕ} (hd : 0 < d) (xs : Fin κ.u → Fin (T.S.N k)) :
    S12.Moderate (T.S.E k) PT.tiling.c
      (fun _ : Fin d => (PT.π (patchAt PT hPT a.1)).w) κ.ξ xs ↔ nominal_tuple_moderate PT hPT a xs := by
  constructor
  · intro h J hJ
    exact h ⟨0, hd⟩ J hJ
  · intro h l J hJ
    exact h J hJ

theorem nominal_ratio_nonneg (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) (x y : Fin (T.S.N k)) : 0 ≤ clusterNominalRatio PT hPT a x y := by
  unfold clusterNominalRatio
  dsimp only
  split_ifs with h
  · exact div_nonneg (by unfold hit; split_ifs <;> norm_num) h.le
  · exact le_rfl

theorem raw_column_factor_nonneg (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (b : OddPosition T k)
    (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
    0 ≤ raw_column_factor PT hPT hm W a b I xs := by
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (conditional_odd_law PT hPT hm W b |>.nonneg y)
    (Finset.prod_nonneg fun j _ => nominal_ratio_nonneg PT hPT a (xs j) y)

theorem nominal_column_factor_nonneg (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
    0 ≤ nominal_column_factor PT hPT a I xs := by
  exact Finset.sum_nonneg fun y _ => mul_nonneg ((PT.π _).nonneg y)
    (Finset.prod_nonneg fun j _ => nominal_ratio_nonneg PT hPT a (xs j) y)

/-- On positive nominal degree gates, the nominal factor power is the Section 12 product term. -/
theorem nominal_factor_power_eq_posTerm (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a : EvenPosition T k) (d : ℕ) (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k))
    (hpos : ∀ j ∈ I, 0 < deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w (xs j)) :
    nominal_column_factor PT hPT a I xs ^ d =
      S12.posTerm (T.S.E k) PT.tiling.c (fun _ : Fin d => (PT.π (patchAt PT hPT a.1)).w) I xs := by
  have hf : nominal_column_factor PT hPT a I xs =
      ∑ y, (PT.π (patchAt PT hPT a.1)).w y *
        ∏ j ∈ I, (1 + S12.acoef (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w (xs j) y) := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [clusterNominalRatio, if_pos (hpos j hj), S12.acoef]
    ring
  rw [hf]
  simp only [S12.posTerm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A positive center tuple lies on positive nominal degree gates. -/
theorem center_tuple_nominal_positive_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k,
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      ∀ hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0,
      ∀ xs : Fin κ.u → Fin (T.S.N k),
      (∏ j, (center_sigma_law PT hPT hm W a Y hσ).w (xs j)) ≠ 0 →
      ∀ j, (2 / 5 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w (xs j) := by
  have hb := (bstar_tendsto_zero T).eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  filter_upwards [cluster_clean_scales_eventually κ hκ T, hb] with k hk hb
  intro PT hPT hm W hW a Y hσ xs hprod j
  obtain ⟨v, hv, hC, hs⟩ := center_sigma_clean_corner PT hPT hm W hW a Y hσ
  have hw : (center_sigma_law PT hPT hm W a Y hσ).w (xs j) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ _)
  have h := hC.degOwn (xs j) (hs _ hw)
  have he := (hk PT hPT hm (patchAt PT hPT a.1)).2.2.1
  have hd : |deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w (xs j) - 1 / 2| ≤ bstar T k := by
    apply le_trans _ he
    rcases hm with hmode | hmode <;> simpa [OwnDegOK, hmode] using h
  linarith [(abs_le.mp hd).1]

/-- On such a tuple a singled-out conditional envelope factor has a fixed cap. -/
theorem raw_column_factor_le_three_pow (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (b : OddPosition T k)
    (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k))
    (hpos : ∀ j, (2 / 5 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π (patchAt PT hPT a.1)).w (xs j)) :
    raw_column_factor PT hPT hm W a b I xs ≤ (3 : ℝ) ^ κ.u := by
  have hrat (j : Fin κ.u) (y : Fin (T.S.N k)) : clusterNominalRatio PT hPT a (xs j) y ≤ 3 := by
    have hd := hpos j
    unfold clusterNominalRatio
    rw [if_pos (by linarith)]
    apply (div_le_iff₀ (by linarith)).mpr
    have hh : hit (T.S.E k) PT.tiling.c (xs j) y ≤ 1 := by unfold hit; split_ifs <;> norm_num
    linarith
  have hprod (y : Fin (T.S.N k)) : (∏ j ∈ I, clusterNominalRatio PT hPT a (xs j) y) ≤ (3 : ℝ) ^ κ.u := by
    calc
      _ ≤ ∏ _j ∈ I, (3 : ℝ) := Finset.prod_le_prod₀
        (fun j _ => nominal_ratio_nonneg PT hPT a (xs j) y) (fun j _ => hrat j y)
      _ = (3 : ℝ) ^ I.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ I |>.trans_eq (Fintype.card_fin κ.u))
  calc
    _ ≤ ∑ y, clusterMarginal PT hPT hm W b y * (3 : ℝ) ^ κ.u :=
      Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hprod y) ((conditional_odd_law PT hPT hm W b).nonneg y)
    _ = (3 : ℝ) ^ κ.u := by
      rw [← Finset.sum_mul]
      change (∑ y, (conditional_odd_law PT hPT hm W b).w y) * (3 : ℝ) ^ κ.u = _
      rw [(conditional_odd_law PT hPT hm W b).sum_eq_one, one_mul]

/-- The averaged remaining nominal column factors are bounded on moderate center tuples. -/
theorem center_moderate_factor_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k,
      ∀ Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1,
      ∀ hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y ≠ 0,
      ∀ xs : Fin κ.u → Fin (T.S.N k),
      (∏ j, (center_sigma_law PT hPT hm W a Y hσ).w (xs j)) ≠ 0 →
      nominal_tuple_moderate PT hPT a xs → ∀ d : ℕ, d ≤ T.S.n k → ∀ I : Finset (Fin κ.u),
      nominal_column_factor PT hPT a I xs ^ d ≤ Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ) := by
  have hpoint (c : Colour) := S12.moderate_posTerm_pointwise κ hκ T hDeep c 2 (by norm_num)
  filter_upwards [hpoint false, hpoint true, center_tuple_nominal_positive_eventually κ hκ T,
    center_sigma_width_eventually κ hκ T, nominal_cluster_width_eventually κ hκ T]
    with k hf ht hpos hτw hπw
  intro PT hPT hm W hW a Y hσ xs hprod hmod d hd I
  let τ := center_sigma_law PT hPT hm W a Y hσ
  let π := PT.π (patchAt PT hPT a.1)
  have hπ : π.SupportedIn (T.Y k) := by
    intro y hy
    apply hPT.law_supported
    intro h
    exact hy (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports (patchAt PT hPT a.1)).2.2.2
      ((hPT.tiling_valid.patch_supports (patchAt PT hPT a.1)).2.2.1 h))).1
  let S : S12.InterSetting T k (κ.xs / 4) := {
    d := d, d_le := hd, τ := τ, π := fun _ => π,
    τ_supp := center_sigma_stage_support PT hPT hm W hW a Y hσ,
    π_supp := fun _ => hπ, τ_width := hτw PT hPT hm W a Y hσ,
    π_width := fun _ => hπw PT hPT hm (patchAt PT hPT a.1) }
  have hsupport (j : Fin κ.u) : 0 < τ.w (xs j) := by
    exact lt_of_le_of_ne (τ.nonneg _) ((Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ _)).symm
  have hmod' : S12.Moderate (T.S.E k) PT.tiling.c (fun l => (S.π l).w) κ.ξ xs := by
    intro l J hJ
    exact hmod J hJ
  have hbound : S12.posTerm (T.S.E k) PT.tiling.c (fun l => (S.π l).w) I xs ≤
      Real.exp ((2 : ℝ) ^ κ.u * d * κ.ξ) := by
    cases hc : PT.tiling.c
    · exact hf S κ.ξ xs I hsupport (by simpa [hc] using hmod')
    · exact ht S κ.ξ xs I hsupport (by simpa [hc] using hmod')
  have heq := nominal_factor_power_eq_posTerm PT hPT a d I xs
    (fun j _ => by linarith [hpos PT hPT hm W hW a Y hσ xs hprod j])
  rw [heq]
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hd) (by positivity : 0 ≤ (2 : ℝ) ^ κ.u)) hκ.ξ_rng.1.le

/-- Product weight of a center tuple in its local reference outcome. -/
noncomputable def center_tuple_weight (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (xs : Fin κ.u → Fin (T.S.N k)) : ℝ :=
  ∏ j, HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y (xs j)

/-- The column-local gated anomaly; the gate retains only coordinates involved in J. -/
def column_gated_anomaly (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (b : OddPosition T k)
    (J : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) : Prop :=
  2 ≤ J.card ∧
    (∀ j ∈ J, |clusterDegree PT hPT hm W b (xs j) - 1 / 2| ≤ 2 * bstar T k) ∧
    2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|

/-- The nominal-large part after averaging the bulk histories. -/
noncomputable def nominal_large_piece (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : ℝ :=
  ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).E fun Y =>
    ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
      center_tuple_weight PT hPT hm W a Y xs *
        (if ¬ nominal_tuple_moderate PT hPT a xs then
          nominal_column_factor PT hPT a I xs ^ (clusterBulkNeighbours PT hPT a).card else 0)

/-- The nominal-large part before averaging bulk histories. -/
noncomputable def raw_large_piece (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) : ℝ :=
  ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).E fun Y =>
    ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
      center_tuple_weight PT hPT hm W a Y xs *
        (if ¬ nominal_tuple_moderate PT hPT a xs then
          ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0)

/-- One moderate-tuple witness after averaging all other bulk histories. -/
noncomputable def moderate_witness_piece (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (b : BulkIndex PT hPT a)
    (J I : Finset (Fin κ.u)) : ℝ :=
  ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).E fun Y =>
    ∑ xs : Fin κ.u → Fin (T.S.N k), center_tuple_weight PT hPT hm W a Y xs *
      (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
        raw_column_factor PT hPT hm W a b.1 I xs *
          nominal_column_factor PT hPT a I xs ^ (Finset.univ.erase b).card else 0)

/-- The same witness before averaging the other bulk columns. -/
noncomputable def raw_witness_piece (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) (b : BulkIndex PT hPT a)
    (J I : Finset (Fin κ.u)) : ℝ :=
  ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).E fun Y =>
    ∑ xs : Fin κ.u → Fin (T.S.N k), center_tuple_weight PT hPT hm W a Y xs *
      (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
        ∏ b' : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b'.1 I xs else 0)

/-- A zero center row gives zero tuple weight since u is positive. -/
theorem center_tuple_weight_zero (κ : CConsts) (hκ : κ.Admissible)
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y = 0)
    (xs : Fin κ.u → Fin (T.S.N k)) : center_tuple_weight PT hPT hm W a Y xs = 0 := by
  have hu : 0 < κ.u := by have h := hκ.u_rng.2; omega
  unfold center_tuple_weight
  rw [hσ]
  simp [Finset.prod_const, hu.ne']

theorem center_tuple_weight_nonneg (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (xs : Fin κ.u → Fin (T.S.N k)) : 0 ≤ center_tuple_weight PT hPT hm W a Y xs := by
  exact Finset.prod_nonneg fun j _ => (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_nonneg
    (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
    (nbrLabels (clusterCenterRole PT hPT hm a).1 Y.2) (xs j)

/-- Bound an expectation on positive support, allowing arbitrary zero-weight values. -/
theorem finite_expectation_le_on_support {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (F : Ω → ℝ) (C : ℝ) (hF : ∀ ω, 0 < P.w ω → F ω ≤ C) : P.E F ≤ C := by
  calc
    P.E F ≤ P.E (fun _ => C) := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases h : P.w ω = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_left (hF ω (lt_of_le_of_ne (P.nonneg ω) (Ne.symm h))) (P.nonneg ω)
    _ = C := by simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

/-- The nominal-large piece is below half the required alarm budget. -/
theorem nominal_large_piece_bound_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k, nominal_large_piece PT hPT hm W a ≤
        (1 / 2) * Real.exp (-300 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  filter_upwards [center_nominal_bad_mass_eventually κ hκ T hDeep,
    center_tuple_nominal_positive_eventually κ hκ T, bulk_nonempty_eventually κ hκ T,
    peeling_factor_absorbed_eventually κ hκ T] with k hbad hpositive hbulk habs
  intro PT hPT hm W hW a
  unfold nominal_large_piece
  apply finite_expectation_le_on_support
  intro Y _
  by_cases hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y = 0
  · simp only [center_tuple_weight_zero κ hκ PT hPT hm W a Y hσ, zero_mul, Finset.sum_const_zero]
    positivity
  · let τ := center_sigma_law PT hPT hm W a Y hσ
    have hd : 0 < (clusterBulkNeighbours PT hPT a).card := Finset.card_pos.mpr (hbulk PT hPT a)
    have hb := hbad PT hPT hm W hW a Y hσ
    have heq : (∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
        center_tuple_weight PT hPT hm W a Y xs *
          (if ¬ nominal_tuple_moderate PT hPT a xs then
            nominal_column_factor PT hPT a I xs ^ (clusterBulkNeighbours PT hPT a).card else 0)) =
        ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ S12.Moderate (T.S.E k) PT.tiling.c
            (fun _ : Fin (clusterBulkNeighbours PT hPT a).card => (PT.π (patchAt PT hPT a.1)).w) κ.ξ xs then
            S12.prodW τ.w xs * S12.posTerm (T.S.E k) PT.tiling.c
              (fun _ : Fin (clusterBulkNeighbours PT hPT a).card => (PT.π (patchAt PT hPT a.1)).w) I xs else 0 := by
      apply Finset.sum_congr rfl
      intro I _
      apply Finset.sum_congr rfl
      intro xs _
      rw [nominal_moderate_replicated PT hPT a hd xs]
      change (∏ j, τ.w (xs j)) * (if ¬ nominal_tuple_moderate PT hPT a xs then _ else 0) =
        if ¬ nominal_tuple_moderate PT hPT a xs then (∏ j, τ.w (xs j)) * _ else 0
      by_cases hmod : nominal_tuple_moderate PT hPT a xs
      · simp only [if_neg (not_not.mpr hmod), mul_zero]
      · simp only [if_pos hmod]
        by_cases hp : (∏ j, τ.w (xs j)) = 0
        · simp [hp]
        · rw [nominal_factor_power_eq_posTerm PT hPT a _ I xs
            (fun j _ => by linarith [hpositive PT hPT hm W hW a Y hσ xs hp j])]
    rw [heq]
    exact hb.trans (habs PT hPT hm (patchAt PT hPT a.1))

/-- A moderate witness is charged by one-free tails after the remaining column average. -/
theorem moderate_witness_piece_bound_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ W : ClusterHistory PT hPT hm, 0 < (clusterHistoryLaw PT hPT hm).w W →
      ∀ a : EvenPosition T k, ∀ b : BulkIndex PT hPT a, ∀ J I : Finset (Fin κ.u),
      moderate_witness_piece PT hPT hm W a b J I ≤
        (3 : ℝ) ^ κ.u * Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ) *
          Real.exp (-(κ.α * T.S.n k / 3)) := by
  filter_upwards [center_moderate_factor_eventually κ hκ T hDeep,
    center_tuple_nominal_positive_eventually κ hκ T,
    center_conditional_gated_tuple_mass_eventually κ hκ T hDeep] with k hfactor hpos htail
  intro PT hPT hm W hW a b J I
  unfold moderate_witness_piece
  apply finite_expectation_le_on_support
  intro Y _
  by_cases hσ : HypercubeRamsey.Lane_q_s15_c1.clusterSigmaAtCenter PT hPT hm W a Y = 0
  · simp only [center_tuple_weight_zero κ hκ PT hPT hm W a Y hσ, zero_mul, Finset.sum_const_zero]
    positivity
  · let τ := center_sigma_law PT hPT hm W a Y hσ
    let C : ℝ := (3 : ℝ) ^ κ.u * Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hrem : (Finset.univ.erase b).card ≤ T.S.n k := by
      calc
        _ ≤ (Finset.univ : Finset (BulkIndex PT hPT a)).card := Finset.card_erase_le
        _ = (clusterBulkNeighbours PT hPT a).card := by simp [BulkIndex, Fintype.card_coe]
        _ ≤ T.S.n k := bulk_card_le PT hPT a
    by_cases hJ : 2 ≤ J.card
    · let B := fun xs : Fin κ.u → Fin (T.S.N k) =>
        (∀ j ∈ J, |clusterDegree PT hPT hm W b.1 (xs j) - 1 / 2| ≤ 2 * bstar T k) ∧
          2 * κ.ξ < |clusterInteraction PT hPT hm W b.1 J xs|
      have hpoint (xs : Fin κ.u → Fin (T.S.N k)) :
          center_tuple_weight PT hPT hm W a Y xs *
            (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
              raw_column_factor PT hPT hm W a b.1 I xs *
                nominal_column_factor PT hPT a I xs ^ (Finset.univ.erase b).card else 0) ≤
          C * (if B xs then ∏ j, τ.w (xs j) else 0) := by
        by_cases hg : nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs
        · have hB : B xs := hg.2.2
          rw [if_pos hg, if_pos hB]
          by_cases hp : (∏ j, τ.w (xs j)) = 0
          · change (∏ j, τ.w (xs j)) * _ ≤ _
            simp [hp]
          · have hnom := hfactor PT hPT hm W hW a Y hσ xs hp hg.1 (Finset.univ.erase b).card
              hrem I
            have hraw := raw_column_factor_le_three_pow PT hPT hm W a b.1 I xs
              (hpos PT hPT hm W hW a Y hσ xs hp)
            have hprod : raw_column_factor PT hPT hm W a b.1 I xs *
                nominal_column_factor PT hPT a I xs ^ (Finset.univ.erase b).card ≤ C :=
              mul_le_mul hraw hnom (pow_nonneg (nominal_column_factor_nonneg PT hPT a I xs) _)
                (by positivity)
            exact (mul_le_mul_of_nonneg_left hprod (center_tuple_weight_nonneg PT hPT hm W a Y xs)).trans_eq (mul_comm _ _)
        · rw [if_neg hg, mul_zero]
          split_ifs
          · exact mul_nonneg hC (Finset.prod_nonneg fun j _ => τ.nonneg (xs j))
          · simp only [mul_zero, le_refl]
      calc
        _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k), C * (if B xs then ∏ j, τ.w (xs j) else 0) :=
          Finset.sum_le_sum fun xs _ => hpoint xs
        _ = C * ∑ xs : Fin κ.u → Fin (T.S.N k), if B xs then ∏ j, τ.w (xs j) else 0 :=
          (Finset.mul_sum _ _ _).symm
        _ ≤ C * Real.exp (-(κ.α * T.S.n k / 3)) :=
          mul_le_mul_of_nonneg_left (htail PT hPT hm W hW a Y hσ b.1 J hJ) hC
    · simp [column_gated_anomaly, hJ]
      positivity

theorem raw_slice_records_eq (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W W' : ClusterHistory PT hPT hm) (s : ClusterSlice PT)
    (h : ∀ r ∈ raw_slice_scope PT hPT hm s, W r = W' r) :
    historyOnSlice W s = historyOnSlice W' s := by
  funext r
  exact h ⟨s, r⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)

/-- The center reference weight times its tuple weight reads only the center slice. -/
theorem center_reference_tuple_depends (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (xs : Fin κ.u → Fin (T.S.N k)) :
    ClusterHistoryDependsOn (fun W =>
      ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).w Y *
        center_tuple_weight PT hPT hm W a Y xs)
      (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT a.1)) := by
  exact raw_slice_function_depends PT hPT hm (clusterSliceAt PT hPT a.1)
    (fun R => ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw R).w Y *
      ∏ j, (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ (clusterCenterRole PT hPT hm a) R
        (nbrLabels (clusterCenterRole PT hPT hm a).1 Y.2) (xs j))

/-- Adding a conditional witness reads the union of its slice and the center slice. -/
theorem witness_reference_tuple_depends (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1)
    (b : BulkIndex PT hPT a) (J I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
    ClusterHistoryDependsOn (fun W =>
      ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).w Y *
        center_tuple_weight PT hPT hm W a Y xs *
          (if column_gated_anomaly PT hPT hm W b.1 J xs then raw_column_factor PT hPT hm W a b.1 I xs else 0))
      (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT a.1) ∪
        raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1)) := by
  intro W W' h
  have hc := center_reference_tuple_depends PT hPT hm a Y xs W W'
    (fun r hr => h r (Finset.mem_union_left _ hr))
  have he := raw_slice_records_eq PT hPT hm W W' (clusterSliceAt PT hPT b.1.1)
    (fun r hr => h r (Finset.mem_union_right _ hr))
  have hmarg (y : Fin (T.S.N k)) : clusterMarginal PT hPT hm W b.1 y = clusterMarginal PT hPT hm W' b.1 y := by
    unfold clusterMarginal
    dsimp only
    rw [he]
  have hdeg (x : Fin (T.S.N k)) : clusterDegree PT hPT hm W b.1 x = clusterDegree PT hPT hm W' b.1 x := by
    simp only [clusterDegree, deg, hmarg]
  have hinter : clusterInteraction PT hPT hm W b.1 J xs = clusterInteraction PT hPT hm W' b.1 J xs := by
    simp only [clusterInteraction, hmarg, hdeg]
  have hfactor : raw_column_factor PT hPT hm W a b.1 I xs = raw_column_factor PT hPT hm W' a b.1 I xs := by
    simp only [raw_column_factor, hmarg]
  have htest : column_gated_anomaly PT hPT hm W b.1 J xs ↔ column_gated_anomaly PT hPT hm W' b.1 J xs := by
    simp only [column_gated_anomaly, hdeg, hinter]
  have hif : (if column_gated_anomaly PT hPT hm W b.1 J xs then raw_column_factor PT hPT hm W a b.1 I xs else 0) =
      (if column_gated_anomaly PT hPT hm W' b.1 J xs then raw_column_factor PT hPT hm W' a b.1 I xs else 0) :=
    if_congr htest hfactor rfl
  exact congrArg₂ (fun x y : ℝ => x * y) hc hif

/-- Averaging a selected set of bulk envelope factors gives a nominal factor power. -/
theorem raw_bulk_factor_average (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (s : Finset (BulkIndex PT hPT a))
    (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k))
    (G : ClusterHistory PT hPT hm → ℝ) (A : Finset (ClusterRecordIndex PT hPT hm))
    (hG : ClusterHistoryDependsOn G A)
    (hdisj : ∀ b ∈ s, Disjoint A (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1))) :
    (clusterHistoryLaw PT hPT hm).E (fun W => G W * ∏ b ∈ s, raw_column_factor PT hPT hm W a b.1 I xs) =
      (clusterHistoryLaw PT hPT hm).E (fun W => G W * nominal_column_factor PT hPT a I xs ^ s.card) := by
  have hb := raw_bulk_product_expectation PT hPT hm a s
    (fun _ y => ∏ j ∈ I, clusterNominalRatio PT hPT a (xs j) y) G A hG hdisj
  have he : (∏ _b ∈ s, ∑ y, (PT.π (patchAt PT hPT a.1)).w y *
      ∏ j ∈ I, clusterNominalRatio PT hPT a (xs j) y) = nominal_column_factor PT hPT a I xs ^ s.card := by
    simp only [nominal_column_factor, Finset.prod_const]
  rw [he] at hb
  calc
    _ = (clusterHistoryLaw PT hPT hm).E G * nominal_column_factor PT hPT a I xs ^ s.card := hb
    _ = _ := by simp only [FinLaw.E, Finset.sum_mul, mul_assoc]

/-- The nominal-large mean replaces every independent bulk column by its nominal law. -/
theorem raw_large_piece_mean (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (a : EvenPosition T k) :
    (clusterHistoryLaw PT hPT hm).E (fun W => raw_large_piece PT hPT hm W a) =
      (clusterHistoryLaw PT hPT hm).E (fun W => nominal_large_piece PT hPT hm W a) := by
  unfold raw_large_piece nominal_large_piece FinLaw.E
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases hmod : nominal_tuple_moderate PT hPT a xs
  · simp only [not_not, if_neg (not_not.mpr hmod), mul_zero, Finset.sum_const_zero]
  · simp only [if_pos hmod]
    let G := fun W : ClusterHistory PT hPT hm =>
      ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).w Y *
        center_tuple_weight PT hPT hm W a Y xs
    have he := raw_bulk_factor_average PT hPT hm a Finset.univ I xs G
      (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT a.1))
      (center_reference_tuple_depends PT hPT hm a Y xs)
      (fun b _ => raw_slice_scopes_disjoint PT hPT hm ((Finset.mem_filter.mp b.2).2.2.2).symm)
    have hcard : (Finset.univ : Finset (BulkIndex PT hPT a)).card = (clusterBulkNeighbours PT hPT a).card := by
      simp [BulkIndex, Fintype.card_coe]
    rw [hcard] at he
    convert he using 1 <;> apply Finset.sum_congr rfl <;> intro W _ <;> simp only [FinLaw.E, G] <;> ring

/-- Freeze a moderate witness column and average every other bulk column independently. -/
theorem raw_witness_piece_mean (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (b : BulkIndex PT hPT a) (J I : Finset (Fin κ.u)) :
    (clusterHistoryLaw PT hPT hm).E (fun W => raw_witness_piece PT hPT hm W a b J I) =
      (clusterHistoryLaw PT hPT hm).E (fun W => moderate_witness_piece PT hPT hm W a b J I) := by
  unfold raw_witness_piece moderate_witness_piece FinLaw.E
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Y _
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xs _
  by_cases hmod : nominal_tuple_moderate PT hPT a xs
  · simp only [hmod, true_and]
    let G := fun W : ClusterHistory PT hPT hm =>
      ((clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))).w Y *
        center_tuple_weight PT hPT hm W a Y xs *
          (if column_gated_anomaly PT hPT hm W b.1 J xs then raw_column_factor PT hPT hm W a b.1 I xs else 0)
    have hdisj (b' : BulkIndex PT hPT a) (hb' : b' ∈ Finset.univ.erase b) :
        Disjoint (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT a.1) ∪
          raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1))
          (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b'.1.1)) := by
      apply Finset.disjoint_union_left.mpr
      refine ⟨raw_slice_scopes_disjoint PT hPT hm ((Finset.mem_filter.mp b'.2).2.2.2).symm, ?_⟩
      apply raw_slice_scopes_disjoint
      intro hslice
      apply (Finset.mem_erase.mp hb').1
      apply Subtype.ext
      exact (cluster_bulk_slices_injective PT hPT a b.2 b'.2 hslice).symm
    have he := raw_bulk_factor_average PT hPT hm a (Finset.univ.erase b) I xs G
      (raw_slice_scope PT hPT hm (clusterSliceAt PT hPT a.1) ∪
        raw_slice_scope PT hPT hm (clusterSliceAt PT hPT b.1.1))
      (witness_reference_tuple_depends PT hPT hm a Y b J I xs) hdisj
    convert he using 1
    · apply Finset.sum_congr rfl
      intro W _
      dsimp only [G]
      by_cases h : column_gated_anomaly PT hPT hm W b.1 J xs
      · simp only [if_pos h]
        rw [← Finset.mul_prod_erase (Finset.univ : Finset (BulkIndex PT hPT a))
          (fun b' => raw_column_factor PT hPT hm W a b'.1 I xs) (Finset.mem_univ b)]
        ring
      · simp only [if_neg h, mul_zero, zero_mul]
    · apply Finset.sum_congr rfl
      intro W _
      dsimp only [G]
      by_cases h : column_gated_anomaly PT hPT hm W b.1 J xs <;>
        simp only [h, if_true, if_false] <;> ring
  · simp only [hmod, false_and, if_false, mul_zero, Finset.sum_const_zero]

/-- Split a weighted alarm into nominal-large tuples and a finite moderate witness union. -/
theorem finite_weighted_alarm_split {B J : Type*} [Fintype B] [Fintype J]
    (A M : Prop) [Decidable A] [Decidable M] (F : B → J → Prop) [∀ b j, Decidable (F b j)] (C : ℝ) (hC : 0 ≤ C)
    (hwitness : A → M → ∃ b j, F b j) :
    (if A then C else 0) ≤ (if ¬ M then C else 0) +
      ∑ b, ∑ j, if M ∧ F b j then C else 0 := by
  by_cases hM : M
  · simp only [if_neg (not_not.mpr hM)]
    by_cases hA : A
    · obtain ⟨b, j, hj⟩ := hwitness hA hM
      simp only [if_pos hA, zero_add]
      calc
        C = if M ∧ F b j then C else 0 := by rw [if_pos ⟨hM, hj⟩]
        _ ≤ ∑ j', if M ∧ F b j' then C else 0 := by
          apply Finset.single_le_sum _ (Finset.mem_univ j)
          intro j' _
          split_ifs <;> positivity
        _ ≤ ∑ b', ∑ j', if M ∧ F b' j' then C else 0 := by
          apply Finset.single_le_sum _ (Finset.mem_univ b)
          intro b' _
          apply Finset.sum_nonneg
          intro j' _
          split_ifs <;> positivity
    · simp only [if_neg hA, zero_add]
      apply Finset.sum_nonneg
      intro b _
      apply Finset.sum_nonneg
      intro j _
      split_ifs <;> positivity
  · by_cases hA : A <;> simp [hA, hM, hC]

/-- At each center outcome, the raw interaction integrand splits into the two positive pieces. -/
theorem raw_interaction_integrand_split (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k)
    (Y : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1) :
    HypercubeRamsey.Lane_q_s15_c1.clusterInteractionIntegrandAtCenter PT hPT hm W a Y ≤
      (∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
        center_tuple_weight PT hPT hm W a Y xs *
          (if ¬ nominal_tuple_moderate PT hPT a xs then
            ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0)) +
      ∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u),
        ∑ xs : Fin κ.u → Fin (T.S.N k), center_tuple_weight PT hPT hm W a Y xs *
          (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
            ∏ b' : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b'.1 I xs else 0) := by
  let A := fun xs : Fin κ.u → Fin (T.S.N k) =>
    (∀ j, clusterJ0 PT hPT hm W a (xs j)) ∧
      ∃ b ∈ clusterBulkNeighbours PT hPT a, ∃ J : Finset (Fin κ.u),
        2 ≤ J.card ∧ 2 * κ.ξ < |clusterInteraction PT hPT hm W b J xs|
  have hwitness (xs : Fin κ.u → Fin (T.S.N k)) :
      A xs → nominal_tuple_moderate PT hPT a xs → ∃ b : BulkIndex PT hPT a,
        ∃ J : Finset (Fin κ.u), column_gated_anomaly PT hPT hm W b.1 J xs := by
    rintro ⟨hg, b, hb, J, hJ, hbad⟩ _
    refine ⟨⟨b, hb⟩, J, hJ, ?_, hbad⟩
    intro j _
    exact (hg j).2.1 b hb
  have hpoint (I : Finset (Fin κ.u)) (xs : Fin κ.u → Fin (T.S.N k)) :
      center_tuple_weight PT hPT hm W a Y xs *
        (if A xs then ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0) ≤
      center_tuple_weight PT hPT hm W a Y xs *
        (if ¬ nominal_tuple_moderate PT hPT a xs then
          ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0) +
      ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u), center_tuple_weight PT hPT hm W a Y xs *
        (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
          ∏ b' : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b'.1 I xs else 0) := by
    have hC : 0 ≤ center_tuple_weight PT hPT hm W a Y xs *
        ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs :=
      mul_nonneg (center_tuple_weight_nonneg PT hPT hm W a Y xs)
        (Finset.prod_nonneg fun b _ => raw_column_factor_nonneg PT hPT hm W a b.1 I xs)
    have hb := finite_weighted_alarm_split (B := BulkIndex PT hPT a) (J := Finset (Fin κ.u)) (A xs)
      (nominal_tuple_moderate PT hPT a xs)
      (fun (b : BulkIndex PT hPT a) (J : Finset (Fin κ.u)) => column_gated_anomaly PT hPT hm W b.1 J xs)
      (center_tuple_weight PT hPT hm W a Y xs * ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs)
      hC (hwitness xs)
    simpa only [mul_ite, mul_zero] using hb
  have heq : HypercubeRamsey.Lane_q_s15_c1.clusterInteractionIntegrandAtCenter PT hPT hm W a Y =
      ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k), center_tuple_weight PT hPT hm W a Y xs *
        (if A xs then ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0) := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xs _
    change center_tuple_weight PT hPT hm W a Y xs * (if A xs then clusterInteractionEnvelope PT hPT hm W a xs else 0) = _
    by_cases hA : A xs
    · simp only [if_pos hA, clusterInteractionEnvelope, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      congr 1
      exact (Finset.prod_coe_sort (clusterBulkNeighbours PT hPT a)
        (fun b => raw_column_factor PT hPT hm W a b I xs)).symm
    · simp only [if_neg hA, mul_zero, Finset.sum_const_zero]
  rw [heq]
  calc
    _ ≤ ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
        (center_tuple_weight PT hPT hm W a Y xs *
          (if ¬ nominal_tuple_moderate PT hPT a xs then
            ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0) +
        ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u), center_tuple_weight PT hPT hm W a Y xs *
          (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
            ∏ b' : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b'.1 I xs else 0)) :=
      Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun xs _ => hpoint I xs
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

/-- The raw cost is bounded by its nominal-large piece plus all moderate witnesses. -/
theorem raw_interaction_cost_split (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (a : EvenPosition T k) :
    clusterInteractionCost PT hPT hm W a ≤ raw_large_piece PT hPT hm W a +
      ∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u),
        raw_witness_piece PT hPT hm W a b J I := by
  rw [HypercubeRamsey.Lane_q_s15_c1.clusterInteractionCost_eq_centerExpectation]
  let P := (clusterSolver PT hPT hm (clusterSliceAt PT hPT a.1).1).refLaw (historyOnSlice W (clusterSliceAt PT hPT a.1))
  have hbound := (FinProb.expect_mono (as_probability P) (fun Y => raw_interaction_integrand_split PT hPT hm W a Y))
  apply hbound.trans_eq
  let L : ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1 → ℝ := fun Y =>
    ∑ I : Finset (Fin κ.u), ∑ xs : Fin κ.u → Fin (T.S.N k),
      center_tuple_weight PT hPT hm W a Y xs * (if ¬ nominal_tuple_moderate PT hPT a xs then
        ∏ b : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b.1 I xs else 0)
  let F : Finset (Fin κ.u) → BulkIndex PT hPT a → Finset (Fin κ.u) →
      ClusterSliceOutcome PT (clusterSliceAt PT hPT a.1).1 → ℝ := fun I b J Y =>
    ∑ xs : Fin κ.u → Fin (T.S.N k), center_tuple_weight PT hPT hm W a Y xs *
      (if nominal_tuple_moderate PT hPT a xs ∧ column_gated_anomaly PT hPT hm W b.1 J xs then
        ∏ b' : BulkIndex PT hPT a, raw_column_factor PT hPT hm W a b'.1 I xs else 0)
  change P.E (fun Y => L Y + ∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a,
    ∑ J : Finset (Fin κ.u), F I b J Y) = P.E L +
      ∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u), P.E (F I b J)
  unfold FinLaw.E
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

/-- The admissible interaction threshold leaves a linear exponential margin. -/
theorem interaction_xi_slack (κ : CConsts) (hκ : κ.Admissible) :
    (2 : ℝ) ^ κ.u * κ.ξ ≤ κ.α / 12 := by
  have hp : (2 : ℝ) ^ κ.u * (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100)) ≤ 1 / 16 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ (2 : ℝ) ^ (-4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by linarith [show (0 : ℝ) ≤ κ.u from Nat.cast_nonneg κ.u])
      _ = 1 / 16 := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  have hξ := mul_le_mul_of_nonneg_left hκ.ξ_rng.2.le (show (0 : ℝ) ≤ 2 ^ κ.u by positivity)
  simp only [Real.rpow_eq_pow] at hξ
  have hα := mul_le_mul_of_nonneg_left hp hκ.α_rng.1.le
  have hαpos := hκ.α_rng.1
  calc
    (2 : ℝ) ^ κ.u * κ.ξ ≤ κ.α * ((2 : ℝ) ^ κ.u * (2 : ℝ) ^ (-(10 * (κ.u : ℝ) + 100))) := by
      simpa only [mul_assoc, mul_left_comm] using hξ
    _ ≤ κ.α / 16 := by simpa only [mul_one_div] using hα
    _ ≤ κ.α / 12 := by linarith

/-- The high gain is uniformly sublinear in the host dimension. -/
theorem high_gain_upper (κ : CConsts) (hκ : κ.Admissible)
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) (i : Fin PT.tiling.m) :
    PT.tiling.gain i ≤ (κ.a / 10 ^ 6) * (T.S.n k : ℝ) ^ κ.ι := by
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hh : ((PT.tiling.P i).h : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    have h := (hPT.tiling_valid.allocation_bounds i).1
    have hm : ((PT.tiling.P i).h : ℝ) ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℕ) := by
      exact_mod_cast Nat.le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ
    apply hm.trans
    simpa only [Nat.cast_max] using h.le
  have hgain : PT.tiling.gain i = (κ.a / 10 ^ 6) * (PT.tiling.P i).h := by
    rcases hm with hmode | hmode <;> simp [Tiling.gain, hmode] <;> ring
  rw [hgain]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- All column, interaction and envelope choices are absorbed by the gain margin. -/
theorem moderate_witness_total_absorbed_eventually (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge, ∀ i,
      (T.S.n k : ℝ) * (12 : ℝ) ^ κ.u * Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ) *
        Real.exp (-(κ.α * T.S.n k / 3)) ≤ (1 / 2) * Real.exp (-300 * PT.tiling.gain i) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hα : 0 < κ.α := hκ.α_rng.1
  let A : ℝ := 300 * (κ.a / 10 ^ 6)
  have hA : 0 < A := by dsimp [A]; positivity
  have hι : κ.ι < 1 := by
    have h := hκ.ι_rng.2
    have hm := min_le_right κ.xs (min κ.η0 0.01)
    have hm' := min_le_right κ.η0 (0.01 : ℝ)
    linarith
  have hg := hn.eventually (real_eventually_rpow_le_mul (p := κ.ι) (q := 1)
    (c := κ.α / (8 * A)) hι (by positivity))
  have hlim : Tendsto (fun k => (12 : ℝ) ^ κ.u * (T.S.n k : ℝ) * Real.exp (-(κ.α / 8) * T.S.n k))
      atTop (nhds 0) := by
    have ht := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (κ.α / 8) (by positivity)).comp hn).const_mul ((12 : ℝ) ^ κ.u)
    simpa only [Real.rpow_one, mul_zero, Function.comp_def, mul_assoc] using ht
  have hsmall := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hg, hsmall] with k hg hs
  intro PT hPT hm i
  have hn0 : 0 ≤ (T.S.n k : ℝ) := Nat.cast_nonneg _
  have hgain : 300 * PT.tiling.gain i ≤ κ.α * T.S.n k / 8 := by
    have h := mul_le_mul_of_nonneg_left (high_gain_upper κ hκ PT hPT hm i) (by norm_num : (0 : ℝ) ≤ 300)
    have h2 := mul_le_mul_of_nonneg_left hg hA.le
    have heq : A * (κ.α / (8 * A) * (T.S.n k : ℝ) ^ (1 : ℝ)) = κ.α * T.S.n k / 8 := by
      rw [Real.rpow_one]; field_simp <;> ring
    rw [heq] at h2
    exact h.trans (by simpa [A, mul_assoc] using h2)
  have hbase : ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ - κ.α * T.S.n k / 3) + 300 * PT.tiling.gain i ≤
      -(κ.α / 8) * T.S.n k := by
    have h := mul_le_mul_of_nonneg_right (interaction_xi_slack κ hκ) hn0
    nlinarith
  have hb : (T.S.n k : ℝ) * (12 : ℝ) ^ κ.u *
      Real.exp (((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ - κ.α * T.S.n k / 3) + 300 * PT.tiling.gain i) ≤ 1 / 2 := by
    apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbase) (by positivity))
    simpa only [mul_comm (T.S.n k : ℝ) ((12 : ℝ) ^ κ.u)] using hs.le
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg (-300 * PT.tiling.gain i))
  calc
    _ = ((T.S.n k : ℝ) * (12 : ℝ) ^ κ.u *
        Real.exp (((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ - κ.α * T.S.n k / 3) + 300 * PT.tiling.gain i)) *
          Real.exp (-300 * PT.tiling.gain i) := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := hm

/-- Finite-law expectations distribute over addition. -/
theorem finite_expectation_add {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (f g : Ω → ℝ) :
    P.E (fun ω => f ω + g ω) = P.E f + P.E g := by
  simp only [FinLaw.E, mul_add, Finset.sum_add_distrib]

/-- The two positive pieces give the raw high-cluster interaction alarm mean. -/
theorem raw_interaction_alarm_mean (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ a : EvenPosition T k,
      (clusterHistoryLaw PT hPT hm).E (fun W => clusterInteractionCost PT hPT hm W a) ≤
        Real.exp (-300 * PT.tiling.gain (patchAt PT hPT a.1)) := by
  filter_upwards [nominal_large_piece_bound_eventually κ hκ T hDeep,
    moderate_witness_piece_bound_eventually κ hκ T hDeep,
    moderate_witness_total_absorbed_eventually κ hκ T] with k hlarge hwitness habs
  intro PT hPT hm a
  let P := clusterHistoryLaw PT hPT hm
  let C : ℝ := (3 : ℝ) ^ κ.u * Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ) *
    Real.exp (-(κ.α * T.S.n k / 3))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsplit : P.E (fun W => clusterInteractionCost PT hPT hm W a) ≤
      P.E (fun W => nominal_large_piece PT hPT hm W a) +
        ∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u),
          P.E (fun W => moderate_witness_piece PT hPT hm W a b J I) := by
    have hm' := FinProb.expect_mono (as_probability P) (fun W => raw_interaction_cost_split PT hPT hm W a)
    apply hm'.trans_eq
    change P.E (fun W => raw_large_piece PT hPT hm W a +
      ∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u), raw_witness_piece PT hPT hm W a b J I) = _
    rw [finite_expectation_add]
    simp_rw [finite_expectation_sum]
    simp only [P, raw_large_piece_mean, raw_witness_piece_mean]
  have hL : P.E (fun W => nominal_large_piece PT hPT hm W a) ≤
      (1 / 2) * Real.exp (-300 * PT.tiling.gain (patchAt PT hPT a.1)) := by
    apply finite_expectation_le_on_support
    intro W hW
    exact hlarge PT hPT hm W hW a
  have hW (I J : Finset (Fin κ.u)) (b : BulkIndex PT hPT a) :
      P.E (fun W => moderate_witness_piece PT hPT hm W a b J I) ≤ C := by
    apply finite_expectation_le_on_support
    intro W hW
    exact hwitness PT hPT hm W hW a b J I
  have hsum : (∑ I : Finset (Fin κ.u), ∑ b : BulkIndex PT hPT a, ∑ J : Finset (Fin κ.u),
      P.E (fun W => moderate_witness_piece PT hPT hm W a b J I)) ≤
        (T.S.n k : ℝ) * (12 : ℝ) ^ κ.u * Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ) *
          Real.exp (-(κ.α * T.S.n k / 3)) := by
    have hcount : (2 : ℝ) ^ κ.u * (2 : ℝ) ^ κ.u * (3 : ℝ) ^ κ.u = (12 : ℝ) ^ κ.u := by
      rw [← mul_pow, ← mul_pow]
      norm_num
    have hb : (Fintype.card (BulkIndex PT hPT a) : ℝ) ≤ T.S.n k := by
      exact_mod_cast (show Fintype.card (BulkIndex PT hPT a) ≤ T.S.n k by
        simpa [BulkIndex, Fintype.card_coe] using bulk_card_le PT hPT a)
    calc
      _ ≤ ∑ _I : Finset (Fin κ.u), ∑ _b : BulkIndex PT hPT a, ∑ _J : Finset (Fin κ.u), C :=
        Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun J _ => hW I J b
      _ = (Fintype.card (BulkIndex PT hPT a) : ℝ) * (12 : ℝ) ^ κ.u *
          Real.exp ((2 : ℝ) ^ κ.u * T.S.n k * κ.ξ) * Real.exp (-(κ.α * T.S.n k / 3)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_finset,
          Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        dsimp [C]
        rw [← hcount]
        ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) (Real.exp_nonneg _))
            (Real.exp_nonneg _)
  have hM := hsum.trans (habs PT hPT hm (patchAt PT hPT a.1))
  exact hsplit.trans (by linarith)

end HypercubeRamsey.Lane_sol_s15_alarm
