import HypercubeRamsey.S03.Injection.Sampler
import HypercubeRamsey.S03.Injection.Comparison_q_inj_comp

set_option maxHeartbeats 100000000

/-!
# Lemma 3.9, the forcing comparison (TeX 03:695–734)

The likelihood identity extracts the target atom product before any failure
probability is used. Single-target forcing has its own concentration claim.
Zero atoms, repeated targets and the empty query are handled in the final
finite comparison node, not by taking a logarithm of a zero atom.
-/

namespace HypercubeRamsey.Injection

open Filter
open HypercubeRamsey.Lane_q_inj_comp
open scoped BigOperators

private theorem lane_q_inj_comp_pr_finset_exists_le
    {Ω ι : Type*} [Fintype Ω] (P : FinProb Ω)
    (E : ι → Ω → Prop) (s : Finset ι) :
    P.pr (fun x => ∃ a ∈ s, E a x) ≤ ∑ a ∈ s, P.pr (E a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [FinProb.pr]
  | @insert a s ha ih =>
      have heq :
          (fun x => ∃ b ∈ insert a s, E b x) =
            (fun x => E a x ∨ ∃ b ∈ s, E b x) := by
        funext x
        simp [Finset.mem_insert, ha, or_left_comm, or_assoc]
      rw [heq]
      calc
        P.pr (fun x => E a x ∨ ∃ b ∈ s, E b x) ≤
            P.pr (E a) + P.pr (fun x => ∃ b ∈ s, E b x) :=
          FinProb.pr_union_le _ _ _
        _ ≤ P.pr (E a) + ∑ b ∈ s, P.pr (E b) :=
          add_le_add le_rfl ih
        _ = ∑ b ∈ insert a s, P.pr (E b) := by simp [ha]

def Targets {d t : ℕ} (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : Prop :=
  ∀ i ∈ S, x i = some (y i)

def PositiveDistinctTargets {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) : Prop :=
  (∀ i ∈ S, 0 < q i (y i)) ∧ Set.InjOn y (↑S : Set (Fin t))

noncomputable def pendingMass {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (j : Fin t) : ℝ :=
  ∑ i ∈ S.filter (fun i => j.val < i.val), q j (y i)

noncomputable def excludedFraction {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) (j : Fin t) : ℝ :=
  pendingMass q S y j / availableMass q x j ∅

/-- Residual after extracting the target atom product. -/
noncomputable def likelihoodFactor {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  (∏ i ∈ S, (availableMass q x i ∅)⁻¹) *
    ∏ j ∈ Finset.univ \ S, (1 - excludedFraction q S y x j)

noncomputable def linearError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  -(∑ i ∈ S, Real.log (availableMass q x i ∅)) -
    ∑ j ∈ Finset.univ \ S, excludedFraction q S y x j

noncomputable def quadraticError {d t : ℕ} (q : Fin t → Fin d → ℝ)
    (S : Finset (Fin t)) (y : Fin t → Fin d) (x : Path t d) : ℝ :=
  ∑ j ∈ Finset.univ \ S,
    |Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j|

/-- TeX 03:699–705. Stated multiplicatively, so tiny target atoms are never divided out. -/
theorem forcing_likelihood_identity :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      ∀ x, Good q x → Targets S y x →
        sequentialWeight q x = forcingWeight q S y x *
          (∏ i ∈ S, q i (y i)) * likelihoodFactor q S y x := by
  have hsmall : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.925 : ℝ))) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.925 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.925 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
    eventually_ge_atTop 100] with d hdsmall hd100
  intro t q hq S y hpos hsize x hx htargets
  classical
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (show 0 < d by omega)
  have hpow : (d : ℝ) ^ (-(0.925 : ℝ)) < 1 / 100 := by
    simpa only [Set.mem_Iio] using hdsmall
  have htrackMono : ∀ b c : ℕ, b ≤ c → trackingError q x b ≤ trackingError q x c := by
    intro b c hbc
    have finiteSet (n : ℕ) :
        ({0} ∪ {r : ℝ | ∃ a : Fin t, ∃ k : Fin (t + 1), k.val ≤ n ∧
          r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
      have hrange : (Set.range (fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|)).Finite := Set.finite_range _
      apply Set.Finite.union
      · exact Set.finite_singleton 0
      · apply hrange.subset
        intro r hr
        rcases hr with ⟨a, k, hk, rfl⟩
        exact ⟨(a, k), rfl⟩
    have hbdd := (finiteSet c).bddAbove
    unfold trackingError
    apply csSup_le_csSup hbdd
    · exact ⟨0, Or.inl rfl⟩
    · intro r hr
      rcases hr with h0 | ⟨a, k, hk, rfl⟩
      · exact Or.inl h0
      · exact Or.inr ⟨a, k, le_trans hk hbc, rfl⟩
  have hvalid (j : Fin t) : PrefixValid x j.val := by
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hx.1.1 k (lt_trans hk j.isLt)
    · intro k l hk hl hkl
      exact hx.1.2 k l (lt_trans hk j.isLt) (lt_trans hl j.isLt) hkl
  have hstop (j : Fin t) : trackingError q x j.val ≤ 1 / 20 := by
    exact (htrackMono j.val t (Nat.le_of_lt j.isLt)).trans hx.2.1
  have hAvail (j : Fin t) : 1 / 5 ≤ availableMass q x j ∅ := by
    exact (free_mass_before_stop q hq x j (hvalid j) (hstop j)).2
  have hAvailPos (j : Fin t) : 0 < availableMass q x j ∅ :=
    lt_of_lt_of_le (by norm_num) (hAvail j)
  have hpend (j : Fin t) : 0 ≤ pendingMass q S y j ∧
      pendingMass q S y j ≤ 10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    unfold pendingMass
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      exact hq.nonneg j (y i)
    · calc
        ∑ i ∈ S.filter (fun i => j.val < i.val), q j (y i) ≤
            ∑ i ∈ S.filter (fun i => j.val < i.val),
              10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
                apply Finset.sum_le_sum
                intro i hi
                exact hq.atom j (y i)
        _ = ((S.filter (fun i => j.val < i.val)).card : ℝ) *
              (10 * (d : ℝ) ^ (-(0.95 : ℝ))) := by simp
        _ ≤ (S.card : ℝ) * (10 * (d : ℝ) ^ (-(0.95 : ℝ))) := by
              apply mul_le_mul_of_nonneg_right
              · exact_mod_cast Finset.card_filter_le S (fun i => j.val < i.val)
              · positivity
        _ = 10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring
  have hpendSmall (j : Fin t) : pendingMass q S y j < 1 / 10 := by
    have hsize' : (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) := hsize
    have hbound : 10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
        10 * (d : ℝ) ^ (-(0.925 : ℝ)) := by
      calc
        10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
            10 * (d : ℝ) ^ (0.025 : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by gcongr
        _ = 10 * ((d : ℝ) ^ (0.025 : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) := by ring
        _ = 10 * (d : ℝ) ^ (-(0.925 : ℝ)) := by
          rw [← Real.rpow_add hd]
          norm_num
    exact lt_of_le_of_lt (hpend j).2 (by nlinarith [hbound, hpow])
  have hBFree (j : Fin t) {z : Fin d}
      (hz : z ∈ pendingLabels S y j) : Free x j.val z := by
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    have hi' := Finset.mem_filter.mp hi
    intro k hk hEq
    have htarget := htargets i hi'.1
    have hki : k = i := hx.1.2 k i k.isLt i.isLt (hEq.trans htarget.symm)
    omega
  have hpendingImage (j : Fin t) :
      pendingMass q S y j = ∑ z ∈ pendingLabels S y j, q j z := by
    unfold pendingMass pendingLabels
    symm
    apply Finset.sum_image
    intro i hi k hk hik
    have hiS := (Finset.mem_filter.mp hi).1
    have hkS := (Finset.mem_filter.mp hk).1
    exact hpos.2 hiS hkS hik
  have hmass (j : Fin t) :
      availableMass q x j (pendingLabels S y j) =
        availableMass q x j ∅ - pendingMass q S y j := by
    rw [hpendingImage j]
    unfold availableMass
    have hterm (z : Fin d) :
        (if Free x j.val z ∧ z ∉ pendingLabels S y j then q j z else 0) =
          (if Free x j.val z then q j z else 0) -
            (if z ∈ pendingLabels S y j then q j z else 0) := by
      by_cases hf : Free x j.val z
      · by_cases hz : z ∈ pendingLabels S y j
        · simp [hf, hz]
        · simp [hf, hz]
      · have hz : z ∉ pendingLabels S y j := by
          intro hz
          exact hf (hBFree j hz)
        simp [hf, hz]
    calc
      (∑ z, if Free x j.val z ∧ z ∉ pendingLabels S y j then q j z else 0) =
          ∑ z, ((if Free x j.val z then q j z else 0) -
            (if z ∈ pendingLabels S y j then q j z else 0)) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hterm z
      _ = (∑ z, if Free x j.val z then q j z else 0) -
            ∑ z, if z ∈ pendingLabels S y j then q j z else 0 := by
              rw [Finset.sum_sub_distrib]
      _ = availableMass q x j ∅ - ∑ z ∈ pendingLabels S y j, q j z := by
            simp [availableMass]
  have hmassPos (j : Fin t) :
      0 < availableMass q x j (pendingLabels S y j) := by
    rw [hmass]
    have := hpendSmall j
    linarith [hAvail j]
  have hstep (j : Fin t) :
      ordinaryWeight q x j ∅ (x j) =
        forcingStepWeight q S y x j (x j) *
          (if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
            else 1 - excludedFraction q S y x j) := by
    by_cases hj : j ∈ S
    · have htarg := htargets j hj
      have hfree : Free x j.val (y j) := by
        intro k hk heq
        have hki : k = j := hx.1.2 k j k.isLt j.isLt (by rw [heq, htarg])
        omega
      have hord : ordinaryWeight q x j ∅ (x j) =
          q j (y j) / availableMass q x j ∅ := by
        unfold ordinaryWeight
        rw [if_pos ⟨hvalid j, hstop j, hAvailPos j⟩]
        rw [htarg]
        simp [hfree]
      have hforce : forcingStepWeight q S y x j (x j) = 1 := by
        unfold forcingStepWeight
        rw [if_pos hj]
        rw [if_pos ⟨hvalid j, hstop j, hfree⟩]
        simp [htarg]
      simp [hj, hord, hforce, div_eq_mul_inv]
    · obtain ⟨z, hz⟩ := hx.1.1 j j.isLt
      have hfree : Free x j.val z := by
        intro k hk heq
        have hkj : k = j := hx.1.2 k j k.isLt j.isLt (by rw [heq, hz])
        omega
      have hnot : z ∉ pendingLabels S y j := by
        intro hzb
        rcases Finset.mem_image.mp hzb with ⟨i, hi, rfl⟩
        have hi' := Finset.mem_filter.mp hi
        have htarget := htargets i hi'.1
        have hji : j = i := hx.1.2 j i j.isLt i.isLt
          (by rw [hz, htarget])
        omega
      have hord : ordinaryWeight q x j ∅ (x j) =
          q j z / availableMass q x j ∅ := by
        unfold ordinaryWeight
        rw [if_pos ⟨hvalid j, hstop j, hAvailPos j⟩]
        rw [hz]
        simp [hfree]
      have hforce : forcingStepWeight q S y x j (x j) =
          q j z / availableMass q x j (pendingLabels S y j) := by
        unfold forcingStepWeight
        rw [if_neg hj]
        unfold ordinaryWeight
        rw [if_pos ⟨hvalid j, hstop j, hmassPos j⟩]
        rw [hz]
        simp [hfree, hnot]
      have hden : availableMass q x j (pendingLabels S y j) =
          availableMass q x j ∅ - pendingMass q S y j := hmass j
      rw [hord, hforce, if_neg hj, excludedFraction, hden]
      have hAne : availableMass q x j ∅ ≠ 0 := (hAvailPos j).ne'
      have hBne : availableMass q x j ∅ - pendingMass q S y j ≠ 0 := by
        rw [← hden]
        exact (hmassPos j).ne'
      field_simp [hAne, hBne]
  have hprod : sequentialWeight q x = forcingWeight q S y x *
      (∏ j : Fin t,
        if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
          else 1 - excludedFraction q S y x j) := by
    unfold sequentialWeight forcingWeight
    calc
      (∏ j, ordinaryWeight q x j ∅ (x j)) =
          ∏ j, forcingStepWeight q S y x j (x j) *
            (if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
              else 1 - excludedFraction q S y x j) := by
                apply Finset.prod_congr rfl
                intro j hj
                exact hstep j
      _ = (∏ j, forcingStepWeight q S y x j (x j)) *
            ∏ j, (if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
              else 1 - excludedFraction q S y x j) := Finset.prod_mul_distrib
  have hsplit :
      (∏ j : Fin t,
        if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
          else (1 - excludedFraction q S y x j)) =
          (∏ i ∈ S, q i (y i) * (availableMass q x i ∅)⁻¹) *
          (∏ j ∈ (Finset.univ \ S), (1 - excludedFraction q S y x j)) := by
    let f : Fin t → ℝ := fun j =>
      if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
      else 1 - excludedFraction q S y x j
    have hprodS : (∏ i ∈ S, f i) =
        ∏ i ∈ S, q i (y i) * (availableMass q x i ∅)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [f, hi]
    have hprodJ : (∏ j ∈ (Finset.univ \ S), f j) =
        ∏ j ∈ (Finset.univ \ S), (1 - excludedFraction q S y x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjnot : j ∉ S := (Finset.mem_sdiff.mp hj).2
      simp [f, hjnot]
    calc
      (∏ j : Fin t, f j) = ∏ j ∈ Finset.univ, f j := by simp
      _ = (∏ j ∈ (Finset.univ \ S), f j) * (∏ j ∈ S, f j) :=
            (Finset.prod_sdiff (Finset.subset_univ S)).symm
      _ = (∏ i ∈ S, q i (y i) * (availableMass q x i ∅)⁻¹) *
            (∏ j ∈ (Finset.univ \ S), (1 - excludedFraction q S y x j)) := by
            rw [hprodJ, hprodS]
            ring
  calc
    sequentialWeight q x = forcingWeight q S y x *
        (∏ j : Fin t,
          if j ∈ S then q j (y j) * (availableMass q x j ∅)⁻¹
            else 1 - excludedFraction q S y x j) := hprod
    _ = forcingWeight q S y x *
          ((∏ i ∈ S, q i (y i) * (availableMass q x i ∅)⁻¹) *
            (∏ j ∈ (Finset.univ \ S), (1 - excludedFraction q S y x j))) := by rw [hsplit]
    _ = forcingWeight q S y x * (∏ i ∈ S, q i (y i)) * likelihoodFactor q S y x := by
          unfold likelihoodFactor
          rw [Finset.prod_mul_distrib]
          ring

/-- TeX 03:709–713: weighted prefix versus the logarithmic uniform integral. -/
theorem prefix_log_comparison : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q → ∀ (i : Fin t) y,
      |(∑ j : Fin t, if j.val < i.val then q j y / (1 - (j.val : ℝ) / d) else 0) +
        Real.log (1 - (i.val : ℝ) / d)| ≤ K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
  refine ⟨120, by norm_num, ?_⟩
  intro d t q h i y
  classical
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 100) h.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hiT : (i.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.le_of_lt i.isLt)
  have hiFrac : (i.val : ℝ) / d ≤ 3 / 4 := by
    apply (div_le_iff₀ hd).2
    nlinarith [h.horizon]
  let n : ℕ := i.val
  let w : ℕ → ℝ := fun r => (1 - (r : ℝ) / d)⁻¹
  let c : ℕ → ℝ := fun r => if hr : r < t then q ⟨r, hr⟩ y - (1 / d : ℝ) else 0
  have hsumLt (f : Fin t → ℝ) (k : ℕ) (hk : k ≤ t) :
      (∑ j : Fin t, if j.val < k then f j else 0) =
        ∑ r ∈ Finset.range k, (if hr : r < t then f ⟨r, hr⟩ else 0) := by
    let T : Finset (Fin t) := Finset.univ.filter (fun j => j.val < k)
    calc
      (∑ j : Fin t, if j.val < k then f j else 0) = ∑ j ∈ T, f j := by
        dsimp [T]
        rw [← Finset.sum_filter]
      _ = ∑ r ∈ Finset.range k, (if hr : r < t then f ⟨r, hr⟩ else 0) := by
        symm
        apply Finset.sum_bij (fun r hr => ⟨r, lt_of_lt_of_le (Finset.mem_range.mp hr) hk⟩)
        · intro r hr
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hr⟩
        · intro r hr s hs heq
          exact congrArg Fin.val heq
        · intro j hj
          have hjk := (Finset.mem_filter.mp hj).2
          refine ⟨j.val, Finset.mem_range.mpr hjk, ?_⟩
          apply Fin.ext
          rfl
        · intro r hr
          have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) hk
          simp [hrt]
  have hpartial (k : ℕ) (hk : k ≤ n) :
      |∑ r ∈ Finset.range k, c r| ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have hkT : k ≤ t := by
      have hnT : n ≤ t := by dsimp [n]; exact Nat.le_of_lt i.isLt
      exact le_trans hk hnT
    let b : Fin (t + 1) := ⟨k, by omega⟩
    have hcol := h.column_prefix b y
    have hqrange : (∑ j : Fin t, if j.val < k then q j y else 0) =
        ∑ r ∈ Finset.range k, (if hr : r < t then q ⟨r, hr⟩ y else 0) :=
      hsumLt (fun j => q j y) k hkT
    have hcsum : (∑ r ∈ Finset.range k, c r) =
        (∑ r ∈ Finset.range k, (if hr : r < t then q ⟨r, hr⟩ y else 0)) -
          (k : ℝ) / d := by
      calc
        ∑ r ∈ Finset.range k, c r =
            ∑ r ∈ Finset.range k,
              ((if hr : r < t then q ⟨r, hr⟩ y else 0) -
                (if r < t then (1 / d : ℝ) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) hkT
                  simp [c, hrt]
        _ = (∑ r ∈ Finset.range k, (if hr : r < t then q ⟨r, hr⟩ y else 0)) -
              ∑ r ∈ Finset.range k, (if r < t then (1 / d : ℝ) else 0) := by
                rw [Finset.sum_sub_distrib]
        _ = _ := by
          have hconst :
              (∑ r ∈ Finset.range k, (if r < t then (1 / d : ℝ) else 0)) =
                (k : ℝ) / d := by
            calc
              _ = ∑ r ∈ Finset.range k, (1 / d : ℝ) := by
                apply Finset.sum_congr rfl
                intro r hr
                simp [lt_of_lt_of_le (Finset.mem_range.mp hr) hkT]
              _ = (k : ℝ) / d := by simp [Finset.sum_const]; ring
          rw [hconst]
    change |(∑ j : Fin t, if j.val < k then q j y else 0) - (k : ℝ) / d| ≤
      10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) at hcol
    rw [hqrange] at hcol
    rw [← hcsum] at hcol
    simpa [b] using hcol
  have hfracBound (k : ℕ) (hk : k ≤ n) : (k : ℝ) / d ≤ 3 / 4 := by
    have hkn : (k : ℝ) ≤ (i.val : ℝ) := by
      have : k ≤ i.val := by simpa [n] using hk
      exact_mod_cast this
    exact (div_le_div_of_nonneg_right hkn hd.le).trans hiFrac
  have hden (k : ℕ) (hk : k ≤ n) : 1 / 4 ≤ 1 - (k : ℝ) / d := by
    have := hfracBound k hk
    linarith
  have hwpos (k : ℕ) (hk : k ≤ n) : 0 < w k := by
    dsimp [w]
    exact inv_pos.mpr (by linarith [hden k hk])
  have hwle (k : ℕ) (hk : k ≤ n) : w k ≤ 4 := by
    dsimp [w]
    simpa using (inv_le_inv₀ (by linarith [hden k hk])
      (by norm_num : (0 : ℝ) < 1 / 4)).2 (hden k hk)
  have hwmono (k : ℕ) (hk : k + 1 ≤ n) : w k ≤ w (k + 1) := by
    have h0 := hden k (by omega)
    have h1 := hden (k + 1) hk
    have hstep : (k : ℝ) / d ≤ ((k + 1 : ℕ) : ℝ) / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact_mod_cast (Nat.le_succ k)
    have hdenle : 1 - ((k + 1 : ℕ) : ℝ) / d ≤ 1 - (k : ℝ) / d := by linarith
    dsimp [w]
    exact (inv_le_inv₀ (by linarith [h0]) (by linarith [h1])).2 hdenle
  have hvariation :
      (∑ r ∈ Finset.range (n - 1), (w (r + 1) - w r)) = w (n - 1) - w 0 := by
    have htelescope : ∀ m : ℕ,
        (∑ r ∈ Finset.range m, (w (r + 1) - w r)) = w m - w 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    exact htelescope (n - 1)
  have habel := Finset.sum_range_by_parts' c w n
  have habel' :
      (∑ r ∈ Finset.range n, c r * w r) =
        (∑ r ∈ Finset.range n, c r) * w (n - 1) -
          ∑ r ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (r + 1), c j) *
            (w (r + 1) - w r) := by
    simpa only [smul_eq_mul] using habel
  have hdevBound : |∑ r ∈ Finset.range n, c r * w r| ≤
      70 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have hfirst : |(∑ r ∈ Finset.range n, c r) * w (n - 1)| ≤
        40 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have hp := hpartial n le_rfl
      have hw := hwle (n - 1) (by omega)
      rw [abs_mul, abs_of_nonneg (le_of_lt (hwpos (n - 1) (by omega)))]
      calc
        |∑ r ∈ Finset.range n, c r| * w (n - 1) ≤
            (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) * 4 :=
              mul_le_mul hp hw (le_of_lt (hwpos (n - 1) (by omega))) (by positivity)
        _ = 40 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
    have hsecond :
        |∑ r ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (r + 1), c j) *
          (w (r + 1) - w r)| ≤ 30 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have hnonneg : ∀ r ∈ Finset.range (n - 1), 0 ≤ w (r + 1) - w r := by
        intro r hr
        have hrn : r + 1 ≤ n := by have := Finset.mem_range.mp hr; omega
        exact sub_nonneg.mpr (hwmono r hrn)
      have hsum := Finset.abs_sum_le_sum_abs
        (fun r : ℕ => (∑ j ∈ Finset.range (r + 1), c j) * (w (r + 1) - w r))
        (Finset.range (n - 1))
      calc
        |∑ r ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (r + 1), c j) *
            (w (r + 1) - w r)| ≤
          ∑ r ∈ Finset.range (n - 1),
            |(∑ j ∈ Finset.range (r + 1), c j) * (w (r + 1) - w r)| := hsum
        _ ≤ ∑ r ∈ Finset.range (n - 1),
            (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) * (w (r + 1) - w r) := by
              apply Finset.sum_le_sum
              intro r hr
              have hrn : r + 1 ≤ n := by have := Finset.mem_range.mp hr; omega
              have hp := hpartial (r + 1) hrn
              rw [abs_mul, abs_of_nonneg (hnonneg r hr)]
              exact mul_le_mul_of_nonneg_right hp (hnonneg r hr)
        _ = (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) *
              (∑ r ∈ Finset.range (n - 1), (w (r + 1) - w r)) := by rw [Finset.mul_sum]
        _ ≤ 30 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
              rw [hvariation]
              have hw0 : w 0 = 1 := by simp [w]
              rw [hw0]
              have hwend := hwle (n - 1) (by omega)
              have hfac : 0 ≤ 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by positivity
              calc
                (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) * (w (n - 1) - 1) ≤
                    (10 * (d : ℝ) ^ (-(1 / 8 : ℝ))) * 3 :=
                      mul_le_mul_of_nonneg_left (by linarith [hwend]) hfac
                _ = 30 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
    rw [habel']
    calc
      |(∑ r ∈ Finset.range n, c r) * w (n - 1) -
          ∑ r ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (r + 1), c j) *
            (w (r + 1) - w r)| ≤
          |(∑ r ∈ Finset.range n, c r) * w (n - 1)| +
            |∑ r ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (r + 1), c j) *
              (w (r + 1) - w r)| := by
                simpa using abs_sub_le
                  ((∑ r ∈ Finset.range n, c r) * w (n - 1)) 0
                  (∑ r ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (r + 1), c j) *
                    (w (r + 1) - w r))
      _ ≤ 70 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by nlinarith [hfirst, hsecond]
  have hdev :
      (∑ j : Fin t, if j.val < n then q j y * w j.val else 0) -
        (∑ j : Fin t, if j.val < n then (1 / d : ℝ) * w j.val else 0) =
          ∑ r ∈ Finset.range n, c r * w r := by
    calc
      _ = ∑ j : Fin t,
          if j.val < n then (q j y - (1 / d : ℝ)) * w j.val else 0 := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j.val < n <;> simp [hji] <;> ring
      _ = ∑ r ∈ Finset.range n, c r * w r := by
            rw [hsumLt (fun j => (q j y - (1 / d : ℝ)) * w j.val) n (by omega)]
            apply Finset.sum_congr rfl
            intro r hr
            have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) (by omega)
            simp [c, w, hrt]
  let Q : ℝ := ∑ j : Fin t,
    if j.val < n then q j y / (1 - (j.val : ℝ) / d) else 0
  let U : ℝ := ∑ j : Fin t,
    if j.val < n then (1 / d : ℝ) * w j.val else 0
  have hQrewrite : Q = ∑ j : Fin t, if j.val < n then q j y * w j.val else 0 := by
    dsimp [Q]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j.val < n <;> simp [w, hji, div_eq_mul_inv]
  have hUrange : U = ∑ r ∈ Finset.range n, (1 / d : ℝ) * w r := by
    dsimp [U]
    rw [hsumLt (fun j => (1 / d : ℝ) * w j.val) n (by omega)]
    apply Finset.sum_congr rfl
    intro r hr
    have hrt : r < t := lt_of_lt_of_le (Finset.mem_range.mp hr) (by omega)
    simp [hrt]
  have hqU : |Q - U| ≤ 70 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [hQrewrite]
    change |(∑ j : Fin t, if j.val < n then q j y * w j.val else 0) - U| ≤ _
    dsimp [U]
    rw [hdev]
    exact hdevBound
  have huniform :
      |U + Real.log (1 - (n : ℝ) / d)| ≤ 32 / d := by
    have hnle : (n : ℝ) ≤ 3 * d / 4 := by
      have hnfrac : (n : ℝ) / d ≤ 3 / 4 := by simpa [n] using hiFrac
      calc
        (n : ℝ) ≤ (3 / 4 : ℝ) * d := (div_le_iff₀ hd).1 hnfrac
        _ = 3 * d / 4 := by ring
    have hdn : 0 < (d : ℝ) - n := by nlinarith [hnle, h.horizon]
    have hmBound (r : ℕ) (hr : r < n) : (d : ℝ) / 4 ≤ (d : ℝ) - r := by
      have hrn : (r : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt hr)
      nlinarith [hnle]
    let ℓ : ℕ → ℝ := fun r => Real.log ((d : ℝ) - r)
    let u : ℕ → ℝ := fun r => ((d : ℝ) - r)⁻¹
    let v : ℕ → ℝ := fun r => Real.log (((d : ℝ) - r) / ((d : ℝ) - r - 1))
    have hterm (r : ℕ) (hr : r < n) :
        0 ≤ v r - u r ∧ v r - u r ≤ 32 / (d : ℝ) ^ 2 := by
      have hmr := hmBound r hr
      have hmr1 : (d : ℝ) / 4 ≤ (d : ℝ) - r - 1 := by
        have hrn : (r : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hr)
        nlinarith [hnle]
      have hupos : 0 < 1 - u r := by
        have hm0 : 0 < (d : ℝ) - r := by linarith [hmr]
        have hm1 : 0 < (d : ℝ) - r - 1 := by linarith [hmr1]
        dsimp [u]
        rw [show 1 - ((d : ℝ) - r)⁻¹ = (((d : ℝ) - r) - 1) / ((d : ℝ) - r) by
          field_simp [ne_of_gt hm0]
          ]
        exact div_pos hm1 hm0
      have hvEq : v r = -Real.log (1 - u r) := by
        dsimp [v, u]
        have hdenne : (d : ℝ) - r ≠ 0 := by linarith [hmr]
        have hnumne : (d : ℝ) - r - 1 ≠ 0 := by linarith [hmr1]
        have heq : ((d : ℝ) - r) / ((d : ℝ) - r - 1) =
            (1 - (((d : ℝ) - r)⁻¹))⁻¹ := by
          field_simp [hdenne, hnumne]
        rw [heq, Real.log_inv]
      have huHalf : u r ≤ 1 / 2 := by
        have hm0 : 0 < (d : ℝ) - r := by linarith [hmr]
        have hd4 : 0 < (d : ℝ) / 4 := by positivity
        have hu : u r ≤ 4 / d := by
          calc
            u r = ((d : ℝ) - r)⁻¹ := rfl
            _ ≤ ((d : ℝ) / 4)⁻¹ := (inv_le_inv₀ hm0 hd4).2 hmr
            _ = 4 / d := by field_simp [hd.ne']
        have hd100 : (100 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h.dimension
        have h4 : (4 : ℝ) / d ≤ 1 / 2 := by
          exact (div_le_iff₀ hd).2 (by nlinarith [hd100])
        exact hu.trans h4
      have hlogLower := Real.log_le_sub_one_of_pos hupos
      have hlogUpper' := Real.log_le_sub_one_of_pos (inv_pos.mpr hupos)
      rw [Real.log_inv] at hlogUpper'
      have hlogLower' : Real.log (1 - u r) ≤ -u r := by
        have heq : (1 - u r) - 1 = -u r := by ring
        rw [heq] at hlogLower
        exact hlogLower
      have hvLower : u r ≤ v r := by rw [hvEq]; linarith [hlogLower']
      have hvUpper : v r ≤ u r + 2 * (u r) ^ 2 := by
        rw [hvEq]
        have hupper : -Real.log (1 - u r) ≤ (u r) / (1 - u r) := by
          calc
            -Real.log (1 - u r) ≤ (1 - u r)⁻¹ - 1 := hlogUpper'
            _ = u r / (1 - u r) := by
              field_simp [ne_of_gt hupos]
              ring
        have hfrac : (u r) / (1 - u r) ≤ u r + 2 * (u r) ^ 2 := by
          apply (div_le_iff₀ hupos).2
          have hpoly : 0 ≤ (u r) ^ 2 * (1 - 2 * u r) :=
            mul_nonneg (sq_nonneg _) (by linarith [huHalf])
          nlinarith
        exact hupper.trans hfrac
      have huBound : u r ≤ 4 / d := by
        have hm0 : 0 < (d : ℝ) - r := by linarith [hmr]
        have hd4 : 0 < (d : ℝ) / 4 := by positivity
        calc
          u r = ((d : ℝ) - r)⁻¹ := rfl
          _ ≤ ((d : ℝ) / 4)⁻¹ := (inv_le_inv₀ hm0 hd4).2 hmr
          _ = 4 / d := by field_simp [hd.ne']
      constructor
      · linarith [hvLower]
      · have : 2 * (u r) ^ 2 ≤ 32 / (d : ℝ) ^ 2 := by
          have hsq : (u r) ^ 2 ≤ (4 / d) ^ 2 := by
            have hprod : 0 ≤ (4 / d - u r) * (4 / d + u r) :=
              mul_nonneg (sub_nonneg.mpr huBound) (by
                have hm0 : 0 < (d : ℝ) - r := by linarith [hmr]
                exact add_nonneg (by positivity) (inv_nonneg.mpr hm0.le))
            nlinarith [hprod]
          calc
            2 * (u r) ^ 2 ≤ 2 * (4 / d) ^ 2 := by nlinarith [hsq]
            _ = 32 / (d : ℝ) ^ 2 := by field_simp [hd.ne']; ring
        linarith [hvUpper]
    have htel : (∑ r ∈ Finset.range n, v r) = Real.log (d : ℝ) - Real.log ((d : ℝ) - n) := by
      have htermEq (r : ℕ) (hr : r < n) : v r = ℓ r - ℓ (r + 1) := by
        dsimp [v, ℓ]
        have hrPos : 0 < (d : ℝ) - r - 1 := by
          have := hmBound r hr
          have hrn : (r : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hr)
          nlinarith [hnle]
        rw [Real.log_div (ne_of_gt (by linarith [hrPos])) (ne_of_gt hrPos)]
        rw [show (d : ℝ) - r - 1 = (d : ℝ) - ((r + 1 : ℕ) : ℝ) by
          push_cast
          ring]
      calc
        ∑ r ∈ Finset.range n, v r =
            ∑ r ∈ Finset.range n, (ℓ r - ℓ (r + 1)) := by
              apply Finset.sum_congr rfl
              intro r hr
              exact htermEq r (Finset.mem_range.mp hr)
        _ = ℓ 0 - ℓ n := by
              have htelescope : ∀ m : ℕ,
                  (∑ r ∈ Finset.range m, (ℓ r - ℓ (r + 1))) = ℓ 0 - ℓ m := by
                intro m
                induction m with
                | zero => simp
                | succ m ih =>
                    rw [Finset.sum_range_succ, ih]
                    ring_nf
              exact htelescope n
        _ = Real.log (d : ℝ) - Real.log ((d : ℝ) - n) := by simp [ℓ]
    have hlogTarget :
        Real.log (d : ℝ) - Real.log ((d : ℝ) - n) =
          -Real.log (1 - (n : ℝ) / d) := by
      have heq : 1 - (n : ℝ) / d = ((d : ℝ) - n) / d := by field_simp
      rw [heq, Real.log_div hdn.ne' hd.ne']
      ring
    have hUsum : U = ∑ r ∈ Finset.range n, u r := by
      rw [hUrange]
      apply Finset.sum_congr rfl
      intro r hr
      have hrlt := Finset.mem_range.mp hr
      have hdenne : (d : ℝ) - r ≠ 0 := by linarith [hmBound r hrlt]
      dsimp [u, w]
      field_simp [hd.ne', hdenne]
    have hsumRem : 0 ≤ ∑ r ∈ Finset.range n, (v r - u r) ∧
        (∑ r ∈ Finset.range n, (v r - u r)) ≤ 32 / d := by
      constructor
      · apply Finset.sum_nonneg
        intro r hr
        exact (hterm r (Finset.mem_range.mp hr)).1
      · calc
          ∑ r ∈ Finset.range n, (v r - u r) ≤
              ∑ r ∈ Finset.range n, 32 / (d : ℝ) ^ 2 := by
                apply Finset.sum_le_sum
                intro r hr
                exact (hterm r (Finset.mem_range.mp hr)).2
          _ = (n : ℝ) * (32 / (d : ℝ) ^ 2) := by simp
          _ ≤ 32 / d := by
                have hn : (n : ℝ) ≤ (d : ℝ) := by nlinarith [hnle]
                have hd2 : 0 < (d : ℝ) := hd
                field_simp [hd2.ne']
                nlinarith [hn]
    have hdiff : Real.log (d : ℝ) - Real.log ((d : ℝ) - n) - U =
        ∑ r ∈ Finset.range n, (v r - u r) := by
      calc
        Real.log (d : ℝ) - Real.log ((d : ℝ) - n) - U =
            (∑ r ∈ Finset.range n, v r) - (∑ r ∈ Finset.range n, u r) := by
              rw [← htel, hUsum]
        _ = ∑ r ∈ Finset.range n, (v r - u r) := by rw [Finset.sum_sub_distrib]
    have hdiff' : U + Real.log (1 - (n : ℝ) / d) =
        -∑ r ∈ Finset.range n, (v r - u r) := by
      have hlogEq : Real.log (1 - (n : ℝ) / d) =
          -(Real.log (d : ℝ) - Real.log ((d : ℝ) - n)) := by linarith [hlogTarget]
      rw [hlogEq]
      linarith [hdiff]
    rw [hdiff']
    rw [abs_neg]
    rw [abs_of_nonneg hsumRem.1]
    exact hsumRem.2
  have hsumQ : Q =
      ∑ j : Fin t, if j.val < n then q j y * w j.val else 0 := hQrewrite
  have htarget :
      |Q + Real.log (1 - (n : ℝ) / d)| ≤
        70 * (d : ℝ) ^ (-(1 / 8 : ℝ)) + 32 / d := by
    calc
      |Q + Real.log (1 - (n : ℝ) / d)| ≤
          |Q - U| + |U + Real.log (1 - (n : ℝ) / d)| := by
            have heq : Q + Real.log (1 - (n : ℝ) / d) =
                (Q - U) + (U + Real.log (1 - (n : ℝ) / d)) := by ring
            rw [heq]
            exact abs_add_le _ _
      _ ≤ 70 * (d : ℝ) ^ (-(1 / 8 : ℝ)) + 32 / d := add_le_add hqU huniform
  have hdinv : 32 / d ≤ 32 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have hdle : (d : ℝ) ^ (-(1 : ℝ)) ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ d by omega))
      norm_num
    have hrecip : (d : ℝ) ^ (-(1 : ℝ)) = 1 / d := by
      simp [Real.rpow_neg_one, div_eq_mul_inv]
    calc
      32 / d = 32 * (d : ℝ) ^ (-(1 : ℝ)) := by rw [hrecip]; ring
      _ ≤ 32 * (d : ℝ) ^ (-(1 / 8 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdle (by norm_num)
  have hncast : (n : ℝ) = (i.val : ℝ) := by simp [n]
  rw [hncast] at htarget
  change |Q + Real.log (1 - (n : ℝ) / d)| ≤ 120 * (d : ℝ) ^ (-(1 / 8 : ℝ))
  calc
    |Q + Real.log (1 - (n : ℝ) / d)| ≤
        70 * (d : ℝ) ^ (-(1 / 8 : ℝ)) + 32 / d := htarget
    _ ≤ 102 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by nlinarith [hdinv]
    _ ≤ 120 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have hpow : 0 ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_nonneg hd.le _
      nlinarith

/-- TeX 03:714–717: replacing tracked denominators and omitting queried steps. -/
theorem linear_likelihood_cancellation : ∃ K : ℝ, 1 ≤ K ∧
    ∀ d t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → ∀ x, Good q x → Targets S y x →
      |linearError q S y x| ≤ K * S.card *
        ((d : ℝ) ^ (-(0.1 : ℝ)) + S.card * (d : ℝ) ^ (-(0.95 : ℝ))) := by
  obtain ⟨Kp, hKp, hprefix⟩ := prefix_log_comparison
  refine ⟨Kp + 300, by linarith, ?_⟩
  intro d t q h S y hpos x hx htargets
  classical
  let J : Finset (Fin t) := Finset.univ \ S
  let δ : ℝ := (d : ℝ) ^ (-(0.1 : ℝ))
  let P : Fin t → ℝ := fun j => 1 - (j.val : ℝ) / d
  let A : Fin t → ℝ := fun j => availableMass q x j ∅
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 100) h.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hdelta : 0 ≤ δ := by dsimp [δ]; positivity
  have hdeltaQuarter : (d : ℝ) ^ (-(1 / 8 : ℝ)) ≤ δ := by
    dsimp [δ]
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ d by omega))
    norm_num
  have htrackMono : ∀ b c : ℕ, b ≤ c → trackingError q x b ≤ trackingError q x c := by
    intro b c hbc
    have finiteSet (n : ℕ) :
        ({0} ∪ {r : ℝ | ∃ a : Fin t, ∃ k : Fin (t + 1), k.val ≤ n ∧
          r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
      have hrange : (Set.range (fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|)).Finite := Set.finite_range _
      apply Set.Finite.union
      · exact Set.finite_singleton 0
      · apply hrange.subset
        intro r hr
        rcases hr with ⟨a, k, hk, rfl⟩
        exact ⟨(a, k), rfl⟩
    have hbdd := (finiteSet c).bddAbove
    unfold trackingError
    apply csSup_le_csSup hbdd
    · exact ⟨0, Or.inl rfl⟩
    · intro r hr
      rcases hr with h0 | ⟨a, k, hk, rfl⟩
      · exact Or.inl h0
      · exact Or.inr ⟨a, k, le_trans hk hbc, rfl⟩
  have hvalid (j : Fin t) : PrefixValid x j.val := by
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hx.1.1 k (lt_trans hk j.isLt)
    · intro k l hk hl hkl
      exact hx.1.2 k l (lt_trans hk j.isLt) (lt_trans hl j.isLt) hkl
  have hstop (j : Fin t) : trackingError q x j.val ≤ 1 / 20 := by
    exact (htrackMono j.val t (Nat.le_of_lt j.isLt)).trans hx.2.1
  have hAvail (j : Fin t) :
      (availableMass q x j ∅ = 1 - usedMass q x j j.val) ∧
        1 / 5 ≤ availableMass q x j ∅ :=
    free_mass_before_stop q h x j (hvalid j) (hstop j)
  have hAvailPos (j : Fin t) : 0 < A j := by
    dsimp [A]
    exact lt_of_lt_of_le (by norm_num) (hAvail j).2
  have hPrefixDen (j : Fin t) : 1 / 4 ≤ P j := by
    dsimp [P]
    have hjt : (j.val : ℝ) / d ≤ 3 / 4 := by
      apply (div_le_iff₀ hd).2
      have hj : (j.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.le_of_lt j.isLt)
      nlinarith [h.horizon]
    linarith
  have hPpos (j : Fin t) : 0 < P j :=
    lt_of_lt_of_le (by norm_num) (hPrefixDen j)
  have htrackVal (j : Fin t) :
      |usedMass q x j j.val - (j.val : ℝ) / d| ≤ (d : ℝ) ^ (-(0.1 : ℝ)) := by
    have hfinite :
        ({0} ∪ {r : ℝ | ∃ a : Fin t, ∃ k : Fin (t + 1), k.val ≤ t ∧
          r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
      have hrange : (Set.range (fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|)).Finite := Set.finite_range _
      apply Set.Finite.union
      · exact Set.finite_singleton 0
      · apply hrange.subset
        intro r hr
        rcases hr with ⟨a, k, hk, rfl⟩
        exact ⟨(a, k), rfl⟩
    have hmem :
        |usedMass q x j j.val - (j.val : ℝ) / d| ∈
          ({0} ∪ {r : ℝ | ∃ a : Fin t, ∃ k : Fin (t + 1), k.val ≤ t ∧
          r = |usedMass q x a k.val - (k.val : ℝ) / d|}) := by
      right
      refine ⟨j, ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, ?_, rfl⟩
      omega
    have hle := le_csSup hfinite.bddAbove hmem
    exact hle.trans hx.2.2
  have hABdiff (j : Fin t) : |A j - P j| ≤ δ := by
    dsimp [A, P]
    rw [(hAvail j).1]
    have heq :
        1 - usedMass q x j j.val - (1 - (j.val : ℝ) / d) =
          -(usedMass q x j j.val - (j.val : ℝ) / d) := by ring
    rw [heq, abs_neg]
    simpa [δ] using htrackVal j
  have hprefixMass (i : Fin t) :
      (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤ 11 := by
    let b : Fin (t + 1) := ⟨i.val, by omega⟩
    have hcol := h.column_prefix b (y i)
    have hratio : (i.val : ℝ) / d ≤ 3 / 4 := by
      apply (div_le_iff₀ hd).2
      have hit : (i.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.le_of_lt i.isLt)
      nlinarith [h.horizon]
    have hsum :
        (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
          (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have h := (abs_le.mp hcol).2
      calc
        (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
            10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) + (i.val : ℝ) / d := by simpa [b] using h
        _ = (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
    have hpow : (d : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (show 1 ≤ d by omega)
      · norm_num
    calc
      (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
          (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := hsum
      _ ≤ 3 / 4 + 10 := by
        apply add_le_add hratio
        simpa using mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 10)
      _ ≤ 11 := by norm_num
  have hRatioAB (j : Fin t) :
      |Real.log (A j) - Real.log (P j)| ≤ 5 * |A j - P j| := by
    have hApos := hAvailPos j
    have hBpos := hPpos j
    have hAinv : (A j)⁻¹ ≤ 5 := by
      have hlow : (1 / 5 : ℝ) ≤ A j := (hAvail j).2
      have hinv := (inv_le_inv₀ hApos (by norm_num : (0 : ℝ) < 1 / 5)).2 hlow
      simpa using hinv
    have hBinv : (P j)⁻¹ ≤ 5 := by
      have hlow : (1 / 5 : ℝ) ≤ P j := le_trans (by norm_num) (hPrefixDen j)
      have hinv := (inv_le_inv₀ hBpos (by norm_num : (0 : ℝ) < 1 / 5)).2 hlow
      simpa using hinv
    have hratioPos : 0 < A j / P j := div_pos hApos hBpos
    have hratioInvPos : 0 < P j / A j := div_pos hBpos hApos
    have hratioUp : Real.log (A j / P j) ≤ 5 * |A j - P j| := by
      have hlog := Real.log_le_sub_one_of_pos hratioPos
      have heq : A j / P j - 1 = (A j - P j) / P j := by
        field_simp [hBpos.ne'] <;> ring
      rw [heq] at hlog
      calc
        Real.log (A j / P j) ≤ (A j - P j) / P j := hlog
        _ ≤ |A j - P j| / P j :=
              div_le_div_of_nonneg_right (le_abs_self _) hBpos.le
        _ = |A j - P j| * (P j)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ |A j - P j| * 5 :=
              mul_le_mul_of_nonneg_left hBinv (abs_nonneg _)
        _ = 5 * |A j - P j| := by ring
    have hratioInvUp : Real.log (P j / A j) ≤ 5 * |A j - P j| := by
      have hlog := Real.log_le_sub_one_of_pos hratioInvPos
      have heq : P j / A j - 1 = (P j - A j) / A j := by
        field_simp [hApos.ne'] <;> ring
      rw [heq] at hlog
      calc
        Real.log (P j / A j) ≤ (P j - A j) / A j := hlog
        _ ≤ |A j - P j| / A j := by
              rw [abs_sub_comm]
              exact div_le_div_of_nonneg_right (le_abs_self _) hApos.le
        _ = |A j - P j| * (A j)⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ |A j - P j| * 5 :=
              mul_le_mul_of_nonneg_left hAinv (abs_nonneg _)
        _ = 5 * |A j - P j| := by ring
    have hlogInv : Real.log (P j / A j) = -Real.log (A j / P j) := by
      have h1 := Real.log_div hApos.ne' hBpos.ne'
      have h2 := Real.log_div hBpos.ne' hApos.ne'
      rw [h1, h2]
      ring
    rw [← Real.log_div hApos.ne' hBpos.ne']
    exact abs_le.mpr ⟨by linarith [hlogInv, hratioInvUp], hratioUp⟩
  have hRecipDiff (j : Fin t) :
      |(A j)⁻¹ - (P j)⁻¹| ≤ 20 * δ := by
    have hApos := hAvailPos j
    have hBpos := hPpos j
    have hprodPos : 0 < A j * P j := mul_pos hApos hBpos
    have hprodLower : (1 / 20 : ℝ) ≤ A j * P j := by
      have hA := (hAvail j).2
      have hB := hPrefixDen j
      nlinarith [mul_le_mul hA hB (by norm_num : (0 : ℝ) ≤ 1 / 4) hApos.le]
    have hprodInv : (A j * P j)⁻¹ ≤ 20 := by
      have hinv :=
        (inv_le_inv₀ hprodPos (by norm_num : (0 : ℝ) < 1 / 20)).2 hprodLower
      simpa [mul_comm] using hinv
    have hEq : (A j)⁻¹ - (P j)⁻¹ = (P j - A j) / (A j * P j) := by
      field_simp [hApos.ne', hBpos.ne'] <;> ring
    rw [hEq, abs_div, abs_mul, abs_of_pos hApos, abs_of_pos hBpos]
    have hnum : |P j - A j| ≤ δ := by simpa [abs_sub_comm] using hABdiff j
    calc
      |P j - A j| / (A j * P j) ≤ δ / (A j * P j) :=
        div_le_div_of_nonneg_right hnum hprodPos.le
      _ = δ * (A j * P j)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ δ * 20 := mul_le_mul_of_nonneg_left hprodInv hdelta
      _ = 20 * δ := by ring
  have hJprefix (i : Fin t) :
      (∑ j ∈ J, if j.val < i.val then q j (y i) else 0) ≤ 11 := by
    calc
      (∑ j ∈ J, if j.val < i.val then q j (y i) else 0) ≤
          (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
            intro j hj hnot
            split_ifs
            · exact h.nonneg j (y i)
            · exact le_rfl
      _ ≤ 11 := hprefixMass i
  have hDenChange (i : Fin t) :
      |∑ j ∈ J, if j.val < i.val then
          q j (y i) / P j - q j (y i) / A j else 0| ≤ 220 * δ := by
    calc
      |∑ j ∈ J, if j.val < i.val then
          q j (y i) / P j - q j (y i) / A j else 0| ≤
          ∑ j ∈ J, |if j.val < i.val then
            q j (y i) / P j - q j (y i) / A j else 0| :=
              Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ J, (20 * δ) * (if j.val < i.val then q j (y i) else 0) := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hji : j.val < i.val
            · simp only [if_pos hji]
              have hq : 0 ≤ q j (y i) := h.nonneg j (y i)
              have hEq : q j (y i) / P j - q j (y i) / A j =
                  q j (y i) * ((P j)⁻¹ - (A j)⁻¹) := by
                rw [div_eq_mul_inv, div_eq_mul_inv]
                ring
              rw [hEq, abs_mul]
              have hRecip := hRecipDiff j
              rw [abs_sub_comm] at hRecip
              have hmul := mul_le_mul_of_nonneg_left hRecip hq
              simpa [abs_of_nonneg hq, mul_comm] using hmul
            · simp [hji]
      _ = (20 * δ) *
            (∑ j ∈ J, if j.val < i.val then q j (y i) else 0) := by rw [Finset.mul_sum]
      _ ≤ 220 * δ := by
            have hfac : 0 ≤ 20 * δ := by positivity
            have := mul_le_mul_of_nonneg_left (hJprefix i) hfac
            nlinarith
  have hOmit (i : Fin t) :
      0 ≤ (∑ j ∈ S, if j.val < i.val then q j (y i) / P j else 0) ∧
      (∑ j ∈ S, if j.val < i.val then q j (y i) / P j else 0) ≤
        40 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    constructor
    · apply Finset.sum_nonneg
      intro j hj
      split_ifs
      · exact div_nonneg (h.nonneg j (y i)) (hPpos j).le
      · exact le_rfl
    · calc
        (∑ j ∈ S, if j.val < i.val then q j (y i) / P j else 0) ≤
            ∑ j ∈ S, 40 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
              apply Finset.sum_le_sum
              intro j hj
              by_cases hji : j.val < i.val
              · have hq := h.atom j (y i)
                have hInv : (P j)⁻¹ ≤ 4 := by
                  have hlow : (1 / 4 : ℝ) ≤ P j := hPrefixDen j
                  have hinv := (inv_le_inv₀ (hPpos j)
                    (by norm_num : (0 : ℝ) < 1 / 4)).2 hlow
                  simpa using hinv
                simp only [if_pos hji]
                calc
                  q j (y i) / P j = q j (y i) * (P j)⁻¹ := by rw [div_eq_mul_inv]
                  _ ≤ (10 * (d : ℝ) ^ (-(0.95 : ℝ))) * 4 :=
                    mul_le_mul hq hInv
                      (inv_nonneg.mpr (le_of_lt (hPpos j)))
                      (by positivity : (0 : ℝ) ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)))
                  _ = 40 * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring
              · simp [hji]
                exact Real.rpow_nonneg hd.le _
        _ = (S.card : ℝ) * (40 * (d : ℝ) ^ (-(0.95 : ℝ))) := by simp
        _ = 40 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring
  let e : Fin t → ℝ := fun i =>
    -Real.log (A i) - ∑ j ∈ J, if j.val < i.val then q j (y i) / A j else 0
  have hdouble : (∑ j ∈ J, excludedFraction q S y x j) =
      ∑ i ∈ S, ∑ j ∈ J, if j.val < i.val then q j (y i) / A j else 0 := by
    unfold excludedFraction pendingMass
    simp_rw [Finset.sum_div, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hlinearEq : linearError q S y x = ∑ i ∈ S, e i := by
    unfold linearError
    rw [hdouble]
    simp only [e]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  have hbase (i : Fin t) :
      |-(Real.log (P i)) -
        (∑ j : Fin t, if j.val < i.val then q j (y i) / P j else 0)| ≤
          Kp * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    have hp := hprefix d t q h i (y i)
    have heq : -(Real.log (P i)) -
        (∑ j : Fin t, if j.val < i.val then q j (y i) / P j else 0) =
        -((∑ j : Fin t, if j.val < i.val then q j (y i) / P j else 0) +
          Real.log (P i)) := by ring
    rw [heq]
    rw [abs_neg]
    simpa [P] using hp
  have hEbound (i : Fin t) :
      |e i| ≤ (Kp + 225) * δ + 40 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    let B0 := -(Real.log (P i)) -
      (∑ j : Fin t, if j.val < i.val then q j (y i) / P j else 0)
    let L0 := Real.log (A i) - Real.log (P i)
    let O0 := ∑ j ∈ S, if j.val < i.val then q j (y i) / P j else 0
    let R0 := ∑ j ∈ J, if j.val < i.val then
      q j (y i) / P j - q j (y i) / A j else 0
    have hsplit :
        (∑ j : Fin t, if j.val < i.val then q j (y i) / P j else 0) =
          (∑ j ∈ J, if j.val < i.val then q j (y i) / P j else 0) + O0 := by
      calc
        _ = ∑ j ∈ Finset.univ, if j.val < i.val then q j (y i) / P j else 0 := by simp
        _ = (∑ j ∈ Finset.univ \ S,
              if j.val < i.val then q j (y i) / P j else 0) + O0 := by
                rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    have hR0 : R0 =
        (∑ j ∈ J, if j.val < i.val then q j (y i) / P j else 0) -
          (∑ j ∈ J, if j.val < i.val then q j (y i) / A j else 0) := by
      dsimp [R0]
      calc
        (∑ j ∈ J, if j.val < i.val then
            q j (y i) / P j - q j (y i) / A j else 0) =
          ∑ j ∈ J,
            ((if j.val < i.val then q j (y i) / P j else 0) -
              (if j.val < i.val then q j (y i) / A j else 0)) := by
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j.val < i.val <;> simp [hji]
        _ = _ := by rw [Finset.sum_sub_distrib]
    have hidentity : e i = B0 - L0 + O0 + R0 := by
      rw [hR0]
      dsimp [e, B0, L0]
      rw [hsplit]
      ring_nf
    have hbaseBound : |B0| ≤ Kp * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      simpa [B0] using hbase i
    have hlogBound : |L0| ≤ 5 * δ := by
      calc
        |Real.log (A i) - Real.log (P i)| ≤ 5 * |A i - P i| := hRatioAB i
        _ ≤ 5 * δ := mul_le_mul_of_nonneg_left (hABdiff i) (by norm_num)
    have hRBound : |R0| ≤ 220 * δ := by simpa [R0] using hDenChange i
    have hOBound : |O0| ≤ 40 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
      have hO := hOmit i
      dsimp [O0]
      rw [abs_of_nonneg hO.1]
      exact hO.2
    rw [hidentity]
    have htri : |B0 - L0 + O0 + R0| ≤ |B0| + |L0| + |O0| + |R0| := by
      calc
        |(B0 - L0 + O0) + R0| ≤ |B0 - L0 + O0| + |R0| := abs_add_le _ _
        _ ≤ |B0 - L0| + |O0| + |R0| := by
              have := abs_add_le (B0 - L0) O0
              linarith
        _ ≤ |B0| + |L0| + |O0| + |R0| := by
              have h := abs_sub_le B0 0 L0
              simp only [sub_zero, zero_sub, abs_neg] at h
              linarith
    have hbound := add_le_add (add_le_add (add_le_add hbaseBound hlogBound) hOBound) hRBound
    calc
      |B0 - L0 + O0 + R0| ≤ |B0| + |L0| + |O0| + |R0| := htri
      _ ≤ _ := by
        have hsmall := hbound
        have hpow := hdeltaQuarter
        have hO := hOBound
        dsimp [δ] at *
        nlinarith
  have hlinearBound :
      |linearError q S y x| ≤
        (Kp + 225) * (S.card : ℝ) * δ +
          40 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    rw [hlinearEq]
    calc
      |∑ i ∈ S, e i| ≤ ∑ i ∈ S, |e i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S,
          ((Kp + 225) * δ + 40 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hEbound i
      _ = (S.card : ℝ) *
          ((Kp + 225) * δ + 40 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) := by
            calc
              _ = ∑ i ∈ S, (1 : ℝ) *
                    ((Kp + 225) * δ + 40 * (S.card : ℝ) *
                      (d : ℝ) ^ (-(0.95 : ℝ))) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
              _ = (∑ i ∈ S, (1 : ℝ)) *
                    ((Kp + 225) * δ + 40 * (S.card : ℝ) *
                      (d : ℝ) ^ (-(0.95 : ℝ))) := by rw [Finset.sum_mul]
              _ = _ := by simp
      _ = (Kp + 225) * (S.card : ℝ) * δ +
          40 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring_nf
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hresult :
      (Kp + 225) * (S.card : ℝ) * δ +
          40 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
        (Kp + 300) * (S.card : ℝ) *
          (δ + (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) := by
    have hδ : 0 ≤ δ := by positivity
    have hp : 0 ≤ (d : ℝ) ^ (-(0.95 : ℝ)) := Real.rpow_nonneg hd.le _
    have hcδ : 0 ≤ (S.card : ℝ) * δ := mul_nonneg hcard hδ
    have hc₂p : 0 ≤ (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) :=
      mul_nonneg (sq_nonneg _) hp
    have hcoef₁ : Kp + 225 ≤ Kp + 300 := by linarith
    have hcoef₂ : 40 ≤ Kp + 300 := by linarith [hKp]
    calc
      (Kp + 225) * (S.card : ℝ) * δ +
          40 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
          (Kp + 300) * ((S.card : ℝ) * δ) +
            (Kp + 300) * ((S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ))) := by
              apply add_le_add
              · calc
                  (Kp + 225) * (S.card : ℝ) * δ =
                      (Kp + 225) * ((S.card : ℝ) * δ) := by ring
                  _ ≤ (Kp + 300) * ((S.card : ℝ) * δ) :=
                    mul_le_mul_of_nonneg_right hcoef₁ hcδ
              · calc
                  40 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) =
                      40 * ((S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ))) := by ring
                  _ ≤ (Kp + 300) * ((S.card : ℝ) ^ 2 *
                      (d : ℝ) ^ (-(0.95 : ℝ))) :=
                    mul_le_mul_of_nonneg_right hcoef₂ hc₂p
      _ = _ := by ring
  calc
    |linearError q S y x| ≤
        (Kp + 225) * (S.card : ℝ) * δ +
          40 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := hlinearBound
    _ ≤ (Kp + 300) * S.card *
        ((d : ℝ) ^ (-(0.1 : ℝ)) + S.card * (d : ℝ) ^ (-(0.95 : ℝ))) := by
          simpa [δ] using hresult

/-- TeX 03:717–720: each excluded fraction is small, and the sum of squares is small. -/
theorem quadratic_likelihood_remainder : ∃ K : ℝ, 1 ≤ K ∧
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      ∀ x, Good q x → Targets S y x →
        (∀ j ∈ Finset.univ \ S, 0 ≤ excludedFraction q S y x j ∧
          excludedFraction q S y x j ≤ 1 / 2) ∧
        quadraticError q S y x ≤ K * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  have hsmallPow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.925 : ℝ))) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.925 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.925 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hsmallCol : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ))) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(1 / 8 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (1 / 8 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  refine ⟨500, by norm_num, ?_⟩
  filter_upwards [hsmallPow.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
    hsmallCol.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
    eventually_ge_atTop 100] with d hdPow hdCol hd100
  intro t q hq S y hpos hsize x hx htargets
  classical
  let J : Finset (Fin t) := Finset.univ \ S
  have hd : 0 < (d : ℝ) := by positivity
  have hpow : (d : ℝ) ^ (-(0.925 : ℝ)) < 1 / 100 := by
    simpa only [Set.mem_Iio] using hdPow
  have hcolerr : (d : ℝ) ^ (-(1 / 8 : ℝ)) < 1 / 100 := by
    simpa only [Set.mem_Iio] using hdCol
  have htrackMono : ∀ b c : ℕ, b ≤ c → trackingError q x b ≤ trackingError q x c := by
    intro b c hbc
    have finiteSet (n : ℕ) :
        ({0} ∪ {r : ℝ | ∃ a : Fin t, ∃ k : Fin (t + 1), k.val ≤ n ∧
          r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
      have hrange : (Set.range (fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|)).Finite := Set.finite_range _
      apply Set.Finite.union
      · exact Set.finite_singleton 0
      · apply hrange.subset
        intro r hr
        rcases hr with ⟨a, k, hk, rfl⟩
        exact ⟨(a, k), rfl⟩
    have hbdd := (finiteSet c).bddAbove
    unfold trackingError
    apply csSup_le_csSup hbdd
    · exact ⟨0, Or.inl rfl⟩
    · intro r hr
      rcases hr with h0 | ⟨a, k, hk, rfl⟩
      · exact Or.inl h0
      · exact Or.inr ⟨a, k, le_trans hk hbc, rfl⟩
  have hvalid (i : Fin t) : PrefixValid x i.val := by
    rcases hx with ⟨hv, he, _⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hv.1 k (lt_trans hk i.isLt)
    · intro k l hk hl hkl
      exact hv.2 k l (lt_trans hk i.isLt) (lt_trans hl i.isLt) hkl
  have hstop (i : Fin t) : trackingError q x i.val ≤ 1 / 20 := by
    exact (htrackMono i.val t (Nat.le_of_lt i.isLt)).trans hx.2.1
  have hAvail (i : Fin t) : 1 / 5 ≤ availableMass q x i ∅ := by
    exact (free_mass_before_stop q hq x i (hvalid i) (hstop i)).2
  have hAvailPos (i : Fin t) : 0 < availableMass q x i ∅ :=
    lt_of_lt_of_le (by norm_num) (hAvail i)
  have hpend (j : Fin t) : 0 ≤ pendingMass q S y j ∧
      pendingMass q S y j ≤ 10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    unfold pendingMass
    constructor
    · apply Finset.sum_nonneg
      intro i hi
      exact hq.nonneg j (y i)
    · calc
        ∑ i ∈ S.filter (fun i => j.val < i.val), q j (y i) ≤
            ∑ i ∈ S.filter (fun i => j.val < i.val),
              10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
                apply Finset.sum_le_sum
                intro i hi
                exact hq.atom j (y i)
        _ = ((S.filter (fun i => j.val < i.val)).card : ℝ) *
              (10 * (d : ℝ) ^ (-(0.95 : ℝ))) := by simp
        _ ≤ (S.card : ℝ) * (10 * (d : ℝ) ^ (-(0.95 : ℝ))) := by
              apply mul_le_mul_of_nonneg_right
              · exact_mod_cast Finset.card_filter_le S (fun i => j.val < i.val)
              · positivity
        _ = 10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring
  have hE (j : Fin t) : 0 ≤ excludedFraction q S y x j ∧
      excludedFraction q S y x j ≤ 50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    rw [excludedFraction]
    constructor
    · exact div_nonneg (hpend j).1 (hAvailPos j).le
    · apply (div_le_iff₀ (hAvailPos j)).2
      have hM : 0 ≤ 50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by positivity
      calc
        pendingMass q S y j ≤ 10 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := (hpend j).2
        _ = (50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) * (1 / 5) := by ring
        _ ≤ (50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) *
              availableMass q x j ∅ := mul_le_mul_of_nonneg_left (hAvail j) hM
  have hmax : 50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
      50 * (d : ℝ) ^ (-(0.925 : ℝ)) := by
    calc
      50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
          50 * (d : ℝ) ^ (0.025 : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ)) := by
            gcongr
      _ = 50 * ((d : ℝ) ^ (0.025 : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) := by ring
      _ = 50 * (d : ℝ) ^ (-(0.925 : ℝ)) := by
            rw [← Real.rpow_add hd]
            norm_num
  have hEhalf (j : Fin t) : excludedFraction q S y x j ≤ 1 / 2 := by
    exact (hE j).2.trans (le_of_lt (by nlinarith [hmax, hpow]))
  have hprefix (i : Fin t) :
      (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤ 1 := by
    let b : Fin (t + 1) := ⟨i.val, by omega⟩
    have hcol := hq.column_prefix b (y i)
    have htime : (i.val : ℝ) / d ≤ 3 / 4 := by
      apply (div_le_iff₀ hd).2
      have hi : (i.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.le_of_lt i.isLt)
      nlinarith [hq.horizon]
    have hsum :
        (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
          (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have := (abs_le.mp hcol).2
      calc
        (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
            10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) + (i.val : ℝ) / d := by
              simpa [b] using this
        _ = (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
    nlinarith [hsum, htime, hcolerr]
  have hpendSum :
      (∑ j ∈ J, pendingMass q S y j) ≤ (S.card : ℝ) := by
    unfold pendingMass
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    calc
      ∑ i ∈ S, ∑ j ∈ J, (if j.val < i.val then q j (y i) else 0) ≤
          ∑ i ∈ S, ∑ j : Fin t, (if j.val < i.val then q j (y i) else 0) := by
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (by
              intro j hj _
              split_ifs
              · exact hq.nonneg j (y i)
              · exact le_rfl)
      _ ≤ ∑ i ∈ S, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hprefix i
      _ = (S.card : ℝ) := by simp
  have hEbyPend (j : Fin t) :
      excludedFraction q S y x j ≤ 5 * pendingMass q S y j := by
    rw [excludedFraction]
    apply (div_le_iff₀ (hAvailPos j)).2
    calc
      pendingMass q S y j = (5 * pendingMass q S y j) * (1 / 5) := by ring
      _ ≤ (5 * pendingMass q S y j) * availableMass q x j ∅ :=
        mul_le_mul_of_nonneg_left (hAvail j) (mul_nonneg (by norm_num) (hpend j).1)
  have hsumE : (∑ j ∈ J, excludedFraction q S y x j) ≤ 5 * (S.card : ℝ) := by
    calc
      ∑ j ∈ J, excludedFraction q S y x j ≤
          ∑ j ∈ J, 5 * pendingMass q S y j := by
            apply Finset.sum_le_sum
            intro j hj
            exact hEbyPend j
      _ = 5 * (∑ j ∈ J, pendingMass q S y j) := by rw [Finset.mul_sum]
      _ ≤ 5 * (S.card : ℝ) := mul_le_mul_of_nonneg_left hpendSum (by norm_num)
  have hsumSq : (∑ j ∈ J, (excludedFraction q S y x j) ^ 2) ≤
      250 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    calc
      ∑ j ∈ J, (excludedFraction q S y x j) ^ 2 ≤
          ∑ j ∈ J,
            (50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) * excludedFraction q S y x j := by
              apply Finset.sum_le_sum
              intro j hj
              simpa [pow_two] using mul_le_mul_of_nonneg_right (hE j).2 (hE j).1
      _ = (50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) *
            (∑ j ∈ J, excludedFraction q S y x j) := by rw [Finset.mul_sum]
      _ ≤ (50 * (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) *
            (5 * (S.card : ℝ)) := mul_le_mul_of_nonneg_left hsumE (by positivity)
      _ = 250 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring
  have hpoint (j : Fin t) (hj : j ∈ J) :
      |Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j| ≤
        2 * (excludedFraction q S y x j) ^ 2 := by
    let e := excludedFraction q S y x j
    have he0 : 0 ≤ e := (hE j).1
    have hehalf : e ≤ 1 / 2 := hEhalf j
    have hxpos : 0 < 1 - e := by linarith
    have hloghi := Real.log_le_sub_one_of_pos hxpos
    have hloglo' := Real.log_le_sub_one_of_pos (inv_pos.mpr hxpos)
    rw [Real.log_inv] at hloglo'
    have hloglo : 1 - (1 - e)⁻¹ ≤ Real.log (1 - e) := by linarith
    have hfracLower : -2 * e ^ 2 ≤ 1 - (1 - e)⁻¹ + e := by
      have hEq : 1 - (1 - e)⁻¹ + e = -(e ^ 2) / (1 - e) := by
        field_simp [hxpos.ne']
        ring
      rw [hEq]
      apply (le_div_iff₀ hxpos).2
      have hpoly : 0 ≤ e ^ 2 * (1 - 2 * e) :=
        mul_nonneg (sq_nonneg e) (by linarith)
      nlinarith
    have hlow : -2 * e ^ 2 ≤ Real.log (1 - e) + e := by linarith [hloglo, hfracLower]
    have hhi : Real.log (1 - e) + e ≤ 2 * e ^ 2 := by
      have : Real.log (1 - e) + e ≤ 0 := by linarith [hloghi]
      linarith [sq_nonneg e]
    have hlow' : -(2 * e ^ 2) ≤ Real.log (1 - e) + e := by nlinarith [hlow]
    simpa [e] using (abs_le.mpr ⟨hlow', hhi⟩)
  constructor
  · intro j hj
    exact ⟨(hE j).1, hEhalf j⟩
  · calc
      quadraticError q S y x =
          ∑ j ∈ J, |Real.log (1 - excludedFraction q S y x j) +
            excludedFraction q S y x j| := by rfl
      _ ≤ 2 * (∑ j ∈ J, (excludedFraction q S y x j) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro j hj
            exact hpoint j hj
      _ ≤ 500 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
            calc
              2 * (∑ j ∈ J, (excludedFraction q S y x j) ^ 2) ≤
                  2 * (250 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ))) :=
                    mul_le_mul_of_nonneg_left hsumSq (by norm_num)
              _ = 500 * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by ring

/-- Algebra and exponent slack only: consumes the two log-error estimates. -/
theorem likelihood_log_transfer (K₁ K₂ : ℝ) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂) :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
      ∀ x, Good q x → Targets S y x →
      |linearError q S y x| ≤ K₁ * S.card *
        ((d : ℝ) ^ (-(0.1 : ℝ)) + S.card * (d : ℝ) ^ (-(0.95 : ℝ))) →
      (∀ j ∈ Finset.univ \ S, 0 ≤ excludedFraction q S y x j ∧
        excludedFraction q S y x j ≤ 1 / 2) →
      quadraticError q S y x ≤ K₂ * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) →
        0 < likelihoodFactor q S y x ∧
        |Real.log (likelihoodFactor q S y x)| ≤ relativeError d / 4 * S.card := by
  have hzero1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.01 : ℝ))) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.01 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.01 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hzero2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.835 : ℝ))) atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.835 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.835 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hthreshold1 : 0 < (1 : ℝ) / (8 * (2 * K₁ + K₂)) := by positivity
  have hthreshold2 : 0 < (1 : ℝ) / (8 * (K₁ + K₂)) := by positivity
  filter_upwards [hzero1.eventually (Iio_mem_nhds hthreshold1),
    hzero2.eventually (Iio_mem_nhds hthreshold2),
    eventually_ge_atTop 100] with d hd1 hd2 hd100
  intro t q hq S y hpos hsize x hx htargets hlin hfrac hquad
  have hd : 0 < (d : ℝ) := by positivity
  have hpow1 : (d : ℝ) ^ (-(0.01 : ℝ)) < 1 / (8 * (2 * K₁ + K₂)) := by
    simpa only [Set.mem_Iio] using hd1
  have hpow2 : (d : ℝ) ^ (-(0.835 : ℝ)) < 1 / (8 * (K₁ + K₂)) := by
    simpa only [Set.mem_Iio] using hd2
  have htrackMono : ∀ b c : ℕ, b ≤ c → trackingError q x b ≤ trackingError q x c := by
    intro b c hbc
    classical
    have finiteSet (n : ℕ) :
        ({0} ∪ {r : ℝ | ∃ a : Fin t, ∃ k : Fin (t + 1), k.val ≤ n ∧
          r = |usedMass q x a k.val - (k.val : ℝ) / d|}).Finite := by
      have hrange : (Set.range (fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|)).Finite := Set.finite_range _
      apply Set.Finite.union
      · exact Set.finite_singleton 0
      · apply hrange.subset
        intro r hr
        rcases hr with ⟨a, k, hk, rfl⟩
        exact ⟨(a, k), rfl⟩
    have hbdd := (finiteSet c).bddAbove
    unfold trackingError
    apply csSup_le_csSup hbdd
    · exact ⟨0, Or.inl rfl⟩
    · intro r hr
      rcases hr with h0 | ⟨a, k, hk, rfl⟩
      · exact Or.inl h0
      · exact Or.inr ⟨a, k, le_trans hk hbc, rfl⟩
  have hvalid (i : Fin t) : PrefixValid x i.val := by
    rcases hx with ⟨hv, he, _⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hv.1 k (lt_trans hk i.isLt)
    · intro k l hk hl hkl
      exact hv.2 k l (lt_trans hk i.isLt) (lt_trans hl i.isLt) hkl
  have hstop (i : Fin t) : trackingError q x i.val ≤ 1 / 20 := by
    exact (htrackMono i.val t (Nat.le_of_lt i.isLt)).trans hx.2.1
  have hAvail (i : Fin t) : 0 < availableMass q x i ∅ := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5)
      (free_mass_before_stop q hq x i (hvalid i) (hstop i)).2
  have hfrac' (j : Fin t) (hj : j ∈ Finset.univ \ S) :
      0 < 1 - excludedFraction q S y x j := by
    have hjf := hfrac j hj
    linarith
  have hfactorpos : 0 < likelihoodFactor q S y x := by
    unfold likelihoodFactor
    apply mul_pos
    · exact Finset.prod_pos fun i hi => inv_pos.mpr (hAvail i)
    · exact Finset.prod_pos fun j hj => hfrac' j hj
  have hlog : Real.log (likelihoodFactor q S y x) =
      linearError q S y x +
        ∑ j ∈ Finset.univ \ S,
          (Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j) := by
    unfold likelihoodFactor linearError
    rw [Real.log_mul]
    · rw [Real.log_prod (fun i hi => inv_ne_zero (hAvail i).ne'),
        Real.log_prod (fun j hj => (hfrac' j hj).ne')]
      simp_rw [Real.log_inv]
      rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
      ring
    · exact Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (hAvail i).ne'
    · exact Finset.prod_ne_zero_iff.mpr fun j hj => (hfrac' j hj).ne'
  have hrem : |∑ j ∈ Finset.univ \ S,
      (Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j)| ≤
      quadraticError q S y x := by
    calc
      |∑ j ∈ Finset.univ \ S,
          (Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j)| ≤
          ∑ j ∈ Finset.univ \ S,
            |Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = quadraticError q S y x := by rfl
  have hlogbound : |Real.log (likelihoodFactor q S y x)| ≤
      K₁ * (S.card : ℝ) * ((d : ℝ) ^ (-(0.1 : ℝ)) +
          (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) +
        K₂ * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    rw [hlog]
    calc
      |linearError q S y x + ∑ j ∈ Finset.univ \ S,
          (Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j)| ≤
          |linearError q S y x| +
            |∑ j ∈ Finset.univ \ S,
              (Real.log (1 - excludedFraction q S y x j) + excludedFraction q S y x j)| :=
        abs_add_le _ _
      _ ≤ |linearError q S y x| + quadraticError q S y x :=
        add_le_add (le_refl _) hrem
      _ ≤ _ := add_le_add hlin hquad
  have hcard : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hsize' : (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) := hsize
  have hpowPos1 : 0 ≤ (d : ℝ) ^ (-(0.09 : ℝ)) := Real.rpow_nonneg hd.le _
  have hpowPos2 : 0 ≤ (d : ℝ) ^ (-(0.95 : ℝ)) := Real.rpow_nonneg hd.le _
  have hbound :
      K₁ * (S.card : ℝ) * ((d : ℝ) ^ (-(0.1 : ℝ)) +
          (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) +
        K₂ * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
      (1 / 4 : ℝ) * (d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ) := by
    have hpowA : (d : ℝ) ^ (-(0.1 : ℝ)) =
        (d : ℝ) ^ (-(0.09 : ℝ)) * (d : ℝ) ^ (-(0.01 : ℝ)) := by
      rw [← Real.rpow_add hd]
      norm_num
    have hpowB : (d : ℝ) ^ (-(0.95 : ℝ)) =
        (d : ℝ) ^ (-(0.09 : ℝ)) * (d : ℝ) ^ (-(0.86 : ℝ)) := by
      rw [← Real.rpow_add hd]
      norm_num
    have hpowC : (d : ℝ) ^ (-(0.86 : ℝ)) ≤ (d : ℝ) ^ (-(0.835 : ℝ)) := by
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ d by omega)) (by norm_num)
    have hpowC' : (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) ≤
        (d : ℝ) ^ (-(0.835 : ℝ)) := by
      calc
        (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) ≤
            (d : ℝ) ^ (0.025 : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) :=
          mul_le_mul_of_nonneg_right hsize' (Real.rpow_nonneg hd.le _)
        _ = (d : ℝ) ^ (-(0.835 : ℝ)) := by
          rw [← Real.rpow_add hd]
          norm_num
    have hcoef : K₁ * (d : ℝ) ^ (-(0.01 : ℝ)) +
        (K₁ + K₂) * (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) ≤ 1 / 4 := by
      have hA : K₁ * (d : ℝ) ^ (-(0.01 : ℝ)) ≤ 1 / 8 := by
        calc
          K₁ * (d : ℝ) ^ (-(0.01 : ℝ)) ≤
              (2 * K₁ + K₂) * (d : ℝ) ^ (-(0.01 : ℝ)) := by
                exact mul_le_mul_of_nonneg_right (by linarith [hK₁, hK₂])
                  (Real.rpow_nonneg hd.le _)
          _ ≤ 1 / 8 := by
            have hden : 0 < 2 * K₁ + K₂ := by linarith [hK₁, hK₂]
            have hmul := mul_lt_mul_of_pos_left hpow1 hden
            have hsimp : (2 * K₁ + K₂) * (1 / (8 * (2 * K₁ + K₂))) =
                (1 / 8 : ℝ) := by field_simp
            rw [hsimp] at hmul
            exact hmul.le
      have hB : (K₁ + K₂) * (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) ≤ 1 / 8 := by
        calc
          (K₁ + K₂) * (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) ≤
              (K₁ + K₂) * (d : ℝ) ^ (-(0.835 : ℝ)) :=
                (by
                  calc
                    (K₁ + K₂) * (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ)) =
                        (K₁ + K₂) * ((S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ))) := by ring
                    _ ≤ (K₁ + K₂) * (d : ℝ) ^ (-(0.835 : ℝ)) :=
                      mul_le_mul_of_nonneg_left hpowC' (by linarith [hK₁, hK₂]))
          _ ≤ 1 / 8 := by
            have hden : 0 < K₁ + K₂ := by linarith [hK₁, hK₂]
            have hmul := mul_lt_mul_of_pos_left hpow2 hden
            have hsimp : (K₁ + K₂) * (1 / (8 * (K₁ + K₂))) =
                (1 / 8 : ℝ) := by field_simp
            rw [hsimp] at hmul
            exact hmul.le
      linarith
    have hcoefnonneg : 0 ≤ (d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ) :=
      mul_nonneg hpowPos1 hcard
    have hfactorized :
        K₁ * (S.card : ℝ) * ((d : ℝ) ^ (-(0.1 : ℝ)) +
            (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) +
          K₂ * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) =
        ((d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ)) *
          (K₁ * (d : ℝ) ^ (-(0.01 : ℝ)) +
            (K₁ + K₂) * (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ))) := by
      rw [hpowA, hpowB]
      ring_nf
    calc
      _ = ((d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ)) *
          (K₁ * (d : ℝ) ^ (-(0.01 : ℝ)) +
            (K₁ + K₂) * (S.card : ℝ) * (d : ℝ) ^ (-(0.86 : ℝ))) := hfactorized
      _ ≤ ((d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ)) * (1 / 4) :=
        mul_le_mul_of_nonneg_left hcoef hcoefnonneg
      _ = (1 / 4 : ℝ) * (d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ) := by ring
  constructor
  · exact hfactorpos
  · calc
      |Real.log (likelihoodFactor q S y x)| ≤
          K₁ * (S.card : ℝ) * ((d : ℝ) ^ (-(0.1 : ℝ)) +
            (S.card : ℝ) * (d : ℝ) ^ (-(0.95 : ℝ))) +
          K₂ * (S.card : ℝ) ^ 2 * (d : ℝ) ^ (-(0.95 : ℝ)) := hlogbound
      _ ≤ (1 / 4 : ℝ) * (d : ℝ) ^ (-(0.09 : ℝ)) * (S.card : ℝ) := hbound
      _ = relativeError d / 4 * S.card := by
        rw [relativeError]
        ring_nf

open Classical in
private theorem lane_q_inj_comp_ordinary_drift_reserved_formula
    {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d)
    (j a : Fin t) (B : Finset (Fin d))
    (hv : PrefixValid x j.val) (he : trackingError q x j.val ≤ 1 / 20)
    (hm : 0 < availableMass q x j B) :
    ∑ z : Option (Fin d), ordinaryWeight q x j B z * z.elim 0 (q a) =
      (∑ y, if Free x j.val y ∧ y ∉ B then q j y * q a y else 0) /
        availableMass q x j B := by
  classical
  have hactive : PrefixValid x j.val ∧ trackingError q x j.val ≤ 1 / 20 ∧
      0 < availableMass q x j B := ⟨hv, he, hm⟩
  calc
    (∑ z : Option (Fin d), ordinaryWeight q x j B z * z.elim 0 (q a)) =
        ∑ y, if Free x j.val y ∧ y ∉ B then
          (q j y * q a y) / availableMass q x j B else 0 := by
            simp only [ordinaryWeight, if_pos hactive, Fintype.sum_option,
              Option.elim, mul_zero, zero_mul, ite_mul, zero_mul]
            simp only [zero_add]
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hfree : Free x j.val y ∧ y ∉ B <;> simp [hfree, div_eq_mul_inv,
              mul_assoc, mul_left_comm, mul_comm]
    _ = (∑ y, if Free x j.val y ∧ y ∉ B then q j y * q a y else 0) /
          availableMass q x j B := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hfree : Free x j.val y ∧ y ∉ B <;> simp [hfree]

open Classical in
private theorem lane_q_inj_comp_available_mass_singleton
    {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d)
    (j : Fin t) (z : Fin d) (hz : Free x j.val z) :
    availableMass q x j {z} = availableMass q x j ∅ - q j z := by
  classical
  unfold availableMass
  have hterm (w : Fin d) :
      (if Free x j.val w ∧ w ∉ ({z} : Finset (Fin d)) then q j w else 0) =
        (if Free x j.val w then q j w else 0) -
          (if w = z then q j w else 0) := by
    by_cases hw : Free x j.val w
    · by_cases hwz : w = z
      · subst w
        simp [hz]
      · simp [hw, hwz]
    · by_cases hwz : w = z
      · subst w
        exact (hw hz).elim
      · simp [hw, hwz]
  calc
    (∑ w, if Free x j.val w ∧ w ∉ ({z} : Finset (Fin d)) then q j w else 0) =
        ∑ w, ((if Free x j.val w then q j w else 0) -
          (if w = z then q j w else 0)) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hterm w
    _ = (∑ w, if Free x j.val w then q j w else 0) -
          ∑ w, if w = z then q j w else 0 := by rw [Finset.sum_sub_distrib]
    _ = availableMass q x j ∅ - q j z := by simp [availableMass]

open Classical in
private theorem lane_q_inj_comp_available_mass_singleton_no_effect
    {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d)
    (j : Fin t) (z : Fin d) (hz : ¬ Free x j.val z) :
    availableMass q x j {z} = availableMass q x j ∅ := by
  unfold availableMass
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hfree : Free x j.val w
  · have hwz : w ≠ z := by
      intro heq
      apply hz
      simpa [heq] using hfree
    simp [hfree, hwz]
  · simp [hfree]

open Classical in
private theorem lane_q_inj_comp_weighted_mass_singleton
    {d t : ℕ} (q : Fin t → Fin d → ℝ) (x : Path t d)
    (j a : Fin t) (z : Fin d) (hz : Free x j.val z) :
    (∑ w, if Free x j.val w ∧ w ≠ z then q j w * q a w else 0) =
      (∑ w, if Free x j.val w then q j w * q a w else 0) -
        q j z * q a z := by
  classical
  have hterm (w : Fin d) :
      (if Free x j.val w ∧ w ≠ z then q j w * q a w else 0) =
        (if Free x j.val w then q j w * q a w else 0) -
          (if w = z then q j w * q a w else 0) := by
    by_cases hfree : Free x j.val w
    · by_cases hwz : w = z
      · subst w
        simp [hz]
      · simp [hfree, hwz]
    · by_cases hwz : w = z
      · subst w
        exact (hfree hz).elim
      · simp [hfree, hwz]
  calc
    (∑ w, if Free x j.val w ∧ w ≠ z then q j w * q a w else 0) =
        ∑ w, ((if Free x j.val w then q j w * q a w else 0) -
          (if w = z then q j w * q a w else 0)) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hterm w
    _ = (∑ w, if Free x j.val w then q j w * q a w else 0) -
          ∑ w, if w = z then q j w * q a w else 0 := by
            rw [Finset.sum_sub_distrib]
    _ = _ := by simp

/-- TeX 03:727–732: one reservation and one forced draw have only atom-scale cumulative drift cost. -/
theorem singleton_forcing_drift_stability :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ), OrderedInput d t q →
      ∀ i y, 0 < q i (y i) → ∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
      |∑ j : Fin t, if j.val < b.val then
        forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| ≤
        1000 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  have hdecay95 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.95 : ℝ)))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.95 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.95 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hdecay125 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ)))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(1 / 8 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (1 / 8 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [
    hdecay95.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
    hdecay125.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_ge_atTop 100] with d h95 h125 hd100
  intro t q h i y htarget x a b hrun
  classical
  let M : ℝ := 10 * (d : ℝ) ^ (-(0.95 : ℝ))
  let A : Fin t → ℝ := fun j => availableMass q x j ∅
  let N : Fin t → ℝ := fun j =>
    ∑ z, if Free x j.val z then q a z * q j z else 0
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 100) h.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hMsmall : M ≤ 1 / 10 := by
    dsimp [M]
    nlinarith [h95]
  have hcolerr : 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 5 / 4 := by
    nlinarith [h125]
  rcases hrun.1 with ⟨hvalidAll, hinjAll⟩
  have hvalid (j : Fin t) (hjb : j.val < b.val) : PrefixValid x j.val := by
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hvalidAll k (lt_trans hk hjb)
    · intro k l hk hl hkl
      exact hinjAll k l (lt_trans hk hjb) (lt_trans hl hjb) hkl
  have hstop (j : Fin t) (hjb : j.val < b.val) :
      trackingError q x j.val ≤ 1 / 20 := hrun.2 j hjb
  have hfreeMass (j : Fin t) (hjb : j.val < b.val) :
      availableMass q x j ∅ = 1 - usedMass q x j j.val ∧
        1 / 5 ≤ availableMass q x j ∅ :=
    free_mass_before_stop q h x j (hvalid j hjb) (hstop j hjb)
  have hprefixMass :
      (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤ 2 := by
    let ib : Fin (t + 1) := ⟨i.val, by omega⟩
    have hcol := h.column_prefix ib (y i)
    have hratio : (i.val : ℝ) / d ≤ 3 / 4 := by
      apply (div_le_iff₀ hd).2
      have hi : (i.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast (Nat.le_of_lt i.isLt)
      nlinarith [h.horizon]
    have hsum :
        (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
          (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
      have h := (abs_le.mp hcol).2
      calc
        (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
            10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) + (i.val : ℝ) / d := by
              simpa [ib] using h
        _ = (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
    calc
      (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) ≤
          (i.val : ℝ) / d + 10 * (d : ℝ) ^ (-(1 / 8 : ℝ)) := hsum
      _ ≤ 3 / 4 + 5 / 4 := add_le_add hratio hcolerr
      _ = 2 := by norm_num
  have hNnonneg (j : Fin t) : 0 ≤ N j := by
    dsimp [N]
    apply Finset.sum_nonneg
    intro z hz
    split_ifs with hfree
    · exact mul_nonneg (h.nonneg a z) (h.nonneg j z)
    · exact le_rfl
  have hNupper (j : Fin t) :
      N j ≤ M * availableMass q x j ∅ := by
    calc
      N j ≤ ∑ z, if Free x j.val z then M * q j z else 0 := by
        dsimp [N]
        apply Finset.sum_le_sum
        intro z hz
        by_cases hf : Free x j.val z
        · simp [hf]
          exact mul_le_mul_of_nonneg_right (h.atom a z) (h.nonneg j z)
        · simp [hf]
      _ = M * (∑ z, if Free x j.val z then q j z else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hf : Free x j.val z <;> simp [hf, mul_assoc]
      _ = M * availableMass q x j ∅ := by simp [availableMass]
  have hordinaryFormula (j : Fin t) (hjb : j.val < b.val) :
      stepDrift q x a j = N j / availableMass q x j ∅ := by
    have hseq := sequential_drift_increment q h x a j
      (hvalid j hjb) (hstop j hjb)
    rw [← (hfreeMass j hjb).1] at hseq
    simpa [N, mul_comm] using hseq.1
  have hordinaryRange (j : Fin t) (hjb : j.val < b.val) :
      0 ≤ stepDrift q x a j ∧ stepDrift q x a j ≤ M := by
    rw [hordinaryFormula j hjb]
    constructor
    · exact div_nonneg (hNnonneg j) (le_of_lt
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5) (hfreeMass j hjb).2))
    · apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5)
        (hfreeMass j hjb).2)).2
      calc
        N j ≤ M * availableMass q x j ∅ := hNupper j
        _ = M * availableMass q x j ∅ := rfl
  have hforceAt (hbi : i.val < b.val) :
      forcedStepDrift q {i} y x a i =
        if Free x i.val (y i) then q a (y i) else 0 := by
    have hv := hvalid i hbi
    have he := hstop i hbi
    have he' : trackingError q x i.val ≤ (20 : ℝ)⁻¹ := by
      nlinarith [he]
    have hiS : i ∈ ({i} : Finset (Fin t)) := by simp
    classical
    unfold forcedStepDrift
    simp [forcingStepWeight, hiS, hv, he', Fintype.sum_option, Option.elim]
  have hstepBound (j : Fin t) (hjb : j.val < b.val) :
      |forcedStepDrift q {i} y x a j - stepDrift q x a j| ≤
        if j.val < i.val then 100 * (d : ℝ) ^ (-(0.95 : ℝ)) * q j (y i)
        else if j = i then M else 0 := by
    by_cases hji : j.val < i.val
    · by_cases hfree : Free x j.val (y i)
      · have hmassRes := lane_q_inj_comp_available_mass_singleton
          q x j (y i) hfree
        have hr : 0 ≤ q j (y i) := h.nonneg j (y i)
        have hrle : q j (y i) ≤ M := h.atom j (y i)
        have hresLower :
            1 / 10 ≤ availableMass q x j {y i} := by
          rw [hmassRes]
          have hbase := (hfreeMass j hjb).2
          dsimp [M] at hMsmall hrle ⊢
          nlinarith [hrle]
        have hresPos : 0 < availableMass q x j {y i} :=
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 10) hresLower
        have hOrd := hordinaryFormula j hjb
        have hforced :
            forcedStepDrift q {i} y x a j =
              (∑ z, if Free x j.val z ∧ z ∉ ({y i} : Finset (Fin d)) then
                q j z * q a z else 0) / availableMass q x j {y i} := by
          have hjS : j ∉ ({i} : Finset (Fin t)) := by
            simp
            exact ne_of_lt hji
          have hpending : pendingLabels {i} y j = {y i} := by
            unfold pendingLabels
            have hfilter :
                ({i} : Finset (Fin t)).filter (fun k => j.val < k.val) = {i} := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · rintro ⟨hk, _⟩
                exact hk
              · intro hk
                subst k
                exact ⟨rfl, hji⟩
            rw [hfilter]
            exact Finset.image_singleton y i
          unfold forcedStepDrift
          simp only [forcingStepWeight, if_neg hjS]
          rw [hpending]
          exact lane_q_inj_comp_ordinary_drift_reserved_formula
            q x j a {y i} (hvalid j hjb) (hstop j hjb) hresPos
        have hnum :
            (∑ z, if Free x j.val z ∧ z ∉ ({y i} : Finset (Fin d)) then
              q j z * q a z else 0) = N j - q j (y i) * q a (y i) := by
          simpa [N, mul_comm, mul_left_comm, mul_assoc] using
            lane_q_inj_comp_weighted_mass_singleton q x j a (y i) hfree
        rw [hnum, hmassRes] at hforced
        have hApos : 0 < availableMass q x j ∅ :=
          lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5) (hfreeMass j hjb).2
        have hdenPos : 0 < availableMass q x j ∅ - q j (y i) := by
          rw [← hmassRes]
          exact hresPos
        have hdiff :
            forcedStepDrift q {i} y x a j - stepDrift q x a j =
              q j (y i) * (stepDrift q x a j - q a (y i)) /
                (availableMass q x j ∅ - q j (y i)) := by
          rw [hforced, hOrd]
          field_simp [hApos.ne', hdenPos.ne'] <;> ring
        have hqa0 : 0 ≤ q a (y i) := h.nonneg a (y i)
        have hqaM : q a (y i) ≤ M := h.atom a (y i)
        have hdiffRange :
            |stepDrift q x a j - q a (y i)| ≤ M := by
          apply abs_le.mpr
          constructor <;> linarith [(hordinaryRange j hjb).1,
            (hordinaryRange j hjb).2, hqa0, hqaM]
        have hfactor : 1 ≤
            10 * (availableMass q x j ∅ - q j (y i)) := by
          rw [← hmassRes]
          linarith [hresLower]
        rw [hdiff, abs_div, abs_mul, abs_of_nonneg hr, abs_of_pos hdenPos]
        simp only [if_pos hji]
        have hbase :
            q j (y i) * |stepDrift q x a j - q a (y i)| ≤
              q j (y i) * M :=
          mul_le_mul_of_nonneg_left hdiffRange hr
        have hscale :
            q j (y i) * M ≤
              10 * q j (y i) * M *
                (availableMass q x j ∅ - q j (y i)) := by
          have hnonneg : 0 ≤ q j (y i) * M := mul_nonneg hr hMnonneg
          calc
            q j (y i) * M = 1 * (q j (y i) * M) := by ring
            _ ≤ (10 * (availableMass q x j ∅ - q j (y i))) *
                (q j (y i) * M) :=
              mul_le_mul_of_nonneg_right hfactor hnonneg
            _ = 10 * q j (y i) * M *
                (availableMass q x j ∅ - q j (y i)) := by ring
        have hquot :
            q j (y i) * |stepDrift q x a j - q a (y i)| /
                (availableMass q x j ∅ - q j (y i)) ≤ 10 * q j (y i) * M :=
          (div_le_iff₀ hdenPos).2 (hbase.trans hscale)
        have hcoeff :
            10 * q j (y i) * M =
              100 * (d : ℝ) ^ (-(0.95 : ℝ)) * q j (y i) := by
          dsimp [M]
          ring
        simpa [hcoeff] using hquot
      · have hmassSame := lane_q_inj_comp_available_mass_singleton_no_effect
          q x j (y i) hfree
        have hOrd := hordinaryFormula j hjb
        have hforced :
            forcedStepDrift q {i} y x a j =
              (∑ z, if Free x j.val z ∧ z ∉ ({y i} : Finset (Fin d)) then
                q j z * q a z else 0) / availableMass q x j {y i} := by
          have hjS : j ∉ ({i} : Finset (Fin t)) := by
            simp
            exact ne_of_lt hji
          have hpending : pendingLabels {i} y j = {y i} := by
            unfold pendingLabels
            have hfilter :
                ({i} : Finset (Fin t)).filter (fun k => j.val < k.val) = {i} := by
              ext k
              simp only [Finset.mem_filter, Finset.mem_singleton]
              constructor
              · rintro ⟨hk, _⟩
                exact hk
              · intro hk
                subst k
                exact ⟨rfl, hji⟩
            rw [hfilter]
            exact Finset.image_singleton y i
          unfold forcedStepDrift
          simp only [forcingStepWeight, if_neg hjS]
          rw [hpending]
          exact lane_q_inj_comp_ordinary_drift_reserved_formula
            q x j a {y i} (hvalid j hjb) (hstop j hjb)
            (by
              rw [hmassSame]
              exact (lt_of_lt_of_le
                (by norm_num : (0 : ℝ) < 1 / 5) ((hfreeMass j hjb).2)))
        have hnum :
            (∑ z, if Free x j.val z ∧ z ∉ ({y i} : Finset (Fin d)) then
              q j z * q a z else 0) = N j := by
          dsimp [N]
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hzfree : Free x j.val z
          · have hzneq : z ≠ y i := by
              intro hEq
              apply hfree
              simpa [hEq] using hzfree
            simp [hzfree, hzneq]
            ring
          · simp [hzfree]
        rw [hnum, hmassSame] at hforced
        rw [hforced, hOrd]
        have hcoeff : 0 ≤ 100 * (d : ℝ) ^ (-(0.95 : ℝ)) := by positivity
        simp only [sub_self, abs_zero, if_pos hji]
        exact mul_nonneg hcoeff (h.nonneg j (y i))
    · by_cases hEq : j = i
      · subst j
        have hforced := hforceAt hjb
        have hqa0 : 0 ≤ q a (y i) := h.nonneg a (y i)
        have hqaM : q a (y i) ≤ M := h.atom a (y i)
        have hforcedRange :
            0 ≤ forcedStepDrift q {i} y x a i ∧
              forcedStepDrift q {i} y x a i ≤ M := by
          rw [hforced]
          by_cases hf : Free x i.val (y i) <;> simp [hf, hqa0, hqaM, hMnonneg]
        have hordinary := hordinaryRange i hjb
        have habs :
            |forcedStepDrift q {i} y x a i - stepDrift q x a i| ≤ M :=
          abs_le.mpr ⟨by linarith [hforcedRange.1, hordinary.2],
            by linarith [hforcedRange.2, hordinary.1]⟩
        simpa [hji] using habs
      · have hgt : i.val < j.val := by omega
        have hjS : j ∉ ({i} : Finset (Fin t)) := by
          simp
          exact hEq
        have hpending : pendingLabels {i} y j = ∅ := by
          unfold pendingLabels
          have hfilter :
              ({i} : Finset (Fin t)).filter (fun k => j.val < k.val) = ∅ := by
            ext k
            simp [Finset.mem_filter, hji]
            omega
          rw [hfilter]
          simp
        have hforceEq :
            forcedStepDrift q {i} y x a j = stepDrift q x a j := by
          unfold forcedStepDrift stepDrift
          apply Finset.sum_congr rfl
          intro z hz
          simp [forcingStepWeight, hjS, hpending]
        simp only [if_neg hji, if_neg hEq]
        rw [hforceEq]
        simp
  have hsumBound :
      (∑ j : Fin t, if j.val < b.val then
        if j.val < i.val then
          100 * (d : ℝ) ^ (-(0.95 : ℝ)) * q j (y i)
        else if j = i then M else 0 else 0) ≤
        100 * (d : ℝ) ^ (-(0.95 : ℝ)) *
            (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) + M := by
    calc
      _ ≤ ∑ j : Fin t,
          ((if j.val < i.val then
              100 * (d : ℝ) ^ (-(0.95 : ℝ)) * q j (y i) else 0) +
            (if j = i then M else 0)) := by
              apply Finset.sum_le_sum
              intro j hj
              by_cases hjb : j.val < b.val
              · simp only [if_pos hjb]
                by_cases hji : j.val < i.val
                · have hne : j ≠ i := by
                    intro heq
                    subst j
                    omega
                  simp [hji, hne]
                · by_cases hEq : j = i <;> simp [hji, hEq]
              · simp only [if_neg hjb]
                by_cases hji : j.val < i.val
                · have hq0 := h.nonneg j (y i)
                  have hc0 : 0 ≤ 100 * (d : ℝ) ^ (-(0.95 : ℝ)) := by positivity
                  simp [hji]
                  exact add_nonneg (mul_nonneg hc0 hq0) (by positivity)
                · by_cases hEq : j = i
                  · simp [hji, hEq]
                    exact hMnonneg
                  · simp [hji, hEq]
      _ = (∑ j : Fin t,
            if j.val < i.val then
              100 * (d : ℝ) ^ (-(0.95 : ℝ)) * q j (y i) else 0) +
            ∑ j : Fin t, if j = i then M else 0 := by
              rw [Finset.sum_add_distrib]
      _ = 100 * (d : ℝ) ^ (-(0.95 : ℝ)) *
            (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) + M := by
              calc
                _ = (∑ j : Fin t,
                      100 * (d : ℝ) ^ (-(0.95 : ℝ)) *
                        (if j.val < i.val then q j (y i) else 0)) +
                      ∑ j : Fin t, if j = i then M else 0 := by
                        congr 1
                        · apply Finset.sum_congr rfl
                          intro j hj
                          by_cases hji : j.val < i.val <;> simp [hji]
                _ = 100 * (d : ℝ) ^ (-(0.95 : ℝ)) *
                      (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) + M := by
                        rw [Finset.mul_sum]
                        simp
  have hsumAbs :
      |∑ j : Fin t, if j.val < b.val then
        forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| ≤
        ∑ j : Fin t, if j.val < b.val then
          |forcedStepDrift q {i} y x a j - stepDrift q x a j| else 0 := by
    calc
      _ ≤ ∑ j : Fin t,
          |if j.val < b.val then
            forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjb : j.val < b.val <;> simp [hjb]
  calc
    |∑ j : Fin t, if j.val < b.val then
        forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| ≤
        ∑ j : Fin t, if j.val < b.val then
          |forcedStepDrift q {i} y x a j - stepDrift q x a j| else 0 := hsumAbs
    _ ≤ ∑ j : Fin t, if j.val < b.val then
          if j.val < i.val then
            100 * (d : ℝ) ^ (-(0.95 : ℝ)) * q j (y i)
          else if j = i then M else 0 else 0 := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases hjb : j.val < b.val
            · simp only [if_pos hjb]
              exact hstepBound j hjb
            · simp [hjb]
    _ ≤ 100 * (d : ℝ) ^ (-(0.95 : ℝ)) *
          (∑ j : Fin t, if j.val < i.val then q j (y i) else 0) + M := hsumBound
    _ ≤ 100 * (d : ℝ) ^ (-(0.95 : ℝ)) * 2 + M := by
          have hcoef : 0 ≤ 100 * (d : ℝ) ^ (-(0.95 : ℝ)) := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hprefixMass hcoef) le_rfl
    _ ≤ 1000 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
          dsimp [M]
          nlinarith [Real.rpow_nonneg hd.le (-(0.95 : ℝ))]

/-- Concentration is under the forcing law, independent of the target's atom size. -/
theorem forced_martingale_concentration :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      ∀ i y, 0 < q i (y i) → 1 - failureBound d ≤
        (forcingLaw q h.nonneg h.row_sum {i} y).pr (ForcedMartingaleGood q {i} y) := by
  have huTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (0.1 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0.1 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hgainTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (0.55 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0.55 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hpolyTail : Tendsto
      (fun n : ℕ => 2 * ((n : ℝ) ^ (0.1 : ℝ)) ^ (20 : ℕ) *
        Real.exp (-((n : ℝ) ^ (0.1 : ℝ)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (20 : ℝ) (1 : ℝ) (by norm_num : (0 : ℝ) < 1)).comp huTop
    simpa [Function.comp_def, mul_comm, mul_assoc] using h.const_mul (2 : ℝ)
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1
    (hpolyTail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨nGain, hnGain⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hgainTop (1200 : ℝ))
  filter_upwards [eventually_ge_atTop nTail, eventually_ge_atTop nGain]
    with d hdTail hdGain
  intro t q h i y htarget
  classical
  by_cases ht0 : t = 0
  · subst t
    exact False.elim (Fin.elim0 i)
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 100) h.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have htNat : 0 < t := Nat.pos_of_ne_zero ht0
  have ht : (t : ℝ) ≤ 3 * (d : ℝ) / 4 := h.horizon
  have hd100real : (100 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h.dimension
  have htLe : (t : ℝ) ≤ (d : ℝ) := by nlinarith [ht, hd100real]
  have ht1Le : (t : ℝ) + 1 ≤ (d : ℝ) := by nlinarith [ht, hd100real]
  have ht1Cast : ((t + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by simpa using ht1Le
  have huPos : 0 < (d : ℝ) ^ (0.1 : ℝ) := Real.rpow_pos_of_pos hd _
  have hpolySmall :
      2 * ((d : ℝ) ^ (0.1 : ℝ)) ^ (20 : ℕ) *
        Real.exp (-((d : ℝ) ^ (0.1 : ℝ))) < 1 := hnTail d hdTail
  have hgain : 1200 ≤ (d : ℝ) ^ (0.55 : ℝ) := hnGain d hdGain
  have hpowFactor : (d : ℝ) ^ (0.65 : ℝ) =
      (d : ℝ) ^ (0.1 : ℝ) * (d : ℝ) ^ (0.55 : ℝ) := by
    rw [← Real.rpow_add hd]
    norm_num
  have hdom : 2 * (d : ℝ) ^ (0.1 : ℝ) ≤
      (1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hgain
      (Real.rpow_nonneg hd.le (0.1 : ℝ))
    rw [hpowFactor]
    nlinarith [hmul]
  have hpow20 : ((d : ℝ) ^ (0.1 : ℝ)) ^ (20 : ℕ) = (d : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
  have hfinalTail :
      2 * (d : ℝ) ^ 2 *
        Real.exp (-2 * (d : ℝ) ^ (0.1 : ℝ)) ≤ failureBound d := by
    rw [failureBound]
    rw [← hpow20]
    have hExpSquare :
        Real.exp (-2 * (d : ℝ) ^ (0.1 : ℝ)) =
          Real.exp (-((d : ℝ) ^ (0.1 : ℝ))) *
            Real.exp (-((d : ℝ) ^ (0.1 : ℝ))) := by
      calc
        Real.exp (-2 * (d : ℝ) ^ (0.1 : ℝ)) =
            Real.exp ((-(d : ℝ) ^ (0.1 : ℝ)) + (-(d : ℝ) ^ (0.1 : ℝ))) := by
              congr 1
              ring
        _ = _ := Real.exp_add _ _
    have hsplit :
        2 * ((d : ℝ) ^ (0.1 : ℝ)) ^ (20 : ℕ) *
          Real.exp (-2 * (d : ℝ) ^ (0.1 : ℝ)) =
        (2 * ((d : ℝ) ^ (0.1 : ℝ)) ^ (20 : ℕ) *
          Real.exp (-((d : ℝ) ^ (0.1 : ℝ)))) *
          Real.exp (-((d : ℝ) ^ (0.1 : ℝ))) := by
      rw [hExpSquare]
      ring
    rw [hsplit]
    calc
      (2 * ((d : ℝ) ^ (0.1 : ℝ)) ^ (20 : ℕ) *
          Real.exp (-((d : ℝ) ^ (0.1 : ℝ)))) *
          Real.exp (-((d : ℝ) ^ (0.1 : ℝ)) ) ≤
        1 * Real.exp (-((d : ℝ) ^ (0.1 : ℝ))) :=
          mul_le_mul_of_nonneg_right hpolySmall.le (Real.exp_nonneg _)
      _ = _ := by ring
  let P : FinProb (Path t d) := forcingLaw q h.nonneg h.row_sum {i} y
  let K : ∀ n, (Fin n → Option (Fin d)) → FinProb (Option (Fin d)) :=
    forcingKernelFamily q h.nonneg {i} y
  have hPweight (x : Path t d) :
      P.w x = (triangularLaw K t).w x := by
    change forcingWeight q {i} y x = _
    exact forcingWeight_eq_triangularLaw_weight q h.nonneg {i} y x
  have hPexpect (G : Path t d → ℝ) :
      P.expect G = (triangularLaw K t).expect G := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro x hx
    rw [hPweight x]
  let hbad : Fin t → Fin (t + 1) → Path t d → Prop := fun a b x =>
    (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ)) <
      |forcedMartingalePart q {i} y x a b.val|
  have hpairTail (a : Fin t) (b : Fin (t + 1)) :
      P.pr (hbad a b) ≤ 2 * Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) := by
    let M : ℝ := 10 * (d : ℝ) ^ (-(0.95 : ℝ))
    let ε : ℝ := (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ))
    let lo : Fin t → ℝ := fun _ => -M
    let hi : Fin t → ℝ := fun _ => M
    let width : ℝ := ∑ r : Fin t, (hi r - lo r) ^ 2
    let Δ : Fin t → Path t d → ℝ := fun r x =>
      if r.val < b.val then
        (x r).elim 0 (q a) - forcedStepDrift q {i} y x a r else 0
    let H : Fin (t + 1) → Type := fun m => Fin m.val → Option (Fin d)
    let history : ∀ m : Fin (t + 1), Path t d → H m :=
      fun m x => takePrefix (Nat.le_of_lt_succ m.isLt) x
    let project : ∀ r : Fin t, H r.succ → H r.castSucc :=
      fun r g => takePrefix (Nat.le_succ r.val) g
    have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
    have hεpos : 0 < ε := by dsimp [ε]; positivity
    have hfiltration (r : Fin t) (x : Path t d) :
        history r.castSucc x = project r (history r.succ x) := by
      funext k
      simp [history, project, takePrefix]
    have hAdapted :
        ∀ (m : ℕ) (hm : m ≤ t) (r : Fin t), r.val < m →
          ∀ x x', history ⟨m, Nat.lt_succ_of_le hm⟩ x =
            history ⟨m, Nat.lt_succ_of_le hm⟩ x' → Δ r x = Δ r x' := by
      intro m hm r hr x x' hhist
      have hcoord (k : Fin t) (hkm : k.val < m) : x k = x' k := by
        have hh := congrFun hhist ⟨k.val, hkm⟩
        simpa [history, takePrefix] using hh
      have hri : x r = x' r := hcoord r hr
      have hprefix :
          takePrefix (Nat.le_of_lt r.isLt) x =
            takePrefix (Nat.le_of_lt r.isLt) x' := by
        funext k
        have hkm : k.val < m := by omega
        have hkt : k.val < t := by omega
        have hh := hcoord ⟨k.val, hkt⟩ hkm
        simpa [takePrefix] using hh
      have hDrift : forcedStepDrift q {i} y x a r =
          forcedStepDrift q {i} y x' a r := by
        rw [← forcingKernel_expect_step q h.nonneg {i} y x r a,
          ← forcingKernel_expect_step q h.nonneg {i} y x' r a]
        rw [hprefix]
      by_cases hmask : r.val < b.val <;> simp [Δ, hmask, hri, hDrift]
    have hObsRange (z : Option (Fin d)) :
        0 ≤ z.elim 0 (q a) ∧ z.elim 0 (q a) ≤ M := by
      cases z with
      | none => simp [M, hMnonneg]
      | some z =>
          constructor
          · exact h.nonneg a z
          · exact h.atom a z
    have hForceRange (r : Fin t) (x : Path t d) :
        0 ≤ forcedStepDrift q {i} y x a r ∧
          forcedStepDrift q {i} y x a r ≤ M := by
      let R := forcingKernel q h.nonneg {i} y r
        (takePrefix (Nat.le_of_lt r.isLt) x)
      have hlow := FinProb.expect_mono R (fun z => (hObsRange z).1)
      have hhigh := FinProb.expect_mono R (fun z => (hObsRange z).2)
      have hstep := forcingKernel_expect_step q h.nonneg {i} y x r a
      constructor
      · calc
          0 = R.expect (fun _ => 0) := by simp [R, FinProb.expect_const]
          _ ≤ R.expect (fun z => z.elim 0 (q a)) := hlow
          _ = forcedStepDrift q {i} y x a r := hstep
      · calc
          forcedStepDrift q {i} y x a r =
              R.expect (fun z => z.elim 0 (q a)) := hstep.symm
          _ ≤ R.expect (fun _ => M) := hhigh
          _ = M := by simp [R, FinProb.expect_const]
    have hBound : ∀ r x, lo r ≤ Δ r x ∧ Δ r x ≤ hi r := by
      intro r x
      by_cases hmask : r.val < b.val
      · have hobs := hObsRange (x r)
        have hdrift := hForceRange r x
        simp [lo, hi, Δ, hmask]
        constructor <;> linarith [hobs.1, hobs.2, hdrift.1, hdrift.2]
      · simp [lo, hi, Δ, hmask, hMnonneg]
    have hwidth : 0 < width := by
      have hwidthEq : width = (t : ℝ) * (2 * M) ^ 2 := by
        have hterm (r : Fin t) : (hi r - lo r) ^ 2 = (2 * M) ^ 2 := by
          dsimp [hi, lo]
          ring
        change (∑ r : Fin t, (hi r - lo r) ^ 2) = _
        calc
          _ = ∑ r : Fin t, (2 * M) ^ 2 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hterm r
          _ = _ := by simp
      rw [hwidthEq]
      positivity
    have hWidthUpper :
        width ≤ 300 * (d : ℝ) ^ (-(0.9 : ℝ)) := by
      have hpowSq : ((d : ℝ) ^ (-(0.95 : ℝ))) ^ 2 =
          (d : ℝ) ^ (-(1.9 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
        norm_num
      have hWformula : width = (t : ℝ) * (2 * M) ^ 2 := by
        have hterm (r : Fin t) : (hi r - lo r) ^ 2 = (2 * M) ^ 2 := by
          dsimp [hi, lo]
          ring
        change (∑ r : Fin t, (hi r - lo r) ^ 2) = _
        calc
          _ = ∑ r : Fin t, (2 * M) ^ 2 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hterm r
          _ = _ := by simp
      rw [hWformula]
      calc
        (t : ℝ) * (2 * M) ^ 2 =
            (t : ℝ) * (400 * (d : ℝ) ^ (-(1.9 : ℝ))) := by
              dsimp [M]
              rw [show (2 * (10 * (d : ℝ) ^ (-(0.95 : ℝ))) ) ^ 2 =
                400 * ((d : ℝ) ^ (-(0.95 : ℝ))) ^ 2 by ring, hpowSq]
        _ ≤ (3 * (d : ℝ) / 4) * (400 * (d : ℝ) ^ (-(1.9 : ℝ))) :=
          mul_le_mul_of_nonneg_right h.horizon (by positivity)
        _ = 300 * (d : ℝ) ^ (-(0.9 : ℝ)) := by
              calc
                _ = 300 * ((d : ℝ) * (d : ℝ) ^ (-(1.9 : ℝ))) := by ring
                _ = _ := by
                  have hmul : (d : ℝ) * (d : ℝ) ^ (-(1.9 : ℝ)) =
                      (d : ℝ) ^ (-(0.9 : ℝ)) := by
                    calc
                      (d : ℝ) * (d : ℝ) ^ (-(1.9 : ℝ)) =
                          (d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-(1.9 : ℝ)) := by
                            exact congrArg (fun z : ℝ => z * (d : ℝ) ^ (-(1.9 : ℝ)))
                              (Real.rpow_one (d : ℝ)).symm
                      _ = (d : ℝ) ^ ((1 : ℝ) + -(1.9 : ℝ)) :=
                        (Real.rpow_add hd 1 (-(1.9 : ℝ))).symm
                      _ = (d : ℝ) ^ (-(0.9 : ℝ)) := by congr 1 <;> norm_num
                  rw [hmul]
    have hpowSqEps : ((d : ℝ) ^ (-(1 / 8 : ℝ))) ^ 2 =
        (d : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
      norm_num
    have hnum : 2 * ε ^ 2 =
        (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 4 : ℝ)) := by
      dsimp [ε]
      rw [mul_pow]
      rw [hpowSqEps]
      norm_num
      ring_nf
    have hExponent :
        (1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ) ≤ 2 * ε ^ 2 / width := by
      apply (le_div_iff₀ hwidth).2
      have hpowFactor : (d : ℝ) ^ (0.65 : ℝ) *
          (d : ℝ) ^ (-(0.9 : ℝ)) = (d : ℝ) ^ (-(0.25 : ℝ)) := by
        rw [← Real.rpow_add hd]
        norm_num
      calc
        (1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ) * width ≤
            (1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ) *
              (300 * (d : ℝ) ^ (-(0.9 : ℝ))) :=
          mul_le_mul_of_nonneg_left hWidthUpper
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hd.le _))
        _ = (1 / 2 : ℝ) * (d : ℝ) ^ (-(0.25 : ℝ)) := by
              calc
                _ = (1 / 2 : ℝ) *
                    ((d : ℝ) ^ (0.65 : ℝ) * (d : ℝ) ^ (-(0.9 : ℝ))) := by ring
                _ = _ := by rw [hpowFactor]
        _ = 2 * ε ^ 2 := by convert hnum.symm using 1 <;> norm_num
    have hcenteredFull (r : Fin t) (g : H r.castSucc) :
        (∑ x, if history r.castSucc x = g then P.w x * Δ r x else 0) = 0 := by
      by_cases hrb : r.val < b.val
      · have hc := forcingLaw_centered_step q h.nonneg h.row_sum
          {i} y r a g
        simpa [P, forcingLaw, history, Δ, hrb] using hc
      · simp [history, Δ, hrb]
    have hAzumaMean (r : Fin t) (g : H r.castSucc) :
        P.pr (fun x => history r.castSucc x = g) = 0 ∨
          (0 : ℝ) * P.pr (fun x => history r.castSucc x = g) ≤
            (∑ x, if history r.castSucc x = g then P.w x * Δ r x else 0) := by
      right
      rw [zero_mul, hcenteredFull r g]
    have htail (D : Fin t → Path t d → ℝ)
        (hadapted : ∀ (m : ℕ) (hm : m ≤ t) (r : Fin t), r.val < m →
          ∀ x x', history ⟨m, Nat.lt_succ_of_le hm⟩ x =
            history ⟨m, Nat.lt_succ_of_le hm⟩ x' → D r x = D r x')
        (hD : ∀ r x, lo r ≤ D r x ∧ D r x ≤ hi r)
        (hmeanD : ∀ r (g : H r.castSucc),
          P.pr (fun x => history r.castSucc x = g) = 0 ∨
            (0 : ℝ) * P.pr (fun x => history r.castSucc x = g) ≤
              (∑ x, if history r.castSucc x = g then P.w x * D r x else 0)) :
      P.pr (fun x => ∑ r, D r x < -ε) ≤
        Real.exp (-2 * ε ^ 2 / width) := by
      simpa [width] using
        xAzuma H P history project hfiltration D hadapted
          (fun _ => 0) lo hi hD hmeanD hwidth ε hεpos
    have htailDown := htail Δ hAdapted hBound hAzumaMean
    let Δneg : Fin t → Path t d → ℝ := fun r x => -Δ r x
    have hAdaptedNeg :
        ∀ (m : ℕ) (hm : m ≤ t) (r : Fin t), r.val < m →
          ∀ x x', history ⟨m, Nat.lt_succ_of_le hm⟩ x =
            history ⟨m, Nat.lt_succ_of_le hm⟩ x' → Δneg r x = Δneg r x' := by
      intro m hm r hr x x' heq
      simp [Δneg, hAdapted m hm r hr x x' heq]
    have hBoundNeg : ∀ r x, lo r ≤ Δneg r x ∧ Δneg r x ≤ hi r := by
      intro r x
      rcases hBound r x with ⟨hl, hu⟩
      constructor <;> dsimp [Δneg, lo, hi] <;> linarith
    have hAzumaMeanNeg :
        ∀ r (g : H r.castSucc),
          P.pr (fun x => history r.castSucc x = g) = 0 ∨
            (0 : ℝ) * P.pr (fun x => history r.castSucc x = g) ≤
              (∑ x, if history r.castSucc x = g then P.w x * Δneg r x else 0) := by
      intro r g
      right
      simp only [zero_mul]
      have hsumNeg :
          (∑ x, if history r.castSucc x = g then
            P.w x * Δneg r x else 0) =
            -(∑ x, if history r.castSucc x = g then
              P.w x * Δ r x else 0) := by
        dsimp [Δneg]
        calc
          (∑ x, if history r.castSucc x = g then P.w x * -Δ r x else 0) =
              ∑ x, -(if history r.castSucc x = g then P.w x * Δ r x else 0) := by
                apply Finset.sum_congr rfl
                intro x hx
                by_cases hEq : history r.castSucc x = g <;> simp [hEq] <;> ring
          _ = -(∑ x, if history r.castSucc x = g then
                P.w x * Δ r x else 0) := by rw [Finset.sum_neg_distrib]
      rw [hsumNeg, hcenteredFull r g]
      simp
    have htailUp := htail Δneg hAdaptedNeg hBoundNeg hAzumaMeanNeg
    have hpairBad (x : Path t d) :
        hbad a b x → (∑ r, Δ r x < -ε) ∨ (∑ r, Δneg r x < -ε) := by
      intro hbad'
      have hsum : (∑ r, Δ r x) =
          forcedMartingalePart q {i} y x a b.val := by rfl
      have hbad'' : ε < |∑ r, Δ r x| := by
        dsimp [ε]
        dsimp [hbad, ε] at hbad'
        rw [← hsum] at hbad'
        exact hbad'
      by_cases hnonneg : 0 ≤ ∑ r, Δ r x
      · right
        have habs := abs_of_nonneg hnonneg
        rw [habs] at hbad''
        change (∑ r, -Δ r x) < -ε
        rw [Finset.sum_neg_distrib]
        linarith
      · left
        have hnonpos : ∑ r, Δ r x ≤ 0 := le_of_not_ge hnonneg
        have habs := abs_of_nonpos hnonpos
        rw [habs] at hbad''
        linarith
    calc
      P.pr (hbad a b) ≤
          P.pr (fun x => (∑ r, Δ r x < -ε) ∨
            (∑ r, Δneg r x < -ε)) :=
        FinProb.pr_mono P _ _ hpairBad
      _ ≤ P.pr (fun x => ∑ r, Δ r x < -ε) +
            P.pr (fun x => ∑ r, Δneg r x < -ε) :=
        FinProb.pr_union_le _ _ _
      _ ≤ Real.exp (-2 * ε ^ 2 / width) +
            Real.exp (-2 * ε ^ 2 / width) := add_le_add htailDown htailUp
      _ ≤ 2 * Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) := by
        have harg : (-2 * ε ^ 2) / width ≤
            -(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ) := by
          have hneg := neg_le_neg hExponent
          simpa [div_eq_mul_inv] using hneg
        have hle : Real.exp (-2 * ε ^ 2 / width) ≤
            Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) :=
          Real.exp_le_exp.mpr harg
        nlinarith
  let badPair : (Fin t × Fin (t + 1)) → Path t d → Prop :=
    fun ab x => hbad ab.1 ab.2 x
  have hbadAny (x : Path t d) :
      ¬ ForcedMartingaleGood q {i} y x →
        ∃ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))), badPair ab x := by
    intro hnot
    dsimp [ForcedMartingaleGood] at hnot
    push_neg at hnot
    rcases hnot with ⟨a, b, hbad'⟩
    have hh : hbad a b x := by
      dsimp [hbad]
      exact hbad'
    exact ⟨(a, b), Finset.mem_univ _, by dsimp [badPair]; exact hh⟩
  have hbadProb :
      P.pr (fun x => ∃ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))),
        badPair ab x) ≤ 2 * (d : ℝ) ^ 2 *
          Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) := by
    calc
      P.pr (fun x => ∃ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))),
          badPair ab x) ≤
          ∑ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))),
            P.pr (badPair ab) :=
        lane_q_inj_comp_pr_finset_exists_le P badPair Finset.univ
      _ ≤ ∑ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))),
            2 * Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) := by
              apply Finset.sum_le_sum
              intro ab hab
              exact hpairTail ab.1 ab.2
      _ ≤ _ := by
            have htcard : (Fintype.card (Fin t × Fin (t + 1)) : ℝ) ≤
                (d : ℝ) ^ 2 := by
              have hcast : (Fintype.card (Fin t × Fin (t + 1)) : ℝ) =
                  (t : ℝ) * ((t + 1 : ℕ) : ℝ) := by simp
              rw [hcast]
              calc
                (t : ℝ) * ((t + 1 : ℕ) : ℝ) ≤
                    (d : ℝ) * ((t + 1 : ℕ) : ℝ) :=
                  mul_le_mul_of_nonneg_right htLe (by positivity)
                _ ≤ (d : ℝ) * (d : ℝ) :=
                  mul_le_mul_of_nonneg_left ht1Cast (by positivity)
                _ = (d : ℝ) ^ 2 := by ring
            calc
              (∑ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))),
                  2 * Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ))) =
                  (Fintype.card (Fin t × Fin (t + 1)) : ℝ) *
                    (2 * Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ))) := by simp
              _ ≤ (d : ℝ) ^ 2 *
                    (2 * Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ))) :=
                mul_le_mul_of_nonneg_right htcard (by positivity)
              _ = 2 * (d : ℝ) ^ 2 *
                    Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) := by ring
  have hbadBound :
      P.pr (fun x => ¬ ForcedMartingaleGood q {i} y x) ≤ failureBound d := by
    calc
      P.pr (fun x => ¬ ForcedMartingaleGood q {i} y x) ≤
          P.pr (fun x => ∃ ab ∈ (Finset.univ : Finset (Fin t × Fin (t + 1))),
            badPair ab x) :=
        FinProb.pr_mono P _ _ hbadAny
      _ ≤ 2 * (d : ℝ) ^ 2 *
          Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) := hbadProb
      _ ≤ failureBound d := by
        have hExp : Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) ≤
            Real.exp (-2 * (d : ℝ) ^ (0.1 : ℝ)) :=
          Real.exp_le_exp.mpr (by linarith [hdom])
        calc
          2 * (d : ℝ) ^ 2 *
              Real.exp (-(1 / 600 : ℝ) * (d : ℝ) ^ (0.65 : ℝ)) ≤
            2 * (d : ℝ) ^ 2 * Real.exp (-2 * (d : ℝ) ^ (0.1 : ℝ)) :=
              mul_le_mul_of_nonneg_left hExp (by positivity)
          _ ≤ failureBound d := hfinalTail
  have htotal :
      P.pr (ForcedMartingaleGood q {i} y) +
        P.pr (fun x => ¬ ForcedMartingaleGood q {i} y x) = 1 := by
    classical
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib, ← P.sum_eq_one]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hg : ForcedMartingaleGood q {i} y x <;> simp [hg]
  have hsuccess :
      1 - failureBound d ≤ P.pr (ForcedMartingaleGood q {i} y) := by
    linarith [htotal, hbadBound]
  simpa [P] using hsuccess

private theorem lane_q_inj_comp_stepDrift_range {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q)
    (x : Path t d) (a j : Fin t) :
    0 ≤ stepDrift q x a j ∧ stepDrift q x a j ≤
      10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
  classical
  let y₀ : Fin t → Fin d := fun _ => ⟨0, by have := h.dimension; omega⟩
  let R := forcingKernel q h.nonneg ∅ y₀ j
    (takePrefix (Nat.le_of_lt j.isLt) x)
  have hstepEq : stepDrift q x a j = forcedStepDrift q ∅ y₀ x a j := by
    unfold stepDrift forcedStepDrift
    apply Finset.sum_congr rfl
    intro z hz
    simp [forcingStepWeight, pendingLabels]
  have hstep : R.expect (fun z => z.elim 0 (q a)) = stepDrift q x a j := by
    rw [hstepEq]
    exact forcingKernel_expect_step q h.nonneg ∅ y₀ x j a
  have hrange (z : Option (Fin d)) :
      0 ≤ z.elim 0 (q a) ∧
        z.elim 0 (q a) ≤ 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    cases z with
    | none =>
        constructor
        · simp
        · positivity
    | some z => exact ⟨h.nonneg a z, h.atom a z⟩
  have hlo := FinProb.expect_mono R (fun z => (hrange z).1)
  have hhi := FinProb.expect_mono R (fun z => (hrange z).2)
  constructor
  · calc
      0 = R.expect (fun _ => 0) := by simp [R, FinProb.expect_const]
      _ ≤ R.expect (fun z => z.elim 0 (q a)) := hlo
      _ = stepDrift q x a j := hstep
  · calc
      stepDrift q x a j = R.expect (fun z => z.elim 0 (q a)) := hstep.symm
      _ ≤ R.expect (fun _ => 10 * (d : ℝ) ^ (-(0.95 : ℝ))) := hhi
      _ = 10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by simp [R, FinProb.expect_const]

private theorem lane_q_inj_comp_stepDrift_prefix_congr {d t : ℕ}
    (q : Fin t → Fin d → ℝ) (y : Fin t → Fin d)
    (x x' : Path t d) (j a : Fin t)
    (hprev : ∀ k : Fin t, k.val < j.val → x k = x' k) :
    stepDrift q x a j = stepDrift q x' a j := by
  classical
  unfold stepDrift
  apply Finset.sum_congr rfl
  intro z hz
  have hweight : ordinaryWeight q x j ∅ z = ordinaryWeight q x' j ∅ z := by
    have hz' := forcingStepWeight_prefix_congr q ∅ y x x' j z hprev
    simpa [forcingStepWeight, pendingLabels] using hz'
  rw [hweight]

/-- Reuses the deterministic recurrence with the forced martingale and drift change. -/
theorem singleton_forcing_tracking_transfer (K : ℝ) (hK : 1 ≤ K) :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      DriftRecurrence q K → ∀ i y, 0 < q i (y i) →
      (∀ x a (b : Fin (t + 1)), RunningThrough q x b.val →
        |∑ j : Fin t, if j.val < b.val then
          forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| ≤
            1000 * (d : ℝ) ^ (-(0.95 : ℝ))) →
      1 - failureBound d ≤
        (forcingLaw q h.nonneg h.row_sum {i} y).pr (ForcedMartingaleGood q {i} y) →
      1 - failureBound d ≤ (forcingLaw q h.nonneg h.row_sum {i} y).pr (Good q) := by
  have hdecay125 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ)))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(1 / 8 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (1 / 8 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hdecay825 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.825 : ℝ)))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.825 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.825 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hdecay95 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.95 : ℝ)))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.95 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.95 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hdecay0025 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(0.025 : ℝ)))
      atTop (nhds 0) := by
    change Tendsto ((fun x : ℝ => x ^ (-(0.025 : ℝ))) ∘ fun n : ℕ => (n : ℝ))
      atTop (nhds 0)
    exact (tendsto_rpow_neg_atTop (by norm_num : (0.025 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hKexpPos : 0 < K * Real.exp K :=
    mul_pos (lt_of_lt_of_le (by norm_num) hK) (Real.exp_pos K)
  have hsmallDriftEvent := hdecay825.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2020))
  have hsmallTrackEvent := hdecay125.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / (20 * (K * Real.exp K)) by positivity))
  have hsmallAtomEvent := hdecay95.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  have hsmallTerminalEvent := hdecay0025.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / (K * Real.exp K) by positivity))
  filter_upwards [hsmallDriftEvent, hsmallTrackEvent, hsmallAtomEvent,
    hsmallTerminalEvent] with d hsmallDrift hsmallTrack hsmallAtom hsmallTerminal
  intro t q hq hRec i y htarget hDrift hForced
  classical
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 100) hq.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hatomSmall : 10 * (d : ℝ) ^ (-(0.95 : ℝ)) ≤ 1 / 10 := by
    nlinarith [hsmallAtom]
  have hpowSplit : (d : ℝ) ^ (-(0.95 : ℝ)) =
      (d : ℝ) ^ (-(1 / 8 : ℝ)) * (d : ℝ) ^ (-(0.825 : ℝ)) := by
    rw [← Real.rpow_add hd]
    norm_num
  have hdriftSmall : 1010 * (d : ℝ) ^ (-(0.95 : ℝ)) ≤
      (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    rw [hpowSplit]
    have hp := hsmallDrift
    have hnonneg := Real.rpow_nonneg hd.le (-(1 / 8 : ℝ))
    nlinarith
  have htrackSmall : K * Real.exp K * (d : ℝ) ^ (-(1 / 8 : ℝ)) ≤
      1 / 20 := by
    have hmul := mul_lt_mul_of_pos_left hsmallTrack hKexpPos
    have hcancel : K * Real.exp K *
        (1 / (20 * (K * Real.exp K))) = (1 / 20 : ℝ) := by
      field_simp
    rw [hcancel] at hmul
    exact hmul.le
  have hpowTerminal : (d : ℝ) ^ (-(1 / 8 : ℝ)) =
      (d : ℝ) ^ (-(0.1 : ℝ)) * (d : ℝ) ^ (-(0.025 : ℝ)) := by
    rw [← Real.rpow_add hd]
    norm_num
  have hterminalSmall : K * Real.exp K * (d : ℝ) ^ (-(1 / 8 : ℝ)) ≤
      (d : ℝ) ^ (-(0.1 : ℝ)) := by
    rw [hpowTerminal]
    have hnonneg := Real.rpow_nonneg hd.le (-(0.1 : ℝ))
    have hmulC := mul_lt_mul_of_pos_left hsmallTerminal hKexpPos
    have hcancel : K * Real.exp K * (1 / (K * Real.exp K)) = 1 := by field_simp
    rw [hcancel] at hmulC
    have hmul := mul_le_mul_of_nonneg_left hmulC.le hnonneg
    calc
      K * Real.exp K *
          ((d : ℝ) ^ (-(0.1 : ℝ)) * (d : ℝ) ^ (-(0.025 : ℝ))) =
          (d : ℝ) ^ (-(0.1 : ℝ)) *
            (K * Real.exp K * (d : ℝ) ^ (-(0.025 : ℝ))) := by ring
      _ ≤ (d : ℝ) ^ (-(0.1 : ℝ)) * 1 := hmul
      _ = (d : ℝ) ^ (-(0.1 : ℝ)) := by ring
  have hRunMono (x : Path t d) {u v : ℕ} (huv : u ≤ v)
      (hrun : RunningThrough q x v) : RunningThrough q x u := by
    rcases hrun with ⟨⟨hvalid, hinj⟩, htrack⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro k hk
      exact hvalid k (lt_of_lt_of_le hk huv)
    · intro k l hk hl hkl
      exact hinj k l (lt_of_lt_of_le hk huv) (lt_of_lt_of_le hl huv) hkl
    · intro k hk
      exact htrack k (lt_of_lt_of_le hk huv)
  have hpartDecomp (x : Path t d) (a : Fin t) (b : Fin (t + 1)) :
      martingalePart q x a b.val = forcedMartingalePart q {i} y x a b.val +
        ∑ j : Fin t, if j.val < b.val then
          forcedStepDrift q {i} y x a j - stepDrift q x a j else 0 := by
    unfold martingalePart forcedMartingalePart
    calc
      _ = ∑ j : Fin t,
          ((if j.val < b.val then
            (x j).elim 0 (q a) - forcedStepDrift q {i} y x a j else 0) +
          (if j.val < b.val then
            forcedStepDrift q {i} y x a j - stepDrift q x a j else 0)) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hjb : j.val < b.val <;> simp [hjb] <;> ring
      _ = _ := by rw [Finset.sum_add_distrib]
  have hordinaryBound (x : Path t d) (a : Fin t) (b : Fin (t + 1))
      (hrun : RunningThrough q x b.val)
      (hforced : ForcedMartingaleGood q {i} y x) :
      |martingalePart q x a b.val| ≤
        (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
          1000 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
    have hdiff := hDrift x a b hrun
    calc
      |martingalePart q x a b.val| =
          |forcedMartingalePart q {i} y x a b.val +
            ∑ j : Fin t, if j.val < b.val then
              forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| := by
                rw [hpartDecomp]
      _ ≤ |forcedMartingalePart q {i} y x a b.val| +
          |∑ j : Fin t, if j.val < b.val then
            forcedStepDrift q {i} y x a j - stepDrift q x a j else 0| := abs_add_le _ _
      _ ≤ (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
          1000 * (d : ℝ) ^ (-(0.95 : ℝ)) := add_le_add (hforced a b) hdiff
  let truncateAt (x : Path t d) (n : ℕ) : Path t d :=
    fun k => if k.val < n then x k else none
  have htruncatedMartingaleGood (x : Path t d) (c : Fin (t + 1))
      (hrun : RunningThrough q x c.val)
      (hforced : ForcedMartingaleGood q {i} y x) :
      MartingaleGood q (truncateAt x c.val) := by
    let xt := truncateAt x c.val
    have hbefore (k : Fin t) (hk : k.val < c.val) : xt k = x k := by
      simp [xt, truncateAt, hk]
    have hstepBefore (a : Fin t) (k : Fin t) (hkc : k.val < c.val) :
        stepDrift q xt a k = stepDrift q x a k := by
      apply lane_q_inj_comp_stepDrift_prefix_congr q y xt x k a
      intro r hr
      exact hbefore r (lt_trans hr hkc)
    have hrunAt (b : Fin (t + 1)) (hbc : b.val ≤ c.val) :
        RunningThrough q x b.val := hRunMono x hbc hrun
    have hstepC (a : Fin t) (hc : c.val < t) :
        stepDrift q xt a ⟨c.val, hc⟩ = stepDrift q x a ⟨c.val, hc⟩ := by
      apply lane_q_inj_comp_stepDrift_prefix_congr q y xt x ⟨c.val, hc⟩ a
      intro r hr
      exact hbefore r hr
    have hstepAfter (a : Fin t) (k : Fin t) (hck : c.val < k.val) :
        stepDrift q xt a k = 0 := by
      have hnot : ¬ PrefixValid xt k.val := by
        intro hv
        have hcFin : c.val < t := by omega
        have hsome := hv.1 ⟨c.val, hcFin⟩ hck
        have hnone : xt ⟨c.val, hcFin⟩ = none := by simp [xt, truncateAt]
        rw [hnone] at hsome
        simp at hsome
      simp [stepDrift, ordinaryWeight, hnot]
    have hsamePrefix (a : Fin t) (b : Fin (t + 1)) (hbc : b.val ≤ c.val) :
        martingalePart q xt a b.val = martingalePart q x a b.val := by
      unfold martingalePart
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkb : k.val < b.val
      · have hkc : k.val < c.val := lt_of_lt_of_le hkb hbc
        simp only [if_pos hkb]
        rw [hbefore k hkc, hstepBefore a k hkc]
      · simp [hkb]
    have hafterPrefix (a : Fin t) (b : Fin (t + 1))
        (hcb : c.val < b.val) (hcLt : c.val < t) :
        martingalePart q xt a b.val =
          martingalePart q x a c.val -
            stepDrift q x a ⟨c.val, hcLt⟩ := by
      let j : Fin t := ⟨c.val, hcLt⟩
      have hpoint (k : Fin t) :
          (if k.val < b.val then
            (xt k).elim 0 (q a) - stepDrift q xt a k else 0) =
          (if k.val < c.val then
            (x k).elim 0 (q a) - stepDrift q x a k else 0) +
          (if k = j then -stepDrift q x a j else 0) := by
        by_cases hkc : k.val < c.val
        · have hkb : k.val < b.val := lt_trans hkc hcb
          have hkj : k ≠ j := by
            intro heq
            have hv := congrArg Fin.val heq
            simp [j] at hv
            omega
          simp [hkb, hkc, hkj, hbefore k hkc, hstepBefore a k hkc]
        · by_cases hkj : k = j
          · subst k
            have hkb : c.val < b.val := hcb
            simp [j, hkb, xt, truncateAt, hstepC a hcLt]
          · have hvalne : k.val ≠ c.val := by
              intro heq
              apply hkj
              apply Fin.ext
              simpa [j] using heq
            have hkg : c.val < k.val := by omega
            by_cases hkb : k.val < b.val
            · simp [hkb, hkc, hkj, xt, truncateAt, hstepAfter a k hkg]
            · simp [hkb, hkc, hkj]
      calc
        martingalePart q xt a b.val =
            ∑ k : Fin t, ((if k.val < c.val then
              (x k).elim 0 (q a) - stepDrift q x a k else 0) +
              (if k = j then -stepDrift q x a j else 0)) := by
                unfold martingalePart
                apply Finset.sum_congr rfl
                intro k hk
                exact hpoint k
        _ = martingalePart q x a c.val - stepDrift q x a j := by
              rw [Finset.sum_add_distrib]
              simp [martingalePart, j]
              ring
    intro a b
    by_cases hbc : b.val ≤ c.val
    · rw [hsamePrefix a b hbc]
      have hb := hordinaryBound x a b (hrunAt b hbc) hforced
      calc
        |martingalePart q x a b.val| ≤
            (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
              1000 * (d : ℝ) ^ (-(0.95 : ℝ)) := hb
        _ ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
          nlinarith [hdriftSmall, Real.rpow_nonneg hd.le (-(0.95 : ℝ))]
    · have hcb : c.val < b.val := by omega
      have hcLt : c.val < t := by omega
      rw [hafterPrefix a b hcb hcLt]
      have hb := hordinaryBound x a c hrun hforced
      have hc := lane_q_inj_comp_stepDrift_range q hq x a ⟨c.val, by omega⟩
      calc
        |martingalePart q x a c.val -
            stepDrift q x a ⟨c.val, by omega⟩| ≤
          |martingalePart q x a c.val| +
            |stepDrift q x a ⟨c.val, by omega⟩| := by
              calc
                |martingalePart q x a c.val -
                    stepDrift q x a ⟨c.val, by omega⟩| =
                    |martingalePart q x a c.val +
                      -stepDrift q x a ⟨c.val, by omega⟩| := by congr 1 <;> ring
                _ ≤ |martingalePart q x a c.val| +
                    |-stepDrift q x a ⟨c.val, by omega⟩| := abs_add_le _ _
                _ = _ := by simp
        _ ≤ (1 / 2 : ℝ) * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
            1000 * (d : ℝ) ^ (-(0.95 : ℝ)) +
            10 * (d : ℝ) ^ (-(0.95 : ℝ)) := by
              exact add_le_add hb
                (abs_le.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩)
        _ ≤ (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
          nlinarith [hdriftSmall, Real.rpow_nonneg hd.le (-(0.95 : ℝ))]
  have htrackNonneg (x : Path t d) (n : ℕ) :
      0 ≤ trackingError q x n := by
    classical
    let T : Set ℝ := {0} ∪ {r | ∃ a : Fin t, ∃ k : Fin (t + 1),
      k.val ≤ n ∧ r = |usedMass q x a k.val - (k.val : ℝ) / d|}
    have hfinite : T.Finite := by
      have hrange : (Set.range (fun p : Fin t × Fin (t + 1) =>
          |usedMass q x p.1 p.2.val - (p.2.val : ℝ) / d|)).Finite := Set.finite_range _
      apply Set.Finite.union
      · exact Set.finite_singleton 0
      · apply hrange.subset
        rintro r ⟨a, k, hk, rfl⟩
        exact ⟨(a, k), rfl⟩
    unfold trackingError
    apply le_csSup hfinite.bddAbove
    simp [T]
  have hrecAt (x : Path t d) (c : Fin (t + 1))
      (hrun : RunningThrough q x c.val)
      (hforced : ForcedMartingaleGood q {i} y x) :
      trackingError q x c.val ≤ K * (d : ℝ) ^ (-(1 / 8 : ℝ)) +
        K / d * ∑ j : Fin t,
          if j.val < c.val then trackingError q x j.val else 0 := by
    let xt := truncateAt x c.val
    have hbefore (k : Fin t) (hk : k.val < c.val) : xt k = x k := by
      simp [xt, truncateAt, hk]
    have htrackC : trackingError q xt c.val = trackingError q x c.val := by
      apply trackingError_prefix_congr q xt x c.val (by omega)
      intro k hk
      exact hbefore k hk
    have htrackRow (j : Fin t) (hj : j.val < c.val) :
        trackingError q xt j.val = trackingError q x j.val := by
      apply trackingError_prefix_congr q xt x j.val (Nat.le_of_lt j.isLt)
      intro k hk
      exact hbefore k (lt_trans hk hj)
    have hrunTrunc : RunningThrough q xt c.val := by
      refine ⟨?_, ?_⟩
      · rcases hrun.1 with ⟨hvalid, hinj⟩
        constructor
        · intro k hk
          rw [hbefore k hk]
          exact hvalid k hk
        · intro k l hk hl heq
          have heq' : x k = x l := by
            rw [hbefore k hk, hbefore l hl] at heq
            exact heq
          exact hinj k l hk hl heq'
      · intro j hj
        rw [htrackRow j hj]
        exact hrun.2 j hj
    have hmart := htruncatedMartingaleGood x c hrun hforced
    have hrec := hRec xt c hrunTrunc hmart
    rw [htrackC] at hrec
    have hsum :
        (∑ j : Fin t, if j.val < c.val then trackingError q xt j.val else 0) =
        ∑ j : Fin t, if j.val < c.val then trackingError q x j.val else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjc : j.val < c.val
      · simp [hjc, htrackRow j hjc]
      · simp [hjc]
    rw [hsum] at hrec
    exact hrec
  have herrorBound (x : Path t d) (c : Fin (t + 1))
      (hrun : RunningThrough q x c.val)
      (hforced : ForcedMartingaleGood q {i} y x) :
      trackingError q x c.val ≤ K * Real.exp K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
    let A : ℝ := K * (d : ℝ) ^ (-(1 / 8 : ℝ))
    let B : ℝ := K / (d : ℝ)
    let e : Fin (t + 1) → ℝ := fun b =>
      if b.val ≤ c.val then max 0 (trackingError q x b.val) else 0
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have heNonneg (b : Fin (t + 1)) : 0 ≤ e b := by
      by_cases hb : b.val ≤ c.val
      · change 0 ≤ if b.val ≤ c.val then
            max 0 (trackingError q x b.val) else 0
        rw [if_pos hb]
        exact le_max_left _ _
      · change 0 ≤ if b.val ≤ c.val then
            max 0 (trackingError q x b.val) else 0
        rw [if_neg hb]
    have hrecGronwall (b : Fin (t + 1)) :
        e b ≤ A + B * ∑ j : Fin (t + 1),
          if j.val < b.val then e j else 0 := by
      by_cases hbc : b.val ≤ c.val
      · have hrunB := hRunMono x hbc hrun
        have hrecB := hrecAt x b hrunB hforced
        have hbval : b.val ≤ t := by omega
        have hsum := fin_sum_prefix_eq hbval
          (fun j : Fin t => trackingError q x j.val)
          (fun j : Fin (t + 1) => e j)
          (by
            intro j hj
            let j' : Fin (t + 1) := ⟨j.val, by omega⟩
            have hj' : j'.val < b.val := by simpa [j'] using hj
            have hj'c : j'.val ≤ c.val := le_trans (Nat.le_of_lt hj') hbc
            change trackingError q x j.val = e j'
            dsimp [e]
            rw [if_pos hj'c]
            rw [show j'.val = j.val by rfl]
            rw [max_eq_right (htrackNonneg x j.val)])
        rw [hsum] at hrecB
        have hsumNonneg :
            0 ≤ ∑ j : Fin (t + 1), if j.val < b.val then e j else 0 := by
          apply Finset.sum_nonneg
          intro j hj
          by_cases hjb : j.val < b.val
          · simp [hjb, heNonneg]
          · simp [hjb]
        have hrhsNonneg :
            0 ≤ A + B * ∑ j : Fin (t + 1),
              if j.val < b.val then e j else 0 :=
          add_nonneg hA (mul_nonneg hB hsumNonneg)
        have heq : e b = max 0 (trackingError q x b.val) := by
          change (if b.val ≤ c.val then max 0 (trackingError q x b.val) else 0) = _
          rw [if_pos hbc]
        rw [heq]
        exact max_le_iff.mpr ⟨hrhsNonneg, hrecB⟩
      · have heq : e b = 0 := by
          change (if b.val ≤ c.val then max 0 (trackingError q x b.val) else 0) = 0
          rw [if_neg hbc]
        rw [heq]
        have hsumNonneg :
            0 ≤ ∑ j : Fin (t + 1), if j.val < b.val then e j else 0 := by
          apply Finset.sum_nonneg
          intro j hj
          by_cases hjb : j.val < b.val
          · simp [hjb, heNonneg j]
          · simp [hjb]
        exact add_nonneg hA (mul_nonneg hB hsumNonneg)
    have hgronwall := discrete_tracking_gronwall t A B hA hB e heNonneg hrecGronwall
    have htrackC : trackingError q x c.val ≤ e c := by
      have heq : e c = max 0 (trackingError q x c.val) := by
        change (if c.val ≤ c.val then max 0 (trackingError q x c.val) else 0) = _
        rw [if_pos le_rfl]
      rw [heq]
      exact le_max_right _ _
    have hcval : (c.val : ℝ) ≤ (t : ℝ) := by exact_mod_cast (show c.val ≤ t by omega)
    have hratio : (c.val : ℝ) / (d : ℝ) ≤ 3 / 4 := by
      apply (div_le_iff₀ hd).2
      nlinarith [hcval, (show (t : ℝ) ≤ 3 * (d : ℝ) / 4 from hq.horizon)]
    have htime : B * (c.val : ℝ) ≤ K := by
      dsimp [B]
      calc
        K / (d : ℝ) * (c.val : ℝ) = K * ((c.val : ℝ) / (d : ℝ)) := by ring
        _ ≤ K := by
          have hmul := mul_le_mul_of_nonneg_left hratio (le_of_lt (lt_of_lt_of_le (by norm_num) hK))
          nlinarith [hmul]
    have hexp : Real.exp (B * (c.val : ℝ)) ≤ Real.exp K :=
      Real.exp_le_exp.mpr htime
    calc
      trackingError q x c.val ≤ e c := htrackC
      _ ≤ A * Real.exp (B * (c.val : ℝ)) := hgronwall c
      _ ≤ K * Real.exp K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by
        dsimp [A]
        calc
          K * (d : ℝ) ^ (-(1 / 8 : ℝ)) * Real.exp (B * (c.val : ℝ)) =
              (K * Real.exp (B * (c.val : ℝ))) * (d : ℝ) ^ (-(1 / 8 : ℝ)) := by ring
          _ ≤ (K * Real.exp K) * (d : ℝ) ^ (-(1 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp (by linarith [hK]))
              (Real.rpow_nonneg hd.le _)
          _ = K * Real.exp K * (d : ℝ) ^ (-(1 / 8 : ℝ)) := rfl
  have hstepFactor (x : Path t d) (hw : forcingWeight q {i} y x ≠ 0)
      (j : Fin t) : forcingStepWeight q {i} y x j (x j) ≠ 0 := by
    unfold forcingWeight at hw
    exact (Finset.prod_ne_zero_iff.mp hw) j (Finset.mem_univ j)
  have hrunAvoid (x : Path t d) (hw : forcingWeight q {i} y x ≠ 0)
      (hforced : ForcedMartingaleGood q {i} y x) (n : ℕ) (hn : n ≤ t) :
      RunningThrough q x n ∧
        ∀ k : Fin t, k.val < n → k.val < i.val → x k ≠ some (y i) := by
    induction n with
    | zero =>
        constructor
        · refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro k hk
            omega
          · intro k l hk hl hEq
            omega
          · intro k hk
            omega
        · intro k hk
          omega
    | succ n ih =>
        have hnlt : n < t := by omega
        have hprev := ih (by omega)
        let c : Fin (t + 1) := ⟨n, by omega⟩
        have htrack := herrorBound x c hprev.1 hforced
        have htrack20 : trackingError q x n ≤ 1 / 20 := by
          exact htrack.trans htrackSmall
        let r : Fin t := ⟨n, hnlt⟩
        have hfactor := hstepFactor x hw r
        have hfreeMass := free_mass_before_stop q hq x r hprev.1.1 htrack20
        have hrow : ∃ z, x r = some z ∧ Free x n z ∧
            (n < i.val → z ≠ y i) := by
          by_cases hri : r = i
          · have hfreeTarget : Free x n (y i) := by
              intro k hk heq
              have hki : k.val < i.val := by
                have hv := congrArg Fin.val hri
                dsimp [r] at hv
                omega
              exact hprev.2 k hk hki heq
            have hactive : PrefixValid x n ∧
                trackingError q x n ≤ 1 / 20 ∧ Free x n (y i) :=
              ⟨hprev.1.1, htrack20, hfreeTarget⟩
            have hactiveR : PrefixValid x r.val ∧
                trackingError q x r.val ≤ 1 / 20 ∧ Free x r.val (y i) := by
              simpa [r] using hactive
            have hmem : r ∈ ({i} : Finset (Fin t)) := by simp [hri]
            have hyEq : y r = y i := congrArg y hri
            have hforceEq : forcingStepWeight q {i} y x r (x r) =
                if x r = some (y i) then 1 else 0 := by
              unfold forcingStepWeight
              rw [if_pos hmem]
              have hcond : PrefixValid x r.val ∧
                  trackingError q x r.val ≤ 1 / 20 ∧ Free x r.val (y r) := by
                simpa [hyEq] using hactiveR
              rw [if_pos hcond]
              simp [hyEq]
            have hlabel : x r = some (y i) := by
              by_contra hne
              rw [hforceEq] at hfactor
              simp [hne] at hfactor
            refine ⟨y i, hlabel, hfreeTarget, ?_⟩
            intro hni
            have hv := congrArg Fin.val hri
            dsimp [r] at hv
            omega
          · let B : Finset (Fin d) := pendingLabels {i} y r
            have hBsingleton (hni : n < i.val) : B = {y i} := by
              dsimp [B]
              unfold pendingLabels
              have hfilter :
                  ({i} : Finset (Fin t)).filter (fun j => r.val < j.val) = {i} := by
                ext j
                simp only [Finset.mem_filter, Finset.mem_singleton]
                constructor
                · rintro ⟨hji, _⟩
                  exact hji
                · intro hji
                  subst j
                  exact ⟨rfl, by simpa [r] using hni⟩
              rw [hfilter]
              exact Finset.image_singleton y i
            have hBempty (hni : ¬ n < i.val) : B = ∅ := by
              dsimp [B]
              unfold pendingLabels
              have hfilter :
                  ({i} : Finset (Fin t)).filter (fun j => r.val < j.val) = ∅ := by
                ext j
                constructor
                · intro hj
                  rcases Finset.mem_filter.mp hj with ⟨hji, hjlt⟩
                  have hjiEq : j = i := Finset.mem_singleton.mp hji
                  subst j
                  exact (hni (by simpa [r] using hjlt)).elim
                · intro hj
                  have hfalse : False := by simpa using hj
                  exact hfalse.elim
              rw [hfilter]
              simp
            have hfreeTarget (hni : n < i.val) : Free x n (y i) := by
              intro k hk heq
              exact hprev.2 k hk (by omega) heq
            have hmassPos : 0 < availableMass q x r B := by
              by_cases hni : n < i.val
              · have hmassSingleton := lane_q_inj_comp_available_mass_singleton
                  q x r (y i) (hfreeTarget hni)
                rw [hBsingleton hni, hmassSingleton]
                have hbase := hfreeMass.2
                have hatom := hq.atom r (y i)
                nlinarith [hatomSmall]
              · rw [hBempty hni]
                exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5) hfreeMass.2
            have hactive : PrefixValid x n ∧
                trackingError q x n ≤ 1 / 20 ∧ 0 < availableMass q x r B :=
              ⟨hprev.1.1, htrack20, hmassPos⟩
            have hactiveR : PrefixValid x r.val ∧
                trackingError q x r.val ≤ 1 / 20 ∧ 0 < availableMass q x r B := by
              simpa [r] using hactive
            have hrnot : r ∉ ({i} : Finset (Fin t)) := by
              simp
              exact hri
            have hforceEq : forcingStepWeight q {i} y x r (x r) =
                ordinaryWeight q x r B (x r) := by
              simp [forcingStepWeight, hrnot, B]
            have hordNe : ordinaryWeight q x r B (x r) ≠ 0 := by
              rw [← hforceEq]
              exact hfactor
            cases hx : x r with
            | none =>
                have hz : ordinaryWeight q x r B none = 0 := by
                  unfold ordinaryWeight
                  rw [if_pos hactiveR]
                have hordNe' := hordNe
                rw [hx] at hordNe'
                exact False.elim (hordNe' hz)
            | some z =>
                have hallowed : Free x n z ∧ z ∉ B := by
                  by_contra hbad
                  have hbadR : ¬ (Free x r.val z ∧ z ∉ B) := by
                    simpa [r] using hbad
                  have hz : ordinaryWeight q x r B (some z) = 0 := by
                    unfold ordinaryWeight
                    rw [if_pos hactiveR]
                    simp [hbadR]
                  have hordNe' := hordNe
                  rw [hx] at hordNe'
                  exact hordNe' hz
                refine ⟨z, rfl, hallowed.1, ?_⟩
                intro hni
                have hpend := hBsingleton hni
                have hzneq : z ≠ y i := by
                  intro hEq
                  apply hallowed.2
                  rw [hpend]
                  simp [hEq]
                exact hzneq
        rcases hrow with ⟨z, hzr, hfreeRow, hrowAvoid⟩
        have hvalidNext : PrefixValid x (n + 1) := by
          rcases hprev.1.1 with ⟨hval, hinj⟩
          constructor
          · intro k hk
            by_cases hkold : k.val < n
            · exact hval k hkold
            · have hkr : k = r := Fin.ext (by dsimp [r]; omega)
              subst k
              exact ⟨z, hzr⟩
          · intro k l hk hl heq
            by_cases hko : k.val < n
            · by_cases hlo : l.val < n
              · exact hinj k l hko hlo heq
              · have hlr : l = r := Fin.ext (by dsimp [r]; omega)
                subst l
                have hek : x k = some z := heq.trans hzr
                exact False.elim ((hfreeRow k hko) hek)
            · have hkr : k = r := Fin.ext (by dsimp [r]; omega)
              subst k
              by_cases hlo : l.val < n
              · have hel : x l = some z := heq.symm.trans hzr
                exact False.elim ((hfreeRow l hlo) hel)
              · have hlr : l = r := Fin.ext (by dsimp [r]; omega)
                subst l
                rfl
        have htrackNext (k : Fin t) (hk : k.val < n + 1) :
            trackingError q x k.val ≤ 1 / 20 := by
          by_cases hko : k.val < n
          · exact hprev.1.2 k hko
          · have hkr : k = r := Fin.ext (by dsimp [r]; omega)
            subst k
            exact htrack20
        have havoidNext : ∀ k : Fin t, k.val < n + 1 → k.val < i.val →
            x k ≠ some (y i) := by
          intro k hk hki
          by_cases hko : k.val < n
          · exact hprev.2 k hko hki
          · have hkr : k = r := Fin.ext (by dsimp [r]; omega)
            subst k
            intro heq
            have hsome : some z = some (y i) := hzr.symm.trans heq
            injection hsome with hzEq
            exact hrowAvoid hki hzEq
        exact ⟨⟨hvalidNext, htrackNext⟩, havoidNext⟩
  have hgoodSupport (x : Path t d) (hw : forcingWeight q {i} y x ≠ 0)
      (hforced : ForcedMartingaleGood q {i} y x) : Good q x := by
    have hall := hrunAvoid x hw hforced t le_rfl
    let c : Fin (t + 1) := ⟨t, by omega⟩
    have hterminal := herrorBound x c hall.1 hforced
    have hterminal20 : trackingError q x t ≤ 1 / 20 := hterminal.trans htrackSmall
    have hterminal01 : trackingError q x t ≤ (d : ℝ) ^ (-(0.1 : ℝ)) := by
      have hc : c.val = t := rfl
      simpa [hc] using hterminal.trans hterminalSmall
    exact ⟨hall.1.1, hterminal20, hterminal01⟩
  let P : FinProb (Path t d) := forcingLaw q hq.nonneg hq.row_sum {i} y
  have hprob : P.pr (ForcedMartingaleGood q {i} y) =
      P.pr (fun x => ForcedMartingaleGood q {i} y x ∧ P.w x ≠ 0) := by
    classical
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hw : P.w x = 0 <;> simp [hw]
  calc
    1 - failureBound d ≤ P.pr (ForcedMartingaleGood q {i} y) := by simpa [P] using hForced
    _ = P.pr (fun x => ForcedMartingaleGood q {i} y x ∧ P.w x ≠ 0) := hprob
    _ ≤ P.pr (Good q) := FinProb.pr_mono P _ _ (by
      intro x hx
      apply hgoodSupport x
      · simpa [P, forcingLaw] using hx.2
      · exact hx.1)

/-- TeX 03:722–734: integrate the atom-extracted ratio and condition on G.
The conclusion quantifies over all queries, including empty, zero and repeated targets. -/
theorem conditioned_comparison_transfer :
    ∀ᶠ d : ℕ in atTop, ∀ t (q : Fin t → Fin d → ℝ) (h : OrderedInput d t q),
      1 - failureBound d ≤ (sequentialLaw q h.nonneg h.row_sum).pr (Good q) →
      (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        ∀ x, Good q x → Targets S y x → sequentialWeight q x = forcingWeight q S y x *
          (∏ i ∈ S, q i (y i)) * likelihoodFactor q S y x) →
      (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), PositiveDistinctTargets q S y → (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        ∀ x, Good q x → Targets S y x → 0 < likelihoodFactor q S y x ∧
          |Real.log (likelihoodFactor q S y x)| ≤ relativeError d / 4 * S.card) →
      (∀ i y, 0 < q i (y i) →
        1 - failureBound d ≤ (forcingLaw q h.nonneg h.row_sum {i} y).pr (Good q)) →
      ∃ hG : 0 < (sequentialLaw q h.nonneg h.row_sum).pr (Good q),
        (∀ x, (conditionedLaw q h hG).w x ≠ 0 → Function.Injective x) ∧
        (∀ (S : Finset (Fin t)) (y : Fin t → Fin d), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
          (conditionedLaw q h hG).pr (fun x => ∀ i ∈ S, x i = y i) ≤
            Real.exp (relativeError d * S.card) * ∏ i ∈ S, q i (y i)) ∧
        (∀ i y, |(conditionedLaw q h hG).pr (fun x => x i = y) - q i y| ≤
          relativeError d * q i y) := by
  have huTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (0.1 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0.1 : ℝ) > 0)).comp
      tendsto_natCast_atTop_atTop
  have hfailTail : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ (0.1 : ℝ)) ^ (0.9 : ℝ) *
        Real.exp (-((n : ℝ) ^ (0.1 : ℝ)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (0.9 : ℝ) (1 : ℝ) (by norm_num : (0 : ℝ) < 1)).comp huTop
    simpa [Function.comp_def] using h
  have hsmallFailEvent := hfailTail.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [hsmallFailEvent, eventually_ge_atTop 100] with d hsmallFail hd100
  intro t q hq hseqGood hIdentity hLog hForcedGood
  classical
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 100) hq.dimension
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hd100 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
  have hdeltaPos : 0 < relativeError d := by
    unfold relativeError
    exact Real.rpow_pos_of_pos hd _
  have hdeltaLeOne : relativeError d ≤ 1 := by
    unfold relativeError
    exact Real.rpow_le_one_of_one_le_of_nonpos hd100 (by norm_num)
  have hpow09 : (d : ℝ) ^ (0.09 : ℝ) =
      ((d : ℝ) ^ (0.1 : ℝ)) ^ (0.9 : ℝ) := by
    rw [← Real.rpow_mul hd.le]
    norm_num
  have hpowCancel : (d : ℝ) ^ (0.09 : ℝ) *
      (d : ℝ) ^ (-(0.09 : ℝ)) = 1 := by
    rw [← Real.rpow_add hd]
    norm_num
  have hfailScaled : failureBound d * (d : ℝ) ^ (0.09 : ℝ) ≤ 1 / 8 := by
    unfold failureBound
    rw [hpow09]
    simpa [mul_comm] using hsmallFail.le
  have hfailureSmall : failureBound d ≤ relativeError d / 8 := by
    calc
      failureBound d = failureBound d * 1 := by ring
      _ = failureBound d *
          ((d : ℝ) ^ (0.09 : ℝ) * (d : ℝ) ^ (-(0.09 : ℝ))) := by
            rw [hpowCancel]
      _ = (failureBound d * (d : ℝ) ^ (0.09 : ℝ)) *
            (d : ℝ) ^ (-(0.09 : ℝ)) := by ring
      _ ≤ (1 / 8 : ℝ) * (d : ℝ) ^ (-(0.09 : ℝ)) :=
        mul_le_mul_of_nonneg_right hfailScaled (Real.rpow_nonneg hd.le _)
      _ = relativeError d / 8 := by rw [relativeError]; ring
  have hfailNonneg : 0 ≤ failureBound d := Real.exp_nonneg _
  have hremainPos : 0 < 1 - failureBound d := by
    have hδdiv : relativeError d / 8 ≤ 1 / 8 :=
      div_le_div_of_nonneg_right hdeltaLeOne (by norm_num)
    have hle : failureBound d ≤ 1 / 8 := hfailureSmall.trans hδdiv
    linarith
  let Pseq : FinProb (Path t d) := sequentialLaw q hq.nonneg hq.row_sum
  let lab : Path t d → (Fin t → Fin d) := fun x =>
    readLabels (by have := hq.dimension; omega) x
  have hGpos : 0 < Pseq.pr (Good q) := lt_of_lt_of_le hremainPos hseqGood
  have hseqGood' : 1 - failureBound d ≤ Pseq.pr (Good q) := by
    simpa [Pseq] using hseqGood
  let hG : 0 < Pseq.pr (Good q) := hGpos
  let Pcond : FinProb (Path t d) := FinProb.cond Pseq (Good q) hG
  let Q : FinProb (Fin t → Fin d) := FinProb.map Pcond lab
  have hGupper : Pseq.pr (Good q) ≤ 1 := by
    calc
      Pseq.pr (Good q) ≤ Pseq.pr (fun _ => True) :=
        FinProb.pr_mono Pseq _ _ (by intro x hx; trivial)
      _ = 1 := by simp [FinProb.pr, Pseq.sum_eq_one]
  have hdenInv : (Pseq.pr (Good q))⁻¹ ≤
      Real.exp (relativeError d / 4) := by
    have hfailHalf : failureBound d ≤ 1 / 2 := by
      have hsmall := hfailureSmall
      nlinarith [hdeltaLeOne]
    have hrecip : (1 - failureBound d)⁻¹ ≤ 1 + 2 * failureBound d := by
      have hdiv : 1 / (1 - failureBound d) ≤ 1 + 2 * failureBound d := by
        apply (div_le_iff₀ hremainPos).2
        have hprod : 0 ≤ failureBound d * (1 - 2 * failureBound d) :=
          mul_nonneg hfailNonneg (by linarith [hfailHalf])
        nlinarith [hprod]
      simpa only [one_div] using hdiv
    have hsumSmall : 1 + 2 * failureBound d ≤
        1 + relativeError d / 4 := by
      linarith [hfailureSmall]
    calc
      (Pseq.pr (Good q))⁻¹ ≤ (1 - failureBound d)⁻¹ := by
        simpa only [one_div] using
          (one_div_le_one_div_of_le hremainPos hseqGood')
      _ ≤ 1 + 2 * failureBound d := hrecip
      _ ≤ 1 + relativeError d / 4 := hsumSmall
      _ ≤ Real.exp (relativeError d / 4) := by
        simpa [add_comm] using Real.add_one_le_exp (relativeError d / 4)
  have hcondPathPr (E : Path t d → Prop) :
      Pcond.pr E = Pseq.pr (fun x => Good q x ∧ E x) / Pseq.pr (Good q) := by
    classical
    unfold Pcond
    simp only [FinProb.pr, FinProb.cond]
    rw [Finset.sum_div (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hg : Good q x <;> by_cases he : E x <;> simp [hg, he]
  have hcondMapPr (E : (Fin t → Fin d) → Prop) :
      Q.pr E = Pseq.pr (fun x => Good q x ∧ E (lab x)) / Pseq.pr (Good q) := by
    classical
    calc
        Q.pr E = Q.expect (fun f => if E f then 1 else 0) := by
          unfold FinProb.pr FinProb.expect
          apply Finset.sum_congr rfl
          intro f hf
          by_cases he : E f <;> simp [he]
        _ = Pcond.expect (fun x => if E (lab x) then 1 else 0) :=
          FinProb.map_expect Pcond lab _
        _ = Pcond.pr (fun x => E (lab x)) := by
          unfold FinProb.pr FinProb.expect
          apply Finset.sum_congr rfl
          intro x hx
          by_cases he : E (lab x) <;> simp [he]
        _ = Pseq.pr (fun x => Good q x ∧ E (lab x)) /
            Pseq.pr (Good q) := hcondPathPr (fun x => E (lab x))
  have hreadTargets (S : Finset (Fin t)) (y₀ : Fin t → Fin d) (x : Path t d)
      (hx : Good q x) :
      (∀ i ∈ S, lab x i = y₀ i) ↔ Targets S y₀ x := by
    constructor
    · intro he i hi
      rcases hx.1.1 i i.isLt with ⟨z, hz⟩
      have hzy : z = y₀ i := by
        simpa [lab, readLabels, hz] using he i hi
      simpa [hzy] using hz
    · intro ht i hi
      rcases hx.1.1 i i.isLt with ⟨z, hz⟩
      have hzy : z = y₀ i := Option.some.inj (hz.symm.trans (ht i hi))
      simp [lab, readLabels, hz, hzy]
  have hQInjective (f : Fin t → Fin d) (hw : Q.w f ≠ 0) : Function.Injective f := by
    classical
    have hex : ∃ x, lab x = f ∧ Pcond.w x ≠ 0 := by
      by_contra hno
      have hzero : (∑ x, if lab x = f then Pcond.w x else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        by_cases heq : lab x = f
        · have hz : Pcond.w x = 0 := by
            by_contra hne
            exact hno ⟨x, heq, hne⟩
          simp [heq, hz]
        · simp [heq]
      apply hw
      change (∑ x, if lab x = f then Pcond.w x else 0) = 0
      exact hzero
    rcases hex with ⟨x, hxf, hwx⟩
    have hxGood : Good q x := by
      by_contra hnot
      have hz : Pcond.w x = 0 := by
        simp [Pcond, FinProb.cond, hnot]
      exact hwx hz
    intro a b hab
    have hsome (k : Fin t) : x k = some (lab x k) := by
      rcases hxGood.1.1 k k.isLt with ⟨z, hz⟩
      simp [lab, readLabels, hz]
    have hEq : x a = x b := by
      rw [hsome a, hsome b, hxf, hab]
    exact hxGood.1.2 a b a.isLt b.isLt hEq
  have hprLeOne (R : FinProb (Path t d)) (E : Path t d → Prop) :
      R.pr E ≤ 1 := by
    calc
      R.pr E ≤ R.pr (fun _ => True) :=
        FinProb.pr_mono R _ _ (by intro x hx; trivial)
      _ = 1 := by simp [FinProb.pr, R.sum_eq_one]
  have hforceTarget (i₀ : Fin t) (z : Fin d) (x : Path t d)
      (hxGood : Good q x) (hw : forcingWeight q {i₀} (fun _ => z) x ≠ 0) :
      x i₀ = some z := by
    have hfactor : forcingStepWeight q {i₀} (fun _ => z) x i₀ (x i₀) ≠ 0 := by
      unfold forcingWeight at hw
      exact (Finset.prod_ne_zero_iff.mp hw) i₀ (Finset.mem_univ i₀)
    have hsome : ∃ w, x i₀ = some w := hxGood.1.1 i₀ i₀.isLt
    rcases hsome with ⟨w, hxi⟩
    by_contra hne
    have hiMem : i₀ ∈ ({i₀} : Finset (Fin t)) := by simp
    by_cases hactive : PrefixValid x i₀.val ∧
        trackingError q x i₀.val ≤ 1 / 20 ∧ Free x i₀.val z
    · have hz : forcingStepWeight q {i₀} (fun _ => z) x i₀ (x i₀) = 0 := by
        unfold forcingStepWeight
        rw [if_pos hiMem, if_pos hactive]
        simp [hne]
      exact hfactor hz
    · have hz : forcingStepWeight q {i₀} (fun _ => z) x i₀ (x i₀) = 0 := by
        unfold forcingStepWeight
        rw [if_pos hiMem, if_neg hactive]
        simp [hxi]
      exact hfactor hz
  have hforceGoodTarget (i₀ : Fin t) (z : Fin d) :
      (forcingLaw q hq.nonneg hq.row_sum {i₀} (fun _ => z)).pr (Good q) =
      (forcingLaw q hq.nonneg hq.row_sum {i₀} (fun _ => z)).pr
        (fun x => Good q x ∧ x i₀ = some z) := by
    classical
    let R := forcingLaw q hq.nonneg hq.row_sum {i₀} (fun _ => z)
    change R.pr (Good q) = R.pr (fun x => Good q x ∧ x i₀ = some z)
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hg : Good q x
    · by_cases hw : R.w x = 0
      · simp [hw]
      · have htarget := hforceTarget i₀ z x hg (by simpa [R, forcingLaw] using hw)
        simp [hg, hw, htarget]
    · simp [hg]
  have hlikelihoodBounds (S : Finset (Fin t)) (y₀ : Fin t → Fin d)
      (hpos : PositiveDistinctTargets q S y₀)
      (hsize : (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ))
      (x : Path t d) (hx : Good q x) (htargets : Targets S y₀ x) :
      Real.exp (-(relativeError d / 4 * (S.card : ℝ))) ≤
          likelihoodFactor q S y₀ x ∧
        likelihoodFactor q S y₀ x ≤
          Real.exp (relativeError d / 4 * (S.card : ℝ)) := by
    let θ : ℝ := relativeError d / 4 * (S.card : ℝ)
    rcases hLog S y₀ hpos hsize x hx htargets with ⟨hLpos, hlog⟩
    have habs := abs_le.mp hlog
    constructor
    · have he := Real.exp_le_exp.mpr habs.1
      rw [Real.exp_log hLpos] at he
      exact he
    · have he := Real.exp_le_exp.mpr habs.2
      rw [Real.exp_log hLpos] at he
      exact he
  have hseqTargetBounds (S : Finset (Fin t)) (y₀ : Fin t → Fin d)
      (hpos : PositiveDistinctTargets q S y₀)
      (hsize : (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ)) :
      let qprod : ℝ := ∏ i ∈ S, q i (y₀ i)
      let θ : ℝ := relativeError d / 4 * (S.card : ℝ)
      let E : Path t d → Prop := fun x => Good q x ∧ Targets S y₀ x
      qprod * Real.exp (-θ) *
          (forcingLaw q hq.nonneg hq.row_sum S y₀).pr E ≤ Pseq.pr E ∧
        Pseq.pr E ≤ qprod * Real.exp θ *
          (forcingLaw q hq.nonneg hq.row_sum S y₀).pr E := by
    classical
    dsimp
    let qprod : ℝ := ∏ i ∈ S, q i (y₀ i)
    let θ : ℝ := relativeError d / 4 * (S.card : ℝ)
    let E : Path t d → Prop := fun x => Good q x ∧ Targets S y₀ x
    let R : FinProb (Path t d) := forcingLaw q hq.nonneg hq.row_sum S y₀
    have hqprod : 0 ≤ qprod := by
      dsimp [qprod]
      apply Finset.prod_nonneg
      intro i hi
      exact hq.nonneg i (y₀ i)
    have hweighted : Pseq.pr E = qprod *
        (∑ x, if E x then forcingWeight q S y₀ x *
          likelihoodFactor q S y₀ x else 0) := by
      classical
      unfold FinProb.pr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases he : E x
      · rcases he with ⟨hgood, htargets⟩
        simp [E, hgood, htargets]
        change sequentialWeight q x = qprod *
          (forcingWeight q S y₀ x * likelihoodFactor q S y₀ x)
        rw [hIdentity S y₀ hpos hsize x hgood htargets]
        ring
      · simp [E, he]
    have hsumUpper :
        (∑ x, if E x then forcingWeight q S y₀ x * likelihoodFactor q S y₀ x else 0) ≤
          Real.exp θ * R.pr E := by
      calc
        _ ≤ ∑ x, if E x then Real.exp θ * forcingWeight q S y₀ x else 0 := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases he : E x
          · rcases he with ⟨hgood, htargets⟩
            simp [E, hgood, htargets]
            have hL := (hlikelihoodBounds S y₀ hpos hsize x hgood htargets).2
            calc
              forcingWeight q S y₀ x * likelihoodFactor q S y₀ x ≤
                  forcingWeight q S y₀ x * Real.exp θ :=
                mul_le_mul_of_nonneg_left hL (R.nonneg x)
              _ = Real.exp θ * forcingWeight q S y₀ x := by ring
          · simp [E, he]
        _ = Real.exp θ * R.pr E := by
          unfold FinProb.pr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases he : E x <;> simp [E, he, R, forcingLaw, mul_comm]
    have hsumLower :
        Real.exp (-θ) * R.pr E ≤
          ∑ x, if E x then forcingWeight q S y₀ x * likelihoodFactor q S y₀ x else 0 := by
      calc
        Real.exp (-θ) * R.pr E =
            ∑ x, if E x then Real.exp (-θ) * forcingWeight q S y₀ x else 0 := by
              unfold FinProb.pr
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              by_cases he : E x <;> simp [E, he, R, forcingLaw, mul_comm]
        _ ≤ ∑ x, if E x then forcingWeight q S y₀ x *
              likelihoodFactor q S y₀ x else 0 := by
                apply Finset.sum_le_sum
                intro x hx
                by_cases he : E x
                · rcases he with ⟨hgood, htargets⟩
                  simp [E, hgood, htargets]
                  have hL := (hlikelihoodBounds S y₀ hpos hsize x hgood htargets).1
                  calc
                    Real.exp (-θ) * forcingWeight q S y₀ x =
                        forcingWeight q S y₀ x * Real.exp (-θ) := by ring
                    _ ≤ forcingWeight q S y₀ x * likelihoodFactor q S y₀ x :=
                      mul_le_mul_of_nonneg_left hL (R.nonneg x)
                · simp [E, he]
    constructor
    · calc
        qprod * Real.exp (-θ) * R.pr E =
            qprod * (Real.exp (-θ) * R.pr E) := by ring
        _ ≤ qprod * (∑ x, if E x then forcingWeight q S y₀ x *
              likelihoodFactor q S y₀ x else 0) :=
                mul_le_mul_of_nonneg_left hsumLower hqprod
        _ = Pseq.pr E := hweighted.symm
    · calc
        Pseq.pr E = qprod * (∑ x, if E x then forcingWeight q S y₀ x *
            likelihoodFactor q S y₀ x else 0) := hweighted
        _ ≤ qprod * (Real.exp θ * R.pr E) :=
          mul_le_mul_of_nonneg_left hsumUpper hqprod
        _ = qprod * Real.exp θ * R.pr E := by ring
  have hjointPositive (S : Finset (Fin t)) (y₀ : Fin t → Fin d)
      (hpos : PositiveDistinctTargets q S y₀)
      (hsize : (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ))
      (hcard : 0 < S.card) :
      Q.pr (fun f => ∀ i ∈ S, f i = y₀ i) ≤
        Real.exp (relativeError d * S.card) * ∏ i ∈ S, q i (y₀ i) := by
    classical
    let qprod : ℝ := ∏ i ∈ S, q i (y₀ i)
    let θ : ℝ := relativeError d / 4 * (S.card : ℝ)
    let E : Path t d → Prop := fun x => Good q x ∧ Targets S y₀ x
    let F : (Fin t → Fin d) → Prop := fun f => ∀ i ∈ S, f i = y₀ i
    let R : FinProb (Path t d) := forcingLaw q hq.nonneg hq.row_sum S y₀
    have hpre : (fun x => Good q x ∧ F (lab x)) = E := by
      funext x
      apply propext
      by_cases hg : Good q x
      · simpa [E, F, hg] using hreadTargets S y₀ x hg
      · simp [hg, E]
    have hcondEq : Q.pr F = Pseq.pr E / Pseq.pr (Good q) := by
      calc
        Q.pr F = Pseq.pr (fun x => Good q x ∧ F (lab x)) /
            Pseq.pr (Good q) := hcondMapPr F
        _ = Pseq.pr E / Pseq.pr (Good q) := by rw [hpre]
    have hbounds := hseqTargetBounds S y₀ hpos hsize
    have hnumUpper : Pseq.pr E ≤ qprod * Real.exp θ := by
      have hup : Pseq.pr E ≤ qprod * Real.exp θ * R.pr E := by
        simpa [E, qprod, θ, R] using hbounds.2
      have hcoef : 0 ≤ qprod * Real.exp θ := by
        have hqp : 0 ≤ qprod := by
          dsimp [qprod]
          apply Finset.prod_nonneg
          intro i hi
          exact hq.nonneg i (y₀ i)
        exact mul_nonneg hqp (Real.exp_nonneg _)
      calc
        Pseq.pr E ≤ qprod * Real.exp θ * R.pr E := hup
        _ ≤ qprod * Real.exp θ * 1 :=
          mul_le_mul_of_nonneg_left (hprLeOne R E) hcoef
        _ = qprod * Real.exp θ := by ring
    have hqprod : 0 ≤ qprod := by
      dsimp [qprod]
      apply Finset.prod_nonneg
      intro i hi
      exact hq.nonneg i (y₀ i)
    have hcardOne : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hcard)
    have htheta : θ + relativeError d / 4 ≤ relativeError d * (S.card : ℝ) := by
      dsimp [θ]
      nlinarith [hdeltaPos, hcardOne]
    calc
      Q.pr F = Pseq.pr E / Pseq.pr (Good q) := hcondEq
      _ ≤ (qprod * Real.exp θ) / Pseq.pr (Good q) :=
        div_le_div_of_nonneg_right hnumUpper hGpos.le
      _ = qprod * Real.exp θ * (Pseq.pr (Good q))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ qprod * Real.exp θ * Real.exp (relativeError d / 4) :=
        mul_le_mul_of_nonneg_left hdenInv (mul_nonneg hqprod (Real.exp_nonneg _))
      _ = qprod * Real.exp (θ + relativeError d / 4) := by
        calc
          qprod * Real.exp θ * Real.exp (relativeError d / 4) =
              qprod * (Real.exp θ * Real.exp (relativeError d / 4)) := by ring
          _ = qprod * Real.exp (θ + relativeError d / 4) := by rw [← Real.exp_add]
      _ ≤ qprod * Real.exp (relativeError d * (S.card : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr htheta) hqprod
      _ = Real.exp (relativeError d * S.card) *
            ∏ i ∈ S, q i (y₀ i) := by
              simp [qprod, mul_comm]
  have hseqEventZero (S : Finset (Fin t)) (y₀ : Fin t → Fin d)
      (hnot : ¬ PositiveDistinctTargets q S y₀) :
      Pseq.pr (fun x => Good q x ∧ Targets S y₀ x) = 0 := by
    classical
    unfold FinProb.pr
    apply Finset.sum_eq_zero
    intro x hx
    by_cases he : Good q x ∧ Targets S y₀ x
    · rcases he with ⟨hgood, htargets⟩
      by_cases hAtoms : ∀ i ∈ S, 0 < q i (y₀ i)
      · have hnotInj : ¬ Set.InjOn y₀ (↑S : Set (Fin t)) := by
          intro hInj
          exact hnot ⟨hAtoms, hInj⟩
        have hExists : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ y₀ a = y₀ b := by
          by_contra hNo
          apply hnotInj
          intro a ha b hb hy
          by_contra hab
          exact hNo ⟨a, ha, b, hb, hab, hy⟩
        rcases hExists with ⟨a, ha, b, hb, hab, hy⟩
        have haS : a ∈ S := by simpa using ha
        have hbS : b ∈ S := by simpa using hb
        have hxa := htargets a haS
        have hxb := htargets b hbS
        have hEq : x a = x b := by rw [hxa, hxb, hy]
        have := hgood.1.2 a b a.isLt b.isLt hEq
        exact (hab this).elim
      · push_neg at hAtoms
        rcases hAtoms with ⟨a, ha, hnotPos⟩
        have hqzero : q a (y₀ a) = 0 :=
          le_antisymm hnotPos (hq.nonneg a (y₀ a))
        have hstepzero : ordinaryWeight q x a ∅ (x a) = 0 := by
          rw [htargets a ha]
          unfold ordinaryWeight
          by_cases hactive : PrefixValid x a.val ∧
              trackingError q x a.val ≤ 1 / 20 ∧
                0 < availableMass q x a ∅
          · rw [if_pos hactive]
            simp [hqzero]
          · rw [if_neg hactive]
            simp
        have hseqzero : sequentialWeight q x = 0 := by
          unfold sequentialWeight
          exact Finset.prod_eq_zero (Finset.mem_univ a) hstepzero
        simp [hgood, htargets, Pseq, sequentialLaw, hseqzero]
    · simp [he]
  refine ⟨hGpos, hQInjective, ?_, ?_⟩
  · intro S y₀ hsize
    by_cases hcard0 : S.card = 0
    · have hS : S = ∅ := Finset.card_eq_zero.mp hcard0
      subst S
      have hQtotal : Q.pr (fun _ => True) = 1 := by
        unfold FinProb.pr
        simp [Q.sum_eq_one]
      simpa [Q, conditionedLaw, Pcond, Pseq, lab] using hQtotal.le
    · have hcard : 0 < S.card := Nat.pos_of_ne_zero hcard0
      by_cases hpos : PositiveDistinctTargets q S y₀
      · exact hjointPositive S y₀ hpos hsize hcard
      · have hzero := hseqEventZero S y₀ hpos
        have hpre :
            (fun x => Good q x ∧ (∀ i ∈ S, lab x i = y₀ i)) =
              (fun x => Good q x ∧ Targets S y₀ x) := by
          funext x
          apply propext
          by_cases hg : Good q x
          · simpa [hg, hreadTargets S y₀ x hg]
          · simp [hg]
        have hQzero : Q.pr (fun f => ∀ i ∈ S, f i = y₀ i) = 0 := by
          rw [hcondMapPr, hpre, hzero]
          simp
        have hRhs : 0 ≤ Real.exp (relativeError d * S.card) *
            ∏ i ∈ S, q i (y₀ i) := by
          apply mul_nonneg (Real.exp_nonneg _)
          apply Finset.prod_nonneg
          intro i hi
          exact hq.nonneg i (y₀ i)
        change Q.pr (fun f => ∀ i ∈ S, f i = y₀ i) ≤ _
        rw [hQzero]
        exact hRhs
  · intro i z
    by_cases hqz : 0 < q i z
    · let S : Finset (Fin t) := {i}
      let y₀ : Fin t → Fin d := fun _ => z
      let E₀ : Path t d → Prop := fun x => Good q x ∧ x i = some z
      let R : FinProb (Path t d) := forcingLaw q hq.nonneg hq.row_sum S y₀
      have hposS : PositiveDistinctTargets q S y₀ := by
        constructor
        · intro j hj
          have hji : j = i := by simpa [S] using hj
          subst j
          exact hqz
        · intro a ha b hb hab
          have hai : a = i := by simpa [S] using ha
          have hbi : b = i := by simpa [S] using hb
          subst a
          subst b
          rfl
      have hsizeS : (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) := by
        have hpow : 1 ≤ (d : ℝ) ^ (0.025 : ℝ) :=
          Real.one_le_rpow hd100 (by norm_num)
        simpa [S] using hpow
      have hBounds := hseqTargetBounds S y₀ hposS hsizeS
      have hnumLower : q i z * Real.exp (-(relativeError d / 4)) * R.pr E₀ ≤
          Pseq.pr E₀ := by
        simpa [S, y₀, E₀, Targets, Finset.card_singleton, mul_assoc, mul_comm]
          using hBounds.1
      have hnumUpper : Pseq.pr E₀ ≤
          q i z * Real.exp (relativeError d / 4) * R.pr E₀ := by
        simpa [S, y₀, E₀, Targets, Finset.card_singleton, mul_assoc, mul_comm]
          using hBounds.2
      have hforceEq :
          R.pr (Good q) = R.pr E₀ := by
        have h := hforceGoodTarget i z
        simpa [R, S, y₀, E₀] using h
      have hforceLower : 1 - failureBound d ≤ R.pr E₀ := by
        calc
          1 - failureBound d ≤ R.pr (Good q) := by
            simpa [R, S, y₀] using hForcedGood i y₀ hqz
          _ = R.pr E₀ := hforceEq
      have hforceUpper : R.pr E₀ ≤ 1 := hprLeOne R E₀
      have hpreMarg :
          (fun x => Good q x ∧ lab x i = z) = E₀ := by
        funext x
        apply propext
        by_cases hg : Good q x
        · have hreadOne : lab x i = z ↔ x i = some z := by
            constructor
            · intro hlabel
              rcases hg.1.1 i i.isLt with ⟨w, hw⟩
              have hwEq : w = z := by
                simpa [lab, readLabels, hw] using hlabel
              simpa [hwEq] using hw
            · intro hlabel
              simpa [lab, readLabels, hlabel]
          simp [E₀, hg, hreadOne]
        · simp [E₀, hg]
      have hp : (Q.pr (fun f => f i = z)) = Pseq.pr E₀ / Pseq.pr (Good q) := by
        calc
          Q.pr (fun f => f i = z) =
              Pseq.pr (fun x => Good q x ∧ lab x i = z) / Pseq.pr (Good q) :=
            hcondMapPr _
          _ = Pseq.pr E₀ / Pseq.pr (Good q) := by rw [hpreMarg]
      have hnumNonneg : 0 ≤ Pseq.pr E₀ := by
        unfold FinProb.pr
        apply Finset.sum_nonneg
        intro x hx
        split_ifs
        · exact Pseq.nonneg x
        · exact le_rfl
      have hpDiv : Pseq.pr E₀ ≤ Pseq.pr E₀ / Pseq.pr (Good q) := by
        apply (le_div_iff₀ hGpos).2
        calc
          Pseq.pr E₀ * Pseq.pr (Good q) ≤ Pseq.pr E₀ * 1 :=
            mul_le_mul_of_nonneg_left hGupper hnumNonneg
          _ = Pseq.pr E₀ := by ring
      have hlow : q i z * (1 - relativeError d) ≤ Q.pr (fun f => f i = z) := by
        have hcoef : 0 ≤ q i z * Real.exp (-(relativeError d / 4)) :=
          mul_nonneg (hq.nonneg i z) (Real.exp_nonneg _)
        have hnumLower' :
            q i z * Real.exp (-(relativeError d / 4)) * (1 - failureBound d) ≤
              Pseq.pr E₀ :=
          le_trans (mul_le_mul_of_nonneg_left hforceLower hcoef) hnumLower
        have hfailHalf : failureBound d ≤ 1 / 2 := by
          nlinarith [hfailureSmall, hdeltaLeOne]
        have hfactorLower :
            1 - relativeError d ≤
              Real.exp (-(relativeError d / 4)) * (1 - failureBound d) := by
          have hExp := Real.one_sub_le_exp_neg (relativeError d / 4)
          have hremainNonneg : 0 ≤ 1 - failureBound d := by linarith [hfailHalf]
          have hmult := mul_le_mul_of_nonneg_right hExp hremainNonneg
          have hcross : 0 ≤ (relativeError d / 4) * failureBound d :=
            mul_nonneg (by positivity) hfailNonneg
          have hsum : 1 - relativeError d ≤
              (1 - relativeError d / 4) * (1 - failureBound d) := by
            nlinarith [hcross, hfailureSmall]
          exact hsum.trans hmult
        have hlowNum : q i z * (1 - relativeError d) ≤ Pseq.pr E₀ := by
          calc
            q i z * (1 - relativeError d) ≤
                q i z * (Real.exp (-(relativeError d / 4)) * (1 - failureBound d)) :=
              mul_le_mul_of_nonneg_left hfactorLower (hq.nonneg i z)
            _ = (q i z * Real.exp (-(relativeError d / 4))) *
                  (1 - failureBound d) := by ring
            _ ≤ Pseq.pr E₀ := by
                  convert hnumLower' using 1 <;> ring
        calc
          q i z * (1 - relativeError d) ≤ Pseq.pr E₀ := hlowNum
          _ ≤ Pseq.pr E₀ / Pseq.pr (Good q) := hpDiv
          _ = Q.pr (fun f => f i = z) := hp.symm
      have hexpUpper : Real.exp (relativeError d / 2) ≤ 1 + relativeError d := by
        have hx : 0 ≤ relativeError d / 2 := by positivity
        have hx2 : relativeError d / 2 < 2 := by linarith [hdeltaLeOne]
        calc
          Real.exp (relativeError d / 2) ≤
              (2 + relativeError d / 2) / (2 - relativeError d / 2) :=
            Real.exp_le_two_add_div_two_sub hx hx2
          _ ≤ 1 + relativeError d := by
            have hden : 0 < 2 - relativeError d / 2 := by linarith [hdeltaLeOne]
            apply (div_le_iff₀ hden).2
            nlinarith [hdeltaLeOne]
      have hupp : Q.pr (fun f => f i = z) ≤ q i z * (1 + relativeError d) := by
        have hnumDiv : Pseq.pr E₀ / Pseq.pr (Good q) ≤
            (q i z * Real.exp (relativeError d / 4) * R.pr E₀) /
              Pseq.pr (Good q) :=
          div_le_div_of_nonneg_right hnumUpper hGpos.le
        have hRatio :
            (q i z * Real.exp (relativeError d / 4) * R.pr E₀) /
                Pseq.pr (Good q) ≤
              q i z * Real.exp (relativeError d / 2) := by
          calc
            _ = q i z * Real.exp (relativeError d / 4) * R.pr E₀ *
                (Pseq.pr (Good q))⁻¹ := by rw [div_eq_mul_inv]
            _ ≤ q i z * Real.exp (relativeError d / 4) *
                Real.exp (relativeError d / 4) := by
                  have hcoef : 0 ≤ q i z * Real.exp (relativeError d / 4) :=
                    mul_nonneg (hq.nonneg i z) (Real.exp_nonneg _)
                  calc
                    q i z * Real.exp (relativeError d / 4) *
                        R.pr E₀ * (Pseq.pr (Good q))⁻¹ =
                        (q i z * Real.exp (relativeError d / 4)) *
                          (R.pr E₀ * (Pseq.pr (Good q))⁻¹) := by ring
                    _ ≤ (q i z * Real.exp (relativeError d / 4)) *
                          (1 * Real.exp (relativeError d / 4)) :=
                      mul_le_mul_of_nonneg_left
                        (mul_le_mul hforceUpper hdenInv (by positivity) (by positivity)) hcoef
                    _ = q i z * Real.exp (relativeError d / 4) *
                          Real.exp (relativeError d / 4) := by ring
            _ = q i z * Real.exp (relativeError d / 2) := by
                  calc
                    q i z * Real.exp (relativeError d / 4) *
                        Real.exp (relativeError d / 4) =
                        q i z * (Real.exp (relativeError d / 4) *
                          Real.exp (relativeError d / 4)) := by ring
                    _ = q i z * Real.exp (relativeError d / 4 + relativeError d / 4) := by
                      rw [← Real.exp_add]
                    _ = q i z * Real.exp (relativeError d / 2) := by congr 2 <;> ring
        calc
          Q.pr (fun f => f i = z) = Pseq.pr E₀ / Pseq.pr (Good q) := hp
          _ ≤ _ := hnumDiv
          _ ≤ q i z * Real.exp (relativeError d / 2) := hRatio
          _ ≤ q i z * (1 + relativeError d) := by
            calc
              q i z * Real.exp (relativeError d / 2) ≤
                  q i z * (1 + relativeError d) :=
                mul_le_mul_of_nonneg_left hexpUpper (hq.nonneg i z)
              _ = _ := rfl
      have hdiff : |Q.pr (fun f => f i = z) - q i z| ≤
          relativeError d * q i z := by
        have hlow' : q i z - relativeError d * q i z ≤
            Q.pr (fun f => f i = z) := by nlinarith [hlow]
        have hupp' : Q.pr (fun f => f i = z) ≤
            q i z + relativeError d * q i z := by nlinarith [hupp]
        apply (abs_le).2
        constructor <;> linarith [hlow', hupp']
      simpa [Q, conditionedLaw, Pcond, lab] using hdiff
    · have hqzero : q i z = 0 := le_antisymm (le_of_not_gt hqz) (hq.nonneg i z)
      have hzeroSeq : Pseq.pr (fun x => Good q x ∧ x i = some z) = 0 := by
        classical
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro x hx
        by_cases he : Good q x ∧ x i = some z
        · rcases he with ⟨hg, hxi⟩
          have hstepzero : ordinaryWeight q x i ∅ (x i) = 0 := by
            rw [hxi]
            unfold ordinaryWeight
            by_cases hactive : PrefixValid x i.val ∧
                trackingError q x i.val ≤ 1 / 20 ∧
                  0 < availableMass q x i ∅
            · rw [if_pos hactive]
              simp [hqzero]
            · rw [if_neg hactive]
              simp
          have hseqzero : sequentialWeight q x = 0 := by
            unfold sequentialWeight
            exact Finset.prod_eq_zero (Finset.mem_univ i) hstepzero
          simp [hg, hxi, hseqzero, Pseq, sequentialLaw]
        · simp [he]
      have hmapzero : Q.pr (fun f => f i = z) = 0 := by
        rw [hcondMapPr]
        have hpre : (fun x => Good q x ∧ lab x i = z) =
            (fun x => Good q x ∧ x i = some z) := by
          funext x
          apply propext
          by_cases hg : Good q x
          · have hreadOneZero : lab x i = z ↔ x i = some z := by
              constructor
              · intro hz
                rcases hg.1.1 i i.isLt with ⟨w, hw⟩
                have hwEq : w = z := by simpa [lab, readLabels, hw] using hz
                simpa [hwEq] using hw
              · intro hz
                simp [lab, readLabels, hz]
            simp [hg, hreadOneZero]
          · simp [hg]
        rw [hpre, hzeroSeq]
        simp
      simpa [hqzero, hmapzero]

end HypercubeRamsey.Injection
