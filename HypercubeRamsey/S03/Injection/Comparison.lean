import HypercubeRamsey.S03.Injection.Sampler

set_option maxHeartbeats 0

/-!
# Lemma 3.9, the forcing comparison (TeX 03:695–734)

The likelihood identity extracts the target atom product before any failure
probability is used. Single-target forcing has its own concentration claim.
Zero atoms, repeated targets and the empty query are handled in the final
finite comparison node, not by taking a logarithm of a zero atom.
-/

namespace HypercubeRamsey.Injection

open Filter
open scoped BigOperators

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
  sorry

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
  sorry

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
  sorry

end HypercubeRamsey.Injection
