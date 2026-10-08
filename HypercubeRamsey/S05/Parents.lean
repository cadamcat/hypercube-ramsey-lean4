import HypercubeRamsey.S05.Parameters

/-!
# D5.2 and L5.1a: parents and stream segments

The parent prior interface is deliberately independent of the construction that supplies it.  A Section 6
caller can replace the parent sampling law while keeping the atom-cap hypotheses used by the later estimates.
-/

namespace HypercubeRamsey

open Classical

/-- A column is good for a tag when its colour degree is at least `0.95`. -/
def GoodColumn5 {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) : Prop :=
  (95 : ℝ) / 100 ≤ colDeg E G μ y

/-- The tag mass for which two proposed parent labels are both good. -/
noncomputable def GoodPairMass5 {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (Λ : FinProb ι) (μ : ι → Law N)
    (y y' : Fin N) : ℝ :=
  ∑ i, if GoodColumn5 E G (μ i) y ∧ GoodColumn5 E G (μ i) y'
    then Λ.w i else 0

/-- Parent labels related at the `χ²/2` threshold. -/
def GoodParentPair5 {N : ℕ} {ι : Type*} [Fintype ι]
    (E : Fin N → Fin N → Prop) (G : Colour) (Λ : FinProb ι) (μ : ι → Law N)
    (χ : ℝ) (y y' : Fin N) : Prop :=
  χ ^ 2 / 2 ≤ GoodPairMass5 E G Λ μ y y'

/-- The parent system selected from the good-pair graph. -/
structure ParentSelection5 (N : ℕ) (Bin : Type*) [Fintype Bin] (χ : ℝ) where
  prior : ParentPrior5 N Bin
  prior_atom_constant : prior.atomConstant = 4 / χ ^ 2
  lab0 : Finset (Fin N)
  lab0_card : χ ^ 2 * N / 4 ≤ (lab0.card : ℝ)
  lab0_atom : ∀ y, y ∉ lab0 → prior.parent.w y = 0
  partnerCount_lower : ∀ v b, v ∈ lab0 → χ ^ 2 * N / 4 ≤
    (prior.partnerSet v b).card

/-- The marginal of one coordinate of a finite word law. -/
noncomputable def wordMarginal5 {N q : ℕ} (P : FinProb (Word5 N q)) (j : Fin q) (x : Fin N) : ℝ :=
  ∑ z, if z j = x then P.w z else 0

/-- One raw stream segment and its unconditioned product reference law. -/
structure StreamSegments5 (n N q : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
    (γ K' a₀ : ℝ) where
  paired : Fin N → Fin N → Prop
  segment : Fin N → Fin N → FinProb (Word5 N q)
  reference : FinProb (Word5 N q)
  segment_density : ∀ x y z, paired x y →
    (segment x y).w z ≤ Real.exp (a₀ * q) * reference.w z
  segment_hits : ∀ x y z, paired x y → (segment x y).w z ≠ 0 →
    ∀ j, Hits E G (z j) x ∧ Hits E G (z j) y
  reference_coordinate_cap : ∀ j x,
    wordMarginal5 reference j x ≤ K' / N
  reference_density : ∀ z,
    reference.w z ≤ Real.exp ((q : ℝ) * (n : ℝ) ^ γ) / (N : ℝ) ^ q

/-- L5.1a (05:40–79): the good-pair construction gives parent atoms, partner sets, and stream-segment bounds;
the partner law of a parent is the same at every bin (05:50–52: `A_w` uniform on the partners of `V₀`).

Only positive-mass tags need satisfy the width and good-column hypotheses; this is the one-shot convention
used by Part B. -/
theorem L5_1a (γ K' χ : ℝ) {n N : ℕ} {ι Bin : Type*} [Fintype ι] [Fintype Bin]
    (p : Params5 γ K' χ) (E : Fin N → Fin N → Prop) (G : Colour)
    (Λ : FinProb ι) (μ : ι → Law N) (hN : 0 < N)
    (hwidth : ∀ i, 0 < Λ.w i → (μ i).WidthLE ((n : ℝ) ^ γ))
    (hbalance : ∀ x, (N : ℝ) * ∑ i, Λ.w i * (μ i).w x ≤ K')
    (hgood : ∀ i, 0 < Λ.w i → χ * N ≤
      ((Finset.univ.filter (fun y => GoodColumn5 E G (μ i) y)).card : ℝ)) :
    ∃ P : ParentSelection5 N Bin χ,
      ∃ S : StreamSegments5 n N p.q0 E G γ K' (p.a 0),
        (∀ v ∈ P.lab0, ∀ b,
          P.prior.partnerSet v b =
            Finset.univ.filter (GoodParentPair5 E G Λ μ χ v)) ∧
        (∀ x y, S.paired x y ↔ GoodParentPair5 E G Λ μ χ x y) ∧
        (∀ v b b', P.prior.partner v b = P.prior.partner v b') := by
  classical
  let goodSet (i : ι) : Finset (Fin N) :=
    Finset.univ.filter (GoodColumn5 E G (μ i))
  let commonSet (i : ι) (x y : Fin N) : Finset (Fin N) :=
    Finset.univ.filter (fun z => Hits E G z x ∧ Hits E G z y)
  have commonMass_lower (i : ι) (x y : Fin N) (hi : 0 < Λ.w i)
      (hxi : GoodColumn5 E G (μ i) x) (hyi : GoodColumn5 E G (μ i) y) :
      (9 : ℝ) / 10 ≤ ∑ z ∈ commonSet i x y, (μ i).w z := by
    have hpoint (z : Fin N) :
        (μ i).w z * (if Hits E G z x ∧ Hits E G z y then 1 else 0) ≥
          (μ i).w z * (if Hits E G z x then 1 else 0) +
            (μ i).w z * (if Hits E G z y then 1 else 0) - (μ i).w z := by
      by_cases hx : Hits E G z x <;> by_cases hy : Hits E G z y <;>
        simp [hx, hy] <;> nlinarith [((μ i).nonneg z)]
    have hsum :
        colDeg E G (μ i) x + colDeg E G (μ i) y - 1 ≤
          ∑ z ∈ commonSet i x y, (μ i).w z := by
      have hfilter :
          (∑ z ∈ commonSet i x y, (μ i).w z) =
            ∑ z, (μ i).w z * (if Hits E G z x ∧ Hits E G z y then 1 else 0) := by
        simp [commonSet, Finset.sum_filter]
      rw [hfilter]
      calc
        colDeg E G (μ i) x + colDeg E G (μ i) y - 1 =
            ∑ z, ((μ i).w z * (if Hits E G z x then 1 else 0) +
              (μ i).w z * (if Hits E G z y then 1 else 0) - (μ i).w z) := by
                simp [colDeg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                  (μ i).sum_eq_one]
        _ ≤ ∑ z, (μ i).w z * (if Hits E G z x ∧ Hits E G z y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro z hz
          exact hpoint z
    have hx := hxi
    have hy := hyi
    unfold GoodColumn5 at hx hy
    nlinarith [hsum]
  have htag_pos : ∃ i, 0 < Λ.w i := by
    by_contra h
    have hle : ∀ i, Λ.w i ≤ 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hle i)
    rw [Λ.sum_eq_one] at hsum
    norm_num at hsum
  obtain ⟨i₀, hi₀⟩ := htag_pos
  have hχ_le_one : χ ≤ 1 := by
    have hgi := hgood i₀ hi₀
    have hcard : ((goodSet i₀).card : ℝ) ≤ N := by
      exact_mod_cast (by simpa using Finset.card_le_univ (goodSet i₀))
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    nlinarith [hgi, hcard, p.hχ]
  have hgood_card (i : ι) (hi : 0 < Λ.w i) :
      χ * N ≤ ((goodSet i).card : ℝ) := by
    have h := hgood i hi
    change χ * N ≤ ((goodSet i).card : ℝ) at h
    exact h
  have hpair_mass_le_one (x y : Fin N) :
      GoodPairMass5 E G Λ μ x y ≤ 1 := by
    unfold GoodPairMass5
    calc
      (∑ i, if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y then Λ.w i else 0) ≤
          ∑ i, Λ.w i := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs <;> simp [Λ.nonneg]
      _ = 1 := Λ.sum_eq_one
  have hpair_sum (i : ι) :
      (∑ x : Fin N, ∑ y : Fin N,
        if x ∈ goodSet i ∧ y ∈ goodSet i then Λ.w i else 0) =
          Λ.w i * (goodSet i).card * (goodSet i).card := by
    have hterm (x y : Fin N) :
        (if x ∈ goodSet i ∧ y ∈ goodSet i then Λ.w i else 0) =
          (Λ.w i * (if x ∈ goodSet i then 1 else 0)) *
            (if y ∈ goodSet i then 1 else 0) := by
      by_cases hx : x ∈ goodSet i <;> by_cases hy : y ∈ goodSet i <;> simp [hx, hy]
    have hcard : (∑ x : Fin N, (if x ∈ goodSet i then (1 : ℝ) else 0)) =
        (goodSet i).card := by simp
    simp_rw [hterm]
    calc
      (∑ x : Fin N, ∑ y : Fin N,
        (Λ.w i * (if x ∈ goodSet i then 1 else 0)) *
          (if y ∈ goodSet i then 1 else 0)) =
          (∑ x : Fin N, Λ.w i * (if x ∈ goodSet i then 1 else 0)) *
            (∑ y : Fin N, if y ∈ goodSet i then 1 else 0) := by
              calc
                _ = ∑ x : Fin N,
                    (Λ.w i * (if x ∈ goodSet i then 1 else 0)) *
                      (∑ y : Fin N, if y ∈ goodSet i then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro x hx
                        rw [Finset.mul_sum]
                _ = (∑ x : Fin N, Λ.w i * (if x ∈ goodSet i then 1 else 0)) *
                      (∑ y : Fin N, if y ∈ goodSet i then 1 else 0) := by rw [Finset.sum_mul]
      _ = Λ.w i * (goodSet i).card * (goodSet i).card := by
          have hxsum : (∑ x : Fin N, Λ.w i * (if x ∈ goodSet i then 1 else 0)) =
              Λ.w i * ∑ x : Fin N, if x ∈ goodSet i then 1 else 0 := by
            rw [Finset.mul_sum]
          rw [hxsum, hcard]
  have hmassTotal_eq :
      (∑ x : Fin N, ∑ y : Fin N, GoodPairMass5 E G Λ μ x y) =
        ∑ i, Λ.w i * (goodSet i).card * (goodSet i).card := by
    unfold GoodPairMass5
    calc
      (∑ x : Fin N, ∑ y : Fin N,
        ∑ i, if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y then Λ.w i else 0) =
          ∑ x : Fin N, ∑ i, ∑ y : Fin N,
            if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y then Λ.w i else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
      _ = ∑ i, ∑ x : Fin N, ∑ y : Fin N,
            if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y then Λ.w i else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ i, Λ.w i * (goodSet i).card * (goodSet i).card := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa [goodSet] using hpair_sum i
  have hmassTotal_lower :
      χ ^ 2 * (N : ℝ) ^ 2 ≤
        ∑ x : Fin N, ∑ y : Fin N, GoodPairMass5 E G Λ μ x y := by
    have hterm (i : ι) :
        Λ.w i * (χ * (N : ℝ)) ^ 2 ≤
          Λ.w i * ((goodSet i).card : ℝ) ^ 2 := by
      by_cases hi : 0 < Λ.w i
      · have hc := hgood_card i hi
        have hsq : (χ * (N : ℝ)) ^ 2 ≤ ((goodSet i).card : ℝ) ^ 2 := by
          have hleft : 0 ≤ χ * (N : ℝ) := mul_nonneg (le_of_lt p.hχ) (Nat.cast_nonneg _)
          have hright : 0 ≤ ((goodSet i).card : ℝ) := Nat.cast_nonneg _
          nlinarith [sq_nonneg (χ * (N : ℝ)), sq_nonneg ((goodSet i).card : ℝ)]
        exact mul_le_mul_of_nonneg_left hsq (Λ.nonneg i)
      · have hz : Λ.w i = 0 := le_antisymm (le_of_not_gt hi) (Λ.nonneg i)
        simp [hz]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hterm i)
    have hsumOne : ∑ i, Λ.w i = 1 := Λ.sum_eq_one
    calc
      χ ^ 2 * (N : ℝ) ^ 2 = (χ * (N : ℝ)) ^ 2 := by ring
      _ = ∑ i, Λ.w i * (χ * (N : ℝ)) ^ 2 := by simp [hsumOne, ← Finset.sum_mul]
      _ ≤ ∑ i, Λ.w i * ((goodSet i).card : ℝ) ^ 2 := hsum
      _ = ∑ i, Λ.w i * (goodSet i).card * (goodSet i).card := by
            apply Finset.sum_congr rfl
            intro i hi
            push_cast
            ring
      _ = ∑ x : Fin N, ∑ y : Fin N, GoodPairMass5 E G Λ μ x y := hmassTotal_eq.symm
  let goodPair (x y : Fin N) := GoodParentPair5 E G Λ μ χ x y
  let degree (x : Fin N) := (Finset.univ.filter fun y => goodPair x y).card
  have hrow_mass (x : Fin N) :
      (∑ y, GoodPairMass5 E G Λ μ x y) ≤
        (degree x : ℝ) + (χ ^ 2 / 2) * (N : ℝ) := by
    letI : DecidablePred (goodPair x) := fun y => Classical.propDecidable _
    letI : DecidablePred (fun y : Fin N => ¬ goodPair x y) := fun y => Classical.propDecidable _
    have hsplit :
        (∑ y, GoodPairMass5 E G Λ μ x y) =
          (∑ y ∈ Finset.univ.filter (goodPair x), GoodPairMass5 E G Λ μ x y) +
            (∑ y ∈ Finset.univ.filter (fun y => ¬ goodPair x y),
              GoodPairMass5 E G Λ μ x y) := by
        classical
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (goodPair x)
          (fun y => GoodPairMass5 E G Λ μ x y)]
    have hgoodpart :
        (∑ y ∈ Finset.univ.filter (goodPair x), GoodPairMass5 E G Λ μ x y) ≤
          (degree x : ℝ) := by
      calc
        _ ≤ ∑ y ∈ Finset.univ.filter (goodPair x), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro y hy
          exact hpair_mass_le_one x y
        _ = (degree x : ℝ) := by simp [degree]
    have hbadpart :
        (∑ y ∈ Finset.univ.filter (fun y => ¬ goodPair x y),
            GoodPairMass5 E G Λ μ x y) ≤ (χ ^ 2 / 2) * (N : ℝ) := by
      calc
        _ ≤ ∑ y ∈ Finset.univ.filter (fun y => ¬ goodPair x y), (χ ^ 2 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro y hy
          have hy' : ¬ (χ ^ 2 / 2 ≤ GoodPairMass5 E G Λ μ x y) := by
            simpa [goodPair, GoodParentPair5] using hy
          exact le_of_lt (lt_of_not_ge hy')
        _ ≤ ∑ y : Fin N, (χ ^ 2 / 2 : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro y hy1 hy2
          positivity
        _ = (χ ^ 2 / 2) * (N : ℝ) := by
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul,
            mul_comm, mul_left_comm, mul_assoc]
    rw [hsplit]
    exact add_le_add hgoodpart hbadpart
  have htotal_upper :
      (∑ x : Fin N, ∑ y : Fin N, GoodPairMass5 E G Λ μ x y) ≤
        (∑ x : Fin N, (degree x : ℝ)) + (χ ^ 2 / 2) * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ x : Fin N, ((degree x : ℝ) + (χ ^ 2 / 2) * (N : ℝ)) :=
        Finset.sum_le_sum (fun x hx => hrow_mass x)
      _ = (∑ x : Fin N, (degree x : ℝ)) + (χ ^ 2 / 2) * (N : ℝ) ^ 2 := by
        rw [Finset.sum_add_distrib]
        simp [Fintype.card_fin]
        ring
  have hdegree_sum_lower :
      χ ^ 2 / 2 * (N : ℝ) ^ 2 ≤ ∑ x : Fin N, (degree x : ℝ) := by
    nlinarith [hmassTotal_lower, htotal_upper]
  let lab0 : Finset (Fin N) := Finset.univ.filter (fun x =>
    χ ^ 2 * (N : ℝ) / 4 ≤ (degree x : ℝ))
  have hdegree_le_N (x : Fin N) : (degree x : ℝ) ≤ N := by
    have hc : degree x ≤ N := by
      simpa [degree] using Finset.card_le_univ (Finset.univ.filter fun y => goodPair x y)
    exact_mod_cast hc
  have hB_nonneg : 0 ≤ χ ^ 2 * (N : ℝ) / 4 := by positivity
  have hdegree_sum_upper :
      (∑ x : Fin N, (degree x : ℝ)) ≤
        (lab0.card : ℝ) * N + N * (χ ^ 2 * (N : ℝ) / 4) := by
    have hpoint (x : Fin N) :
        (degree x : ℝ) ≤
          χ ^ 2 * (N : ℝ) / 4 + (if x ∈ lab0 then (N : ℝ) else 0) := by
      by_cases hx : x ∈ lab0
      · have hNdeg := hdegree_le_N x
        simp only [hx, if_pos]
        nlinarith [hB_nonneg]
      · have hlow : (degree x : ℝ) ≤ χ ^ 2 * (N : ℝ) / 4 := by
          have hx' : ¬ χ ^ 2 * (N : ℝ) / 4 ≤ (degree x : ℝ) := by
            simpa [lab0, Finset.mem_filter] using hx
          exact le_of_not_ge hx'
        simpa [hx] using hlow
    have hsumPoint := Finset.sum_le_sum (s := Finset.univ) (fun x hx => hpoint x)
    have hsumIte :
        (∑ x : Fin N, (if x ∈ lab0 then (N : ℝ) else 0)) =
          (lab0.card : ℝ) * N := by
      calc
        _ = ∑ x : Fin N, (N : ℝ) * (if x ∈ lab0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          split_ifs <;> ring
        _ = (N : ℝ) * ∑ x : Fin N, if x ∈ lab0 then 1 else 0 := by
          rw [Finset.mul_sum]
        _ = (N : ℝ) * (lab0.card : ℝ) := by simp [lab0]
        _ = _ := by ring
    rw [Finset.sum_add_distrib, hsumIte] at hsumPoint
    simpa [Fintype.card_fin, add_comm, add_left_comm, add_assoc] using hsumPoint
  have hlab0_card : χ ^ 2 * N / 4 ≤ (lab0.card : ℝ) := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    nlinarith [hdegree_sum_lower, hdegree_sum_upper, hNreal]
  have hchiSq_pos : 0 < χ ^ 2 := sq_pos_of_pos p.hχ
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hthreshold_pos : 0 < χ ^ 2 * (N : ℝ) / 4 :=
    div_pos (mul_pos hchiSq_pos hNreal_pos) (by norm_num)
  have hlab0_nonempty : lab0.Nonempty := by
    have hcard : 0 < (lab0.card : ℝ) := lt_of_lt_of_le hthreshold_pos hlab0_card
    exact Finset.card_pos.mp (by exact_mod_cast hcard)
  let partnerSet (v : Fin N) (_b : Bin) : Finset (Fin N) :=
    if v ∈ lab0 then Finset.univ.filter (fun y => goodPair v y) else Finset.univ
  have hpartnerSet_nonempty (v : Fin N) (b : Bin) : (partnerSet v b).Nonempty := by
    by_cases hv : v ∈ lab0
    · have hdegree_pos : 0 < degree v := by
        have hmem : χ ^ 2 * (N : ℝ) / 4 ≤ (degree v : ℝ) :=
          (Finset.mem_filter.mp hv).2
        have hpos : 0 < (degree v : ℝ) := lt_of_lt_of_le hthreshold_pos hmem
        exact_mod_cast hpos
      have hset : (Finset.univ.filter (fun y => goodPair v y)).Nonempty :=
        Finset.card_pos.mp hdegree_pos
      simpa [partnerSet, hv] using hset
    · simp only [partnerSet, if_neg hv]
      exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hthreshold_recip : (lab0.card : ℝ)⁻¹ ≤ (4 / χ ^ 2) / N := by
    have hrec : (lab0.card : ℝ)⁻¹ ≤ (χ ^ 2 * (N : ℝ) / 4)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hthreshold_pos hlab0_card
    calc
      (lab0.card : ℝ)⁻¹ ≤ (χ ^ 2 * (N : ℝ) / 4)⁻¹ := hrec
      _ = (4 / χ ^ 2) / N := by
        have hχsq : χ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos p.hχ)
        have hNne : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
        field_simp [hχsq, hNne]
  have hfallback_recip : (N : ℝ)⁻¹ ≤ (4 / χ ^ 2) / N := by
    have hconst : (1 : ℝ) ≤ 4 / χ ^ 2 := by
      have hsquare : χ ^ 2 ≤ χ := by
        have hmul := mul_le_mul_of_nonneg_right hχ_le_one (le_of_lt p.hχ)
        nlinarith [hmul]
      apply (le_div_iff₀ hchiSq_pos).2
      nlinarith [hsquare, hχ_le_one]
    calc
      (N : ℝ)⁻¹ = (1 : ℝ) / N := by simp
      _ ≤ (4 / χ ^ 2) / N := div_le_div_of_nonneg_right hconst hNreal_pos.le
  let prior : ParentPrior5 N Bin := {
    parent := FinProb.uniform lab0 hlab0_nonempty
    partner v b := FinProb.uniform (partnerSet v b) (hpartnerSet_nonempty v b)
    partnerSet := partnerSet
    atomConstant := 4 / χ ^ 2
    atomConstant_nonneg := by positivity
    parent_atom := by
      intro y
      change (if y ∈ lab0 then (lab0.card : ℝ)⁻¹ else 0) ≤ (4 / χ ^ 2) / N
      by_cases hy : y ∈ lab0
      · rw [if_pos hy]
        exact hthreshold_recip
      · rw [if_neg hy]
        positivity
    partner_atom := by
      intro v b y
      by_cases hv : v ∈ lab0
      · simp only [FinProb.uniform, partnerSet, if_pos hv]
        by_cases hy : y ∈ Finset.univ.filter (fun z => goodPair v z)
        · rw [if_pos hy]
          have hdeg : χ ^ 2 * (N : ℝ) / 4 ≤
              ((Finset.univ.filter (fun z => goodPair v z)).card : ℝ) := by
            simpa [degree] using (Finset.mem_filter.mp hv).2
          have hrec := one_div_le_one_div_of_le
            hthreshold_pos hdeg
          calc
            ((Finset.univ.filter (fun z => goodPair v z)).card : ℝ)⁻¹ ≤
                (χ ^ 2 * (N : ℝ) / 4)⁻¹ := by simpa only [one_div] using hrec
            _ = (4 / χ ^ 2) / N := by
              have hχsq : χ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos p.hχ)
              have hNne : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
              field_simp [hχsq, hNne]
        · rw [if_neg hy]
          positivity
      · simp only [FinProb.uniform, partnerSet, if_neg hv, Finset.mem_univ, if_pos]
        simpa [Fintype.card_fin, one_div] using hfallback_recip
    partner_support := by
      intro v b y hy
      simp [FinProb.uniform, hy]
  }
  let P : ParentSelection5 N Bin χ := {
    prior := prior
    prior_atom_constant := rfl
    lab0 := lab0
    lab0_card := hlab0_card
    lab0_atom := by
      intro y hy
      simp [prior, FinProb.uniform, hy]
    partnerCount_lower := by
      intro v b hv
      have hmem : χ ^ 2 * (N : ℝ) / 4 ≤ (degree v : ℝ) :=
        (Finset.mem_filter.mp hv).2
      simpa [prior, partnerSet, hv, degree, goodPair] using hmem
  }
  refine ⟨P, ?_⟩
  have hlabelNonempty : (Finset.univ : Finset (Fin N)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  let U0 : Law N := Law.mix Λ μ
  let refProduct (i : ι) : FinProb (Word5 N p.q0) :=
    FinProb.pi (fun _ : Fin p.q0 => μ i)
  let U : FinProb (Word5 N p.q0) :=
    FinProb.map (FinProb.bind Λ refProduct) Prod.snd
  let tagGood (x y : Fin N) (i : ι) : Prop :=
    GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y
  have htagMass (x y : Fin N) :
      FinProb.pr Λ (tagGood x y) = GoodPairMass5 E G Λ μ x y := by
    classical
    simp only [FinProb.pr, GoodPairMass5]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y
    · simp [tagGood, h]
    · simp [tagGood, h]
  have htagMassPos (x y : Fin N) (hxy : goodPair x y) :
    0 < FinProb.pr Λ (tagGood x y) := by
    rw [htagMass]
    exact lt_of_lt_of_le (by positivity) hxy
  let tagLaw (x y : Fin N) (hxy : goodPair x y) : FinProb ι :=
    FinProb.cond Λ (tagGood x y) (htagMassPos x y hxy)
  let commonLaw (x y : Fin N) (i : ι) : Law N :=
    if h : 0 < Λ.w i ∧ tagGood x y i then
      Law.restrict (μ i) (commonSet i x y) (by
        have hc := commonMass_lower i x y h.1 h.2.1 h.2.2
        linarith)
    else μ i
  have hUweight (z : Word5 N p.q0) :
      U.w z = ∑ i, Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) := by
    simp [U, refProduct, FinProb.map, FinProb.bind, FinProb.pi, Fintype.sum_prod_type]
  let streamSeg (x y : Fin N) : FinProb (Word5 N p.q0) :=
    if hxy : goodPair x y then
      FinProb.map
        (FinProb.bind (tagLaw x y hxy)
          (fun i => FinProb.pi (fun _ : Fin p.q0 => commonLaw x y i))) Prod.snd
    else U
  have hstreamSegWeight (x y : Fin N) (hxy : goodPair x y) (z : Word5 N p.q0) :
      (streamSeg x y).w z =
        ∑ i, (tagLaw x y hxy).w i * ∏ j : Fin p.q0, (commonLaw x y i).w (z j) := by
    simp [streamSeg, hxy, FinProb.map, FinProb.bind, FinProb.pi, Fintype.sum_prod_type]
  have htagLawWeight (x y : Fin N) (hxy : goodPair x y) (i : ι) :
      (tagLaw x y hxy).w i =
        (if tagGood x y i then Λ.w i else 0) / GoodPairMass5 E G Λ μ x y := by
    by_cases h : tagGood x y i
    · simp [tagLaw, FinProb.cond, htagMass, h]
    · simp [tagLaw, FinProb.cond, htagMass, h]
  let S : StreamSegments5 n N p.q0 E G γ K' (p.a 0) := {
    paired := goodPair
    segment := streamSeg
    reference := U
    segment_density := by
      intro x y z hpair
      let mass : ℝ := GoodPairMass5 E G Λ μ x y
      let L : FinProb ι := tagLaw x y hpair
      have hmassPos : 0 < mass := by
        dsimp [mass]
        have hχ : 0 < χ ^ 2 / 2 := by positivity
        exact lt_of_lt_of_le hχ hpair
      have hLweight (i : ι) : L.w i =
          (if tagGood x y i then Λ.w i else 0) / mass := by
        dsimp [L, mass]
        exact htagLawWeight x y hpair i
      have hcommonPoint (i : ι) (hi : 0 < Λ.w i) (hgood : tagGood x y i)
          (j : Fin p.q0) :
          (commonLaw x y i).w (z j) ≤ (10 / 9 : ℝ) * (μ i).w (z j) := by
        have hmassCommon := commonMass_lower i x y hi hgood.1 hgood.2
        have hmassCommonPos : 0 < ∑ u ∈ commonSet i x y, (μ i).w u :=
          lt_of_lt_of_le (by norm_num) hmassCommon
        dsimp [commonLaw]
        have hcase : 0 < Λ.w i ∧ tagGood x y i := ⟨hi, hgood⟩
        rw [dif_pos hcase, Law.restrict]
        change (if z j ∈ commonSet i x y then
          (μ i).w (z j) / (∑ u ∈ commonSet i x y, (μ i).w u) else 0) ≤ _
        by_cases hz : z j ∈ commonSet i x y
        · rw [if_pos hz]
          calc
            (μ i).w (z j) / (∑ u ∈ commonSet i x y, (μ i).w u) ≤
                (μ i).w (z j) / (9 / 10 : ℝ) :=
              div_le_div_of_nonneg_left ((μ i).nonneg (z j)) (by norm_num) hmassCommon
            _ = (10 / 9 : ℝ) * (μ i).w (z j) := by ring
        · rw [if_neg hz]
          exact mul_nonneg (by norm_num) ((μ i).nonneg (z j))
      have hprodBound (i : ι) (hi : 0 < Λ.w i) (hgood : tagGood x y i) :
          (∏ j : Fin p.q0, (commonLaw x y i).w (z j)) ≤
            (10 / 9 : ℝ) ^ p.q0 * ∏ j : Fin p.q0, (μ i).w (z j) := by
        calc
          _ ≤ ∏ j : Fin p.q0, ((10 / 9 : ℝ) * (μ i).w (z j)) :=
            Finset.prod_le_prod₀ (fun j hj => (commonLaw x y i).nonneg (z j))
              (fun j hj => hcommonPoint i hi hgood j)
          _ = (10 / 9 : ℝ) ^ p.q0 * ∏ j : Fin p.q0, (μ i).w (z j) := by
            rw [Finset.prod_mul_distrib]
            have hconst :
                (∏ _j : Fin p.q0, (10 / 9 : ℝ)) = (10 / 9 : ℝ) ^ p.q0 := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            rw [hconst]
      have hterm (i : ι) :
          L.w i * ∏ j : Fin p.q0, (commonLaw x y i).w (z j) ≤
            ((10 / 9 : ℝ) ^ p.q0 / mass) *
              (Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j)) := by
        by_cases hgood : tagGood x y i
        · by_cases hi : 0 < Λ.w i
          · rw [hLweight]
            simp only [if_pos hgood]
            calc
              (Λ.w i / mass) * ∏ j : Fin p.q0, (commonLaw x y i).w (z j) ≤
                  (Λ.w i / mass) *
                    ((10 / 9 : ℝ) ^ p.q0 * ∏ j : Fin p.q0, (μ i).w (z j)) :=
                mul_le_mul_of_nonneg_left (hprodBound i hi hgood)
                  (div_nonneg (Λ.nonneg i) hmassPos.le)
              _ = ((10 / 9 : ℝ) ^ p.q0 / mass) *
                    (Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j)) := by ring
          · have hz : Λ.w i = 0 := le_antisymm (le_of_not_gt hi) (Λ.nonneg i)
            have hzero : L.w i = 0 := by rw [hLweight, if_pos hgood, hz]; simp
            rw [hzero]
            have hcoefNonneg : 0 ≤ ((10 / 9 : ℝ) ^ p.q0 / mass) :=
              div_nonneg (pow_nonneg (by norm_num : 0 ≤ (10 / 9 : ℝ)) _) hmassPos.le
            have htermNonneg : 0 ≤ Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) :=
              mul_nonneg (Λ.nonneg i) (Finset.prod_nonneg fun j hj => (μ i).nonneg (z j))
            calc
              0 * ∏ j : Fin p.q0, (commonLaw x y i).w (z j) = 0 := by ring
              _ ≤ ((10 / 9 : ℝ) ^ p.q0 / mass) *
                    (Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j)) :=
                mul_nonneg hcoefNonneg htermNonneg
        · have hzero : L.w i = 0 := by rw [hLweight, if_neg hgood]; simp
          rw [hzero]
          have hcoefNonneg : 0 ≤ ((10 / 9 : ℝ) ^ p.q0 / mass) :=
            div_nonneg (pow_nonneg (by norm_num : 0 ≤ (10 / 9 : ℝ)) _) hmassPos.le
          have htermNonneg : 0 ≤ Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) :=
            mul_nonneg (Λ.nonneg i) (Finset.prod_nonneg fun j hj => (μ i).nonneg (z j))
          calc
            0 * ∏ j : Fin p.q0, (commonLaw x y i).w (z j) = 0 := by ring
            _ ≤ ((10 / 9 : ℝ) ^ p.q0 / mass) *
                  (Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j)) :=
              mul_nonneg hcoefNonneg htermNonneg
      have hsumBound :
          (∑ i, L.w i * ∏ j : Fin p.q0, (commonLaw x y i).w (z j)) ≤
            ((10 / 9 : ℝ) ^ p.q0 / mass) * U.w z := by
        rw [hUweight]
        calc
          _ ≤ ∑ i, ((10 / 9 : ℝ) ^ p.q0 / mass) *
                (Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j)) :=
            Finset.sum_le_sum fun i _ => hterm i
          _ = ((10 / 9 : ℝ) ^ p.q0 / mass) *
                ∑ i, Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) := by rw [Finset.mul_sum]
      have hcoef : (10 / 9 : ℝ) ^ p.q0 / mass ≤
          Real.exp ((p.a 0) * (p.q0 : ℝ)) := by
        have hqnonneg : 0 ≤ (10 / 9 : ℝ) ^ p.q0 := by positivity
        have hthresholdPos : 0 < χ ^ 2 / 2 := by positivity
        calc
          _ ≤ (10 / 9 : ℝ) ^ p.q0 / (χ ^ 2 / 2) :=
            div_le_div_of_nonneg_left hqnonneg hthresholdPos hpair
          _ = (2 / χ ^ 2) * (10 / 9 : ℝ) ^ p.q0 := by
            field_simp [ne_of_gt (sq_pos_of_pos p.hχ)]
            <;> ring
          _ ≤ Real.exp ((p.a 0) * (p.q0 : ℝ)) := p.hq0.2
      rw [hstreamSegWeight x y hpair z]
      calc
        _ ≤ ((10 / 9 : ℝ) ^ p.q0 / mass) * U.w z := hsumBound
        _ ≤ Real.exp ((p.a 0) * (p.q0 : ℝ)) * U.w z :=
          mul_le_mul_of_nonneg_right hcoef (U.nonneg z)
    segment_hits := by
      intro x y z hpair hz j
      have hsumne :
          (∑ i, (tagLaw x y hpair).w i *
            ∏ k : Fin p.q0, (commonLaw x y i).w (z k)) ≠ 0 := by
        rw [← hstreamSegWeight x y hpair z]
        exact hz
      have hsumpos : 0 <
          ∑ i, (tagLaw x y hpair).w i *
            ∏ k : Fin p.q0, (commonLaw x y i).w (z k) := by
        apply lt_of_le_of_ne
        · exact Finset.sum_nonneg fun i hi =>
            mul_nonneg ((tagLaw x y hpair).nonneg i)
              (Finset.prod_nonneg fun k hk => (commonLaw x y i).nonneg (z k))
        · exact Ne.symm hsumne
      obtain ⟨i, hi, htermPos⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun i hi =>
          mul_nonneg ((tagLaw x y hpair).nonneg i)
            (Finset.prod_nonneg fun k hk => (commonLaw x y i).nonneg (z k)))).mp hsumpos
      have hprodPos : 0 < ∏ k : Fin p.q0, (commonLaw x y i).w (z k) := by
        exact lt_of_le_of_ne
          (Finset.prod_nonneg fun k hk => (commonLaw x y i).nonneg (z k))
          (by
            intro heq
            rw [← heq, mul_zero] at htermPos
            exact (lt_irrefl 0) htermPos)
      have htagPos : 0 < (tagLaw x y hpair).w i := by
        exact lt_of_le_of_ne ((tagLaw x y hpair).nonneg i)
          (by
            intro heq
            rw [← heq, zero_mul] at htermPos
            exact (lt_irrefl 0) htermPos)
      have htagW := htagLawWeight x y hpair i
      have htag : tagGood x y i := by
        by_contra hnot
        rw [htagW, if_neg hnot] at htagPos
        norm_num at htagPos
      have htagLambda : 0 < Λ.w i := by
        rw [htagW, if_pos htag] at htagPos
        have hmass : 0 < GoodPairMass5 E G Λ μ x y :=
          lt_of_lt_of_le (by positivity) hpair
        by_contra hnot
        have hzero : Λ.w i = 0 := le_antisymm (le_of_not_gt hnot) (Λ.nonneg i)
        rw [hzero] at htagPos
        norm_num at htagPos
      have hfactorNe (k : Fin p.q0) : (commonLaw x y i).w (z k) ≠ 0 := by
        intro hz0
        have hzero : ∏ u : Fin p.q0, (commonLaw x y i).w (z u) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) hz0
        exact (ne_of_gt hprodPos) hzero
      have hmem (k : Fin p.q0) : z k ∈ commonSet i x y := by
        by_contra hnot
        apply hfactorNe k
        simp [commonLaw, htagLambda, htag, Law.restrict, hnot]
      exact (Finset.mem_filter.mp (hmem j)).2
    reference_coordinate_cap := by
      intro j x
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hpiMarginal (i : ι) :
          (refProduct i).expect (fun z => if z j = x then 1 else 0) = (μ i).w x := by
        letI : Unique {k : Fin p.q0 // k ∈ ({j} : Finset (Fin p.q0))} :=
          ⟨⟨j, by simp⟩, fun k => Subtype.ext (Finset.mem_singleton.mp k.property)⟩
        have hpi := FinProb.pi_marginal_expect
          (P := fun _ : Fin p.q0 => μ i) ({j} : Finset (Fin p.q0))
          (fun z => if z ⟨j, by simp⟩ = x then 1 else 0)
        have hidx : (⟨j, by simp⟩ : {k : Fin p.q0 // k ∈ ({j} : Finset (Fin p.q0))}) = default :=
          Unique.eq_default _
        have hsum :
            (∑ z : (∀ k : {k // k ∈ ({j} : Finset (Fin p.q0))}, Fin N),
              if z default = x then (μ i).w (z default) else 0) = (μ i).w x := by
          let z₀ : (∀ k : {k // k ∈ ({j} : Finset (Fin p.q0))}, Fin N) := fun _ => x
          rw [Finset.sum_eq_single z₀]
          · simp [z₀]
          · intro z hz hzne
            have hzx : z default ≠ x := by
              intro hzval
              apply hzne
              funext k
              rw [Unique.eq_default k]
              exact hzval
            simp [hzx]
          · simp
        calc
          _ = (FinProb.pi (fun k : {k // k ∈ ({j} : Finset (Fin p.q0))} => μ i)).expect
                (fun z => if z ⟨j, by simp⟩ = x then 1 else 0) := by
              simpa [refProduct] using hpi
          _ = ∑ z : (∀ k : {k // k ∈ ({j} : Finset (Fin p.q0))}, Fin N),
                if z default = x then (μ i).w (z default) else 0 := by
              simp only [FinProb.expect, FinProb.pi]
              apply Finset.sum_congr rfl
              intro z hz
              have hprod :
                  (∏ k : {k // k ∈ ({j} : Finset (Fin p.q0))}, (μ i).w (z k)) =
                    (μ i).w (z default) := Fintype.prod_unique _
              rw [hprod, hidx]
              by_cases hzx : z default = x <;> simp [hzx]
          _ = (μ i).w x := hsum
      have hpr : wordMarginal5 U j x = U.expect (fun z => if z j = x then 1 else 0) := by
        unfold wordMarginal5 FinProb.expect
        apply Finset.sum_congr rfl
        intro z hz
        by_cases hzx : z j = x <;> simp [hzx]
      have hmargin : wordMarginal5 U j x = U0.w x := by
        rw [hpr]
        calc
          _ = ∑ i, Λ.w i * (refProduct i).expect
                (fun z => if z j = x then 1 else 0) := by
            change (FinProb.map (FinProb.bind Λ refProduct) Prod.snd).expect _ = _
            rw [FinProb.map_expect]
            change (FinProb.bind Λ refProduct).expect
              (fun a => if a.2 j = x then 1 else 0) = _
            have hbind := FinProb.bind_expect Λ refProduct
              (fun (_ : ι) (z : Word5 N p.q0) => if z j = x then (1 : ℝ) else 0)
            simpa using hbind
          _ = ∑ i, Λ.w i * (μ i).w x := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hpiMarginal]
          _ = U0.w x := by simp [U0, Law.mix]
      rw [hmargin]
      have hbalance' : (N : ℝ) * U0.w x ≤ K' := by
        simpa [U0, Law.mix] using hbalance x
      apply (le_div_iff₀ hNreal).2
      nlinarith [hbalance']
    reference_density := by
      intro z
      let A : ℝ := Real.exp ((n : ℝ) ^ γ) / (N : ℝ)
      have hUweight : U.w z = ∑ i, Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) := by
        simp [U, refProduct, FinProb.map, FinProb.bind, FinProb.pi, Fintype.sum_prod_type]
      have hterm (i : ι) :
          Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) ≤ Λ.w i * A ^ p.q0 := by
        by_cases hi : 0 < Λ.w i
        · have hprod :
              (∏ j : Fin p.q0, (μ i).w (z j)) ≤ ∏ _j : Fin p.q0, A := by
            apply Finset.prod_le_prod₀
            · intro j hj
              exact (μ i).nonneg (z j)
            · intro j hj
              simpa [A] using hwidth i hi (z j)
          calc
            Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j) ≤
                Λ.w i * ∏ _j : Fin p.q0, A :=
              mul_le_mul_of_nonneg_left hprod (Λ.nonneg i)
            _ = Λ.w i * A ^ p.q0 := by simp [Finset.prod_const]
        · have hzero : Λ.w i = 0 := le_antisymm (le_of_not_gt hi) (Λ.nonneg i)
          simp [hzero]
      have hsum :
          (∑ i, Λ.w i * ∏ j : Fin p.q0, (μ i).w (z j)) ≤ A ^ p.q0 := by
        calc
          _ ≤ ∑ i, Λ.w i * A ^ p.q0 := Finset.sum_le_sum fun i _ => hterm i
          _ = A ^ p.q0 := by simp [← Finset.sum_mul, Λ.sum_eq_one]
      have hAq : A ^ p.q0 =
          Real.exp ((p.q0 : ℝ) * (n : ℝ) ^ γ) / (N : ℝ) ^ p.q0 := by
        dsimp [A]
        rw [div_pow, ← Real.exp_nat_mul]
      rw [hUweight]
      exact hsum.trans_eq hAq
  }
  refine ⟨S, ?_⟩
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro v hv b
    simp [P, prior, partnerSet, hv, goodPair]
  · intro x y
    rfl
  · intro v b b'
    rfl

end HypercubeRamsey
