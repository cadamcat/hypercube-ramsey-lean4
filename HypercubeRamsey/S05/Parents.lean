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
  let U0 : Law N := FinProb.uniform Finset.univ hlabelNonempty
  let U : FinProb (Word5 N p.q0) := FinProb.pi (fun _ : Fin p.q0 => U0)
  have hgoodTag_exists (x y : Fin N) (hxy : goodPair x y) :
      ∃ i, 0 < Λ.w i ∧ GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y := by
    have hmass : 0 < GoodPairMass5 E G Λ μ x y := by
      change χ ^ 2 / 2 ≤ GoodPairMass5 E G Λ μ x y at hxy
      exact lt_of_lt_of_le (by positivity : 0 < χ ^ 2 / 2) hxy
    have hterm : ∃ i, 0 <
        (if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y then Λ.w i else 0) := by
      by_contra hnone
      have hle : ∀ i, (if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y
          then Λ.w i else 0) ≤ 0 := by
        intro i
        exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
      have hs :
          (∑ i, if GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y
            then Λ.w i else 0) ≤ 0 := by
        calc
          _ ≤ ∑ i, 0 := Finset.sum_le_sum (fun i hi => hle i)
          _ = 0 := by simp
      unfold GoodPairMass5 at hmass
      linarith
    obtain ⟨i, hi⟩ := hterm
    by_cases hgood : GoodColumn5 E G (μ i) x ∧ GoodColumn5 E G (μ i) y
    · simp [hgood] at hi
      exact ⟨i, hi, hgood.1, hgood.2⟩
    · simp [hgood] at hi
  have hselected_exists (x y : Fin N) (hxy : goodPair x y) :
      ∃ z : Fin N, Hits E G z x ∧ Hits E G z y := by
    obtain ⟨i, hi, hxi, hyi⟩ := hgoodTag_exists x y hxy
    have hm := commonMass_lower i x y hi hxi hyi
    have hset : (commonSet i x y).Nonempty := by
      by_contra hne
      have hempty : commonSet i x y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty] at hm
      norm_num at hm
    obtain ⟨z, hz⟩ := hset
    exact ⟨z, (Finset.mem_filter.mp hz).2.1, (Finset.mem_filter.mp hz).2.2⟩
  let pickedLabel (x y : Fin N) (hxy : goodPair x y) : Fin N :=
    Classical.choose (hselected_exists x y hxy)
  have hpickedLabel (x y : Fin N) (hxy : goodPair x y) :
      Hits E G (pickedLabel x y hxy) x ∧ Hits E G (pickedLabel x y hxy) y :=
    Classical.choose_spec (hselected_exists x y hxy)
  let streamSeg (x y : Fin N) : FinProb (Word5 N p.q0) :=
    if hxy : goodPair x y then
      FinProb.uniform {fun _ : Fin p.q0 => pickedLabel x y hxy} (by simp)
    else U
  let S : StreamSegments5 n N p.q0 E G γ K' (p.a 0) := {
    paired := goodPair
    segment := streamSeg
    reference := U
    segment_density := by
      intro x y z hpair
      sorry
    segment_hits := by
      intro x y z hpair hz j
      have hzword : z = (fun _ : Fin p.q0 => pickedLabel x y hpair) := by
        by_contra hne
        simp [streamSeg, hpair, FinProb.uniform, hne] at hz
      subst z
      exact hpickedLabel x y hpair
    reference_coordinate_cap := by
      intro j x
      sorry
    reference_density := by
      intro z
      have hbase : 0 ≤ (n : ℝ) ^ γ := by positivity
      have hExpArg : 0 ≤ (p.q0 : ℝ) * (n : ℝ) ^ γ :=
        mul_nonneg (Nat.cast_nonneg _) hbase
      have hExp : 1 ≤ Real.exp ((p.q0 : ℝ) * (n : ℝ) ^ γ) := by
        calc
          1 = Real.exp 0 := by simp
          _ ≤ Real.exp ((p.q0 : ℝ) * (n : ℝ) ^ γ) := Real.exp_le_exp.mpr hExpArg
      have hUweight : U.w z = ((N : ℝ)⁻¹) ^ p.q0 := by
        simp [U, U0, FinProb.pi, FinProb.uniform, Finset.mem_univ, Fintype.card_fin]
      rw [hUweight]
      have hNp : 0 < (N : ℝ) ^ p.q0 := by positivity
      have hpow : ((N : ℝ)⁻¹) ^ p.q0 = ((N : ℝ) ^ p.q0)⁻¹ := by simp
      rw [hpow]
      calc
        ((N : ℝ) ^ p.q0)⁻¹ = 1 / (N : ℝ) ^ p.q0 := by simp
        _ ≤ Real.exp ((p.q0 : ℝ) * (n : ℝ) ^ γ) / (N : ℝ) ^ p.q0 :=
          (div_le_div_iff₀ hNp hNp).2
            (mul_le_mul_of_nonneg_right hExp (le_of_lt hNp))
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
