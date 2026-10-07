import HypercubeRamsey.Framework.FinProb

/-!
# Selection-adjusted posterior

Finite form of F-SelAdj. It includes both the rowwise domination after a successful presentation gate and the
aggregate prior bound that pays at most `ε` for each record whose gate is small.
-/

namespace HypercubeRamsey

open scoped BigOperators

/-- F-SelAdj: select the presentation-weighted posterior when its mass is at least `ε` times the raw mass,
and otherwise use the raw posterior. The resulting rows have a controlled aggregate under the presented law. -/
theorem selectionAdjustedPosterior
    {Candidate Records Outcome : Type*} [Fintype Candidate] [DecidableEq Candidate]
    [Fintype Records] [DecidableEq Records] [Fintype Outcome] [DecidableEq Outcome]
    (π : FinProb Candidate) (Q : Records → FinProb Outcome)
    (F a : Records → Candidate → Outcome → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hF : ∀ r ξ o, 0 ≤ F r ξ o)
    (ha : ∀ r ξ o, 0 ≤ a r ξ o ∧ a r ξ o ≤ 1)
    (hrecord : ∀ r ξ, ∑ o, F r ξ o * (Q r).w o ≤ 1)
    (hpresentation : ∀ ξ, ∑ r, ∑ o, F r ξ o * a r ξ o * (Q r).w o ≤ 1) :
    let M : Records → Outcome → ℝ := fun r o => ∑ ξ, π.w ξ * F r ξ o
    let Ma : Records → Outcome → ℝ := fun r o => ∑ ξ, π.w ξ * F r ξ o * a r ξ o
    ∃ p : Records → Outcome → FinProb Candidate,
      (∀ r o ξ,
        (if 0 < M r o ∧ ε * M r o ≤ Ma r o then
          (p r o).w ξ = π.w ξ * F r ξ o * a r ξ o / Ma r o
        else if 0 < M r o then
          (p r o).w ξ = π.w ξ * F r ξ o / M r o
        else (p r o).w ξ = π.w ξ)) ∧
      (∀ r o ξ, 0 < M r o ∧ ε * M r o ≤ Ma r o →
        (p r o).w ξ ≤ ε⁻¹ * (π.w ξ * F r ξ o / M r o)) ∧
      (∀ ξ, ∑ r, ∑ o, Ma r o * (Q r).w o * (p r o).w ξ ≤
        (1 + ε * Fintype.card Records) * π.w ξ) := by
  classical
  let M : Records → Outcome → ℝ := fun r o => ∑ ξ, π.w ξ * F r ξ o
  let Ma : Records → Outcome → ℝ := fun r o => ∑ ξ, π.w ξ * F r ξ o * a r ξ o
  have hMnonneg (r : Records) (o : Outcome) : 0 ≤ M r o := by
    dsimp [M]
    exact Finset.sum_nonneg fun ξ _ => mul_nonneg (π.nonneg ξ) (hF r ξ o)
  have hManonneg (r : Records) (o : Outcome) : 0 ≤ Ma r o := by
    dsimp [Ma]
    exact Finset.sum_nonneg fun ξ _ =>
      mul_nonneg (mul_nonneg (π.nonneg ξ) (hF r ξ o)) (ha r ξ o).1
  have hMaLeM (r : Records) (o : Outcome) : Ma r o ≤ M r o := by
    dsimp [Ma, M]
    apply Finset.sum_le_sum
    intro ξ _
    have hnum : 0 ≤ π.w ξ * F r ξ o := mul_nonneg (π.nonneg ξ) (hF r ξ o)
    nlinarith [mul_le_mul_of_nonneg_left (ha r ξ o).2 hnum]
  let pw : Records → Outcome → Candidate → ℝ := fun r o ξ =>
    if h : 0 < M r o ∧ ε * M r o ≤ Ma r o then
      π.w ξ * F r ξ o * a r ξ o / Ma r o
    else if h : 0 < M r o then
      π.w ξ * F r ξ o / M r o
    else π.w ξ
  have hpw_nonneg (r : Records) (o : Outcome) (ξ : Candidate) : 0 ≤ pw r o ξ := by
    dsimp [pw]
    split_ifs with hgood hmass
    · apply div_nonneg
      · exact mul_nonneg (mul_nonneg (π.nonneg ξ) (hF r ξ o)) (ha r ξ o).1
      · have hpos : 0 < ε * M r o := mul_pos hε hgood.1
        exact le_trans hpos.le hgood.2
    · exact div_nonneg (mul_nonneg (π.nonneg ξ) (hF r ξ o)) hmass.le
    · exact π.nonneg ξ
  let p : Records → Outcome → FinProb Candidate := fun r o =>
    { w := pw r o
      nonneg := hpw_nonneg r o
      sum_eq_one := by
        dsimp [pw]
        split_ifs with hgood hmass
        · have hpos : 0 < Ma r o :=
            lt_of_lt_of_le (mul_pos hε hgood.1) hgood.2
          calc
            (∑ ξ, π.w ξ * F r ξ o * a r ξ o / Ma r o) =
                (∑ ξ, π.w ξ * F r ξ o * a r ξ o) / Ma r o := by rw [Finset.sum_div]
            _ = Ma r o / Ma r o := rfl
            _ = 1 := div_self hpos.ne'
        · calc
            (∑ ξ, π.w ξ * F r ξ o / M r o) =
                (∑ ξ, π.w ξ * F r ξ o) / M r o := by rw [Finset.sum_div]
            _ = M r o / M r o := rfl
            _ = 1 := div_self hmass.ne'
        · exact π.sum_eq_one }
  refine ⟨p, ?_, ?_, ?_⟩
  · intro r o ξ
    change (if 0 < M r o ∧ ε * M r o ≤ Ma r o then
      (p r o).w ξ = π.w ξ * F r ξ o * a r ξ o / Ma r o
      else if 0 < M r o then
        (p r o).w ξ = π.w ξ * F r ξ o / M r o
      else (p r o).w ξ = π.w ξ)
    by_cases hgood : 0 < M r o ∧ ε * M r o ≤ Ma r o
    · simp [p, pw, hgood]
    · by_cases hmass : 0 < M r o
      · have hgate : ¬ (ε * M r o ≤ Ma r o) := by
          intro hle
          exact hgood ⟨hmass, hle⟩
        simp [p, pw, hgood, hmass, hgate]
      · simp [p, pw, hmass]
  · intro r o ξ hgood
    change pw r o ξ ≤ ε⁻¹ * (π.w ξ * F r ξ o / M r o)
    change 0 < M r o ∧ ε * M r o ≤ Ma r o at hgood
    have hpw : pw r o ξ = π.w ξ * F r ξ o * a r ξ o / Ma r o := by
      simp [pw, hgood]
    rw [hpw]
    have hnum : 0 ≤ π.w ξ * F r ξ o := mul_nonneg (π.nonneg ξ) (hF r ξ o)
    have hMaPos : 0 < Ma r o := lt_of_lt_of_le (mul_pos hε hgood.1) hgood.2
    have hεMPos : 0 < ε * M r o := mul_pos hε hgood.1
    have hfrac :
        π.w ξ * F r ξ o * a r ξ o / Ma r o ≤
          π.w ξ * F r ξ o / (ε * M r o) := by
      calc
        π.w ξ * F r ξ o * a r ξ o / Ma r o ≤
            π.w ξ * F r ξ o / Ma r o := by
              apply div_le_div_of_nonneg_right _ hMaPos.le
              calc
                π.w ξ * F r ξ o * a r ξ o ≤
                    π.w ξ * F r ξ o * 1 :=
                  mul_le_mul_of_nonneg_left (ha r ξ o).2 hnum
                _ = π.w ξ * F r ξ o := by ring
        _ ≤ π.w ξ * F r ξ o / (ε * M r o) :=
          div_le_div_of_nonneg_left hnum hεMPos hgood.2
    have hMpos : M r o ≠ 0 := (ne_of_gt hgood.1)
    have hεne : ε ≠ 0 := ne_of_gt hε
    calc
      π.w ξ * F r ξ o * a r ξ o / Ma r o ≤
          π.w ξ * F r ξ o / (ε * M r o) := hfrac
      _ = ε⁻¹ * (π.w ξ * F r ξ o / M r o) := by
        field_simp [hεne, hMpos]
        <;> ring
  · intro ξ
    have hgoodBound (r : Records) (o : Outcome) :
        Ma r o * (Q r).w o * pw r o ξ ≤
          π.w ξ * F r ξ o * a r ξ o * (Q r).w o +
            ε * (π.w ξ * F r ξ o) * (Q r).w o := by
      by_cases hgood : 0 < M r o ∧ ε * M r o ≤ Ma r o
      · have hMaPos : 0 < Ma r o := lt_of_lt_of_le (mul_pos hε hgood.1) hgood.2
        rw [show pw r o ξ = π.w ξ * F r ξ o * a r ξ o / Ma r o by simp [pw, hgood]]
        have hQ : 0 ≤ (Q r).w o := (Q r).nonneg o
        calc
          Ma r o * (Q r).w o *
              (π.w ξ * F r ξ o * a r ξ o / Ma r o) =
                π.w ξ * F r ξ o * a r ξ o * (Q r).w o := by
                  field_simp [ne_of_gt hMaPos]
          _ ≤ π.w ξ * F r ξ o * a r ξ o * (Q r).w o +
                ε * (π.w ξ * F r ξ o) * (Q r).w o := by
                  have := mul_nonneg (mul_nonneg (mul_nonneg hε.le (π.nonneg ξ))
                    (hF r ξ o)) hQ
                  nlinarith
      · by_cases hmass : 0 < M r o
        · have hMaSmall : Ma r o < ε * M r o := by
            by_contra hnot
            exact hgood ⟨hmass, le_of_not_gt hnot⟩
          have hgate : ¬ (ε * M r o ≤ Ma r o) := by
            intro hle
            exact hgood ⟨hmass, hle⟩
          have hpw : pw r o ξ = π.w ξ * F r ξ o / M r o := by
            simp [pw, hmass, hgate]
          rw [hpw]
          have hQ : 0 ≤ (Q r).w o := (Q r).nonneg o
          have hnum : 0 ≤ π.w ξ * F r ξ o := mul_nonneg (π.nonneg ξ) (hF r ξ o)
          have hterm : Ma r o * (π.w ξ * F r ξ o / M r o) ≤
              ε * (π.w ξ * F r ξ o) := by
            rw [div_eq_mul_inv]
            have hratio : Ma r o / M r o < ε := (div_lt_iff₀ hmass).2 hMaSmall
            calc
              Ma r o * (π.w ξ * F r ξ o * (M r o)⁻¹) =
                  (Ma r o / M r o) * (π.w ξ * F r ξ o) := by
                    field_simp [ne_of_gt hmass] <;> ring
              _ ≤ ε * (π.w ξ * F r ξ o) :=
                mul_le_mul_of_nonneg_right hratio.le hnum
          calc
            Ma r o * (Q r).w o * (π.w ξ * F r ξ o / M r o) ≤
                ε * (π.w ξ * F r ξ o) * (Q r).w o := by
                  nlinarith [mul_le_mul_of_nonneg_right hterm hQ]
            _ ≤ π.w ξ * F r ξ o * a r ξ o * (Q r).w o +
                  ε * (π.w ξ * F r ξ o) * (Q r).w o := by
                    have := mul_nonneg (mul_nonneg (mul_nonneg (π.nonneg ξ)
                      (hF r ξ o)) (ha r ξ o).1) hQ
                    nlinarith
        · have hMzero : M r o = 0 := le_antisymm (le_of_not_gt hmass) (hMnonneg r o)
          have hMazero : Ma r o = 0 := le_antisymm
            ((hMaLeM r o).trans_eq hMzero) (hManonneg r o)
          have hpw : pw r o ξ = π.w ξ := by simp [pw, hMzero, hmass]
          rw [hMazero, hpw]
          have hQ : 0 ≤ (Q r).w o := (Q r).nonneg o
          have hnum : 0 ≤ π.w ξ * F r ξ o := mul_nonneg (π.nonneg ξ) (hF r ξ o)
          have hnuma : 0 ≤ π.w ξ * F r ξ o * a r ξ o :=
            mul_nonneg hnum (ha r ξ o).1
          have hfirst : 0 ≤ π.w ξ * F r ξ o * a r ξ o * (Q r).w o :=
            mul_nonneg hnuma hQ
          have hsecond : 0 ≤ ε * (π.w ξ * F r ξ o) * (Q r).w o :=
            mul_nonneg (mul_nonneg hε.le hnum) hQ
          simpa using add_nonneg hfirst hsecond
    calc
      (∑ r, ∑ o, Ma r o * (Q r).w o * (p r o).w ξ) ≤
          ∑ r, ∑ o,
            (π.w ξ * F r ξ o * a r ξ o * (Q r).w o +
              ε * (π.w ξ * F r ξ o) * (Q r).w o) := by
                apply Finset.sum_le_sum
                intro r hr
                apply Finset.sum_le_sum
                intro o ho
                exact hgoodBound r o
      _ = π.w ξ * (∑ r, ∑ o, F r ξ o * a r ξ o * (Q r).w o) +
            ε * π.w ξ * ∑ r, ∑ o, F r ξ o * (Q r).w o := by
              have hfirst :
                  (∑ r, ∑ o, π.w ξ * F r ξ o * a r ξ o * (Q r).w o) =
                    π.w ξ * (∑ r, ∑ o, F r ξ o * a r ξ o * (Q r).w o) := by
                calc
                  _ = ∑ r, ∑ o, π.w ξ * (F r ξ o * a r ξ o * (Q r).w o) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    apply Finset.sum_congr rfl
                    intro o ho
                    ring
                  _ = ∑ r, π.w ξ * (∑ o, F r ξ o * a r ξ o * (Q r).w o) := by
                    simp_rw [Finset.mul_sum]
                  _ = π.w ξ * (∑ r, ∑ o, F r ξ o * a r ξ o * (Q r).w o) := by
                    rw [Finset.mul_sum]
              have hsecond :
                  (∑ r, ∑ o, ε * (π.w ξ * F r ξ o) * (Q r).w o) =
                    (ε * π.w ξ) * (∑ r, ∑ o, F r ξ o * (Q r).w o) := by
                calc
                  _ = ∑ r, ∑ o, (ε * π.w ξ) * (F r ξ o * (Q r).w o) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    apply Finset.sum_congr rfl
                    intro o ho
                    ring
                  _ = ∑ r, (ε * π.w ξ) * (∑ o, F r ξ o * (Q r).w o) := by
                    simp_rw [Finset.mul_sum]
                  _ = (ε * π.w ξ) * (∑ r, ∑ o, F r ξ o * (Q r).w o) := by
                    rw [Finset.mul_sum]
              simp_rw [Finset.sum_add_distrib]
              rw [hfirst, hsecond]
      _ ≤ π.w ξ + ε * π.w ξ * Fintype.card Records := by
            have hpres := hpresentation ξ
            have hrec : ∑ r, ∑ o, F r ξ o * (Q r).w o ≤ Fintype.card Records := by
              calc
                ∑ r, ∑ o, F r ξ o * (Q r).w o ≤ ∑ _r : Records, (1 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro r hr
                  exact hrecord r ξ
                _ = Fintype.card Records := by simp
            have hfirst := mul_le_mul_of_nonneg_left hpres (π.nonneg ξ)
            have hsecond := mul_le_mul_of_nonneg_left hrec (mul_nonneg hε.le (π.nonneg ξ))
            calc
              π.w ξ * (∑ r, ∑ o, F r ξ o * a r ξ o * (Q r).w o) +
                    ε * π.w ξ * ∑ r, ∑ o, F r ξ o * (Q r).w o ≤
                  π.w ξ * 1 + (ε * π.w ξ) * Fintype.card Records := by
                    exact add_le_add hfirst hsecond
              _ = π.w ξ + ε * π.w ξ * Fintype.card Records := by ring
      _ = (1 + ε * Fintype.card Records) * π.w ξ := by ring

end HypercubeRamsey
