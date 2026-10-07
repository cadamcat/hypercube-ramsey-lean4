import HypercubeRamsey.S18.Transitions
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s18_1b
open Classical
open scoped BigOperators

noncomputable def empirical {Ω : Type*} (m : ℕ) (I : Fin m → Ω → Prop) (y : Ω) : ℝ :=
  (∑ t, if I t y then (1 : ℝ) else 0) / m

private theorem expect_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (f : ι → Ω → ℝ) :
    P.expect (fun y => ∑ t, f t y) = ∑ t, P.expect (f t) := by
  simp only [FinProb.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem expect_div {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (f : Ω → ℝ) (c : ℝ) :
    P.expect (fun y => f y / c) = P.expect f / c := by
  simp [FinProb.expect, mul_div_assoc, Finset.sum_div]

private theorem expect_indicator {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.expect (fun y => if A y then (1 : ℝ) else 0) = P.pr A := by
  simp only [FinProb.expect, FinProb.pr]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

/-- A supported sketch's first and second moments give a uniform lower-tail
bound. Conflicting ordered pairs, including the diagonal, are paid separately. -/
theorem empirical_lower_tail {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (m : ℕ) (hm : 0 < m) (I : Fin m → Ω → Prop)
    (C : Fin m → Fin m → Prop) (e B : ℝ) (he : 0 < e) (hB : B ≤ e ^ 4)
    (hfirst : ∀ t, |P.pr (I t) - 1 / 2| ≤ 10 * B)
    (hpair : ∀ t u, ¬ C t u →
      |P.pr (fun y => I t y ∧ I u y) - 1 / 4| ≤ 10 * B)
    (hconflict : (∑ t, ∑ u, if C t u then (1 : ℝ) else 0) / (m : ℝ) ^ 2 ≤
      2 * e ^ 4) :
    P.pr (fun y => empirical m I y < 1 / 2 - e) ≤ 22 * e ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 := ne_of_gt hmR
  have hB0 : 0 ≤ B := by
    have h := le_trans (abs_nonneg _) (hfirst ⟨0, hm⟩)
    linarith
  have hmean : 1 / 2 - 10 * B ≤ P.expect (empirical m I) := by
    unfold empirical
    rw [expect_div, expect_sum]
    simp_rw [expect_indicator]
    apply (le_div_iff₀ hmR).2
    calc
      (1 / 2 - 10 * B) * m = ∑ _ : Fin m, (1 / 2 - 10 * B) := by simp; ring
      _ ≤ ∑ t, P.pr (I t) := Finset.sum_le_sum fun t _ => by
        have h := (abs_le.mp (hfirst t)).1
        linarith
  have hsecond_id : P.expect (fun y => empirical m I y ^ 2) =
      (∑ t, ∑ u, P.pr (fun y => I t y ∧ I u y)) / (m : ℝ) ^ 2 := by
    have hid (y : Ω) : empirical m I y ^ 2 =
        (∑ t, ∑ u, if I t y ∧ I u y then (1 : ℝ) else 0) / (m : ℝ) ^ 2 := by
      unfold empirical
      rw [div_pow, pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro u _
      by_cases ht : I t y <;> by_cases hu : I u y <;> simp [ht, hu]
    simp_rw [hid]
    rw [expect_div, expect_sum]
    simp only [expect_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    unfold FinProb.expect FinProb.pr
    apply Finset.sum_congr rfl
    intro y _
    by_cases ht : I t y <;> by_cases hu : I u y <;> simp [ht, hu]
  have hpr1 (A : Ω → Prop) : P.pr A ≤ 1 := by
    calc
      P.pr A ≤ ∑ y, P.w y := Finset.sum_le_sum fun y _ => by
        by_cases h : A y <;> simp [h, P.nonneg y]
      _ = 1 := P.sum_eq_one
  have hpairs : (∑ t, ∑ u, P.pr (fun y => I t y ∧ I u y)) ≤
      (m : ℝ) ^ 2 * (1 / 4 + 10 * B) +
        ∑ t, ∑ u, if C t u then (1 : ℝ) else 0 := by
    calc
      _ ≤ ∑ t, ∑ u, ((1 / 4 + 10 * B) + if C t u then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro t _
        apply Finset.sum_le_sum
        intro u _
        by_cases h : C t u
        · simp only [if_pos h]
          have := hpr1 (fun y => I t y ∧ I u y)
          linarith
        · simp only [if_neg h, add_zero]
          have := (abs_le.mp (hpair t u h)).2
          linarith
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  have hsecond : P.expect (fun y => empirical m I y ^ 2) ≤
      1 / 4 + 10 * B + 2 * e ^ 4 := by
    rw [hsecond_id]
    have h := (div_le_div_iff_of_pos_right (sq_pos_of_pos hmR)).2 hpairs
    rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt (sq_pos_of_pos hmR))] at h
    linarith
  have hvariance : P.expect (fun y => (empirical m I y - 1 / 2) ^ 2) ≤ 22 * e ^ 4 := by
    have hid : P.expect (fun y => (empirical m I y - 1 / 2) ^ 2) =
        P.expect (fun y => empirical m I y ^ 2) - P.expect (empirical m I) + 1 / 4 := by
      calc
        _ = P.expect (fun y => (empirical m I y ^ 2 + -empirical m I y) + 1 / 4) := by
          congr 1; funext y; ring
        _ = _ := by
          rw [FinProb.expect_add, FinProb.expect_add, FinProb.expect_const]
          have hn := FinProb.expect_smul P (-1) (empirical m I)
          simp only [neg_one_mul] at hn
          rw [hn]; ring
    rw [hid]
    linarith
  have hpoint : e ^ 2 * P.pr (fun y => empirical m I y < 1 / 2 - e) ≤
      P.expect (fun y => (empirical m I y - 1 / 2) ^ 2) := by
    unfold FinProb.pr FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    by_cases h : empirical m I y < 1 / 2 - e
    · simp only [if_pos h]
      have hs : e ^ 2 ≤ (empirical m I y - 1 / 2) ^ 2 := by
        have hh := pow_le_pow_left₀ he.le (show e ≤ 1 / 2 - empirical m I y by linarith) 2
        nlinarith
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hs (P.nonneg y)
    · simp only [if_neg h, mul_zero]
      exact mul_nonneg (P.nonneg y) (sq_nonneg _)
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  apply (mul_le_mul_iff_right₀ he2).mp
  nlinarith [le_trans hpoint hvariance]

theorem pr_exists_le {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (P : FinProb Ω) (S : Finset ι) (A : ι → Ω → Prop) :
    P.pr (fun y => ∃ a ∈ S, A a y) ≤ ∑ a ∈ S, P.pr (A a) := by
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert a S ha ih =>
    have hid : (fun y => ∃ a' ∈ insert a S, A a' y) =
        (fun y => A a y ∨ ∃ a' ∈ S, A a' y) := by funext y; simp
    rw [hid, Finset.sum_insert ha]
    exact le_trans (P.pr_union _ _) (add_le_add le_rfl ih)

open S18
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

noncomputable def prefixLaw (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmass : 0 < D.retainedMass j side tests) :
    FinProb (Fin (T.S.N k)) where
  w y := (if D.passes j side tests y then D.maskWeight side y else 0) /
    D.retainedMass j side tests
  nonneg y := by
    apply div_nonneg _ hmass.le
    split_ifs
    · unfold LateData.maskWeight; split_ifs <;> positivity
    · exact le_rfl
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self hmass.ne'

theorem prefixLaw_pr (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmass : 0 < D.retainedMass j side tests)
    (A : Fin (T.S.N k) → Prop) :
    (prefixLaw D j side tests hmass).pr A =
      (∑ y, if D.passes j side tests y ∧ A y then D.maskWeight side y else 0) /
        D.retainedMass j side tests := by
  unfold FinProb.pr prefixLaw
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : D.passes j side tests y <;> by_cases hA : A y <;> simp [h, hA]

theorem prefix_sketch_failure (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b) (hsupport : S18.InitialSketchSupport D j h side)
    (order : List (Finset (Fin (T.S.n k)))) (q : ℕ) (a : Fin (T.S.n k))
    (hcut : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side (D.prefixTests order q))
    (hmom : D.prefixMoments j h side order q a) (hR1 : D.R1 j side)
    (hm : 0 < sketchLength T k) (he : 0 < D.error (flipPos b a) j)
    (hB : bstar T k ≤ D.error (flipPos b a) j ^ 4) :
    (prefixLaw D j side (D.prefixTests order q)
      ((Real.exp_pos _).trans_le hcut)).pr
      (fun y => D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j) ≤
        22 * D.error (flipPos b a) j ^ 2 := by
  let tests := D.prefixTests order q
  let P := prefixLaw D j side tests ((Real.exp_pos _).trans_le hcut)
  obtain ⟨hfirst, hpair⟩ := hmom hcut
  apply empirical_lower_tail P (sketchLength T k) hm
    (fun t y => Hits (T.S.E k) PT.tiling.c (side.2.1 a t) y)
    (fun t u => ¬ D.nonconflict (flipPos b a) (side.2.1 a t) (side.2.1 a u))
    (D.error (flipPos b a) j) (bstar T k) he hB
  · intro t
    rw [prefixLaw_pr]
    exact hfirst _ (hsupport a t)
  · intro t u hnc
    rw [prefixLaw_pr]
    have hh := hpair _ _ (hsupport a t) (hsupport a u) (not_not.mp hnc)
    convert hh using 1
    congr 8
    funext y
    by_cases hp : D.passes j side tests y <;>
      by_cases ht : Hits (T.S.E k) PT.tiling.c (side.2.1 a t) y <;>
      by_cases hu : Hits (T.S.E k) PT.tiling.c (side.2.1 a u) y <;>
      simp [tests] at hp <;> simp [tests, hp, ht, hu]
  · convert hR1 a using 1
    congr 8
    funext t
    apply Finset.sum_congr rfl
    intro u _
    by_cases hn : D.nonconflict (flipPos b a) (side.2.1 a t) (side.2.1 a u) <;> simp [hn]

theorem prefix_batch_retention (D : LateData hPT) (j : Fin D.geom.r)
    {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests B : Finset (Fin (T.S.n k))) (hmass : 0 < D.retainedMass j side tests)
    (htail : ∀ a ∈ B, (prefixLaw D j side tests hmass).pr
      (fun y => D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j) ≤
        22 * D.error (flipPos b a) j ^ 2) :
    (1 - ∑ a ∈ B, 22 * D.error (flipPos b a) j ^ 2) * D.retainedMass j side tests ≤
      D.retainedMass j side (tests ∪ B) := by
  let P := prefixLaw D j side tests hmass
  have hbad := pr_exists_le P B
    (fun a y => D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j)
  have hsum := Finset.sum_le_sum fun a ha => htail a ha
  have hcomp : P.pr (fun y => ∃ a ∈ B,
      D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j) +
      P.pr (D.passes j side B) = 1 := by
    conv_rhs => rw [← P.sum_eq_one]
    unfold FinProb.pr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hb : D.passes j side B y
    · have hn : ¬ ∃ a ∈ B,
          D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j := by
        rintro ⟨a, ha, hlt⟩
        exact (not_lt_of_ge (hb a ha)) hlt
      simp only [if_neg hn, if_pos hb, zero_add]
    · have hx : ∃ a ∈ B,
          D.sketchHit side a y < 1 / 2 - D.error (flipPos b a) j := by
        unfold LateData.passes at hb
        push_neg at hb
        exact hb
      simp only [if_pos hx, if_neg hb, add_zero]
  have hkeep : P.pr (D.passes j side B) =
      D.retainedMass j side (tests ∪ B) / D.retainedMass j side tests := by
    rw [prefixLaw_pr]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    have hp : D.passes j side (tests ∪ B) y ↔
        D.passes j side tests y ∧ D.passes j side B y := by
      simp only [LateData.passes, Finset.mem_union]
      constructor
      · intro hp
        exact ⟨fun a ha => hp a (Or.inl ha), fun a ha => hp a (Or.inr ha)⟩
      · rintro ⟨ht, hb⟩ a (ha | ha)
        · exact ht a ha
        · exact hb a ha
    simp only [hp]
  rw [hkeep] at hcomp
  apply (le_div_iff₀ hmass).mp
  linarith

end HypercubeRamsey.Lane_sol_s18_1b
