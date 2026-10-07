import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Tools.Concentration

namespace HypercubeRamsey

open scoped BigOperators
open Classical

/-- Integrate a pointwise bound on one coordinate of a finite product law. -/
theorem FinProb.pr_piSplitAt_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (A : (∀ j, Ω j) → Prop) (p : ℝ)
    (hp : 0 ≤ p)
    (hbound : ∀ rest : (∀ j : {j // j ≠ i}, Ω j.1),
      (∑ x, if A ((Equiv.piSplitAt i Ω).symm (x, rest)) then (P i).w x else 0) ≤ p) :
    (FinProb.pi P).pr A ≤ p := by
  classical
  let R : FinProb (∀ j : {j // j ≠ i}, Ω j.1) := FinProb.pi (fun j => P j.1)
  have hprod (x : Ω i) (rest : ∀ j : {j // j ≠ i}, Ω j.1) :
      (∏ j, (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)) =
        (P i).w x * R.w rest := by
    let f : ι → ℝ := fun j => (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)
    have hi : (Equiv.piSplitAt i Ω).symm (x, rest) i = x := by
      simp [Equiv.piSplitAt]
    have hrest : (∏ j ∈ Finset.univ.erase i, f j) = R.w rest := by
      have hset : Finset.univ.erase i = Finset.univ.filter (fun j : ι => j ≠ i) := by
        ext j
        simp
      rw [hset]
      rw [← Finset.prod_subtype_eq_prod_filter
        (s := Finset.univ) (p := fun j : ι => j ≠ i)]
      dsimp [R, FinProb.pi]
      have hsub :
          Finset.univ.subtype (fun j : ι => j ≠ i) =
            (Finset.univ : Finset {j // j ≠ i}) := by
        ext j
        simp
      rw [hsub]
      change (∏ j : {j // j ≠ i}, f j.1) = ∏ j : {j // j ≠ i}, (P j.1).w (rest j)
      apply Finset.prod_congr rfl
      intro j hj
      simp [f, Equiv.piSplitAt, j.2]
    calc
      ∏ j, f j = (∏ j ∈ Finset.univ.erase i, f j) * f i := by
        simpa [f] using (Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)).symm
      _ = (P i).w x * R.w rest := by
        rw [hrest]
        change R.w rest * (P i).w ((Equiv.piSplitAt i Ω).symm (x, rest) i) = _
        rw [hi]
        ring
  change (∑ ω, if A ω then ∏ j, (P j).w (ω j) else 0) ≤ p
  let e := Equiv.piSplitAt i Ω
  have hEquivSum :
      (∑ ω, if A ω then ∏ j, (P j).w (ω j) else 0) =
        ∑ z : Ω i × (∀ j : {j // j ≠ i}, Ω j.1),
          if A (e.symm z) then ∏ j, (P j).w ((e.symm z) j) else 0 := by
    exact Fintype.sum_equiv e _ _ (by intro ω; simp only [Equiv.symm_apply_apply])
  rw [hEquivSum]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hrewrite :
      (∑ rest, ∑ x, if A (e.symm (x, rest)) then
          (∏ j, (P j).w ((e.symm (x, rest)) j)) else 0) =
        ∑ rest, R.w rest *
          (∑ x, if A (e.symm (x, rest)) then (P i).w x else 0) := by
    apply Finset.sum_congr rfl
    intro rest hrest
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hprod]
    by_cases hA : A (e.symm (x, rest)) <;> simp [hA, mul_comm]
  rw [hrewrite]
  calc
    (∑ rest, R.w rest *
        (∑ x, if A (e.symm (x, rest)) then (P i).w x else 0)) ≤
        ∑ rest, R.w rest * p := by
      apply Finset.sum_le_sum
      intro rest hrest
      exact mul_le_mul_of_nonneg_left (hbound rest) (R.nonneg rest)
    _ = p := by
      rw [← Finset.sum_mul]
      rw [R.sum_eq_one]
      ring

/-- The expectation of a function under a finite product, split at one coordinate. -/
theorem FinProb.expect_piSplitAt_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (X : (∀ j, Ω j) → ℝ) :
    (FinProb.pi P).expect X =
      ∑ rest : (∀ j : {j // j ≠ i}, Ω j.1),
        (FinProb.pi (fun j => P j.1)).w rest *
          (∑ x, (P i).w x * X ((Equiv.piSplitAt i Ω).symm (x, rest))) := by
  classical
  let R : FinProb (∀ j : {j // j ≠ i}, Ω j.1) := FinProb.pi (fun j => P j.1)
  have hprod (x : Ω i) (rest : ∀ j : {j // j ≠ i}, Ω j.1) :
      (∏ j, (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)) =
        (P i).w x * R.w rest := by
    let f : ι → ℝ := fun j => (P j).w (((Equiv.piSplitAt i Ω).symm (x, rest)) j)
    have hi : (Equiv.piSplitAt i Ω).symm (x, rest) i = x := by
      simp [Equiv.piSplitAt]
    have hrest : (∏ j ∈ Finset.univ.erase i, f j) = R.w rest := by
      have hset : Finset.univ.erase i = Finset.univ.filter (fun j : ι => j ≠ i) := by
        ext j
        simp
      rw [hset]
      rw [← Finset.prod_subtype_eq_prod_filter
        (s := Finset.univ) (p := fun j : ι => j ≠ i)]
      dsimp [R, FinProb.pi]
      have hsub :
          Finset.univ.subtype (fun j : ι => j ≠ i) =
            (Finset.univ : Finset {j // j ≠ i}) := by
        ext j
        simp
      rw [hsub]
      change (∏ j : {j // j ≠ i}, f j.1) = ∏ j : {j // j ≠ i}, (P j.1).w (rest j)
      apply Finset.prod_congr rfl
      intro j hj
      simp [f, Equiv.piSplitAt, j.2]
    calc
      ∏ j, f j = (∏ j ∈ Finset.univ.erase i, f j) * f i := by
        simpa [f] using (Finset.prod_erase_mul Finset.univ f (Finset.mem_univ i)).symm
      _ = (P i).w x * R.w rest := by
        rw [hrest]
        change R.w rest * (P i).w ((Equiv.piSplitAt i Ω).symm (x, rest) i) = _
        rw [hi]
        ring
  change (∑ ω, (∏ j, (P j).w (ω j)) * X ω) = _
  let e := Equiv.piSplitAt i Ω
  have hEquivSum :
      (∑ ω, (∏ j, (P j).w (ω j)) * X ω) =
        ∑ z : Ω i × (∀ j : {j // j ≠ i}, Ω j.1),
          (∏ j, (P j).w ((e.symm z) j)) * X (e.symm z) := by
    exact Fintype.sum_equiv e _ _ (by intro ω; simp only [Equiv.symm_apply_apply])
  rw [hEquivSum, Fintype.sum_prod_type, Finset.sum_comm]
  have hrewrite :
      (∑ rest, ∑ x,
        (∏ j, (P j).w ((e.symm (x, rest)) j)) * X (e.symm (x, rest))) =
        ∑ rest, R.w rest *
          (∑ x, (P i).w x * X (e.symm (x, rest))) := by
    apply Finset.sum_congr rfl
    intro rest hrest
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hprod]
    ring
  rw [hrewrite]

/-- The squared likelihood tilt of a finite law. -/
noncomputable def FinProb.squareTilt
    {ι : Type*} [Fintype ι] (P : FinProb ι) (m : ι → ℝ)
    (hpos : 0 < ∑ i, P.w i * (m i) ^ 2) : FinProb ι where
  w i := P.w i * (m i) ^ 2 / ∑ j, P.w j * (m j) ^ 2
  nonneg i := div_nonneg (mul_nonneg (P.nonneg i) (sq_nonneg _)) hpos.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hpos)

namespace Law

/-- Condition a finite law on a set when it has positive mass, and leave it unchanged on a null set. -/
noncomputable def restrictOrSelf {N : ℕ} (μ : Law N) (A : Finset (Fin N)) : Law N :=
  if h : 0 < ∑ x ∈ A, μ.w x then Law.restrict μ A h else μ

end Law

/-- Jensen's square inequality for a finite law. -/
theorem FinProb.expect_sq_ge_sq_expect {ι : Type*} [Fintype ι]
    (P : FinProb ι) (f : ι → ℝ) :
    (P.expect f) ^ 2 ≤ P.expect (fun i => (f i) ^ 2) := by
  classical
  let m := P.expect f
  have hvar : 0 ≤ P.expect (fun i => (f i - m) ^ 2) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (P.nonneg i) (sq_nonneg _)
  have hcalc :
      P.expect (fun i => (f i - m) ^ 2) =
        P.expect (fun i => (f i) ^ 2) - m ^ 2 := by
    unfold FinProb.expect at *
    calc
      (∑ i, P.w i * (f i - m) ^ 2) =
          ∑ i, (P.w i * (f i) ^ 2 - 2 * m * (P.w i * f i) + m ^ 2 * P.w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, P.w i * (f i) ^ 2) -
          2 * m * (∑ i, P.w i * f i) + m ^ 2 * (∑ i, P.w i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [Finset.mul_sum, Finset.mul_sum] <;> ring
      _ = (∑ i, P.w i * (f i) ^ 2) - m ^ 2 := by
        simp [m, FinProb.expect, P.sum_eq_one] <;> ring
  have hvar' : 0 ≤ P.expect (fun i => (f i) ^ 2) - (P.expect f) ^ 2 := by
    simpa [m] using hvar.trans_eq hcalc
  linarith

/-- Expanding a squared degree gives the expected common-neighbor codegree. -/
theorem FinProb.expect_rowDeg_sq_eq_codeg {N : ℕ}
    (μ π : Law N) (E : Fin N → Fin N → Prop) (G : Colour) :
    μ.expect (fun x => (rowDeg E G x π) ^ 2) =
      ∑ y, ∑ y', π.w y * π.w y' * codeg E G μ y y' := by
  classical
  unfold FinProb.expect rowDeg codeg
  have hinner (x : Fin N) :
      (∑ y, π.w y * (if Hits E G x y then (1 : ℝ) else 0)) ^ 2 =
        ∑ y, ∑ y', π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0) := by
    rw [pow_two, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro y' hy'
    by_cases hxy : Hits E G x y <;> by_cases hxy' : Hits E G x y' <;>
      simp [hxy, hxy'] <;> ring
  calc
    (∑ x, μ.w x *
        (∑ y, π.w y * (if Hits E G x y then (1 : ℝ) else 0)) ^ 2) =
      ∑ x, μ.w x *
        (∑ y, ∑ y', π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hinner]
    _ = ∑ x, ∑ y, ∑ y', μ.w x * (π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
    _ = ∑ y, ∑ y', ∑ x, μ.w x * (π.w y * π.w y' *
          (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ y, ∑ y', π.w y * π.w y' *
          (∑ x, μ.w x *
            (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro y' hy'
      calc
        (∑ x, μ.w x * (π.w y * π.w y' *
            (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0))) =
            ∑ x, (π.w y * π.w y') * (μ.w x *
              (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = π.w y * π.w y' *
            (∑ x, μ.w x *
              (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0)) := by
          rw [Finset.mul_sum]
    _ = ∑ y, ∑ y', π.w y * π.w y' *
          ∑ x, μ.w x *
            (if Hits E G x y ∧ Hits E G x y' then (1 : ℝ) else 0) := rfl

/-- A finite union bound for events in a finite probability space. -/
theorem FinProb.pr_iUnion_le_s10
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinProb Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  calc
    P.pr (fun ω => ∃ i, A i ω) =
        ∑ ω, if ∃ i, A i ω then P.w ω else 0 := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∃ i, A i ω <;> simp [h]
    _ ≤ ∑ ω, ∑ i, if A i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hA : ∃ i, A i ω
      · obtain ⟨i, hi⟩ := hA
        have hExist : ∃ i, A i ω := ⟨i, hi⟩
        have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
            0 ≤ if A j ω then P.w ω else 0 := by
          intro j hj
          split_ifs <;> simp [P.nonneg ω]
        have hsingle : P.w ω ≤ ∑ j, if A j ω then P.w ω else 0 := by
          calc
            P.w ω = if A i ω then P.w ω else 0 := by simp [hi]
            _ ≤ ∑ j, if A j ω then P.w ω else 0 :=
              Finset.single_le_sum hnonneg (Finset.mem_univ i)
        simpa [hExist] using hsingle
      · have hnonneg : ∀ j ∈ (Finset.univ : Finset ι),
            0 ≤ if A j ω then P.w ω else 0 := by
          intro j hj
          split_ifs <;> simp [P.nonneg ω]
        simp [hA]
        exact Finset.sum_nonneg hnonneg
    _ = ∑ i, P.pr (A i) := by
      rw [Finset.sum_comm]
      rfl

/-- The chord of `log` between `θ` and `1` lies below `log`, including after clipping at `θ`. -/
theorem real_log_max_ge_chord {θ x : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.log (max θ x) ≥ Real.log θ * (1 - x) / (1 - θ) := by
  let z : ℝ := max θ x
  let lam : ℝ := (z - θ) / (1 - θ)
  have hz0 : 0 < z := lt_of_lt_of_le hθ0 (le_max_left θ x)
  have hz1 : z ≤ 1 := max_le hθ1.le hx1
  have hzt : θ ≤ z := le_max_left θ x
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact div_nonneg (sub_nonneg.mpr hzt) (sub_nonneg.mpr hθ1.le)
  have hlam1 : lam ≤ 1 := by
    dsimp [lam]
    rw [div_le_one (sub_pos.mpr hθ1)]
    linarith
  have hleft : 0 ≤ 1 - lam := by linarith
  have hinterp : (1 - lam) * θ + lam * 1 = z := by
    dsimp [lam]
    field_simp [ne_of_gt (sub_pos.mpr hθ1)]
    ring
  have hconc : (1 - lam) * Real.log θ + lam * Real.log 1 ≤
      Real.log ((1 - lam) * θ + lam * 1) := by
    simpa [smul_eq_mul] using
      (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hθ0)
        (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1)) hleft hlam0 (by ring)
  have hlogθ : Real.log θ ≤ 0 := by
    calc
      Real.log θ ≤ Real.log 1 := Real.log_le_log hθ0 hθ1.le
      _ = 0 := by simp
  have hweight : 1 - lam = (1 - z) / (1 - θ) := by
    dsimp [lam]
    field_simp [ne_of_gt (sub_pos.mpr hθ1)]
    ring
  have hline : Real.log θ * (1 - z) / (1 - θ) ≤ Real.log z := by
    simp only [Real.log_one, mul_zero, add_zero] at hconc
    rw [hinterp] at hconc
    rw [hweight] at hconc
    convert hconc using 1 <;> ring
  have hline_mono : Real.log θ * (1 - x) / (1 - θ) ≤
      Real.log θ * (1 - z) / (1 - θ) := by
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hθ1.le)
    exact mul_le_mul_of_nonpos_left (sub_le_sub_left (le_max_right θ x) 1) hlogθ
  simpa [z] using hline_mono.trans hline

/-- Jensen's chord lower bound for a clipped logarithm under a finite law. -/
theorem FinProb.expect_log_max_ge_chord {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (θ : ℝ) (q : Ω → ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hq : ∀ ω, 0 ≤ q ω ∧ q ω ≤ 1) :
    P.expect (fun ω => Real.log (max θ (q ω))) ≥
      Real.log θ * (1 - P.expect q) / (1 - θ) := by
  have hpoint (ω : Ω) :
      Real.log θ * (1 - q ω) / (1 - θ) ≤ Real.log (max θ (q ω)) :=
    real_log_max_ge_chord hθ0 hθ1 (hq ω).1 (hq ω).2
  calc
    P.expect (fun ω => Real.log (max θ (q ω))) ≥
        P.expect (fun ω => Real.log θ * (1 - q ω) / (1 - θ)) := by
      unfold FinProb.expect
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hpoint ω) (P.nonneg ω)
    _ = Real.log θ * (1 - P.expect q) / (1 - θ) := by
      unfold FinProb.expect
      have hsum :
          (∑ ω, P.w ω * (Real.log θ * (1 - q ω) / (1 - θ))) =
            (Real.log θ * (1 - θ)⁻¹) * (∑ ω, P.w ω * (1 - q ω)) := by
        calc
          (∑ ω, P.w ω * (Real.log θ * (1 - q ω) / (1 - θ))) =
              ∑ ω, (Real.log θ * (1 - θ)⁻¹) * (P.w ω * (1 - q ω)) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (Real.log θ * (1 - θ)⁻¹) * (∑ ω, P.w ω * (1 - q ω)) := by
            rw [Finset.mul_sum]
      have hsum2 : (∑ ω, P.w ω * (1 - q ω)) =
          1 - ∑ ω, P.w ω * q ω := by
        calc
          (∑ ω, P.w ω * (1 - q ω)) =
              ∑ ω, (P.w ω - P.w ω * q ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (∑ ω, P.w ω) - ∑ ω, P.w ω * q ω := by
            rw [← Finset.sum_sub_distrib]
          _ = 1 - ∑ ω, P.w ω * q ω := by rw [P.sum_eq_one]
      rw [hsum, hsum2]
      ring

namespace FinProb

theorem p_s10_1c_pr_fiber_single_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω : Ω) (hω : A ω) : P.w ω ≤ P.pr A := by
  classical
  unfold FinProb.pr
  calc
    P.w ω = if A ω then P.w ω else 0 := by simp [hω]
    _ ≤ ∑ x, if A x then P.w x else 0 :=
      Finset.single_le_sum
        (f := fun x => if A x then P.w x else 0)
        (fun x hx => by split_ifs with hAx <;> simp [P.nonneg x])
        (Finset.mem_univ ω)

theorem p_s10_1c_expect_cond_eq_sum {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) [DecidablePred A] (hA : 0 < P.pr A) (f : Ω → ℝ) :
    (P.cond A hA).expect f =
      (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
  classical
  simp only [FinProb.expect, FinProb.cond]
  calc
    _ = ∑ ω, (if A ω then P.w ω * f ω else 0) / P.pr A := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : A ω <;> simp [h] <;> field_simp [ne_of_gt hA] <;> ring
    _ = (∑ ω, if A ω then P.w ω * f ω else 0) / P.pr A := by
      rw [Finset.sum_div]

theorem p_s10_1c_expect_exp_neg_centered_cond_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (hA : 0 < P.pr A) (X : Ω → ℝ)
    (a b μ s : ℝ) (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b)
    (hs : 0 ≤ s)
    (hmean : μ * P.pr A ≤ ∑ ω, if A ω then P.w ω * X ω else 0) :
    (P.cond A hA).expect (fun ω => Real.exp (-s * (X ω - μ))) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  let Q := P.cond A hA
  have hμ : μ ≤ Q.expect X := by
    rw [p_s10_1c_expect_cond_eq_sum]
    exact (le_div_iff₀ hA).2 hmean
  let mQ : ℝ := Q.expect X
  have hhoeffding := xHoeffdingLemma Q X a b (-s) hab hX
  have hhoeffding' : Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) ≤
      Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
    simpa [mQ, pow_two] using hhoeffding
  have hfactor : Q.expect (fun ω => Real.exp (-s * (X ω - μ))) =
      Real.exp (s * (μ - mQ)) * Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) := by
    unfold FinProb.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    change Q.w ω * Real.exp (-s * (X ω - μ)) =
      Real.exp (s * (μ - mQ)) * (Q.w ω * Real.exp (-s * (X ω - mQ)))
    have he : -s * (X ω - μ) = s * (μ - mQ) + -s * (X ω - mQ) := by ring
    rw [he, Real.exp_add]
    ring_nf
  have hscalar : Real.exp (s * (μ - mQ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    dsimp [mQ]
    nlinarith
  have hcenter_nonneg : 0 ≤ Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (Q.nonneg ω) (Real.exp_nonneg _)
  rw [hfactor]
  calc
    _ ≤ 1 * Q.expect (fun ω => Real.exp (-s * (X ω - mQ))) :=
      mul_le_mul_of_nonneg_right hscalar hcenter_nonneg
    _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by simpa using hhoeffding'

theorem p_s10_1c_fiber_exp_neg_centered_le {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) [DecidablePred A] (X : Ω → ℝ) (a b μ s : ℝ)
    (hab : a ≤ b) (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b) (hs : 0 ≤ s)
    (hmean : P.pr A = 0 ∨ μ * P.pr A ≤
      ∑ ω, if A ω then P.w ω * X ω else 0) :
    (∑ ω, if A ω then P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
      P.pr A * Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by
  classical
  have hqnonneg : 0 ≤ P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_nonneg
    intro ω hω
    by_cases hA : A ω
    · simp [hA, P.nonneg ω]
    · simp [hA]
  by_cases hq : P.pr A = 0
  · have hzero (ω : Ω) (hω : A ω) : P.w ω = 0 := by
      have hle := p_s10_1c_pr_fiber_single_le P A ω hω
      rw [hq] at hle
      exact le_antisymm hle (P.nonneg ω)
    have hsum :
        (∑ ω, if A ω then P.w ω * Real.exp (-s * (X ω - μ)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hA : A ω <;> simp [hA, hzero ω]
    rw [hsum, hq]
    simp
  · have hqpos : 0 < P.pr A := by
      by_contra hnot
      have hle : P.pr A ≤ 0 := le_of_not_gt hnot
      exact hq (le_antisymm hle hqnonneg)
    have hmean' : μ * P.pr A ≤ ∑ ω, if A ω then P.w ω * X ω else 0 := by
      rcases hmean with hz | hmean'
      · exact (hq hz).elim
      · exact hmean'
    have hcond := p_s10_1c_expect_exp_neg_centered_cond_le
      P A hqpos X a b μ s hab hX hs hmean'
    rw [p_s10_1c_expect_cond_eq_sum] at hcond
    have hmul := (div_le_iff₀ hqpos).mp hcond
    calc
      _ ≤ Real.exp (s ^ 2 * (b - a) ^ 2 / 8) * P.pr A := hmul
      _ = P.pr A * Real.exp (s ^ 2 * (b - a) ^ 2 / 8) := by ring

theorem p_s10_1c_expect_mul_fiber_exp_neg_centered_le
    {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]
    (P : FinProb Ω) (history : Ω → H) (F X : Ω → ℝ) (μ s E : ℝ)
    (hFfiber : ∀ ω ω', history ω = history ω' → F ω = F ω')
    (hFnonneg : ∀ ω, 0 ≤ F ω)
    (hlocal : ∀ h : H,
      (∑ ω, if history ω = h then P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
        (∑ ω, if history ω = h then P.w ω else 0) * E) :
    P.expect (fun ω => F ω * Real.exp (-s * (X ω - μ))) ≤ E * P.expect F := by
  classical
  have hfiber (h : H) :
      (∑ ω, if history ω = h then P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0) ≤
        E * (∑ ω, if history ω = h then P.w ω * F ω else 0) := by
    by_cases hex : ∃ ω, history ω = h
    · obtain ⟨ω₀, hω₀⟩ := hex
      have hleft :
          (∑ ω, if history ω = h then P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0) =
            F ω₀ * (∑ ω, if history ω = h then P.w ω * Real.exp (-s * (X ω - μ)) else 0) := by
        calc
          _ = ∑ ω, (if history ω = h then P.w ω else 0) *
              (F ω₀ * Real.exp (-s * (X ω - μ))) := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h
            · have hF := hFfiber ω ω₀ (hωh.trans hω₀.symm)
              simp [hωh, hF]
            · simp [hωh]
          _ = F ω₀ * (∑ ω, if history ω = h then
                P.w ω * Real.exp (-s * (X ω - μ)) else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h <;> simp [hωh] <;> ring
      have hright :
          (∑ ω, if history ω = h then P.w ω * F ω else 0) =
            F ω₀ * (∑ ω, if history ω = h then P.w ω else 0) := by
        calc
          _ = ∑ ω, (if history ω = h then P.w ω else 0) * F ω₀ := by
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h
            · have hF := hFfiber ω ω₀ (hωh.trans hω₀.symm)
              simp [hωh, hF, mul_comm]
            · simp [hωh]
          _ = F ω₀ * (∑ ω, if history ω = h then P.w ω else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ω hω
            by_cases hωh : history ω = h <;> simp [hωh, mul_comm]
      rw [hleft, hright]
      calc
        F ω₀ * (∑ ω, if history ω = h then
            P.w ω * Real.exp (-s * (X ω - μ)) else 0) ≤
            F ω₀ * ((∑ ω, if history ω = h then P.w ω else 0) * E) :=
          mul_le_mul_of_nonneg_left (hlocal h) (hFnonneg ω₀)
        _ = E * (F ω₀ * ∑ ω, if history ω = h then P.w ω else 0) := by ring
    · have hnone (ω : Ω) : history ω ≠ h := by
        intro heq
        exact hex ⟨ω, heq⟩
      simp [hnone]
  have hpartition (ω : Ω) :
      P.w ω * (F ω * Real.exp (-s * (X ω - μ))) =
        ∑ h : H, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := by
    rw [Finset.sum_eq_single (history ω)]
    · simp
    · intro h hh hne
      have hne' : history ω ≠ h := fun heq => hne heq.symm
      simp [hne']
    · simp
  have hsumF :
      (∑ h : H, ∑ ω, if history ω = h then P.w ω * F ω else 0) = P.expect F := by
    unfold FinProb.expect
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.sum_eq_single (history ω)]
    · simp
    · intro h hh hne
      have hne' : history ω ≠ h := fun heq => hne heq.symm
      simp [hne']
    · simp
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * (F ω * Real.exp (-s * (X ω - μ)))) =
        ∑ ω, ∑ h : H, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact hpartition ω
    _ = ∑ h : H, ∑ ω, if history ω = h then
          P.w ω * (F ω * Real.exp (-s * (X ω - μ))) else 0 := Finset.sum_comm
    _ ≤ ∑ h : H, E * (∑ ω, if history ω = h then P.w ω * F ω else 0) :=
      Finset.sum_le_sum fun h hh => hfiber h
    _ = E * P.expect F := by
      rw [← Finset.mul_sum, hsumF]

end FinProb

/-- Local adapted finite Azuma bound, used until the shared concentration node lands. -/
theorem p_s10_1c_xAzuma {Ω : Type*} [Fintype Ω] {k : ℕ}
    (H : Fin (k + 1) → Type*) [∀ t, Fintype (H t)] [∀ t, DecidableEq (H t)] (P : FinProb Ω)
    (history : ∀ t, Ω → H t)
    (project : ∀ i : Fin k, H i.succ → H i.castSucc)
    (hfiltration : ∀ i ω, history i.castSucc ω = project i (history i.succ ω))
    (Δ : Fin k → Ω → ℝ)
    (hadapted : ∀ (m : ℕ) (hm : m ≤ k) (i : Fin k), i.val < m →
      ∀ ω ω', history ⟨m, Nat.lt_succ_of_le hm⟩ ω = history ⟨m, Nat.lt_succ_of_le hm⟩ ω' →
        Δ i ω = Δ i ω')
    (μ lo hi : Fin k → ℝ)
    (hbound : ∀ i ω, lo i ≤ Δ i ω ∧ Δ i ω ≤ hi i)
    (hmean : ∀ i (h : H i.castSucc),
      P.pr (fun ω => history i.castSucc ω = h) = 0 ∨
        μ i * P.pr (fun ω => history i.castSucc ω = h) ≤
          (∑ ω, if history i.castSucc ω = h then P.w ω * Δ i ω else 0))
    (hwidth : 0 < ∑ i, (hi i - lo i) ^ 2) (t : ℝ) (ht : 0 < t) :
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
      Real.exp (-2 * t ^ 2 / ∑ i, (hi i - lo i) ^ 2) := by
  classical
  let yNat : ℕ → Ω → ℝ := fun j ω =>
    if hj : j < k then Δ ⟨j, hj⟩ ω - μ ⟨j, hj⟩ else 0
  let widthNat : ℕ → ℝ := fun j =>
    if hj : j < k then (hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ^ 2 else 0
  let S : ℕ → Ω → ℝ := fun m ω => ∑ j ∈ Finset.range m, yNat j ω
  let W : ℕ → ℝ := fun m => ∑ j ∈ Finset.range m, widthNat j
  let U : ℝ := ∑ i, (hi i - lo i) ^ 2
  have hU : 0 < U := by simpa [U] using hwidth
  let s : ℝ := 4 * t / U
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hΩ : Nonempty Ω := by
    by_contra hne
    haveI : IsEmpty Ω := not_nonempty_iff.mp hne
    have hsum : (∑ ω, P.w ω) = 0 := by simp
    rw [P.sum_eq_one] at hsum
    norm_num at hsum
  have hmgf : ∀ m, m ≤ k →
      P.expect (fun ω => Real.exp (-s * S m ω)) ≤
        Real.exp (s ^ 2 * W m / 8) := by
    intro m
    induction m with
    | zero =>
      intro hm
      simp [S, W, FinProb.expect, P.sum_eq_one]
    | succ m ih =>
      intro hm
      have hm_lt : m < k := by omega
      have hm_le : m ≤ k := by omega
      let i : Fin k := ⟨m, hm_lt⟩
      have hstep (ω : Ω) : S (m + 1) ω = S m ω + (Δ i ω - μ i) := by
        simp [S, yNat, Finset.sum_range_succ, i, hm_lt]
      have hwidthStep : W (m + 1) = W m + (hi i - lo i) ^ 2 := by
        simp [W, widthNat, Finset.sum_range_succ, i, hm_lt]
      have hab : lo i ≤ hi i := by
        obtain ⟨ω⟩ := hΩ
        exact (hbound i ω).1.trans (hbound i ω).2
      have hlocal (g : H i.castSucc) :
          (∑ ω, if history i.castSucc ω = g then
            P.w ω * Real.exp (-s * (Δ i ω - μ i)) else 0) ≤
          (∑ ω, if history i.castSucc ω = g then P.w ω else 0) *
            Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) := by
        have hlocal' := FinProb.p_s10_1c_fiber_exp_neg_centered_le P
          (fun ω => history i.castSucc ω = g) (Δ i) (lo i) (hi i) (μ i) s
          hab (fun ω => hbound i ω) hs (hmean i g)
        have hprob : P.pr (fun ω => history i.castSucc ω = g) =
            ∑ ω, if history i.castSucc ω = g then P.w ω else 0 := by
          unfold FinProb.pr
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hEq : history i.castSucc ω = g <;> simp [hEq]
        rw [hprob] at hlocal'
        exact hlocal'
      have hSfiber (ω ω' : Ω)
          (hh : history i.castSucc ω = history i.castSucc ω') : S m ω = S m ω' := by
        unfold S
        apply Finset.sum_congr rfl
        intro j hj
        have hj_lt : j < m := Finset.mem_range.mp hj
        have hj_k : j < k := lt_of_lt_of_le hj_lt (Nat.le_of_lt i.isLt)
        have hΔ := hadapted m hm_le ⟨j, hj_k⟩ hj_lt ω ω' hh
        simp [yNat, hj_k, hΔ]
      have hstepMgf :
          P.expect (fun ω => Real.exp (-s * S (m + 1) ω)) =
            P.expect (fun ω => Real.exp (-s * S m ω) *
              Real.exp (-s * (Δ i ω - μ i))) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro ω hω
        change P.w ω * Real.exp (-s * S (m + 1) ω) =
          P.w ω * (Real.exp (-s * S m ω) * Real.exp (-s * (Δ i ω - μ i)))
        have he : -s * S (m + 1) ω =
            (-s * S m ω) + (-s * (Δ i ω - μ i)) := by
          rw [hstep ω]
          ring
        rw [he, Real.exp_add]
      have htail := FinProb.p_s10_1c_expect_mul_fiber_exp_neg_centered_le P
        (history i.castSucc) (fun ω => Real.exp (-s * S m ω)) (Δ i) (μ i) s
        (Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8))
        (fun ω ω' hh => by rw [hSfiber ω ω' hh])
        (fun ω => Real.exp_nonneg _)
        hlocal
      calc
        P.expect (fun ω => Real.exp (-s * S (m + 1) ω)) =
            P.expect (fun ω => Real.exp (-s * S m ω) *
              Real.exp (-s * (Δ i ω - μ i))) := hstepMgf
        _ ≤ Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) *
              P.expect (fun ω => Real.exp (-s * S m ω)) := htail
        _ ≤ Real.exp (s ^ 2 * (hi i - lo i) ^ 2 / 8) *
              Real.exp (s ^ 2 * W m / 8) :=
            mul_le_mul_of_nonneg_left (ih hm_le) (Real.exp_nonneg _)
        _ = Real.exp (s ^ 2 * W (m + 1) / 8) := by
          rw [hwidthStep, ← Real.exp_add]
          congr 1
          ring
  have hWfull : W k = ∑ i, (hi i - lo i) ^ 2 := by
    dsimp [W, widthNat]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => if hj : j < k then (hi ⟨j, hj⟩ - lo ⟨j, hj⟩) ^ 2 else 0)]
    simp
  have hsumY (ω : Ω) : S k ω = ∑ i, (Δ i ω - μ i) := by
    dsimp [S, yNat]
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => if hj : j < k then Δ ⟨j, hj⟩ ω - μ ⟨j, hj⟩ else 0)]
    simp
  have hsumCentered (ω : Ω) :
      (∑ i, Δ i ω) - ∑ i, μ i = S k ω := by
    calc
      (∑ i, Δ i ω) - ∑ i, μ i = ∑ i, (Δ i ω - μ i) := by
        rw [Finset.sum_sub_distrib]
      _ = S k ω := (hsumY ω).symm
  have hevent (ω : Ω) :
      (∑ i, Δ i ω < (∑ i, μ i) - t) →
        t ≤ -((∑ i, Δ i ω) - ∑ i, μ i) := by
    intro h
    linarith
  have hmark := FinProb.pr_exp_markov P
    (fun ω => -((∑ i, Δ i ω) - ∑ i, μ i)) s t hs
  have hmgfMark :
      P.expect (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) ≤
        Real.exp (s ^ 2 * U / 8) := by
    have hfun : (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) =
        (fun ω => Real.exp (-s * S k ω)) := by
      funext ω
      rw [hsumCentered]
      congr 1
      ring
    rw [hfun]
    simpa [hWfull, U] using hmgf k le_rfl
  calc
    P.pr (fun ω => ∑ i, Δ i ω < (∑ i, μ i) - t) ≤
        P.pr (fun ω => t ≤ -((∑ i, Δ i ω) - ∑ i, μ i)) :=
      FinProb.pr_mono P _ _ hevent
    _ ≤ Real.exp (-s * t) *
          P.expect (fun ω => Real.exp (s * -((∑ i, Δ i ω) - ∑ i, μ i))) := hmark
    _ ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * U / 8) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact hmgfMark
    _ = Real.exp (-2 * t ^ 2 / U) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [s]
      field_simp [ne_of_gt hU]
      ring

end HypercubeRamsey
