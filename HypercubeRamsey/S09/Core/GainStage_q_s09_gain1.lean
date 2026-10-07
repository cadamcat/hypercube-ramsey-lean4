import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.Framework.OneShot

namespace HypercubeRamsey.Lane_q_s09_gain1

open HypercubeRamsey Classical
open scoped BigOperators

private theorem one_sign_mass {N : ℕ} {X : Finset (Fin N)}
    {wX err w : ℝ} (α : Law N)
    (hαX : α.SupportedIn X) (hαW : α.WidthLE w)
    (f : Fin N → ℝ)
    (hmean : ∀ ρ : Law N, ρ.SupportedIn X → ρ.WidthLE wX →
      |∑ x, ρ.w x * f x| ≤ err)
    (S : Finset (Fin N)) (hside : ∀ x ∈ S, err < f x) :
    ∑ x ∈ S, α.w x ≤ Real.exp (w - wX) := by
  classical
  by_contra hnot
  have hmass : Real.exp (w - wX) < ∑ x ∈ S, α.w x := lt_of_not_ge hnot
  have hmasspos : 0 < ∑ x ∈ S, α.w x := lt_trans (Real.exp_pos _) hmass
  let ρ : Law N := α.restrict S hmasspos
  have hlog : w - wX < Real.log (∑ x ∈ S, α.w x) := by
    have h := Real.log_lt_log (Real.exp_pos (w - wX)) hmass
    simpa only [Real.log_exp] using h
  have hρwidth : ρ.WidthLE wX := by
    apply Law.WidthLE.mono (Law.WidthLE.restrict hαW hmasspos)
    linarith
  have hρX : ρ.SupportedIn X := by
    intro x hx
    simp [ρ, Law.restrict, hαX x hx]
  have hρS : ρ.SupportedIn S := by
    intro x hx
    simp [ρ, Law.restrict, hx]
  have hρsumpos : 0 < ∑ x, ρ.w x := by
    rw [ρ.sum_eq_one]
    norm_num
  obtain ⟨x₀, hx₀, hx₀pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
      (by intro x hx; exact ρ.nonneg x)).mp hρsumpos
  have hx₀S : x₀ ∈ S := by
    by_contra hx
    have hzero := hρS x₀ hx
    simp [hzero] at hx₀pos
  have havg : err < ∑ x, ρ.w x * f x := by
    have hconst : (∑ x, ρ.w x * err) = err := by
      rw [← Finset.sum_mul, ρ.sum_eq_one]
      ring
    rw [← hconst]
    apply Finset.sum_lt_sum
    · intro x hx
      by_cases hxS : x ∈ S
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hside x hxS)) (ρ.nonneg x)
      · simp [hρS x hxS]
    · exact ⟨x₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hside x₀ hx₀S) hx₀pos⟩
  have hbound := hmean ρ hρX hρwidth
  rcases abs_le.mp hbound with ⟨hlo, hhi⟩
  linarith

private theorem dens_eq_rowDegree {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) : dens E G μ ν = ∑ x, μ.w x * rowDeg E G x ν := by
  classical
  simp only [dens, rowDeg]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

private theorem row_deviation_mean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    ∑ x, μ.w x * (rowDeg E G x ν - 1 / 2) = dens E G μ ν - 1 / 2 := by
  classical
  rw [dens_eq_rowDegree]
  calc
    (∑ x, μ.w x * (rowDeg E G x ν - 1 / 2)) =
        (∑ x, μ.w x * rowDeg E G x ν) - ∑ x, μ.w x * (1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ = (∑ x, μ.w x * rowDeg E G x ν) - 1 / 2 := by
          have hhalf : (∑ x, μ.w x * (1 / 2)) = 1 / 2 := by
            rw [← Finset.sum_mul, μ.sum_eq_one]
            ring
          rw [hhalf]

private theorem col_deviation_mean {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ ν : Law N) :
    ∑ y, ν.w y * (colDeg E G μ y - 1 / 2) = dens E G μ ν - 1 / 2 := by
  classical
  have hdens : dens E G μ ν = ∑ y, ν.w y * colDeg E G μ y := by
    unfold dens colDeg
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hdens]
  calc
    (∑ y, ν.w y * (colDeg E G μ y - 1 / 2)) =
        (∑ y, ν.w y * colDeg E G μ y) - ∑ y, ν.w y * (1 / 2) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = (∑ y, ν.w y * colDeg E G μ y) - 1 / 2 := by
          have hhalf : (∑ y, ν.w y * (1 / 2)) = 1 / 2 := by
            rw [← Finset.sum_mul, ν.sum_eq_one]
            ring
          rw [hhalf]

/-- Degree outliers under the first law, by conditioning on either signed exceptional set. -/
theorem forward_bound {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (lam : Law N) (hlamY : lam.SupportedIn Y) (hlamW : lam.WidthLE (P.Sd (n : ℝ)))
    (α : Law N) (hαX : α.SupportedIn X) (w : ℝ) (hαW : α.WidthLE w)
    (hw : w ≤ (n : ℝ) ^ (P.xD : ℝ)) :
    ∑ x ∈ Finset.univ.filter (fun x => 2 * P.bStar n < |rowDeg E G x lam - 1 / 2|), α.w x ≤
      2 * Real.exp (w - (n : ℝ) ^ (P.xD : ℝ)) := by
  classical
  let err : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))
  let W : ℝ := (n : ℝ) ^ (P.xD : ℝ)
  have hdisc : DiscOne E X Y W (P.Sd (n : ℝ)) err := by
    change DiscOne E X Y W (P.Sd (n : ℝ)) err at hdeep
    exact hdeep
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hbstar_nonneg : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    positivity
  let q : Fin N → ℝ := fun x => rowDeg E G x lam - 1 / 2
  let Splus : Finset (Fin N) := Finset.univ.filter (fun x => 2 * P.bStar n < q x)
  let Sminus : Finset (Fin N) := Finset.univ.filter (fun x => 2 * P.bStar n < -q x)
  have hmean (ρ : Law N) (hρX : ρ.SupportedIn X) (hρW : ρ.WidthLE W) :
      |∑ x, ρ.w x * (rowDeg E G x lam - 1 / 2)| ≤ err := by
    rw [row_deviation_mean]
    have hd := hdisc ρ lam hρX hlamY hρW hlamW G
    simpa [err] using hd
  have hplus : ∑ x ∈ Splus, α.w x ≤ Real.exp (w - W) := by
    apply one_sign_mass α hαX hαW
      (fun x => rowDeg E G x lam - 1 / 2)
    · intro ρ hρX hρW
      exact hmean ρ hρX hρW
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      dsimp [q] at hx'
      have hpow : P.bStar n = err := by
        simp [Params9.bStar, err]
      rw [hpow] at hx'
      linarith
  have hminus : ∑ x ∈ Sminus, α.w x ≤ Real.exp (w - W) := by
    apply one_sign_mass α hαX hαW
      (fun x => 1 / 2 - rowDeg E G x lam)
    · intro ρ hρX hρW
      have hm := hmean ρ hρX hρW
      have hneg : (∑ x, ρ.w x * (1 / 2 - rowDeg E G x lam)) =
          -∑ x, ρ.w x * (rowDeg E G x lam - 1 / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hneg]
      simpa only [abs_neg] using hm
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have hpow : P.bStar n = err := by
        simp [Params9.bStar, err]
      rw [hpow] at hx'
      dsimp [q] at hx'
      linarith
  let Sbad := Finset.univ.filter (fun x => 2 * P.bStar n < |q x|)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    by_cases hqx : 0 ≤ q x
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simpa [abs_of_nonneg hqx] using hx'
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have habs : |q x| = -q x := abs_of_neg (lt_of_not_ge hqx)
        rw [habs] at hx'
        exact hx'
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have h₁ := (Finset.mem_filter.mp hx₁).2
    have h₂ := (Finset.mem_filter.mp hx₂).2
    linarith [hbstar_nonneg]
  calc
    (∑ x ∈ Sbad, α.w x) ≤ ∑ x ∈ Splus ∪ Sminus, α.w x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun x hx _ => α.nonneg x)
    _ = (∑ x ∈ Splus, α.w x) + ∑ x ∈ Sminus, α.w x := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (w - W) + Real.exp (w - W) := add_le_add hplus hminus
    _ = 2 * Real.exp (w - W) := by ring

/-- The transposed first-side estimate is the second-side degree test. -/
theorem reverse_bound {P : Params9} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hdeep : P.DeepAt n N E X Y) (G : Colour)
    (σ : Law N) (hσX : σ.SupportedIn X) (hσW : σ.WidthLE ((n : ℝ) ^ (P.xD : ℝ)))
    (lam : Law N) (hlamY : lam.SupportedIn Y) (s : ℝ)
    (hlamW : lam.WidthLE s) (hs : s ≤ P.Sd (n : ℝ)) :
    ∑ y ∈ Finset.univ.filter (fun y => 2 * P.bStar n < |colDeg E G σ y - 1 / 2|), lam.w y ≤
      2 * Real.exp (s - P.Sd (n : ℝ)) := by
  classical
  let err : ℝ := (n : ℝ) ^ (-(P.hMinus : ℝ))
  have hdisc : DiscOne (transposeRel E) Y X (P.Sd (n : ℝ)) ((n : ℝ) ^ (P.xD : ℝ)) err := by
    change DiscOne E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) err at hdeep
    exact (DiscOne.transpose_iff E X Y ((n : ℝ) ^ (P.xD : ℝ)) (P.Sd (n : ℝ)) err).mpr hdeep
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    positivity
  have hbstar_nonneg : 0 ≤ P.bStar n := by
    dsimp [Params9.bStar]
    positivity
  let q : Fin N → ℝ := fun y => colDeg E G σ y - 1 / 2
  let Splus : Finset (Fin N) := Finset.univ.filter (fun y => 2 * P.bStar n < q y)
  let Sminus : Finset (Fin N) := Finset.univ.filter (fun y => 2 * P.bStar n < -q y)
  have hmean (ρ : Law N) (hρY : ρ.SupportedIn Y) (hρW : ρ.WidthLE (P.Sd (n : ℝ))) :
      |∑ y, ρ.w y * (rowDeg (transposeRel E) G y σ - 1 / 2)| ≤ err := by
    rw [row_deviation_mean]
    have hd := hdisc ρ σ hρY hσX hρW hσW G
    simpa [err] using hd
  have hrowEq (y : Fin N) : rowDeg (transposeRel E) G y σ = colDeg E G σ y := by
    exact (colDeg_transpose (transposeRel E) G σ y).symm.trans (by rfl)
  have hplus : ∑ y ∈ Splus, lam.w y ≤ Real.exp (s - P.Sd (n : ℝ)) := by
    apply one_sign_mass lam hlamY hlamW
      (fun y => rowDeg (transposeRel E) G y σ - 1 / 2)
    · intro ρ hρY hρW
      exact hmean ρ hρY hρW
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [q] at hy'
      rw [← hrowEq] at hy'
      have hpow : P.bStar n = err := by simp [Params9.bStar, err]
      rw [hpow] at hy'
      linarith
  have hminus : ∑ y ∈ Sminus, lam.w y ≤ Real.exp (s - P.Sd (n : ℝ)) := by
    apply one_sign_mass lam hlamY hlamW
      (fun y => 1 / 2 - rowDeg (transposeRel E) G y σ)
    · intro ρ hρY hρW
      have hm := hmean ρ hρY hρW
      have hneg : (∑ y, ρ.w y * (1 / 2 - rowDeg (transposeRel E) G y σ)) =
          -∑ y, ρ.w y * (rowDeg (transposeRel E) G y σ - 1 / 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      rw [hneg]
      simpa only [abs_neg] using hm
    · intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp [q] at hy'
      rw [← hrowEq] at hy'
      have hpow : P.bStar n = err := by simp [Params9.bStar, err]
      rw [hpow] at hy'
      linarith
  let Sbad := Finset.univ.filter (fun y => 2 * P.bStar n < |q y|)
  have hsubset : Sbad ⊆ Splus ∪ Sminus := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    by_cases hqy : 0 ≤ q y
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · simpa [abs_of_nonneg hqy] using hy'
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · have habs : |q y| = -q y := abs_of_neg (lt_of_not_ge hqy)
        rw [habs] at hy'
        exact hy'
  have hdis : Disjoint Splus Sminus := by
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    have h₁ := (Finset.mem_filter.mp hy₁).2
    have h₂ := (Finset.mem_filter.mp hy₂).2
    linarith [hbstar_nonneg]
  calc
    (∑ y ∈ Sbad, lam.w y) ≤ ∑ y ∈ Splus ∪ Sminus, lam.w y :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun y hy _ => lam.nonneg y)
    _ = (∑ y ∈ Splus, lam.w y) + ∑ y ∈ Sminus, lam.w y := by rw [Finset.sum_union hdis]
    _ ≤ Real.exp (s - P.Sd (n : ℝ)) + Real.exp (s - P.Sd (n : ℝ)) := add_le_add hplus hminus
    _ = 2 * Real.exp (s - P.Sd (n : ℝ)) := by ring

end HypercubeRamsey.Lane_q_s09_gain1
