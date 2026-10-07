import HypercubeRamsey.S12.Defs
import HypercubeRamsey.S12.Exceptional_q_s12_exc

/-!
# Section 12 exceptional sets

These are the one-sign conditioning, weighted-test, and conditioning-width
interfaces used by the later interaction and trimming estimates.
-/

namespace HypercubeRamsey.Law

open scoped BigOperators

/-- L12.0(d): conditioning on a positive-mass set increases width by its log cost. -/
theorem cond_widthLE {N : ℕ} (τ : _root_.HypercubeRamsey.Law N)
    (S : Finset (Fin N)) (h : 0 < ∑ x ∈ S, τ.w x)
    {w : ℝ} (hw : τ.WidthLE w) :
    (τ.cond S h).WidthLE (w + Real.log (1 / ∑ x ∈ S, τ.w x)) := by
  exact HypercubeRamsey.S12.Exceptional_q_s12_exc.cond_widthLE τ S h hw

end HypercubeRamsey.Law

namespace HypercubeRamsey.S12

open HypercubeRamsey
open Classical
open HypercubeRamsey.S12.Exceptional_q_s12_exc
open scoped BigOperators

/-- L12.0(a): exceptional first-side mass under a narrow second-side law. -/
theorem exceptional_first {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (ν : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w₁)
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w) :
    ∑ x ∈ Finset.univ.filter
      (fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|), τ.w x ≤
        2 * Real.exp (w - W₂) := by
  classical
  let Splus := Finset.univ.filter (fun x => err < deg (T.S.E k) c ν.w x - 1 / 2)
  let Sminus := Finset.univ.filter (fun x => err < 1 / 2 - deg (T.S.E k) c ν.w x)
  have sign_bound (S : Finset (Fin (T.S.N k)))
      (hsign : ∀ x ∈ S, err < deg (T.S.E k) c ν.w x - 1 / 2) :
      ∑ x ∈ S, τ.w x ≤ Real.exp (w - W₂) := by
    by_contra hnot
    have hmass : Real.exp (w - W₂) < ∑ x ∈ S, τ.w x := lt_of_not_ge hnot
    have hmasspos : 0 < ∑ x ∈ S, τ.w x := lt_trans (Real.exp_pos _) hmass
    let ρ := τ.cond S hmasspos
    have hlog : w - W₂ < Real.log (∑ x ∈ S, τ.w x) := by
      have h := Real.log_lt_log (Real.exp_pos (w - W₂)) hmass
      simpa only [Real.log_exp] using h
    have hlogInv : Real.log (1 / (∑ x ∈ S, τ.w x)) =
        -Real.log (∑ x ∈ S, τ.w x) := by
      rw [one_div, Real.log_inv]
    have hbudget : w + Real.log (1 / (∑ x ∈ S, τ.w x)) ≤ W₂ := by
      rw [hlogInv]
      linarith
    have hρw : ρ.WidthLE W₂ := by
      exact width_mono (Law.cond_widthLE τ S hmasspos hτw) hbudget
    have hρS : ρ.SupportedIn S := by
      intro x hx
      simp [ρ, Law.cond, Law.restrict, hx]
    have hρX : ρ.SupportedIn (T.X k) := by
      intro x hx
      simp [ρ, Law.cond, Law.restrict, hτ x hx]
    have hbud :
        (ρ.WidthLE wL ∧ ν.WidthLE wS) ∨ (ρ.WidthLE wS ∧ ν.WidthLE wL) := by
      rcases hpair with hp | hp
      · exact Or.inl ⟨width_mono hρw hp.2, width_mono hνw hp.1⟩
      · exact Or.inr ⟨width_mono hρw hp.2, width_mono hνw hp.1⟩
    have hρsumpos : 0 < ∑ x, ρ.w x := by rw [ρ.sum_eq_one]; norm_num
    obtain ⟨x, hx, hxpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
        (by intro x hx; exact ρ.nonneg x)).mp hρsumpos
    have havg : 1 / 2 + err < ∑ x, ρ.w x * deg (T.S.E k) c ν.w x := by
      calc
        1 / 2 + err = (∑ x, ρ.w x) * (1 / 2 + err) := by
          rw [ρ.sum_eq_one]
          ring
        _ = ∑ x, ρ.w x * (1 / 2 + err) := by rw [Finset.sum_mul]
        _ < ∑ x, ρ.w x * deg (T.S.E k) c ν.w x := by
          apply Finset.sum_lt_sum
          · intro z hz
            by_cases hzs : z ∈ S
            · exact mul_le_mul_of_nonneg_left
                (le_of_lt (by have := hsign z hzs; linarith)) (ρ.nonneg z)
            · simp [hρS z hzs]
          · have hxs : x ∈ S := by
              by_contra hnotS
              have hz := hρS x hnotS
              linarith
            exact ⟨x, hx, mul_lt_mul_of_pos_left
              (by have := hsign x hxs; linarith) hxpos⟩
    rw [← dens_eq_rowDegree_sum (T.S.E k) c ρ ν] at havg
    have hdisc := hD c ρ ν hρX hν hbud
    have hupper := (abs_le.mp hdisc).2
    linarith
  have hplus : ∑ x ∈ Splus, τ.w x ≤ Real.exp (w - W₂) := by
    apply sign_bound
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hminus : ∑ x ∈ Sminus, τ.w x ≤ Real.exp (w - W₂) := by
    have hbound : ∑ x ∈ Sminus, τ.w x ≤ Real.exp (w - W₂) := by
      by_contra hnot
      have hmass : Real.exp (w - W₂) < ∑ x ∈ Sminus, τ.w x := lt_of_not_ge hnot
      have hmasspos : 0 < ∑ x ∈ Sminus, τ.w x := lt_trans (Real.exp_pos _) hmass
      let ρ := τ.cond Sminus hmasspos
      have hlog : w - W₂ < Real.log (∑ x ∈ Sminus, τ.w x) := by
        have h := Real.log_lt_log (Real.exp_pos (w - W₂)) hmass
        simpa only [Real.log_exp] using h
      have hlogInv : Real.log (1 / (∑ x ∈ Sminus, τ.w x)) =
          -Real.log (∑ x ∈ Sminus, τ.w x) := by
        rw [one_div, Real.log_inv]
      have hbudget : w + Real.log (1 / (∑ x ∈ Sminus, τ.w x)) ≤ W₂ := by
        rw [hlogInv]
        linarith
      have hρw : ρ.WidthLE W₂ := by
        exact width_mono (Law.cond_widthLE τ Sminus hmasspos hτw) hbudget
      have hρS : ρ.SupportedIn Sminus := by
        intro x hx
        simp [ρ, Law.cond, Law.restrict, hx]
      have hρX : ρ.SupportedIn (T.X k) := by
        intro x hx
        simp [ρ, Law.cond, Law.restrict, hτ x hx]
      have hbud :
          (ρ.WidthLE wL ∧ ν.WidthLE wS) ∨ (ρ.WidthLE wS ∧ ν.WidthLE wL) := by
        rcases hpair with hp | hp
        · exact Or.inl ⟨width_mono hρw hp.2, width_mono hνw hp.1⟩
        · exact Or.inr ⟨width_mono hρw hp.2, width_mono hνw hp.1⟩
      have hρsumpos : 0 < ∑ x, ρ.w x := by rw [ρ.sum_eq_one]; norm_num
      obtain ⟨x, hx, hxpos⟩ :=
        (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
          (by intro x hx; exact ρ.nonneg x)).mp hρsumpos
      have havg : 1 / 2 + err < ∑ x, ρ.w x *
          (1 - deg (T.S.E k) c ν.w x) := by
        calc
          1 / 2 + err = (∑ x, ρ.w x) * (1 / 2 + err) := by
            rw [ρ.sum_eq_one]
            ring
          _ = ∑ x, ρ.w x * (1 / 2 + err) := by rw [Finset.sum_mul]
          _ < ∑ x, ρ.w x * (1 - deg (T.S.E k) c ν.w x) := by
            apply Finset.sum_lt_sum
            · intro z hz
              by_cases hzs : z ∈ Sminus
              · exact mul_le_mul_of_nonneg_left
                  (le_of_lt (by have := (Finset.mem_filter.mp hzs).2; linarith))
                  (ρ.nonneg z)
              · simp [hρS z hzs]
            · have hxs : x ∈ Sminus := by
                by_contra hnotS
                have hz := hρS x hnotS
                linarith
              exact ⟨x, hx, mul_lt_mul_of_pos_left
                (by have := (Finset.mem_filter.mp hxs).2; linarith) hxpos⟩
      have hcomplement : ∑ x, ρ.w x * (1 - deg (T.S.E k) c ν.w x) =
          1 - dens (T.S.E k) c ρ ν := by
        calc
          ∑ x, ρ.w x * (1 - deg (T.S.E k) c ν.w x) =
              (∑ x, ρ.w x) - ∑ x, ρ.w x * deg (T.S.E k) c ν.w x := by
                calc
                  _ = ∑ x, (ρ.w x - ρ.w x * deg (T.S.E k) c ν.w x) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    ring
                  _ = _ := by
                    simpa using (Finset.sum_sub_distrib (s := Finset.univ)
                      (f := fun x => ρ.w x)
                      (g := fun x => ρ.w x * deg (T.S.E k) c ν.w x))
          _ = 1 - dens (T.S.E k) c ρ ν := by
            rw [ρ.sum_eq_one, ← dens_eq_rowDegree_sum (T.S.E k) c ρ ν]
      rw [hcomplement] at havg
      have hdisc := hD c ρ ν hρX hν hbud
      have hlower := (abs_le.mp hdisc).1
      linarith
    exact hbound
  let Sbad := Finset.univ.filter (fun x => err <
    |deg (T.S.E k) c ν.w x - 1 / 2|)
  have hsub : Sbad ⊆ Splus ∪ Sminus := by
    intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    by_cases hsign : 0 ≤ deg (T.S.E k) c ν.w x - 1 / 2
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · rw [abs_of_nonneg hsign] at hbad
        linarith
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · have hnonpos : deg (T.S.E k) c ν.w x - 1 / 2 ≤ 0 := le_of_not_ge hsign
        rw [abs_of_nonpos hnonpos] at hbad
        linarith
  calc
    ∑ x ∈ Sbad, τ.w x ≤ ∑ x ∈ Splus ∪ Sminus, τ.w x :=
      sum_subset_le Sbad (Splus ∪ Sminus) τ.w hsub (fun x hx => τ.nonneg x)
    _ ≤ (∑ x ∈ Splus, τ.w x) + ∑ x ∈ Sminus, τ.w x :=
      sum_union_le Splus Sminus τ.w (fun x => τ.nonneg x)
    _ ≤ Real.exp (w - W₂) + Real.exp (w - W₂) := add_le_add hplus hminus
    _ = 2 * Real.exp (w - W₂) := by ring

/-- L12.0(b): exceptional second-side mass under a narrow first-side law. -/
theorem exceptional_second {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w₁)
    (ν : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w) :
    ∑ y ∈ Finset.univ.filter (fun y => err <
      |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|), ν.w y ≤
        2 * Real.exp (w - W₂) := by
  classical
  let degree := fun y : Fin (T.S.N k) =>
    ∑ x, τ.w x * hit (T.S.E k) c x y
  let Splus := Finset.univ.filter (fun y => err < degree y - 1 / 2)
  let Sminus := Finset.univ.filter (fun y => err < 1 / 2 - degree y)
  have sign_bound (S : Finset (Fin (T.S.N k)))
      (hsign : ∀ y ∈ S, err < degree y - 1 / 2) :
      ∑ y ∈ S, ν.w y ≤ Real.exp (w - W₂) := by
    by_contra hnot
    have hmass : Real.exp (w - W₂) < ∑ y ∈ S, ν.w y := lt_of_not_ge hnot
    have hmasspos : 0 < ∑ y ∈ S, ν.w y := lt_trans (Real.exp_pos _) hmass
    let ρ := ν.cond S hmasspos
    have hlog : w - W₂ < Real.log (∑ y ∈ S, ν.w y) := by
      have h := Real.log_lt_log (Real.exp_pos (w - W₂)) hmass
      simpa only [Real.log_exp] using h
    have hlogInv : Real.log (1 / (∑ y ∈ S, ν.w y)) =
        -Real.log (∑ y ∈ S, ν.w y) := by
      rw [one_div, Real.log_inv]
    have hbudget : w + Real.log (1 / (∑ y ∈ S, ν.w y)) ≤ W₂ := by
      rw [hlogInv]
      linarith
    have hρw : ρ.WidthLE W₂ := by
      exact width_mono (Law.cond_widthLE ν S hmasspos hνw) hbudget
    have hρS : ρ.SupportedIn S := by
      intro y hy
      simp [ρ, Law.cond, Law.restrict, hy]
    have hρY : ρ.SupportedIn (T.Y k) := by
      intro y hy
      simp [ρ, Law.cond, Law.restrict, hν y hy]
    have hbud :
        (τ.WidthLE wL ∧ ρ.WidthLE wS) ∨ (τ.WidthLE wS ∧ ρ.WidthLE wL) := by
      rcases hpair with hp | hp
      · exact Or.inr ⟨width_mono hτw hp.1, width_mono hρw hp.2⟩
      · exact Or.inl ⟨width_mono hτw hp.1, width_mono hρw hp.2⟩
    have hρsumpos : 0 < ∑ y, ρ.w y := by rw [ρ.sum_eq_one]; norm_num
    obtain ⟨y, hy, hypos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
        (by intro y hy; exact ρ.nonneg y)).mp hρsumpos
    have havg : 1 / 2 + err < ∑ y, ρ.w y * degree y := by
      calc
        1 / 2 + err = (∑ y, ρ.w y) * (1 / 2 + err) := by
          rw [ρ.sum_eq_one]
          ring
        _ = ∑ y, ρ.w y * (1 / 2 + err) := by rw [Finset.sum_mul]
        _ < ∑ y, ρ.w y * degree y := by
          apply Finset.sum_lt_sum
          · intro z hz
            by_cases hzs : z ∈ S
            · exact mul_le_mul_of_nonneg_left
                (le_of_lt (by have := hsign z hzs; linarith)) (ρ.nonneg z)
            · simp [hρS z hzs]
          · have hys : y ∈ S := by
              by_contra hnotS
              have hz := hρS y hnotS
              linarith
            exact ⟨y, hy, mul_lt_mul_of_pos_left
              (by have := hsign y hys; linarith) hypos⟩
    rw [← dens_eq_colDegree_sum (T.S.E k) c τ ρ] at havg
    have hdisc := hD c τ ρ hτ hρY hbud
    have hupper := (abs_le.mp hdisc).2
    linarith
  have hplus : ∑ y ∈ Splus, ν.w y ≤ Real.exp (w - W₂) := by
    apply sign_bound
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  have hminus : ∑ y ∈ Sminus, ν.w y ≤ Real.exp (w - W₂) := by
    by_contra hnot
    have hmass : Real.exp (w - W₂) < ∑ y ∈ Sminus, ν.w y := lt_of_not_ge hnot
    have hmasspos : 0 < ∑ y ∈ Sminus, ν.w y := lt_trans (Real.exp_pos _) hmass
    let ρ := ν.cond Sminus hmasspos
    have hlog : w - W₂ < Real.log (∑ y ∈ Sminus, ν.w y) := by
      have h := Real.log_lt_log (Real.exp_pos (w - W₂)) hmass
      simpa only [Real.log_exp] using h
    have hlogInv : Real.log (1 / (∑ y ∈ Sminus, ν.w y)) =
        -Real.log (∑ y ∈ Sminus, ν.w y) := by
      rw [one_div, Real.log_inv]
    have hbudget : w + Real.log (1 / (∑ y ∈ Sminus, ν.w y)) ≤ W₂ := by
      rw [hlogInv]
      linarith
    have hρw : ρ.WidthLE W₂ := by
      exact width_mono (Law.cond_widthLE ν Sminus hmasspos hνw) hbudget
    have hρS : ρ.SupportedIn Sminus := by
      intro y hy
      simp [ρ, Law.cond, Law.restrict, hy]
    have hρY : ρ.SupportedIn (T.Y k) := by
      intro y hy
      simp [ρ, Law.cond, Law.restrict, hν y hy]
    have hbud :
        (τ.WidthLE wL ∧ ρ.WidthLE wS) ∨ (τ.WidthLE wS ∧ ρ.WidthLE wL) := by
      rcases hpair with hp | hp
      · exact Or.inr ⟨width_mono hτw hp.1, width_mono hρw hp.2⟩
      · exact Or.inl ⟨width_mono hτw hp.1, width_mono hρw hp.2⟩
    have hρsumpos : 0 < ∑ y, ρ.w y := by rw [ρ.sum_eq_one]; norm_num
    obtain ⟨y, hy, hypos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (s := Finset.univ) (f := ρ.w)
        (by intro y hy; exact ρ.nonneg y)).mp hρsumpos
    have havg : 1 / 2 + err < ∑ y, ρ.w y * (1 - degree y) := by
      calc
        1 / 2 + err = (∑ y, ρ.w y) * (1 / 2 + err) := by
          rw [ρ.sum_eq_one]
          ring
        _ = ∑ y, ρ.w y * (1 / 2 + err) := by rw [Finset.sum_mul]
        _ < ∑ y, ρ.w y * (1 - degree y) := by
          apply Finset.sum_lt_sum
          · intro z hz
            by_cases hzs : z ∈ Sminus
            · exact mul_le_mul_of_nonneg_left
                (le_of_lt (by have := (Finset.mem_filter.mp hzs).2; linarith))
                (ρ.nonneg z)
            · simp [hρS z hzs]
          · have hys : y ∈ Sminus := by
              by_contra hnotS
              have hz := hρS y hnotS
              linarith
            exact ⟨y, hy, mul_lt_mul_of_pos_left
              (by have := (Finset.mem_filter.mp hys).2; linarith) hypos⟩
    have hcomplement : ∑ y, ρ.w y * (1 - degree y) =
        1 - dens (T.S.E k) c τ ρ := by
      calc
        ∑ y, ρ.w y * (1 - degree y) =
            (∑ y, ρ.w y) - ∑ y, ρ.w y * degree y := by
              calc
                _ = ∑ y, (ρ.w y - ρ.w y * degree y) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  ring
                _ = _ := by
                  simpa using (Finset.sum_sub_distrib (s := Finset.univ)
                    (f := fun y => ρ.w y)
                    (g := fun y => ρ.w y * degree y))
        _ = 1 - dens (T.S.E k) c τ ρ := by
          simp only [degree]
          rw [ρ.sum_eq_one, ← dens_eq_colDegree_sum (T.S.E k) c τ ρ]
    rw [hcomplement] at havg
    have hdisc := hD c τ ρ hτ hρY hbud
    have hlower := (abs_le.mp hdisc).1
    linarith
  let Sbad := Finset.univ.filter (fun y => err < |degree y - 1 / 2|)
  have hsub : Sbad ⊆ Splus ∪ Sminus := by
    intro y hy
    have hbad := (Finset.mem_filter.mp hy).2
    by_cases hsign : 0 ≤ degree y - 1 / 2
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · rw [abs_of_nonneg hsign] at hbad
        linarith
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · have hnonpos : degree y - 1 / 2 ≤ 0 := le_of_not_ge hsign
        rw [abs_of_nonpos hnonpos] at hbad
        linarith
  calc
    ∑ y ∈ Sbad, ν.w y ≤ ∑ y ∈ Splus ∪ Sminus, ν.w y :=
      sum_subset_le Sbad (Splus ∪ Sminus) ν.w hsub (fun y hy => ν.nonneg y)
    _ ≤ (∑ y ∈ Splus, ν.w y) + ∑ y ∈ Sminus, ν.w y :=
      sum_union_le Splus Sminus ν.w (fun y => ν.nonneg y)
    _ ≤ Real.exp (w - W₂) + Real.exp (w - W₂) := add_le_add hplus hminus
    _ = 2 * Real.exp (w - W₂) := by ring

/-- L12.0(c), first orientation: a bounded signed test on the second side. -/
theorem exceptional_signed {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (π : Law (T.S.N k)) (hπ : π.SupportedIn (T.Y k))
    (hπw : π.WidthLE (w₁ - Real.log 3))
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w)
    (f : Fin (T.S.N k) → ℝ) (hf : ∀ y, |f y| ≤ 1) :
    ∑ x ∈ Finset.univ.filter (fun x => 6 * err <
      |∑ y, π.w y * f y * (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|),
      τ.w x ≤ 4 * Real.exp (w - W₂) := by
  classical
  let πf := tiltLaw π f hf
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hπw' : π.WidthLE w₁ :=
    width_mono hπw (by linarith)
  have hπfw : πf.WidthLE w₁ := tiltLaw_width π f hf hπw
  have hπfS : πf.SupportedIn (T.Y k) := tiltLaw_supported π f hf _ hπ
  let Sbase := Finset.univ.filter (fun x => err <
    |deg (T.S.E k) c π.w x - 1 / 2|)
  let Stilt := Finset.univ.filter (fun x => err <
    |deg (T.S.E k) c πf.w x - 1 / 2|)
  let Sbad := Finset.univ.filter (fun x => 6 * err <
    |∑ y, π.w y * f y *
      (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|)
  have hbase : ∑ x ∈ Sbase, τ.w x ≤ 2 * Real.exp (w - W₂) := by
    exact exceptional_first hD c hpair π hπ hπw' τ hτ hτw
  have htilt : ∑ x ∈ Stilt, τ.w x ≤ 2 * Real.exp (w - W₂) := by
    exact exceptional_first hD c hpair πf hπfS hπfw τ hτ hτw
  have hsub : Sbad ⊆ Stilt ∪ Sbase := by
    intro x hx
    have hevent := (Finset.mem_filter.mp hx).2
    by_contra hnot
    have hbaseAbs : |deg (T.S.E k) c π.w x - 1 / 2| ≤ err := by
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have htiltAbs : |deg (T.S.E k) c πf.w x - 1 / 2| ≤ err := by
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have herr : 0 ≤ err := le_trans (abs_nonneg _) hbaseAbs
    have hdiff :
        |deg (T.S.E k) c πf.w x - deg (T.S.E k) c π.w x| ≤ 2 * err := by
      apply abs_le.mpr
      constructor
      · have h₁ := (abs_le.mp htiltAbs).1
        have h₂ := (abs_le.mp hbaseAbs).2
        linarith
      · have h₁ := (abs_le.mp htiltAbs).2
        have h₂ := (abs_le.mp hbaseAbs).1
        linarith
    have hZ := tiltMass_bounds π f hf
    have hZpos : 0 < tiltMass π f := lt_of_lt_of_le zero_lt_one hZ.1
    have hbound :
        |∑ y, π.w y * f y *
          (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)| ≤ 6 * err := by
      rw [← tilt_degree_identity π f hf (T.S.E k) c x]
      rw [abs_mul, abs_of_nonneg hZpos.le]
      calc
        tiltMass π f *
            |deg (T.S.E k) c πf.w x - deg (T.S.E k) c π.w x| ≤
          tiltMass π f * (2 * err) :=
            mul_le_mul_of_nonneg_left hdiff hZpos.le
        _ ≤ 3 * (2 * err) := mul_le_mul_of_nonneg_right hZ.2 (by positivity)
        _ = 6 * err := by ring
    linarith
  calc
    ∑ x ∈ Sbad, τ.w x ≤ ∑ x ∈ Stilt ∪ Sbase, τ.w x :=
      sum_subset_le Sbad (Stilt ∪ Sbase) τ.w hsub (fun x hx => τ.nonneg x)
    _ ≤ (∑ x ∈ Stilt, τ.w x) + ∑ x ∈ Sbase, τ.w x :=
      sum_union_le Stilt Sbase τ.w (fun x => τ.nonneg x)
    _ ≤ 2 * Real.exp (w - W₂) + 2 * Real.exp (w - W₂) := add_le_add htilt hbase
    _ = 4 * Real.exp (w - W₂) := by ring

/-- L12.0(c), transposed orientation: a bounded signed test on the first side. -/
theorem exceptional_signed_second {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w₁ W₂ w : ℝ}
    (hpair : (w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS))
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k))
    (hτw : τ.WidthLE (w₁ - Real.log 3))
    (ν : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w)
    (f : Fin (T.S.N k) → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    ∑ y ∈ Finset.univ.filter (fun y => 6 * err <
      |∑ x, τ.w x * f x * (hit (T.S.E k) c x y -
        ∑ z, τ.w z * hit (T.S.E k) c z y)|),
      ν.w y ≤ 4 * Real.exp (w - W₂) := by
  classical
  let τf := tiltLaw τ f hf
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hτw' : τ.WidthLE w₁ :=
    width_mono hτw (by linarith)
  have hτfw : τf.WidthLE w₁ := tiltLaw_width τ f hf hτw
  have hτfS : τf.SupportedIn (T.X k) := tiltLaw_supported τ f hf _ hτ
  let coldeg := fun y : Fin (T.S.N k) =>
    ∑ x, τ.w x * hit (T.S.E k) c x y
  let coldegF := fun y : Fin (T.S.N k) =>
    ∑ x, τf.w x * hit (T.S.E k) c x y
  let Sbase := Finset.univ.filter (fun y => err < |coldeg y - 1 / 2|)
  let Stilt := Finset.univ.filter (fun y => err < |coldegF y - 1 / 2|)
  let Sbad := Finset.univ.filter (fun y => 6 * err <
    |∑ x, τ.w x * f x * (hit (T.S.E k) c x y - coldeg y)|)
  have hbase : ∑ y ∈ Sbase, ν.w y ≤ 2 * Real.exp (w - W₂) := by
    simpa [Sbase, coldeg] using exceptional_second hD c hpair τ hτ hτw' ν hν hνw
  have htilt : ∑ y ∈ Stilt, ν.w y ≤ 2 * Real.exp (w - W₂) := by
    simpa [Stilt, coldegF] using exceptional_second hD c hpair τf hτfS hτfw ν hν hνw
  have hsub : Sbad ⊆ Stilt ∪ Sbase := by
    intro y hy
    have hevent := (Finset.mem_filter.mp hy).2
    by_contra hnot
    have hbaseAbs : |coldeg y - 1 / 2| ≤ err := by
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have htiltAbs : |coldegF y - 1 / 2| ≤ err := by
      apply le_of_not_gt
      intro hlt
      apply hnot
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have herr : 0 ≤ err := le_trans (abs_nonneg _) hbaseAbs
    have hdiff : |coldegF y - coldeg y| ≤ 2 * err := by
      apply abs_le.mpr
      constructor
      · have h₁ := (abs_le.mp htiltAbs).1
        have h₂ := (abs_le.mp hbaseAbs).2
        linarith
      · have h₁ := (abs_le.mp htiltAbs).2
        have h₂ := (abs_le.mp hbaseAbs).1
        linarith
    have hZ := tiltMass_bounds τ f hf
    have hZpos : 0 < tiltMass τ f := lt_of_lt_of_le zero_lt_one hZ.1
    have hbound :
        |∑ x, τ.w x * f x * (hit (T.S.E k) c x y - coldeg y)| ≤ 6 * err := by
      rw [← tilt_colDegree_identity τ f hf (T.S.E k) c y]
      rw [abs_mul, abs_of_nonneg hZpos.le]
      calc
        tiltMass τ f * |coldegF y - coldeg y| ≤ tiltMass τ f * (2 * err) :=
          mul_le_mul_of_nonneg_left hdiff hZpos.le
        _ ≤ 3 * (2 * err) := mul_le_mul_of_nonneg_right hZ.2 (by positivity)
        _ = 6 * err := by ring
    linarith
  calc
    ∑ y ∈ Sbad, ν.w y ≤ ∑ y ∈ Stilt ∪ Sbase, ν.w y :=
      sum_subset_le Sbad (Stilt ∪ Sbase) ν.w hsub (fun y hy => ν.nonneg y)
    _ ≤ (∑ y ∈ Stilt, ν.w y) + ∑ y ∈ Sbase, ν.w y :=
      sum_union_le Stilt Sbase ν.w (fun y => ν.nonneg y)
    _ ≤ 2 * Real.exp (w - W₂) + 2 * Real.exp (w - W₂) := add_le_add htilt hbase
    _ = 4 * Real.exp (w - W₂) := by ring

/-- L12.0: the four exceptional-set conclusions at a fixed two-budget discrepancy input. -/
def ExceptionalSetClaims {T : Stage} {k : ℕ} {wS wL err : ℝ} (c : Colour) : Prop :=
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (ν : Law (T.S.N k)), ν.SupportedIn (T.Y k) → ν.WidthLE w₁ →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) → τ.WidthLE w →
      ∑ x ∈ Finset.univ.filter
        (fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|), τ.w x ≤
          2 * Real.exp (w - W₂)) ∧
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) → τ.WidthLE w₁ →
      ∀ (ν : Law (T.S.N k)), ν.SupportedIn (T.Y k) → ν.WidthLE w →
      ∑ y ∈ Finset.univ.filter (fun y => err <
        |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|), ν.w y ≤
          2 * Real.exp (w - W₂)) ∧
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (π : Law (T.S.N k)), π.SupportedIn (T.Y k) →
        π.WidthLE (w₁ - Real.log 3) →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) → τ.WidthLE w →
      ∀ (f : Fin (T.S.N k) → ℝ), (∀ y, |f y| ≤ 1) →
      ∑ x ∈ Finset.univ.filter (fun x => 6 * err <
        |∑ y, π.w y * f y *
          (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|),
        τ.w x ≤ 4 * Real.exp (w - W₂)) ∧
    (∀ {w₁ W₂ w : ℝ},
      ((w₁ ≤ wS ∧ W₂ ≤ wL) ∨ (w₁ ≤ wL ∧ W₂ ≤ wS)) →
      ∀ (τ : Law (T.S.N k)), τ.SupportedIn (T.X k) →
        τ.WidthLE (w₁ - Real.log 3) →
      ∀ (ν : Law (T.S.N k)), ν.SupportedIn (T.Y k) → ν.WidthLE w →
      ∀ (f : Fin (T.S.N k) → ℝ), (∀ x, |f x| ≤ 1) →
      ∑ y ∈ Finset.univ.filter (fun y => 6 * err <
        |∑ x, τ.w x * f x *
          (hit (T.S.E k) c x y - ∑ z, τ.w z * hit (T.S.E k) c z y)|),
        ν.w y ≤ 4 * Real.exp (w - W₂))

/-- L12.0: assembled exceptional-set tools for both sides and both signed-test orientations. -/
theorem exceptional_set_lemma {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour) :
    ExceptionalSetClaims (T := T) (k := k) (wS := wS) (wL := wL) (err := err) c := by
  exact ⟨fun hpair => exceptional_first hD c hpair,
    fun hpair => exceptional_second hD c hpair,
    fun hpair => exceptional_signed hD c hpair,
    fun hpair => exceptional_signed_second hD c hpair⟩

/-- L12.0: package the conditioning-width estimate alongside the four exception bounds. -/
theorem exceptional_export {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour) :
    ExceptionalSetClaims (T := T) (k := k) (wS := wS) (wL := wL) (err := err) c ∧
    (∀ {N : ℕ} (τ : Law N) (S : Finset (Fin N))
      (h : 0 < ∑ x ∈ S, τ.w x) {w : ℝ} (hw : τ.WidthLE w),
      (τ.cond S h).WidthLE (w + Real.log (1 / ∑ x ∈ S, τ.w x))) := by
  exact ⟨exceptional_set_lemma hD c,
    fun {N} τ S h {w} hw => _root_.HypercubeRamsey.Law.cond_widthLE (w := w) τ S h hw⟩

end HypercubeRamsey.S12
