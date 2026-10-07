import HypercubeRamsey.S12.ModerateMoment_q_s12_mom

/-!
# Section 12 moderate interactions
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.4a: on a moderate tuple from the support, a positive product term has an exponential bound. -/
theorem moderate_posTerm_pointwise (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (t : ℝ)
        (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)),
        (∀ i, 0 < S.τ.w (xs i)) →
        Moderate (T.S.E k) c (fun l => (S.π l).w) t xs →
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (((2 : ℝ) ^ κ.u) * S.d * t) := by
  exact moderate_posTerm_pointwise_helper κ hκ T hDeep c C0 hC0

/-- L12.4b: the two large-interaction ranges have exponentially small product-law mass. -/
theorem moderate_tail_ranges (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) ∧
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-(κ.α * T.S.n k / 3)) := by
  classical
  obtain ⟨hInterOne, _, hTwo, _, _⟩ := interaction_tails κ hκ T hDeep c κ.u C0 hC0
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have hn2 : ∀ᶠ k in atTop, 2 ≤ (T.S.n k : ℝ) :=
    hn.eventually_ge_atTop 2
  have hcut : ∀ᶠ k in atTop,
      100 * 3 ^ κ.u * C0 * bstar T k < (T.S.n k : ℝ) ^ (-(0.94 : ℝ)) := by
    have hnpos : ∀ᶠ k in atTop, 0 < (T.S.n k : ℝ) := hn.eventually_gt_atTop 0
    have hpw : Tendsto (fun k => (T.S.n k : ℝ) ^ (0.02 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp hn
    have hbig := hpw.eventually_gt_atTop (100 * 3 ^ κ.u * C0)
    filter_upwards [hnpos, hbig] with k hnk hbigk
    have hpow : (T.S.n k : ℝ) ^ (-(0.94 : ℝ)) =
        (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) *
          (T.S.n k : ℝ) ^ (0.02 : ℝ) := by
      rw [← Real.rpow_add hnk]
      congr 1 <;> norm_num
    have hbstar : bstar T k = (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := by
      simp [bstar]
      congr 1 <;> norm_num
    rw [hpow, hbstar]
    have hpos : 0 < (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) := Real.rpow_pos_of_pos hnk _
    calc
      100 * 3 ^ κ.u * C0 * (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) =
          (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) * (100 * 3 ^ κ.u * C0) := by ring
      _ < (T.S.n k : ℝ) ^ (-(0.96 : ℝ)) * (T.S.n k : ℝ) ^ (0.02 : ℝ) :=
        mul_lt_mul_of_pos_left hbigk hpos
  filter_upwards [hTwo, hInterOne, hn2, hcut] with k hkTwo hkOne hnk hcutk
  intro S hDeg
  have hweight_nonneg (xs : Fin κ.u → Fin (T.S.N k)) : 0 ≤ prodW S.τ.w xs := by
    unfold prodW
    exact Finset.prod_nonneg fun i hi => S.τ.nonneg (xs i)
  let p₁ : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
      ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
  let q₁ : (Fin S.d × Finset (Fin κ.u)) →
      (Fin κ.u → Fin (T.S.N k)) → Prop := fun a xs =>
    2 ≤ a.2.card ∧
      (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) <
        |inter (T.S.E k) c (S.π a.1).w a.2 xs|
  have hcover₁ : ∀ xs, p₁ xs → ∃ a, q₁ a xs := by
    intro xs hp
    change ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
      ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs at hp
    simp only [Moderate] at hp
    push_neg at hp
    rcases hp with ⟨l, J, hJ, hbad⟩
    exact ⟨(l, J), hJ, hbad⟩
  have hmass₁ (a : Fin S.d × Finset (Fin κ.u)) :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if q₁ a xs then prodW S.τ.w xs else 0) ≤
        Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
    rcases a with ⟨l, J⟩
    by_cases hJ : 2 ≤ J.card
    · obtain ⟨i₀, i₁, hi₀, hi₁, hne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < J.card)
      let gate : Fin (T.S.N k) → Prop := fun x =>
        DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) x
      have hpoint := hkTwo S l J i₀ i₁ hi₀ hi₁ hne hJ
      have hgate : ∀ x, 0 < S.τ.w x → gate x := hDeg l
      have hmass := interaction_event_mass_two_le S.τ (T.S.E k) c (S.π l).w
        J i₀ i₁ hi₀ hi₁ hne ((T.S.n k : ℝ) ^ (-(1.03 : ℝ)))
        (Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ)))) (Real.exp_nonneg _) gate hgate
        (fun xs hother => hpoint xs hother)
      simpa [q₁, hJ] using hmass
    ·
      simp [q₁, hJ]
      positivity
  have hcount₁ : Fintype.card (Fin S.d × Finset (Fin κ.u)) ≤
      T.S.n k * 4 ^ κ.u := by
    have hpows : 2 ^ κ.u ≤ 4 ^ κ.u := Nat.pow_le_pow_left (by decide : 2 ≤ 4) κ.u
    calc
      Fintype.card (Fin S.d × Finset (Fin κ.u)) = S.d * 2 ^ κ.u := by simp
      _ ≤ T.S.n k * 4 ^ κ.u := Nat.mul_le_mul S.d_le hpows
  have hcount₁R : (Fintype.card (Fin S.d × Finset (Fin κ.u)) : ℝ) ≤
      (T.S.n k : ℝ) * 4 ^ κ.u := by exact_mod_cast hcount₁
  have hsum₁ :
      (∑ a : Fin S.d × Finset (Fin κ.u),
        ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if q₁ a xs then prodW S.τ.w xs else 0)) ≤
      (T.S.n k : ℝ) * 4 ^ κ.u *
        Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by
    calc
      _ ≤ ∑ a : Fin S.d × Finset (Fin κ.u),
          Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) :=
        Finset.sum_le_sum fun a ha => hmass₁ a
      _ = (Fintype.card (Fin S.d × Finset (Fin κ.u)) : ℝ) *
          Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) := by simp
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right hcount₁R
          (Real.exp_nonneg _)
  have hfirst :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if p₁ xs then prodW S.τ.w xs else 0) ≤
        (T.S.n k : ℝ) * 4 ^ κ.u *
          Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) :=
    (weighted_event_exists_le_sum (fun xs : Fin κ.u → Fin (T.S.N k) =>
      prodW S.τ.w xs) hweight_nonneg p₁ q₁ hcover₁).trans hsum₁
  constructor
  · have hsumEq :
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs else 0) =
        ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if p₁ xs then prodW S.τ.w xs else 0) := by
      apply Finset.sum_congr rfl
      intro xs hxs
      by_cases hmod : Moderate (T.S.E k) c (fun l => (S.π l).w)
          ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs <;> simp [p₁, hmod]
    calc
      _ = ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if p₁ xs then prodW S.τ.w xs else 0) := hsumEq
      _ ≤ _ := hfirst
  · let p₂ : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
      ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
        ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs
    let q₂ : (Fin S.d × Finset (Fin κ.u)) →
        (Fin κ.u → Fin (T.S.N k)) → Prop := fun a xs =>
      2 ≤ a.2.card ∧
        (T.S.n k : ℝ) ^ (-(0.94 : ℝ)) <
          |inter (T.S.E k) c (S.π a.1).w a.2 xs|
    have hcover₂ : ∀ xs, p₂ xs → ∃ a, q₂ a xs := by
      intro xs hp
      change ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
        ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs at hp
      simp only [Moderate] at hp
      push_neg at hp
      rcases hp with ⟨l, J, hJ, hbad⟩
      exact ⟨(l, J), hJ, hbad⟩
    have hmass₂ (a : Fin S.d × Finset (Fin κ.u)) :
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if q₂ a xs then prodW S.τ.w xs else 0) ≤
          Real.exp (-(κ.α * T.S.n k / 3)) := by
      rcases a with ⟨l, J⟩
      by_cases hJ : 2 ≤ J.card
      · obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
        let gate : Fin (T.S.N k) → Prop := fun x =>
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) x
        have hpoint := hkOne S l J i₀ hi₀ hJ
        have hgate : ∀ x, 0 < S.τ.w x → gate x := hDeg l
        have hTail (xs : Fin κ.u → Fin (T.S.N k))
            (hother : ∀ i ∈ J, i ≠ i₀ → gate (xs i)) :
            ∑ z ∈ Finset.univ.filter (fun z =>
              gate z ∧ (T.S.n k : ℝ) ^ (-(0.94 : ℝ)) <
                |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|),
              S.τ.w z ≤ Real.exp (-(κ.α * T.S.n k / 3)) := by
          calc
            _ ≤ ∑ z ∈ Finset.univ.filter (fun z =>
                gate z ∧ 100 * 3 ^ κ.u * C0 * bstar T k <
                  |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|),
                S.τ.w z := by
                  have hsub :
                      Finset.univ.filter (fun z => gate z ∧
                        (T.S.n k : ℝ) ^ (-(0.94 : ℝ)) <
                          |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|) ⊆
                      Finset.univ.filter (fun z => gate z ∧
                        100 * 3 ^ κ.u * C0 * bstar T k <
                          |inter (T.S.E k) c (S.π l).w J (Function.update xs i₀ z)|) := by
                    intro z hz
                    rcases Finset.mem_filter.mp hz with ⟨hzU, hgz⟩
                    exact Finset.mem_filter.mpr
                      ⟨Finset.mem_univ z, hgz.1, lt_trans hcutk hgz.2⟩
                  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
                    (fun z hz hnz => S.τ.nonneg z)
            _ ≤ Real.exp (-(κ.α * T.S.n k / 3)) := hpoint xs hother
        have hmass := interaction_event_mass_one_le S.τ (T.S.E k) c (S.π l).w
          J i₀ hi₀ ((T.S.n k : ℝ) ^ (-(0.94 : ℝ)))
          (Real.exp (-(κ.α * T.S.n k / 3))) gate hgate hTail
        simpa [q₂, hJ] using hmass
      ·
        simp [q₂, hJ]
        positivity
    have hsum₂ :
        (∑ a : Fin S.d × Finset (Fin κ.u),
          ∑ xs : Fin κ.u → Fin (T.S.N k),
            (if q₂ a xs then prodW S.τ.w xs else 0)) ≤
        (T.S.n k : ℝ) * 4 ^ κ.u *
          Real.exp (-(κ.α * T.S.n k / 3)) := by
      calc
        _ ≤ ∑ a : Fin S.d × Finset (Fin κ.u),
            Real.exp (-(κ.α * T.S.n k / 3)) :=
          Finset.sum_le_sum fun a ha => hmass₂ a
        _ = (Fintype.card (Fin S.d × Finset (Fin κ.u)) : ℝ) *
            Real.exp (-(κ.α * T.S.n k / 3)) := by simp
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right hcount₁R
            (Real.exp_nonneg _)
    have hsecond :
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if p₂ xs then prodW S.τ.w xs else 0) ≤
        (T.S.n k : ℝ) * 4 ^ κ.u *
          Real.exp (-(κ.α * T.S.n k / 3)) :=
      (weighted_event_exists_le_sum (fun xs : Fin κ.u → Fin (T.S.N k) =>
        prodW S.τ.w xs) hweight_nonneg p₂ q₂ hcover₂).trans hsum₂
    have hsumEq :
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs
          then prodW S.τ.w xs else 0) =
        ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if p₂ xs then prodW S.τ.w xs else 0) := by
      apply Finset.sum_congr rfl
      intro xs hxs
      by_cases hmod : Moderate (T.S.E k) c (fun l => (S.π l).w)
          ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs <;> simp [p₂, hmod]
    calc
      _ = ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if p₂ xs then prodW S.τ.w xs else 0) := hsumEq
      _ ≤ _ := hsecond

/-- L12.4c: inclusion-exclusion cancellation on the very small-interaction range. -/
theorem moderate_cancellation (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
            (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) / 3 := by
  sorry

/-- L12.4: combine the pointwise, tail-range, and cancellation subnodes. -/
theorem moderate_moment_core (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hPointwise : ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (t : ℝ)
        (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)),
        (∀ i, 0 < S.τ.w (xs i)) →
        Moderate (T.S.E k) c (fun l => (S.π l).w) t xs →
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (((2 : ℝ) ^ κ.u) * S.d * t))
    (hTails : ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-((T.S.n k : ℝ) ^ (0.4 : ℝ))) ∧
        (∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(0.94 : ℝ))) xs
          then prodW S.τ.w xs else 0) ≤
            (T.S.n k : ℝ) * 4 ^ κ.u *
              Real.exp (-(κ.α * T.S.n k / 3)))
    (hCancel : ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
        |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w)
            ((T.S.n k : ℝ) ^ (-(1.03 : ℝ))) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
            (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) / 3) :
    ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
      |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0|
        ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) ∧
      ∀ u' ≤ κ.u, ∀ I : Finset (Fin u'),
        ∑ xs : Fin u' → Fin (T.S.N k),
          (if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
           then prodW S.τ.w xs *
             posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 2 := by
  sorry

/-- L12.4: the conjunction of the moderate signed-moment and positive-term estimates. -/
def ModerateMomentClaim (κ : CConsts) (T : Stage) (c : Colour) (C0 : ℝ) : Prop :=
  ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
    |∑ xs : Fin κ.u → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
        then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0|
      ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) ∧
    ∀ u' ≤ κ.u, ∀ I : Finset (Fin u'),
      ∑ xs : Fin u' → Fin (T.S.N k),
        (if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
         then prodW S.τ.w xs *
           posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 2

/-- L12.4: the exported moderate-interaction moment estimate. -/
theorem moderate_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ModerateMomentClaim κ T c C0 := by
  exact moderate_moment_core κ hκ T hDeep c C0 hC0
    (moderate_posTerm_pointwise κ hκ T hDeep c C0 hC0)
    (moderate_tail_ranges κ hκ T hDeep c C0 hC0)
    (moderate_cancellation κ hκ T hDeep c C0 hC0)

end HypercubeRamsey.S12
