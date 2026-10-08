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

set_option maxHeartbeats 1000000 in
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
  classical
  obtain ⟨_, _, _, _, hMean⟩ := interaction_tails κ hκ T hDeep c κ.u C0 hC0
  have hnNat : Tendsto T.S.n atTop atTop := T.S.n_tendsto
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp hnNat
  have hPpos : 0 < κ.P := by
    have hp := hκ.P_big.2
    rw [hκ.Ac_eq] at hp
    omega
  have hRpos : 0 < κ.R := by
    rw [hκ.R_eq]
    positivity
  have hRone : 1 ≤ κ.R := by omega
  have hLpos : 0 < κ.L := by
    rw [hκ.L_eq]
    omega
  have hLreal : (κ.L : ℝ) = 500 * (κ.R : ℝ) := by
    exact_mod_cast hκ.L_eq
  have hRreal : (1 : ℝ) ≤ (κ.R : ℝ) := by exact_mod_cast hRone
  have hstarPow :
      Tendsto (fun k => (T.S.n k : ℝ) ^ (-(0.96 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp hn
  have hbstar : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
    refine Tendsto.congr' ?_ hstarPow
    filter_upwards with k
    simp [bstar]
    congr 1
    norm_num
  have hstar : Tendsto (fun k => C0 * bstar T k) atTop (nhds 0) := by
    simpa [mul_comm] using (tendsto_const_nhds (x := C0)).mul hbstar
  have hstarSmall : ∀ᶠ k in atTop, C0 * bstar T k < 1 / 2 :=
    hstar.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have htPow :
      Tendsto (fun k => (T.S.n k : ℝ) ^ (-(1.03 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp hn
  have htSmall : ∀ᶠ k in atTop, (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) ≤ 1 := by
    have htSmall' := htPow.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [htSmall'] with k hk
    exact le_of_lt hk
  have hnOne : ∀ᶠ k in atTop, 1 ≤ T.S.n k := hnNat.eventually_ge_atTop 1
  let A : ℝ := ((κ.L + 1 : ℕ) : ℝ) * ((2 ^ κ.u : ℕ) : ℝ) ^ κ.L
  let δL : ℝ := (1 / 2 : ℝ) * (κ.L : ℝ) - 3 * (κ.R : ℝ)
  let δH : ℝ := (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ) - 1 - 3 * (κ.R : ℝ)
  have hδL : 0 < δL := by
    rw [show δL = (1 / 2 : ℝ) * (κ.L : ℝ) - 3 * (κ.R : ℝ) by rfl,
      hLreal]
    nlinarith [hRreal]
  have hδH : 0 < δH := by
    rw [show δH = (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ) - 1 -
      3 * (κ.R : ℝ) by rfl, hκ.L_eq]
    norm_num
    nlinarith [hRone]
  have hLowRatio :
      Tendsto (fun k => 6 * A * (T.S.n k : ℝ) ^ (-δL)) atTop (nhds 0) := by
    have hp := (tendsto_rpow_neg_atTop hδL).comp hn
    simpa [mul_assoc] using hp.const_mul (6 * A)
  have hLowSmall : ∀ᶠ k in atTop,
      6 * A * (T.S.n k : ℝ) ^ (-δL) < 1 :=
    hLowRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hHighRatio :
      Tendsto (fun k => 12 * (T.S.n k : ℝ) ^ (-δH)) atTop (nhds 0) := by
    have hp := (tendsto_rpow_neg_atTop hδH).comp hn
    simpa [mul_assoc] using hp.const_mul 12
  have hHighSmall : ∀ᶠ k in atTop,
      12 * (T.S.n k : ℝ) ^ (-δH) < 1 :=
    hHighRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hnSmallPow : Tendsto (fun k => (T.S.n k : ℝ) ^ (0.01 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hn
  have h2powSmall : ∀ᶠ k in atTop,
      (2 : ℝ) ^ (κ.u : ℝ) < (T.S.n k : ℝ) ^ (0.01 : ℝ) :=
    hnSmallPow.eventually_gt_atTop ((2 : ℝ) ^ (κ.u : ℝ))
  filter_upwards [hMean, hstarSmall, htSmall, hnOne,
    hLowSmall, hHighSmall, h2powSmall] with k hMeanK hstarK htK hnNatK hLowK hHighK h2powK
  intro S hDeg
  let n : ℝ := (T.S.n k : ℝ)
  let t : ℝ := n ^ (-(1.03 : ℝ))
  let a : ℝ := ((2 ^ κ.u : ℕ) : ℝ)
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast hnNatK
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
  have htle : t ≤ 1 := by simpa [n, t] using htK
  have hWnonneg (xs : Fin κ.u → Fin (T.S.N k)) :
      0 ≤ prodW S.τ.w xs := by
    unfold prodW
    exact Finset.prod_nonneg fun i hi => S.τ.nonneg (xs i)
  have hcoords (xs : Fin κ.u → Fin (T.S.N k)) (hW : 0 < prodW S.τ.w xs) :
      ∀ i, 0 < S.τ.w (xs i) := by
    intro i
    by_contra hi
    have hzero : S.τ.w (xs i) = 0 :=
      le_antisymm (le_of_not_gt hi) (S.τ.nonneg _)
    have hprod : prodW S.τ.w xs = 0 := by
      unfold prodW
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
    exact (ne_of_gt hW) hprod
  have hdegPos (xs : Fin κ.u → Fin (T.S.N k)) (hW : 0 < prodW S.τ.w xs)
      (l : Fin S.d) (i : Fin κ.u) :
      0 < deg (T.S.E k) c (S.π l).w (xs i) := by
    have hgate := hDeg l (xs i) (hcoords xs hW i)
    have hlow : 1 / 2 - C0 * bstar T k ≤
        deg (T.S.E k) c (S.π l).w (xs i) := by
      have h := abs_le.mp hgate
      linarith
    linarith [hstarK]
  let P : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    Moderate (T.S.E k) c (fun l => (S.π l).w) t xs
  let W : (Fin κ.u → Fin (T.S.N k)) → ℝ := fun xs => prodW S.τ.w xs
  let good : ∀ K : Finset (Fin S.d),
      (∀ l : {l // l ∈ K}, Finset (Fin κ.u)) → Prop := fun K f =>
    (∀ l, 2 ≤ (f l).card) ∧
      Lane_q_s12_mom.selected_interaction_union K f = Finset.univ
  let selectorAbs (K : Finset (Fin S.d))
      (f : ∀ l : {l // l ∈ K}, Finset (Fin κ.u))
      (xs : Fin κ.u → Fin (T.S.N k)) : ℝ :=
    if good K f then
      |∏ l : {l // l ∈ K}, inter (T.S.E k) c (S.π l.1).w (f l) xs|
    else 0
  let H (K : Finset (Fin S.d))
      (f : ∀ l : {l // l ∈ K}, Finset (Fin κ.u)) : ℝ :=
    ∑ xs : Fin κ.u → Fin (T.S.N k),
      if P xs then W xs * selectorAbs K f xs else 0
  have hPhiPoint (xs : Fin κ.u → Fin (T.S.N k)) (hW : 0 < W xs) :
      |Phi (T.S.E k) c (fun l => (S.π l).w) xs| ≤
        ∑ K : Finset (Fin S.d),
          ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)),
            selectorAbs K f xs := by
    have h := Lane_q_s12_mom.Phi_cover_abs_bound
      (T.S.E k) c (fun l => (S.π l).w) xs
      (fun l => (S.π l).sum_eq_one) (hdegPos xs hW)
    simpa [selectorAbs, good] using h
  have hpoint (xs : Fin κ.u → Fin (T.S.N k)) :
      (if P xs then W xs * |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0) ≤
        (if P xs then W xs *
          (∑ K : Finset (Fin S.d),
            ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), selectorAbs K f xs)
         else 0) := by
    by_cases hmod : P xs
    · simp only [if_pos hmod]
      have hWn := hWnonneg xs
      by_cases hzero : W xs = 0
      · simp [hzero]
      · have hW : 0 < W xs := lt_of_le_of_ne hWn (Ne.symm hzero)
        exact mul_le_mul_of_nonneg_left (hPhiPoint xs hW) hWn
    · simp [hmod]
  have hmove :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if P xs then W xs *
          (∑ K : Finset (Fin S.d),
            ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), selectorAbs K f xs)
        else 0) =
      ∑ K : Finset (Fin S.d),
        ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), H K f := by
    dsimp [H]
    calc
      _ = ∑ xs : Fin κ.u → Fin (T.S.N k),
            ∑ K : Finset (Fin S.d),
              ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)),
                (if P xs then W xs * selectorAbs K f xs else 0) := by
          apply Finset.sum_congr rfl
          intro xs hxs
          by_cases hmod : P xs
          · simp only [if_pos hmod]
            rw [Finset.univ.mul_sum]
            apply Finset.sum_congr rfl
            intro K hK
            rw [Finset.univ.mul_sum]
          · simp [hmod]
      _ = ∑ K : Finset (Fin S.d),
            ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)),
              ∑ xs : Fin κ.u → Fin (T.S.N k),
                (if P xs then W xs * selectorAbs K f xs else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro K hK
          rw [Finset.sum_comm]
  have hIntegralBound :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        if P xs then W xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
        ∑ K : Finset (Fin S.d),
          ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), H K f := by
    calc
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
            |if P xs then W xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ xs : Fin κ.u → Fin (T.S.N k),
            if P xs then W xs * |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0 := by
          apply Finset.sum_congr rfl
          intro xs hxs
          by_cases hmod : P xs
          · calc
              |if P xs then W xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| =
                  |W xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs| := by rw [if_pos hmod]
              _ = W xs * |Phi (T.S.E k) c (fun l => (S.π l).w) xs| := by
                rw [abs_mul, abs_of_nonneg (hWnonneg xs)]
              _ = if P xs then W xs *
                    |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0 := by simp [hmod]
          · simp [hmod]
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
            if P xs then W xs *
              (∑ K : Finset (Fin S.d),
                ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), selectorAbs K f xs)
            else 0 := by
          apply Finset.sum_le_sum
          intro xs hxs
          exact hpoint xs
      _ = _ := hmove
  let B : ℝ := n ^ (-(1.5 : ℝ) * (κ.L : ℝ))
  have hBnonneg : 0 ≤ B := by positivity
  have hselectorBound (K : Finset (Fin S.d))
      (f : ∀ l : {l // l ∈ K}, Finset (Fin κ.u)) :
      H K f ≤ if K.card ≤ κ.L then B else t ^ K.card := by
    by_cases hgood : good K f
    · have hsize : ∀ l, 2 ≤ (f l).card := hgood.1
      by_cases hK : K.card ≤ κ.L
      · obtain ⟨l₀, hl₀⟩ := Lane_q_s12_mom.selected_cover_has_large_interaction
          hLpos hκ.u_rng.2 K f hK hgood.2
        have hJtwo : 2 ≤ (f l₀).card := by omega
        have hJle : (f l₀).card ≤ κ.u := by
          simpa using Finset.card_le_univ (f l₀)
        have hmeanRaw := hMeanK S l₀.1 (f l₀) hJtwo hJle hDeg
        have hmean :
            (∑ xs : Fin κ.u → Fin (T.S.N k),
              W xs * |inter (T.S.E k) c (S.π l₀.1).w (f l₀) xs|) ≤
                n ^ (-(0.4 : ℝ) * ((f l₀).card : ℝ)) := by
          simpa [n, W] using hmeanRaw
        have hlargeR : 4 * (κ.L : ℝ) ≤ ((f l₀).card : ℝ) := by
          exact_mod_cast hl₀
        have hexp : -(0.4 : ℝ) * ((f l₀).card : ℝ) ≤
            -(1.5 : ℝ) * (κ.L : ℝ) := by
          nlinarith
        have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hexp
        have hmeanStrong := hmean.trans hpow
        have hprod (xs : Fin κ.u → Fin (T.S.N k)) (hmod : P xs) :
            |∏ l : {l // l ∈ K}, inter (T.S.E k) c (S.π l.1).w (f l) xs| ≤
              |inter (T.S.E k) c (S.π l₀.1).w (f l₀) xs| :=
          Lane_q_s12_mom.selected_interaction_product_abs_le
            (T.S.E k) c (fun l => (S.π l).w) xs K f l₀ t htle hsize hmod
        have hcomp :
            (∑ xs : Fin κ.u → Fin (T.S.N k),
              if P xs then W xs *
                |∏ l : {l // l ∈ K}, inter (T.S.E k) c (S.π l.1).w (f l) xs|
              else 0) ≤
            ∑ xs : Fin κ.u → Fin (T.S.N k),
              W xs * |inter (T.S.E k) c (S.π l₀.1).w (f l₀) xs| := by
          apply Finset.sum_le_sum
          intro xs hxs
          by_cases hmod : P xs
          · simp only [if_pos hmod]
            exact mul_le_mul_of_nonneg_left (hprod xs hmod) (hWnonneg xs)
          · simp only [if_neg hmod]
            have hnonneg := mul_nonneg (hWnonneg xs)
              (abs_nonneg (inter (T.S.E k) c (S.π l₀.1).w (f l₀) xs))
            simpa [W] using hnonneg
        have hlow :
            (∑ xs : Fin κ.u → Fin (T.S.N k),
              if P xs then W xs * selectorAbs K f xs else 0) ≤ B := by
          simpa [selectorAbs, hgood, B] using hcomp.trans hmeanStrong
        simpa [H, hgood, hK] using hlow
      · have hhigh :
            (∑ xs : Fin κ.u → Fin (T.S.N k),
              if P xs then W xs *
                |∏ l : {l // l ∈ K}, inter (T.S.E k) c (S.π l.1).w (f l) xs|
              else 0) ≤ t ^ K.card := by
          apply prodW_mul_event_le S.τ P
            (fun xs => |∏ l : {l // l ∈ K},
              inter (T.S.E k) c (S.π l.1).w (f l) xs|) (t ^ K.card)
          · positivity
          · intro xs
            positivity
          · intro xs hsupp hmod
            exact Lane_q_s12_mom.selected_interaction_product_abs_le_pow
              (T.S.E k) c (fun l => (S.π l).w) xs K f t
              (le_of_lt htpos) hsize hmod
        simpa [H, selectorAbs, hgood, hK] using hhigh
    · have hnonneg : 0 ≤ if K.card ≤ κ.L then B else t ^ K.card := by
        split_ifs
        · exact hBnonneg
        · exact pow_nonneg (le_of_lt htpos) _
      simpa [H, selectorAbs, hgood] using hnonneg
  have hselectorInner (K : Finset (Fin S.d)) :
      (∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), H K f) ≤
        if K.card ≤ κ.L then
          (Fintype.card (∀ l : {l // l ∈ K}, Finset (Fin κ.u)) : ℝ) * B
        else
          (Fintype.card (∀ l : {l // l ∈ K}, Finset (Fin κ.u)) : ℝ) * t ^ K.card := by
    calc
      _ ≤ ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)),
            (if K.card ≤ κ.L then B else t ^ K.card) := by
        apply Finset.sum_le_sum
        intro f hf
        exact hselectorBound K f
      _ = (Fintype.card (∀ l : {l // l ∈ K}, Finset (Fin κ.u)) : ℝ) *
            (if K.card ≤ κ.L then B else t ^ K.card) := by simp
      _ = _ := by by_cases hK : K.card ≤ κ.L <;> simp [hK]
  have hcardFunction (K : Finset (Fin S.d)) :
      (Fintype.card (∀ l : {l // l ∈ K}, Finset (Fin κ.u)) : ℝ) = a ^ K.card := by
    rw [Lane_q_s12_mom.selector_function_card K]
    simp [a, Nat.cast_pow]
  have hselectorInner' (K : Finset (Fin S.d)) :
      (∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), H K f) ≤
        if K.card ≤ κ.L then a ^ K.card * B else (a * t) ^ K.card := by
    have h := hselectorInner K
    rw [hcardFunction K] at h
    by_cases hK : K.card ≤ κ.L
    · simpa [hK] using h
    · simpa [hK, ← mul_pow] using h
  have hselectorTotalBound :
      (∑ K : Finset (Fin S.d), ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), H K f) ≤
        (∑ K : Finset (Fin S.d),
          if K.card ≤ κ.L then a ^ K.card * B else 0) +
        (∑ K : Finset (Fin S.d),
          if κ.L < K.card then (a * t) ^ K.card else 0) := by
    calc
      _ ≤ ∑ K : Finset (Fin S.d),
            if K.card ≤ κ.L then a ^ K.card * B else (a * t) ^ K.card := by
        apply Finset.sum_le_sum
        intro K hK
        exact hselectorInner' K
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro K hK
        by_cases hKsmall : K.card ≤ κ.L
        · have hKlarge : ¬ κ.L < K.card := by omega
          simp [hKsmall, hKlarge]
        · have hKlarge : κ.L < K.card := by omega
          simp [hKsmall, hKlarge]
  have hcountLow := Lane_q_s12_mom.low_selection_count_bound_real
    (d := S.d) (u := κ.u) (L := κ.L) (n := T.S.n k) S.d_le hnNatK
  have hLowCount :
      (∑ K : Finset (Fin S.d), if K.card ≤ κ.L then a ^ K.card else 0) ≤
        A * n ^ κ.L := by
    calc
      _ ≤ ((κ.L + 1 : ℕ) : ℝ) * n ^ κ.L * a ^ κ.L := by
        simpa [a, n, Nat.cast_pow, Real.rpow_natCast] using hcountLow
      _ = A * n ^ κ.L := by dsimp [A]; ring
  have hLowSumEq :
      (∑ K : Finset (Fin S.d),
        if K.card ≤ κ.L then a ^ K.card * B else 0) =
        (∑ K : Finset (Fin S.d),
          if K.card ≤ κ.L then a ^ K.card else 0) * B := by
    calc
      _ = ∑ K : Finset (Fin S.d),
            (if K.card ≤ κ.L then a ^ K.card else 0) * B := by
              apply Finset.sum_congr rfl
              intro K hK
              by_cases hKsmall : K.card ≤ κ.L <;> simp [hKsmall]
      _ = _ := by rw [Finset.sum_mul]
  have hLowTotalBound :
      (∑ K : Finset (Fin S.d),
        if K.card ≤ κ.L then a ^ K.card * B else 0) ≤ A * n ^ κ.L * B := by
    rw [hLowSumEq]
    exact mul_le_mul_of_nonneg_right hLowCount hBnonneg
  have hA2 : a < n ^ (0.01 : ℝ) := by
    simpa [a, n, Nat.cast_pow, Real.rpow_natCast] using h2powK
  have hdReal : (S.d : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast S.d_le
  have hq : (S.d : ℝ) * (a * t) ≤ n ^ (-(0.02 : ℝ)) := by
    calc
      (S.d : ℝ) * (a * t) = (S.d : ℝ) * a * t := by ring
      _ ≤ n * a * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdReal (by positivity)) (le_of_lt htpos)
      _ ≤ n * n ^ (0.01 : ℝ) * t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_of_lt hA2) (le_of_lt hnpos)) (le_of_lt htpos)
      _ = n ^ (-(0.02 : ℝ)) := by
        dsimp [t]
        calc
          n * n ^ (0.01 : ℝ) * n ^ (-(1.03 : ℝ)) =
              n ^ (1 : ℝ) * n ^ (0.01 : ℝ) * n ^ (-(1.03 : ℝ)) := by simp
          _ = n ^ ((1 : ℝ) + (0.01 : ℝ)) * n ^ (-(1.03 : ℝ)) := by
            rw [← Real.rpow_add hnpos]
          _ = n ^ (((1 : ℝ) + (0.01 : ℝ)) + (-(1.03 : ℝ))) := by
            rw [← Real.rpow_add hnpos]
          _ = n ^ (-(0.02 : ℝ)) := by congr 1 <;> norm_num
  have hqOne : (S.d : ℝ) * (a * t) ≤ 1 :=
    hq.trans (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num))
  have hHighSelectorBound :
      (∑ K : Finset (Fin S.d),
        if κ.L < K.card then (a * t) ^ K.card else 0) ≤
          ((S.d + 1 : ℕ) : ℝ) * ((S.d : ℝ) * (a * t)) ^ (κ.L + 1) :=
    Lane_q_s12_mom.high_selection_weight_bound (d := S.d) (L := κ.L)
      (a * t) (mul_nonneg (by positivity) (le_of_lt htpos)) hqOne
  have hselectorTotal :
      (∑ K : Finset (Fin S.d),
        ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin κ.u)), H K f) ≤
          A * n ^ κ.L * B +
            ((S.d + 1 : ℕ) : ℝ) * ((S.d : ℝ) * (a * t)) ^ (κ.L + 1) := by
    calc
      _ ≤ _ := hselectorTotalBound
      _ ≤ _ := add_le_add hLowTotalBound hHighSelectorBound
  have hLowPow :
      n ^ (κ.L : ℝ) * n ^ (-(1.5 : ℝ) * (κ.L : ℝ)) =
        n ^ (-(0.5 : ℝ) * (κ.L : ℝ)) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hLowApproxEq : A * n ^ κ.L * B = A * n ^ (-(0.5 : ℝ) * (κ.L : ℝ)) := by
    dsimp [B]
    calc
      _ = A * (n ^ (κ.L : ℝ) * n ^ (-(1.5 : ℝ) * (κ.L : ℝ))) := by
        rw [← Real.rpow_natCast n κ.L]
        ring
      _ = _ := by rw [hLowPow]
  have hLowRatioEq :
      A * n ^ (-(0.5 : ℝ) * (κ.L : ℝ)) =
        (6 * A * n ^ (-δL)) * (n ^ (-(3 * (κ.R : ℝ))) / 6) := by
    symm
    calc
      (6 * A * n ^ (-δL)) * (n ^ (-(3 * (κ.R : ℝ))) / 6) =
          A * (n ^ (-δL) * n ^ (-(3 * (κ.R : ℝ)))) := by ring
      _ = A * n ^ ((-δL) + (-(3 * (κ.R : ℝ)))) := by
        rw [← Real.rpow_add hnpos]
      _ = A * n ^ (-(0.5 : ℝ) * (κ.L : ℝ)) := by
        congr 1
        dsimp [δL]
        ring
  have hLowApprox :
      A * n ^ κ.L * B ≤ n ^ (-(3 * (κ.R : ℝ))) / 6 := by
    rw [hLowApproxEq, hLowRatioEq]
    have hLowK' : 6 * A * n ^ (-δL) ≤ 1 := by
      simpa [n] using (le_of_lt hLowK)
    calc
      6 * A * n ^ (-δL) * (n ^ (-(3 * (κ.R : ℝ))) / 6) ≤
          1 * (n ^ (-(3 * (κ.R : ℝ))) / 6) :=
        mul_le_mul_of_nonneg_right hLowK' (by positivity)
      _ = n ^ (-(3 * (κ.R : ℝ))) / 6 := by ring
  have hdPlus : ((S.d + 1 : ℕ) : ℝ) ≤ n + 1 := by
    dsimp [n]
    exact_mod_cast Nat.add_le_add_right S.d_le 1
  have hnPlus : n + 1 ≤ 2 * n := by linarith only [hn1]
  have hqNonneg : 0 ≤ (S.d : ℝ) * (a * t) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (le_of_lt htpos))
  have hqPow :
      ((S.d : ℝ) * (a * t)) ^ (κ.L + 1) ≤
        (n ^ (-(0.02 : ℝ))) ^ (κ.L + 1) :=
    pow_le_pow_left₀ hqNonneg hq (κ.L + 1)
  have hHighPow :
      (n ^ (-(0.02 : ℝ))) ^ (κ.L + 1) =
        n ^ (-(0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_mul_natCast (le_of_lt hnpos) (-(0.02 : ℝ)) (κ.L + 1)]
  have hHighRatioEq :
      (12 * n ^ (-δH)) * (n ^ (-(3 * (κ.R : ℝ))) / 6) =
        2 * n ^ (1 - (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) := by
    calc
      (12 * n ^ (-δH)) * (n ^ (-(3 * (κ.R : ℝ))) / 6) =
          2 * (n ^ (-δH) * n ^ (-(3 * (κ.R : ℝ)))) := by ring
      _ = 2 * n ^ ((-δH) + (-(3 * (κ.R : ℝ)))) := by
        rw [← Real.rpow_add hnpos]
      _ = 2 * n ^ (1 - (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) := by
        congr 1
        dsimp [δH]
        ring
  have hHighApprox :
      2 * n ^ (1 - (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) ≤
        n ^ (-(3 * (κ.R : ℝ))) / 6 := by
    rw [← hHighRatioEq]
    calc
      12 * n ^ (-δH) * (n ^ (-(3 * (κ.R : ℝ))) / 6) ≤
          1 * (n ^ (-(3 * (κ.R : ℝ))) / 6) :=
        mul_le_mul_of_nonneg_right (le_of_lt hHighK) (by positivity)
      _ = n ^ (-(3 * (κ.R : ℝ))) / 6 := by ring
  have hHighCoarse :
      ((S.d + 1 : ℕ) : ℝ) * ((S.d : ℝ) * (a * t)) ^ (κ.L + 1) ≤
        2 * n ^ (1 - (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ (n + 1) * ((S.d : ℝ) * (a * t)) ^ (κ.L + 1) :=
        mul_le_mul_of_nonneg_right hdPlus (pow_nonneg hqNonneg _)
      _ ≤ (n + 1) * (n ^ (-(0.02 : ℝ))) ^ (κ.L + 1) :=
        mul_le_mul_of_nonneg_left hqPow (by positivity)
      _ ≤ 2 * n * (n ^ (-(0.02 : ℝ))) ^ (κ.L + 1) :=
        mul_le_mul_of_nonneg_right hnPlus (pow_nonneg (Real.rpow_nonneg hnpos.le _) _)
      _ = 2 * n ^ (1 - (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) := by
        rw [hHighPow]
        calc
          2 * n * n ^ (-(0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) =
              2 * (n ^ (1 : ℝ) *
                n ^ (-(0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ))) := by
                  rw [Real.rpow_one]
                  ring
          _ = 2 * n ^ (1 - (0.02 : ℝ) * ((κ.L + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_add hnpos]
            congr 2
            ring
  calc
    _ ≤ A * n ^ κ.L * B +
          ((S.d + 1 : ℕ) : ℝ) * ((S.d : ℝ) * (a * t)) ^ (κ.L + 1) :=
      hIntegralBound.trans hselectorTotal
    _ ≤ n ^ (-(3 * (κ.R : ℝ))) / 6 +
          n ^ (-(3 * (κ.R : ℝ))) / 6 :=
      add_le_add hLowApprox (hHighCoarse.trans hHighApprox)
    _ = n ^ (-(3 * (κ.R : ℝ))) / 3 := by ring

set_option maxHeartbeats 1000000 in
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
  classical
  have hnNat : Tendsto T.S.n atTop atTop := T.S.n_tendsto
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp hnNat
  have hPpos : 0 < κ.P := by
    have hp := hκ.P_big.2
    rw [hκ.Ac_eq] at hp
    omega
  have hRpos : 0 < κ.R := by rw [hκ.R_eq]; positivity
  have hRone : 1 ≤ κ.R := by omega
  have hLpos : 0 < κ.L := by rw [hκ.L_eq]; omega
  have hUpos : 1 ≤ κ.u := by
    have hu := hκ.u_rng.2
    omega
  have hAlpha : 0 < κ.α := hκ.α_rng.1
  have hXi : 0 < κ.ξ := hκ.ξ_rng.1
  let a : ℝ := ((2 ^ κ.u : ℕ) : ℝ)
  have h2a : 2 * a = (2 : ℝ) ^ (κ.u + 1) := by
    dsimp [a]
    rw [Nat.cast_pow, pow_succ]
    ring
  have hXiPower :
      (2 : ℝ) ^ (κ.u + 1) * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) =
        Real.rpow 2 (-(9 * (κ.u : ℝ) + 99)) := by
    have hNatCastPow : (2 : ℝ) ^ (κ.u + 1) =
        Real.rpow 2 ((κ.u + 1 : ℕ) : ℝ) := by
      symm
      exact Real.rpow_natCast 2 (κ.u + 1)
    calc
      (2 : ℝ) ^ (κ.u + 1) * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) =
          Real.rpow 2 ((κ.u + 1 : ℕ) : ℝ) *
            Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := by rw [hNatCastPow]
      _ = Real.rpow 2 (((κ.u + 1 : ℕ) : ℝ) + (-(10 * (κ.u : ℝ) + 100))) :=
        (Real.rpow_add (by norm_num : 0 < (2 : ℝ)) _ _).symm
      _ = Real.rpow 2 (-(9 * (κ.u : ℝ) + 99)) := by
        congr 1
        push_cast
        ring
  have hXiPowBound :
      Real.rpow 2 (-(9 * (κ.u : ℝ) + 99)) ≤ 1 / 16 := by
    have huReal : 1 ≤ (κ.u : ℝ) := by exact_mod_cast hUpos
    have hexp : -(9 * (κ.u : ℝ) + 99) ≤ (-4 : ℝ) := by nlinarith
    have hpow : Real.rpow 2 (-4 : ℝ) = 1 / 16 := by
      change (2 : ℝ) ^ (-(4 : ℝ)) = 1 / 16
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (4 : ℝ)]
      norm_num
    calc
      _ ≤ Real.rpow 2 (-4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 / 16 := hpow
  have hXiCoeff : 2 * a * κ.ξ ≤ κ.α / 12 := by
    rw [h2a]
    have hmul := mul_lt_mul_of_pos_left hκ.ξ_rng.2
      (pow_pos (by norm_num : (0 : ℝ) < 2) (κ.u + 1))
    have hstrict : (2 : ℝ) ^ (κ.u + 1) * κ.ξ < κ.α / 12 := by
      calc
        (2 : ℝ) ^ (κ.u + 1) * κ.ξ <
            (2 : ℝ) ^ (κ.u + 1) * (κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100))) := hmul
        _ = κ.α * ((2 : ℝ) ^ (κ.u + 1) *
            Real.rpow 2 (-(10 * (κ.u : ℝ) + 100))) := by ring
        _ ≤ κ.α * (1 / 16) := mul_le_mul_of_nonneg_left
            (by rw [hXiPower]; exact hXiPowBound) hAlpha.le
        _ ≤ κ.α / 12 := by nlinarith [hAlpha]
    exact hstrict.le
  have hsmallLogTendsto : Tendsto
      (fun k => a * (T.S.n k : ℝ) ^ (-(0.03 : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.03)).comp hn
    simpa [mul_comm] using h.const_mul a
  have hsmallLog : ∀ᶠ k in atTop,
      a * (T.S.n k : ℝ) ^ (-(0.03 : ℝ)) < Real.log (3 / 2 : ℝ) := by
    have h := hsmallLogTendsto.eventually
      (Iio_mem_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)))
    filter_upwards [h] with k hk
    exact hk
  have hmidExpTendsto : Tendsto
      (fun k => a * (T.S.n k : ℝ) ^ (-(0.34 : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.34)).comp hn
    simpa [mul_comm] using h.const_mul a
  have hmidExpSmall : ∀ᶠ k in atTop,
      a * (T.S.n k : ℝ) ^ (-(0.34 : ℝ)) < 1 / 2 := by
    have h := hmidExpTendsto.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [h] with k hk
    exact hk
  have hnOne : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) :=
    hn.eventually_ge_atTop 1
  have ht1 : Tendsto (fun k => (T.S.n k : ℝ) ^ (-(1.03 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp hn
  have ht94 : Tendsto (fun k => (T.S.n k : ℝ) ^ (-(0.94 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp hn
  have hT1to2 : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (-(1.03 : ℝ)) ≤ 2 * κ.ξ := by
    have hsmall := ht1.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 2 * κ.ξ))
    filter_upwards [hsmall] with k hk
    exact le_of_lt hk
  have hT94to2 : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (-(0.94 : ℝ)) ≤ 2 * κ.ξ := by
    have hsmall := ht94.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 2 * κ.ξ))
    filter_upwards [hsmall] with k hk
    exact le_of_lt hk
  have hn33 : Tendsto (fun k => (T.S.n k : ℝ) ^ (0.33 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hn
  have hn33Two : ∀ᶠ k in atTop, 2 ≤ (T.S.n k : ℝ) ^ (0.33 : ℝ) :=
    hn33.eventually_ge_atTop 2
  let Cmid : ℝ := a * 4 ^ κ.u
  let Chigh : ℝ := a * 4 ^ κ.u
  have hMidRatio :
      Tendsto (fun k => 3 * Cmid * (T.S.n k : ℝ) ^ (1 + 3 * (κ.R : ℝ)) *
        Real.exp (-(1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ))) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_rpow
      (x := fun k => (T.S.n k : ℝ)) (p := (0.4 : ℝ))
      (s := 1 + 3 * (κ.R : ℝ)) (b := (1 / 2 : ℝ)) hn
      (by norm_num) (by norm_num)
    simpa [mul_assoc] using h.const_mul (3 * Cmid)
  have hMidRatioSmall : ∀ᶠ k in atTop,
      3 * Cmid * (T.S.n k : ℝ) ^ (1 + 3 * (κ.R : ℝ)) *
        Real.exp (-(1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (0.4 : ℝ)) < 1 :=
    hMidRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hHighRatio :
      Tendsto (fun k => 3 * Chigh * (T.S.n k : ℝ) ^ (1 + 3 * (κ.R : ℝ)) *
        Real.exp (-(κ.α / 4) * (T.S.n k : ℝ))) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_rpow
      (x := fun k => (T.S.n k : ℝ)) (p := (1 : ℝ))
      (s := 1 + 3 * (κ.R : ℝ)) (b := κ.α / 4) hn
      (by norm_num) (by positivity)
    simpa [mul_assoc] using h.const_mul (3 * Chigh)
  have hHighRatioSmall : ∀ᶠ k in atTop,
      3 * Chigh * (T.S.n k : ℝ) ^ (1 + 3 * (κ.R : ℝ)) *
        Real.exp (-(κ.α / 4) * (T.S.n k : ℝ)) < 1 :=
    hHighRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have htarget : Tendsto
      (fun k => (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) / 3) atTop (nhds 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by positivity : 0 < 3 * (κ.R : ℝ))).comp hn
    simpa using hpow.div_const 3
  have htargetQuarter : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) / 3 ≤ 1 / 4 := by
    have hsmall := htarget.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    filter_upwards [hsmall] with k hk
    exact le_of_lt hk
  filter_upwards [hPointwise, hTails, hCancel, hT1to2, hT94to2, hn33Two,
    hMidRatioSmall, hHighRatioSmall, htargetQuarter, hsmallLog, hmidExpSmall, hnOne] with
    k hPointwiseK hTailsK hCancelK hT1K hT94K _hn33K
      hMidRatioK hHighRatioK htargetQuarterK hsmallLogK hmidExpSmallK hnOneK
  intro S hDeg
  let n : ℝ := (T.S.n k : ℝ)
  let t1 : ℝ := n ^ (-(1.03 : ℝ))
  let t94 : ℝ := n ^ (-(0.94 : ℝ))
  let t2 : ℝ := 2 * κ.ξ
  let target : ℝ := n ^ (-(3 * (κ.R : ℝ)))
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hnOneK
  have hcut12 : t1 ≤ t94 := by
    dsimp [t1, t94]
    exact Real.rpow_le_rpow_of_exponent_le hnOneK (by norm_num)
  have hcut2 : t94 ≤ t2 := by simpa [n, t94, t2] using hT94K
  have hcut1 : t1 ≤ t2 := hcut12.trans hcut2
  have ht1pos : 0 < t1 := Real.rpow_pos_of_pos hnpos _
  have ht94pos : 0 < t94 := Real.rpow_pos_of_pos hnpos _
  have ht2pos : 0 < t2 := by positivity
  have htail1Bound :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
        then prodW S.τ.w xs else 0) ≤
        n * 4 ^ κ.u * Real.exp (-(n ^ (0.4 : ℝ))) := by
    rcases hTailsK S hDeg with ⟨h1, _⟩
    simpa [n, t1] using h1
  have htail94Bound :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
        then prodW S.τ.w xs else 0) ≤
        n * 4 ^ κ.u * Real.exp (-(κ.α * n / 3)) := by
    rcases hTailsK S hDeg with ⟨_, h94⟩
    simpa [n, t94] using h94
  have hcancelSmall :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
        then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
          target / 3 := by
    simpa [n, t1, target] using hCancelK S hDeg
  let M1 : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
  let M94 : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
  let M2 : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs
  have hModerateMono {v : ℕ} (s t : ℝ) (hst : s ≤ t)
      (xs : Fin v → Fin (T.S.N k)) :
      Moderate (T.S.E k) c (fun l => (S.π l).w) s xs →
        Moderate (T.S.E k) c (fun l => (S.π l).w) t xs := by
    intro h l J hJ
    exact (h l J hJ).trans hst
  have hM12 : ∀ xs, M1 xs → M94 xs := by
    intro xs h
    exact hModerateMono t1 t94 hcut12 xs h
  have hM942 : ∀ xs, M94 xs → M2 xs := by
    intro xs h
    exact hModerateMono t94 t2 hcut2 xs h
  have hWnonneg (xs : Fin κ.u → Fin (T.S.N k)) : 0 ≤ prodW S.τ.w xs := by
    unfold prodW
    exact Finset.prod_nonneg fun i hi => S.τ.nonneg (xs i)
  have hcoords (xs : Fin κ.u → Fin (T.S.N k))
      (hW : 0 < prodW S.τ.w xs) : ∀ i, 0 < S.τ.w (xs i) := by
    intro i
    by_contra hi
    have hz : S.τ.w (xs i) = 0 := le_antisymm (le_of_not_gt hi) (S.τ.nonneg _)
    have hzero : prodW S.τ.w xs = 0 := by
      unfold prodW
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact (ne_of_gt hW) hzero
  have hπsum : ∀ l : Fin S.d, ∑ y, (S.π l).w y = 1 :=
    fun l => (S.π l).sum_eq_one
  have hπnonneg : ∀ l y, 0 ≤ (S.π l).w y := fun l y => (S.π l).nonneg y
  have haEq : (2 : ℝ) ^ κ.u = a := by simp [a, Nat.cast_pow]
  have haOne : 1 ≤ a := by
    have hnat : 1 ≤ 2 ^ κ.u := by
      calc
        1 = 1 ^ κ.u := by simp
        _ ≤ 2 ^ κ.u := Nat.pow_le_pow_left (by decide : 1 ≤ 2) κ.u
    dsimp [a]
    exact_mod_cast hnat
  have hpowU (u' : ℕ) (hu : u' ≤ κ.u) : ((2 : ℝ) ^ u') ≤ a := by
    have hnat : 2 ^ u' ≤ 2 ^ κ.u :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) hu
    dsimp [a]
    exact_mod_cast hnat
  have hcoeff {u' : ℕ} (hu : u' ≤ κ.u) (t : ℝ) (ht : 0 ≤ t) :
      ((2 : ℝ) ^ u') * S.d * t ≤ a * S.d * t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hpowU u' hu) (Nat.cast_nonneg _)) ht
  have hposPoint {u' : ℕ} (hu : u' ≤ κ.u)
      (xs : Fin u' → Fin (T.S.N k)) (I : Finset (Fin u')) (t : ℝ)
      (ht : 0 ≤ t) (hmod : Moderate (T.S.E k) c (fun l => (S.π l).w) t xs) :
      posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤ Real.exp (a * S.d * t) := by
    have hgeneric := posTerm_moderate_pointwise_generic
      (N := T.S.N k) (d := S.d) (u := u') (T.S.E k) c
      (fun l => (S.π l).w) hπsum hπnonneg xs I t ht hmod
    exact hgeneric.trans (Real.exp_le_exp.mpr (hcoeff hu t ht))
  have hsmallPower : n * t1 = n ^ (-(0.03 : ℝ)) := by
    calc
      n * t1 = n ^ (1 : ℝ) * t1 := by rw [Real.rpow_one]
      _ = n ^ (1 + (-(1.03 : ℝ))) := by
        dsimp [t1]
        rw [Real.rpow_add hnpos]
      _ = n ^ (-(0.03 : ℝ)) := by congr 1 <;> norm_num
  have hmidPower : n * t94 = n ^ (0.06 : ℝ) := by
    calc
      n * t94 = n ^ (1 : ℝ) * t94 := by rw [Real.rpow_one]
      _ = n ^ (1 + (-(0.94 : ℝ))) := by
        dsimp [t94]
        rw [Real.rpow_add hnpos]
      _ = n ^ (0.06 : ℝ) := by congr 1 <;> norm_num
  have hmidSplitPower :
      n ^ (-(0.34 : ℝ)) * n ^ (0.4 : ℝ) = n ^ (0.06 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    norm_num
  have hsmallExponent : a * S.d * t1 ≤ Real.log (3 / 2 : ℝ) := by
    have hd : (S.d : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast S.d_le
    have hdn : a * (S.d : ℝ) * t1 ≤ a * n * t1 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (by dsimp [a]; positivity)) ht1pos.le
    apply le_of_lt
    calc
      a * S.d * t1 ≤ a * n * t1 := hdn
      _ = a * n ^ (-(0.03 : ℝ)) := by
        calc
          a * n * t1 = a * (n * t1) := by ring
          _ = a * n ^ (-(0.03 : ℝ)) := by rw [hsmallPower]
      _ < Real.log (3 / 2 : ℝ) := by simpa [n] using hsmallLogK
  have hmidExponent : a * S.d * t94 ≤ (1 / 2 : ℝ) * n ^ (0.4 : ℝ) := by
    have hd : (S.d : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast S.d_le
    have hdn : a * S.d * t94 ≤ a * n * t94 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (by dsimp [a]; positivity)) ht94pos.le
    have hscaled := mul_lt_mul_of_pos_right hmidExpSmallK
      (Real.rpow_pos_of_pos hnpos (0.4 : ℝ))
    apply le_of_lt
    calc
      a * S.d * t94 ≤ a * n * t94 := hdn
      _ = a * n ^ (0.06 : ℝ) := by
        calc
          a * n * t94 = a * (n * t94) := by ring
          _ = a * n ^ (0.06 : ℝ) := by rw [hmidPower]
      _ = (a * n ^ (-(0.34 : ℝ))) * n ^ (0.4 : ℝ) := by
        rw [← hmidSplitPower]
        ring
      _ < (1 / 2 : ℝ) * n ^ (0.4 : ℝ) := by
        simpa [mul_assoc] using hscaled
  have hhighExponent : a * S.d * t2 ≤ κ.α * n / 12 := by
    have hd : (S.d : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast S.d_le
    have ha : 0 ≤ a := by dsimp [a]; positivity
    calc
      a * S.d * t2 ≤ a * n * t2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd ha) ht2pos.le
      _ = n * (2 * a * κ.ξ) := by dsimp [t2]; ring
      _ ≤ n * (κ.α / 12) :=
        mul_le_mul_of_nonneg_left hXiCoeff (le_of_lt hnpos)
      _ = κ.α * n / 12 := by ring
  have htargetQuarterK : target / 3 ≤ 1 / 4 := by
    simpa [n, target] using htargetQuarterK
  let tailMid : ℝ := n * 4 ^ κ.u * Real.exp (-(n ^ (0.4 : ℝ)))
  let tailHigh : ℝ := n * 4 ^ κ.u * Real.exp (-(κ.α * n / 3))
  let Bmid : ℝ := a * Real.exp (a * S.d * t94)
  let Bhigh : ℝ := a * Real.exp (a * S.d * t2)
  have htail1 :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ M1 xs then prodW S.τ.w xs else 0) ≤ tailMid := by
    simpa [tailMid, M1, t1, n] using htail1Bound
  have htail94 :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if ¬ M94 xs then prodW S.τ.w xs else 0) ≤ tailHigh := by
    simpa [tailHigh, M94, t94, n] using htail94Bound
  have hBmidtail : Bmid * tailMid ≤ target / 3 := by
    have hexp : Real.exp (a * S.d * t94) ≤
        Real.exp ((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) :=
      Real.exp_le_exp.mpr hmidExponent
    have hprod : Bmid * tailMid ≤
        Cmid * n * Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) := by
      calc
        Bmid * tailMid =
            (a * Real.exp (a * S.d * t94)) *
              (n * 4 ^ κ.u * Real.exp (-(n ^ (0.4 : ℝ)))) := by
                simp [Bmid, tailMid]
        _ ≤ (a * Real.exp ((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) *
              (n * 4 ^ κ.u * Real.exp (-(n ^ (0.4 : ℝ)))) := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left hexp (by dsimp [a]; positivity)
                · positivity
        _ = Cmid * n * Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) := by
          have he : Real.exp ((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) *
              Real.exp (-(n ^ (0.4 : ℝ))) =
                Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            (a * Real.exp ((1 / 2 : ℝ) * n ^ (0.4 : ℝ))) *
                (n * 4 ^ κ.u * Real.exp (-(n ^ (0.4 : ℝ)))) =
              (a * n * 4 ^ κ.u) *
                (Real.exp ((1 / 2 : ℝ) * n ^ (0.4 : ℝ)) *
                  Real.exp (-(n ^ (0.4 : ℝ)))) := by ring
            _ = (a * n * 4 ^ κ.u) *
                Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) := by rw [he]
            _ = Cmid * n * Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) := by
              simp [Cmid]
              ring
    have hratio : Cmid * n ^ (1 + 3 * (κ.R : ℝ)) *
        Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) < 1 / 3 := by
      nlinarith [hMidRatioK]
    have hpower : n ^ (1 + 3 * (κ.R : ℝ)) = n * n ^ (3 * (κ.R : ℝ)) := by
      calc
        n ^ (1 + 3 * (κ.R : ℝ)) = n ^ (1 : ℝ) * n ^ (3 * (κ.R : ℝ)) :=
          Real.rpow_add hnpos 1 (3 * (κ.R : ℝ))
        _ = n * n ^ (3 * (κ.R : ℝ)) := by rw [Real.rpow_one]
    have hcancelPower : n ^ (3 * (κ.R : ℝ)) *
        n ^ (-(3 * (κ.R : ℝ))) = 1 := by
      calc
        n ^ (3 * (κ.R : ℝ)) * n ^ (-(3 * (κ.R : ℝ))) =
            n ^ (3 * (κ.R : ℝ) + -(3 * (κ.R : ℝ))) := by
              rw [← Real.rpow_add hnpos]
        _ = 1 := by simp
    have hratio' := mul_lt_mul_of_pos_right hratio
      (Real.rpow_pos_of_pos hnpos (-(3 * (κ.R : ℝ))))
    rw [hpower] at hratio'
    have heq : Cmid * n * Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) =
        (Cmid * n * n ^ (3 * (κ.R : ℝ)) *
          Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ))) *
            n ^ (-(3 * (κ.R : ℝ))) := by
      calc
        _ = Cmid * n * Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) *
            (n ^ (3 * (κ.R : ℝ)) * n ^ (-(3 * (κ.R : ℝ)))) := by rw [hcancelPower]; ring
        _ = _ := by ring
    apply le_of_lt
    calc
      Bmid * tailMid ≤ Cmid * n *
          Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ)) := hprod
      _ = (Cmid * n * n ^ (3 * (κ.R : ℝ)) *
          Real.exp (-(1 / 2 : ℝ) * n ^ (0.4 : ℝ))) *
            n ^ (-(3 * (κ.R : ℝ))) := heq
      _ < (1 / 3 : ℝ) * n ^ (-(3 * (κ.R : ℝ))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hratio'
      _ = target / 3 := by simp [target]; ring
  have hBhighTail : Bhigh * tailHigh ≤ target / 3 := by
    have hexp : Real.exp (a * S.d * t2) ≤ Real.exp (κ.α * n / 12) :=
      Real.exp_le_exp.mpr hhighExponent
    have hprod : Bhigh * tailHigh ≤
        Cmid * n * Real.exp (-(κ.α / 4) * n) := by
      calc
        Bhigh * tailHigh =
            (a * Real.exp (a * S.d * t2)) *
              (n * 4 ^ κ.u * Real.exp (-(κ.α * n / 3))) := by
                simp [Bhigh, tailHigh]
        _ ≤ (a * Real.exp (κ.α * n / 12)) *
              (n * 4 ^ κ.u * Real.exp (-(κ.α * n / 3))) := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left hexp (by dsimp [a]; positivity)
                · positivity
        _ = Cmid * n * Real.exp (-(κ.α / 4) * n) := by
          have he : Real.exp (κ.α * n / 12) * Real.exp (-(κ.α * n / 3)) =
              Real.exp (-(κ.α / 4) * n) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            (a * Real.exp (κ.α * n / 12)) *
                (n * 4 ^ κ.u * Real.exp (-(κ.α * n / 3))) =
              (a * n * 4 ^ κ.u) *
                (Real.exp (κ.α * n / 12) * Real.exp (-(κ.α * n / 3))) := by ring
            _ = (a * n * 4 ^ κ.u) * Real.exp (-(κ.α / 4) * n) := by rw [he]
            _ = Cmid * n * Real.exp (-(κ.α / 4) * n) := by
              simp [Cmid]
              ring
    have hratio : Cmid * n ^ (1 + 3 * (κ.R : ℝ)) *
        Real.exp (-(κ.α / 4) * n) < 1 / 3 := by
      nlinarith [hHighRatioK]
    have hpower : n ^ (1 + 3 * (κ.R : ℝ)) = n * n ^ (3 * (κ.R : ℝ)) := by
      calc
        n ^ (1 + 3 * (κ.R : ℝ)) = n ^ (1 : ℝ) * n ^ (3 * (κ.R : ℝ)) :=
          Real.rpow_add hnpos 1 (3 * (κ.R : ℝ))
        _ = n * n ^ (3 * (κ.R : ℝ)) := by rw [Real.rpow_one]
    have hcancelPower : n ^ (3 * (κ.R : ℝ)) *
        n ^ (-(3 * (κ.R : ℝ))) = 1 := by
      calc
        n ^ (3 * (κ.R : ℝ)) * n ^ (-(3 * (κ.R : ℝ))) =
            n ^ (3 * (κ.R : ℝ) + -(3 * (κ.R : ℝ))) := by
              rw [← Real.rpow_add hnpos]
        _ = 1 := by simp
    have hratio' := mul_lt_mul_of_pos_right hratio
      (Real.rpow_pos_of_pos hnpos (-(3 * (κ.R : ℝ))))
    rw [hpower] at hratio'
    have heq : Cmid * n * Real.exp (-(κ.α / 4) * n) =
        (Cmid * n * n ^ (3 * (κ.R : ℝ)) *
          Real.exp (-(κ.α / 4) * n)) * n ^ (-(3 * (κ.R : ℝ))) := by
      calc
        _ = Cmid * n * Real.exp (-(κ.α / 4) * n) *
            (n ^ (3 * (κ.R : ℝ)) * n ^ (-(3 * (κ.R : ℝ)))) := by rw [hcancelPower]; ring
        _ = _ := by ring
    apply le_of_lt
    calc
      Bhigh * tailHigh ≤ Cmid * n * Real.exp (-(κ.α / 4) * n) := hprod
      _ = (Cmid * n * n ^ (3 * (κ.R : ℝ)) *
          Real.exp (-(κ.α / 4) * n)) * n ^ (-(3 * (κ.R : ℝ))) := heq
      _ < (1 / 3 : ℝ) * n ^ (-(3 * (κ.R : ℝ))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hratio'
      _ = target / 3 := by simp [target]; ring
  have hmedPhiPoint (xs : Fin κ.u → Fin (T.S.N k)) (hmod : M94 xs)
      (hsupport : ∀ i, 0 < S.τ.w (xs i)) : |Phi (T.S.E k) c (fun l => (S.π l).w) xs| ≤ Bmid := by
    have hpoint : ∀ I : Finset (Fin κ.u),
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (a * S.d * t94) := by
      intro I
      simpa [haEq] using hPointwiseK S t94 xs I hsupport hmod
    have hcard : (Fintype.card (Finset (Fin κ.u)) : ℝ) = a := by
      simp [a, Nat.cast_pow]
    calc
      |Phi (T.S.E k) c (fun l => (S.π l).w) xs| ≤
          (Fintype.card (Finset (Fin κ.u)) : ℝ) * Real.exp (a * S.d * t94) :=
        Lane_q_s12_mom.Phi_abs_le_card_mul_of_posTerm_bound
          (T.S.E k) c (fun l => (S.π l).w) hπnonneg xs
          (Real.exp (a * S.d * t94)) hpoint
      _ = a * Real.exp (a * S.d * t94) := by rw [hcard]
      _ = Bmid := rfl
  have hhighPhiPoint (xs : Fin κ.u → Fin (T.S.N k)) (hmod : M2 xs)
      (hsupport : ∀ i, 0 < S.τ.w (xs i)) : |Phi (T.S.E k) c (fun l => (S.π l).w) xs| ≤ Bhigh := by
    have hpoint : ∀ I : Finset (Fin κ.u),
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (a * S.d * t2) := by
      intro I
      simpa [haEq] using hPointwiseK S t2 xs I hsupport hmod
    have hcard : (Fintype.card (Finset (Fin κ.u)) : ℝ) = a := by
      simp [a, Nat.cast_pow]
    calc
      |Phi (T.S.E k) c (fun l => (S.π l).w) xs| ≤
          (Fintype.card (Finset (Fin κ.u)) : ℝ) * Real.exp (a * S.d * t2) :=
        Lane_q_s12_mom.Phi_abs_le_card_mul_of_posTerm_bound
          (T.S.E k) c (fun l => (S.π l).w) hπnonneg xs
          (Real.exp (a * S.d * t2)) hpoint
      _ = a * Real.exp (a * S.d * t2) := by rw [hcard]
      _ = Bhigh := rfl
  have htail1ForWeighted :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        @ite ℝ (¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs)
          (Classical.propDecidable _) (prodW S.τ.w xs) 0) ≤ tailMid := by
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hp : ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs <;> simp [hp]
      _ ≤ _ := htail1Bound
  have htail94ForWeighted :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        @ite ℝ (¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs)
          (Classical.propDecidable _) (prodW S.τ.w xs) 0) ≤ tailHigh := by
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hp : ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs <;> simp [hp]
      _ ≤ _ := htail94Bound
  let qtail1 : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
  let qtail94 : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
  let m94Dec : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
  let m2Dec : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs =>
    Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs
  let pmed : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs => m94Dec xs ∧ qtail1 xs
  let phigh : (Fin κ.u → Fin (T.S.N k)) → Prop := fun xs => m2Dec xs ∧ qtail94 xs
  letI : DecidablePred m94Dec := fun xs => Classical.propDecidable _
  letI : DecidablePred m2Dec := fun xs => Classical.propDecidable _
  letI : DecidablePred qtail1 := fun xs => by
    letI : Decidable (Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs) :=
      Classical.propDecidable _
    exact inferInstance
  letI : DecidablePred qtail94 := fun xs => by
    letI : Decidable (Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs) :=
      Classical.propDecidable _
    exact inferInstance
  letI : DecidablePred pmed := fun xs => inferInstance
  letI : DecidablePred phigh := fun xs => inferInstance
  have hmedPhiWeighted :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if M94 xs ∧ ¬ M1 xs then prodW S.τ.w xs *
          |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0) ≤ Bmid * tailMid := by
    have hbound := Lane_q_s12_mom.weighted_event_factor_bound S.τ
      pmed qtail1
      (fun xs => |Phi (T.S.E k) c (fun l => (S.π l).w) xs|)
      Bmid tailMid (by unfold Bmid; positivity) (by unfold tailMid; positivity)
      (by intro xs h; exact h.2)
      (by intro xs h hs; exact hmedPhiPoint xs h.1 hs)
      (fun xs => abs_nonneg _) htail1ForWeighted
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hp : M94 xs ∧ ¬ M1 xs <;> simp [hp, pmed, m94Dec, qtail1, M94, M1]
      _ ≤ _ := hbound
  have hhighPhiWeighted :
      (∑ xs : Fin κ.u → Fin (T.S.N k),
        if M2 xs ∧ ¬ M94 xs then prodW S.τ.w xs *
          |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0) ≤ Bhigh * tailHigh := by
    have hbound := Lane_q_s12_mom.weighted_event_factor_bound S.τ
      phigh qtail94
      (fun xs => |Phi (T.S.E k) c (fun l => (S.π l).w) xs|)
      Bhigh tailHigh (by unfold Bhigh; positivity) (by unfold tailHigh; positivity)
      (by intro xs h; exact h.2)
      (by intro xs h hs; exact hhighPhiPoint xs h.1 hs)
      (fun xs => abs_nonneg _) htail94ForWeighted
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hp : M2 xs ∧ ¬ M94 xs <;> simp [hp, phigh, m2Dec, qtail94, M2, M94]
      _ ≤ _ := hbound
  have hsignedMid :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        if M94 xs ∧ ¬ M1 xs then prodW S.τ.w xs *
          Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤ target / 3 := by
    calc
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          if M94 xs ∧ ¬ M1 xs then prodW S.τ.w xs *
            |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0 := by
        calc
          _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
              |if M94 xs ∧ ¬ M1 xs then prodW S.τ.w xs *
                Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro xs hxs
            by_cases hp : M94 xs ∧ ¬ M1 xs
            · simp [hp, abs_mul, abs_of_nonneg (hWnonneg xs)]
            · simp [hp]
      _ ≤ Bmid * tailMid := hmedPhiWeighted
      _ ≤ target / 3 := hBmidtail
  have hsignedHigh :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        if M2 xs ∧ ¬ M94 xs then prodW S.τ.w xs *
          Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤ target / 3 := by
    calc
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          if M2 xs ∧ ¬ M94 xs then prodW S.τ.w xs *
            |Phi (T.S.E k) c (fun l => (S.π l).w) xs| else 0 := by
        calc
          _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
              |if M2 xs ∧ ¬ M94 xs then prodW S.τ.w xs *
                Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro xs hxs
            by_cases hp : M2 xs ∧ ¬ M94 xs
            · simp [hp, abs_mul, abs_of_nonneg (hWnonneg xs)]
            · simp [hp]
      _ ≤ Bhigh * tailHigh := hhighPhiWeighted
      _ ≤ target / 3 := hBhighTail
  have hdecomp := Lane_q_s12_mom.sum_if_nested_split M1 M94 M2
    (fun xs => prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs)
    hM12 hM942
  have hsigned :
      |∑ xs : Fin κ.u → Fin (T.S.N k),
        if M2 xs then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤ target := by
    rw [hdecomp]
    let s1 := ∑ xs : Fin κ.u → Fin (T.S.N k),
      if M1 xs then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0
    let s2 := ∑ xs : Fin κ.u → Fin (T.S.N k),
      if M94 xs ∧ ¬ M1 xs then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0
    let s3 := ∑ xs : Fin κ.u → Fin (T.S.N k),
      if M2 xs ∧ ¬ M94 xs then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0
    have h1 : |s1| ≤ target / 3 := by simpa [s1, M1, t1, target, n] using hcancelSmall
    have h2 : |s2| ≤ target / 3 := hsignedMid
    have h3 : |s3| ≤ target / 3 := hsignedHigh
    calc
      |(s1 + s2) + s3| ≤ |s1 + s2| + |s3| := abs_add_le _ _
      _ ≤ (|s1| + |s2|) + |s3| := by linarith [abs_add_le s1 s2]
      _ ≤ target := by linarith
  have hprefixTail1 {u' : ℕ} (hu : u' ≤ κ.u) :
      (∑ xs : Fin u' → Fin (T.S.N k),
        if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
        then prodW S.τ.w xs else 0) ≤ tailMid := by
    calc
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
          then prodW S.τ.w xs else 0 :=
        by
          exact Lane_q_s12_mom.moderate_bad_prefix_mass_le S.τ
            (T.S.E k) c (fun l => (S.π l).w) t1 hu
      _ ≤ tailMid := htail1Bound
  have hprefixTail94 {u' : ℕ} (hu : u' ≤ κ.u) :
      (∑ xs : Fin u' → Fin (T.S.N k),
        if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
        then prodW S.τ.w xs else 0) ≤ tailHigh := by
    calc
      _ ≤ ∑ xs : Fin κ.u → Fin (T.S.N k),
          if ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
          then prodW S.τ.w xs else 0 :=
        by
          exact Lane_q_s12_mom.moderate_bad_prefix_mass_le S.τ
            (T.S.E k) c (fun l => (S.π l).w) t94 hu
      _ ≤ tailHigh := htail94Bound
  have hsmallIntegral {u' : ℕ} (hu : u' ≤ κ.u) (I : Finset (Fin u')) :
      (∑ xs : Fin u' → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
        then prodW S.τ.w xs * posTerm (T.S.E k) c (fun l => (S.π l).w) I xs
        else 0) ≤ 3 / 2 := by
    have hInt := moderate_posTerm_integral_bound
      S.τ (T.S.E k) c (fun l => (S.π l).w) hπsum hπnonneg I t1 ht1pos.le
    have hExp : Real.exp (((2 : ℝ) ^ u') * S.d * t1) ≤ 3 / 2 := by
      calc
        _ ≤ Real.exp (a * S.d * t1) := Real.exp_le_exp.mpr (hcoeff hu t1 ht1pos.le)
        _ ≤ 3 / 2 := by
          calc
            _ ≤ Real.exp (Real.log (3 / 2 : ℝ)) := Real.exp_le_exp.mpr hsmallExponent
            _ = 3 / 2 := Real.exp_log (by norm_num)
    exact hInt.trans hExp
  have hposMedium {u' : ℕ} (hu : u' ≤ κ.u) (I : Finset (Fin u')) :
      (∑ xs : Fin u' → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs ∧
            ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
        then prodW S.τ.w xs * posTerm (T.S.E k) c (fun l => (S.π l).w) I xs
        else 0) ≤ target / 3 := by
    let good : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
    let bad : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
    let p : (Fin u' → Fin (T.S.N k)) → Prop := fun xs => good xs ∧ bad xs
    letI : DecidablePred good := fun xs => Classical.propDecidable _
    letI : DecidablePred bad := fun xs => by
      letI : Decidable (Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs) :=
        Classical.propDecidable _
      exact inferInstance
    letI : DecidablePred p := fun xs => inferInstance
    have hmass :
        (∑ xs : Fin u' → Fin (T.S.N k),
          @ite ℝ (¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs)
            (Classical.propDecidable _) (prodW S.τ.w xs) 0) ≤ tailMid := by
      calc
        _ = _ := by
          apply Finset.sum_congr rfl
          intro xs hxs
          by_cases hp : ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs <;>
            simp [hp]
        _ ≤ _ := hprefixTail1 hu
    have hweighted := Lane_q_s12_mom.weighted_event_factor_bound S.τ
      p bad
      (fun xs => posTerm (T.S.E k) c (fun l => (S.π l).w) I xs)
      Bmid tailMid (by unfold Bmid; positivity) (by unfold tailMid; positivity)
      (by intro xs h; exact h.2)
      (by intro xs h hs
          exact (hposPoint hu xs I t94 ht94pos.le h.1).trans (by
            have hh := mul_le_mul_of_nonneg_right haOne
              (Real.exp_nonneg (a * S.d * t94))
            simpa [Bmid] using hh))
      (fun xs => posTerm_nonneg_of_nonneg_weights (T.S.E k) c
        (fun l => (S.π l).w) hπnonneg I xs)
      (by
        exact hmass)
    have hweightedFinal := hweighted.trans hBmidtail
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hp : Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs ∧
            ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs <;>
          simp [hp, p, good, bad]
      _ ≤ _ := hweightedFinal
  have hposHigh {u' : ℕ} (hu : u' ≤ κ.u) (I : Finset (Fin u')) :
      (∑ xs : Fin u' → Fin (T.S.N k),
        if Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs ∧
            ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
        then prodW S.τ.w xs * posTerm (T.S.E k) c (fun l => (S.π l).w) I xs
        else 0) ≤ target / 3 := by
    let good : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs
    let bad : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
    let p : (Fin u' → Fin (T.S.N k)) → Prop := fun xs => good xs ∧ bad xs
    letI : DecidablePred good := fun xs => Classical.propDecidable _
    letI : DecidablePred bad := fun xs => by
      letI : Decidable (Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs) :=
        Classical.propDecidable _
      exact inferInstance
    letI : DecidablePred p := fun xs => inferInstance
    have hmass :
        (∑ xs : Fin u' → Fin (T.S.N k),
          @ite ℝ (¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs)
            (Classical.propDecidable _) (prodW S.τ.w xs) 0) ≤ tailHigh := by
      calc
        _ = _ := by
          apply Finset.sum_congr rfl
          intro xs hxs
          by_cases hp : ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs <;>
            simp [hp]
        _ ≤ _ := hprefixTail94 hu
    have hweighted := Lane_q_s12_mom.weighted_event_factor_bound S.τ
      p bad
      (fun xs => posTerm (T.S.E k) c (fun l => (S.π l).w) I xs)
      Bhigh tailHigh (by unfold Bhigh; positivity) (by unfold tailHigh; positivity)
      (by intro xs h; exact h.2)
      (by intro xs h hs
          exact (hposPoint hu xs I t2 ht2pos.le h.1).trans (by
            have hh := mul_le_mul_of_nonneg_right haOne
              (Real.exp_nonneg (a * S.d * t2))
            simpa [Bhigh] using hh))
      (fun xs => posTerm_nonneg_of_nonneg_weights (T.S.E k) c
        (fun l => (S.π l).w) hπnonneg I xs)
      (by
        exact hmass)
    have hweightedFinal := hweighted.trans hBhighTail
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hp : Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs ∧
            ¬ Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs <;>
          simp [hp, p, good, bad]
      _ ≤ _ := hweightedFinal
  have hpositive {u' : ℕ} (hu : u' ≤ κ.u) (I : Finset (Fin u')) :
      (∑ xs : Fin u' → Fin (T.S.N k),
        (if Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs
         then prodW S.τ.w xs *
           posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0)) ≤ 2 := by
    let M1' : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      Moderate (T.S.E k) c (fun l => (S.π l).w) t1 xs
    let M94' : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      Moderate (T.S.E k) c (fun l => (S.π l).w) t94 xs
    let M2' : (Fin u' → Fin (T.S.N k)) → Prop := fun xs =>
      Moderate (T.S.E k) c (fun l => (S.π l).w) t2 xs
    have hM12' : ∀ xs, M1' xs → M94' xs := by
      intro xs h
      exact hModerateMono t1 t94 hcut12 xs h
    have hM942' : ∀ xs, M94' xs → M2' xs := by
      intro xs h
      exact hModerateMono t94 t2 hcut2 xs h
    have hdecomp' := Lane_q_s12_mom.sum_if_nested_split M1' M94' M2'
      (fun xs => prodW S.τ.w xs * posTerm (T.S.E k) c (fun l => (S.π l).w) I xs)
      hM12' hM942'
    rw [hdecomp']
    have hs := hsmallIntegral hu I
    have hm := hposMedium hu I
    have hh := hposHigh hu I
    have hq : target / 3 ≤ 1 / 4 := htargetQuarterK
    have hm' : (∑ xs : Fin u' → Fin (T.S.N k),
        if M94' xs ∧ ¬ M1' xs then prodW S.τ.w xs *
          posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 1 / 4 := by
      exact hm.trans hq
    have hh' : (∑ xs : Fin u' → Fin (T.S.N k),
        if M2' xs ∧ ¬ M94' xs then prodW S.τ.w xs *
          posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 1 / 4 := by
      exact hh.trans hq
    have hs' : (∑ xs : Fin u' → Fin (T.S.N k),
        if M1' xs then prodW S.τ.w xs *
          posTerm (T.S.E k) c (fun l => (S.π l).w) I xs else 0) ≤ 3 / 2 := by
      simpa [M1'] using hs
    linarith
  exact ⟨hsigned, fun u' hu I => hpositive hu I⟩

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
