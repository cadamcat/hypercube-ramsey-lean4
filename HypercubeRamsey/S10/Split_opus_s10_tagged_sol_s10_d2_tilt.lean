import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Polynomial factors are absorbed by a negative exponential of a positive power. -/
theorem power_exp_neg_tendsto {a c : ℝ} (b : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ b * Real.exp (-c * (n : ℝ) ^ a))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (_root_.tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hscaled :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / a) c hc).comp hpow
  apply Tendsto.congr' _ hscaled
  filter_upwards [Filter.eventually_atTop.mpr ⟨1, fun _ hn => hn⟩] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hexp : a * (b / a) = b := by field_simp [ha.ne']
  change ((n : ℝ) ^ a) ^ (b / a) * Real.exp (-c * (n : ℝ) ^ a) = _
  rw [← Real.rpow_mul hnpos.le, hexp]

/-- The retained-tilt error budget is small uniformly over all positive list sizes
up to the Section 10 block-count bound. -/
theorem uniform_retained_budget (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → r ≤ p10_1kFixedListBlockCount n δ →
      Real.exp (-((p10_1kTupleListLength n δ : ℝ) * r)) + (r : ℝ) *
        (Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (-δ) * p10_1kTupleListLength n δ)) +
          Real.exp (-((2 / 5 : ℝ) * p10_1kTupleListLength n δ))) ≤ 1 / 2 := by
  let B (n : ℕ) : ℝ :=
    Real.exp (-(n : ℝ) ^ (300 * δ)) +
      3 * (n : ℝ) ^ (200 * δ) * Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) +
      3 * (n : ℝ) ^ (200 * δ) * Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ)))
  have hA : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) ^ (300 * δ))) atTop (nhds 0) := by
    simpa using power_exp_neg_tendsto (a := 300 * δ) (c := 1) 0 (by positivity) (by norm_num)
  have hO : Tendsto (fun n : ℕ => 3 * (n : ℝ) ^ (200 * δ) *
      Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ)))) atTop (nhds 0) := by
    simpa [mul_assoc] using
      (power_exp_neg_tendsto (a := 299 * δ) (c := 6 / 25) (200 * δ)
        (by positivity) (by norm_num)).const_mul 3
  have hE : Tendsto (fun n : ℕ => 3 * (n : ℝ) ^ (200 * δ) *
      Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ)))) atTop (nhds 0) := by
    simpa [mul_assoc] using
      (power_exp_neg_tendsto (a := 300 * δ) (c := 2 / 5) (200 * δ)
        (by positivity) (by norm_num)).const_mul 3
  have hB : Tendsto B atTop (nhds 0) := by
    simpa [B] using (hA.add hO).add hE
  have hsmall := hB.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩]
    with n hsmall hn
  intro r hr hrR
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hround := p10_1kFixedListScale_rounding_bounds n δ hn hδ
  have hk : (n : ℝ) ^ (300 * δ) ≤ (p10_1kTupleListLength n δ : ℝ) := by
    exact_mod_cast Nat.le_ceil ((n : ℝ) ^ (300 * δ))
  have hgain : (n : ℝ) ^ (299 * δ) ≤
      (n : ℝ) ^ (-δ) * (p10_1kTupleListLength n δ : ℝ) := by
    calc
      (n : ℝ) ^ (299 * δ) = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hnpos.le _)
  have hr' : (r : ℝ) ≤ 3 * (n : ℝ) ^ (200 * δ) :=
    (by exact_mod_cast hrR : (r : ℝ) ≤ p10_1kFixedListBlockCount n δ).trans hround.2.2
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) ≤ p10_1kTupleListLength n δ := Nat.cast_nonneg _
  have hkr : (n : ℝ) ^ (300 * δ) ≤ (p10_1kTupleListLength n δ : ℝ) * r := by
    exact hk.trans (by nlinarith [hk0])
  have hAbs : Real.exp (-((p10_1kTupleListLength n δ : ℝ) * r)) ≤
      Real.exp (-(n : ℝ) ^ (300 * δ)) := Real.exp_le_exp.mpr (neg_le_neg hkr)
  have hOwn : Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (-δ) * p10_1kTupleListLength n δ)) ≤
      Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (299 * δ))) :=
    Real.exp_le_exp.mpr (by nlinarith [hgain])
  have hExt : Real.exp (-((2 / 5 : ℝ) * p10_1kTupleListLength n δ)) ≤
      Real.exp (-((2 / 5 : ℝ) * (n : ℝ) ^ (300 * δ))) :=
    Real.exp_le_exp.mpr (by nlinarith [hk])
  have hdom : Real.exp (-((p10_1kTupleListLength n δ : ℝ) * r)) + (r : ℝ) *
      (Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (-δ) * p10_1kTupleListLength n δ)) +
        Real.exp (-((2 / 5 : ℝ) * p10_1kTupleListLength n δ))) ≤ B n := by
    dsimp [B]
    calc
      _ = Real.exp (-((p10_1kTupleListLength n δ : ℝ) * r)) +
        (r : ℝ) * Real.exp (-((6 / 25 : ℝ) * (n : ℝ) ^ (-δ) * p10_1kTupleListLength n δ)) +
        (r : ℝ) * Real.exp (-((2 / 5 : ℝ) * p10_1kTupleListLength n δ)) := by ring
      _ ≤ _ := by gcongr
  exact hdom.trans hsmall.le

/-- A passing list has positive retained squared weight for the prescribed own
flags, provided every flagged own block satisfies the codegree condition. -/
theorem retained_weight_pos {N r k q : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour)
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (μ : Fin r → Law N)
    (gain : ℝ) (hgain : 0 ≤ gain) (own : Fin r → Prop)
    (hown : ∀ b, own b → FixedListOwnBlock E G ρ D (μ b) gain)
    (W : Fin r → Fin k → Fin N)
    (hgood : ¬ fixedListFailure E G ρ D μ gain W)
    (hbudget : Real.exp (-((k : ℝ) * r)) + (r : ℝ) *
      (Real.exp (-((6 / 25 : ℝ) * gain * k)) + Real.exp (-((2 / 5 : ℝ) * k))) ≤ 1 / 2) :
    0 < ∑ j : Fin q,
      if Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) (fixedListHitSet E G W) ∧
        ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * gain) * k)
          else Real.exp (-(6 / 5 : ℝ) * k)) *
            lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤
              lawMassOn (D j) (fixedListHitSet E G W)
      then ρ.w j * (lawMassOn (D j) (fixedListHitSet E G W)) ^ 2 else 0 := by
  classical
  obtain ⟨hA, hR⟩ := p10_1k_successfulFixedList_retainedTilt_half_mass E G ρ D μ gain W hgood hbudget
  let P := p10_1kSquaredTiltPrior ρ D (fixedListHitSet E G W) hA
  obtain ⟨j, hj, hp⟩ := p10_1k_FinProb_exists_pos_of_pr_pos P _
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hR)
  simp only [p10_1kTiltGoodClusterSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨habs, hrat⟩ := hj
  have habs' : Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D j) (fixedListHitSet E G W) := by
    simpa [mul_assoc] using le_of_not_gt habs
  have hmass : 0 < lawMassOn (D j) (fixedListHitSet E G W) :=
    lt_of_lt_of_le (Real.exp_pos _) habs'
  have hrat' (b : Fin r) :
      (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * gain) * k)
          else Real.exp (-(6 / 5 : ℝ) * k)) *
        lawMassOn (D j) (fixedListHitSetWithout E G W b) ≤
          lawMassOn (D j) (fixedListHitSet E G W) := by
    have hm : lawMassOn (D j) (fixedListHitSet E G W) ≤
        lawMassOn (D j) (fixedListHitSetWithout E G W b) :=
      Finset.sum_le_sum_of_subset_of_nonneg (p10_1k_fixedListHitSet_subsetWithout E G W b)
        (fun y _ _ => (D j).nonneg y)
    have hmp : 0 < lawMassOn (D j) (fixedListHitSetWithout E G W b) := hmass.trans_le hm
    have htest := hrat b
    have hthreshold :
        (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * gain) * k)
          else Real.exp (-(6 / 5 : ℝ) * k)) ≤
        lawMassOn (D j) (fixedListHitSet E G W) /
          lawMassOn (D j) (fixedListHitSetWithout E G W b) := by
      by_cases hc : FixedListOwnBlock E G ρ D (μ b) gain
      · have hr : Real.exp ((-Real.log 2 + (2 / 25 : ℝ) * gain) * k) ≤
          lawMassOn (D j) (fixedListHitSet E G W) /
            lawMassOn (D j) (fixedListHitSetWithout E G W b) := by
          apply le_of_not_gt
          intro hlt
          exact htest (Or.inl ⟨hc, hlt⟩)
        by_cases ho : own b
        · simpa only [if_pos ho, show (8 / 100 : ℝ) = 2 / 25 by norm_num] using hr
        · rw [if_neg ho]
          apply le_trans _ hr
          apply Real.exp_le_exp.mpr
          have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          have hg := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 25) hgain
          have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          nlinarith
      · have ho : ¬ own b := fun ho => hc (hown b ho)
        rw [if_neg ho]
        apply le_of_not_gt
        intro hlt
        exact htest (Or.inr ⟨hc, hlt⟩)
    exact (le_div_iff₀ hmp).mp hthreshold
  have hpos : 0 < ρ.w j * (lawMassOn (D j) (fixedListHitSet E G W)) ^ 2 := by
    have hp' : 0 < (ρ.w j * (lawMassOn (D j) (fixedListHitSet E G W)) ^ 2) /
        squaredClusterMass ρ D (fixedListHitSet E G W) := hp
    exact (div_pos_iff.mp hp').resolve_right (by intro h; linarith [h.2]) |>.1
  have hnonneg (i : Fin q) : 0 ≤
      (if Real.exp (-(3 / 2 : ℝ) * k * r) ≤ lawMassOn (D i) (fixedListHitSet E G W) ∧
        ∀ b, (if own b then Real.exp ((-Real.log 2 + (8 / 100 : ℝ) * gain) * k)
          else Real.exp (-(6 / 5 : ℝ) * k)) *
            lawMassOn (D i) (fixedListHitSetWithout E G W b) ≤
              lawMassOn (D i) (fixedListHitSet E G W)
      then ρ.w i * (lawMassOn (D i) (fixedListHitSet E G W)) ^ 2 else 0) := by
    split_ifs
    · exact mul_nonneg (ρ.nonneg i) (sq_nonneg _)
    · exact le_rfl
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ j))
  rw [if_pos (And.intro habs' hrat')]
  exact hpos

end HypercubeRamsey.Lane_sol_s10_d2
