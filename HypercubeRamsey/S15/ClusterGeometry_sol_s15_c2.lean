import HypercubeRamsey.S15.ClusterRank_sol_s15_c2
import HypercubeRamsey.S15.ClusterNodes_q_s15_c2
import HypercubeRamsey.S15.MaskNumerics_sol_s15_mask

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 OAI.HypercubeRamsey Filter Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem small_entropy_bound : Real.binEntropy (1 / 100000) ≤ (0.001 : ℝ) := by
  let p : ℝ := 1 / 100000
  have hp : 0 < p := by norm_num [p]
  have hp1 : p < 1 := by norm_num [p]
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hlog : Real.log (p⁻¹) ≤ 20 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h20 : (100000 : ℝ) ≤ Real.exp 20 := by
      have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 20
      rw [← Real.exp_nat_mul] at hpow
      norm_num at hpow
      linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100000) h20
    simpa [p] using h
  have hsecond : (1 - p) * Real.log (1 - p)⁻¹ ≤ p := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (inv_pos.mpr hq)) hq.le
    have heq : (1 - p) * ((1 - p)⁻¹ - 1) = p := by field_simp; ring
    exact h.trans_eq heq
  have hfirst : p * Real.log p⁻¹ ≤ p * 20 := mul_le_mul_of_nonneg_left hlog hp.le
  have heq : Real.binEntropy p = p * Real.log p⁻¹ + (1 - p) * Real.log (1 - p)⁻¹ := by
    simp [Real.binEntropy, Real.log_inv]
  rw [heq]
  dsimp [p] at hfirst hsecond ⊢
  linarith only [hfirst, hsecond]

theorem crossing_fraction_parameters (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, 1000000 ≤ T.S.n k ∧
      (T.S.n k : ℝ) ^ (2 * κ.ι) ≤ (T.S.n k : ℝ) / 200000 := by
  have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hι : 2 * κ.ι < 1 := by linarith [hκ.ι_rng.2]
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  have hbound := hn.eventually (Lane_sol_consts_adm.eventually_power_bound (2 * κ.ι) 1 200000 1 hι (by norm_num))
  filter_upwards [hbound, T.S.n_tendsto.eventually_ge_atTop 1000000] with k hk hn
  refine ⟨hn, ?_⟩
  rw [Real.rpow_one, one_mul] at hk
  change 200000 * (T.S.n k : ℝ) ^ (2 * κ.ι) ≤ (T.S.n k : ℝ) at hk
  linarith only [hk]

theorem crossing_near_card_bound {κ : CConsts} (hκ : κ.Admissible) {T : Stage} {k : ℕ}
    (hn : 1000000 ≤ T.S.n k)
    (hnear : (T.S.n k : ℝ) ^ (2 * κ.ι) ≤ (T.S.n k : ℝ) / 200000)
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (i : Fin PT.tiling.m) (y : EvenPosition T k) :
    (((evenPatchPositions PT.tiling i).filter fun x => clusterCrossingNear PT x y).card : ℝ) ≤
      ((evenPatchPositions PT.tiling i).card : ℝ) * clusterCrossingFraction T k := by
  let n : ℝ := T.S.n k
  let ell : ℝ := (PT.tiling.P i).ℓ
  let R : ℕ := ⌊n / 100000⌋₊
  have hnBig : (1000000 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast hn
  have hnpos : 0 < n := by linarith
  have hfloor : (R : ℝ) ≤ n / 100000 := Nat.floor_le (by positivity)
  have hfloorLo : n / 200000 ≤ (R : ℝ) := by
    have h := Nat.lt_floor_add_one (n / 100000)
    dsimp [R]
    linarith only [h, hnBig]
  have hRhalf : R ≤ T.S.n k / 2 := by
    have hdouble : (2 : ℝ) * R ≤ (T.S.n k : ℝ) := by
      change 2 * (R : ℝ) ≤ n
      linarith only [hfloor, hnBig]
    have hNat : 2 * R ≤ T.S.n k := by exact_mod_cast hdouble
    omega
  have hBall := HypercubeRamsey.hammingBall_volume_bound
    (by omega : 0 < T.S.n k) hRhalf y.1
  have harg : (R : ℝ) / n ≤ 1 / 100000 := by
    apply (div_le_iff₀ hnpos).2
    linarith only [hfloor]
  have hEntropy : Real.binEntropy ((R : ℝ) / n) ≤ (0.001 : ℝ) := by
    apply le_trans _ small_entropy_bound
    apply Real.binEntropy_strictMonoOn.monotoneOn
    · exact ⟨by positivity, harg.trans (by norm_num)⟩
    · norm_num
    · exact harg
  have hBallBound : ((HypercubeRamsey.hammingBall y.1 R).card : ℝ) ≤ Real.exp (0.001 * n) :=
    hBall.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hEntropy hnpos.le))
  let A := (evenPatchPositions PT.tiling i).filter fun x => clusterCrossingNear PT x y
  have hsub : A.image Subtype.val ⊆ HypercubeRamsey.hammingBall y.1 R := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hdist : (HypercubeRamsey.hammingDist x.1 y.1 : ℝ) ≤ (R : ℝ) :=
      (Finset.mem_filter.mp hx).2.trans (hnear.trans hfloorLo)
    have hdistNat : HypercubeRamsey.hammingDist x.1 y.1 ≤ R := by exact_mod_cast hdist
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change _root_.hammingDist y.1 x.1 ≤ R
    change _root_.hammingDist x.1 y.1 ≤ R at hdistNat
    rw [_root_.hammingDist_comm]
    exact hdistNat
  have hA : (A.card : ℝ) ≤ Real.exp (0.001 * n) := by
    have hcard : A.card ≤ (HypercubeRamsey.hammingBall y.1 R).card := by
      rw [← Finset.card_image_of_injective A Subtype.val_injective] at *
      exact Finset.card_le_card hsub
    have hcardR : (A.card : ℝ) ≤ (HypercubeRamsey.hammingBall y.1 R).card := by exact_mod_cast hcard
    exact hcardR.trans hBallBound
  have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hι : κ.ι ≤ 1 / 2 := by linarith [hκ.ι_rng.2]
  have hn1 : 1 ≤ n := by linarith
  have hell : ell ≤ Real.sqrt n := by
    calc
      ell ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ) := by
        dsimp [ell]
        exact_mod_cast Nat.le_max_right (PT.tiling.P i).h (PT.tiling.P i).ℓ
      _ ≤ n ^ κ.ι := (hPT.tiling_valid.allocation_bounds i).1.le
      _ ≤ n ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hι
      _ = Real.sqrt n := by rw [Real.sqrt_eq_rpow]
  have hroot : Real.sqrt n ≤ n / 1000 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith only [hnBig]⟩
  have hellSmall : ell ≤ n / 1000 := hell.trans hroot
  have hEllNat : (PT.tiling.P i).ℓ < T.S.n k := by
    have h : ell < n := by linarith only [hellSmall, hnBig]
    dsimp [ell, n] at h
    exact_mod_cast h
  have hScard := Lane_q_s15_c2.evenPatchPositions_card_formula PT i hEllNat
  have hScardR : ((evenPatchPositions PT.tiling i).card : ℝ) =
      Real.exp ((n - ell - 1) * Real.log 2) := by
    have hpow : (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) =
        Real.exp (((T.S.n k - (PT.tiling.P i).ℓ - 1 : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hcast : ((T.S.n k - (PT.tiling.P i).ℓ - 1 : ℕ) : ℝ) = n - ell - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ T.S.n k - (PT.tiling.P i).ℓ),
        Nat.cast_sub hEllNat.le]
      simp [n, ell]
    have hScardR : ((evenPatchPositions PT.tiling i).card : ℝ) =
        (2 : ℝ) ^ (T.S.n k - (PT.tiling.P i).ℓ - 1) := by exact_mod_cast hScard
    exact hScardR.trans (hpow.trans (by rw [hcast]))
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hcost : (ell + 1) * Real.log 2 ≤ 0.009 * n := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by dsimp [ell]; positivity : 0 ≤ ell + 1)
    nlinarith only [hmul, hellSmall, hnBig]
  calc
    _ ≤ Real.exp (0.001 * n) := hA
    _ ≤ Real.exp (0.01 * n - (ell + 1) * Real.log 2) := Real.exp_le_exp.mpr (by linarith only [hcost])
    _ = ((evenPatchPositions PT.tiling i).card : ℝ) * clusterCrossingFraction T k := by
      rw [hScardR, Lane_sol_s15_mask.crossing_fraction_exp, ← Real.exp_add]
      congr 1
      dsimp [n]
      ring

theorem crossing_rank_tail_bound {κ : CConsts} (hκ : κ.Admissible) {T : Stage} {k : ℕ}
    (hn : 1000000 ≤ T.S.n k)
    (hnear : (T.S.n k : ℝ) ^ (2 * κ.ι) ≤ (T.S.n k : ℝ) / 200000)
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (i : Fin PT.tiling.m) (G : Finset (Fin (T.S.n k))) (j : ℕ) :
    clusterCrossingRankTail PT i G j ≤
      ((T.S.n k : ℝ) ^ 2 * clusterCrossingFraction T k) ^ j := by
  let S := evenPatchPositions PT.tiling i
  by_cases hS : S.Nonempty
  · let U := {a : EvenPosition T k // a ∈ S}
    letI : Nonempty U := by obtain ⟨a, ha⟩ := hS; exact ⟨⟨a, ha⟩⟩
    let P : FinLaw U := FinLaw.uniform Finset.univ Finset.univ_nonempty
    let Q := FinLaw.pi (fun _ : Fin (T.S.n k) => P)
    let near : U → U → Prop := fun x y => clusterCrossingNear PT x.1 y.1
    let E := fun vs : Fin (T.S.n k) → U => crossingGraph PT (fun r => (vs r).1) G
    have hcardU : Fintype.card U = S.card := Fintype.card_of_subtype S (fun _ => Iff.rfl)
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    have hprob (y : U) : P.pr (fun x => near x y) ≤ clusterCrossingFraction T k := by
      let A : Finset U := Finset.univ.filter fun x => near x y
      have hsub : A.image Subtype.val ⊆ S.filter fun x => clusterCrossingNear PT x y.1 := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨u.2, (Finset.mem_filter.mp hu).2⟩
      have hcount : (A.card : ℝ) ≤ (S.card : ℝ) * clusterCrossingFraction T k := by
        have hcard : A.card ≤ (S.filter fun x => clusterCrossingNear PT x y.1).card := by
          rw [← Finset.card_image_of_injective A Subtype.val_injective]
          exact Finset.card_le_card hsub
        have hcardR : (A.card : ℝ) ≤ (S.filter fun x => clusterCrossingNear PT x y.1).card := by exact_mod_cast hcard
        exact hcardR.trans (crossing_near_card_bound hκ hn hnear PT hPT i y.1)
      have hPr : P.pr (fun x => near x y) = (A.card : ℝ) / S.card := by
        unfold FinLaw.pr
        simp only [P, FinLaw.uniform, Finset.mem_univ, ↓reduceIte, Finset.card_univ, hcardU]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        change (A.card : ℝ) * (1 / S.card) = _
        ring
      rw [hPr]
      apply (div_le_iff₀ hSpos).2
      simpa only [mul_comm] using hcount
    have hweight (vs : Fin (T.S.n k) → U) : Q.w vs = ((S.card : ℝ) ^ (T.S.n k))⁻¹ := by
      simp [Q, P, FinLaw.pi, FinLaw.uniform, Finset.card_univ, hcardU, one_div, inv_pow]
    have hTail : clusterCrossingRankTail PT i G j = Q.pr
        (fun vs => j ≤ clusterCrossingRank PT (fun r => (vs r).1) G) := by
      rw [Lane_sol_s15_mask.rank_tail_subtype]
      unfold FinLaw.pr
      simp_rw [hweight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro vs hvs
      split_ifs <;> simp [S]
    rw [hTail]
    have hp : 0 ≤ clusterCrossingFraction T k := by unfold clusterCrossingFraction; positivity
    have hbound := rank_probability_le P near (clusterCrossingFraction T k) hp hprob E
      (fun vs u v h => h.2.2.2) (j := j)
    have hRank (vs : Fin (T.S.n k) → U) :
        clusterCrossingRank PT (fun r => (vs r).1) G = T.S.n k -
          (Finset.univ.filter fun v => ∀ w, (E vs).Reachable w v → v ≤ w).card := by
      unfold clusterCrossingRank
      congr 1
      apply congrArg Finset.card
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply forall_congr'
      intro w
      rw [(E vs).reachable_iff_reflTransGen]
      rfl
    simpa only [← hRank] using hbound
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hn0 : T.S.n k ≠ 0 := by omega
    have hcard0 : (evenPatchPositions PT.tiling i).card = 0 := by
      change S.card = 0
      rw [hempty, Finset.card_empty]
    simp only [clusterCrossingRankTail, hcard0, Nat.cast_zero, zero_pow hn0, div_zero]
    exact pow_nonneg (mul_nonneg (sq_nonneg _) (by unfold clusterCrossingFraction; positivity)) _

end HypercubeRamsey.Lane_sol_s15_c2
