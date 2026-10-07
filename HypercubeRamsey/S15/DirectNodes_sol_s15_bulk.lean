import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import HypercubeRamsey.S15.DirectNodes_sol_s15_cross

namespace HypercubeRamsey.Lane_sol_s15_bulk

open HypercubeRamsey S15 S15.Needs Lane_q_s15_direct Filter
open Classical
open scoped BigOperators

set_option maxHeartbeats 400000

/-- The degree surplus pays for almost all of the bulk inverse degree product. -/
theorem inverse_degree_power_bound (n d : ℕ) (g D : ℝ)
    (hn : 0 < n) (hg : 0 < g) (hgn : g ≤ n)
    (hd : (9 / 10 : ℝ) * n ≤ d) (hdn : d ≤ n)
    (hD : 1 / 2 + g / (4 * n) ≤ D) :
    D ^ (-(d : ℝ)) ≤ (2 : ℝ) ^ n * Real.exp (-(9 / 40 : ℝ) * g) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let t := g / (2 * (n : ℝ))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
    nlinarith
  have hlog : t / 2 ≤ Real.log (1 + t) := by
    have hfrac : t / 2 ≤ 2 * t / (t + 2) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity : 0 < t + 2)).2
      nlinarith
    exact hfrac.trans (Real.le_log_one_add_of_nonneg ht)
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hrecip : D⁻¹ ≤ 2 * Real.exp (-g / (4 * (n : ℝ))) := by
    have hlowpos : 0 < (1 / 2 : ℝ) + g / (4 * (n : ℝ)) := by positivity
    have hinv := one_div_le_one_div_of_le hlowpos hD
    have heq : 1 / ((1 / 2 : ℝ) + g / (4 * (n : ℝ))) = 2 / (1 + t) := by
      dsimp [t]
      field_simp
      <;> ring
    rw [heq] at hinv
    have hexp : (1 + t)⁻¹ ≤ Real.exp (-g / (4 * (n : ℝ))) := by
      calc
        (1 + t)⁻¹ = Real.exp (-Real.log (1 + t)) := by
          rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 + t)]
        _ ≤ Real.exp (-g / (4 * (n : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have heq : t / 2 = g / (4 * (n : ℝ)) := by dsimp [t]; ring
          rw [heq] at hlog
          simpa only [neg_div] using neg_le_neg hlog
    calc
      D⁻¹ ≤ 2 / (1 + t) := by simpa [one_div] using hinv
      _ ≤ 2 * Real.exp (-g / (4 * (n : ℝ))) := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 2)
  have hdecay : (9 / 40 : ℝ) * g ≤ (g / (4 * (n : ℝ))) * d := by
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ g / (4 * (n : ℝ)))
    have heq : g / (4 * (n : ℝ)) * (9 / 10 * (n : ℝ)) = 9 / 40 * g := by
      field_simp
      <;> ring
    rwa [heq] at hh
  calc
    D ^ (-(d : ℝ)) = (D⁻¹) ^ d := by rw [Real.rpow_neg hDpos.le, Real.rpow_natCast, inv_pow]
    _ ≤ (2 * Real.exp (-g / (4 * (n : ℝ)))) ^ d := pow_le_pow_left₀ (inv_nonneg.mpr hDpos.le) hrecip d
    _ = (2 : ℝ) ^ d * Real.exp (-(g / (4 * (n : ℝ))) * d) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2 <;> ring
    _ ≤ (2 : ℝ) ^ n * Real.exp (-(9 / 40 : ℝ) * g) := by
      apply mul_le_mul
      · exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hdn
      · exact Real.exp_le_exp.mpr (by nlinarith)
      · positivity
      · positivity

/-- A successful crossing mass leaves an explicitly bounded posterior width. -/
theorem post_crossing_atom_bound {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hmode : PT.tiling.mode = .highDirect) (a : EvenPosition T k)
    (ys : OddAssignment T k) (hcross : 9 / 10 ≤ directCrossingMass PT hPT ys a)
    (hn : 0 < T.S.n k) (hb : 3 * bstar T k ≤ 1 / 4) :
    ∀ x, directPostCrossingWeight PT hPT ys a x ≤
      Real.exp (2 + 2 * (PT.tiling.P (patchAt PT hPT a.1)).ℓ +
        Real.log ((T.S.N k : ℝ) / (PT.tiling.P (patchAt PT hPT a.1)).M)) / T.S.N k := by
  intro x
  let i := patchAt PT hPT a.1
  let M : ℝ := (PT.tiling.P i).M
  let ell := (PT.tiling.P i).ℓ
  have hM : 0 < M := by
    dsimp [M]
    have hh := Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
    rw [(PT.tiling.P i).cardX] at hh
    exact_mod_cast hh
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hm : 0 < directCrossingMass PT hPT ys a := by linarith
  have hbase : directBaseWeight PT hPT a x ≤ 2 / M := by
    have hh := highDirect_scaled_baseweight_le_two PT hPT hmode i a rfl x
    apply (le_div_iff₀ hM).2
    simpa [mul_comm, M] using hh
  have hweight : directPostCrossingWeight PT hPT ys a x ≤
      (2 / M * (4 : ℝ) ^ ell) / (9 / 10) := by
    by_cases hx : x ∈ PT.envelope i
    · have hf := (highDirect_row_factor_bounds PT hPT hmode i a rfl x hx hn ys hb).1
      have hp : (∏ b ∈ crossingNeighbours PT hPT a, directFactor PT hPT a ys b x) ≤ 4 ^ ell := by
        calc
          _ ≤ ∏ b ∈ crossingNeighbours PT hPT a, (4 : ℝ) :=
            Finset.prod_le_prod₀ (fun b hb => (hf b hb).1) (fun b hb => (hf b hb).2)
          _ = (4 : ℝ) ^ (crossingNeighbours PT hPT a).card := by simp
          _ ≤ 4 ^ ell := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 4)
              (highDirect_crossingNeighbours_card_le_prefix PT hPT a i rfl)
      simp only [directPostCrossingWeight, if_pos hm]
      apply div_le_div₀
      · positivity
      · exact mul_le_mul hbase hp (Finset.prod_nonneg fun b _ => directFactor_nonneg PT hPT a ys b x) (by positivity)
      · norm_num
      · exact hcross
    · have hz : directPostCrossingWeight PT hPT ys a x = 0 := by
        simp [directPostCrossingWeight, directBaseWeight, i, hx, hm]
      rw [hz]
      positivity
  have hfour : (4 : ℝ) ^ ell ≤ Real.exp (2 * (ell : ℝ)) := by
    have hl : Real.log (4 : ℝ) ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (ell : ℝ) * Real.log 4 ≤ (ell : ℝ) * 2 := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg ell)
      _ = 2 * (ell : ℝ) := by ring
  have hconst : (20 / 9 : ℝ) ≤ Real.exp 2 := by
    have hh := Real.add_one_le_exp (2 : ℝ)
    linarith
  calc
    directPostCrossingWeight PT hPT ys a x ≤ (2 / M * (4 : ℝ) ^ ell) / (9 / 10) := hweight
    _ = (20 / 9 : ℝ) * (4 : ℝ) ^ ell * ((T.S.N k : ℝ) / M) / T.S.N k := by field_simp <;> ring
    _ ≤ Real.exp 2 * Real.exp (2 * (ell : ℝ)) * Real.exp (Real.log ((T.S.N k : ℝ) / M)) / T.S.N k := by
      rw [Real.exp_log (div_pos hN hM)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul hconst hfour (by positivity) (Real.exp_pos _).le) (by positivity)) hN.le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]


theorem admissible_positive {κ : CConsts} (hκ : κ.Admissible) :
    1 ≤ κ.u ∧ 0 < κ.KB := by
  have hu : 0 < κ.u := lt_of_le_of_lt (Nat.zero_le _) hκ.u_rng.2
  have hP : 1 ≤ κ.P := by
    have hh := hκ.P_big.2
    rw [hκ.Ac_eq] at hh
    omega
  have hR : 1 ≤ κ.R := by rw [hκ.R_eq]; nlinarith
  have hRr : 1 ≤ (κ.R : ℝ) := by exact_mod_cast hR
  constructor
  · omega
  · nlinarith [hκ.KB_big]

/-- The allocation losses are negligible relative to the direct gain. -/
theorem highDirect_numeric_parameters {κ : CConsts} (hκ : κ.Admissible)
    (T : Stage) (Qmin : ℝ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    PT.tiling.mode = .highDirect → ∀ a : EvenPosition T k,
    let i := patchAt PT hPT a.1
    let g : ℝ := (PT.tiling.P i).g
    0 < T.S.n k ∧ 3 * bstar T k ≤ 1 / 4 ∧
    (2 : ℝ) ^ (T.S.n k) ≤ T.S.N k ∧
    1000 ≤ g ∧ g ≤ T.S.n k ∧
    g ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) ∧
    Qmin ≤ (PT.tiling.Q i : ℝ) ∧
    Cstar κ.u κ.ξ * PT.tiling.Q i ≤ g / 10000 ∧
    2 + 2 * (PT.tiling.P i).ℓ + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ g / 100 ∧
    (9 / 10 : ℝ) * T.S.n k ≤ (bulkNeighbours PT hPT a).card ∧
    (bulkNeighbours PT hPT a).card ≤ T.S.n k := by
  obtain ⟨hu, hKB⟩ := admissible_positive hκ
  have hloglim := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hglarge : ∀ᶠ k in atTop,
      max 1000 (2 * Real.sqrt κ.M1 * Qmin) ≤ κ.KB * Real.log (T.S.n k : ℝ) :=
    (hloglim.const_mul_atTop hKB).eventually_ge_atTop _
  have hhost := T.S.eventually_large 1 2
  have hsmall := Lane_q_s15_needs2.eventually_degree_radius_lt_half T 12
  filter_upwards [hglarge, hhost, hsmall] with k hlarge hhost hsmall
  intro PT hPT hmode a
  dsimp only
  let i := patchAt PT hPT a.1
  let g : ℝ := (PT.tiling.P i).g
  let nR : ℝ := T.S.n k
  have hn : 0 < T.S.n k := by omega
  have hn1 : 1 ≤ nR := by dsimp [nR]; exact_mod_cast (show 1 ≤ T.S.n k by omega)
  have hnR : 0 < nR := by linarith
  have hbstar : 3 * bstar T k ≤ 1 / 4 := by linarith
  have hN : (2 : ℝ) ^ (T.S.n k) ≤ T.S.N k := by
    simpa only [one_mul] using hhost.2.1
  have hgain := (hPT.tiling_valid.direct_data (Or.inr hmode) i).2.2.2.2.2.2.mp hmode
  have hg1000 : 1000 ≤ g := by
    have hh := (le_max_left (1000 : ℝ) (2 * Real.sqrt κ.M1 * Qmin)).trans hlarge
    exact hh.trans hgain.le
  have hgpos : 0 < g := by linarith
  have hι : κ.ι / 2 ≤ κ.xs / 4 := by
    have hm : min κ.xs (min κ.η0 0.01) ≤ κ.xs := min_le_left _ _
    linarith [hκ.ι_rng.2, hκ.xs_rng.1]
  have hι1 : κ.ι / 2 ≤ 1 := by linarith [hκ.xs_rng.2]
  have hscale : g ≤ nR ^ (κ.ι / 2) := hPT.tiling_valid.direct_scale_bound (Or.inr hmode) i
  have hgn : g ≤ nR := by
    exact hscale.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hn1 hι1)
  have hgw : g ≤ nR ^ (κ.xs / 4) :=
    hscale.trans (Real.rpow_le_rpow_of_exponent_le hn1 hι)
  have hsqrt : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.2 (by linarith [hκ.M1_big.1])
  have hQ := (hPT.tiling_valid.clique_scales i).2 (Or.inr hmode)
  have hQmin : Qmin ≤ (PT.tiling.Q i : ℝ) := by
    have hh := (le_max_right (1000 : ℝ) (2 * Real.sqrt κ.M1 * Qmin)).trans hlarge
    have hhg : 2 * Real.sqrt κ.M1 * Qmin ≤ g := hh.trans hgain.le
    have hratio : Qmin ≤ g / (2 * Real.sqrt κ.M1) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt κ.M1)).2
      nlinarith
    exact hratio.trans hQ.2.1.le
  have hCpos : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
  have hCQ : Cstar κ.u κ.ξ * PT.tiling.Q i ≤ g / 10000 := by
    calc
      _ ≤ Cstar κ.u κ.ξ * (2 * g / Real.sqrt κ.M1) :=
        mul_le_mul_of_nonneg_left hQ.2.2.1 hCpos
      _ = (2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1) * g := by ring
      _ ≤ (1e-4 : ℝ) * g := mul_le_mul_of_nonneg_right hκ.M1_big.2 hgpos.le
      _ = g / 10000 := by ring
  have halloc := (hPT.tiling_valid.allocation_bounds i).2
  have hnot : PT.tiling.mode ≠ .bounded := by simp [hmode]
  have hgainEq : PT.tiling.gain i = g / 1000 := by simp [Tiling.gain, hmode, g]
  have ha := halloc.resolve_left hnot
  rw [hgainEq] at ha
  have huR : 1 ≤ (κ.u : ℝ) := by exact_mod_cast hu
  have hden : 0 < (1000000 : ℝ) * κ.u := by positivity
  have hell : ((PT.tiling.P i).ℓ : ℝ) ≤ g / 1000000 := by
    have hh : ((PT.tiling.P i).ℓ : ℝ) ≤ g / (1000000 * κ.u) := by
      convert ha.1 using 1 <;> ring
    exact hh.trans (by
      apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 1000000)).2
      nlinarith)
  have hlog : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ g / 1000000 := by
    have hh : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ g / (1000000 * κ.u) := by
      convert ha.2 using 1 <;> ring
    exact hh.trans (by
      apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 1000000)).2
      nlinarith)
  have hA : 2 + 2 * (PT.tiling.P i).ℓ + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ g / 100 := by
    nlinarith
  have hellNat : (PT.tiling.P i).ℓ ≤ T.S.n k := by
    have hh : ((PT.tiling.P i).ℓ : ℝ) ≤ (T.S.n k : ℝ) := by nlinarith
    exact_mod_cast hh
  have hbNat := directBulkNeighbours_card_lower PT hPT a i rfl
  -- Cast natural subtraction explicitly before the linear arithmetic step.
  have hbLower : (9 / 10 : ℝ) * T.S.n k ≤ (bulkNeighbours PT hPT a).card := by
    have hh : ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) = nR - ((PT.tiling.P i).ℓ : ℝ) := by
      simp [Nat.cast_sub hellNat, nR]
    have hbCast : ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) ≤ (bulkNeighbours PT hPT a).card := by exact_mod_cast hbNat
    rw [hh] at hbCast
    nlinarith
  have hbUpper : (bulkNeighbours PT hPT a).card ≤ T.S.n k := by
    calc
      _ ≤ (star a).card := Finset.card_le_card (by
        intro b hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩)
      _ = _ := star_card_eq_dimension a
  exact ⟨hn, hbstar, hN, hg1000, hgn, hgw, hQmin, hCQ, hA, hbLower, hbUpper⟩


/-- The complete homogeneous-tail hypotheses of a crossing-conditioned direct row. -/
theorem highDirect_bulk_inputs {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (Qmin : ℝ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    PT.tiling.mode = .highDirect → ∀ a : EvenPosition T k,
    ∀ ys : OddAssignment T k, ∀ hc : 9 / 10 ≤ directCrossingMass PT hPT ys a,
    let i := patchAt PT hPT a.1
    let τ := directPostCrossingLaw PT hPT ys a (by linarith)
    let Γ := Real.exp (-200 * PT.tiling.gain i)
    τ.SupportedIn (T.X k) ∧ (PT.π i).SupportedIn (T.Y k) ∧
    τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) ∧
    (PT.π i).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) ∧
    (∀ x, x ∉ PT.envelope i → τ.w x = 0) ∧
    (bulkNeighbours PT hPT a).card ≤ T.S.n k ∧
    Qmin ≤ (PT.tiling.Q i : ℝ) ∧ 0 ≤ Γ ∧ Γ < 1 ∧
    (∀ x ∈ PT.envelope i, τ.w x *
      (deg (T.S.E k) PT.tiling.c (PT.π i).w x) ^ (-((bulkNeighbours PT hPT a).card : ℝ)) *
      Real.exp (Cstar κ.u κ.ξ * PT.tiling.Q i) ≤ Γ) := by
  filter_upwards [highDirect_numeric_parameters hκ T Qmin] with k hnum
  intro PT hPT hmode a ys hc
  let i := patchAt PT hPT a.1
  let g : ℝ := (PT.tiling.P i).g
  let τ := directPostCrossingLaw PT hPT ys a (by linarith : 0 < directCrossingMass PT hPT ys a)
  let Γ := Real.exp (-200 * PT.tiling.gain i)
  obtain ⟨hn, hb, hNpow, hg1000, hgn, hgw, hQ, hCQ, hA, hdlo, hdhi⟩ := hnum PT hPT hmode a
  have hgpos : 0 < g := by change 1000 ≤ g at hg1000; linarith
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    have hh := Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
    rw [(PT.tiling.P i).cardX] at hh
    exact_mod_cast hh
  have hτSp : ∀ x, x ∉ PT.envelope i → τ.w x = 0 := by
    intro x hx
    by_contra hne
    exact hx (directPostCrossingLaw_supported PT hPT ys a _ x hne)
  have hτX : τ.SupportedIn (T.X k) := by
    intro x hx
    apply hτSp x
    intro hxSp
    exact hx ((Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1
      ((hPT.tiling_valid.patch_supports i).1 (hPT.envelope_subset i hxSp)))).1)
  have hπY : (PT.π i).SupportedIn (T.Y k) := by
    intro y hy
    apply hPT.law_supported i y
    intro hyP
    exact hy ((Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.2.2
      ((hPT.tiling_valid.patch_supports i).2.2.1 hyP))).1)
  have hτatom : ∀ x, τ.w x ≤ Real.exp (g / 100) / T.S.N k := by
    intro x
    have hh := post_crossing_atom_bound PT hPT hmode a ys hc hn hb x
    exact hh.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hA) hN.le)
  have hτwidth : τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
    intro x
    exact (hτatom x).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (by change g ≤ _ at hgw; linarith)) hN.le)
  have hπwidth : (PT.π i).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
    intro y
    have h11 : (11 : ℝ) ≤ Real.exp 4 := by
      have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        (11 : ℝ) ≤ 2 ^ (4 : ℕ) := by norm_num
        _ ≤ (Real.exp 1) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hh 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    have hlog : 4 + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ g := by
      have hell0 : (0 : ℝ) ≤ (PT.tiling.P i).ℓ := Nat.cast_nonneg _
      change 2 + 2 * (PT.tiling.P i).ℓ + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ g / 100 at hA
      nlinarith
    calc
      (PT.π i).w y ≤ 11 / (PT.tiling.P i).M := hPT.law_cap i y
      _ ≤ Real.exp 4 / (PT.tiling.P i).M := div_le_div_of_nonneg_right h11 hM.le
      _ = Real.exp (4 + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) / T.S.N k := by
        rw [Real.exp_add, Real.exp_log (div_pos hN hM)]
        field_simp
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) / T.S.N k :=
        div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (hlog.trans hgw)) hN.le
  have hgain : -200 * PT.tiling.gain i = -g / 5 := by simp [Tiling.gain, hmode, g]; ring
  have hΓ0 : 0 ≤ Γ := (Real.exp_pos _).le
  have hΓ1 : Γ < 1 := by
    dsimp [Γ]
    rw [hgain]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hbudget (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope i) :
      τ.w x * (deg (T.S.E k) PT.tiling.c (PT.π i).w x) ^
        (-((bulkNeighbours PT hPT a).card : ℝ)) *
        Real.exp (Cstar κ.u κ.ξ * PT.tiling.Q i) ≤ Γ := by
    have hOwn := hPT.envelope_degree i x hx
    have hD : 1 / 2 + g / (4 * (T.S.n k : ℝ)) ≤
        deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
      have hh := hOwn
      simp [OwnDegOK, hmode] at hh
      simpa [g] using hh.1
    have hDp : 0 < deg (T.S.E k) PT.tiling.c (PT.π i).w x := lt_of_lt_of_le (by positivity) hD
    have hpower := inverse_degree_power_bound (T.S.n k) (bulkNeighbours PT hPT a).card
      g (deg (T.S.E k) PT.tiling.c (PT.π i).w x) hn hgpos hgn hdlo hdhi hD
    have hratio : (2 : ℝ) ^ (T.S.n k) / T.S.N k ≤ 1 := (div_le_one hN).2 hNpow
    calc
      _ ≤ (Real.exp (g / 100) / T.S.N k) *
          ((2 : ℝ) ^ (T.S.n k) * Real.exp (-(9 / 40 : ℝ) * g)) *
          Real.exp (g / 10000) := by
        apply mul_le_mul
        · exact mul_le_mul (hτatom x) hpower (Real.rpow_nonneg hDp.le _) (by positivity)
        · exact Real.exp_le_exp.mpr hCQ
        · positivity
        · positivity
      _ = ((2 : ℝ) ^ (T.S.n k) / T.S.N k) *
          (Real.exp (g / 100) * Real.exp (-(9 / 40 : ℝ) * g) * Real.exp (g / 10000)) := by ring
      _ ≤ Real.exp (g / 100) * Real.exp (-(9 / 40 : ℝ) * g) * Real.exp (g / 10000) := by
        simpa using mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ Real.exp (g / 100) * Real.exp (-(9 / 40 : ℝ) * g) * Real.exp (g / 10000))
      _ ≤ Γ := by
        rw [← Real.exp_add, ← Real.exp_add]
        dsimp [Γ]
        rw [hgain]
        exact Real.exp_le_exp.mpr (by nlinarith)
  exact ⟨hτX, hπY, hτwidth, hπwidth, hτSp, hdhi, hQ, hΓ0, hΓ1, hbudget⟩


/-- Split a finite product expectation into two coordinate sets. -/
theorem product_expect_split {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinLaw Ω) (s : Finset ι) (F : (ι → Ω) → ℝ) :
    (FinLaw.pi P).E F =
      ∑ u : s → Ω, ∑ v : {i // i ∉ s} → Ω,
        (∏ i : s, (P i.1).w (u i)) *
          (∏ i : {i // i ∉ s}, (P i.1).w (v i)) *
          F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => Ω)).symm (u,v)) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ => Ω)
  have split (ω : ι → Ω) :
      (∏ i, (P i).w (ω i)) = (∏ i : s, (P i.1).w (ω i.1)) *
        (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
    let f := fun i => (P i).w (ω i)
    have hs : (∏ i : s, f i.1) = ∏ i ∈ s, f i := by
      rw [Finset.univ_eq_attach, Finset.prod_attach]
    let t := Finset.univ.filter (fun i : ι => i ∉ s)
    let ec : {i // i ∉ s} ≃ t := {
      toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
      invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
    have ht : (∏ i : {i // i ∉ s}, f i.1) = ∏ i ∈ t, f i := by
      calc
        _ = ∏ i : t, f i.1 := Fintype.prod_equiv ec _ _ (fun _ => rfl)
        _ = _ := by rw [Finset.univ_eq_attach, Finset.prod_attach]
    rw [hs, ht]
    simpa [t] using (Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i : ι => i ∈ s) f).symm
  change (∑ ω, (∏ i, (P i).w (ω i)) * F ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * F ω), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  rw [split]
  have hleft (b : s) : e.symm (u,v) b.1 = u b := by
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, b.2]
  have hright (b : {i // i ∉ s}) : e.symm (u,v) b.1 = v b := by
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, b.2]
  simp_rw [hleft, hright]
  rfl

/-- A uniform bound on every complement-conditioned event integrates unchanged. -/
theorem product_event_bound {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (P : ι → FinLaw Ω) (s : Finset ι) (A : (ι → Ω) → Prop) (B : ℝ)
    (hB : 0 ≤ B)
    (hcond : ∀ v : {i // i ∉ s} → Ω,
      (∑ u : s → Ω, if A ((Equiv.piEquivPiSubtypeProd
          (fun i => i ∈ s) (fun _ => Ω)).symm (u,v))
        then ∏ i : s, (P i.1).w (u i) else 0) ≤ B) :
    (FinLaw.pi P).pr A ≤ B := by
  have hpr : (FinLaw.pi P).pr A = (FinLaw.pi P).E (fun ω => if A ω then 1 else 0) := by
    unfold FinLaw.pr FinLaw.E
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : A ω <;> simp [h]
  rw [hpr, product_expect_split, Finset.sum_comm]
  calc
    _ = ∑ v : {i // i ∉ s} → Ω, (∏ i : {i // i ∉ s}, (P i.1).w (v i)) *
        ∑ u : s → Ω, if A ((Equiv.piEquivPiSubtypeProd
          (fun i => i ∈ s) (fun _ => Ω)).symm (u,v))
        then ∏ i : s, (P i.1).w (u i) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs <;> ring
    _ ≤ ∑ v : {i // i ∉ s} → Ω, (∏ i : {i // i ∉ s}, (P i.1).w (v i)) * B := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (hcond v) (Finset.prod_nonneg fun i _ => (P i.1).nonneg _)
    _ = B := by
      rw [← Finset.sum_mul]
      have hh := (FinLaw.pi (fun i : {i // i ∉ s} => P i.1)).sum_one
      simpa [FinLaw.pi] using congrArg (fun x : ℝ => x * B) hh


/-- Integrate a uniform homogeneous bulk tail over all crossing assignments. -/
theorem bulk_probability_of_conditioned_tails {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (B : ℝ) (hB : 0 ≤ B)
    (hTail : ∀ ys : OddAssignment T k, 9 / 10 ≤ directCrossingMass PT hPT ys a →
      (∑ zs : Fin (bulkNeighbours PT hPT a).card → Fin (T.S.N k),
        if Zmass (T.S.E k) PT.tiling.c (directPostCrossingWeight PT hPT ys a)
          (fun _ => (PT.π (patchAt PT hPT a.1)).w) zs < 3 / 4
        then ∏ l, (PT.π (patchAt PT hPT a.1)).w (zs l) else 0) ≤ B) :
    (directRawLaw PT hPT).pr (fun ys => 9 / 10 ≤ directCrossingMass PT hPT ys a ∧
      directBulkMass PT hPT ys a < 3 / 4) ≤ B := by
  let s := bulkNeighbours PT hPT a
  let i := patchAt PT hPT a.1
  let combine := (Equiv.piEquivPiSubtypeProd (fun b : OddPosition T k => b ∈ s)
    (fun _ => Fin (T.S.N k))).symm
  apply product_event_bound (fun b => lawToFinLaw (lawAtOdd PT hPT b)) s _ B hB
  intro v
  suffices hlocal : (∑ u : s → Fin (T.S.N k),
    if 9 / 10 ≤ directCrossingMass PT hPT (combine (u,v)) a ∧
      directBulkMass PT hPT (combine (u,v)) a < 3 / 4
    then ∏ b : s, (lawToFinLaw (lawAtOdd PT hPT b.1)).w (u b) else 0) ≤ B by
    convert hlocal using 1
    apply Finset.sum_congr rfl
    intro u hu
    simp only [combine]
    split_ifs <;> rfl
  let u0 : s → Fin (T.S.N k) := fun _ => ⟨0, T.S.N_pos k⟩
  let ys0 : OddAssignment T k := combine (u0,v)
  have hcross (u : s → Fin (T.S.N k)) :
      directCrossingMass PT hPT (combine (u,v)) a = directCrossingMass PT hPT ys0 a := by
    unfold directCrossingMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    have hbnot : b ∉ s := fun hbs =>
      (Finset.disjoint_left.mp (direct_neighbor_sets_disjoint PT hPT a)) hb hbs
    simp [directFactor, combine, ys0, Equiv.piEquivPiSubtypeProd_symm_apply, hbnot]
  have hpost (u : s → Fin (T.S.N k)) (x : Fin (T.S.N k)) :
      directPostCrossingWeight PT hPT (combine (u,v)) a x =
        directPostCrossingWeight PT hPT ys0 a x := by
    have hp : (∏ b ∈ crossingNeighbours PT hPT a, directFactor PT hPT a (combine (u,v)) b x) =
        ∏ b ∈ crossingNeighbours PT hPT a, directFactor PT hPT a ys0 b x := by
      apply Finset.prod_congr rfl
      intro b hb
      have hbnot : b ∉ s := fun hbs =>
        (Finset.disjoint_left.mp (direct_neighbor_sets_disjoint PT hPT a)) hb hbs
      simp [directFactor, combine, ys0, Equiv.piEquivPiSubtypeProd_symm_apply, hbnot]
    simp only [directPostCrossingWeight, hcross u, hp]
  have hlaw (b : s) : lawAtOdd PT hPT b.1 = PT.π i := by
    have hh := (Finset.mem_filter.mp b.2).2.2
    simp [lawAtOdd, i, hh]
  by_cases hc : 9 / 10 ≤ directCrossingMass PT hPT ys0 a
  · let e : Fin s.card ≃ s := s.equivFin.symm
    let ef := Equiv.arrowCongr e (Equiv.refl (Fin (T.S.N k)))
    have hbulk (zs : Fin s.card → Fin (T.S.N k)) :
        directBulkMass PT hPT (combine (ef zs,v)) a =
          Zmass (T.S.E k) PT.tiling.c (directPostCrossingWeight PT hPT ys0 a)
            (fun _ => (PT.π i).w) zs := by
      rw [directBulkMass_eq_centered_product PT hPT a _ (PT.π i) (fun b hb => hlaw ⟨b,hb⟩)]
      unfold Zmass
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpost]
      congr 1
      calc
        (∏ b ∈ s, (1 + acoef (T.S.E k) PT.tiling.c (PT.π i).w x (combine (ef zs,v) b))) =
            ∏ b : s, (1 + acoef (T.S.E k) PT.tiling.c (PT.π i).w x (ef zs b)) := by
          rw [Finset.univ_eq_attach]
          have hh (b : s) : combine (ef zs,v) b.1 = ef zs b := by
            simp [combine, Equiv.piEquivPiSubtypeProd_symm_apply, b.2]
          simp_rw [← hh]
          exact (Finset.prod_attach s _).symm
        _ = ∏ l : Fin s.card, (1 + acoef (T.S.E k) PT.tiling.c (PT.π i).w x (zs l)) := by
          rw [← Equiv.prod_comp e]
          simp [ef, Equiv.arrowCongr]
    have hprod (zs : Fin s.card → Fin (T.S.N k)) :
        (∏ b : s, (lawToFinLaw (lawAtOdd PT hPT b.1)).w (ef zs b)) =
          ∏ l, (PT.π i).w (zs l) := by
      simp only [lawToFinLaw, hlaw]
      rw [← Equiv.prod_comp e]
      simp [ef, Equiv.arrowCongr]
    rw [← Equiv.sum_comp ef]
    calc
      _ = ∑ zs : Fin s.card → Fin (T.S.N k),
          if Zmass (T.S.E k) PT.tiling.c (directPostCrossingWeight PT hPT ys0 a)
            (fun _ => (PT.π i).w) zs < 3 / 4
          then ∏ l, (PT.π i).w (zs l) else 0 := by
        apply Finset.sum_congr rfl
        intro zs hzs
        rw [hcross, hbulk, hprod]
        simp [hc]
      _ ≤ B := hTail ys0 hc
  · have hz : (∑ u : s → Fin (T.S.N k),
        if 9 / 10 ≤ directCrossingMass PT hPT (combine (u,v)) a ∧
          directBulkMass PT hPT (combine (u,v)) a < 3 / 4
        then ∏ b : s, (lawToFinLaw (lawAtOdd PT hPT b.1)).w (u b) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      simp [hcross, hc]
    rw [hz]
    exact hB


/-- The high-direct bulk estimate from the homogeneous tail and finite conditioning. -/
theorem bulk_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∃ Cbulk : ℝ, 0 < Cbulk ∧
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    PT.tiling.mode = .highDirect → ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys => 9 / 10 ≤ directCrossingMass PT hPT ys a ∧
        directBulkMass PT hPT ys a < 3 / 4) ≤
      4 ^ κ.u * ((T.S.n k : ℝ) ^ (-((3 * κ.R : ℕ) : ℝ)) +
        Cbulk * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1))) := by
  have hcores := fun c : Colour => homogeneous_lower_tail κ hκ T hDeep c 1 (by norm_num)
  choose Cu Qmin hCu hQmin hTail using hcores
  let Cbulk := max (Cu false) (Cu true)
  let Qmax := max (Qmin false) (Qmin true)
  have hCuLe (c : Colour) : Cu c ≤ Cbulk := by cases c <;> simp [Cbulk]
  have hQLe (c : Colour) : Qmin c ≤ Qmax := by cases c <;> simp [Qmax]
  have hCpos : 0 < Cbulk := lt_of_lt_of_le (hCu false) (hCuLe false)
  refine ⟨Cbulk, hCpos, ?_⟩
  filter_upwards [Filter.eventually_all.2 hTail, highDirect_bulk_inputs hκ T Qmax,
    highDirect_own_degree_gate hκ T] with k hkTail hkInputs hkGate
  intro PT hPT hmode a
  let i := patchAt PT hPT a.1
  let Γ := Real.exp (-200 * PT.tiling.gain i)
  let B := (4 : ℝ) ^ κ.u * ((T.S.n k : ℝ) ^ (-((3 * κ.R : ℕ) : ℝ)) + Cbulk * Γ)
  have hB : 0 ≤ B := by dsimp [B, Γ]; positivity
  apply bulk_probability_of_conditioned_tails PT hPT a B hB
  intro ys hc
  let τ := directPostCrossingLaw PT hPT ys a (by linarith : 0 < directCrossingMass PT hPT ys a)
  obtain ⟨hτX, hπY, hτw, hπw, hτSp, hd, hQ, hΓ0, hΓ1, hbudget⟩ :=
    hkInputs PT hPT hmode a ys hc
  have htail := hkTail PT.tiling.c (bulkNeighbours PT hPT a).card hd τ (PT.π i)
    (PT.envelope i) (PT.tiling.Q i) Γ (3 / 4)
    hτX hπY hτw hπw hτSp ((hQLe PT.tiling.c).trans hQ)
    (highDirect_envelope_noClique PT hPT hmode i) hΓ0 hΓ1 hbudget
    (by norm_num) (by norm_num) (by
      intro x hx
      simpa [DegGate] using hkGate PT hPT hmode i x hx)
  have hp' : ((1 : ℝ) - 3 / 4) ^ (-(κ.u : ℝ)) = (4 : ℝ) ^ κ.u := by
    have hquarter : (1 : ℝ) - 3 / 4 = (4 : ℝ)⁻¹ := by norm_num
    rw [hquarter, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹), Real.rpow_natCast, ← inv_pow]
    simp
  rw [hp'] at htail
  calc
    _ ≤ (4 : ℝ) ^ κ.u * ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + Cu PT.tiling.c * Γ) := htail
    _ ≤ B := by
      dsimp [B]
      have hexp := mul_le_mul_of_nonneg_right (hCuLe PT.tiling.c) hΓ0
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (4 : ℝ) ^ κ.u)
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Γ] using
        add_le_add_right hexp ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))))


/-- The direct high-gain condition makes the bulk error smaller than half the mass budget. -/
theorem bulk_error_half (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
    PT.tiling.mode = .highDirect → ∀ i : Fin PT.tiling.m,
      (4 : ℝ) ^ κ.u * ((T.S.n k : ℝ) ^ (-((3 * κ.R : ℕ) : ℝ)) +
        C * Real.exp (-200 * PT.tiling.gain i)) ≤
      (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) / 2 := by
  have hP : 1 ≤ κ.P := by
    have hh := hκ.P_big.2
    rw [hκ.Ac_eq] at hh
    omega
  have hR : (0 : ℝ) < κ.R := by
    have hh : 1 ≤ κ.R := by rw [hκ.R_eq]; nlinarith
    exact_mod_cast (show 0 < κ.R by omega)
  have hnlim := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hlarge : ∀ᶠ k in atTop, 2 * (4 : ℝ) ^ κ.u * (1 + C) ≤
      (T.S.n k : ℝ) ^ (2 * (κ.R : ℝ)) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 * (κ.R : ℝ))).comp hnlim).eventually_ge_atTop _
  filter_upwards [hlarge, hnlim.eventually_ge_atTop 1] with k hlarge hn1
  intro PT hPT hm i
  let n : ℝ := T.S.n k
  change (1 : ℝ) ≤ n at hn1
  have hn : 0 < n := by linarith
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hg := (hPT.tiling_valid.direct_data (Or.inr hm) i).2.2.2.2.2.2.mp hm
  have hcoef : 3 * (κ.R : ℝ) ≤ κ.KB / 5 := by nlinarith [hκ.KB_big]
  have hgain : -200 * PT.tiling.gain i = -((PT.tiling.P i).g : ℝ) / 5 := by simp [Tiling.gain, hm]; ring
  have hdecay : Real.exp (-200 * PT.tiling.gain i) ≤ n ^ (-(3 * (κ.R : ℝ))) := by
    rw [hgain, Real.rpow_def_of_pos hn]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hcoef hl
    change κ.KB * Real.log n < ((PT.tiling.P i).g : ℝ) at hg
    nlinarith
  have hbudget : (4 : ℝ) ^ κ.u * (1 + C) * n ^ (-(3 * (κ.R : ℝ))) ≤
      n ^ (-(κ.R : ℝ)) / 2 := by
    have hh := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hn.le (-(3 * (κ.R : ℝ))))
    have heq : n ^ (2 * (κ.R : ℝ)) * n ^ (-(3 * (κ.R : ℝ))) = n ^ (-(κ.R : ℝ)) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    change 2 * (4 : ℝ) ^ κ.u * (1 + C) * n ^ (-(3 * (κ.R : ℝ))) ≤
      n ^ (2 * (κ.R : ℝ)) * n ^ (-(3 * (κ.R : ℝ))) at hh
    rw [heq] at hh
    linarith
  calc
    _ ≤ (4 : ℝ) ^ κ.u * (n ^ (-(3 * (κ.R : ℝ))) + C * n ^ (-(3 * (κ.R : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (4 : ℝ) ^ κ.u)
      have hh := mul_le_mul_of_nonneg_left hdecay hC.le
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using add_le_add_right hh (n ^ (-(3 * (κ.R : ℝ))))
    _ = (4 : ℝ) ^ κ.u * (1 + C) * n ^ (-(3 * (κ.R : ℝ))) := by ring
    _ ≤ _ := hbudget

/-- Exponential crossing errors leave half of the mass budget unused. -/
theorem crossing_error_half (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop,
      8 * (T.S.n k : ℝ) ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) / 2 := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hlim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((κ.R : ℝ) + 2)
    (κ.α / 2) (by positivity [hκ.α_rng.1])).const_mul 8).comp hn
  have ht := hlim.eventually (Iic_mem_nhds (show 8 * (0 : ℝ) < 1 / 2 by norm_num))
  filter_upwards [ht, hn.eventually_ge_atTop 1] with k ht hk
  change (1 : ℝ) ≤ (T.S.n k : ℝ) at hk
  have hpos : (0 : ℝ) < T.S.n k := by linarith
  have hh := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hpos.le (-(κ.R : ℝ)))
  have he : (T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) * (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) =
      (T.S.n k : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hneg : -(κ.α / 2) * (T.S.n k : ℝ) = -κ.α * T.S.n k / 2 := by ring
  dsimp at hh
  rw [hneg] at hh
  have hswap : 8 * ((T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) *
      Real.exp (-κ.α * T.S.n k / 2)) * (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) =
      8 * ((T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) * (T.S.n k : ℝ) ^ (-(κ.R : ℝ))) *
        Real.exp (-κ.α * T.S.n k / 2) := by ring
  rw [hswap, he] at hh
  convert hh using 1 <;> ring

open Lane_sol_s15_cross

section CrossingData
variable {κ : CConsts} {T : Stage} {k : ℕ}
theorem highDirect_envelope_nonempty (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (i : Fin PT.tiling.m) : (PT.envelope i).Nonempty := by
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hsize := Lane_q_s15_direct.highDirect_envelope_card_lower PT hPT hm i
  apply Finset.card_pos.mp
  have hsizeR : ((PT.tiling.P i).M : ℝ) / 2 ≤ ((PT.envelope i).card : ℝ) := hsize
  exact_mod_cast (show (0 : ℝ) < (PT.envelope i).card by linarith)

noncomputable def directBaseLaw (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (a : S15.EvenPosition T k) : Law (T.S.N k) :=
  FinProb.uniform (PT.envelope (S15.patchAt PT hPT a.1))
    (highDirect_envelope_nonempty PT hPT hm _)

theorem directBaseLaw_w (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (a : S15.EvenPosition T k) (x : Fin (T.S.N k)) :
    (directBaseLaw PT hPT hm a).w x = S15.directBaseWeight PT hPT a x := rfl

theorem law_width_of_cap {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (P : Law N) {C v : ℝ} (hC : 0 < C)
    (hcap : ∀ x, (M : ℝ) * P.w x ≤ C)
    (hlog : Real.log ((N : ℝ) / M) ≤ v) : P.WidthLE (Real.log C + v) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  intro x
  calc
    P.w x ≤ C / M := (le_div_iff₀ hMR).2 (by simpa [mul_comm] using hcap x)
    _ = Real.exp (Real.log C + Real.log ((N : ℝ) / M)) / N := by
      rw [Real.exp_add, Real.exp_log hC, Real.exp_log (div_pos hNR hMR)]
      field_simp
    _ ≤ Real.exp (Real.log C + v) / N :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hNR.le

theorem direct_patch_log_width (hκ : κ.Admissible) (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (hn : 1 ≤ (T.S.n k : ℝ)) (i : Fin PT.tiling.m) :
    Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ (T.S.n k : ℝ) ^ κ.ι := by
  have hu : (1 : ℝ) ≤ κ.u := by exact_mod_cast (show 1 ≤ κ.u by have := hκ.u_rng.2; omega)
  rcases (hPT.tiling_valid.allocation_bounds i).2 with hb | ⟨_, hlog⟩
  · rw [hm] at hb; cases hb
  have hg := hPT.tiling_valid.direct_scale_bound (Or.inr hm) i
  have hpow := Real.rpow_le_rpow_of_exponent_le hn (show κ.ι / 2 ≤ κ.ι by linarith [hκ.ι_rng.1])
  have hgain : PT.tiling.gain i ≤ (T.S.n k : ℝ) ^ κ.ι := by
    simp only [Tiling.gain, hm]
    have hg0 : (0 : ℝ) ≤ (PT.tiling.P i).g := by positivity
    linarith
  have hgain0 : 0 ≤ PT.tiling.gain i := by simp [Tiling.gain, hm]; positivity
  have hdiv : PT.tiling.gain i / (1000 * (κ.u : ℝ)) ≤ PT.tiling.gain i := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (κ.u : ℝ))).2
    nlinarith
  exact hlog.trans (hdiv.trans hgain)

theorem exp_window_abs {r ℓ : ℕ} {b M : ℝ} (hb : 0 ≤ b) (hr : r ≤ ℓ)
    (hlo : Real.exp (-10 * r * b) ≤ M) (hhi : M ≤ Real.exp (10 * r * b)) :
    |M - 1| ≤ Real.exp (20 * ℓ * b) - 1 := by
  have harg : 10 * (r : ℝ) * b ≤ 20 * (ℓ : ℝ) * b := by
    have hc : (r : ℝ) ≤ ℓ := by exact_mod_cast hr
    have hm := mul_le_mul_of_nonneg_right hc hb
    nlinarith [show (0 : ℝ) ≤ ℓ by positivity]
  have he := Real.exp_le_exp.mpr harg
  have ha := Real.add_one_le_exp (10 * (r : ℝ) * b)
  have hb' := Real.add_one_le_exp (-10 * (r : ℝ) * b)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def directExperiment (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highDirect) (a : S15.EvenPosition T k) :
    CrossingExperiment T k (S15.OddPosition T k) (fun _ => Fin (T.S.N k)) where
  P := S15.lawAtOdd PT hPT
  label := fun _ y => y
  ν := S15.lawAtOdd PT hPT
  marginal := by
    intro b
    apply FinProb.ext
    intro y
    simp [FinProb.map]
  c := PT.tiling.c
  C := S15.crossingNeighbours PT hPT a
  μ := fun _ => directBaseLaw PT hPT hm a
  A := fun _ => True
  μ_update := by intros; rfl
  A_update := by intros; rfl

 theorem crossing_parameters (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) ∧ bstar T k ≤ 1 / 100 ∧
      20 * (T.S.n k : ℝ) ^ κ.ι ≤ (T.S.n k : ℝ) ^ κ.xs ∧
      20 * (T.S.n k : ℝ) ^ κ.ι ≤ κ.α * T.S.n k / 2 ∧
      8 * (T.S.n k : ℝ) ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := by
  have hn := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hιxs : κ.ι < κ.xs := by
    have hi := hκ.ι_rng.2
    have hm := min_le_left κ.xs (min κ.η0 (0.01 : ℝ))
    linarith [hκ.xs_rng.1]
  have hι1 : κ.ι < 1 := by linarith [hκ.xs_rng.2]
  have hs := hn.eventually (Lane_sol_consts_adm.eventually_power_bound κ.ι κ.xs 20 1 hιxs (by norm_num))
  have hl := hn.eventually (Lane_sol_consts_adm.eventually_power_bound κ.ι 1 20 (κ.α / 2) hι1 (by positivity [hκ.α_rng.1]))
  have hblim : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (show (0 : ℝ) < 0.96 by norm_num)).comp hn using 1
    funext k
    norm_num [bstar]
  have hb := hblim.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  have htailim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((κ.R : ℝ) + 2)
    (κ.α / 2) (by positivity [hκ.α_rng.1])).const_mul 8).comp hn
  have ht := htailim.eventually (Iic_mem_nhds (show 8 * (0 : ℝ) < 1 by norm_num))
  filter_upwards [hn.eventually (eventually_ge_atTop 1), hs, hl, hb, ht] with k hk hs hl hb ht
  change 1 ≤ (T.S.n k : ℝ) at hk
  refine ⟨hk, hb, by simpa using hs, by simpa [Real.rpow_one, div_mul_eq_mul_div] using hl, ?_⟩
  have hpos : (0 : ℝ) < T.S.n k := by linarith
  have hmul := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hpos.le (-(κ.R : ℝ)))
  have he : (T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) * (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) =
      (T.S.n k : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hneg : -(κ.α / 2) * (T.S.n k : ℝ) = -κ.α * T.S.n k / 2 := by ring
  dsimp at hmul
  rw [hneg] at hmul
  calc
    8 * (T.S.n k : ℝ) ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) =
        (8 * ((T.S.n k : ℝ) ^ ((κ.R : ℝ) + 2) * Real.exp (-κ.α * T.S.n k / 2))) *
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := by rw [← he]; ring
    _ ≤ 1 * (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) := hmul
    _ = _ := one_mul _

end CrossingData

open Lane_sol_s15_cross

theorem sharp_direct_crossing_bound (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highDirect, ∀ a : S15.EvenPosition T k,
        (S15.directRawLaw PT hPT).pr (fun ys =>
          |S15.directCrossingMass PT hPT ys a - 1| >
            Real.exp (20 * (PT.tiling.P (S15.patchAt PT hPT a.1)).ℓ * bstar T k) - 1) ≤
              (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) / 2 := by
  filter_upwards [hDeep, crossing_parameters κ hκ T, crossing_error_half κ hκ T] with k hD hp htHalf
  intro PT hPT hm a
  rcases hp with ⟨hn, hb, hs, hl, ht⟩
  let i := S15.patchAt PT hPT a.1
  let Q := directExperiment PT hPT hm a
  let n := (T.S.n k : ℝ)
  have hN := T.S.N_pos k
  have hpow : 1 ≤ n ^ κ.ι := Real.one_le_rpow hn hκ.ι_rng.1.le
  have hb0 : 0 ≤ bstar T k := by unfold bstar; positivity
  have hM (j : Fin PT.tiling.m) : 0 < (PT.tiling.P j).M := by
    rw [← (PT.tiling.P j).cardX]
    exact Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty j).1
  have hMR (j : Fin PT.tiling.m) : (0 : ℝ) < (PT.tiling.P j).M := by exact_mod_cast hM j
  have hμ : ∀ ys, Q.A ys → (Q.μ ys).SupportedIn (T.X k) := by
    intro ys hys x hx
    have hsub : PT.envelope i ⊆ T.X k :=
      (hPT.envelope_subset i).trans ((hPT.tiling_valid.patch_supports i).1.trans
        (fun z hz => (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1 hz)).1))
    have hx' : x ∉ PT.envelope i := fun he => hx (hsub he)
    change (directBaseLaw PT hPT hm a).w x = 0
    rw [directBaseLaw_w]
    simp [S15.directBaseWeight, i, hx']
  have hwμ : ∀ ys, Q.A ys → (Q.μ ys).WidthLE (2 * n ^ κ.ι) := by
    intro ys hys
    have hcap : ∀ x, ((PT.tiling.P i).M : ℝ) * (directBaseLaw PT hPT hm a).w x ≤ 2 := by
      intro x
      rw [directBaseLaw_w]
      exact Lane_q_s15_direct.highDirect_scaled_baseweight_le_two PT hPT hm i a rfl x
    have hw := law_width_of_cap hN (hM i) (directBaseLaw PT hPT hm a)
      (by norm_num : (0 : ℝ) < 2) hcap (direct_patch_log_width hκ PT hPT hm hn i)
    apply Law.WidthLE.mono hw
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hlog
    dsimp [n]
    linarith
  have hν : ∀ b ∈ Q.C, (Q.ν b).SupportedIn (T.Y k) := by
    intro b hb' y hy
    let j := S15.patchAt PT hPT b.1
    have hsub : (PT.tiling.P j).Y ⊆ T.Y k :=
      (hPT.tiling_valid.patch_supports j).2.2.1.trans
        (fun z hz => (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports j).2.2.2 hz)).1)
    exact hPT.law_supported j y (fun he => hy (hsub he))
  have hwν : ∀ b ∈ Q.C, (Q.ν b).WidthLE (11 * n ^ κ.ι) := by
    intro b hb'
    let j := S15.patchAt PT hPT b.1
    have hcap : ∀ y, ((PT.tiling.P j).M : ℝ) * (PT.π j).w y ≤ 11 := by
      intro y
      have hh := (le_div_iff₀ (hMR j)).mp (hPT.law_cap j y)
      simpa [mul_comm] using hh
    have hw := law_width_of_cap hN (hM j) (PT.π j)
      (by norm_num : (0 : ℝ) < 11) hcap (direct_patch_log_width hκ PT hPT hm hn j)
    apply Law.WidthLE.mono hw
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
    norm_num at hlog
    dsimp [n]
    linarith
  have hdeg : ∀ ys, Q.A ys → ∀ b ∈ Q.C, ∀ x, (Q.μ ys).w x ≠ 0 →
      |deg (T.S.E k) Q.c (Q.ν b).w x - 1 / 2| ≤ 3 * bstar T k := by
    intro ys hys b hb' x hxNe
    have hx : x ∈ PT.envelope i := by
      change (directBaseLaw PT hPT hm a).w x ≠ 0 at hxNe
      rw [directBaseLaw_w] at hxNe
      by_contra hx
      apply hxNe
      simp [S15.directBaseWeight, i, hx]
    have hj : S15.patchAt PT hPT b.1 ≠ i := (Finset.mem_filter.mp hb').2.2
    exact hPT.envelope_other_degree i (S15.patchAt PT hPT b.1) hj x hx
  have hcNat := Lane_q_s15_direct.highDirect_crossingNeighbours_card_le_prefix PT hPT a i rfl
  have hc : (Q.C.card : ℝ) ≤ n ^ κ.ι := by
    have hc' : (Q.C.card : ℝ) ≤ (PT.tiling.P i).ℓ := by exact_mod_cast hcNat
    have he : ((PT.tiling.P i).ℓ : ℝ) ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ) := by
      exact_mod_cast (le_max_right (PT.tiling.P i).h (PT.tiling.P i).ℓ)
    exact hc'.trans (he.trans (hPT.tiling_valid.allocation_bounds i).1.le)
  have hbudget : 2 * n ^ κ.ι + (Q.C.card : ℝ) * (Real.log 4 + 10 * bstar T k) ≤ n ^ κ.xs := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at hlog
    have hf : Real.log 4 + 10 * bstar T k ≤ 4 := by linarith
    have hm1 := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ Q.C.card by positivity)
    have hm2 := mul_le_mul_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 4)
    dsimp [n] at *
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.ι]
  have hD' : TwoBudgetDisc T k (n ^ κ.xs) (κ.α * T.S.n k) (bstar T k) := by
    simpa [n, bstar] using hD
  have htail := Q.product_tail hD' hN hb0 hb hbudget hμ hwμ hν hwν hdeg
  have hcN : (Q.C.card : ℝ) ≤ n := by
    have hs : Q.C ⊆ Lane_q_s15_direct.star a := by
      intro b hb'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb').2.1⟩
    dsimp [n]
    exact_mod_cast (Finset.card_le_card hs).trans (Lane_q_s15_direct.star_card_le a)
  have he : Real.exp (11 * n ^ κ.ι - κ.α * T.S.n k) ≤ Real.exp (-κ.α * T.S.n k / 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.ι]
  calc
    (S15.directRawLaw PT hPT).pr (fun ys => |S15.directCrossingMass PT hPT ys a - 1| >
        Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1) ≤
      (FinProb.pi Q.P).pr (fun ys => Q.A ys ∧ ¬ Q.Good Q.C ys) := by
        change (FinProb.pi Q.P).pr _ ≤ _
        apply CrossingExperiment.pr_mono
        intro ys hbad
        refine ⟨True.intro, ?_⟩
        intro hgood
        have hbound := exp_window_abs hb0 hcNat hgood.1 hgood.2
        exact not_lt_of_ge hbound hbad
    _ ≤ (Q.C.card : ℝ) * (2 * Real.exp (11 * n ^ κ.ι - κ.α * T.S.n k)) := htail
    _ ≤ n * (2 * Real.exp (-κ.α * T.S.n k / 2)) :=
      mul_le_mul hcN (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity) (by positivity)
    _ ≤ 8 * n ^ (2 : ℕ) * Real.exp (-κ.α * T.S.n k / 2) := by
      have hn2 : n ≤ n ^ (2 : ℕ) := by nlinarith
      nlinarith [Real.exp_pos (-κ.α * T.S.n k / 2)]
    _ ≤ n ^ (-(κ.R : ℝ)) / 2 := htHalf


end HypercubeRamsey.Lane_sol_s15_bulk
