import HypercubeRamsey.S05.History_sol_s05_1f_raw
import HypercubeRamsey.S05.History_sol_s05_1f_rates

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {γ K' χ : ℝ}

/-- Fixed-data feasibility tails with rates independent of K_D and K_s. -/
theorem high_data_tail_eventually (p : Params5 γ K' χ) (hR : highRequest.Holds p) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ (H : X.KeyHist) (r : X.AbsRecord),
      X.RecOccurs r → r.1.isRight →
      (∀ y, (N : ℝ) * (X.prior H.1 r.1).w y ≤
        Real.exp (p.Kcap * ((p.q0 : ℝ) * p.uSeg n (p.J n + 1)))) →
      ∀ a : X.ArraysOn (Fin (X.p.T n)),
      Real.exp (-(X.p.delta * X.p.s n)) ≤ X.step3MassOn H r a none →
      (∀ c ∈ X.refsOn H r a,
        Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
          X.step3MassOn H r a (some c) ≤ X.step3MassOn H r a none) →
      ∀ hm : 0 < X.step3MassOn H r a none,
        (posteriorLaw X H r a none hm).pr (fun θ =>
          ¬ (X.HighCapped (X.withCol H r.1 θ) r a ∧
            X.HighPriceFeasible (X.withCol H r.1 θ) r a)) ≤
          Real.exp (-(2 * highRate p.pre1 * (p.s n : ℝ))) := by
  let δ := p.delta
  let η := p.delta / 100
  let L0 := pathL0 p.pre1
  let rate := highRate p.pre1
  let c := 8 * rate
  let A : ℝ := (2 * highTypeBudget : ℕ) + 6
  let K := A * (Real.log ((3 + η⁻¹) * A) + 2)
  have hδ : 0 < δ := p.hdelta.1
  have hη : 0 < η := div_pos hδ (by norm_num)
  have hL0 : 0 < L0 := pathL0_pos p.pre1
  have hr : 0 < rate := (rates_pos p.pre1).2
  have hc : 0 < c := mul_pos (by norm_num) hr
  have hlog2 : Real.log 2 < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at hh
    exact hh
  have ha3 : 0 < p.a 3 := by
    have hh := p.ha_order (0 : Fin 9) (3 : Fin 9) (by decide)
    rw [p.ha0] at hh; linarith
  have ha3lt : p.a 3 < 1 := by
    have hh := p.ha_order (3 : Fin 9) (8 : Fin 9) (by decide)
    linarith [p.hgap.1, p.hgap.2.1, p.hgap.2.2]
  have hδsmall : p.delta < 1 / 100 := by
    have hh := p.hdelta_a (0 : Fin 9) (3 : Fin 9) (by decide)
    rw [p.ha0] at hh; linarith
  have hcδ : c ≤ p.delta / 4 := by
    have hh : rate ≤ p.delta / 32 := by
      simpa only [rate, highRate, pathDelta_params] using min_le_left
        (pathDelta p.pre1 / 32)
        (min ((pathEta p.pre1) ^ 2 / 64) ((pathDelta p.pre1) ^ 2 / (64 * (pathL0 p.pre1) ^ 2)))
    dsimp [c]; linarith
  have hc3 : c ≤ 3 := by linarith
  have hcCost : c ≤ p.delta ^ 2 / (8 * L0 ^ 2) := by
    have hh : rate ≤ p.delta ^ 2 / (64 * L0 ^ 2) := by
      have h1 : highRate p.pre1 ≤ min ((pathEta p.pre1) ^ 2 / 64)
          ((pathDelta p.pre1) ^ 2 / (64 * (pathL0 p.pre1) ^ 2)) := min_le_right _ _
      have h2 := min_le_right ((pathEta p.pre1) ^ 2 / 64)
        ((pathDelta p.pre1) ^ 2 / (64 * (pathL0 p.pre1) ^ 2))
      simpa only [pathDelta_params, L0] using h1.trans h2
    have hx := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 8)
    have he : 8 * (p.delta ^ 2 / (64 * L0 ^ 2)) = p.delta ^ 2 / (8 * L0 ^ 2) := by ring
    simpa only [c, he] using hx
  have hcDensity : c ≤ η ^ 2 / 8 := by
    have hh : rate ≤ η ^ 2 / 64 := by
      have h1 : highRate p.pre1 ≤ min ((pathEta p.pre1) ^ 2 / 64)
          ((pathDelta p.pre1) ^ 2 / (64 * (pathL0 p.pre1) ^ 2)) := min_le_right _ _
      have h2 := min_le_left ((pathEta p.pre1) ^ 2 / 64)
        ((pathDelta p.pre1) ^ 2 / (64 * (pathL0 p.pre1) ^ 2))
      simpa only [pathEta, pathDelta_params, η] using h1.trans h2
    dsimp [c]
    linarith
  obtain ⟨_, _, _, _, _, hKD, hKs, _, _⟩ := hR
  have hKD' : 4 * (|highAtomCoefficient p| + 1) / η ≤ p.KD := by
    change 4 * (|atomCoefficientBeforeD p.pre3| + 1) / pathEta p.pre1 ≤ p.KD at hKD
    simpa only [atomCoefficientBeforeD_params, pathEta, pathDelta_params, η] using hKD
  have hKs' : 16 * K / rate ≤ p.Ks := by
    simpa only [highRequest, Params5.pre4, Params5.pre3, Params5.pre2, pathDelta_params,
      η, A, K, rate, mul_assoc] using hKs
  have hK0 : highAtomCoefficient p ≤ η * p.KD / 4 := by
    have hh := (div_le_iff₀ hη).mp hKD'
    have hh' := le_abs_self (highAtomCoefficient p)
    nlinarith
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast (by omega : 1 ≤ 2 * highTypeBudget + 6)
  have hK : 0 ≤ K := by
    have hcoef : 1 ≤ (3 + η⁻¹) * A := by have := (inv_pos.mpr hη).le; nlinarith
    exact mul_nonneg (by linarith) (by have := Real.log_nonneg hcoef; linarith)
  have hCks : K ≤ c * p.Ks / 2 := by
    have hh := (div_le_iff₀ hr).mp hKs'
    dsimp [c]
    nlinarith
  let Bbig := max (max (1 / δ) ((2 * (8 + Real.log 2)) / δ))
    (max ((4 * (8 + Real.log 2)) / (η * p.KD)) ((4 * Real.log 3) / c))
  filter_upwards [high_scales_eventually p Bbig, high_atom_exponent_eventually p,
    high_reference_count_eventually p] with n hscales hatoms hrefs
  obtain ⟨hmN, hJ, hlog, hJLbig, hkbig, hsBig⟩ := hscales
  have hJL : 0 ≤ (p.J n : ℝ) * Real.log (p.m n : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hkone : 1 / δ ≤ (p.usedBlocks n * (p.q0 * p.uStarSeg n) : ℕ) :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hkbig)
  have hkactual : (2 * (8 + Real.log 2)) / δ ≤
      (p.usedBlocks n * (p.q0 * p.uStarSeg n) : ℕ) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hkbig)
  have hDmargin : (4 * (8 + Real.log 2)) / (η * p.KD) ≤
      (p.J n : ℝ) * Real.log (p.m n : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hJLbig)
  have habsorb : 4 * Real.log 3 ≤ c * (p.s n : ℝ) := by
    have hh : (4 * Real.log 3) / c ≤ p.s n :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hsBig)
    simpa [mul_comm] using (div_le_iff₀ hc).mp hh
  have hJpos : (0 : ℝ) < p.J n := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hJ
  have hsN : 0 < p.s n := by
    have hJLpos : 0 < (p.J n : ℝ) * Real.log (p.m n : ℝ) := mul_pos hJpos (by linarith)
    have hceil : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ (p.s n : ℝ) := Nat.le_ceil _
    have hsR : (0 : ℝ) < p.s n := by
      have hmul : 0 < p.Ks * ((p.J n : ℝ) * Real.log (p.m n : ℝ)) := mul_pos p.hKs hJLpos
      rw [← mul_assoc] at hmul
      exact hmul.trans_le hceil
    exact_mod_cast hsR
  have hDH : 0 < p.DH n := by
    unfold Params5.DH
    exact mul_pos (mul_pos p.hKD hJpos) (by linarith)
  intro N E G X hXp H r hrec hh hprior a hlo hrat hm
  obtain ⟨key, hkey⟩ : ∃ key : CoarseKey5 n, r.1 = .inr key := by
    cases h : r.1 with
    | inl key => simp [h] at hh
    | inr key => exact ⟨key, rfl⟩
  have hcolp : colLen5 (p.s n) r.1 = p.s n := by rw [hkey]; rfl
  have hcol : colLen5 (X.p.s n) r.1 = p.s n := by simpa only [hXp] using hcolp
  let k : ℝ := (p.usedBlocks n * (p.q0 * p.uStarSeg n) : ℕ)
  have hk : 0 < k := (div_pos (by norm_num) hδ).trans_le hkone
  have hL : 0 < L0 * k := mul_pos hL0 hk
  have hε : 0 < p.delta * k / 2 := div_pos (mul_pos p.hdelta.1 hk) (by norm_num)
  have hεD : 0 < η * p.DH n / 2 := div_pos (mul_pos hη hDH) (by norm_num)
  have hB : 0 ≤ (p.a 3 + p.delta) * k := mul_nonneg (add_nonneg ha3.le p.hdelta.1.le) hk.le
  have hβ : η + ((p.a 3 + p.delta) * k) / (L0 * k) ≤ p.delta / 50 := by
    have he : ((p.a 3 + p.delta) * k) / (L0 * k) = (p.a 3 + p.delta) / L0 := by
      field_simp [hk.ne', hL0.ne']
    rw [he]
    have hL0eq : L0 = 100 * (p.a 3 + p.delta + 1) / p.delta := by
      change pathL0 p.pre1 = _
      rw [pathL0_params, abs_of_pos ha3]
    have hh : (p.a 3 + p.delta) / L0 ≤ p.delta / 100 := by
      apply (div_le_iff₀ hL0).mpr
      rw [hL0eq]
      field_simp [p.hdelta.1.ne']
      nlinarith only [p.hdelta.1]
    change p.delta / 100 + (p.a 3 + p.delta) / L0 ≤ p.delta / 50
    linarith
  have hactual : p.a 3 * k + 8 + Real.log 2 + p.delta * k / 2 ≤ (p.a 3 + p.delta) * k := by
    have hmargin := (div_le_iff₀ hδ).mp hkactual
    dsimp [δ] at hmargin
    nlinarith only [hmargin]
  have hdenBudget : highAtomCoefficient p * (p.J n : ℝ) * Real.log (p.m n : ℝ) +
      8 + Real.log 2 + η * p.DH n / 2 ≤ η * p.DH n := by
    have hK0scaled := mul_le_mul_of_nonneg_right hK0 hJL
    have hmargin := (div_le_iff₀ (mul_pos hη p.hKD)).mp hDmargin
    unfold Params5.DH
    nlinarith only [hK0scaled, hmargin]
  have hatom (θ) : (N : ℝ) ^ colLen5 (X.p.s n) r.1 * X.step3PostOn H r a none θ ≤
      Real.exp ((highAtomCoefficient p * (p.J n : ℝ) * Real.log (p.m n : ℝ)) *
        colLen5 (X.p.s n) r.1) := by
    have hlower : Real.exp (-(X.p.delta * colLen5 (X.p.s n) r.1)) ≤ X.step3MassOn H r a none := by
      simpa only [hXp, hcolp] using hlo
    have hfinite := posterior_atom_bound X H r a (p.Kcap * ((p.q0 : ℝ) * p.uSeg n (p.J n + 1)))
      hprior hlower θ
    apply hfinite.trans
    apply Real.exp_le_exp.mpr
    have hb := hatoms N E G X hXp r hrec hh
    simpa only [hXp] using mul_le_mul_of_nonneg_right hb
      (Nat.cast_nonneg (colLen5 (X.p.s n) r.1))
  have htail := high_posterior_feasibility_tail X H r hrec hh a hm
    (by simpa [hcol] using hsN) hrat
    (highAtomCoefficient p * (p.J n : ℝ) * Real.log (p.m n : ℝ)) 8 (L0 * k)
    (p.delta * k / 2) (η * p.DH n / 2) η ((p.a 3 + p.delta) * k) η (p.delta / 50)
    (by simpa only [hXp] using hDH) hL hε hεD hη hB hη.le
    (by dsimp [η]; linarith) hβ (by linarith)
    (by simpa only [hXp, k] using hactual) (by simpa only [hXp] using hdenBudget)
    (by simpa only [hXp, k, η] using high_cost_budget p k hkone) hatom
  let rcount := (X.refsOn H r a).card
  have hrcount : (rcount : ℝ) ≤ A * (p.J n : ℝ) := by
    have hsmall : rcount ≤ r.2.2.1.card := Finset.card_image_le
    have hbudget := hrefs N E G X hXp r hrec hh
    have hsmallR : (rcount : ℝ) ≤ r.2.2.1.card := by exact_mod_cast hsmall
    exact hsmallR.trans (by simpa [A] using hbudget)
  have hJm : p.J n ≤ p.m n := by
    have hpow : (p.m n : ℝ) ^ (1 / 20 : ℝ) ≤ p.m n := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.le_of_lt hmN : (1 : ℝ) ≤ p.m n)
        (by norm_num : (1 / 20 : ℝ) ≤ 1)
    have hfloor : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact_mod_cast hfloor.trans hpow
  have hbox := finite_box_grid_budget rcount (p.J n) (p.m n) A η hA hη hJ hlog hJm hrcount
  have hsceil : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ p.s n := Nat.le_ceil _
  have hgridExp : K * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤ c * (p.s n : ℝ) / 2 := by
    have h1 := mul_le_mul_of_nonneg_right hCks hJL
    have h2 := mul_le_mul_of_nonneg_left hsceil hc.le
    nlinarith only [h1, h2]
  let grid : ℝ := ((⌈(1 + η⁻¹) * rcount⌉₊ + 1) ^ rcount : ℕ)
  have hgrid : grid * ((rcount : ℝ) + 1) ≤ Real.exp (c * (p.s n : ℝ) / 2) := by
    have hh := hbox.trans (Real.exp_le_exp.mpr hgridExp)
    simpa [grid, K, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hh
  have habs := high_finite_tail_absorption (p.s n) k (p.DH n) p.delta η L0 c grid rcount
    (by exact_mod_cast hsN) hk hDH p.hdelta.1 hη hL0 hc hc3 hcCost hcDensity
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hgrid habsorb
  apply htail.trans
  simpa only [hXp, hcolp, grid, rcount, c, show 8 * rate * (p.s n : ℝ) / 4 =
    2 * highRate p.pre1 * (p.s n : ℝ) by dsimp [rate]; ring] using habs


/-- The complete high raw one-target bound, including both denominator and
fixed-data feasibility exceptions. -/
theorem high_raw_eventual_bound (p : Params5 γ K' χ) (hR : highRequest.Holds p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ (H : X.KeyHist) (r : X.AbsRecord),
      X.RecOccurs r → r.1.isRight →
      (∀ y, (N : ℝ) * (X.prior H.1 r.1).w y ≤
        Real.exp (p.Kcap * ((p.q0 : ℝ) * p.uSeg n (p.J n + 1)))) →
      (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
        (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r) ≤
          Real.exp (-(highRate p.pre1 * (p.s n : ℝ))) := by
  have hrate : 0 < highRate p.pre1 := (rates_pos p.pre1).2
  have hrateDelta : highRate p.pre1 ≤ p.delta / 32 := by
    simpa only [highRate, pathDelta_params] using min_le_left (pathDelta p.pre1 / 32)
      (min ((pathEta p.pre1) ^ 2 / 64) ((pathDelta p.pre1) ^ 2 / (64 * (pathL0 p.pre1) ^ 2)))
  obtain ⟨nD, hD⟩ := high_denominator_eventual_bound p
  have hscales := high_scales_eventually p (Real.log 2 / highRate p.pre1)
  have hdata := high_data_tail_eventually p hR
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hscales.and (hdata.and (eventually_ge_atTop nD)))
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp H r hr hh hprior
  obtain ⟨hsc, hd, hnD⟩ := hn₀ n hn
  have hraw := high_raw_bound_of_posterior_tail X H r hr hh
    (Real.exp (-(2 * highRate p.pre1 * (p.s n : ℝ)))) (Real.exp_pos _).le
    (hd N E G X hXp H r hr hh hprior)
  have hden := hD n hnD N E G X hXp H r hr hh
  have hlower : Real.log 2 ≤ highRate p.pre1 * (p.s n : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hrate).mp hsc.2.2.2.2.2
  have hcomp : Real.exp (-((p.delta / 4) * X.p.s n)) ≤
      Real.exp (-(2 * highRate p.pre1 * (p.s n : ℝ))) := by
    rw [hXp]
    apply Real.exp_le_exp.mpr
    have hnonneg : (0 : ℝ) ≤ p.s n := Nat.cast_nonneg _
    have hcoef : 2 * highRate p.pre1 ≤ p.delta / 4 := by linarith
    nlinarith
  apply hraw.trans
  calc
    _ ≤ Real.exp (-(2 * highRate p.pre1 * (p.s n : ℝ))) +
        Real.exp (-(2 * highRate p.pre1 * (p.s n : ℝ))) :=
      add_le_add (hden.trans hcomp) le_rfl
    _ = Real.exp (Real.log 2 - 2 * highRate p.pre1 * (p.s n : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end
end HypercubeRamsey.Lane_sol_s05_1f
