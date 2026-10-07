import HypercubeRamsey.S17.Nodes_sol_s17_pool

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.Lane_sol_s17_pool

open Classical Filter
open scoped BigOperators

/-- A cleaned probability prior, viewed as an actual first-side probability law. -/
noncomputable def cleanPriorLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ) :
    Law (T.S.N k) where
  w := σ
  nonneg := hσ.1
  sum_eq_one := hσ.2.1

theorem cleanPriorLaw_supported {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ) :
    (cleanPriorLaw D v σ hσ).SupportedIn (T.X k) := by
  intro x hx
  by_contra hne
  have hxenv := Lane_q_s17_pool.cleanSupport_subset_envelope D D.tiling_valid v σ hσ x hne
  exact hx (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports (D.G.patchOf v)).2.1
    ((D.tiling_valid.tiling_valid.patch_supports (D.G.patchOf v)).1
      (D.tiling_valid.envelope_subset _ hxenv)))).1

/-- The common atom cap needed before short crossing and compatibility exposures. -/
theorem clean_prior_cap {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (W : ℝ) (hW : 0 ≤ W)
    (hMass : Real.log ((T.S.N k : ℝ) / (PT.tiling.P (D.G.patchOf v)).M) ≤ W)
    (hGain : 0 ≤ PT.tiling.gain (D.G.patchOf v)) :
    (cleanPriorLaw D v σ hσ).CapLE
      (2 ^ (PT.tiling.P (D.G.patchOf v)).h * (2 * Real.exp W)) := by
  let i := D.G.patchOf v
  have hMnat : 0 < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact Finset.card_pos.mpr (D.tiling_valid.tiling_valid.patch_nonempty i).1
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by exact_mod_cast hMnat
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hRatio : (T.S.N k : ℝ) / (PT.tiling.P i).M ≤ Real.exp W := by
    rw [← Real.exp_log (div_pos hN hM)]
    exact Real.exp_le_exp.mpr hMass
  obtain ⟨a, ha, hsupport, hclu, hdirect⟩ := hσ.2.2
  intro x
  change (T.S.N k : ℝ) * σ x ≤ _
  by_cases hm : PT.tiling.mode.isCluster
  · have h := hclu hm x
    have hExp : Real.exp (-500 * PT.tiling.gain i) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      (T.S.N k : ℝ) * σ x ≤ 2 ^ (PT.tiling.P i).h * Real.exp (-500 * PT.tiling.gain i) := h
      _ ≤ 2 ^ (PT.tiling.P i).h := by
        simpa using mul_le_mul_of_nonneg_left hExp (by positivity : 0 ≤ (2 : ℝ) ^ (PT.tiling.P i).h)
      _ ≤ 2 ^ (PT.tiling.P i).h * (2 * Real.exp W) := by
        have hExpW : 1 ≤ Real.exp W := Real.one_le_exp_iff.mpr hW
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (PT.tiling.P i).h]
  · have hc := (D.tiling_valid.corner_clean i a ha).card_lower
    have hcpos : 0 < ((PT.mesh.corner a i).card : ℝ) := by linarith
    have hxform := (hdirect hm).2 x
    rw [hxform]
    by_cases hx : x ∈ PT.mesh.corner a i
    · simp only [show x ∈ PT.mesh.corner a (D.G.patchOf v) from hx, ite_true]
      have hcorner : (T.S.N k : ℝ) / (PT.mesh.corner a i).card ≤
          2 * ((T.S.N k : ℝ) / (PT.tiling.P i).M) := by
        apply (div_le_iff₀ hcpos).2
        have h' : (PT.tiling.P i).M ≤ 2 * ((PT.mesh.corner a i).card : ℝ) := by linarith
        have hh := mul_le_mul_of_nonneg_left h' (div_nonneg hN.le hM.le)
        have hid : (T.S.N k : ℝ) / (PT.tiling.P i).M * (PT.tiling.P i).M = T.S.N k :=
          div_mul_cancel₀ _ hM.ne'
        rw [hid] at hh
        nlinarith
      have hpow : (1 : ℝ) ≤ 2 ^ (PT.tiling.P i).h := one_le_pow₀ (by norm_num)
      calc
        (T.S.N k : ℝ) * (1 / (PT.mesh.corner a i).card) =
            (T.S.N k : ℝ) / (PT.mesh.corner a i).card := by ring
        _ ≤ 2 * ((T.S.N k : ℝ) / (PT.tiling.P i).M) := hcorner
        _ ≤ 2 * Real.exp W := mul_le_mul_of_nonneg_left hRatio (by norm_num)
        _ ≤ 2 ^ (PT.tiling.P i).h * (2 * Real.exp W) := by
          simpa using mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ 2 * Real.exp W)
    · simp only [show x ∉ PT.mesh.corner a (D.G.patchOf v) from hx, ite_false, mul_zero]
      positivity

/-- Applying the prescribed hit ratios first retains the pinned mass divided
by the worst allowed denominator product. -/
theorem pinned_restriction_mass_lower {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (pins : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k))
    (dmax : ℝ) (hdmax : 0 < dmax)
    (hdeg : ∀ x, σ x ≠ 0 → ∀ w ∈ pins,
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ∧
      deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤ dmax) :
    D.pinnedPriorMass v σ pins fixed / dmax ^ pins.card ≤
      ∑ x, σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w) := by
  classical
  rw [Lane_q_s17_pool.pinnedPriorMass_eq_hits D D.tiling_valid v σ hσ pins fixed,
    Finset.sum_div]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hz : σ x = 0
  · simp [hz]
  · have hpoint : ∀ w ∈ pins,
        hit (T.S.E k) PT.tiling.c x (fixed w) / dmax ≤ D.hitRatio w x (fixed w) := by
      intro w hw
      exact div_le_div_of_nonneg_left (by unfold hit; split_ifs <;> norm_num)
        (hdeg x hz w hw).1 (hdeg x hz w hw).2
    have hprod : (∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w) / dmax) ≤
        ∏ w ∈ pins, D.hitRatio w x (fixed w) := by
      apply Finset.prod_le_prod₀
      · intro w hw
        exact div_nonneg (by unfold hit; split_ifs <;> norm_num) hdmax.le
      · exact hpoint
    rw [Finset.prod_div_distrib, Finset.prod_const] at hprod
    have hm := mul_le_mul_of_nonneg_left hprod (hσ.1 x)
    convert hm using 1 <;> ring

/-- A hit ratio is nonnegative, including at zero denominators. -/
theorem hitRatio_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (w : Pos T k) (x y : Fin (T.S.N k)) : 0 ≤ D.hitRatio w x y := by
  apply div_nonneg
  · unfold hit
    split_ifs <;> norm_num
  · unfold deg
    exact Finset.sum_nonneg (fun y _ => mul_nonneg ((PT.π _).nonneg y)
      (by unfold hit; split_ifs <;> norm_num))

/-- The actual pinned restriction has a normalized law whose cap grows only
by the inverse denominator product and the inverse retained mass. -/
theorem normalize_pinned_restriction {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (pins : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k))
    (B dmin Z : ℝ) (hB : 0 ≤ B) (hmin : 0 < dmin) (hZ : 0 < Z)
    (hcap : (cleanPriorLaw D v σ hσ).CapLE B)
    (hZeq : ∑ x, σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w) = Z)
    (hdeg : ∀ x, σ x ≠ 0 → ∀ w ∈ pins,
      dmin ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) :
    ∃ τ : Law (T.S.N k),
      τ.SupportedIn (PT.envelope (D.G.patchOf v)) ∧
      τ.CapLE (B * (1 / dmin) ^ pins.card / Z) ∧
      ∀ x, Z * τ.w x = σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w) := by
  classical
  let g : Fin (T.S.N k) → ℝ := fun x => ∏ w ∈ pins, D.hitRatio w x (fixed w)
  have hg : ∀ x, 0 ≤ g x := fun x => Finset.prod_nonneg (fun w _ => hitRatio_nonneg D w x _)
  have hgCap : ∀ x, σ x ≠ 0 → g x ≤ (1 / dmin) ^ pins.card := by
    intro x hx
    calc
      g x ≤ ∏ _w ∈ pins, (1 / dmin) := by
        apply Finset.prod_le_prod₀
        · intro w hw
          exact hitRatio_nonneg D w x _
        · intro w hw
          have hd : 0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x :=
            hmin.trans_le (hdeg x hx w hw)
          unfold ListGateContext.hitRatio
          calc
            _ ≤ 1 / deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x :=
              div_le_div_of_nonneg_right (by unfold hit; split_ifs <;> norm_num) hd.le
            _ ≤ 1 / dmin := one_div_le_one_div_of_le hmin (hdeg x hx w hw)
      _ = _ := by simp
  let τ := Lane_q_s17_pool.reweightLaw (cleanPriorLaw D v σ hσ) g hg Z hZ hZeq
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x hx
    have hz : σ x = 0 := by
      by_contra hne
      exact hx (Lane_q_s17_pool.cleanSupport_subset_envelope D D.tiling_valid v σ hσ x hne)
    simp [τ, Lane_q_s17_pool.reweightLaw, cleanPriorLaw, hz]
  · intro x
    change (T.S.N k : ℝ) * (σ x * g x / Z) ≤ _
    by_cases hx : σ x = 0
    · simp [hx]
      positivity
    · have hmul := mul_le_mul (hcap x) (hgCap x hx) (hg x) hB
      calc
        (T.S.N k : ℝ) * (σ x * g x / Z) = ((T.S.N k : ℝ) * σ x * g x) / Z := by ring
        _ ≤ (B * (1 / dmin) ^ pins.card) / Z := div_le_div_of_nonneg_right hmul hZ.le
  · intro x
    change Z * (σ x * g x / Z) = σ x * g x
    field_simp

/-- A successful normalized pin restriction factors the full initial row
without changing the subsequent crossing or bulk hit ratios. -/
theorem rowMass_after_pins {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (τ : Law (T.S.N k))
    (pins : Finset (Pos T k)) (hPins : pins ⊆ D.externalEarly v)
    (fixed ys : Pos T k → Fin (T.S.N k)) (Z : ℝ)
    (hfixed : ∀ w ∈ pins, ys w = fixed w)
    (hrow : ∀ x, Z * τ.w x = σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w)) :
    D.rowMass v σ ys = Z *
      ∑ x, τ.w x * ∏ w ∈ D.externalEarly v \ pins, D.hitRatio w x (ys w) := by
  classical
  unfold ListGateContext.rowMass ListGateContext.row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hpin : (∏ w ∈ pins, D.hitRatio w x (ys w)) =
      ∏ w ∈ pins, D.hitRatio w x (fixed w) :=
    Finset.prod_congr rfl (fun w hw => by rw [hfixed w hw])
  rw [← Finset.prod_sdiff hPins, hpin]
  calc
    _ = (σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w)) *
        (∏ w ∈ D.externalEarly v \ pins, D.hitRatio w x (ys w)) := by ring
    _ = _ := by rw [← hrow x]; ring

private theorem E_indicator_eq_pr {α : Type*} [Fintype α]
    (P : FinLaw α) (A : α → Prop) :
    P.E (fun a => if A a then (1 : ℝ) else 0) = P.pr A := by
  classical
  unfold FinLaw.E FinLaw.pr
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : A a <;> simp [h]

/-- The permission table controls the actual fresh own-tape first degree,
averaged over its unforced iid pool. This is the forced-external-slot case. -/
theorem forced_permission_average {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K)
    (v : Pos T k) (heven : IsEvenRole v) (b : Pos T k) (hb : b ∈ D.externalEarly v)
    (B : Bin PT.tiling (D.G.patchOf b)) (hB : hQuant.sampler.permittedBin b B)
    (y : Fin (T.S.N k)) (hy : y ∈ B.1) :
    (iidPoolLaw D.G hQuant.pool_support_nonempty).E (fun pools =>
      if D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) then
        (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
          |(∑ x, D.F.prior (D.G.cellOf v) s v x *
            hit (T.S.E k) PT.tiling.c x y) - 1 / 2| > 2 * bstar T k)
      else 0) ≤ K * Real.exp (-κ.cperm * T.S.n k) := by
  classical
  let Φ : (Fin (T.S.N k) → ℝ) → ℝ := fun σ =>
    if σ ≠ 0 ∧ |(∑ x, σ x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| > 2 * bstar T k
      then 1 else 0
  have hΦ : ∀ σ, 0 ≤ Φ σ := fun σ => by dsimp [Φ]; split_ifs <;> norm_num
  have hΦzero : Φ 0 = 0 := by simp [Φ]
  have hCompare := hQuant.sampler.base_comparison hQuant.pool_support_nonempty v heven Φ hΦ hΦzero
  have hOwn : ∀ (pools : D.PoolAssignment), D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) →
      (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).E
        (fun s => Φ (D.F.prior (D.G.cellOf v) s v)) =
      (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
        |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
          2 * bstar T k) := by
    intro pools htyp
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hw : (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).w s = 0
    · simp [hw, Φ]
    · have hpos : 0 < (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).w s :=
        lt_of_le_of_ne ((D.F.fresh _ _).nonneg s) (Ne.symm hw)
      have hsv := D.fresh_spec.fresh_valid _ _ s htyp hpos
      have hclean := hQuant.prior_shape v (pools (D.G.cellOf v)) s heven htyp hsv
      have hne : D.F.prior (D.G.cellOf v) s v ≠ 0 := by
        intro hz
        have hh := hclean.2.1
        rw [hz] at hh
        simp at hh
      dsimp [Φ]
      simp [hne]
  have hLeft :
      (iidPoolLaw D.G hQuant.pool_support_nonempty).E (fun pools =>
        if D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) then
          (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).E
            (fun s => Φ (D.F.prior (D.G.cellOf v) s v)) else 0) =
      (iidPoolLaw D.G hQuant.pool_support_nonempty).E (fun pools =>
        if D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) then
          (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
            |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
              2 * bstar T k) else 0) := by
    apply congrArg (FinLaw.E _)
    funext pools
    by_cases ht : D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v))
    · simp only [ht, ite_true]
      exact hOwn pools ht
    · simp [ht]
  rw [hLeft] at hCompare
  refine hCompare.trans ?_
  have hBase := hQuant.sampler.permission_test v heven b hb B hB y hy
  have hE : (hQuant.sampler.base v).law.E
      (fun ω => Φ ((hQuant.sampler.base v).readout ω)) =
      (hQuant.sampler.base v).law.pr (fun ω =>
        (hQuant.sampler.base v).readout ω ≠ 0 ∧
          |(∑ x, (hQuant.sampler.base v).readout ω x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
            2 * bstar T k) := by
    unfold FinLaw.E FinLaw.pr
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp [Φ]
    split_ifs with h₁ h₂ <;> simp_all
  rw [hE]
  exact mul_le_mul_of_nonneg_left hBase hK

/-- Small degree errors retain the prescribed ninety-percent pin threshold. -/
theorem short_hit_mass_threshold (s : ℕ) (err : ℝ) (he : 0 ≤ err)
    (heSmall : err ≤ 1 / 4) (hs : 2 * (s : ℝ) * err ≤ 1 / 10) :
    (9 / 10 : ℝ) * Real.rpow 2 (-(s : ℝ)) ≤ (1 / 2 - err) ^ s := by
  have hBern : 1 + (s : ℝ) * (-2 * err) ≤ (1 + (-2 * err)) ^ s :=
    one_add_mul_le_pow (by linarith) s
  have hPower : (9 / 10 : ℝ) ≤ (1 - 2 * err) ^ s := by
    rw [show 1 + (-2 * err) = 1 - 2 * err by ring] at hBern
    exact (show (9 / 10 : ℝ) ≤ 1 + (s : ℝ) * (-2 * err) by nlinarith).trans hBern
  have hTwo : Real.rpow (2 : ℝ) (-(s : ℝ)) = (1 / 2 : ℝ) ^ s := by
    change ((2 : ℝ) ^ (-(s : ℝ))) = (1 / 2 : ℝ) ^ s
    rw [Real.rpow_neg (x := (2 : ℝ)) (y := (s : ℝ)) (by norm_num), Real.rpow_natCast]
    simp [one_div, inv_pow]
  rw [hTwo, show (1 / 2 - err) = (1 / 2 : ℝ) * (1 - 2 * err) by ring, mul_pow]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hPower
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) s)

/-- The adaptive small-width estimate reaches the exact compatibility
threshold for a fixed set of independent unforced bin labels. -/
theorem independent_pin_mass_tail {T : Stage} {k s : ℕ}
    {wS wL err W : ℝ} (hDisc : TwoBudgetDisc T k wS wL err)
    (c : Colour) (μ : Law (T.S.N k)) (ν : Fin s → Law (T.S.N k))
    (hμ : μ.SupportedIn (T.X k)) (he : 0 ≤ err) (heSmall : err ≤ 1 / 4)
    (hs : 2 * (s : ℝ) * err ≤ 1 / 10)
    (hCap : μ.CapLE (Real.exp wS * (1 / 2 - err) ^ s))
    (hν : ∀ i, (ν i).SupportedIn (T.Y k)) (hνW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr (fun ys =>
      productMass μ (fun _ x y => hit (T.S.E k) c x y) ys <
        (9 / 10 : ℝ) * Real.rpow 2 (-(s : ℝ))) ≤
      (s : ℝ) * (2 * Real.exp (W - wL)) := by
  have ht := independent_hits_lower_tail hDisc c μ ν hμ (by linarith) he hCap hν hνW
  apply le_trans _ ht
  apply Lane_q_s17_pool.pr_mono
  intro ys hy
  exact hy.trans_le (short_hit_mass_threshold s err he heSmall hs)

/-- The unforced-label compatibility tail remains uniform after averaging
the actual fresh own tape on any typical own pool, including a pinned one. -/
theorem fresh_own_independent_pin_mass_tail {κ : CConsts} {T : Stage} {k s : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k) (heven : IsEvenRole v)
    (P : D.F.Pool (D.G.cellOf v)) (htyp : D.F.typical (D.G.cellOf v) P)
    {wS wL err W : ℝ} (hDisc : TwoBudgetDisc T k wS wL err)
    (ν : Fin s → Law (T.S.N k)) (he : 0 ≤ err) (heSmall : err ≤ 1 / 4)
    (hs : 2 * (s : ℝ) * err ≤ 1 / 10)
    (hCap : ∀ σ, D.ValidInitialPrior v σ → ∀ hσ : D.CleanInitialPrior v σ,
      (cleanPriorLaw D v σ hσ).CapLE (Real.exp wS * (1 / 2 - err) ^ s))
    (hν : ∀ i, (ν i).SupportedIn (T.Y k)) (hνW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.bind (D.F.fresh (D.G.cellOf v) P)
      (fun _ => FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i))).pr (fun ω =>
        (∑ x, D.F.prior (D.G.cellOf v) ω.1 v x *
          ∏ i, hit (T.S.E k) PT.tiling.c x (ω.2 i)) <
            (9 / 10 : ℝ) * Real.rpow 2 (-(s : ℝ))) ≤
      (s : ℝ) * (2 * Real.exp (W - wL)) := by
  classical
  let ρ := (s : ℝ) * (2 * Real.exp (W - wL))
  rw [bind_pr]
  change (D.F.fresh (D.G.cellOf v) P).E _ ≤ ρ
  calc
    _ ≤ ∑ t, (D.F.fresh (D.G.cellOf v) P).w t * ρ := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hz : (D.F.fresh (D.G.cellOf v) P).w t = 0
      · simp [hz]
      · have hp : 0 < (D.F.fresh (D.G.cellOf v) P).w t :=
          lt_of_le_of_ne ((D.F.fresh _ _).nonneg t) (Ne.symm hz)
        have hsv := D.fresh_spec.fresh_valid _ _ t htyp hp
        have hclean := hQuant.prior_shape v P t heven htyp hsv
        have hvalid : D.ValidInitialPrior v (D.F.prior (D.G.cellOf v) t v) :=
          ⟨hclean, P, t, htyp, hsv, fun _ => rfl⟩
        apply mul_le_mul_of_nonneg_left _ ((D.F.fresh _ _).nonneg t)
        exact independent_pin_mass_tail hDisc PT.tiling.c (cleanPriorLaw D v _ hclean) ν
          (cleanPriorLaw_supported D v _ hclean) he heSmall hs
          (hCap _ hvalid hclean) hν hνW
    _ = ρ := by rw [← Finset.sum_mul, (D.F.fresh _ _).sum_one, one_mul]

/-- Restriction does not enlarge the original cleaned corner support. -/
theorem restricted_row_corner_support {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (τ : Law (T.S.N k))
    (a : PT.mesh.V) (hσ : ∀ x, σ x ≠ 0 → x ∈ PT.mesh.corner a (D.G.patchOf v))
    (f : Fin (T.S.N k) → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hrow : ∀ x, Z * τ.w x = σ x * f x) :
    τ.SupportedIn (PT.mesh.corner a (D.G.patchOf v)) := by
  intro x hx
  have hz : σ x = 0 := by by_contra hne; exact hx (hσ x hne)
  have hh := hrow x
  rw [hz, zero_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left hZ.ne'

/-- Construct the homogeneous bulk experiment on its actual cleaned corner.
Only the quantitative width, degree, clique-scale and gamma budgets remain
to be supplied by the mode-dependent calculation. -/
noncomputable def cornerHomogeneousInput {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (a : PT.mesh.V) (ha : a ∈ PT.activeVertices) (τ : Law (T.S.N k))
    (d : ℕ) (hd : d ≤ T.S.n k)
    (hτ : τ.SupportedIn (PT.mesh.corner a (D.G.patchOf v)))
    (hτwidth : τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (hπwidth : (PT.π (D.G.patchOf v)).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (C0 : ℝ)
    (hGate : ∀ x ∈ PT.mesh.corner a (D.G.patchOf v),
      S12.DegGate (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w C0 (bstar T k) x)
    (hPos : ∀ x ∈ PT.mesh.corner a (D.G.patchOf v),
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x)
    (hQ : Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤
      PT.tiling.Q (D.G.patchOf v) ∧ 1 ≤ (PT.tiling.Q (D.G.patchOf v) : ℝ))
    (γ : ℝ)
    (hγ : γ = Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q (D.G.patchOf v) : ℝ)) *
      (PT.mesh.corner a (D.G.patchOf v)).sup'
        (D.tiling_valid.corner_clean _ a ha).nonempty (fun x => τ.w x *
          Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) (-(d : ℝ))))
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    S12.HomogeneousInput κ hκ T k PT.tiling.c C0 := by
  let i := D.G.patchOf v
  have hClean := D.tiling_valid.corner_clean i a ha
  have hSp : PT.mesh.corner a i ⊆ T.X k := by
    intro x hx
    exact (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports i).2.1
      ((D.tiling_valid.tiling_valid.patch_supports i).1 (hClean.sub hx)))).1
  have hπY : (PT.π i).SupportedIn (T.Y k) := by
    intro y hy
    apply D.tiling_valid.law_supported i y
    intro hyY
    exact hy (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports i).2.2.2
      ((D.tiling_valid.tiling_valid.patch_supports i).2.2.1 hyY))).1
  refine {
    S := {
      d := d
      d_le := hd
      τ := τ
      π := fun _ => PT.π i
      τ_supp := fun x hx => hτ x (fun hxSp => hx (hSp hxSp))
      π_supp := fun _ => hπY
      τ_width := hτwidth
      π_width := fun _ => hπwidth }
    π := PT.π i
    homogeneous := fun _ => rfl
    Sp := PT.mesh.corner a i
    Sp_nonempty := hClean.nonempty
    Sp_subset := hSp
    τ_supported := hτ
    π_supported := hπY
    degree_gate := hGate
    degree_positive := hPos
    Q := PT.tiling.Q i
    Q_large := hQ
    noClique := hClean.noClique
    gamma := γ
    gamma_eq := hγ
    gamma_nonneg := hγ0
    gamma_lt_one := hγ1 }

/-- S12's homogeneous lower tail applies directly to the bulk product of
hit ratios used by the actual initial row. -/
theorem homogeneous_bulk_product_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop, ∀ (H : S12.HomogeneousInput κ hκ T k c C0)
      (t : ℝ), 0 ≤ t → t < 1 →
      (FinLaw.pi fun _ : Fin H.S.d => ListGateContext.lawAsFinLaw H.π).pr (fun ys =>
        productMass H.S.τ (fun _ x y => hit (T.S.E k) c x y / deg (T.S.E k) c H.π.w x) ys < t) ≤
          (1 - t) ^ (-(κ.u : ℝ)) *
            ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma) := by
  have hm := S12.moderate_moment κ hκ T hDeep c C0 hC0
  have hp := S12.homogeneous_peeling κ hκ T hDeep c C0 hC0 hm
  have hTail := S12.homogeneous_lower_tail κ hκ T hDeep c C0 hC0 hm hp
  filter_upwards [hTail] with k hk
  intro H t ht0 ht1
  have hZ (ys : Fin H.S.d → Fin (T.S.N k)) :
      S12.Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys =
        productMass H.S.τ (fun _ x y => hit (T.S.E k) c x y / deg (T.S.E k) c H.π.w x) ys := by
    unfold S12.Zmass productMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    unfold S12.acoef
    ring
  have h := hk H t ht0 ht1
  simp_rw [hZ] at h
  exact h

/-- The external early incidence count retains the exact late-role saving
used in the homogeneous gamma estimate. -/
theorem externalEarly_late_budget {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k) (heven : IsEvenRole v)
    (hh : (PT.tiling.P (D.G.patchOf v)).h ≤ T.S.n k) :
    ((D.externalEarly v).card : ℝ) + (PT.tiling.P (D.G.patchOf v)).h +
      κ.A0 * Real.log (T.S.n k : ℝ) / 2 ≤ (T.S.n k : ℝ) + 1 := by
  classical
  let I := PT.tiling.Icoord (D.G.patchOf v)
  let L : Finset (Fin (T.S.n k)) := Finset.univ.filter fun j =>
    (D.G.classOf (flipPos v j)).isSome
  let E : Finset (Fin (T.S.n k)) := Finset.univ \ (I ∪ L)
  have hnone (j : Fin (T.S.n k)) : D.G.classOf (flipPos v j) = none ↔ j ∉ L := by
    cases h : D.G.classOf (flipPos v j) <;> simp [L, h]
  have hExt : D.externalEarly v = E.image (flipPos v) := by
    ext w
    simp only [ListGateContext.externalEarly, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨hclass, j, hj, rfl⟩
      exact ⟨j, by simpa [E, I, Finset.mem_union] using And.intro hj ((hnone j).mp hclass), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hj' : j ∉ I ∧ j ∉ L := by simpa [E] using hj
      exact ⟨(hnone j).mpr hj'.2, j, hj'.1, rfl⟩
  have hflip : Function.Injective (flipPos v) := by
    intro a b hab
    by_contra hne
    have heq := congrArg (fun z : Pos T k => z a) hab
    have hleft : flipPos v a a = !v a := by simp [flipPos]
    have hright : flipPos v b a = v a := by simp [flipPos, hne]
    rw [hleft, hright] at heq
    cases hv : v a <;> simp [hv] at heq
  have hExtCard : (D.externalEarly v).card = E.card := by
    rw [hExt, Finset.card_image_of_injective _ hflip]
  have hIcard : I.card = (PT.tiling.P (D.G.patchOf v)).h :=
    Lane_q_s17_pool.tiling_internal_coord_card PT.tiling _ hh
  have hLateI : I ∩ L = I.filter (fun j => (D.G.classOf (flipPos v j)).isSome) := by
    ext j
    simp [L]
  have hOverlap : (I ∩ L).card ≤ 1 := by
    rw [hLateI]
    exact hQuant.geometry.internal_late_count v heven
  have hComplement := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (I ∪ L))
  have hUnion := Finset.card_union_add_card_inter I L
  have hCount : (D.externalEarly v).card + (PT.tiling.P (D.G.patchOf v)).h + L.card ≤ T.S.n k + 1 := by
    simp only [Finset.card_univ, Fintype.card_fin] at hComplement
    dsimp [E] at hExtCard
    omega
  have hCountR : ((D.externalEarly v).card : ℝ) + (PT.tiling.P (D.G.patchOf v)).h +
      (L.card : ℝ) ≤ (T.S.n k : ℝ) + 1 := by exact_mod_cast hCount
  have hLate : (D.G.r : ℝ) / 2 ≤ (L.card : ℝ) := hQuant.geometry.late_count v heven
  have hScale := hQuant.geometry.class_scale.1
  linarith

/-- Bounded-mode bulk degree drift has a fixed exponential cost rather than
a polynomial loss with the arbitrary upstream geometry constant. -/
theorem bounded_bulk_denominator_cost (n d : ℕ) (K D : ℝ)
    (hn : 0 < (n : ℝ)) (hd : d ≤ n) (hK : 0 ≤ K)
    (hSmall : 4 * K ≤ (n : ℝ)) (hD : (1 / 2 : ℝ) - K / n ≤ D) :
    Real.rpow D (-(d : ℝ)) ≤ (2 : ℝ) ^ d * Real.exp (4 * K) := by
  have hRatio : K / (n : ℝ) ≤ 1 / 4 := (div_le_iff₀ hn).2 (by linarith)
  have hDquarter : (1 / 4 : ℝ) ≤ D := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hDquarter
  have hTwoD : 0 < 2 * D := by positivity
  have hInv : (2 * D)⁻¹ - 1 ≤ 4 * K / n := by
    apply (le_div_iff₀ hn).2
    have h' : (2 * D)⁻¹ - 1 = (1 - 2 * D) / (2 * D) := by field_simp <;> ring
    rw [h']
    have hLinear : (1 - 2 * D) * (n : ℝ) ≤ 2 * K := by
      have hmul := mul_le_mul_of_nonneg_right hD hn.le
      have hcancel : K / (n : ℝ) * n = K := div_mul_cancel₀ _ hn.ne'
      nlinarith [hmul, hcancel]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hTwoD).2
    nlinarith
  have hLog : -Real.log (2 * D) ≤ 4 * K / n := by
    have hh := Real.one_sub_inv_le_log_of_pos hTwoD
    linarith
  have hDreal : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hd
  have hScale : -(d : ℝ) * Real.log (2 * D) ≤ 4 * K := by
    have hh := mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg d)
    have hnratio : (d : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn).2 hDreal
    have hc := mul_le_mul_of_nonneg_left hnratio (show 0 ≤ 4 * K by positivity)
    calc
      _ = (d : ℝ) * (-Real.log (2 * D)) := by ring
      _ ≤ (d : ℝ) * (4 * K / n) := hh
      _ = 4 * K * ((d : ℝ) / n) := by ring
      _ ≤ 4 * K := by simpa using hc
  have hLogD : Real.log (2 * D) = Real.log 2 + Real.log D :=
    Real.log_mul (by norm_num) hDpos.ne'
  change D ^ (-(d : ℝ)) ≤ _
  rw [Real.rpow_def_of_pos hDpos]
  have hExp : Real.exp ((d : ℝ) * Real.log 2) = (2 : ℝ) ^ d := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc
    _ ≤ Real.exp ((d : ℝ) * Real.log 2 + 4 * K) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hScale, hLogD]
    _ = (2 : ℝ) ^ d * Real.exp (4 * K) := by rw [Real.exp_add, hExp]

end HypercubeRamsey.Lane_sol_s17_pool
