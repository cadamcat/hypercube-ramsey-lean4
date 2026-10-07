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

end HypercubeRamsey.Lane_sol_s17_pool
