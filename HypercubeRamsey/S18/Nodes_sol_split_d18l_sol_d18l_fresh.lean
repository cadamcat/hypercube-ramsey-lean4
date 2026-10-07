import HypercubeRamsey.S18.Nodes_sol_s18_dl
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.S18.Lane_sol_d18l_fresh

open Classical Filter
open S16 S16.Lane_sol_fix2_s16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

private theorem law_ext {Ω : Type*} [Fintype Ω] (P Q : FinLaw Ω)
    (hw : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases hw
  rfl

private theorem map_support {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (P : FinLaw A) (f : A → B) (y : B)
    (hy : (FinLaw.map P f).w y ≠ 0) : ∃ x, f x = y ∧ P.w x ≠ 0 := by
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  by_cases heq : f x = y
  · exact ⟨x, heq, by simpa only [if_pos heq] using hx⟩
  · simp only [if_neg heq, ne_eq, not_true_eq_false] at hx

private theorem map_equiv_weight {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (P : FinLaw A) (e : A ≃ B) (y : B) :
    (FinLaw.map P e).w y = P.w (e.symm y) := by
  change (∑ x, if e x = y then P.w x else 0) = _
  simp only [Equiv.apply_eq_iff_eq_symm_apply]
  simp

theorem fresh_supported_encoding (physical : PhysicalFreshCertificate G F)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (s : F.State C) (hs : (F.fresh C pool).w s ≠ 0) :
    ∃ W a ys,
      physical.calibration.encode C (W, a, ys) = s ∧
      (physical.calibration.gatedHistory C pool).w W ≠ 0 ∧
      (physical.calibration.binSampler C pool W).w a ≠ 0 ∧
      (physical.calibration.labelSampler C pool W a).w ys ≠ 0 ∧
      (physical.raw.history C).w (physical.construction.histories C W) ≠ 0 := by
  rw [physical.calibration.fresh_eq C pool ht] at hs
  obtain ⟨⟨W, a, ys⟩, heq, hmass⟩ := map_support _ _ s hs
  have hw : (physical.calibration.gatedHistory C pool).w W ≠ 0 :=
    (mul_ne_zero_iff.mp hmass).1
  have ha := (mul_ne_zero_iff.mp ((mul_ne_zero_iff.mp hmass).2)).1
  have hy := (mul_ne_zero_iff.mp ((mul_ne_zero_iff.mp hmass).2)).2
  have hhist := (Lane_sol_s16_prod1.cond_support _ _ _ W
    (show (FinLaw.cond (physical.calibration.history C)
      (physical.calibration.gate C pool) (physical.calibration.gate_pos C pool ht)).w W ≠ 0 by
      simpa only [← physical.calibration.gated_eq C pool ht] using hw)).2
  rw [physical.construction.history_eq C,
    map_equiv_weight _ (physical.construction.histories C).symm W] at hhist
  exact ⟨W, a, ys, heq, hw, ha, hy, hhist⟩

theorem internal_neighbor_cell (R : CellRawData G) (v : Pos T k)
    (a : Fin (T.S.n k)) (ha : a ∈ PT.tiling.Icoord (G.patchOf v)) :
    G.cellOf (flipPos v a) = G.cellOf v := by
  let C := G.cellOf v
  let sz := (R.cellWords C).symm ⟨v, rfl⟩
  have hsite : (R.cellWords C (sz.1, sz.2)).1 = v :=
    congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v, rfl⟩)
  have hamem : a ∈ Finset.univ.image (R.axis C) := by
    rw [R.axes_eq C]
    simpa only [C, G.cellOf_patch v] using ha
  obtain ⟨j, _, haxis⟩ := Finset.mem_image.mp hamem
  have hc := (R.cellWords C (sz.1, flipPos sz.2 j)).2
  rw [R.word_flip, hsite, haxis] at hc
  exact hc

theorem raw_prior_shape (hPT : PT.Valid) (R : CellRawData G) (hR : R.SourceValid)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (ys : OddCellRole G C → Fin (T.S.N k))
    (v : Pos T k) (hc : G.cellOf v = C) (he : IsEvenRole v)
    (hnorm : (∑ x, R.rawPrior C W ys v x) = 1) :
    (if PT.tiling.mode.isCluster then
      ∀ x, (T.S.N k : ℝ) * R.rawPrior C W ys v x ≤
        (2 : ℝ) ^ (PT.tiling.P (G.cellPatch C)).h *
          Real.exp (-500 * PT.tiling.gain (G.cellPatch C))
     else ∃ q ∈ PT.activeVertices, ∀ x, R.rawPrior C W ys v x =
      if x ∈ PT.mesh.corner q (G.cellPatch C) then
        1 / ((PT.mesh.corner q (G.cellPatch C)).card : ℝ) else 0) ∧
    ∃ q ∈ PT.activeVertices, ∀ x,
      x ∉ PT.mesh.corner q (G.cellPatch C) → R.rawPrior C W ys v x = 0 := by
  rcases hR with ⟨hMode, hUniform, hSource⟩ | ⟨hDirect, hSource⟩
  · have hCluster : PT.tiling.mode.isCluster := by simp [hMode, Mode.isCluster]
    obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let sz := (R.cellWords C).symm ⟨v, hc⟩
    have hv : (R.cellWords C (sz.1, sz.2)).1 = v :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply ⟨v, hc⟩)
    have heword : IsEvenRole sz.2 := (R.word_parity hCluster C sz.1 sz.2).mp (by rw [hv]; exact he)
    let w : EvenRole PT.tiling (G.cellPatch C) := ⟨sz.2, heword⟩
    obtain ⟨fallback, _⟩ := hPT.tiling_valid.patch_nonempty (G.cellPatch C) |>.2
    have hprior : R.rawPrior C W ys v =
        S.σ w (records sz.1 (W sz.1)) (nbrLabels w.1 (R.wordLabel C ys sz.1 fallback)) := by
      rw [← hv]
      exact hPrior W sz.1 w ys fallback
    have hslice := Lane_sol_s16_prod1.pi_support
      (fun s => FinLaw.cond (R.sliceLaw C s) (R.slicePass C s) (R.slice_pos C s)) W hW sz.1
    have hraw := (Lane_sol_s16_prod1.cond_support _ _ _ _ hslice).2
    rw [hLaw sz.1, map_equiv_weight _ (records sz.1).symm] at hraw
    have hrec : 0 < (S.recLaw PT.parameter).w (records sz.1 (W sz.1)) :=
      lt_of_le_of_ne ((S.recLaw PT.parameter).nonneg _) hraw.symm
    have hnonzero : S.σ w (records sz.1 (W sz.1))
        (nbrLabels w.1 (R.wordLabel C ys sz.1 fallback)) ≠ 0 := by
      intro hz
      rw [hprior, hz] at hnorm
      simp at hnorm
    obtain ⟨q, hactive, hsupport⟩ := S.σ_support w _ _ hnonzero
    have hq : q ∈ PT.activeVertices := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive PT.parameter hrec⟩
    rw [if_pos hCluster]
    refine ⟨?_, q, hq, ?_⟩
    · intro x
      rw [hprior]
      exact S.σ_cap w _ _ x
    · intro x hx
      by_contra hn
      rw [hprior] at hn
      exact hx (hsupport x hn).1
  · obtain ⟨hInj, hVal, hPass, hQ, hTrim, hU, hEnv, hPrior⟩ := hSource C
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (hPT.direct_single_corner hDirect)
    have hqmem : q ∈ PT.activeVertices := by rw [hq]; simp
    have hEnvEq : PT.envelope (G.cellPatch C) = PT.mesh.corner q (G.cellPatch C) := by
      rw [hPT.envelope_eq, hq]
      simp
    have hp : ∀ x, R.rawPrior C W ys v x =
        if x ∈ PT.mesh.corner q (G.cellPatch C) then
          1 / ((PT.mesh.corner q (G.cellPatch C)).card : ℝ) else 0 := by
      intro x
      rw [hPrior W ys v hc he]
      simp only [Law.unifCore, hEnvEq, one_div]
    rw [if_neg hDirect]
    exact ⟨⟨q, hqmem, hp⟩, q, hqmem, fun x hx => by rw [hp x, if_neg hx]⟩

theorem physical_prior_shape (hPT : PT.Valid)
    (physical : PhysicalFreshCertificate G F)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool)
    (s : F.State C) (hs : (F.fresh C pool).w s ≠ 0)
    (v : Pos T k) (hc : G.cellOf v = C) (he : IsEvenRole v)
    (hnorm : (∑ x, F.prior C s v x) = 1) :
    (if PT.tiling.mode.isCluster then
      ∀ x, (T.S.N k : ℝ) * F.prior C s v x ≤
        (2 : ℝ) ^ (PT.tiling.P (G.cellPatch C)).h *
          Real.exp (-500 * PT.tiling.gain (G.cellPatch C))
     else ∃ q ∈ PT.activeVertices, ∀ x, F.prior C s v x =
      if x ∈ PT.mesh.corner q (G.cellPatch C) then
        1 / ((PT.mesh.corner q (G.cellPatch C)).card : ℝ) else 0) ∧
    ∃ q ∈ PT.activeVertices, ∀ x,
      x ∉ PT.mesh.corner q (G.cellPatch C) → F.prior C s v x = 0 := by
  obtain ⟨W, a, ys, heq, hW, ha, hy, hraw⟩ := fresh_supported_encoding physical C pool ht s hs
  have hp : F.prior C s v = physical.raw.rawPrior C
      (physical.construction.histories C W) ys v := by
    rw [← heq]
    exact physical.construction.prior_eq C pool W a ys v ht hW ha hy hc he
  rw [hp] at hnorm ⊢
  exact raw_prior_shape hPT physical.raw physical.source_valid C _ hraw ys v hc he hnorm

theorem uniform_univ_pi {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (x : ∀ i, Ω i) :
    FinLaw.uniform Finset.univ ⟨x, Finset.mem_univ _⟩ =
      FinLaw.pi (fun i => FinLaw.uniform Finset.univ ⟨x i, Finset.mem_univ _⟩) := by
  apply law_ext
  funext ω
  simp [FinLaw.uniform, FinLaw.pi, Fintype.card_pi, Nat.cast_prod,
    Finset.prod_div_distrib]

theorem pi_coordinate_map {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : I) :
    FinLaw.map (FinLaw.pi P) (fun ω => ω i) = P i := by
  let base : ∀ j, Ω j := Classical.choice (S16.Lane_q_s16_comp2.nonempty_of_finLaw (FinLaw.pi P))
  apply law_ext
  funext y
  rw [S16.Lane_q_s16_comp2.map_weight_eq_pr]
  let x := Function.update base i y
  have hevent : (fun ω : ∀ j, Ω j => ω i = y) =
      (fun ω => ∀ j ∈ ({i} : Finset I), ω j = x j) := by
    funext ω
    simp [x]
  rw [hevent, S16.Lane_q_s16_comp2.pi_pr_cylinder]
  simp [x]

theorem iid_marginal_eq (hPools : (permPools G).Nonempty)
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty)
    (C : G.Cell) :
    FinLaw.map (iidPoolLaw G hPools) (fun P => P C) = iidCellPoolLaw C (hBins C) := by
  let x := hPools.choose
  have hglobal : iidPoolLaw G hPools =
      FinLaw.pi (fun C => iidCellPoolLaw C (hBins C)) := by
    apply law_ext
    funext P
    simp [iidPoolLaw, iidCellPoolLaw, FinLaw.uniform, FinLaw.pi,
      Fintype.card_pi, Fintype.card_fun, Nat.cast_prod, Nat.cast_pow,
      Finset.prod_inv_distrib]
  rw [hglobal, pi_coordinate_map]

theorem diagnostic_pool_eq (physical : PhysicalFreshCertificate G F)
    (C : G.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (G.cellPatch C))).Nonempty) :
    (physical.diagnostics.diagnostic C).poolLaw = iidCellPoolLaw C hBins := by
  apply law_ext
  funext P
  change (∏ slot, ((physical.diagnostics.diagnostic C).iidSlotLaw slot).w (P slot)) = _
  simp [iidCellPoolLaw, FinLaw.pi, FinLaw.uniform,
    (physical.diagnostics.diagnostic C).uniform_slots]

theorem eventually_typical_failure (T : Stage) :
    ∀ᶠ k in atTop, Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-3) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hs := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hn
  have he := (tendsto_exp_div_rpow_atTop 6).comp hs
  filter_upwards [he.eventually_ge_atTop 1, hn.eventually_gt_atTop 0] with k hk hpos
  have hpowpos : 0 < Real.rpow (Real.rpow (T.S.n k : ℝ) (1 / 2)) 6 :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hpos _) _
  have hpow : Real.rpow (Real.rpow (T.S.n k : ℝ) (1 / 2)) 6 =
      Real.rpow (T.S.n k : ℝ) 3 := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hpos.le]
    norm_num
  have hlarge : Real.rpow (T.S.n k : ℝ) 3 ≤
      Real.exp (Real.rpow (T.S.n k : ℝ) (1 / 2)) := by
    rw [← hpow]
    simpa using (le_div_iff₀ hpowpos).mp hk
  simp only [Real.rpow_eq_pow]
  rw [Real.exp_neg, Real.rpow_neg hpos.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hpos _) hlarge

theorem physical_singleton (physical : PhysicalFreshCertificate G F)
    (hPools : (permPools G).Nonempty)
    (hSmall : Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-3))
    (b : Pos T k) (hOdd : ¬ IsEvenRole b) (y : Fin (T.S.N k)) :
    let C := G.cellOf b
    let law := FinLaw.map (iidPoolLaw G hPools) (fun P => P C)
    ∃ hTypical : 0 < ∑ P ∈ Finset.univ.filter (F.typical C), law.w P,
      (FinLaw.bind (FinLaw.cond law (Finset.univ.filter (F.typical C)) hTypical)
        (F.fresh C)).pr (fun Ps => F.label C Ps.2 b = y) ≤
        (1 + 2 * Real.rpow (T.S.n k : ℝ) (-3)) * (PT.π (G.patchOf b)).w y := by
  rcases physical with ⟨hκ, K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, S, hTypicalEq, hGateEq, Cal, link, hF, hFailure, hPositive⟩
  subst G
  let hBins (C : H.geom.Cell) :
      (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty :=
    ⟨Classical.choice (Ds.diagnostic C).bins_nonempty, Finset.mem_univ _⟩
  let C := H.geom.cellOf b
  have hDiag : (Ds.diagnostic C).poolLaw = iidCellPoolLaw C (hBins C) := by
    apply law_ext
    funext P
    simp [CellPoolDiagnostics.poolLaw, iidCellPoolLaw, FinLaw.pi, FinLaw.uniform,
      (Ds.diagnostic C).uniform_slots]
  have hMarg := iid_marginal_eq hPools hBins C
  have htyp : 0 < ∑ P ∈ Finset.univ.filter (F.typical C),
      (iidCellPoolLaw C (hBins C)).w P := by
    rw [← hDiag]
    exact hPositive C
  refine ⟨?_, ?_⟩
  · change 0 < ∑ P ∈ Finset.univ.filter (F.typical C),
      (FinLaw.map (iidPoolLaw H.geom hPools) (fun P => P C)).w P
    rw [hMarg]
    exact htyp
  have hcond : ∀ (P Q : FinLaw (F.Pool C)) (heq : P = Q)
      (hP : 0 < ∑ p ∈ Finset.univ.filter (F.typical C), P.w p)
      (hQ : 0 < ∑ p ∈ Finset.univ.filter (F.typical C), Q.w p),
      FinLaw.cond P (Finset.univ.filter (F.typical C)) hP =
        FinLaw.cond Q (Finset.univ.filter (F.typical C)) hQ := by
    intro P Q heq hP hQ
    subst Q
    rfl
  rw [hcond _ _ hMarg _ htyp, S16.Lane_q_s16_comp2.bind_pr]
  have hfail : (iidCellPoolLaw C (hBins C)).pr (fun P => ¬ F.typical C P) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) / 2 := by
    rw [← hDiag]
    simpa only [Ds.exponent_half, Real.rpow_eq_pow] using hFailure C
  have hresult := (fresh_singleton_comparison hκ Q H Cal hF C (hBins C)
    (Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) / 2) (by positivity) hfail
    (by simpa only [Real.rpow_eq_pow] using div_le_div_of_nonneg_right hSmall (by norm_num : (0 : ℝ) ≤ 2))
    htyp (H.geom.patchOf b) b rfl rfl hOdd y).2
  simpa only [Real.rpow_eq_pow] using hresult

theorem pipeline_base_mean (hPT : PT.Valid) (hMass : ProfileCornerMass PT)
    {C : G.Cell} {v : Pos T k} (P : FreshPriorPipeline F C v)
    (hSource : FreshPriorSourceValid P) (y : Fin (T.S.N k)) :
    P.baseExperiment.expect (fun σ => max 0 (σ y)) ≤
      max (rowMeanConstant κ) 2 / ((PT.tiling.P (G.cellPatch C)).M : ℝ) := by
  rcases hSource with ⟨hMode, S, hS, w, loc, records, roleAt, hRole, hPrior, hJoint⟩ |
    ⟨hDirect, hEnv, hPrior⟩
  · let B := solverBasePriorExperiment S w
    let f (ω : P.baseExperiment.State) := (records ω.1, fun j => ω.2.2 (roleAt j))
    let g (ω : B.State) := (ω.1, nbrLabels w.1 ω.2.2)
    let test (z : (∀ r, S.Val r) × InternalLabels PT.tiling (G.cellPatch C)) :=
      max 0 (S.σ w z.1 z.2 y)
    have hmaps : FinLaw.map P.baseExperiment.law f = FinLaw.map B.law g := by
      apply law_ext
      funext z
      rcases z with ⟨W, ys⟩
      rw [S16.Lane_q_s16_comp2.map_weight_eq_pr,
        S16.Lane_q_s16_comp2.map_weight_eq_pr]
      simpa only [f, g, B, Prod.mk.injEq] using hJoint W ys
    have hEq : P.baseExperiment.expect (fun σ => max 0 (σ y)) =
        B.expect (fun σ => max 0 (σ y)) := by
      calc
        P.baseExperiment.expect (fun σ => max 0 (σ y)) = P.baseExperiment.law.E (fun ω => test (f ω)) := by
          unfold PriorExperiment.expect
          apply congrArg P.baseExperiment.law.E
          funext ω
          change max 0 (P.rawPrior ω.1 ω.2.2 y) = _
          rw [hPrior]
        _ = (FinLaw.map P.baseExperiment.law f).E test :=
          (S16.Lane_q_s16_comp2.map_expect _ f test).symm
        _ = (FinLaw.map B.law g).E test := by rw [hmaps]
        _ = B.expect (fun σ => max 0 (σ y)) :=
          S16.Lane_q_s16_comp2.map_expect _ g test
    rw [hEq]
    have hmean : B.expect (fun σ => max 0 (σ y)) ≤
        rowMeanConstant κ / ((PT.tiling.P (G.cellPatch C)).M : ℝ) := by
      change (FinLaw.bind (S.recLaw PT.parameter) S.refLaw).E
        (fun ω => max 0 (S.σ w ω.1 (nbrLabels w.1 ω.2.2) y)) ≤ _
      rw [S16.Lane_q_s16_comp2.bind_expect]
      simp only [max_eq_right (S.σ_nonneg _ _ _ _)]
      exact S.σ_mean PT.parameter w y
    exact hmean.trans (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  · obtain ⟨q, hq⟩ := Finset.card_eq_one.mp (hPT.direct_single_corner hDirect)
    have hqmem : q ∈ PT.activeVertices := by rw [hq]; simp
    have hEnvEq : PT.envelope (G.cellPatch C) = PT.mesh.corner q (G.cellPatch C) := by
      rw [hPT.envelope_eq, hq]
      simp
    have hEnvPos : 0 < ((PT.envelope (G.cellPatch C)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hEnv
    have hM : 0 < ((PT.tiling.P (G.cellPatch C)).M : ℝ) := by
      have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
      have hS : (0 : ℝ) < PT.tiling.S := by linarith [hPT.tiling_valid.S_lower]
      have hp : 0 < (2 : ℝ) ^ (-((PT.tiling.P (G.cellPatch C)).ℓ : ℤ)) := by positivity
      have hh := (lt_div_iff₀ hS).mp (hPT.tiling_valid.dyadic_mass_upper (G.cellPatch C))
      nlinarith [mul_pos hp hS]
    have hMass' : ((PT.tiling.P (G.cellPatch C)).M : ℝ) ≤
        2 * (PT.envelope (G.cellPatch C)).card := by
      rw [hEnvEq]
      exact hMass _ _ hqmem
    have hcap : ∀ W ys, max 0 (P.rawPrior W ys y) ≤
        2 / ((PT.tiling.P (G.cellPatch C)).M : ℝ) := by
      intro W ys
      rw [hPrior]
      change max 0 (if y ∈ PT.envelope (G.cellPatch C) then
        ((PT.envelope (G.cellPatch C)).card : ℝ)⁻¹ else 0) ≤ _
      split_ifs
      · rw [max_eq_right (inv_nonneg.mpr hEnvPos.le)]
        rw [← one_div]
        exact (div_le_div_iff₀ hEnvPos hM).mpr (by simpa using hMass')
      · simp
        exact div_nonneg (by norm_num) hM.le
    have hmean : P.baseExperiment.expect (fun σ => max 0 (σ y)) ≤
        2 / ((PT.tiling.P (G.cellPatch C)).M : ℝ) := by
      unfold PriorExperiment.expect
      calc
        _ ≤ P.baseExperiment.law.E (fun _ => 2 / ((PT.tiling.P (G.cellPatch C)).M : ℝ)) :=
          S16.Lane_q_s16_comp2.expect_le _ _ _ (fun ω => hcap ω.1 ω.2.2)
        _ = _ := by simp [FinLaw.E, ← Finset.sum_mul, P.baseExperiment.law.sum_one]
    exact hmean.trans (div_le_div_of_nonneg_right (le_max_right _ _) hM.le)

theorem physical_prior_mean_bound (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
      (G : LowGeom PT) (F : FreshCell G) (physical : PhysicalFreshCertificate G F)
      (hPools : (permPools G).Nonempty), ProfileCornerMass PT →
      ∀ v y, IsEvenRole v →
        (iidPoolLaw G hPools).E (fun pools =>
          if F.typical (G.cellOf v) (pools (G.cellOf v)) then
            (F.fresh (G.cellOf v) (pools (G.cellOf v))).E
              (fun s => F.prior (G.cellOf v) s v y) else 0) ≤
        (100 * κ.Kcell * (κ.Kp : ℝ)) * max (rowMeanConstant κ) 2 /
          ((PT.tiling.P (G.patchOf v)).M : ℝ) := by
  obtain ⟨n₀, hpipeline⟩ := fresh_prior_pipeline_exists hκ
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop n₀] with k hn
  intro PT hPT G F physical hPools hMass v y he
  rcases physical with ⟨hκ', K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, S, hTypicalEq, hGateEq, Cal, link, hF, hFailure, hPositive⟩
  subst G
  let C := H.geom.cellOf v
  let hBins (C : H.geom.Cell) :
      (Finset.univ : Finset (Bin PT.tiling (H.geom.cellPatch C))).Nonempty :=
    ⟨Classical.choice (Ds.diagnostic C).bins_nonempty, Finset.mem_univ _⟩
  obtain ⟨P, hSource, hBaseEq⟩ := hpipeline Q H hScale R Perm K Ds S F Cal hR hn hPerm
    hTypicalEq hGateEq link C v rfl he
  have hCompare := fresh_internal_prior_comparison hκ Q H hBins C v rfl he P hSource
    (fun σ => max 0 (σ y)) (fun _ => le_max_left _ _) (by simp)
  have hMean := pipeline_base_mean hPT hMass P hSource y
  have hKcell : 0 ≤ κ.Kcell := by
    exact (lt_of_lt_of_le (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big).le
  have hCoefficient : 0 ≤ 100 * κ.Kcell * (κ.Kp : ℝ) := by positivity
  have hMain := hCompare.trans (mul_le_mul_of_nonneg_left hMean hCoefficient)
  rw [H.geom.cellOf_patch v] at hMain
  have hMarg := iid_marginal_eq hPools hBins C
  have hIntegral : (iidPoolLaw H.geom hPools).E (fun pools =>
      if F.typical C (pools C) then (F.fresh C (pools C)).E
        (fun s => F.prior C s v y) else 0) =
      freshPriorTest F hBins C v rfl he (fun σ => max 0 (σ y)) := by
    let testPool (pool : F.Pool C) := if F.typical C pool then
      (F.fresh C pool).E (fun s => F.prior C s v y) else 0
    have hMap := S16.Lane_q_s16_comp2.map_expect (iidPoolLaw H.geom hPools)
      (fun P => P C) testPool
    change (iidPoolLaw H.geom hPools).E (fun pools => testPool (pools C)) = _
    rw [← hMap, hMarg]
    unfold freshPriorTest
    apply congrArg (iidCellPoolLaw C (hBins C)).E
    funext pool
    by_cases ht : F.typical C pool
    · simp only [testPool, ht, ite_true]
      apply congrArg (F.fresh C pool).E
      funext s
      exact (max_eq_right (hF.prior_nonneg C s v y)).symm
    · simp [testPool, ht]
  rw [hIntegral]
  convert hMain using 1 <;> ring

theorem admissible_increase_Kcell (hκ : κ.Admissible) (L : ℝ) (hL : κ.Kcell ≤ L) :
    ({κ with Kcell := L} : CConsts).Admissible := by
  refine { hκ with Kcell_big := hκ.Kcell_big.trans hL }

theorem thresholds_increase_Kcell (hThresholds : LateThresholds κ) (L : ℝ) :
    LateThresholds ({κ with Kcell := L} : CConsts) := hThresholds

/-- The frozen numerical contracts do not entail the last scalar bound
needed by the exported Section 16 mean-comparison route. This is a scalar
contract obstruction, not a counterexample to the full D18_L_prior_mean. -/
theorem mean_coefficient_not_controlled (hκ : κ.Admissible)
    (hThresholds : LateThresholds κ) :
    ∃ κ' : CConsts, κ'.Admissible ∧ LateThresholds κ' ∧
      κ'.KB < (100 * κ'.Kcell * (κ'.Kp : ℝ)) * max (rowMeanConstant κ') 2 := by
  have hKp : (0 : ℝ) < κ.Kp := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 40) hκ.bucket.1)
  let c : ℝ := 100 * (κ.Kp : ℝ) * max (rowMeanConstant κ) 2
  have hc : 0 < c := by
    dsimp [c]
    have hh : (0 : ℝ) < max (rowMeanConstant κ) 2 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    positivity
  let L := max κ.Kcell (κ.KB / c + 1)
  let κ' : CConsts := {κ with Kcell := L}
  refine ⟨κ', admissible_increase_Kcell hκ L (le_max_left _ _),
    thresholds_increase_Kcell hThresholds L, ?_⟩
  change κ.KB < (100 * L * (κ.Kp : ℝ)) * max (rowMeanConstant κ) 2
  have hL : κ.KB / c + 1 ≤ L := le_max_right _ _
  have hm := mul_le_mul_of_nonneg_left hL hc.le
  have hcancel : c * (κ.KB / c + 1) = κ.KB + c := by
    field_simp [ne_of_gt hc]
  calc
    κ.KB < κ.KB + c := lt_add_of_pos_right _ hc
    _ = c * (κ.KB / c + 1) := hcancel.symm
    _ ≤ c * L := hm
    _ = _ := by dsimp [c]; ring

end HypercubeRamsey.S18.Lane_sol_d18l_fresh
