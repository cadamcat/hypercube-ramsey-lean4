import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_fresh
import HypercubeRamsey.S17.Nodes

namespace HypercubeRamsey.S18.Lane_sol_d18l_up

open Classical Filter
open S16 S16.Lane_sol_fix2_s16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT} {F : FreshCell G}

theorem initial_pr_pool (E : LateEncoding F) (A : (∀ C, F.Pool C) → Prop) :
    E.permLaw.pr (fun x => A x.1) = E.poolLaw.pr A := by
  rw [LateEncoding.permLaw, LateEncoding.initialLaw, S16.Lane_q_s16_comp2.bind_pr]
  unfold FinLaw.E FinLaw.pr
  apply Finset.sum_congr rfl
  intro P _
  by_cases h : A P
  · simp only [h, if_true]
    rw [(tapeLaw F E.Ts).sum_one, mul_one]
  · simp [h]

theorem pool_cond_pr {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (pin A : Ω → Prop)
    (hp : 0 < ∑ x ∈ Finset.univ.filter pin, P.w x) :
    (FinLaw.cond P (Finset.univ.filter pin) hp).pr A =
      P.pr (fun x => pin x ∧ A x) / P.pr pin := by
  have hmass : (∑ x ∈ Finset.univ.filter pin, P.w x) = P.pr pin := by
    rw [Finset.sum_filter]
    rfl
  unfold FinLaw.pr FinLaw.cond
  rw [Finset.sum_div]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmass]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hpin : pin x <;> by_cases ha : A x <;> simp [hpin, ha, FinLaw.pr]

theorem physical_typical_tail (physical : PhysicalFreshCertificate G F)
    (hpools : (permPools G).Nonempty) (C : G.Cell) :
    (permPoolLaw G hpools).pr (fun P => ¬ F.typical C (P C)) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ∧
    ∀ (s : CellSlot G) (b : Bin PT.tiling (G.cellPatch s.1))
      (hpin : 0 < ∑ P ∈ poolPinEvent s b, (permPoolLaw G hpools).w P),
      (FinLaw.cond (permPoolLaw G hpools) (poolPinEvent s b) hpin).pr
        (fun P => ¬ F.typical C (P C)) ≤
          Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) := by
  rcases physical with ⟨hκ, K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, S, hTypicalEq, hGateEq, Cal, link, hF, hFailure, hPositive⟩
  subst G
  have ht (P : F.Pool C) : F.typical C P ↔ (Ds.diagnostic C).typical P :=
    (link.typical_eq C P).trans (hTypicalEq C P)
  obtain ⟨hu, hp⟩ := pool_typicality_concentration_after_permission
    (Ds.diagnostic C) (Ds.concentration C)
  obtain ⟨hraw, hpinned⟩ := pool_typicality_permutation_transfer hκ Q H C
    (Ds.diagnostic C) hu hp
  constructor
  · simpa only [ht, Ds.exponent_half, Real.rpow_eq_pow] using hraw
  · intro s b hpin
    simpa only [ht, Ds.exponent_half, Real.rpow_eq_pow] using hpinned s b hpin

theorem physical_clean_prior (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F)
    (v : Pos T k) (P : F.Pool (G.cellOf v)) (s : F.State (G.cellOf v))
    (heven : IsEvenRole v) (ht : F.typical (G.cellOf v) P)
    (hs : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).stateValid
      (G.cellOf v) P s) :
    (Lane_sol_s18_dl.physical_list_context hPT hLow physical).CleanInitialPrior v
      (F.prior (G.cellOf v) s v) := by
  have hn := (hs.1.2 v rfl heven).1
  obtain ⟨hshape, q, hq, hsupport⟩ := Lane_sol_d18l_fresh.physical_prior_shape
    hPT physical (G.cellOf v) P ht s (ne_of_gt hs.2) v rfl heven hn
  simp only [G.cellOf_patch] at hshape hsupport
  dsimp only [ListGateContext.CleanInitialPrior, Lane_sol_s18_dl.physical_list_context]
  refine ⟨physical.fresh_spec.prior_nonneg _ _ v, hn, ?_⟩
  by_cases hc : PT.tiling.mode.isCluster
  · refine ⟨q, hq, ?_, ?_, ?_⟩
    · intro x hx
      by_contra hnot
      exact hx (hsupport x hnot)
    · intro _
      simpa only [if_pos hc] using hshape
    · intro h
      exact (h hc).elim
  · obtain ⟨a, ha, heq⟩ := by simpa only [if_neg hc] using hshape
    refine ⟨a, ha, ?_, ?_, ?_⟩
    · intro x hx
      by_contra hnot
      exact hx (by rw [heq x, if_neg hnot])
    · intro h
      exact (hc h).elim
    · intro _
      exact ⟨Lane_sol_fix_corner.active_corner_card_lower_waste hPT _ a ha, heq⟩

theorem physical_singleton_bound (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F)
    (C : G.Cell) (P : F.Pool C) (b : Pos T k) (y : Fin (T.S.N k))
    (ht : F.typical C P) (hb : G.cellOf b = C) (ho : ¬ IsEvenRole b) :
    let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
    (F.fresh C P).pr (fun s => F.label C s b = y) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) * D.slotFactor b *
        (PT.π (G.patchOf b)).w y *
          (if y ∈ D.permittedLabels C P b then 1 else 0) := by
  rcases physical with ⟨hκ, K16, Q, H, hG, hUniform, hScale, R, hR,
    Perm, hPerm, K, c0, Ds, S, hTypicalEq, hGateEq, Cal, link, hF, hFailure, hPositive⟩
  subst G
  have hTarget := fresh_singleton_target_bound hκ Q H Cal C P ht b y
    (H.geom.patchOf b) hb ho rfl
  have hBound := fresh_singleton_fixed_pool_node hκ Q H Cal C P ht b y
    (H.geom.patchOf b) hb ho hTarget
  dsimp only
  simpa only [Lane_sol_s18_dl.physical_list_context, Finset.mem_filter,
    hb, Real.rpow_eq_pow, mul_div_assoc, and_comm] using hBound

theorem local_typical_tail (D : ListGateContext κ T k PT)
    (μ : FinLaw D.PoolAssignment) (ε : ℝ) (hε : 0 ≤ ε)
    (hTail : ∀ C, μ.pr (fun P => ¬ D.F.typical C (P C)) ≤ ε)
    (v : Pos T k) :
    μ.pr (fun P => ¬ D.LocalPoolsTypical v P) ≤ ((T.S.n k : ℝ) + 1) * ε := by
  have hEq : (fun P => ¬ D.LocalPoolsTypical v P) =
      (fun P => ∃ C ∈ D.scopeCells v, ¬ D.F.typical C (P C)) := by
    funext P
    apply propext
    simp only [ListGateContext.LocalPoolsTypical, not_forall, exists_prop]
  rw [hEq]
  have hUnion := Lane_q_s17_pool.pr_exists_finset_le μ (D.scopeCells v)
    (fun C P => ¬ D.F.typical C (P C))
  have hscope : (D.scopeCells v).card ≤ T.S.n k + 1 := by
    unfold ListGateContext.scopeCells
    have hc := Finset.card_union_le ({D.G.cellOf v} : Finset D.G.Cell)
      ((D.externalEarly v).image D.G.cellOf)
    have hi := Finset.card_image_le (s := D.externalEarly v) (f := D.G.cellOf)
    have he := Lane_q_s17_pool.externalEarly_card_le D v
    simp only [Finset.card_singleton] at hc
    omega
  calc
    _ ≤ ∑ C ∈ D.scopeCells v, μ.pr (fun P => ¬ D.F.typical C (P C)) := hUnion
    _ ≤ ∑ C ∈ D.scopeCells v, ε := Finset.sum_le_sum fun C _ => hTail C
    _ = ((D.scopeCells v).card : ℝ) * ε := by simp
    _ ≤ ((T.S.n k : ℝ) + 1) * ε := by
      apply mul_le_mul_of_nonneg_right _ hε
      exact_mod_cast hscope

theorem rpow_R_le_P (hκ : κ.Admissible) (hn : 1 ≤ (T.S.n k : ℝ))
    (m : ℕ) :
    Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * m / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * m / 2)) := by
  have hp : 1 ≤ κ.P := by have := hκ.P_big.2; omega
  have hPR : κ.P ≤ κ.R := by rw [hκ.R_eq]; nlinarith
  have hPRr : (κ.P : ℝ) ≤ κ.R := by exact_mod_cast hPR
  apply Real.rpow_le_rpow_of_exponent_le hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

theorem eventually_typical_tail (T : Stage) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ k in atTop, Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ)
        (-(P * (initialResamplingRounds T k : ℝ) / 2)) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hl := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).const_mul_left P
  have hev := hn.eventually (hl.def (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1,
    hn.eventually_gt_atTop 0] with k he hlog hnpos
  simp only [Function.comp_apply] at he hlog
  have hlogpos : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hroom : P * Real.log (T.S.n k : ℝ) ^ 3 ≤
      Real.rpow (T.S.n k : ℝ) (1 / 2) := by
    have hlp : 0 ≤ Real.log (T.S.n k : ℝ) ^ (3 : ℝ) :=
      Real.rpow_nonneg hlogpos _
    have hnp : 0 ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg hnpos.le _
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hP hlp),
      abs_of_nonneg hnp, one_mul] at he
    simpa only [Real.rpow_ofNat, Real.rpow_eq_pow] using he
  have hceil : (initialResamplingRounds T k : ℝ) ≤
      2 * Real.log (T.S.n k : ℝ) ^ 2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg (Real.log (T.S.n k : ℝ)))
    dsimp only [initialResamplingRounds]
    nlinarith
  have hcost : P * (initialResamplingRounds T k : ℝ) / 2 * Real.log (T.S.n k : ℝ) ≤
      Real.rpow (T.S.n k : ℝ) (1 / 2) := by
    have hprod := mul_le_mul_of_nonneg_left hceil (mul_nonneg hP hlogpos)
    nlinarith [hroom]
  simp only [Real.rpow_eq_pow] at hcost
  simp only [Real.rpow_eq_pow]
  conv_rhs => rw [Real.rpow_def_of_pos hnpos]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem eventually_local_typical_tail (T : Stage) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ k in atTop, ((T.S.n k : ℝ) + 1) *
      Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
        Real.rpow (T.S.n k : ℝ) (-(R * (initialResamplingRounds T k : ℝ))) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [eventually_typical_tail T (4 * (R + 1)) (by positivity),
    hn.eventually_ge_atTop 2, (Real.tendsto_log_atTop.comp hn).eventually_ge_atTop 1]
    with k hsmall hk hlog
  simp only [Function.comp_apply] at hlog
  have hnpos : (0 : ℝ) < T.S.n k := by linarith
  have hm : (1 : ℝ) ≤ initialResamplingRounds T k := by
    have hceil := Nat.le_ceil (Real.log (T.S.n k : ℝ) ^ 2)
    change (1 : ℝ) ≤ ⌈Real.log (T.S.n k : ℝ) ^ 2⌉₊
    nlinarith
  have hcoef : (T.S.n k : ℝ) + 1 ≤ (T.S.n k : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ (T.S.n k : ℝ) ^ 2 *
        Real.rpow (T.S.n k : ℝ) (-(4 * (R + 1) * (initialResamplingRounds T k : ℝ) / 2)) :=
      mul_le_mul hcoef hsmall (Real.exp_nonneg _)
        (by positivity)
    _ = Real.rpow (T.S.n k : ℝ)
        (2 - 2 * (R + 1) * (initialResamplingRounds T k : ℝ)) := by
      simp only [Real.rpow_eq_pow]
      rw [show (T.S.n k : ℝ) ^ 2 = (T.S.n k : ℝ) ^ (2 : ℝ) by norm_num,
        ← Real.rpow_add hnpos]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have hprod := mul_le_mul_of_nonneg_left hm (show 0 ≤ R + 2 by linarith)
      nlinarith

theorem physical_local_typical_tails (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (physical : PhysicalFreshCertificate G F) (hpools : (permPools G).Nonempty)
    (hsmall : ((T.S.n k : ℝ) + 1) * Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k))) :
    let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
    (∀ v, (permPoolLaw G hpools).pr (fun P => ¬ D.LocalPoolsTypical v P) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k))) ∧
    ∀ (pin : D.PoolPin)
      (hpin : 0 < ∑ P ∈ D.poolPinSet pin, (permPoolLaw G hpools).w P) v,
      (D.pinnedPoolLaw hpools pin hpin).pr (fun P => ¬ D.LocalPoolsTypical v P) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k)) := by
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  constructor
  · intro v
    exact (local_typical_tail D (permPoolLaw G hpools) _ (Real.exp_nonneg _)
      (fun C => (physical_typical_tail physical hpools C).1) v).trans hsmall
  · intro pin hpin v
    apply (local_typical_tail D (D.pinnedPoolLaw hpools pin hpin) _
      (Real.exp_nonneg _) _ v).trans hsmall
    intro C
    exact (physical_typical_tail physical hpools C).2 ⟨pin.cell, pin.slot⟩ pin.bin hpin

/-- The remaining deterministic/source adapter fields. The probability,
clean-prior and retained-corner fields are constructed below. -/
structure RemainingInputs (D : ListGateContext κ T k PT) (K : ℝ)
    (hpools : (permPools D.G).Nonempty) where
  geometry : D.S17GeometryValidity K
  sampler : D.S17SamplerData K
  pool_iid_comparison : ∀ (μ : FinLaw D.PoolAssignment),
    D.IsPermOrPinnedPoolLaw hpools μ →
    ∃ ν : FinLaw D.PoolAssignment,
      (ν = iidPoolLaw D.G hpools ∨
        ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
          (iidPoolLaw D.G hpools).w pools),
          ν = FinLaw.cond (iidPoolLaw D.G hpools) (D.poolPinSet pin) hpin) ∧
      ∀ (slots : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)))
        (f : D.PoolAssignment → ℝ),
        slots.card ≤ (T.S.n k) ^ (κ.Ac + 4) → (∀ pools, 0 ≤ f pools) →
        (∀ p q, (∀ a ∈ slots, p a.1 a.2 = q a.1 a.2) → f p = f q) →
        μ.E f ≤ (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) * ν.E f

noncomputable def physical_quantitative_of_remaining (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (hpools : (permPools G).Nonempty) (K : ℝ)
    (hsmall : ((T.S.n k : ℝ) + 1) * Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k)))
    (rest : RemainingInputs (Lane_sol_s18_dl.physical_list_context hPT hLow physical) K hpools) :
    (Lane_sol_s18_dl.physical_list_context hPT hLow physical).L16QuantitativeValidity K := by
  obtain ⟨hraw, hpinned⟩ := physical_local_typical_tails hPT hLow physical hpools hsmall
  refine {
    geometry := rest.geometry
    sampler := rest.sampler
    pool_support_nonempty := hpools
    pool_typical_tail := hraw
    pool_typical_tail_pinned := fun v pin hp => hpinned pin hp v
    singleton_bound := ?_
    prior_shape := ?_
    corner_size := Lane_sol_fix_corner.active_corner_card_lower_waste hPT
    pool_iid_comparison := rest.pool_iid_comparison }
  · intro C P b y ht hb ho
    exact physical_singleton_bound hPT hLow physical C P b y ht hb ho
  · intro v P s he ht hs
    exact physical_clean_prior hPT hLow physical v P s he ht hs

theorem physical_initial_typical_tail (E : LateEncoding F)
    (physical : PhysicalFreshCertificate G F) (C : G.Cell)
    (hsmall : Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * E.Ts / 2))) :
    E.permLaw.pr (fun x => ¬ F.typical C (x.1 C)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * E.Ts / 2)) := by
  rw [initial_pr_pool E (fun P => ¬ F.typical C (P C))]
  exact (physical_typical_tail physical E.pools_nonempty C).1.trans hsmall

theorem physical_initial_typical_tail_pinned (E : LateEncoding F)
    (physical : PhysicalFreshCertificate G F) (C : G.Cell)
    (pin : CellSlot G) (bin : Bin PT.tiling (G.cellPatch pin.1))
    (hsmall : Real.exp (-Real.rpow (T.S.n k : ℝ) (1 / 2)) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * E.Ts / 2))) :
    E.permLaw.pr (fun x => x.1 pin.1 pin.2 = bin ∧ ¬ F.typical C (x.1 C)) /
      E.permLaw.pr (fun x => x.1 pin.1 pin.2 = bin) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * E.Ts / 2)) := by
  rw [initial_pr_pool E (fun P => P pin.1 pin.2 = bin ∧ ¬ F.typical C (P C)),
    initial_pr_pool E (fun P => P pin.1 pin.2 = bin)]
  by_cases hz : E.poolLaw.pr (fun P => P pin.1 pin.2 = bin) = 0
  · simp only [hz, div_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · have hnonneg : 0 ≤ E.poolLaw.pr (fun P => P pin.1 pin.2 = bin) := by
      unfold FinLaw.pr
      apply Finset.sum_nonneg
      intro P _
      split_ifs <;> simp [E.poolLaw.nonneg]
    have hp : 0 < ∑ P ∈ poolPinEvent pin bin, E.poolLaw.w P := by
      change 0 < ∑ P ∈ Finset.univ.filter (fun P => P pin.1 pin.2 = bin), E.poolLaw.w P
      rw [Finset.sum_filter]
      exact lt_of_le_of_ne hnonneg (Ne.symm hz)
    rw [← pool_cond_pr E.poolLaw (fun P => P pin.1 pin.2 = bin)
      (fun P => ¬ F.typical C (P C)) hp]
    exact ((physical_typical_tail physical E.pools_nonempty C).2 pin bin hp).trans hsmall

theorem physical_initial_list_tail (hκ : κ.Admissible) (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (E : LateEncoding F)
    (hEvents : E.events = (Lane_sol_s18_dl.physical_list_context hPT hLow physical).asListEvent)
    (hn : 1 ≤ (T.S.n k : ℝ)) (v : Pos T k)
    (hEstimate : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).UniformPoolEstimateAt
      v E.poolLaw) :
    E.permLaw.pr (fun x => Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) <
      (FinLaw.pi fun C => F.fresh C (x.1 C)).pr (E.events.S v)) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * E.Ts / 2)) := by
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  rw [initial_pr_pool E (fun P => Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) <
    (FinLaw.pi fun C => F.fresh C (P C)).pr (E.events.S v))]
  have hevent : E.events.S v = D.event v := by rw [hEvents]; rfl
  rw [hevent]
  have hmono := S16.Lane_q_s16_comp2.pr_mono E.poolLaw
    (fun P => Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) < D.freshEventProbability v P)
    (D.poolException v) (by
      intro P hb hs
      exact (not_lt_of_ge hs.2) hb)
  apply hmono.trans (hEstimate.trans _)
  rw [E.Ts_eq]
  exact rpow_R_le_P hκ hn _

theorem physical_initial_list_tail_pinned (hκ : κ.Admissible) (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (E : LateEncoding F)
    (hEvents : E.events = (Lane_sol_s18_dl.physical_list_context hPT hLow physical).asListEvent)
    (hn : 1 ≤ (T.S.n k : ℝ)) (v : Pos T k)
    (pin : CellSlot G) (bin : Bin PT.tiling (G.cellPatch pin.1))
    (hp : 0 < ∑ P ∈ poolPinEvent pin bin, E.poolLaw.w P)
    (hEstimate : (Lane_sol_s18_dl.physical_list_context hPT hLow physical).UniformPoolEstimateAt
      v (FinLaw.cond E.poolLaw (poolPinEvent pin bin) hp)) :
    E.permLaw.pr (fun x => x.1 pin.1 pin.2 = bin ∧
      Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) <
        (FinLaw.pi fun C => F.fresh C (x.1 C)).pr (E.events.S v)) /
      E.permLaw.pr (fun x => x.1 pin.1 pin.2 = bin) ≤
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * E.Ts / 2)) := by
  let D := Lane_sol_s18_dl.physical_list_context hPT hLow physical
  rw [initial_pr_pool E (fun P => P pin.1 pin.2 = bin ∧
      Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) <
        (FinLaw.pi fun C => F.fresh C (P C)).pr (E.events.S v)),
    initial_pr_pool E (fun P => P pin.1 pin.2 = bin), ← pool_cond_pr E.poolLaw
    (fun P => P pin.1 pin.2 = bin) _ hp]
  have hevent : E.events.S v = D.event v := by rw [hEvents]; rfl
  rw [hevent]
  have hmono := S16.Lane_q_s16_comp2.pr_mono
    (FinLaw.cond E.poolLaw (poolPinEvent pin bin) hp)
    (fun P => Real.rpow (T.S.n k : ℝ) (-(κ.P : ℝ)) < D.freshEventProbability v P)
    (D.poolException v) (by
      intro P hb hs
      exact (not_lt_of_ge hs.2) hb)
  apply hmono.trans (hEstimate.trans _)
  rw [E.Ts_eq]
  exact rpow_R_le_P hκ hn _

theorem physical_odd_list_probability (hPT : PT.Valid)
    (hLow : PT.tiling.mode.isLow) (physical : PhysicalFreshCertificate G F)
    (E : LateEncoding F)
    (hEvents : E.events = (Lane_sol_s18_dl.physical_list_context hPT hLow physical).asListEvent)
    (v : Pos T k) (hodd : ¬ IsEvenRole v) (P : ∀ C, F.Pool C) :
    (FinLaw.pi fun C => F.fresh C (P C)).pr (E.events.S v) = 0 := by
  rw [hEvents]
  simp [FinLaw.pr, ListGateContext.asListEvent, ListGateContext.event, hodd]

end HypercubeRamsey.S18.Lane_sol_d18l_up
