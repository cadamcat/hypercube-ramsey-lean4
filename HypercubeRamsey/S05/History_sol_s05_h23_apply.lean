import HypercubeRamsey.S05.History_sol_s05_h23

namespace HypercubeRamsey.Lane_sol_s05_h23
open Classical Filter OAI.HypercubeRamsey Lane_q_s05_h23
open scoped BigOperators Topology
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 400000
noncomputable section
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

theorem stage2GroupLLL_to_conclusion5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (x : CoarseKey5 n → ℝ)
    (hL : ProductLLLData5 (CoarsePairLaw5 X v) (stage2GroupBadOnPairs5 X v)
      (stage2GroupScope5 X) x)
    (hfactor : ∀ B : Finset (BinVector5 n),
      (∏ i ∈ Finset.univ.filter (fun i : CoarseKey5 n =>
        ¬ Disjoint (stage2GroupScope5 X i) B), (1 - x i))⁻¹ ≤ (2 : ℝ) ^ B.card) :
    ∃ ν : FinProb X.Coarse, stage2AlarmConclusion5 X v ν := by
  classical
  let e := coarsePairEquiv5 X
  let P := CoarsePairLaw5 X v
  obtain ⟨Q, hQbad, hQraw, hQexpect⟩ :=
    productAvoidanceLocalCompare5 P (stage2GroupBadOnPairs5 X v)
      (stage2GroupScope5 X) x hL
  let ν : FinProb X.Coarse := FinProb.map Q e
  have hsource (c : X.Coarse) (hc : ν.w c ≠ 0) : Q.w (e.symm c) ≠ 0 := by
    change (FinProb.map Q e).w c ≠ 0 at hc
    rw [map_equiv_weight5 Q e c] at hc
    exact hc
  have hgood (c : X.Coarse) (hc : ν.w c ≠ 0) (i : CoarseKey5 n) :
      ¬ stage2GroupBad5 X v i c := by
    have h := hQbad (e.symm c) (hsource c hc) i
    simpa [stage2GroupBadOnPairs5, e] using h
  have hrawSupport : ∀ c, ν.w c ≠ 0 → (X.coarseLaw v).w c ≠ 0 := by
    intro c hc
    have hprod : (FinProb.pi P).w (e.symm c) ≠ 0 := hQraw (e.symm c) (hsource c hc)
    have heq : (X.coarseLaw v).w c = (FinProb.pi P).w (e.symm c) := by
      calc
        (X.coarseLaw v).w c = (FinProb.map (FinProb.pi P) e).w c := by
          rw [coarseLaw_eq_map_pi5 X v]
        _ = (FinProb.pi P).w (e.symm c) := map_equiv_weight5 (FinProb.pi P) e c
    rw [heq]
    exact hprod
  have hpass (c : X.Coarse) (hc : ν.w c ≠ 0) :=
    stage2GroupGood_conclusions5 X v c (hgood c hc)
  refine ⟨ν, ?_, ?_, ?_, ?_, hrawSupport⟩
  · intro c hc
    exact ⟨(hpass c hc).1, (hpass c hc).2.1⟩
  · intro c hc
    exact (hpass c hc).2.2.1
  · intro c hc
    exact (hpass c hc).2.2.2
  · intro B f hf hdep
    let Φ : (BinVector5 n → Fin N × X.Stream) → ℝ := fun ω => f (e ω)
    have hΦ : ∀ ω, 0 ≤ Φ ω := fun ω => hf (e ω)
    have hΦdep : FinProb.DependsOn Φ B := by
      intro ω ω' heq
      apply hdep (e ω) (e ω')
      intro w hw
      have hp := heq w hw
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    have hmapν : ν.expect f = Q.expect Φ := by
      simpa [ν, Φ, e] using (FinProb.map_expect Q e f)
    have hmapCoarse : X.coarseLaw v = FinProb.map (FinProb.pi P) e := by
      simpa [P, e] using coarseLaw_eq_map_pi5 X v
    have hmapRaw : (X.coarseLaw v).expect f = (FinProb.pi P).expect Φ := by
      rw [hmapCoarse]
      simpa [Φ] using (FinProb.map_expect (FinProb.pi P) e f)
    have hRawNonneg : 0 ≤ (FinProb.pi P).expect Φ := by
      unfold FinProb.expect
      apply Finset.sum_nonneg
      intro ω hω
      exact mul_nonneg ((FinProb.pi P).nonneg ω) (hΦ ω)
    calc
      ν.expect f = Q.expect Φ := hmapν
      _ ≤ (∏ i ∈ Finset.univ.filter (fun i =>
            ¬ Disjoint (stage2GroupScope5 X i) B), (1 - x i))⁻¹ *
            (FinProb.pi P).expect Φ := hQexpect B Φ hΦ hΦdep
      _ ≤ (2 : ℝ) ^ B.card * (FinProb.pi P).expect Φ :=
        mul_le_mul_of_nonneg_right (hfactor B) hRawNonneg
      _ = (2 : ℝ) ^ B.card * (X.coarseLaw v).expect f := by rw [← hmapRaw]

def stage2Request : ParamReq5 where
  Kcap := fun _ => 0
  Kpp := fun _ => 0
  Kh := fun _ => 0
  K1 := fun x => 8 / x.1.2.2.2.1
  K2 := fun _ => 0
  KD := fun _ => 0
  Ks := fun _ => 0
  KB := fun _ => 0
  alpha := fun _ => 1
  alpha_pos := by intro x; norm_num

theorem stage2Budget_tendsto (p : Params5 γ K' χ) :
    Tendsto (stage2GroupBudgetVanishing5 p) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_m_atTop_h23 p)
  have decay (k : ℝ) (hk : 0 < k) :
      Tendsto (fun n => Real.exp (-k * Real.log (p.m n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp (hlog.const_mul_atTop hk)
  have h1 := (decay 5 (by norm_num)).const_mul
    (8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ))
  have h2 := (decay 19 (by norm_num)).const_mul 3
  have h3 := (decay (p.delta * p.eta / 4) (div_pos (mul_pos p.hdelta.1 p.heta.1) (by norm_num))).const_mul
    (((stage2TypeCountBase5 * (2 * (stage2CoarseCountBase5) + 3) : ℕ) : ℝ))
  change Tendsto (fun n => stage2GroupBudgetVanishing5 p n) atTop (𝓝 0)
  simpa only [stage2GroupBudgetVanishing5, mul_zero, add_zero] using (h1.add h2).add h3

theorem stage2Budget_nonneg (p : Params5 γ K' χ) (n : ℕ) :
    0 ≤ stage2GroupBudgetVanishing5 p n := by
  unfold stage2GroupBudgetVanishing5
  positivity

theorem stage2Bounds_eventually (p : Params5 γ K' χ) :
    ∀ᶠ n in atTop, 1 ≤ p.m n ∧
      stage2GroupBudgetVanishing5 p n < 1 / 2 ∧
      (stage2GroupDegreeBound5 : ℝ) * stage2GroupBudgetVanishing5 p n ≤ 1 / 4 ∧
      2 * stage2GroupBudgetVanishing5 p n ≤
        Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ)) := by
  have hb := stage2Budget_tendsto p
  have hC : 0 < (stage2GroupTouchPerBin5 : ℝ) := by
    unfold stage2GroupTouchPerBin5 stage2GroupScopeCardBound5
    positivity
  have hf : 0 < Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ)) :=
    div_pos (Real.log_pos (by norm_num)) (by positivity)
  filter_upwards [(tendsto_m_atTop_h23 p).eventually_ge_atTop 1,
    hb.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    (hb.const_mul (stage2GroupDegreeBound5 : ℝ)).eventually_lt_const
      (by norm_num : (stage2GroupDegreeBound5 : ℝ) * 0 < 1 / 4),
    (hb.const_mul 2).eventually_lt_const (by simpa only [mul_zero] using hf)]
      with n hm hb hd hf
  exact ⟨by exact_mod_cast hm, hb, hd.le, hf.le⟩

theorem stage2Law_exists (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (hraw : Stage2RawBounds5 X v) (hm : 1 ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1)
    (hbhalf : stage2GroupBudgetVanishing5 X.p n < 1 / 2)
    (hbdeg : (stage2GroupDegreeBound5 : ℝ) * stage2GroupBudgetVanishing5 X.p n ≤ 1 / 4)
    (hbfactor : 2 * stage2GroupBudgetVanishing5 X.p n ≤
      Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ))) :
    ∃ ν : FinProb X.Coarse, stage2AlarmConclusion5 X v ν := by
  classical
  let b := stage2GroupBudgetVanishing5 X.p n
  have hb : 0 ≤ b := stage2Budget_nonneg X.p n
  have hJ := J_le_m_h23 X.p n hm
  have hprob (q : CoarseKey5 n) :
      (FinProb.pi (CoarsePairLaw5 X v)).pr (stage2GroupBadOnPairs5 X v q) ≤ b := by
    rw [stage2GroupBadOnPairs_pr5]
    exact (stage2GroupBad_pr_le_budget5 X v hraw q hm hJ hK1).trans
      (stage2GroupBudgetBound_le_vanishing5 X hm hJ hK1)
  have hneighbor (q : CoarseKey5 n) :
      (∑ q' ∈ Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q), b) ≤ 1 / 4 := by
    calc
      _ = ((Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q)).card : ℝ) * b := by simp
      _ ≤ (stage2GroupDegreeBound5 : ℝ) * b :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast stage2GroupNeighbors_card_le5 X q) hb
      _ ≤ 1 / 4 := hbdeg
  have hLLL := productLLLData_of_budget5 (CoarsePairLaw5 X v)
    (stage2GroupBadOnPairs5 X v) (stage2GroupScope5 X) (fun _ => b)
    (stage2GroupBadOnPairs_depends5 X v) (fun _ => hb) (fun _ => hbhalf) hprob hneighbor
  exact stage2GroupLLL_to_conclusion5 X v (fun _ => 2 * b) hLLL
    (fun B => stage2GroupFactor_le5 X B b hb hbfactor)


end
end HypercubeRamsey.Lane_sol_s05_h23
