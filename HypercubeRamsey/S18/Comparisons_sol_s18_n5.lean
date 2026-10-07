import HypercubeRamsey.S18.Nodes_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem pr_eq_indicator {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (F : Ω → Prop) :
    P.pr F = P.E (fun x => if F x then 1 else 0) := by
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : F x <;> simp [hx]

theorem endpoint_integral (D : LateData hPT) {δ εterm εrun : ℝ}
    (C : TerminalCertificate D δ εterm) (H : CompletionCertificate D C εrun)
    (A : InitialPairData D) (assignment : PairAssignment T k) :
    endpointProbability D C H A assignment =
      (D.encoding.terminalLaw (terminalSet D δ) C.positive).E (fun x =>
        (D.encoding.base.runFull H.samplers.act (D.encoding.initialState x)).E (fun h =>
          if D.full δ x h then ∏ v ∈ A.rows, (D.pairLaw h v).w (assignment v) else 0)) := by
  rw [endpointProbability, pr_eq_indicator]
  simp only [pairExperiment, LateEncoding.experiment, bind_E]
  apply congrArg
  funext x
  apply congrArg
  funext h
  by_cases hf : D.full δ x h
  · simp only [hf, true_and, LateData.pairSampler]
    simp only [if_true]
    calc
      _ = (FinLaw.pi (D.pairLaw h)).pr (fun b => ∀ v ∈ A.rows, b v = assignment v) := by
        unfold FinLaw.E FinLaw.pr
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : ∀ v ∈ A.rows, b v = assignment v <;> simp [hb]
      _ = _ := S16.Lane_q_s16_comp2.pi_pr_cylinder (D.pairLaw h) A.rows assignment
  · simp only [hf, false_and, if_false]
    exact E_const _ 0

theorem full_side_requirements (D : LateData hPT) (δ : ℝ)
    (input : D.encoding.InitInput) (h : D.encoding.base.History (Fin.last D.geom.r))
    (hf : D.full δ input h) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) :
    D.R1 j (D.pastRows h j j.isLt b) ∧
      D.R2 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) (D.pastRows h j j.isLt b) ∧
      D.R3 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) (D.pastRows h j j.isLt b) := by
  have hs := hf.2.2.2.2.2.2 j
  have hg := hs.2.2.2.2 b
  have hR1 : D.R1 j (D.pastRows h j j.isLt b) := by
    by_contra hn
    apply hs.2.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hg.1, Or.inl hn⟩
  have hR2 : D.R2 j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt))
      (D.pastRows h j j.isLt b) := by
    by_contra hn
    apply hs.2.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hg.1, Or.inr (Or.inl hn)⟩
  exact ⟨hR1, hR2, hg.2.1⟩

private theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (F : Ω → Prop) : 0 ≤ P.pr F := by
  unfold FinLaw.pr
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact P.nonneg x
  · exact le_rfl

theorem reached_column_tail (D : LateData hPT) (j : Fin D.geom.r)
    (P : FinLaw (D.encoding.base.History j.castSucc))
    (Reached : D.encoding.base.History j.castSucc → Prop) (θ K : ℝ) (hθ : 0 < θ)
    (n : ℕ) (hmoment : ∀ y, P.E (fun h => if Reached h then D.columnSum j h y ^ n else 0) ≤ K) :
    ∀ y, P.pr (fun h => Reached h ∧ θ < D.columnSum j h y) ≤ K / θ ^ n := by
  intro y
  have hpow : 0 < θ ^ n := pow_pos hθ n
  apply (le_div_iff₀ hpow).mpr
  apply le_trans _ (hmoment y)
  unfold FinLaw.pr FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro h _
  have hc : 0 ≤ D.columnSum j h y := by
    apply Finset.sum_nonneg
    intro b _
    exact pr_nonneg _ _
  by_cases hr : Reached h
  · by_cases ht : θ < D.columnSum j h y
    · simp only [hr, ht, and_self, if_true]
      apply mul_le_mul_of_nonneg_left _ (P.nonneg h)
      exact pow_le_pow_left₀ hθ.le ht.le n
    · simp only [hr, ht, and_false, if_false, if_true, zero_mul]
      exact mul_nonneg (P.nonneg h) (pow_nonneg hc n)
  · simp [hr]

noncomputable def scopedFreshPoolTest (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (pools : ∀ C, D.fresh.Pool C) : ℝ :=
  if ∀ C ∈ A.scope, D.fresh.typical C (pools C) then
    (D.freshConfigLaw pools).E (A.phi assignment) else 0

theorem scopedFreshPoolTest_nonneg (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) (pools : ∀ C, D.fresh.Pool C) :
    0 ≤ scopedFreshPoolTest D A assignment pools := by
  unfold scopedFreshPoolTest
  split_ifs
  · apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg ((D.freshConfigLaw pools).nonneg s) (phi_nonneg D A assignment s)
  · exact le_rfl

theorem scopedFreshPoolTest_local (D : LateData hPT) (hD : D.Spec) (A : InitialPairData D)
    (assignment : PairAssignment T k) (pools pools' : ∀ C, D.fresh.Pool C)
    (hp : ∀ C ∈ A.scope, pools C = pools' C) :
    scopedFreshPoolTest D A assignment pools = scopedFreshPoolTest D A assignment pools' := by
  have htyp : (∀ C ∈ A.scope, D.fresh.typical C (pools C)) ↔
      ∀ C ∈ A.scope, D.fresh.typical C (pools' C) := by
    apply forall_congr'
    intro C
    apply imp_congr_right
    intro hC
    rw [hp C hC]
  unfold scopedFreshPoolTest
  simp only [htyp]
  split_ifs
  · letI : ∀ C, Nonempty (D.fresh.State C) := fun C => ⟨D.fresh.fallback C⟩
    exact pi_E_local _ _ A.scope (A.phi assignment) (phi_local D hD A assignment)
      (fun C hC => congrArg (D.fresh.fresh C) (hp C hC))
  · rfl

theorem permFresh_gate_weaken (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k) :
    A.permFreshTest assignment ≤ D.encoding.poolLaw.E (scopedFreshPoolTest D A assignment) := by
  simp only [InitialPairData.permFreshTest, LateEncoding.permLaw, LateEncoding.initialLaw, bind_E]
  have hp (pools : ∀ C, D.fresh.Pool C) :
      (tapeLaw D.fresh D.encoding.Ts).E (fun t =>
        if D.poolGate (D.expandCells A.scope) (pools, t) then
          (D.freshConfigLaw pools).E (A.phi assignment) else 0) ≤
        scopedFreshPoolTest D A assignment pools := by
    let t0 : Tapes D.fresh D.encoding.Ts := fun C _ _ => D.fresh.fallback C
    have hgate : ∀ t : Tapes D.fresh D.encoding.Ts,
        D.poolGate (D.expandCells A.scope) (pools, t) ↔
          D.poolGate (D.expandCells A.scope) (pools, t0) := fun _ => Iff.rfl
    simp only [hgate, E_const]
    by_cases hg : D.poolGate (D.expandCells A.scope) (pools, t0)
    · have htyp : ∀ C ∈ A.scope, D.fresh.typical C (pools C) := by
        intro C hC
        exact hg.1 C (Finset.mem_union.mpr (Or.inl hC))
      simp only [hg, if_true, scopedFreshPoolTest, if_pos htyp]
      exact le_rfl
    · simp only [hg, if_false]
      exact scopedFreshPoolTest_nonneg D A assignment pools
  exact S16.Lane_q_s16_comp2.expect_le _ _ _ hp

theorem permFresh_comparison_of_scoped_pool (D : LateData hPT) (A : InitialPairData D)
    (assignment : PairAssignment T k)
    (hpool : D.encoding.poolLaw.E (scopedFreshPoolTest D A assignment) ≤
      2 * D.encoding.iidLaw.E (scopedFreshPoolTest D A assignment)) :
    A.permFreshTest assignment ≤ 2 * A.iidFreshTest assignment :=
  (permFresh_gate_weaken D A assignment).trans hpool

end HypercubeRamsey.S18.Lane_sol_s18_n5
