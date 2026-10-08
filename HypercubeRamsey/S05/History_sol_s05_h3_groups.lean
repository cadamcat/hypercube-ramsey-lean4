import HypercubeRamsey.S05.History_sol_s05_h3_growth

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open Lane_sol_s05_hist1b Lane_sol_s05_h5l
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

 def stage3GroupBad (X : Setup5 γ K' χ n N E G) (b : X.Base) (cH : ℝ)
    (q : CoarseKey5 n) (hi : HiddenHigh5 X) : Prop :=
  (∃ i : Stage2GroupAlarm5 (halfDeltaSetup X) q, stage3PatternBad X b q i hi) ∨
    (∃ r : NormalizedHighRecordAt X q,
      Real.exp (-(cH * X.p.s n) / 2) < highRecordMean X b r.1 hi)

 theorem stage3GroupBad_depends (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (cH : ℝ) (q : CoarseKey5 n) :
    FinProb.DependsOn (stage3GroupBad X b cH q) (highGroupScope q) := by
  intro hi hi' h
  apply propext
  have hp (i : Stage2GroupAlarm5 (halfDeltaSetup X) q) := stage3Pattern_depends X b q i hi hi' h
  have hr (r : NormalizedHighRecordAt X q) := highRecordMean_depends X b q r hi hi' h
  constructor
  · rintro (⟨i, hi⟩ | ⟨r, hi⟩)
    · exact Or.inl ⟨i, Eq.mp (hp i) hi⟩
    · exact Or.inr ⟨r, by rw [← hr r]; exact hi⟩
  · rintro (⟨i, hi⟩ | ⟨r, hi⟩)
    · exact Or.inl ⟨i, Eq.mpr (hp i) hi⟩
    · exact Or.inr ⟨r, by rw [hr r]; exact hi⟩

 theorem stage3GroupBad_pr (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (cH : ℝ) (hcH : 0 < cH) (hraw : Stage3RawBounds X b cH)
    (q : CoarseKey5 n) (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n)
    (hTm : X.p.T n ≤ X.p.m n) (hTJ : X.p.T n ≤ X.p.J n) (hJ : 1 ≤ X.p.J n)
    (hK1 : 16 / X.p.delta ≤ X.p.K1)
    (hKs : 2 * ((signatureConstant : ℝ) + 204) / cH ≤ X.p.Ks) :
    (highRawLaw X b).pr (stage3GroupBad X b cH q) ≤ highGroupBudget X.p n := by
  classical
  let P := highRawLaw X b
  let e := Real.exp (-(cH * X.p.s n) / 2)
  have hp : P.pr (fun hi => ∃ i : Stage2GroupAlarm5 (halfDeltaSetup X) q,
      stage3PatternBad X b q i hi) ≤ stage2GroupBudgetVanishing5 (halfDelta X.p) n := by
    calc
      _ ≤ ∑ i : Stage2GroupAlarm5 (halfDeltaSetup X) q, P.pr (stage3PatternBad X b q i) :=
        pr_exists_le_sum5 P (stage3PatternBad X b q)
      _ ≤ ∑ i : Stage2GroupAlarm5 (halfDeltaSetup X) q, stage3PatternBudget X q i := by
        apply Finset.sum_le_sum
        intro i _
        exact stage3Pattern_pr X b cH hraw q i
      _ ≤ _ := stage3Pattern_budget_sum X q (by omega) hK1
  have hr : P.pr (fun hi => ∃ r : NormalizedHighRecordAt X q,
      e < highRecordMean X b r.1 hi) ≤ 3 * Real.exp (-4 * Real.log (X.p.m n : ℝ)) := by
    calc
      _ ≤ ∑ r : NormalizedHighRecordAt X q,
          P.pr (fun hi => e < highRecordMean X b r.1 hi) := pr_exists_le_sum5 P _
      _ ≤ ∑ _r : NormalizedHighRecordAt X q, e := by
        apply Finset.sum_le_sum
        intro r _
        exact highRecord_bad_pr X b cH hraw q r
      _ = (Fintype.card (NormalizedHighRecordAt X q) : ℝ) * e := by simp
      _ ≤ (3 * highRecordCountBound X.p n : ℕ) * e :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast normalizedHighRecordAt_card X q hm hD hTm)
          (Real.exp_pos _).le
      _ ≤ _ := highRecordBudget_le X.p n cH hcH hKs hm hTJ hJ
  exact (FinProb.pr_union P _ _).trans (add_le_add hp hr)

 theorem highGroup_avoidance (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (cH : ℝ) (hcH : 0 < cH) (hraw : Stage3RawBounds X b cH)
    (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n)
    (hTm : X.p.T n ≤ X.p.m n) (hTJ : X.p.T n ≤ X.p.J n) (hJ : 1 ≤ X.p.J n)
    (hK1 : 16 / X.p.delta ≤ X.p.K1)
    (hKs : 2 * ((signatureConstant : ℝ) + 204) / cH ≤ X.p.Ks)
    (hhalf : highGroupBudget X.p n < 1 / 2)
    (hdeg : (coarseCountBound 4 : ℝ) * highGroupBudget X.p n ≤ 1 / 4) :
    ∃ ν : FinProb (HiddenHigh5 X),
      (∀ hi, ν.w hi ≠ 0 → ∀ q, ¬ stage3GroupBad X b cH q hi) ∧
      (∀ hi, ν.w hi ≠ 0 → ∀ q h, (X.prior b (.inr q)).w (hi q h) ≠ 0) := by
  classical
  let P : CoarseKey5 n → FinProb (Fin (X.p.s n) → Fin N) :=
    fun q => FinProb.pi fun _ => X.prior b (.inr q)
  let B := highGroupBudget X.p n
  have hB : 0 ≤ B := highGroupBudget_nonneg X.p n
  have hp (q) : (FinProb.pi P).pr (stage3GroupBad X b cH q) ≤ B :=
    stage3GroupBad_pr X b cH hcH hraw q hm hD hTm hTJ hJ hK1 hKs
  have hn (q : CoarseKey5 n) :
      (∑ q' ∈ Finset.univ.filter (LocalAdj5 highGroupScope q), B) ≤ 1 / 4 := by
    calc
      _ = ((Finset.univ.filter (LocalAdj5 highGroupScope q)).card : ℝ) * B := by simp
      _ ≤ (coarseCountBound 4 : ℝ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast highGroup_neighbors_card q) hB
      _ ≤ _ := hdeg
  have hL := productLLLData_of_budget5 P (stage3GroupBad X b cH) highGroupScope (fun _ => B)
    (stage3GroupBad_depends X b cH) (fun _ => hB) (fun _ => hhalf) hp hn
  obtain ⟨ν, hgood, hsupport, hcompare⟩ :=
    productAvoidanceLocalCompare5 P (stage3GroupBad X b cH) highGroupScope (fun _ => 2 * B) hL
  refine ⟨ν, hgood, ?_⟩
  intro hi hhi q h
  have hs := hsupport hi hhi
  change (∏ q : CoarseKey5 n, ∏ h : Fin (X.p.s n), (X.prior b (.inr q)).w (hi q h)) ≠ 0 at hs
  exact Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hs q (Finset.mem_univ q)) h (Finset.mem_univ h)

end
end HypercubeRamsey.Lane_sol_s05_h23
