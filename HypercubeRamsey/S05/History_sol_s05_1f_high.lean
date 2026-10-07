import HypercubeRamsey.S05.History_sol_s05_1f_integrate

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Fixed-data high posterior failure, after the preceding denominator tests. -/
theorem high_posterior_feasibility_tail (H : X.KeyHist) (r : X.AbsRecord)
    (hr : X.RecOccurs r) (hh : r.1.isRight) (a : X.ArraysOn (Fin (X.p.T n)))
    (hm : 0 < X.step3MassOn H r a none) (hs : 0 < colLen5 (X.p.s n) r.1)
    (hratio : ∀ c ∈ X.refsOn H r a,
      Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) *
        X.step3MassOn H r a (some c) ≤ X.step3MassOn H r a none)
    (bD C L ε εD εg B η β : ℝ)
    (hD : 0 < X.p.DH n) (hL : 0 < L) (hε : 0 < ε) (hεD : 0 < εD) (hεg : 0 < εg)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2)
    (hβ : η + B / L ≤ β) (hβhalf : β ≤ 1 / 2)
    (hactual : X.p.a 3 * (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ) +
      C + Real.log 2 + ε ≤ B)
    (hdensityBudget : bD + C + Real.log 2 + εD ≤ η * X.p.DH n)
    (hcost : (1 + εg) * (B / (1 - β) + Real.log (1 / (1 - β))) ≤
      X.p.a 4 * (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ))
    (hatom : ∀ θ, (N : ℝ) ^ colLen5 (X.p.s n) r.1 * X.step3PostOn H r a none θ ≤
      Real.exp (bD * colLen5 (X.p.s n) r.1)) :
    (posteriorLaw X H r a none hm).pr (fun θ =>
      ¬ (X.HighCapped (X.withCol H r.1 θ) r a ∧ X.HighPriceFeasible (X.withCol H r.1 θ) r a)) ≤
      Real.exp ((colLen5 (X.p.s n) r.1 : ℝ) * Real.log 2 - C * colLen5 (X.p.s n) r.1 / 2) +
        Real.exp (-2 * (εD * colLen5 (X.p.s n) r.1) ^ 2 /
          ((colLen5 (X.p.s n) r.1 : ℝ) * (2 * X.p.DH n) ^ 2)) +
      ((⌈(1 + εg⁻¹) * (X.refsOn H r a).card⌉₊ + 1) ^ (X.refsOn H r a).card : ℕ) *
        (((X.refsOn H r a).card : ℝ) *
          Real.exp ((colLen5 (X.p.s n) r.1 : ℝ) * Real.log 2 - C * colLen5 (X.p.s n) r.1 / 2) +
          Real.exp (-2 * (ε * colLen5 (X.p.s n) r.1) ^ 2 /
            ((colLen5 (X.p.s n) r.1 : ℝ) * (2 * L) ^ 2))) := by
  let P := posteriorLaw X H r a none hm
  let I := {c // c ∈ X.refsOn H r a}
  let Q := fun c : I => posteriorLaw X H r a (some c.1) (step3Mass_deleted_pos X H r a c.1 hm)
  let k : ℝ := (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ)
  let ν := fun θ => coordinatePair (fun h => X.condCoord P.w θ h) hs
  let densityBad := fun θ => (ν θ).pr (fun hy =>
    Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N) < (ν θ).w hy) > η
  let gridBad := fun θ => ∃ b : I → Fin (⌈(1 + εg⁻¹) * Fintype.card I⌉₊ + 1),
    0 < ∑ c, (b c).val ∧
    (ν θ).expect (fun hy => min L (∑ c,
      ((b c).val : ℝ) / (∑ d, (b d).val : ℕ) *
        max 0 (Real.log ((X.condCoord P.w θ hy.1).w hy.2 /
          (X.smooth (X.condCoord (Q c).w θ hy.1)).w hy.2)))) > B
  have hlen (c : I) : X.refLen c.1.2.1 c.1.2.2 =
      X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) :=
    highRefs_length X r hr hh c.1 (refsOn_high_subset X H r hr hh a c.2)
  have hdom (c : I) (θ) : P.w θ ≤ Real.exp (X.p.a 3 * k * colLen5 (X.p.s n) r.1) * (Q c).w θ := by
    have hh := posterior_delete_domination X H r a c.1 hm
      (step3Mass_deleted_pos X H r a c.1 hm) (hratio c.1 c.2) θ
    simpa only [P, Q, posteriorLaw, hlen c, k] using hh
  have hdenTail := density_path_tail X P bD C (X.p.DH n) εD η hs hD hεD hdensityBudget hatom
  have hgridTail := clipped_grid_tail X P Q (X.p.a 3 * k) C L ε εg B hs hL hε
    hactual hdom
  have hsource (θ h) : X.highSource (X.withCol H r.1 θ) r a h = X.condCoord P.w θ h := by
    unfold Setup5.highSource
    have he : X.step3PostOn (X.withCol H r.1 θ) r a none = P.w := by
      funext ϑ
      exact step3PostOn_withCol X H r a ϑ θ none
    rw [he]
    simp [Setup5.withCol]
  have hdeleted (θ) (c : I) (h) :
      X.highDeleted (X.withCol H r.1 θ) r a c.1 h = X.smooth (X.condCoord (Q c).w θ h) := by
    unfold Setup5.highDeleted
    have he : X.step3PostOn (X.withCol H r.1 θ) r a (some c.1) = (Q c).w := by
      funext ϑ
      exact step3PostOn_withCol X H r a ϑ θ (some c.1)
    rw [he]
    simp [Setup5.withCol]
  have hgood (θ) (hd : ¬ densityBad θ) (hg : ¬ gridBad θ) :
      X.HighCapped (X.withCol H r.1 θ) r a ∧ X.HighPriceFeasible (X.withCol H r.1 θ) r a := by
    have hden : (ν θ).pr (fun hy => Real.exp (X.p.DH n) /
        ((colLen5 (X.p.s n) r.1 : ℝ) * N) < (ν θ).w hy) ≤ η := le_of_not_gt hd
    have hmassGood : 1 / 2 ≤ (ν θ).pr (fun hy => (ν θ).w hy ≤
        Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)) := by
      have he : (ν θ).pr (fun hy => (ν θ).w hy ≤
          Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)) +
          (ν θ).pr (fun hy => Real.exp (X.p.DH n) /
            ((colLen5 (X.p.s n) r.1 : ℝ) * N) < (ν θ).w hy) = 1 := by
        unfold FinProb.pr
        rw [← Finset.sum_add_distrib]
        calc
          _ = ∑ hy, (ν θ).w hy := by
            apply Finset.sum_congr rfl
            intro hy _
            by_cases hxy : (ν θ).w hy ≤ Real.exp (X.p.DH n) /
                ((colLen5 (X.p.s n) r.1 : ℝ) * N) <;> simp [hxy]
          _ = _ := (ν θ).sum_eq_one
      linarith
    have hν : coordinatePair (X.highSource (X.withCol H r.1 θ) r a) hs = ν θ := by
      congr 1; funext h; exact hsource θ h
    have hcap := high_capped_of_density X (X.withCol H r.1 θ) r a hs
      (by simpa only [hν] using hmassGood)
    refine ⟨hcap, ?_⟩
    apply high_price_feasible_of_grid X (X.withCol H r.1 θ) r hr hh a hs L B η β εg
      hL hB hη hβ hβhalf hεg hcost (by simpa only [hν] using hden)
    rw [refsOn_withCol_high X H r hh a θ]
    intro b hb
    have hno : ¬ ((ν θ).expect (fun hy => min L (∑ c,
      ((b c).val : ℝ) / (∑ d, (b d).val : ℕ) *
        max 0 (Real.log ((X.condCoord P.w θ hy.1).w hy.2 /
          (X.smooth (X.condCoord (Q c).w θ hy.1)).w hy.2)))) > B) :=
      fun h => hg ⟨b, hb, h⟩
    simpa only [hν, hsource, hdeleted] using le_of_not_gt hno
  have himp (θ) (hbad : ¬ (X.HighCapped (X.withCol H r.1 θ) r a ∧
      X.HighPriceFeasible (X.withCol H r.1 θ) r a)) : densityBad θ ∨ gridBad θ := by
    by_contra h
    push_neg at h
    exact hbad (hgood θ h.1 h.2)
  calc
    _ ≤ P.pr (fun θ => densityBad θ ∨ gridBad θ) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro θ _
      by_cases hbad : ¬ (X.HighCapped (X.withCol H r.1 θ) r a ∧
          X.HighPriceFeasible (X.withCol H r.1 θ) r a)
      · simp only [if_pos hbad, if_pos (himp θ hbad)]; exact le_rfl
      · simp only [if_neg hbad]; split_ifs <;> simp [P.nonneg θ]
    _ ≤ P.pr densityBad + P.pr gridBad := P.pr_union _ _
    _ ≤ _ := by simpa only [I, Fintype.card_coe] using add_le_add hdenTail hgridTail

end
end HypercubeRamsey.Lane_sol_s05_1f
