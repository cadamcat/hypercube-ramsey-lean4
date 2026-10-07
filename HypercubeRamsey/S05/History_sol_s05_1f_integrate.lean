import HypercubeRamsey.S05.History_sol_s05_1f_tests

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Integrate a fixed-data posterior tail against the true-target-gated data
subdensity. Unobserved arrays are marginalized before changing likelihoods. -/
theorem step3_conditional_tail (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (F : (Fin (colLen5 (X.p.s n) r.1) → Fin N) → X.ArraysOn (Fin (X.p.T n)) → Prop)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hF : ∀ θ, FinProb.DependsOn (fun a => if F θ a then (1 : ℝ) else 0) r.2.1)
    (htail : ∀ a (hm : 0 < X.step3MassOn H r a none),
      (posteriorLaw X H r a none hm).pr (fun θ => F θ a) ≤ ε) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a =>
          X.candGateOn H r a θ ∧ F θ a)) ≤ ε := by
  let Q := Lane_sol_s05_hist1b.step3Reference X H r
  let w := fun a θ => (∏ h, (X.prior H.1 r.1).w (θ h)) *
    (if X.candGateOn H r a θ then 1 else 0) * X.obsLikOn H r a θ none
  have hw (a θ) : 0 ≤ w a θ := by
    apply mul_nonneg _ (Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ none)
    apply mul_nonneg (Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg _)
    split_ifs <;> norm_num
  have hwmass (a) : ∑ θ, w a θ = X.step3MassOn H r a none := rfl
  have hdata (a) : (∑ θ, if F θ a then w a θ else 0) ≤ ε * X.step3MassOn H r a none := by
    by_cases hm : 0 < X.step3MassOn H r a none
    · have hh := htail a hm
      have he : (posteriorLaw X H r a none hm).pr (fun θ => F θ a) =
          (∑ θ, if F θ a then w a θ else 0) / X.step3MassOn H r a none := by
        unfold FinProb.pr
        simp only [posteriorLaw, Setup5.step3PostOn]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro θ _
        by_cases h : F θ a <;> simp [h, w]
      rw [he] at hh
      exact (div_le_iff₀ hm).mp hh
    · have hz : X.step3MassOn H r a none = 0 := le_antisymm (le_of_not_gt hm)
        (Lane_sol_s05_hist1b.step3MassOn_nonneg X H r a none)
      have hn : ∑ θ, (if F θ a then w a θ else 0) ≤ ∑ θ, w a θ := by
        apply Finset.sum_le_sum
        intro θ _
        split_ifs
        · exact le_rfl
        · exact hw a θ
      simpa only [hwmass, hz, mul_zero] using hn
  obtain ⟨y, μ, hrec⟩ := hr
  have hmask := Lane_sol_s05_hist1b.record_mask_mem X r y μ hrec
  have hraw : (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) *
        (X.recArrayLaw (X.withCol H r.1 θ)).pr (fun a => X.candGateOn H r a θ ∧ F θ a)) =
      Q.expect (fun a => ∑ θ, if F θ a then w a θ else 0) := by
    simp_rw [Lane_sol_s05_hist1b.gated_array_pr X H r _ hmask _ (hF _)]
    unfold FinProb.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro θ _
    by_cases hg : X.candGateOn H r a θ <;> by_cases hf : F θ a <;> simp [Q, w, hg, hf, mul_assoc, mul_comm, mul_left_comm]
  rw [hraw]
  calc
    _ ≤ Q.expect (fun a => ε * X.step3MassOn H r a none) := Q.expect_mono hdata
    _ = ε * Q.expect (fun a => X.step3MassOn H r a none) := by
      unfold FinProb.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
      (Lane_sol_s05_hist1b.step3_reference_mass_integral X H r none) hε
    _ = ε := mul_one _


/-- Every array named by a legitimate record is already in its observations. -/
theorem recordArrays_eq_observed (r : X.AbsRecord) (hr : X.RecOccurs r) :
    Lane_sol_s05_h5l.recordArrays X r = r.2.1 := by
  obtain ⟨y, μ, hrec⟩ := hr
  apply Finset.Subset.antisymm
  · intro c hc
    simp only [Lane_sol_s05_h5l.recordArrays, Finset.mem_union, Finset.mem_image] at hc
    rcases hc with (hc | ⟨d, hd, rfl⟩) | ⟨d, hd, he⟩
    · exact hc
    · exact Lane_sol_s05_hist1b.record_ref_mem X r y μ hrec d hd
    · have hm : r.2.2.2 = some d := Option.mem_toFinset.mp hd
      have hmem := Lane_sol_s05_hist1b.record_mask_mem X r y μ hrec (d.1, d.2.1) d.2.2 hm
      exact he ▸ hmem
  · intro c hc
    simp [Lane_sol_s05_h5l.recordArrays, hc]

/-- Computed references only consult their observed array and fixed named columns. -/
theorem refsOn_arrays_congr (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (a b : X.ArraysOn (Fin (X.p.T n))) (hab : ∀ c ∈ r.2.1, a c = b c) :
    X.refsOn H r a = X.refsOn H r b := by
  obtain ⟨y, μ, hrec⟩ := hr
  unfold Setup5.refsOn
  apply Finset.image_congr
  intro d hd
  change (d.1, d.2.1, X.refSubsetOn H a (d.1, d.2.1) d.2.2) =
    (d.1, d.2.1, X.refSubsetOn H b (d.1, d.2.1) d.2.2)
  have ha := hab (d.1, d.2.1) (Lane_sol_s05_hist1b.record_ref_mem X r y μ hrec d hd)
  have hh (z : Fin N) : X.hitSet a (d.1, d.2.1) z = X.hitSet b (d.1, d.2.1) z := by
    unfold Setup5.hitSet
    rw [ha]
  simp only [Setup5.refSubsetOn, hh]

theorem denominatorFail_arrays_congr (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (a b : X.ArraysOn (Fin (X.p.T n))) (hab : ∀ c ∈ r.2.1, a c = b c) :
    denominatorFail X H r a ↔ denominatorFail X H r b := by
  obtain ⟨y, μ, hrec⟩ := hr
  have hmask := Lane_sol_s05_hist1b.record_mask_mem X r y μ hrec
  have hmass (excl) := Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r a b hmask hab excl
  have hgate := Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r a b hmask hab (H.2 r.1)
  have href := refsOn_arrays_congr X H r ⟨y, μ, hrec⟩ a b hab
  simp only [denominatorFail, hmass, hgate, href]

end
end HypercubeRamsey.Lane_sol_s05_1f
