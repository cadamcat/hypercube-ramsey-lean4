import HypercubeRamsey.S18.Comparison_sol_s18_n4
import HypercubeRamsey.S18.Leaf_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

private theorem testPrPartition {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (partition : Ω → I) (F : Ω → Prop) :
    (∑ a, P.pr (fun x => F x ∧ partition x = a)) = P.pr F := by
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hf : F x <;> simp [hf]

private theorem testPrNonneg {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (F : Ω → Prop) : 0 ≤ P.pr F := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;> simp [P.nonneg])

set_option maxHeartbeats 400000 in
/-- Partition a test by the consulted pool images. Forcing each positive slice
then gives its lopsided inequality against all leaves it does not touch. -/
theorem testComparisonFromForcingPartition
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ ε : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2)
    (hpositive : 0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x)
    {I : Type*} [Fintype I] (partition : D.encoding.InitInput → I)
    (Ψ : D.encoding.InitInput → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x)
    (touches : ℝ → I → L.Leaf → Prop)
    (force : ∀ v a, 0 < ∑ x ∈ Finset.univ.filter (fun x => Ψ x = v ∧ partition x = a),
      D.encoding.permLaw.w x →
      D.encoding.InitInput → FinLaw D.encoding.InitInput)
    (hpush : ∀ v a ha,
      FinLaw.map (FinLaw.bind D.encoding.permLaw (force v a ha)) Prod.snd =
        FinLaw.cond D.encoding.permLaw (Finset.univ.filter (fun x => Ψ x = v ∧ partition x = a)) ha)
    (hpreserve : ∀ v a ha x y, 0 < (force v a ha x).w y →
      ∀ i, ¬ touches v a i → x ∈ L.leaf i → y ∈ L.leaf i)
    (hcost : ∀ v a, (∏ i ∈ Finset.univ.filter (touches v a),
      (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹) ≤ 1 + ε) :
    (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).E Ψ ≤
      (1 + ε) * D.encoding.permLaw.E Ψ := by
  apply testComparisonFromFibers _ _ Ψ hΨ (1 + ε)
  intro v
  have hslice (a : I) :
      (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).pr
        (fun x => Ψ x = v ∧ partition x = a) ≤
      (1 + ε) * D.encoding.permLaw.pr (fun x => Ψ x = v ∧ partition x = a) := by
    let F := fun x : D.encoding.InitInput => Ψ x = v ∧ partition x = a
    have hnonneighbor : ∀ S : Finset L.Leaf, (∀ i ∈ S, ¬ touches v a i) →
        D.encoding.permLaw.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
          D.encoding.permLaw.pr F * D.encoding.permLaw.pr (fun x => ∀ i ∈ S, x ∉ L.leaf i) := by
      intro S hS
      by_cases ha : 0 < D.encoding.permLaw.pr F
      · have hmass : 0 < ∑ x ∈ Finset.univ.filter F, D.encoding.permLaw.w x := by
          have heq : (∑ x ∈ Finset.univ.filter F, D.encoding.permLaw.w x) =
              D.encoding.permLaw.pr F := by
            rw [← Finset.sum_ite_mem_eq]
            unfold FinLaw.pr
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hf : F x <;> simp [hf]
          exact lt_of_lt_of_eq ha heq.symm
        have hlop := forcingLopsided D.encoding.permLaw (Finset.univ.filter F) hmass
          (force v a hmass) (hpush v a hmass) (fun x => ∀ i ∈ S, x ∉ L.leaf i)
          (by
            intro x y hxy hy i hi hleaf
            exact hy i hi (hpreserve v a hmass x y hxy i (hS i hi) hleaf))
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hlop
      · have hz : D.encoding.permLaw.pr F = 0 :=
          le_antisymm (le_of_not_gt ha) (testPrNonneg _ _)
        rw [hz, zero_mul]
        have hle : D.encoding.permLaw.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
            D.encoding.permLaw.pr F := by
          unfold FinLaw.pr
          apply Finset.sum_le_sum
          intro x hx
          by_cases hf : F x
          · simp only [hf, true_and, ite_true]
            split_ifs <;> simp [D.encoding.permLaw.nonneg]
          · simp [hf]
        exact hz ▸ hle
    have hh := leafTestProbabilityBound D δ L hprob hcharge hpositive F
      (touches v a) hnonneighbor
    have hp0 : 0 ≤ D.encoding.permLaw.pr F := testPrNonneg _ _
    have hbound : D.encoding.permLaw.pr F *
        (∏ i ∈ Finset.univ.filter (touches v a),
          (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹) ≤
        (1 + ε) * D.encoding.permLaw.pr F := by
      have h := mul_le_mul_of_nonneg_left (hcost v a) hp0
      exact h.trans_eq (mul_comm _ _)
    exact hh.trans hbound
  rw [← testPrPartition _ partition (fun x => Ψ x = v),
    ← testPrPartition D.encoding.permLaw partition (fun x => Ψ x = v), Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hslice a)

end HypercubeRamsey.Lane_sol_s18_n4
