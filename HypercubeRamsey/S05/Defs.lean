import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.Framework.Hall
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.S03.ScatteredMoments

/-!
# Section 5 interfaces

Basic interfaces shared by the Section 5 nodes: words, density domination, the parent prior (general enough
for Section 6's restricted partner prior), and the final row certificate with its Hall assembly.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- A finite word of labels from one host side. -/
abbrev Word5 (N q : ℕ) := Fin q → Fin N

/-- Pointwise domination of finite probability weights. -/
def FinProb.DensityLE5 {Ω : Type*} [Fintype Ω] (P Q : FinProb Ω) (c : ℝ) : Prop :=
  ∀ ω, P.w ω ≤ c * Q.w ω

/-- A parent prior with `O(1)/N` atoms, including a conditional partner law at each bin.

This general form is shared with Section 6, where the parent law is changed to a restricted partner prior.
-/
structure ParentPrior5 (N : ℕ) (Bin : Type*) [Fintype Bin] where
  parent : Law N
  partner : Fin N → Bin → Law N
  partnerSet : Fin N → Bin → Finset (Fin N)
  atomConstant : ℝ
  atomConstant_nonneg : 0 ≤ atomConstant
  parent_atom : ∀ y, parent.w y ≤ atomConstant / N
  partner_atom : ∀ v b y, (partner v b).w y ≤ atomConstant / N
  partner_support : ∀ v b y, y ∉ partnerSet v b → (partner v b).w y = 0

open Classical in
/-- Probability rows on even cube roles together with an injective assignment of odd roles. -/
structure CubeRows5 {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) where
  oddLabel : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  odd_injective : Function.Injective oddLabel
  evenRow : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  row_nonneg : ∀ a x, 0 ≤ evenRow a x
  row_sum : ∀ a, ∑ x, evenRow a x = 1
  row_supported : ∀ a x, evenRow a x ≠ 0 →
    ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (oddLabel b)
  column_load : ∀ x, ∑ a, evenRow a x ≤ 1

open Classical in
/-- The final finite assignment certificate gives a cube with the requested colour. -/
theorem cube_of_rows5 {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (R : CubeRows5 (n := n) (N := N) E G) : CubeAt n N E := by
  let L : {v : CubeVertex n // IsEvenRole v} → Finset (Fin N) := fun a =>
    Finset.univ.filter (fun x => ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (R.oddLabel b))
  obtain ⟨fA, hA, hL⟩ := exists_injective_of_fractional R.evenRow L
    R.row_nonneg R.row_sum
    (by
      intro a x hx
      by_contra hp
      apply hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, R.row_supported a x hp⟩)
    R.column_load
  refine ⟨G, ?_⟩
  apply cube_copy_of_parts (G := fun x y => Hits E G x y)
    fA R.oddLabel hA R.odd_injective
  intro a b hadj
  exact (Finset.mem_filter.mp (hL a)).2 b hadj

end HypercubeRamsey
