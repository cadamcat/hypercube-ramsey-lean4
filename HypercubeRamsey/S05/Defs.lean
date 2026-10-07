import HypercubeRamsey.Framework.OneShot
import HypercubeRamsey.Framework.Hall
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.S03.ScatteredMoments

/-!
# Section 5 interfaces

Finite interfaces for the staged experiment in Section 5.  The parent prior, chunk/sign encoding,
state encoding, local height data, and selected rows are parameterized so the corresponding Section 6
nodes can reuse them with a different parent prior or selection rule.
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

/-- A chunk/sign interface whose arity and severity range are supplied by the caller. -/
structure ChunkSignData5 (Vertex Coarse : Type*) (m : ℕ) where
  parity : Vertex → Bool
  coarseKey : Vertex → Coarse
  sign : Vertex → Fin m → Bool
  severity : Vertex → ℕ
  boundary : Vertex → Prop
  sensitiveChunks : Vertex → Finset (Fin m)
  adjacent : Vertex → Vertex → Prop

/-- A finite state graph and its one-hot ambient encoding. -/
structure StateEncoding5 (State : Type*) [Fintype State] (d : ℕ) where
  parity : State → Bool
  ambient : State → Fin d → Bool
  key : State → ℕ
  neighbors : State → Finset State
  degree_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ v, (neighbors v).card ≤ C
  adjacent_distance : ∃ D : ℕ, ∀ u v w,
    u ∈ neighbors v → w ∈ neighbors v →
      (Finset.univ.filter (fun i => ambient u i ≠ ambient w i)).card ≤ D

/-- Local data for a marking-and-height selection rule.  Its radius, level set, and threshold are explicit
parameters, so Section 6 can alter the height rule without changing the interface. -/
structure MarkingHeightData5 (Site Centre Level : Type*) where
  site : Centre → Site
  level : Centre → Level
  radius : ℕ
  threshold : ℕ
  marked : Centre → Prop
  eligible : Site → Centre → Prop
  selected : Site → Centre → Prop
  selected_eligible : ∀ v c, selected v c → eligible v c

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
