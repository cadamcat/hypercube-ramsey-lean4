import Mathlib

/-!
# Lemma 3.4: conditional avoidance comparison

The lopsided asymmetric local lemma with conditional comparisons, on a finite probability space given by
weights, and the independent-variables case of its hypothesis. Source: `sections/03-…tex`, Lemma 3.4 and the
paragraph after it.
-/

namespace HypercubeRamsey.LocalLemma

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {I : Type*} [Fintype I] [DecidableEq I]

/-- The mass of an event. -/
def mass (w : Ω → ℝ) (A : Finset Ω) : ℝ := ∑ ω ∈ A, w ω

/-- The avoidance event `A_S`: no event indexed by `S` occurs. -/
def avoid (E : I → Finset Ω) (S : Finset I) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ j ∈ S, ω ∉ E j)

/-- Lemma 3.4. `adj` is the symmetric, irreflexive neighbour relation; the hypothesis `hp` is the lopsided
condition in multiplicative form (so it holds trivially when the conditioning event has mass zero). -/
theorem conditional_avoidance
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hw1 : ∑ ω, w ω = 1)
    (E : I → Finset Ω) (adj : I → I → Prop) [DecidableRel adj]
    (hsymm : ∀ i j, adj i j → adj j i) (hirr : ∀ i, ¬ adj i i)
    (p x : I → ℝ)
    (hp : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ adj i j) →
      mass w (E i ∩ avoid E S) ≤ p i * mass w (avoid E S))
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hpx : ∀ i, p i ≤ x i * ∏ j ∈ Finset.univ.filter (adj i), (1 - x j)) :
    (0 < mass w (avoid E Finset.univ)) ∧
    (∀ i (S : Finset I), i ∉ S → mass w (E i ∩ avoid E S) ≤ x i * mass w (avoid E S)) ∧
    (∀ S T : Finset I, Disjoint S T → ∀ W : Ω → ℝ, (∀ ω, 0 ≤ W ω) →
      (∑ ω ∈ avoid E (S ∪ T), w ω * W ω) / mass w (avoid E (S ∪ T)) ≤
        (∏ j ∈ T, (1 - x j))⁻¹ * ((∑ ω ∈ avoid E S, w ω * W ω) / mass w (avoid E S))) ∧
    (∀ (F : Finset Ω) (pF : ℝ) (adjF : I → Prop) [DecidablePred adjF],
      (∀ S : Finset I, (∀ j ∈ S, ¬ adjF j) → mass w (F ∩ avoid E S) ≤ pF * mass w (avoid E S)) →
      ∀ S : Finset I, mass w (F ∩ avoid E S) / mass w (avoid E S) ≤
        pF * ∏ j ∈ S.filter adjF, (1 - x j)⁻¹) := sorry

/-- Independent underlying variables: an event and an avoidance event with disjoint variable scopes are
independent under the product weights, so `hp` holds with `p i = mass w (E i)` when events are joined exactly
when their scopes overlap. -/
theorem mass_inter_avoid_of_disjoint_scopes {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (hq0 : ∀ v a, 0 ≤ q v a) (hq1 : ∀ v, ∑ a, q v a = 1)
    (E : I → Finset (∀ v, α v)) (scope : I → Finset V)
    (hscope : ∀ i (ω ω' : ∀ v, α v), (∀ v ∈ scope i, ω v = ω' v) → (ω ∈ E i ↔ ω' ∈ E i))
    (i : I) (S : Finset I) (hS : ∀ j ∈ S, Disjoint (scope i) (scope j)) :
    mass (fun ω => ∏ v, q v (ω v)) (E i ∩ avoid E S) =
      mass (fun ω => ∏ v, q v (ω v)) (E i) * mass (fun ω => ∏ v, q v (ω v)) (avoid E S) := sorry

/-- The product weights form a probability. -/
theorem sum_prod_weights {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (q : ∀ v, α v → ℝ) (hq1 : ∀ v, ∑ a, q v a = 1) :
    ∑ ω : (∀ v, α v), ∏ v, q v (ω v) = 1 := sorry

end HypercubeRamsey.LocalLemma
