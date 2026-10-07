import HypercubeRamsey.Framework.FinProb
import HypercubeRamsey.Framework.FinProbLemmas

/-!
# Lemma 8.1: finite-probability helpers

Normalized laws with a fallback (`normOr`), conditioning with a fallback (`condOr`), and the local-lemma interface on
a product law (`LLLInput`, `CondProductBound`, Lemma 3.4 with independent variables).  The last two have the same
form as the Section 7 re-split (`S07/Experiment.lean` on branch `lane/opus-s07`); the coordinator may unify them.
-/

namespace HypercubeRamsey.S08

open Classical
open scoped BigOperators

/-- Normalize a nonnegative weight; the law `P` when the total mass is zero. -/
noncomputable def normOr {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (P : FinProb Ω) :
    FinProb Ω where
  w ω := if ∑ ω', f ω' = 0 then P.w ω else f ω / ∑ ω', f ω'
  nonneg ω := by
    by_cases h : ∑ ω', f ω' = 0
    · simp only [h, ↓reduceIte]; exact P.nonneg ω
    · simp only [h, ↓reduceIte]; exact div_nonneg (hf ω) (Finset.sum_nonneg fun ω' _ => hf ω')
  sum_eq_one := by
    by_cases h : ∑ ω', f ω' = 0
    · simp only [h, ↓reduceIte]; exact P.sum_eq_one
    · simp only [h, ↓reduceIte]; rw [← Finset.sum_div]; exact div_self h

/-- Conditioning on an event, keeping the law when the event has mass zero. -/
noncomputable def condOr {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : FinProb Ω :=
  if h : 0 < P.pr A then P.cond A h else P

/-- Probabilities are nonnegative. -/
theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [P.nonneg ω]

/-- Replace the coordinates in `U` of `ω` by `a`. -/
noncomputable def glue {V : Type*} {α : V → Type*} (U : Finset V) (ω : ∀ v, α v) (a : ∀ v : U, α v) :
    ∀ v, α v :=
  fun v => by classical exact if h : v ∈ U then a ⟨v, h⟩ else ω v

/-- Local-lemma input on a product law (Lemma 3.4 with independent variables): scopes, dependency degree at
most `Δ` (events adjacent when their scopes meet), and probabilities at most `x (1 - x)^Δ`. -/
structure LLLInput {V : Type} [Fintype V] [DecidableEq V] {α : V → Type} [∀ v, Fintype (α v)]
    (P : ∀ v, FinProb (α v)) {I : Type} [Fintype I] (Bad : I → (∀ v, α v) → Prop)
    (sc : I → Finset V) (x : ℝ) (Δ : ℕ) : Prop where
  x_nonneg : 0 ≤ x
  x_lt_one : x < 1
  scope : ∀ i, FinProb.DependsOn (Bad i) (sc i)
  degree : ∀ i, (Finset.univ.filter fun j => j ≠ i ∧ ¬ Disjoint (sc i) (sc j)).card ≤ Δ
  prob : ∀ i, (FinProb.pi P).pr (Bad i) ≤ x * (1 - x) ^ Δ

/-- Conditional avoidance on a product law with free coordinates (Lemma 3.4 and its independent-variables case):
the avoidance event has positive mass, and conditioning on it costs at most `(1 - x)^{-#T}` against any bound `B`
for the integral over the coordinates `U`, where `T` is the set of events whose scopes meet `U`. -/
def CondProductBound : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {α : V → Type} [∀ v, Fintype (α v)]
    [∀ v, DecidableEq (α v)] (P : ∀ v, FinProb (α v)) {I : Type} [Fintype I] [DecidableEq I]
    (Bad : I → (∀ v, α v) → Prop) (sc : I → Finset V) (x : ℝ) (Δ : ℕ),
    LLLInput P Bad sc x Δ →
      0 < (FinProb.pi P).pr (fun ω => ∀ i, ¬ Bad i ω) ∧
      ∀ (U : Finset V) (Φ : (∀ v, α v) → ℝ), (∀ ω, 0 ≤ Φ ω) → ∀ B : ℝ,
        (∀ ω, ∑ a : (∀ v : U, α v), (∏ v : U, (P v).w (a v)) * Φ (glue U ω a) ≤ B) →
        (condOr (FinProb.pi P) (fun ω => ∀ i, ¬ Bad i ω)).expect Φ ≤
          ((1 - x) ^ (Finset.univ.filter fun i => ¬ Disjoint (sc i) U).card)⁻¹ * B

/-- SHARED (Lemma 3.4, `S03/ConditionalAvoidance.lean`, independent-variables case; same statement as the
Section 7 node `S07.cond_product_bound`): with events joined when their scopes meet, the avoidance event has
positive mass; removing the events whose scopes meet `U` costs `∏ (1 - x)^{-1}`, and the remaining events do
not read the coordinates in `U`. -/
theorem cond_product_bound : CondProductBound := by
  sorry

end HypercubeRamsey.S08
