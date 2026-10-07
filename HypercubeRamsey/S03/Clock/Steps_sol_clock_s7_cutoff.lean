import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_survival
import HypercubeRamsey.S03.Clock.Steps_sol_clock_s7_cross

set_option autoImplicit false

namespace HypercubeRamsey.Lane_sol_clock_s7

open Clock
open scoped BigOperators

/-- Cross edges are indexed once in each orientation from a queried target. -/
abbrev CrossIndex {R : Type*} {g : ℕ} (S : Finset R) (L : Finset (Fin g)) :=
  (S × {y : Fin g // y ∉ L}) ⊕ (S × {b : R // b ∉ S})

def crossEdge {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) : CrossIndex S L → RowLabel R g
  | .inl (a, y) => (a.1, y.1)
  | .inr (a, b) => (b.1, lab a.1 (o a.1))

theorem crossEdge_injective {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (hInj : Set.InjOn (fun a => lab a (o a)) S) :
    Function.Injective (crossEdge S L o lab) := by
  intro c d h
  cases c with
  | inl p =>
    cases d with
    | inl q =>
      apply congrArg Sum.inl
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst h
      · apply Subtype.ext
        exact congrArg Prod.snd h
    | inr q =>
      have hrow : p.1.1 = q.2.1 := congrArg Prod.fst h
      exact False.elim (q.2.2 (hrow ▸ p.1.2))
  | inr p =>
    cases d with
    | inl q =>
      have hrow : p.2.1 = q.1.1 := congrArg Prod.fst h
      exact False.elim (p.2.2 (hrow.symm ▸ q.1.2))
    | inr q =>
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Subtype.ext
        exact hInj p.1.2 q.1.2 (congrArg Prod.snd h)
      · apply Subtype.ext
        exact congrArg Prod.fst h

/-- The edge coordinates used to determine the outside background. -/
def backgroundEdges {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    (S : Finset R) (L : Finset (Fin g)) : Finset (RowLabel R g) :=
  Finset.univ.filter (fun e => e.1 ∉ S ∧ e.2 ∉ L)

theorem crossEdge_not_background {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g)
    (hL : ∀ a ∈ S, lab a (o a) ∈ L) (c : CrossIndex S L) :
    crossEdge S L o lab c ∉ backgroundEdges S L := by
  cases c with
  | inl p => simp [crossEdge, backgroundEdges, p.1.2]
  | inr p => simp [crossEdge, backgroundEdges, hL p.1.1 p.1.2]

theorem crossEdge_ne_target {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (hL : ∀ a ∈ S, lab a (o a) ∈ L)
    (c : CrossIndex S L) (a : R) (ha : a ∈ S) :
    crossEdge S L o lab c ≠ (a, lab a (o a)) := by
  intro h
  cases c with
  | inl p =>
    have hy : p.2.1 = lab a (o a) := congrArg Prod.snd h
    exact p.2.2 (hy.symm ▸ hL a ha)
  | inr p =>
    have hb : p.2.1 = a := congrArg Prod.fst h
    exact p.2.2 (hb.symm ▸ ha)

/-- Extend cross-edge cutoffs by zero on target, background and unused internal edges. -/
noncomputable def extendCrossCutoff {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (cut : CrossIndex S L → ℕ) : RowLabel R g → ℕ :=
  Function.extend (crossEdge S L o lab) cut (fun _ => 0)

theorem extendCrossCutoff_apply {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (hInj : Set.InjOn (fun a => lab a (o a)) S)
    (cut : CrossIndex S L → ℕ) (c : CrossIndex S L) :
    extendCrossCutoff S L o lab cut (crossEdge S L o lab c) = cut c :=
  (crossEdge_injective S L o lab hInj).extend_apply cut (fun _ => 0) c

theorem extendCrossCutoff_target_zero {R : Type*} {g : ℕ} {Ω : R → Type*}
    (S : Finset R) (L : Finset (Fin g)) (o : ∀ a, Ω a)
    (lab : ∀ a, Ω a → Fin g) (hL : ∀ a ∈ S, lab a (o a) ∈ L)
    (cut : CrossIndex S L → ℕ) (a : R) (ha : a ∈ S) :
    extendCrossCutoff S L o lab cut (a, lab a (o a)) = 0 := by
  apply Function.extend_apply'
  rintro ⟨c, hc⟩
  exact crossEdge_ne_target S L o lab hL c a ha hc

theorem extendCrossCutoff_background_zero {R : Type*} [Fintype R] [DecidableEq R]
    {g : ℕ} {Ω : R → Type*} (S : Finset R) (L : Finset (Fin g))
    (o : ∀ a, Ω a) (lab : ∀ a, Ω a → Fin g)
    (hL : ∀ a ∈ S, lab a (o a) ∈ L) (cut : CrossIndex S L → ℕ)
    (e : RowLabel R g) (he : e ∈ backgroundEdges S L) :
    extendCrossCutoff S L o lab cut e = 0 := by
  apply Function.extend_apply'
  rintro ⟨c, hc⟩
  exact crossEdge_not_background S L o lab hL c (hc.symm ▸ he)

end HypercubeRamsey.Lane_sol_clock_s7
