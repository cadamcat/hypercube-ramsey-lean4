import HypercubeRamsey.S18.Defs
import HypercubeRamsey.S16.Comparisons_q_s16_comp1

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

noncomputable def forceInjectionPin {A B : Type*} [DecidableEq B]
    (a : A) (b : B) (x : A ↪ B) : A ↪ B :=
  x.trans (Equiv.swap (x a) b).toEmbedding

 theorem forceInjectionPin_image {A B : Type*} [DecidableEq B]
    (a : A) (b : B) (x : A ↪ B) : forceInjectionPin a b x a = b := by
  simp [forceInjectionPin]

 theorem forceInjectionPin_preserves {A B : Type*} [DecidableEq B]
    (a a' : A) (b b' : B) (x : A ↪ B)
    (hdom : a' ≠ a) (himage : b' ≠ b) (hoccurs : x a' = b') :
    forceInjectionPin a b x a' = b' := by
  change Equiv.swap (x a) b (x a') = b'
  rw [Equiv.swap_apply_of_ne_of_ne (fun h => hdom (x.injective h))]
  · exact hoccurs
  · simpa only [hoccurs] using himage

private theorem forceInjectionPin_preimage {A B : Type*} [DecidableEq B]
    (a : A) (b : B) (y : A ↪ B) (hy : y a = b) (z : B) :
    forceInjectionPin a b (y.trans (Equiv.swap z b).toEmbedding) = y := by
  ext i
  change Equiv.swap (Equiv.swap z b (y a)) b (Equiv.swap z b (y i)) = y i
  rw [hy, Equiv.swap_apply_right, Equiv.swap_apply_self]

noncomputable def forceInjectionPinFiber {A B : Type*} [DecidableEq B]
    (a : A) (b : B) (y : A ↪ B) (hy : y a = b) :
    {x : A ↪ B // forceInjectionPin a b x = y} ≃ B where
  toFun x := x.1 a
  invFun z := ⟨y.trans (Equiv.swap z b).toEmbedding, forceInjectionPin_preimage a b y hy z⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    change Equiv.swap (x.1 a) b (y i) = x.1 i
    have h := congrArg (fun f : A ↪ B => f i) x.2
    change Equiv.swap (x.1 a) b (x.1 i) = y i at h
    rw [← h, Equiv.swap_apply_self]
  right_inv z := by
    change Equiv.swap z b (y a) = z
    rw [hy, Equiv.swap_apply_right]

/-- A single image swap pushes a uniform injection to its law conditioned on the prescribed pin. -/
theorem forceInjectionPin_conditional {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : A) (b : B) (x₀ : A ↪ B)
    (hpos : 0 < ∑ x ∈ Finset.univ.filter (fun x : A ↪ B => x a = b),
      (FinLaw.uniform Finset.univ ⟨x₀, Finset.mem_univ _⟩).w x) :
    FinLaw.map (FinLaw.uniform Finset.univ ⟨x₀, Finset.mem_univ _⟩) (forceInjectionPin a b) =
      FinLaw.cond (FinLaw.uniform Finset.univ ⟨x₀, Finset.mem_univ _⟩)
        (Finset.univ.filter (fun x : A ↪ B => x a = b)) hpos := by
  let P := FinLaw.uniform (Finset.univ : Finset (A ↪ B)) ⟨x₀, Finset.mem_univ _⟩
  let S := Finset.univ.filter (fun x : A ↪ B => x a = b)
  let J := FinLaw.map P (forceInjectionPin a b)
  have hS : S.Nonempty := ⟨forceInjectionPin a b x₀, by simp [S, forceInjectionPin_image]⟩
  have hJzero : ∀ y, y ∉ S → J.w y = 0 := by
    intro y hy
    unfold J FinLaw.map
    apply Finset.sum_eq_zero
    intro x hx
    have hne : forceInjectionPin a b x ≠ y := by
      intro heq
      exact hy (by simp [S, ← heq, forceInjectionPin_image])
    simp [hne]
  have hJconst : ∀ y ∈ S, J.w y = (Fintype.card B : ℝ) / Fintype.card (A ↪ B) := by
    intro y hy
    have hy' : y a = b := (Finset.mem_filter.mp hy).2
    let fiber := Finset.univ.filter (fun x : A ↪ B => forceInjectionPin a b x = y)
    have hcard : fiber.card = Fintype.card B := by
      have he : fiber ≃ {x : A ↪ B // forceInjectionPin a b x = y} :=
        Equiv.subtypeEquivRight (fun x => by simp [fiber])
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (he.trans (forceInjectionPinFiber a b y hy'))
    change (∑ x, if forceInjectionPin a b x = y then P.w x else 0) = _
    simp only [P, FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ]
    rw [← Finset.sum_filter]
    change (∑ x ∈ fiber, (1 : ℝ) / Fintype.card (A ↪ B)) = _
    simp [hcard, div_eq_mul_inv]
  apply Lane_q_s16_comp1.finlaw_eq_of_const_on_set J (FinLaw.cond P S hpos) S hS
    ((Fintype.card B : ℝ) / Fintype.card (A ↪ B))
    ((1 / (Fintype.card (A ↪ B) : ℝ)) / ∑ x ∈ S, P.w x)
  · exact hJzero
  · intro y hy
    simp [FinLaw.cond, hy]
  · exact hJconst
  · intro y hy
    simp [FinLaw.cond, hy, P, FinLaw.uniform]

end HypercubeRamsey.Lane_sol_s18_n4
