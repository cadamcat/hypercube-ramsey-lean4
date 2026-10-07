import HypercubeRamsey.Framework.Basic

/-!
# Embedding interface

A cube copy across the two host sides from injective maps of the even and the odd roles.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- Even roles: an even number of coordinates equal to `true`. -/
def IsEvenRole {n : ℕ} (v : CubeVertex n) : Prop :=
  Even (Finset.univ.filter (fun i => v i = true)).card

private theorem even_iff_not_even_succ (m : ℕ) : Even m ↔ ¬ Even (m + 1) := by
  constructor
  · intro hm hsucc
    exact (Nat.not_even_iff_odd.mpr hm.add_one) hsucc
  · intro hsucc
    rcases Nat.even_or_odd m with hm | hm
    · exact hm
    · exact (hsucc hm.add_one).elim

private theorem even_succ_iff_not_even (m : ℕ) : Even (m + 1) ↔ ¬ Even m :=
  Nat.even_add_one

private theorem evenRole_flip_of_adj {n : ℕ} {u v : CubeVertex n}
    (h : (cube n).Adj u v) : IsEvenRole u ↔ ¬ IsEvenRole v := by
  classical
  have hone : (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1 := h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin n => u j ≠ v j) := by
    rw [hi]
    simp
  have hdiff : u i ≠ v i := (Finset.mem_filter.mp hi_mem).2
  have hsame : ∀ j, j ≠ i → u j = v j := by
    intro j hji
    by_contra hne
    have hj_mem : j ∈ Finset.univ.filter (fun t : Fin n => u t ≠ v t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hi] at hj_mem
    exact hji (Finset.mem_singleton.mp hj_mem)
  let A := Finset.univ.filter (fun j : Fin n => u j = true)
  let B := Finset.univ.filter (fun j : Fin n => v j = true)
  have hbit : (u i = false ∧ v i = true) ∨ (u i = true ∧ v i = false) := by
    cases hu : u i <;> cases hv : v i <;> simp_all
  rcases hbit with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hset : B = insert i A := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, hu, hv]
      · have hsame' := hsame j hji
        simp [A, B, hji, hsame']
    have hi_notA : i ∉ A := by simp [A, hu]
    have hcard : B.card = A.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notA]
    change Even A.card ↔ ¬ Even B.card
    rw [hcard]
    exact even_iff_not_even_succ A.card
  · have hset : A = insert i B := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, hu, hv]
      · have hsame' := hsame j hji
        simp [A, B, hji, hsame']
    have hi_notB : i ∉ B := by simp [B, hv]
    have hcard : A.card = B.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notB]
    change Even A.card ↔ ¬ Even B.card
    rw [hcard]
    exact even_succ_iff_not_even B.card

/-- Even roles to the first side, odd roles to the second side. -/
theorem cube_copy_of_parts {n N : ℕ} {G : Fin N → Fin N → Prop}
    (fA : {v : CubeVertex n // IsEvenRole v} → Fin N)
    (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (hA : Function.Injective fA) (hB : Function.Injective fB)
    (hedge : ∀ a b, (cube n).Adj a.1 b.1 → G (fA a) (fB b)) :
    Nonempty ((cube n).Copy (crossGraph G)) := by
  classical
  let f : CubeVertex n → Fin N ⊕ Fin N := fun v =>
    if hv : IsEvenRole v then Sum.inl (fA ⟨v, hv⟩)
    else Sum.inr (fB ⟨v, hv⟩)
  have hinj : Function.Injective f := by
    intro u v huv
    by_cases hu : IsEvenRole u <;> by_cases hv : IsEvenRole v
    · have hval : fA ⟨u, hu⟩ = fA ⟨v, hv⟩ := by simpa [f, hu, hv] using huv
      exact congrArg Subtype.val (hA hval)
    · simp [f, hu, hv] at huv
    · simp [f, hu, hv] at huv
    · have hval : fB ⟨u, hu⟩ = fB ⟨v, hv⟩ := by simpa [f, hu, hv] using huv
      exact congrArg Subtype.val (hB hval)
  refine ⟨{
    toHom := {
      toFun := f
      map_rel' := by
        intro u v huv
        by_cases hu : IsEvenRole u
        · have hv : ¬ IsEvenRole v := (evenRole_flip_of_adj huv).mp hu
          simpa [f, hu, hv, crossGraph] using hedge ⟨u, hu⟩ ⟨v, hv⟩ huv
        · have hv : IsEvenRole v := by
            by_contra hvnot
            exact hu ((evenRole_flip_of_adj huv).mpr hvnot)
          simpa [f, hu, hv, crossGraph] using
            hedge ⟨v, hv⟩ ⟨u, hu⟩ huv.symm
    }
    injective' := hinj
  }⟩

/-- Even roles to the second side, odd roles to the first side. -/
theorem cube_copy_of_parts_swap {n N : ℕ} {G : Fin N → Fin N → Prop}
    (fA : {v : CubeVertex n // IsEvenRole v} → Fin N)
    (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (hA : Function.Injective fA) (hB : Function.Injective fB)
    (hedge : ∀ a b, (cube n).Adj a.1 b.1 → G (fB b) (fA a)) :
    Nonempty ((cube n).Copy (crossGraph G)) := by
  classical
  let f : CubeVertex n → Fin N ⊕ Fin N := fun v =>
    if hv : IsEvenRole v then Sum.inr (fA ⟨v, hv⟩)
    else Sum.inl (fB ⟨v, hv⟩)
  have hinj : Function.Injective f := by
    intro u v huv
    by_cases hu : IsEvenRole u <;> by_cases hv : IsEvenRole v
    · have hval : fA ⟨u, hu⟩ = fA ⟨v, hv⟩ := by simpa [f, hu, hv] using huv
      exact congrArg Subtype.val (hA hval)
    · simp [f, hu, hv] at huv
    · simp [f, hu, hv] at huv
    · have hval : fB ⟨u, hu⟩ = fB ⟨v, hv⟩ := by simpa [f, hu, hv] using huv
      exact congrArg Subtype.val (hB hval)
  refine ⟨{
    toHom := {
      toFun := f
      map_rel' := by
        intro u v huv
        by_cases hu : IsEvenRole u
        · have hv : ¬ IsEvenRole v := (evenRole_flip_of_adj huv).mp hu
          simpa [f, hu, hv, crossGraph] using hedge ⟨u, hu⟩ ⟨v, hv⟩ huv
        · have hv : IsEvenRole v := by
            by_contra hvnot
            exact hu ((evenRole_flip_of_adj huv).mpr hvnot)
          simpa [f, hu, hv, crossGraph] using
            hedge ⟨v, hv⟩ ⟨u, hu⟩ huv.symm
    }
    injective' := hinj
  }⟩

/-- Total-map form: one label per role, injective on each parity class (even roles on the first side). -/
theorem copy_of_parity_maps {n N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (f : CubeVertex n → Fin N)
    (hA : Set.InjOn f {v | IsEvenRole v}) (hB : Set.InjOn f {v | ¬ IsEvenRole v})
    (hedge : ∀ a b, (cube n).Adj a b → IsEvenRole a → Hits E c (f a) (f b)) :
    Nonempty ((cube n).Copy (crossGraph (Hits E c))) := sorry

/-- Total-map form with even roles on the second side. -/
theorem copy_of_parity_maps_swap {n N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (f : CubeVertex n → Fin N)
    (hA : Set.InjOn f {v | IsEvenRole v}) (hB : Set.InjOn f {v | ¬ IsEvenRole v})
    (hedge : ∀ a b, (cube n).Adj a b → IsEvenRole a → Hits E c (f b) (f a)) :
    Nonempty ((cube n).Copy (crossGraph (Hits E c))) := sorry

/-- A copy for the transposed relation gives one for the original. -/
theorem copy_transpose {n N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (h : Nonempty ((cube n).Copy (crossGraph (Hits (transposeRel E) c)))) :
    Nonempty ((cube n).Copy (crossGraph (Hits E c))) := sorry

end HypercubeRamsey
