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

noncomputable def forceInjectionPins {A B : Type*} [DecidableEq B]
    (target : A ↪ B) (slots : List A) (x : A ↪ B) : A ↪ B :=
  slots.foldl (fun y a => forceInjectionPin a (target a) y) x

/-- Sequential forcing preserves every prescribed mapping already in place. -/
theorem forceInjectionPins_preserves {A B : Type*} [DecidableEq B]
    (target : A ↪ B) (slots : List A) (a : A) (x : A ↪ B)
    (hx : x a = target a) : forceInjectionPins target slots x a = target a := by
  induction slots generalizing x with
  | nil => exact hx
  | cons b slots ih =>
      apply ih
      by_cases hba : a = b
      · subst b
        exact forceInjectionPin_image a (target a) x
      · exact forceInjectionPin_preserves b a (target b) (target a) x hba
          (fun h => hba (target.injective h)) hx

/-- Every slot listed in the partial mapping has its prescribed image after forcing. -/
theorem forceInjectionPins_image {A B : Type*} [DecidableEq B]
    (target : A ↪ B) (slots : List A) (a : A) (ha : a ∈ slots) (x : A ↪ B) :
    forceInjectionPins target slots x a = target a := by
  induction slots generalizing x with
  | nil => simp at ha
  | cons b slots ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact forceInjectionPins_preserves target slots a (forceInjectionPin a (target a) x)
          (forceInjectionPin_image a (target a) x)
      · exact ih ha (forceInjectionPin b (target b) x)

/-- Full partial-map forcing preserves an occurring mapping disjoint in domain and image. -/
theorem forceInjectionPins_nonneighbor {A B : Type*} [DecidableEq B]
    (target : A ↪ B) (slots : List A) (a : A) (b : B) (x : A ↪ B)
    (hdom : a ∉ slots) (himage : ∀ i ∈ slots, b ≠ target i) (hx : x a = b) :
    forceInjectionPins target slots x a = b := by
  induction slots generalizing x with
  | nil => exact hx
  | cons i slots ih =>
      have hai : a ≠ i := fun h => hdom (List.mem_cons.mpr (Or.inl h))
      exact ih (forceInjectionPin i (target i) x) (fun h => hdom (List.mem_cons.mpr (Or.inr h)))
        (fun j hj => himage j (List.mem_cons.mpr (Or.inr hj)))
        (forceInjectionPin_preserves i a (target i) b x hai
          (himage i (by simp)) hx)

noncomputable def injectionPinSet {A B : Type*} [Fintype A] [Fintype B]
    (target : A ↪ B) (fixed : Finset A) : Finset (A ↪ B) :=
  Finset.univ.filter fun x => ∀ i ∈ fixed, x i = target i

theorem mem_injectionPinSet {A B : Type*} [Fintype A] [Fintype B]
    (target : A ↪ B) (fixed : Finset A) (x : A ↪ B) :
    x ∈ injectionPinSet target fixed ↔ ∀ i ∈ fixed, x i = target i := by
  simp [injectionPinSet]

/-- Fibers of the next swap have one preimage for each image not used by earlier pins. -/
noncomputable def forceInjectionPinRestrictedFiber {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (target : A ↪ B) (fixed : Finset A)
    (a : A) (ha : a ∉ fixed) (y : A ↪ B)
    (hy : y ∈ injectionPinSet target (insert a fixed)) :
    {x : A ↪ B // x ∈ injectionPinSet target fixed ∧
      forceInjectionPin a (target a) x = y} ≃ {z : B // ∀ i ∈ fixed, z ≠ target i} where
  toFun x := ⟨x.1 a, by
    intro i hi heq
    have hx := (mem_injectionPinSet target fixed x.1).1 x.2.1 i hi
    exact ha ((x.1.injective (heq.trans hx.symm)).symm ▸ hi)⟩
  invFun z := ⟨y.trans (Equiv.swap z.1 (target a)).toEmbedding, by
    constructor
    · apply (mem_injectionPinSet target fixed _).2
      intro i hi
      have hya := (mem_injectionPinSet target (insert a fixed) y).1 hy a (Finset.mem_insert_self a fixed)
      have hyi := (mem_injectionPinSet target (insert a fixed) y).1 hy i (Finset.mem_insert_of_mem hi)
      change Equiv.swap z.1 (target a) (y i) = target i
      rw [hyi, Equiv.swap_apply_of_ne_of_ne (Ne.symm (z.2 i hi))
        (fun h => ha ((target.injective h : i = a) ▸ hi))]
    · exact forceInjectionPin_preimage a (target a) y
        ((mem_injectionPinSet target (insert a fixed) y).1 hy a (Finset.mem_insert_self a fixed)) z.1⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    change Equiv.swap (x.1 a) (target a) (y i) = x.1 i
    have h := congrArg (fun f : A ↪ B => f i) x.2.2
    change Equiv.swap (x.1 a) (target a) (x.1 i) = y i at h
    rw [← h, Equiv.swap_apply_self]
  right_inv z := by
    apply Subtype.ext
    change Equiv.swap z.1 (target a) (y a) = z.1
    rw [(mem_injectionPinSet target (insert a fixed) y).1 hy a (Finset.mem_insert_self a fixed),
      Equiv.swap_apply_right]

theorem injectionPinSet_nonempty {A B : Type*} [Fintype A] [Fintype B]
    (target : A ↪ B) (fixed : Finset A) : (injectionPinSet target fixed).Nonempty := by
  exact ⟨target, by simp [injectionPinSet]⟩

/-- Each next swap is exact even after conditioning on all earlier pins. -/
theorem forceInjectionPin_restricted {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (target : A ↪ B) (fixed : Finset A)
    (a : A) (ha : a ∉ fixed) :
    FinLaw.map (FinLaw.uniform (injectionPinSet target fixed)
        (injectionPinSet_nonempty target fixed)) (forceInjectionPin a (target a)) =
      FinLaw.uniform (injectionPinSet target (insert a fixed))
        (injectionPinSet_nonempty target (insert a fixed)) := by
  let S := injectionPinSet target fixed
  let S' := injectionPinSet target (insert a fixed)
  let P := FinLaw.uniform S (injectionPinSet_nonempty target fixed)
  let J := FinLaw.map P (forceInjectionPin a (target a))
  let U := FinLaw.uniform S' (injectionPinSet_nonempty target (insert a fixed))
  have hforce : ∀ x ∈ S, forceInjectionPin a (target a) x ∈ S' := by
    intro x hx
    apply (mem_injectionPinSet target (insert a fixed) _).2
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact forceInjectionPin_image i (target i) x
    · exact forceInjectionPin_preserves a i (target a) (target i) x
        (fun h => ha (h ▸ hi)) (fun h => ha ((target.injective h) ▸ hi))
        ((mem_injectionPinSet target fixed x).1 hx i hi)
  have hzero : ∀ y, y ∉ S' → J.w y = 0 := by
    intro y hy
    unfold J FinLaw.map
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hs : x ∈ S
    · have hf : forceInjectionPin a (target a) x ≠ y := fun h => hy (h ▸ hforce x hs)
      simp [hf]
    · simp [P, FinLaw.uniform, hs]
  have hconst : ∀ y ∈ S', J.w y =
      (Fintype.card {z : B // ∀ i ∈ fixed, z ≠ target i} : ℝ) / S.card := by
    intro y hy
    let fiber := Finset.univ.filter (fun x : A ↪ B =>
      x ∈ S ∧ forceInjectionPin a (target a) x = y)
    have hcard : fiber.card = Fintype.card {z : B // ∀ i ∈ fixed, z ≠ target i} := by
      have he : fiber ≃ {x : A ↪ B // x ∈ S ∧ forceInjectionPin a (target a) x = y} :=
        Equiv.subtypeEquivRight (fun x => by simp [fiber])
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (he.trans (forceInjectionPinRestrictedFiber target fixed a ha y hy))
    change (∑ x, if forceInjectionPin a (target a) x = y then P.w x else 0) = _
    have hterm : ∀ x : A ↪ B,
        (if forceInjectionPin a (target a) x = y then P.w x else 0) =
          if x ∈ S ∧ forceInjectionPin a (target a) x = y then 1 / (S.card : ℝ) else 0 := by
      intro x
      by_cases hs : x ∈ S <;> by_cases hf : forceInjectionPin a (target a) x = y <;>
        simp [P, FinLaw.uniform, hs, hf]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    change (∑ x ∈ fiber, (1 : ℝ) / S.card) = _
    simp [hcard, div_eq_mul_inv]
  exact Lane_q_s16_comp1.finlaw_eq_of_const_on_set J U S'
    (injectionPinSet_nonempty target (insert a fixed)) _ (1 / (S'.card : ℝ)) hzero
    (by intro y hy; simp [U, FinLaw.uniform, hy]) hconst
    (by intro y hy; simp [U, FinLaw.uniform, hy])

private theorem swapMapMap {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (P : FinLaw A) (f : A → B) (g : B → C) :
    FinLaw.map (FinLaw.map P f) g = FinLaw.map P (fun x => g (f x)) := by
  apply Lane_q_s16_comp1.finlaw_ext
  intro z
  unfold FinLaw.map
  have hterm : ∀ y,
      (if g y = z then ∑ x, if f x = y then P.w x else 0 else 0) =
        ∑ x, if f x = y then (if g (f x) = z then P.w x else 0) else 0 := by
    intro y
    by_cases hg : g y = z
    · simp only [hg, ite_true]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hf : f x = y <;> simp [hf, hg]
    · simp only [hg, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hf : f x = y <;> simp [hf, hg]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

private theorem forceInjectionPin_fixed {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (target : A ↪ B) (fixed : Finset A)
    (a : A) (ha : a ∈ fixed) :
    FinLaw.map (FinLaw.uniform (injectionPinSet target fixed)
        (injectionPinSet_nonempty target fixed)) (forceInjectionPin a (target a)) =
      FinLaw.uniform (injectionPinSet target fixed) (injectionPinSet_nonempty target fixed) := by
  apply Lane_q_s16_comp1.finlaw_ext
  intro y
  unfold FinLaw.map
  have hterm : ∀ x : A ↪ B,
      (if forceInjectionPin a (target a) x = y then
        (FinLaw.uniform (injectionPinSet target fixed) (injectionPinSet_nonempty target fixed)).w x else 0) =
      if x = y then (FinLaw.uniform (injectionPinSet target fixed)
        (injectionPinSet_nonempty target fixed)).w x else 0 := by
    intro x
    by_cases hx : x ∈ injectionPinSet target fixed
    · have hpin := (mem_injectionPinSet target fixed x).1 hx a ha
      have hf : forceInjectionPin a (target a) x = x := by
        ext i
        change Equiv.swap (x a) (target a) (x i) = x i
        rw [hpin, Equiv.swap_self]
        rfl
      rw [hf]
    · simp [FinLaw.uniform, hx]
  simp_rw [hterm]
  simp

/-- The complete successive-swap map has the uniform conditional law of a partial mapping. -/
theorem forceInjectionPins_uniform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (target : A ↪ B) (slots : List A) (fixed : Finset A) :
    FinLaw.map (FinLaw.uniform (injectionPinSet target fixed)
        (injectionPinSet_nonempty target fixed)) (forceInjectionPins target slots) =
      FinLaw.uniform (injectionPinSet target (fixed ∪ slots.toFinset))
    (injectionPinSet_nonempty target (fixed ∪ slots.toFinset)) := by
  classical
  induction slots generalizing fixed with
  | nil =>
      apply Lane_q_s16_comp1.finlaw_ext
      intro y
      simp only [forceInjectionPins, List.foldl_nil, FinLaw.map,
        List.toFinset_nil, Finset.union_empty]
      rw [Finset.sum_eq_single y]
      · simp
      · intro x hx hxy
        simp [hxy]
      · intro hy
        exact False.elim (hy (Finset.mem_univ y))
  | cons a slots ih =>
      have hstep : FinLaw.map (FinLaw.uniform (injectionPinSet target fixed)
          (injectionPinSet_nonempty target fixed)) (forceInjectionPin a (target a)) =
        FinLaw.uniform (injectionPinSet target (insert a fixed))
          (injectionPinSet_nonempty target (insert a fixed)) := by
        by_cases ha : a ∈ fixed
        · simpa only [Finset.insert_eq_of_mem ha] using forceInjectionPin_fixed target fixed a ha
        · exact forceInjectionPin_restricted target fixed a ha
      have hcomp : forceInjectionPins target (a :: slots) = fun x =>
          forceInjectionPins target slots (forceInjectionPin a (target a) x) := rfl
      rw [hcomp, ← swapMapMap, hstep, ih]
      congr 2
      simp [Finset.insert_union, Finset.union_insert]

end HypercubeRamsey.Lane_sol_s18_n4
