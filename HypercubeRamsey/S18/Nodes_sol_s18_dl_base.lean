import HypercubeRamsey.S18.Lists

namespace HypercubeRamsey.S18.Lane_sol_s18_dl

open Classical
open scoped BigOperators

private theorem equal_disjoint_subsets {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (r : ℕ) :
    ∃ pools : Fin r → Finset α,
      (∀ j, pools j ⊆ S) ∧
      (∀ j j', j ≠ j' → Disjoint (pools j) (pools j')) ∧
      ∀ j, (pools j).card = S.card / r := by
  let e : {y : α // y ∈ S} ≃ Fin S.card :=
    (Fintype.equivFin _).trans (finCongr (by simp))
  have hc : r * (S.card / r) ≤ S.card := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self S.card r
  let read : Fin r × Fin (S.card / r) → α := fun p =>
    (e.symm (Fin.castLE hc (finProdFinEquiv p))).1
  have hinj : Function.Injective read := by
    intro p q hpq
    apply finProdFinEquiv.injective
    apply Fin.castLE_injective hc
    apply e.symm.injective
    exact Subtype.ext hpq
  let pools (j : Fin r) := Finset.univ.image fun t : Fin (S.card / r) => read (j, t)
  refine ⟨pools, ?_, ?_, ?_⟩
  · intro j y hy
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    exact (e.symm (Fin.castLE hc (finProdFinEquiv (j, t)))).2
  · intro j j' hne
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t', _, heq⟩ := Finset.mem_image.mp hy'
    exact hne (congrArg Prod.fst (hinj heq)).symm
  · intro j
    have hj : Function.Injective (fun t : Fin (S.card / r) => read (j, t)) := by
      intro t t' h
      exact congrArg Prod.snd (hinj h)
    simpa only [pools, Finset.card_image_of_injective _ hj,
      Finset.card_univ, Fintype.card_fin]

theorem late_process_base_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (hPT : PT.Valid) (F : FreshCell G) :
    ∃ B : LateProcessBase F,
      (∀ j t, j.val ≤ t.val → B.processed j ⊆ B.processed t) ∧
      (∀ j t, j.val < t.val → B.classes j ⊆ B.processed t) := by
  obtain ⟨pools, hsub, hdisj, hcard⟩ := equal_disjoint_subsets PT.tiling.reserveY G.r
  let classes (j : Fin G.r) := Finset.univ.filter fun b : Pos T k => G.classOf b = some j
  let processed (j : Fin (G.r + 1)) := Finset.univ.filter fun b : Pos T k =>
    ∃ t : Fin G.r, t.val < j.val ∧ G.classOf b = some t
  have hmono : ∀ j t, j.val ≤ t.val → processed j ⊆ processed t := by
    intro j t hjt b hb
    obtain ⟨s, hs, hclass⟩ := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, lt_of_lt_of_le hs hjt, hclass⟩
  have hbefore : ∀ j t, j.val < t.val → classes j ⊆ processed t := by
    intro j t hjt b hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, j, hjt, (Finset.mem_filter.mp hb).2⟩
  have hstep : ∀ j : Fin G.r, processed j.castSucc ∪ classes j = processed j.succ := by
    intro j
    ext b
    simp only [processed, classes, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro (⟨s, hs, hclass⟩ | hclass)
      · exact ⟨s, by omega, hclass⟩
      · exact ⟨j, by omega, hclass⟩
    · rintro ⟨s, hs, hclass⟩
      by_cases hsj : s.val < j.val
      · exact Or.inl ⟨s, hsj, hclass⟩
      · have heq : s = j := Fin.ext (by omega)
        exact Or.inr (heq ▸ hclass)
  have hfresh : ∀ j : Fin G.r, Disjoint (classes j) (processed j.castSucc) := by
    intro j
    apply Finset.disjoint_left.mpr
    intro b hb hp
    have hb' := (Finset.mem_filter.mp hb).2
    obtain ⟨s, hs, hclass⟩ := (Finset.mem_filter.mp hp).2
    have heq : j = s := Option.some.inj (hb'.symm.trans hclass)
    subst s
    exact (Nat.lt_irrefl j.val) hs
  have hlast : processed (Fin.last G.r) =
      Finset.univ.filter fun b => ∃ j : Fin G.r, G.classOf b = some j := by
    ext b
    simp only [processed, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
    constructor
    · rintro ⟨j, _, hj⟩
      exact ⟨j, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, j.isLt, hj⟩
  let B : LateProcessBase F := {
    classes := classes
    class_disjoint := by
      intro j j' hne
      apply Finset.disjoint_left.mpr
      intro b hb hb'
      exact hne (Option.some.inj
        ((Finset.mem_filter.mp hb).2.symm.trans (Finset.mem_filter.mp hb').2))
    class_of_spec := by intro b j; simp [classes]
    processed := processed
    processed_zero := by simp [processed]
    processed_step := hstep
    class_fresh := hfresh
    processed_last := hlast
    latePool := pools
    latePool_reserve := hsub
    latePool_disjoint := hdisj
    latePool_card := by
      intro j
      rw [hcard j, hPT.tiling_valid.reserveY_card] }
  exact ⟨B, hmono, hbefore⟩

end HypercubeRamsey.S18.Lane_sol_s18_dl
