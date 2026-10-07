import HypercubeRamsey.S13.ResidualBounds

namespace HypercubeRamsey.S13

open scoped BigOperators

/-- Partition the initial `d`-blocks of a finite set, leaving only its final remainder. -/
theorem allocation_chunks_exact {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (d : ℕ) (hd : 0 < d) :
    ∃ C : Fin (B.card / d) → Finset α,
      (∀ i, C i ⊆ B) ∧
      (∀ i, (C i).card = d) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C).card = (B.card / d) * d := by
  classical
  let e : {x : α // x ∈ B} ≃ Fin B.card :=
    Fintype.equivFinOfCardEq (by simp)
  let emb : Fin B.card ↪ α :=
    ⟨fun x => (e.symm x).val, by
      intro x y h
      have hs : e.symm x = e.symm y := Subtype.ext h
      exact e.symm.injective hs⟩
  have interval_card (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ B.card) :
      (Finset.univ.filter fun x : Fin B.card => lo ≤ x.val ∧ x.val < hi).card = hi - lo := by
    let f : {x : ℕ // x ∈ Finset.Ico lo hi} ↪ Fin B.card :=
      ⟨fun x => ⟨x.val, (Finset.mem_Ico.mp x.property).2.trans_le hhi⟩, by
        intro x y h
        apply Subtype.ext
        exact congrArg Fin.val h⟩
    have himage : (Finset.Ico lo hi).attach.map f =
        Finset.univ.filter fun x : Fin B.card => lo ≤ x.val ∧ x.val < hi := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hy' : y.val ∈ Finset.Ico lo hi := y.property
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_Ico.mp hy').1,
          (Finset.mem_Ico.mp hy').2⟩
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨_, hloX, hhiX⟩
        let y : {y : ℕ // y ∈ Finset.Ico lo hi} :=
          ⟨x.val, Finset.mem_Ico.mpr ⟨hloX, hhiX⟩⟩
        refine Finset.mem_map.mpr ⟨y, Finset.mem_attach (Finset.Ico lo hi) y, ?_⟩
        exact Fin.ext rfl
    rw [← himage, Finset.card_map, Finset.card_attach]
    simp
  let C : Fin (B.card / d) → Finset α := fun i =>
    (Finset.univ.filter fun x : Fin B.card =>
      i.val * d ≤ x.val ∧ x.val < (i.val + 1) * d).map emb
  have hupper (i : Fin (B.card / d)) : (i.val + 1) * d ≤ B.card := by
    have hi : i.val + 1 ≤ B.card / d := by omega
    calc
      _ ≤ (B.card / d) * d := Nat.mul_le_mul_right d hi
      _ ≤ B.card := Nat.div_mul_le_self _ _
  have hcard (i : Fin (B.card / d)) : (C i).card = d := by
    dsimp [C]
    rw [Finset.card_map]
    have hlo : i.val * d ≤ (i.val + 1) * d :=
      Nat.mul_le_mul_right d (Nat.le_succ _)
    rw [interval_card (i.val * d) ((i.val + 1) * d) hlo (hupper i)]
    rw [Nat.add_mul, one_mul]
    omega
  have hsub (i : Fin (B.card / d)) : C i ⊆ B := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact (e.symm y).property
  have hdisj (i j : Fin (B.card / d)) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    rcases Finset.mem_map.mp hxi with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxj with ⟨b, hb, hbx⟩
    have hab : a = b := emb.injective (hax.trans hbx.symm)
    subst b
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hgap : (i.val + 1) * d ≤ j.val * d :=
        Nat.mul_le_mul_right d (by omega)
      omega
    · have hgap : (j.val + 1) * d ≤ i.val * d :=
        Nat.mul_le_mul_right d (by omega)
      omega
  have hUnion : (Finset.univ.biUnion C).card = (B.card / d) * d := by
    rw [Finset.card_biUnion]
    · simp_rw [hcard]
      simp [Finset.sum_const, nsmul_eq_mul]
    · intro i hi j hj hij
      exact hdisj i j hij
  exact ⟨C, hsub, hcard, hdisj, hUnion⟩

end HypercubeRamsey.S13
