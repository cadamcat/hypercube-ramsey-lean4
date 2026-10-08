import HypercubeRamsey.S18.Transitions

namespace HypercubeRamsey.Lane_sol_s18_1b
open Classical S18
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

@[simp] theorem getD_append_last {α : Type*} (pre : List α) (B d : α) :
    (pre ++ [B]).getD pre.length d = B := by
  rw [List.getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem getD_mem {α : Type*} (order : List α) (q : ℕ) (d : α) (hq : q < order.length) :
    order.getD q d ∈ order := by
  rw [← List.getElem_eq_getD d (h := hq)]
  exact List.getElem_mem hq

private theorem mem_fold_union {α : Type*} [DecidableEq α]
    (L : List (Finset α)) (A : Finset α) (a : α) :
    a ∈ L.foldl (fun A B => A ∪ B) A ↔ a ∈ A ∨ ∃ B ∈ L, a ∈ B := by
  induction L generalizing A with
  | nil => simp
  | cons B L ih => simp [List.foldl_cons, ih, Finset.mem_union]; aesop

theorem prefix_step (D : LateData hPT) (order : List (Finset (Fin (T.S.n k))))
    (q : ℕ) (hq : q < order.length) :
    D.prefixTests order (q + 1) = D.prefixTests order q ∪ order.getD q ∅ := by
  unfold LateData.prefixTests
  rw [List.take_succ_eq_append_getElem hq, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [List.getElem_eq_getD ∅]

theorem order_batch (D : LateData hPT) (b : Pos T k)
    (order : List (Finset (Fin (T.S.n k)))) (horder : order ∈ D.testOrders b)
    (B : Finset (Fin (T.S.n k))) (hB : B ∈ order) :
    B = PT.tiling.Icoord (D.geom.patchOf b) ∨ ∃ a, B = {a} := by
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := Finset.univ \ intern
  let base := extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k)))) ++
    (if intern = ∅ then [] else [intern])
  have hbase : ∀ B ∈ base, B = intern ∨ ∃ a, B = {a} := by
    intro B hB
    simp only [base, List.mem_append, List.mem_map] at hB
    rcases hB with ⟨a, _, rfl⟩ | hi
    · exact Or.inr ⟨a, rfl⟩
    · by_cases he : intern = ∅ <;> simp [he] at hi
      exact Or.inl hi
  change order ∈ base :: extern.toList.map
    (fun a => base.filter (fun B => B ≠ {a}) ++ [{a}]) at horder
  rcases List.mem_cons.mp horder with rfl | hm
  · exact hbase B hB
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
    simp only [List.mem_append, List.mem_singleton] at hB
    rcases hB with hf | rfl
    · exact hbase B (List.mem_filter.mp hf).1
    · exact Or.inr ⟨a, rfl⟩

theorem order_length (D : LateData hPT) (b : Pos T k)
    (order : List (Finset (Fin (T.S.n k)))) (horder : order ∈ D.testOrders b) :
    order.length ≤ T.S.n k + 2 := by
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := Finset.univ \ intern
  let base := extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k)))) ++
    (if intern = ∅ then [] else [intern])
  have hext : extern.card ≤ T.S.n k := by
    simpa using Finset.card_le_card (Finset.subset_univ extern)
  have hb : base.length ≤ T.S.n k + 1 := by
    dsimp [base]
    split_ifs <;> simp_all <;> omega
  change order ∈ base :: extern.toList.map
    (fun a => base.filter (fun B => B ≠ {a}) ++ [{a}]) at horder
  rcases List.mem_cons.mp horder with rfl | hm
  · omega
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
    have hf := List.length_filter_le (l := base) (fun B => B ≠ {a})
    simp only [List.length_append, List.length_singleton]
    omega

/-- Every coordinate has a designated order ending with its deletion batch. -/
theorem deletion_order (D : LateData hPT) (b : Pos T k) (a : Fin (T.S.n k)) :
    ∃ pre : List (Finset (Fin (T.S.n k))),
      let intern := PT.tiling.Icoord (D.geom.patchOf b)
      let omitted := if a ∈ intern then intern else {a}
      pre ++ [omitted] ∈ D.testOrders b ∧
      D.prefixTests (pre ++ [omitted]) pre.length = Finset.univ \ omitted ∧
      D.prefixTests (pre ++ [omitted]) (pre.length + 1) = Finset.univ := by
  let intern := PT.tiling.Icoord (D.geom.patchOf b)
  let extern := Finset.univ \ intern
  let ext := extern.toList.map (fun a => ({a} : Finset (Fin (T.S.n k))))
  let base := ext ++ (if intern = ∅ then [] else [intern])
  have hbase : base ∈ D.testOrders b := List.mem_cons_self
  have hfold : ∀ L : List (Finset (Fin (T.S.n k))), ∀ t,
      t ∈ L.foldl (fun A B => A ∪ B) ∅ ↔ ∃ B ∈ L, t ∈ B := by
    intro L t
    simp [mem_fold_union]
  have hex : ∀ t, (∃ B ∈ ext, t ∈ B) ↔ t ∈ extern := by
    intro t
    simp [ext]
  have htotal : ∀ t, (∃ B ∈ base, t ∈ B) := by
    intro t
    by_cases hi : t ∈ intern
    · refine ⟨intern, ?_, hi⟩
      have hn : intern ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨t, hi⟩
      simp [base, hn]
    · obtain ⟨B, hB, ht⟩ := (hex t).mpr (by simp [extern, hi])
      exact ⟨B, List.mem_append_left _ hB, ht⟩
  by_cases ha : a ∈ intern
  · have hn : intern ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩
    have hp : D.prefixTests (ext ++ [intern]) ext.length = extern := by
      ext t
      simp only [LateData.prefixTests, List.take_left, hfold, hex]
    refine ⟨ext, ?_⟩
    change ext ++ [if a ∈ intern then intern else {a}] ∈ D.testOrders b ∧
      D.prefixTests (ext ++ [if a ∈ intern then intern else {a}]) ext.length =
        Finset.univ \ (if a ∈ intern then intern else {a}) ∧
      D.prefixTests (ext ++ [if a ∈ intern then intern else {a}]) (ext.length + 1) = Finset.univ
    simp only [if_pos ha]
    refine ⟨by simpa [base, hn] using hbase, hp, ?_⟩
    rw [prefix_step D (ext ++ [intern]) ext.length (by simp), hp]
    ext t
    simp [extern]
  · let pre := base.filter (fun B => B ≠ {a})
    have hp : D.prefixTests (pre ++ [{a}]) pre.length = Finset.univ \ {a} := by
      ext t
      simp only [LateData.prefixTests, List.take_left, hfold, Finset.mem_sdiff,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨B, hB, ht⟩ heq
        subst t
        have hfilter : B ∈ base ∧ B ≠ {a} := by simpa [pre] using hB
        obtain ⟨hB, hne⟩ := hfilter
        simp only [base, List.mem_append, ext, List.mem_map] at hB
        rcases hB with ⟨u, _, rfl⟩ | hi
        · simp only [Finset.mem_singleton] at ht
          subst u
          exact hne rfl
        · by_cases hn : intern = ∅ <;> simp [hn] at hi
          subst B
          exact ha ht
      · intro ht
        obtain ⟨B, hB, htB⟩ := htotal t
        refine ⟨B, ?_, htB⟩
        have hne : B ≠ {a} := by
          intro heq
          subst B
          exact ht (Finset.mem_singleton.mp htB)
        simpa [pre] using And.intro hB hne
    refine ⟨pre, ?_⟩
    change pre ++ [if a ∈ intern then intern else {a}] ∈ D.testOrders b ∧
      D.prefixTests (pre ++ [if a ∈ intern then intern else {a}]) pre.length =
        Finset.univ \ (if a ∈ intern then intern else {a}) ∧
      D.prefixTests (pre ++ [if a ∈ intern then intern else {a}]) (pre.length + 1) = Finset.univ
    simp only [if_neg ha]
    refine ⟨?_, hp, ?_⟩
    · apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      refine ⟨a, ?_, rfl⟩
      change a ∈ extern.toList
      simpa [extern] using ha
    · calc
        _ = D.prefixTests (pre ++ [{a}]) pre.length ∪
            (pre ++ [{a}]).getD pre.length ∅ := prefix_step D _ _ (by simp)
        _ = (Finset.univ \ {a}) ∪ {a} := by rw [hp, getD_append_last]
        _ = Finset.univ := by ext t; simp

end HypercubeRamsey.Lane_sol_s18_1b
