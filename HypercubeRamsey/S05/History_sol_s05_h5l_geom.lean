import HypercubeRamsey.S05.History_sol_s05_h5l_local

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical OAI.HypercubeRamsey

noncomputable section
set_option maxHeartbeats 800000

private theorem filter_agree {n : ℕ} (C : Finset (Fin n)) (x y : CubeVertex n)
    (h : ∀ a ∈ C, x a = y a) :
    C.filter (fun a => x a = true) = C.filter (fun a => y a = true) := by
  ext a
  by_cases ha : a ∈ C
  · simp only [Finset.mem_filter, ha, true_and, h a ha]
  · simp [ha]

theorem adjacent_flip {n : ℕ} (x y : CubeVertex n) (hxy : (cube n).Adj x y) :
    ∃ a, y = flipVertex5 x a := by
  change _root_.hammingDist x y = 1 at hxy
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hxy
  have hneq : x a ≠ y a := by
    have hh : a ∈ Finset.univ.filter (fun b => x b ≠ y b) := by rw [ha]; simp
    exact (Finset.mem_filter.mp hh).2
  refine ⟨a, ?_⟩
  funext b
  by_cases hb : b = a
  · subst b
    cases hx : x a <;> cases hy : y a <;> simp_all [flipVertex5]
  · have he : x b = y b := by
      by_contra h
      have hh : b ∈ Finset.univ.filter (fun b => x b ≠ y b) := by simp [h]
      rw [ha] at hh
      exact hb (Finset.mem_singleton.mp hh)
    simp [flipVertex5, hb, he]

variable {n m : ℕ} (g : ChunkGeometry5 n m)

theorem fineCount_flip_outside (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∉ g.fineChunks i) : g.fineCount (flipVertex5 x a) i = g.fineCount x i := by
  unfold ChunkGeometry5.fineCount
  congr 1
  apply filter_agree
  intro b hb
  have hba : b ≠ a := by intro he; subst b; exact ha hb
  simp [flipVertex5, hba]

theorem fineCount_flip_inside (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∈ g.fineChunks i) :
    g.fineCount (flipVertex5 x a) i + 1 = g.fineCount x i ∨
      g.fineCount x i + 1 = g.fineCount (flipVertex5 x a) i := by
  let C := g.fineChunks i
  by_cases hx : x a = true
  · have hf : C.filter (fun b => flipVertex5 x a b = true) =
        (C.filter (fun b => x b = true)).erase a := by
      ext b
      by_cases hb : b = a
      · subst b; simp [C, ha, hx, flipVertex5]
      · have hf : flipVertex5 x a b = x b := Function.update_of_ne hb _ _
        constructor
        · intro hh
          have hm := Finset.mem_filter.mp hh
          exact Finset.mem_erase.mpr ⟨hb, Finset.mem_filter.mpr ⟨hm.1, hf.symm.trans hm.2⟩⟩
        · intro hh
          have hm := Finset.mem_filter.mp (Finset.mem_erase.mp hh).2
          exact Finset.mem_filter.mpr ⟨hm.1, hf.trans hm.2⟩
    have hm : a ∈ C.filter (fun b => x b = true) := by simp [C, ha, hx]
    left
    change (C.filter (fun b => flipVertex5 x a b = true)).card + 1 = (C.filter (fun b => x b = true)).card
    rw [hf]
    exact Finset.card_erase_add_one hm
  · have hfalse : x a = false := by cases h : x a <;> simp_all
    have hf : C.filter (fun b => flipVertex5 x a b = true) =
        insert a (C.filter (fun b => x b = true)) := by
      ext b
      by_cases hb : b = a
      · subst b; simp [C, ha, hfalse, flipVertex5]
      · have hf : flipVertex5 x a b = x b := Function.update_of_ne hb _ _
        constructor
        · intro hh
          have hm := Finset.mem_filter.mp hh
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hm.1, hf.symm.trans hm.2⟩))
        · intro hh
          rcases Finset.mem_insert.mp hh with he | hm
          · exact (hb he).elim
          · have hm' := Finset.mem_filter.mp hm
            exact Finset.mem_filter.mpr ⟨hm'.1, hf.trans hm'.2⟩
    have hm : a ∉ C.filter (fun b => x b = true) := by simp [C, hx]
    right
    change (C.filter (fun b => x b = true)).card + 1 = (C.filter (fun b => flipVertex5 x a b = true)).card
    rw [hf, Finset.card_insert_of_notMem hm]

theorem fine_counts_single_change (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∈ g.fineChunks i) :
    ∀ j, j ≠ i → g.fineCount (flipVertex5 x a) j = g.fineCount x j := by
  intro j hji
  apply fineCount_flip_outside g x a j
  intro haj
  exact Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 j i hji) haj ha

private theorem filter_erase_counts (x y : CubeVertex n) (i : Fin m)
    (h : ∀ j, j ≠ i → g.fineCount x j = g.fineCount y j) :
    (Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount x j) g.fineLength ≤ 11)).erase i =
      (Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount y j) g.fineLength ≤ 11)).erase i := by
  ext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj, h j hj]

/-- Crossing from a high role to a low neighbour changes a fringe chunk, preserving its sign and
flippability. The count fact is the reason the high-record low scope is only `O(J)`. -/
theorem crossing_fine_features (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∈ g.fineChunks i) (hdrop : g.severity (flipVertex5 x a) < g.severity x) :
    g.sign (flipVertex5 x a) = g.sign x ∧ g.flippable (flipVertex5 x a) = g.flippable x ∧
      g.severity x = g.severity (flipVertex5 x a) + 1 := by
  let y := flipVertex5 x a
  let Sx := Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount x j) g.fineLength ≤ 11)
  let Sy := Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount y j) g.fineLength ≤ 11)
  have hcounts := fine_counts_single_change g x a i ha
  have he : Sx.erase i = Sy.erase i := filter_erase_counts g x y i (fun j hj => (hcounts j hj).symm)
  have hc := congrArg Finset.card he
  have hxmem : i ∈ Sx := by
    by_contra hh
    have hle : Sx.card ≤ Sy.card := by
      rw [Finset.erase_eq_of_notMem hh] at hc
      exact hc.trans_le (Finset.card_le_card (Finset.erase_subset _ _))
    exact (not_le_of_gt hdrop) hle
  have hymem : i ∉ Sy := by
    intro hh
    rw [Finset.card_erase_of_mem hxmem, Finset.card_erase_of_mem hh] at hc
    have : Sx.card = Sy.card := by
      have hxpos := Finset.card_pos.mpr ⟨i, hxmem⟩
      have hypos := Finset.card_pos.mpr ⟨i, hh⟩
      omega
    exact (ne_of_gt hdrop) this
  have hj : g.severity x = g.severity y + 1 := by
    rw [Finset.card_erase_of_mem hxmem, Finset.erase_eq_of_notMem hymem] at hc
    have hxpos := Finset.card_pos.mpr ⟨i, hxmem⟩
    change Sx.card = Sy.card + 1
    omega
  have hdx : Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11 := (Finset.mem_filter.mp hxmem).2
  have hdy : 11 < Nat.dist (2 * g.fineCount y i) g.fineLength := by
    have hh : ¬ Nat.dist (2 * g.fineCount y i) g.fineLength ≤ 11 := by
      intro hh; exact hymem (by simp [Sy, hh])
    omega
  have hstep := fineCount_flip_inside g x a i ha
  have hsign : (g.fineLength < 2 * g.fineCount y i) = (g.fineLength < 2 * g.fineCount x i) := by
    apply propext
    simp only [Nat.dist] at hdx hdy
    dsimp only [y] at *
    omega
  have hxnot : Nat.dist (2 * g.fineCount x i) g.fineLength ≠ 1 := by
    simp only [Nat.dist] at hdx hdy ⊢
    dsimp only [y] at *
    omega
  have hynot : Nat.dist (2 * g.fineCount y i) g.fineLength ≠ 1 := by omega
  dsimp only [y] at hsign hynot
  refine ⟨?_, ?_, hj⟩
  · funext j
    by_cases hji : j = i
    · subst j; simp only [ChunkGeometry5.sign, hsign]
    · simp only [ChunkGeometry5.sign, hcounts j hji]
  · ext j
    by_cases hji : j = i
    · subst j; simp [ChunkGeometry5.flippable, hxnot, hynot]
    · simp [ChunkGeometry5.flippable, hcounts j hji]

theorem flippable_card_le_severity (x : CubeVertex n) : (g.flippable x).card ≤ g.severity x := by
  apply Finset.card_le_card
  intro i hi
  have hh := (Finset.mem_filter.mp hi).2
  change i ∈ Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount x j) g.fineLength ≤ 11)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem key_agree_coarse (x y : CubeVertex n)
    (h : ∀ a ∈ g.coarseCoords, x a = y a) : g.key x = g.key y := by
  have hbin (x y : CubeVertex n) (h : ∀ a ∈ g.coarseCoords, x a = y a) :
      g.coarseBin x = g.coarseBin y := by
    funext i
    unfold ChunkGeometry5.coarseBin ChunkGeometry5.coarseCount
    congr 2
    apply filter_agree
    intro a ha
    exact h a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ha⟩)
  have hb := hbin x y h
  have hflip (a : Fin n) : g.coarseBin (flipVertex5 x a) = g.coarseBin (flipVertex5 y a) := by
    apply hbin
    intro b hb
    by_cases hba : b = a
    · subst b; simp [flipVertex5, h a hb]
    · simp [flipVertex5, hba, h b hb]
  have hbound : g.boundary x = g.boundary y := by
    apply propext
    unfold ChunkGeometry5.boundary
    simp_rw [hflip, hb]
  unfold ChunkGeometry5.key
  rw [hb, hbound]

theorem coarseRange_agree (x y : CubeVertex n)
    (h : ∀ a ∈ g.coarseCoords, x a = y a) : g.coarseRange x = g.coarseRange y := by
  unfold ChunkGeometry5.coarseRange
  rw [key_agree_coarse g x y h]
  congr 1
  apply Finset.image_congr
  intro a ha
  apply key_agree_coarse g
  intro b hb
  by_cases hba : b = a
  · subst b; simp [flipVertex5, h a hb]
  · simp [flipVertex5, hba, h b hb]

theorem fine_flip_agree_coarse (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∈ g.fineChunks i) : ∀ b ∈ g.coarseCoords, flipVertex5 x a b = x b := by
  intro b hb
  have hba : b ≠ a := by
    intro he
    subst b
    obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp hb
    exact Finset.disjoint_left.mp (g.chunks_disjoint.2.1 j i) haj ha
  simp [flipVertex5, hba]

/-- A neighbour below the interface has unchanged signs, flippable set and coarse data. -/
theorem high_low_neighbor (J : ℕ) (x y : CubeVertex n) (hxy : (cube n).Adj x y)
    (hx : J < g.severity x) (hy : g.severity y ≤ J) :
    g.severity x = J + 1 ∧ g.severity y = J ∧ g.sign y = g.sign x ∧
      g.flippable y = g.flippable x ∧ g.key y = g.key x ∧ g.coarseRange y = g.coarseRange x := by
  obtain ⟨a, rfl⟩ := adjacent_flip x y hxy
  have hdrop : g.severity (flipVertex5 x a) < g.severity x := lt_of_le_of_lt hy hx
  have hsome : ∃ i, a ∈ g.fineChunks i := by
    by_contra hh
    push_neg at hh
    have hcounts : ∀ i, g.fineCount (flipVertex5 x a) i = g.fineCount x i :=
      fun i => fineCount_flip_outside g x a i (hh i)
    have heq : g.severity (flipVertex5 x a) = g.severity x := by
      unfold ChunkGeometry5.severity
      simp_rw [hcounts]
    exact (ne_of_lt hdrop) heq
  obtain ⟨i, hi⟩ := hsome
  have hf := crossing_fine_features g x a i hi hdrop
  have hcoarse := fine_flip_agree_coarse g x a i hi
  refine ⟨by omega, by omega, hf.1, hf.2.1, ?_, ?_⟩
  · exact key_agree_coarse g _ _ hcoarse
  · exact coarseRange_agree g _ _ hcoarse

/-- All low even types in the neighbourhood of one high target coincide. -/
theorem high_low_type_unique (J : ℕ) (x y z : CubeVertex n)
    (hxy : (cube n).Adj x y) (hxz : (cube n).Adj x z) (hx : J < g.severity x)
    (hy : g.severity y ≤ J) (hz : g.severity z ≤ J) :
    g.evenType J y = g.evenType J z := by
  have hfy := high_low_neighbor g J x y hxy hx hy
  have hfz := high_low_neighbor g J x z hxz hx hz
  have hsign : g.sign y = g.sign z := hfy.2.2.1.trans hfz.2.2.1.symm
  have hflip : g.flippable y = g.flippable z := hfy.2.2.2.1.trans hfz.2.2.2.1.symm
  have hkey : g.key y = g.key z := hfy.2.2.2.2.1.trans hfz.2.2.2.2.1.symm
  have hcoarse : g.coarseRange y = g.coarseRange z := hfy.2.2.2.2.2.trans hfz.2.2.2.2.2.symm
  have hsev : g.severity y = g.severity z := hfy.2.1.trans hfz.2.1.symm
  unfold ChunkGeometry5.evenType ChunkGeometry5.typeKeys
  simp only [dite_eq_left hy, dite_eq_left hz, ite_eq_left hy, ite_eq_left hz]
  simp only [hsign, hflip, hkey, hcoarse, hsev]

def neighborSigns (x : CubeVertex n) : Finset (CubeVertex m) :=
  insert (g.sign x) ((g.flippable x).image fun i => Function.update (g.sign x) i (!g.sign x i))

theorem neighborSigns_card (x : CubeVertex n) : (neighborSigns g x).card ≤ g.severity x + 1 := by
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
    (Finset.card_image_le.trans (flippable_card_le_severity g x)) 1)

theorem fine_flip_sign (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∈ g.fineChunks i) : g.sign (flipVertex5 x a) ∈ neighborSigns g x := by
  by_cases hs : g.sign (flipVertex5 x a) = g.sign x
  · simp [neighborSigns, hs]
  · have hcounts := fine_counts_single_change g x a i ha
    have hsigns : ∀ j, j ≠ i → g.sign (flipVertex5 x a) j = g.sign x j := by
      intro j hj
      simp only [ChunkGeometry5.sign, hcounts j hj]
    have hneq : g.sign (flipVertex5 x a) i ≠ g.sign x i := by
      intro hh
      apply hs
      funext j
      by_cases hj : j = i
      · subst j; exact hh
      · exact hsigns j hj
    have hstep := fineCount_flip_inside g x a i ha
    have hmid : Nat.dist (2 * g.fineCount x i) g.fineLength = 1 := by
      have hneq' : ¬ ((g.fineLength < 2 * g.fineCount (flipVertex5 x a) i) ↔
          (g.fineLength < 2 * g.fineCount x i)) := by
        intro hh
        apply hneq
        simp only [ChunkGeometry5.sign, propext hh]
      obtain ⟨k, hk⟩ := g.fine_length_odd
      simp only [Nat.dist]
      omega
    have hi : i ∈ g.flippable x := by simp [ChunkGeometry5.flippable, hmid]
    have heq : g.sign (flipVertex5 x a) = Function.update (g.sign x) i (!g.sign x i) := by
      funext j
      by_cases hj : j = i
      · subst j
        rw [Function.update_self]
        cases hx : g.sign x i <;> cases hy : g.sign (flipVertex5 x a) i <;> simp_all
      · rw [Function.update_of_ne hj]
        exact hsigns j hj
    simp only [neighborSigns, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨i, hi, heq.symm⟩

theorem adjacent_sign_mem (x y : CubeVertex n) (hxy : (cube n).Adj x y) :
    g.sign y ∈ neighborSigns g x := by
  obtain ⟨a, rfl⟩ := adjacent_flip x y hxy
  by_cases hh : ∃ i, a ∈ g.fineChunks i
  · obtain ⟨i, hi⟩ := hh
    exact fine_flip_sign g x a i hi
  · push_neg at hh
    have he : g.sign (flipVertex5 x a) = g.sign x := by
      funext i
      simp only [ChunkGeometry5.sign, fineCount_flip_outside g x a i (hh i)]
    simp [neighborSigns, he]

theorem adjacent_severity (x y : CubeVertex n) (hxy : (cube n).Adj x y) :
    g.severity x ≤ g.severity y + 1 ∧ g.severity y ≤ g.severity x + 1 := by
  obtain ⟨a, rfl⟩ := adjacent_flip x y hxy
  by_cases hh : ∃ i, a ∈ g.fineChunks i
  · obtain ⟨i, hi⟩ := hh
    let S := Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount x j) g.fineLength ≤ 11)
    let T := Finset.univ.filter (fun j => Nat.dist (2 * g.fineCount (flipVertex5 x a) j) g.fineLength ≤ 11)
    have he : S.erase i = T.erase i := filter_erase_counts g x (flipVertex5 x a) i
      (fun j hj => (fine_counts_single_change g x a i hi j hj).symm)
    have hs : S.card ≤ (S.erase i).card + 1 := by
      by_cases h : i ∈ S
      · exact (Finset.card_erase_add_one h).symm.le
      · simp [Finset.erase_eq_of_notMem h]
    have ht : T.card ≤ (T.erase i).card + 1 := by
      by_cases h : i ∈ T
      · exact (Finset.card_erase_add_one h).symm.le
      · simp [Finset.erase_eq_of_notMem h]
    change S.card ≤ T.card + 1 ∧ T.card ≤ S.card + 1
    rw [he] at hs
    rw [← he] at ht
    constructor
    · exact hs.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset _ _)) 1)
    · exact ht.trans (Nat.add_le_add_right (Finset.card_le_card (Finset.erase_subset _ _)) 1)
  · push_neg at hh
    have hcounts : ∀ i, g.fineCount (flipVertex5 x a) i = g.fineCount x i :=
      fun i => fineCount_flip_outside g x a i (hh i)
    have he : g.severity (flipVertex5 x a) = g.severity x := by
      unfold ChunkGeometry5.severity
      simp_rw [hcounts]
    simp [he]

theorem adjacent_key_mem (x y : CubeVertex n) (hxy : (cube n).Adj x y) :
    g.key y ∈ g.coarseRange x := by
  obtain ⟨a, rfl⟩ := adjacent_flip x y hxy
  by_cases ha : a ∈ g.coarseCoords
  · simp only [ChunkGeometry5.coarseRange, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨a, ha, rfl⟩
  · have he : g.key (flipVertex5 x a) = g.key x := by
      apply key_agree_coarse g
      intro b hb
      have hba : b ≠ a := by intro he; subst b; exact ha hb
      simp [flipVertex5, hba]
    simp [ChunkGeometry5.coarseRange, he]

theorem low_type_card (J : ℕ) (x : CubeVertex n) (hx : g.severity x ≤ J) :
    (g.typeKeys J x).card ≤ coarseChunkCount5 * 4 + 1 + g.severity x + 2 := by
  unfold ChunkGeometry5.typeKeys
  rw [ite_eq_left hx]
  have hc := g.coarseRange_card_le x
  have hf := flippable_card_le_severity g x
  have hA := Finset.card_image_le (s := g.coarseRange x)
    (f := fun i => keyAt5 J i (g.sign x) (g.severity x))
  have hB := Finset.card_image_le (s := g.flippable x)
    (f := fun i => keyAt5 J (g.key x) (Function.update (g.sign x) i (!g.sign x i)) (g.severity x))
  have hC : (({g.severity x + 1} : Finset ℕ) ∪
      (if 0 < g.severity x then {g.severity x - 1} else ∅)).card ≤ 2 := by
    split_ifs
    · exact (Finset.card_union_le _ _).trans (by simp)
    · simp
  have hD := Finset.card_image_le
    (s := ({g.severity x + 1} : Finset ℕ) ∪ (if 0 < g.severity x then {g.severity x - 1} else ∅))
    (f := fun j => keyAt5 J (g.key x) (g.sign x) j)
  have hU := Finset.card_union_le
    ((g.coarseRange x).image (fun i => keyAt5 J i (g.sign x) (g.severity x)))
    ((g.flippable x).image (fun i => keyAt5 J (g.key x) (Function.update (g.sign x) i (!g.sign x i)) (g.severity x)))
  have hV := Finset.card_union_le
    (((g.coarseRange x).image (fun i => keyAt5 J i (g.sign x) (g.severity x))) ∪
      ((g.flippable x).image (fun i => keyAt5 J (g.key x) (Function.update (g.sign x) i (!g.sign x i)) (g.severity x))))
    ((({g.severity x + 1} : Finset ℕ) ∪ (if 0 < g.severity x then {g.severity x - 1} else ∅)).image
      (fun j => keyAt5 J (g.key x) (g.sign x) j))
  omega

section Records

variable {γ K' χ : ℝ} {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

def observedLowScope (r : X.AbsRecord) : Finset (LowCoordinates X) :=
  r.2.1.biUnion (fun c => lowTypeScope X c.2)

private theorem obs_witness (r : X.AbsRecord) (y : OddRole5 n) (μ)
    (hr : X.RecordFrom r y μ) (c) (hc : c ∈ r.2.1) :
    ∃ a ∈ Setup5.evenNbrs y, c = (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1) := by
  have hc' := Eq.mp (congrArg (fun S => c ∈ S) hr.2.1) hc
  have hm := by
    letI : DecidableEq (Fin (X.p.T n) × X.Ty) := Classical.decEq _
    exact Finset.mem_image.mp hc'
  obtain ⟨a, ha, he⟩ := hm
  exact ⟨a, ha, he.symm⟩

private theorem low_key_implies_low_type (a : EvenRole5 n) (k : LowCoordinates X)
    (hk : Sum.inl k ∈ (X.g.evenType (X.p.J n) a.1).2.1) :
    X.g.severity a.1 ≤ X.p.J n := by
  by_contra hh
  change Sum.inl k ∈ X.g.typeKeys (X.p.J n) a.1 at hk
  rw [ChunkGeometry5.typeKeys, ite_eq_right hh] at hk
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hk
  cases he

private theorem low_scope_mem (K : X.Ty) (k : LowCoordinates X) :
    k ∈ lowTypeScope X K ↔ Sum.inl k ∈ K.2.1 := by
  simp only [lowTypeScope, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The observation arrays at a high target read one low tuple list, with `O(J)` keys. -/
theorem high_observedLowScope_card (r : X.AbsRecord) (hr : X.RecOccurs r)
    (hhigh : ∃ i, r.1 = .inr i) :
    (observedLowScope X r).card ≤ coarseChunkCount5 * 4 + 1 + X.p.J n + 2 := by
  obtain ⟨y, μ, hy⟩ := hr
  have hcentral : X.p.J n < X.g.severity y.1 := by
    obtain ⟨i, hi⟩ := hhigh
    by_contra hh
    have hle : X.g.severity y.1 ≤ X.p.J n := by omega
    have ht := hy.1.trans hi
    simp only [ChunkGeometry5.roleKey, dite_eq_left hle] at ht
    cases ht
  by_cases hnone : observedLowScope X r = ∅
  · simp [hnone]
  · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hnone
    obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨a, ha, rfl⟩ := obs_witness X r y μ hy c hc
    have hak := (low_scope_mem X _ _).mp hkc
    have haLow := low_key_implies_low_type X a k hak
    have hay : (cube n).Adj y.1 a.1 :=
      (cube n).adj_symm ((Finset.mem_filter.mp ha).2)
    have hsev := (high_low_neighbor X.g (X.p.J n) y.1 a.1 hay hcentral haLow).2.1
    have hsub : observedLowScope X r ⊆ lowTypeScope X (X.g.evenType (X.p.J n) a.1) := by
      intro k' hk'
      obtain ⟨c', hc', hk'c⟩ := Finset.mem_biUnion.mp hk'
      obtain ⟨a', ha', rfl⟩ := obs_witness X r y μ hy c' hc'
      have ha'Low := low_key_implies_low_type X a' k' ((low_scope_mem X _ _).mp hk'c)
      have ha'y : (cube n).Adj y.1 a'.1 := (cube n).adj_symm ((Finset.mem_filter.mp ha').2)
      have htype := high_low_type_unique X.g (X.p.J n) y.1 a'.1 a.1 ha'y hay hcentral ha'Low haLow
      rwa [htype] at hk'c
    calc
      _ ≤ (lowTypeScope X (X.g.evenType (X.p.J n) a.1)).card := Finset.card_le_card hsub
      _ ≤ (X.g.evenType (X.p.J n) a.1).2.1.card := lowTypeScope_card X _
      _ ≤ coarseChunkCount5 * 4 + 1 + X.g.severity a.1 + 2 := low_type_card X.g (X.p.J n) a.1 haLow
      _ = _ := by rw [hsev]

def optionalLowScope (r : X.AbsRecord) : Finset (LowCoordinates X) :=
  Finset.univ.filter fun k => ∃ c ∈ r.2.2.1, c.2.2 = some (.inl k)

private theorem ref_witness (r : X.AbsRecord) (y : OddRole5 n) (μ)
    (hr : X.RecordFrom r y μ) (c) (hc : c ∈ r.2.2.1) :
    ∃ a ∈ Setup5.evenNbrs y,
      c = (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1) := by
  have hc' := Eq.mp (congrArg (fun S => c ∈ S) hr.2.2.1) hc
  have hm := by
    letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
    exact Finset.mem_image.mp hc'
  obtain ⟨a, ha, he⟩ := hm
  refine ⟨a, ?_, he.symm⟩
  letI : DecidablePred (fun a : EvenRole5 n =>
      r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
        r.1.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome) :=
    fun a => @instDecidableAnd _ _ (Finset.decidableMem _ _) (inferInstance)
  exact Finset.mem_of_mem_filter a ha

private theorem optional_key_data (a : EvenRole5 n) (k : LowCoordinates X)
    (hk : X.g.optionalKey (X.p.J n) a.1 = some (.inl k)) :
    X.g.severity a.1 = X.p.J n + 1 ∧
      (X.g.key a.1, X.g.sign a.1, (⟨X.p.J n, Nat.lt_succ_self _⟩ : Fin (X.p.J n + 1))) = k := by
  by_cases hj : X.g.severity a.1 = X.p.J n + 1
  · refine ⟨hj, ?_⟩
    simpa only [ChunkGeometry5.optionalKey, ite_eq_left hj, Option.some.injEq, Sum.inl.injEq] using hk
  · simp only [ChunkGeometry5.optionalKey, ite_eq_right hj] at hk
    cases hk

theorem optionalLowScope_card (r : X.AbsRecord) (hr : X.RecOccurs r) :
    (optionalLowScope X r).card ≤ (coarseChunkCount5 * 4 + 1) * (X.p.J n + 3) := by
  obtain ⟨y, μ, hy⟩ := hr
  by_cases hempty : optionalLowScope X r = ∅
  · simp [hempty]
  · obtain ⟨k₀, hk₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨c₀, hc₀, hkey₀⟩ := (Finset.mem_filter.mp hk₀).2
    obtain ⟨a₀, ha₀, rfl⟩ := ref_witness X r y μ hy c₀ hc₀
    have hdata₀ := optional_key_data X a₀ k₀ hkey₀
    have hay₀ : (cube n).Adj y.1 a₀.1 := (cube n).adj_symm ((Finset.mem_filter.mp ha₀).2)
    have hcentral : X.g.severity y.1 ≤ X.p.J n + 2 := by
      have hh := (adjacent_severity X.g y.1 a₀.1 hay₀).1
      omega
    let S := (X.g.coarseRange y.1).product (neighborSigns X.g y.1)
    let f : (CoarseKey5 n × CubeVertex (X.p.m n)) → LowCoordinates X :=
      fun k => (k.1, k.2, ⟨X.p.J n, Nat.lt_succ_self _⟩)
    have hsub : optionalLowScope X r ⊆ S.image f := by
      intro k hk
      obtain ⟨c, hc, hkey⟩ := (Finset.mem_filter.mp hk).2
      obtain ⟨a, ha, rfl⟩ := ref_witness X r y μ hy c hc
      have hdata := (optional_key_data X a k hkey).2
      have hay : (cube n).Adj y.1 a.1 := (cube n).adj_symm ((Finset.mem_filter.mp ha).2)
      refine Finset.mem_image.mpr ⟨(X.g.key a.1, X.g.sign a.1), ?_, hdata⟩
      exact Finset.mem_product.mpr ⟨adjacent_key_mem X.g y.1 a.1 hay, adjacent_sign_mem X.g y.1 a.1 hay⟩
    calc
      _ ≤ (S.image f).card := Finset.card_le_card hsub
      _ ≤ S.card := Finset.card_image_le
      _ = (X.g.coarseRange y.1).card * (neighborSigns X.g y.1).card := Finset.card_product _ _
      _ ≤ (coarseChunkCount5 * 4 + 1) * (X.p.J n + 3) :=
        Nat.mul_le_mul (X.g.coarseRange_card_le y.1) ((neighborSigns_card X.g y.1).trans (by omega))

/-- A high record reads the possible low tuple and its named optional keys. -/
theorem high_recordLowScope_card (r : X.AbsRecord) (hr : X.RecOccurs r)
    (hhigh : ∃ i, r.1 = .inr i) :
    (recordLowScope X r).card ≤ (coarseChunkCount5 * 4 + 2) * (X.p.J n + 4) := by
  have harrays := occurring_record_arrays X r hr
  have hsub : recordLowScope X r ⊆ observedLowScope X r ∪ optionalLowScope X r := by
    intro k hk
    have hh : Sum.inl k ∈ recordKeys X r := by
      simpa only [recordLowScope, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    simp only [recordKeys, Finset.mem_insert, Finset.mem_union] at hh
    rcases hh with ht | hobs | hopt
    · obtain ⟨i, hi⟩ := hhigh
      rw [hi] at ht
      cases ht
    · rw [harrays] at hobs
      obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp hobs
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨c, hc, by simp [lowTypeScope, hkc]⟩)
    · obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp hopt
      have hkey : c.2.2 = some (.inl k) := Option.mem_def.mp (Option.mem_toFinset.mp hkc)
      apply Finset.mem_union_right
      simp only [optionalLowScope, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨c, hc, hkey⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have ho := high_observedLowScope_card X r hr hhigh
  have hp := optionalLowScope_card X r hr
  nlinarith

end Records

end
end HypercubeRamsey.Lane_sol_s05_h5l
