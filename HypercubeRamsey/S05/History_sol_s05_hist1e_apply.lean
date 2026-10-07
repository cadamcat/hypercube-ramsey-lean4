import HypercubeRamsey.S05.History_sol_s05_hist1e

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical OAI.HypercubeRamsey
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

private theorem fine_count_flip {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n)
    (i : Fin m) (a : Fin n) (ha : a ∈ g.fineChunks i) :
    g.fineCount (flipVertex5 x a) i = if x a then g.fineCount x i - 1 else g.fineCount x i + 1 := by
  have hs : (g.fineChunks i).filter (fun c => flipVertex5 x a c = true) =
      if x a then ((g.fineChunks i).filter (fun c => x c = true)).erase a
      else insert a ((g.fineChunks i).filter (fun c => x c = true)) := by
    ext c
    by_cases hc : c = a
    · subst c
      cases hbit : x a <;> simp [flipVertex5, hbit, ha]
    · cases hbit : x a <;> simp [flipVertex5, hbit, hc]
  unfold ChunkGeometry5.fineCount
  rw [hs]
  cases hbit : x a <;> simp [hbit, ha]

private theorem count_flip_outside {n : ℕ} (S : Finset (Fin n)) (x : CubeVertex n)
    (a : Fin n) (ha : a ∉ S) :
    (S.filter (fun c => flipVertex5 x a c = true)).card = (S.filter (fun c => x c = true)).card := by
  congr 1
  apply Finset.ext
  intro c
  constructor
  · intro h
    obtain ⟨hc, hbit⟩ := Finset.mem_filter.mp h
    have hca : c ≠ a := fun heq => ha (heq ▸ hc)
    exact Finset.mem_filter.mpr ⟨hc, by
      simpa only [flipVertex5, Function.update_of_ne hca] using hbit⟩
  · intro h
    obtain ⟨hc, hbit⟩ := Finset.mem_filter.mp h
    have hca : c ≠ a := fun heq => ha (heq ▸ hc)
    exact Finset.mem_filter.mpr ⟨hc, by
      simpa only [flipVertex5, Function.update_of_ne hca] using hbit⟩

/-- An outward flip from distance 5.5 to 6.5 does not change any merged fine count. -/
theorem fine_flip_outward_merged {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n)
    (i : Fin m) (a : Fin n) (ha : a ∈ g.fineChunks i)
    (hbefore : Nat.dist (2 * g.fineCount x i) g.fineLength = 11)
    (hafter : Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength = 13) :
    ∀ j, mergedFineCount5 g.fineLength (g.fineCount (flipVertex5 x a) j) =
      mergedFineCount5 g.fineLength (g.fineCount x j) := by
  intro j
  by_cases hj : j = i
  · subst j
    have hc := fine_count_flip g x i a ha
    have hn : Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength ≠ 11 := by omega
    simp only [mergedFineCount5, hn, hbefore, ite_false, ite_true]
    simp only [Nat.dist] at hbefore hafter
    cases hbit : x a
    · simp only [hbit, Bool.false_eq_true, ite_false] at hc
      split_ifs <;> omega
    · simp only [hbit, ite_true] at hc
      split_ifs <;> omega
  · have hout : a ∉ g.fineChunks j := fun h =>
      Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 j i hj) h ha
    have hc : g.fineCount (flipVertex5 x a) j = g.fineCount x j :=
      count_flip_outside (g.fineChunks j) x a hout
    rw [hc]

/-- All outward boundary flips of a fixed severity have one quotient state,
even when they occur in different fine chunks. -/
theorem fine_outward_states_eq {n m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x : CubeVertex n) (i j : Fin m) (a b : Fin n)
    (ha : a ∈ g.fineChunks i) (hb : b ∈ g.fineChunks j)
    (ha0 : Nat.dist (2 * g.fineCount x i) g.fineLength = 11)
    (ha1 : Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength = 13)
    (hb0 : Nat.dist (2 * g.fineCount x j) g.fineLength = 11)
    (hb1 : Nat.dist (2 * g.fineCount (flipVertex5 x b) j) g.fineLength = 13)
    (hsev : g.severity (flipVertex5 x a) = g.severity (flipVertex5 x b)) :
    St.stateOf (flipVertex5 x a) = St.stateOf (flipVertex5 x b) := by
  apply St.data_determine_state
  · intro c hc
    have hca : c ≠ a := fun h => Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 i) ha (h ▸ hc)
    have hcb : c ≠ b := fun h => Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.2 j) hb (h ▸ hc)
    simp [flipVertex5, hca, hcb]
  · intro k
    have hna : a ∉ g.coarseChunks k := fun h =>
      Finset.disjoint_left.mp (g.chunks_disjoint.2.1 k i) h ha
    have hnb : b ∉ g.coarseChunks k := fun h =>
      Finset.disjoint_left.mp (g.chunks_disjoint.2.1 k j) h hb
    unfold ChunkGeometry5.coarseCount
    rw [count_flip_outside _ _ _ hna, count_flip_outside _ _ _ hnb]
  · intro k
    rw [fine_flip_outward_merged g x i a ha ha0 ha1,
      fine_flip_outward_merged g x j b hb hb0 hb1]
  · exact hsev

/-- The states reached by outward flips at a fixed resulting severity form a singleton. -/
theorem outward_states_card_le_one {n m J : ℕ} (g : ChunkGeometry5 n m)
    (St : CubeStates5 g J) (x : CubeVertex n) (j : ℕ) :
    ((Finset.univ.filter fun a : Fin n => g.severity (flipVertex5 x a) = j ∧
      ∃ i, a ∈ g.fineChunks i ∧ Nat.dist (2 * g.fineCount x i) g.fineLength = 11 ∧
        Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength = 13).image
      (fun a => St.stateOf (flipVertex5 x a))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hsa, i, hai, hai0, hai1⟩ := (Finset.mem_filter.mp ha).2
  obtain ⟨hsb, k, hbk, hbk0, hbk1⟩ := (Finset.mem_filter.mp hb).2
  exact fine_outward_states_eq g St x i k a b hai hbk hai0 hai1 hbk0 hbk1 (hsa.trans hsb.symm)

/-- One coordinate flip changes severity by at most one. -/
theorem severity_flip_bounds {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n) (a : Fin n) :
    g.severity (flipVertex5 x a) ≤ g.severity x + 1 ∧
      g.severity x ≤ g.severity (flipVertex5 x a) + 1 := by
  let S := Finset.univ.filter fun i : Fin m => Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11
  let T := Finset.univ.filter fun i : Fin m => Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength ≤ 11
  by_cases hex : ∃ i, a ∈ g.fineChunks i
  · obtain ⟨i, hi⟩ := hex
    have hother (j : Fin m) (hj : j ≠ i) : g.fineCount (flipVertex5 x a) j = g.fineCount x j := by
      exact count_flip_outside _ _ _ (fun h => Finset.disjoint_left.mp (g.chunks_disjoint.2.2.1 j i hj) h hi)
    have hTS : T ⊆ insert i S := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · apply Finset.mem_insert_of_mem
        have hh := (Finset.mem_filter.mp hj).2
        rw [hother j hji] at hh
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
    have hST : S ⊆ insert i T := by
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by rw [hother j hji]; exact (Finset.mem_filter.mp hj).2⟩
    exact ⟨(Finset.card_le_card hTS).trans (Finset.card_insert_le _ _),
      (Finset.card_le_card hST).trans (Finset.card_insert_le _ _)⟩
  · have hother (i : Fin m) : g.fineCount (flipVertex5 x a) i = g.fineCount x i :=
      count_flip_outside _ _ _ (fun h => hex ⟨i, h⟩)
    have heq : g.severity (flipVertex5 x a) = g.severity x := by
      unfold ChunkGeometry5.severity
      simp_rw [hother]
    omega

/-- Cube adjacency is a single Boolean coordinate flip. -/
theorem cube_adj_eq_flip {n : ℕ} {x y : CubeVertex n} (h : (cube n).Adj x y) :
    ∃ a : Fin n, x = flipVertex5 y a := by
  classical
  have hc : (Finset.univ.filter fun a : Fin n => x a ≠ y a).card = 1 := h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a, ?_⟩
  funext b
  by_cases hb : b = a
  · subst b
    have hne : x a ≠ y a := by
      have hh : a ∈ Finset.univ.filter fun a => x a ≠ y a := by rw [ha]; simp
      exact (Finset.mem_filter.mp hh).2
    cases hx : x a <;> cases hy : y a <;> simp_all [flipVertex5]
  · have heq : x b = y b := by
      by_contra hn
      have hh : b ∈ Finset.univ.filter fun a => x a ≠ y a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
      rw [ha] at hh
      exact hb (Finset.mem_singleton.mp hh)
    simp [flipVertex5, hb, heq]

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- An odd role has at most `n` even neighbors. -/
theorem evenNbrs_card_le (y : OddRole5 n) : (Setup5.evenNbrs y).card ≤ n := by
  classical
  let S := Setup5.evenNbrs y
  have hs : S.image Subtype.val ⊆ Finset.univ.image (fun a : Fin n => flipVertex5 y.1 a) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    have hadj := (Finset.mem_filter.mp hb).2
    obtain ⟨a, ha⟩ := cube_adj_eq_flip hadj
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha.symm⟩
  calc
    _ = (S.image Subtype.val).card := (Finset.card_image_of_injective S Subtype.val_injective).symm
    _ ≤ (Finset.univ.image (fun a : Fin n => flipVertex5 y.1 a)).card := Finset.card_le_card hs
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- A canonical record is reconstructed from its joint type/optional-key image
and its separately stored interface mask. -/
theorem record_fixed_center_card_le {Id : Type} [Fintype Id] [DecidableEq Id]
    (y : OddRole5 n) (generic : Finset (X.Ty × Option X.Key)) (exceptional : Finset X.St.Site)
    (masks : Finset (Option (Id × X.Ty × Finset (Fin X.blockBound))))
    (hg : ∀ a ∈ Setup5.evenNbrs y, X.St.stateOf a.1 ∉ exceptional →
      (X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1) ∈ generic)
    (hm : ∀ r : X.RecordOn Id, ∀ μ, X.RecordFrom r y μ → r.2.2.2 ∈ masks) :
    (Finset.univ.filter (fun r : X.RecordOn Id => ∃ μ, X.RecordFrom r y μ)).card ≤
      2 ^ (Fintype.card Id * generic.card) * Fintype.card Id ^ exceptional.card * masks.card := by
  classical
  let sig (a : EvenRole5 n) := (X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)
  let joint (μ : X.St.Site → Id) := (Setup5.evenNbrs y).image (fun a => (μ (X.St.stateOf a.1), sig a))
  let images := Finset.univ.image joint
  let target := X.g.roleKey (X.p.J n) y.1
  let pred (c : Id × X.Ty × Option X.Key) := target ∈ c.2.1.2.1 ∧ target.isLeft = c.2.1.2.2.isSome
  let emit (c : Finset (Id × X.Ty × Option X.Key) × Option (Id × X.Ty × Finset (Fin X.blockBound))) : X.RecordOn Id :=
    (target, c.1.image (fun d => (d.1, d.2.1)), c.1.filter pred, c.2)
  have hsub : Finset.univ.filter (fun r : X.RecordOn Id => ∃ μ, X.RecordFrom r y μ) ⊆
      (images.product masks).image emit := by
    intro r hr
    obtain ⟨μ, hrecord⟩ := (Finset.mem_filter.mp hr).2
    have hmask := hm r μ hrecord
    obtain ⟨hkey, hobs, href, _⟩ := hrecord
    apply Finset.mem_image.mpr
    refine ⟨(joint μ, r.2.2.2), Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨μ, Finset.mem_univ _, rfl⟩, hmask⟩, ?_⟩
    have ho : (joint μ).image (fun d => (d.1, d.2.1)) = r.2.1 := by
      rw [hobs]
      simp only [joint, sig, Finset.image_image]
      rfl
    have hd : (joint μ).filter pred = r.2.2.1 := by
      rw [href]
      ext c
      simp only [joint, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, hca⟩, hc⟩
        refine ⟨a, ⟨ha, ?_⟩, hca⟩
        have hh : pred (μ (X.St.stateOf a.1), sig a) := hca ▸ hc
        simpa only [pred, target, sig, hkey] using hh
      · rintro ⟨a, ⟨ha, hp⟩, hca⟩
        refine ⟨⟨a, ha, hca⟩, ?_⟩
        have hh : pred (μ (X.St.stateOf a.1), sig a) := by
          simpa only [pred, target, sig, hkey] using hp
        exact hca ▸ hh
    apply Prod.ext hkey
    apply Prod.ext ho
    exact Prod.ext hd rfl
  have hcount : images.card ≤ 2 ^ (Fintype.card Id * generic.card) * Fintype.card Id ^ exceptional.card :=
    observation_images_card_le (Setup5.evenNbrs y) (fun a => X.St.stateOf a.1) sig generic exceptional hg
  calc
    _ ≤ ((images.product masks).image emit).card := Finset.card_le_card hsub
    _ ≤ (images.product masks).card := Finset.card_image_le
    _ = images.card * masks.card := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul_right _ hcount

end
end HypercubeRamsey.Lane_sol_s05_hist1b
