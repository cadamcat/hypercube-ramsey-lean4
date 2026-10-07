import HypercubeRamsey.S05.Experiment

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical OAI.HypercubeRamsey
noncomputable section

private theorem ones_flip {n : ℕ} (S : Finset (Fin n)) (x : CubeVertex n) (a : Fin n)
    (ha : a ∈ S) :
    S.filter (fun c => flipVertex5 x a c = true) =
      if x a then (S.filter (fun c => x c = true)).erase a
      else insert a (S.filter (fun c => x c = true)) := by
  ext c
  by_cases hca : c = a
  · subst c
    cases hbit : x a <;> simp [flipVertex5, hbit, ha]
  · cases hbit : x a <;> simp [flipVertex5, hbit, hca]

private theorem ones_flip_same {n : ℕ} (S : Finset (Fin n)) (x : CubeVertex n)
    (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hab : x a = x b) :
    (S.filter (fun c => flipVertex5 x a c = true)).card =
      (S.filter (fun c => flipVertex5 x b c = true)).card := by
  rw [ones_flip S x a ha, ones_flip S x b hb]
  cases hbit : x b <;> simp [hab, hbit, ha, hb]

private theorem ones_flip_outside {n : ℕ} (S : Finset (Fin n)) (x : CubeVertex n)
    (a : Fin n) (ha : a ∉ S) :
    S.filter (fun c => flipVertex5 x a c = true) = S.filter (fun c => x c = true) := by
  ext c
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

/-- Flips in one fine chunk with the same original bit have the same quotient state. -/
theorem fine_flip_state_eq {n m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x : CubeVertex n) (i : Fin m) (a b : Fin n)
    (ha : a ∈ g.fineChunks i) (hb : b ∈ g.fineChunks i) (hab : x a = x b) :
    St.stateOf (flipVertex5 x a) = St.stateOf (flipVertex5 x b) := by
  have hout (S : Finset (Fin n)) (hd : Disjoint S (g.fineChunks i)) : a ∉ S ∧ b ∉ S :=
    ⟨fun h => Finset.disjoint_left.mp hd h ha, fun h => Finset.disjoint_left.mp hd h hb⟩
  have hfine (j : Fin m) : g.fineCount (flipVertex5 x a) j = g.fineCount (flipVertex5 x b) j := by
    unfold ChunkGeometry5.fineCount
    by_cases hji : j = i
    · subst j
      exact ones_flip_same (g.fineChunks i) x a b ha hb hab
    · have hd := hout (g.fineChunks j) (g.chunks_disjoint.2.2.1 j i hji)
      rw [ones_flip_outside _ _ _ hd.1, ones_flip_outside _ _ _ hd.2]
  apply St.data_determine_state
  · intro c hc
    have hd := hout g.residual (g.chunks_disjoint.2.2.2.2 i).symm
    have hca : c ≠ a := fun heq => hd.1 (heq ▸ hc)
    have hcb : c ≠ b := fun heq => hd.2 (heq ▸ hc)
    simp [flipVertex5, hca, hcb]
  · intro j
    have hd := hout (g.coarseChunks j) (g.chunks_disjoint.2.1 j i)
    unfold ChunkGeometry5.coarseCount
    rw [ones_flip_outside _ _ _ hd.1, ones_flip_outside _ _ _ hd.2]
  · intro j
    rw [hfine j]
  · unfold ChunkGeometry5.severity
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfine j]

/-- Fine chunks capable of changing the sign or flippable set in one step. -/
def criticalChunks {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n) : Finset (Fin m) :=
  Finset.univ.filter fun i => Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 3

theorem criticalChunks_card_le {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n) :
    (criticalChunks g x).card ≤ g.severity x := by
  apply Finset.card_le_card
  intro i hi
  have hd := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

/-- The exceptional neighboring states number at most twice the central severity. -/
theorem critical_flip_states_card_le {n m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x : CubeVertex n) :
    (((criticalChunks g x).biUnion g.fineChunks).image
      (fun a => St.stateOf (flipVertex5 x a))).card ≤ 2 * g.severity x := by
  let rep (i : Fin m) (bit : Bool) : St.Site :=
    if h : ∃ a ∈ g.fineChunks i, x a = bit then
      St.stateOf (flipVertex5 x (Classical.choose h)) else St.stateOf x
  let codes := (criticalChunks g x).product (Finset.univ : Finset Bool)
  have hsub : (((criticalChunks g x).biUnion g.fineChunks).image
      (fun a => St.stateOf (flipVertex5 x a))) ⊆ codes.image (fun c => rep c.1 c.2) := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    have hex : ∃ b ∈ g.fineChunks i, x b = x a := ⟨a, hai, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(i, x a), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, ?_⟩
    dsimp [rep]
    rw [dif_pos hex]
    have hs := Classical.choose_spec hex
    exact fine_flip_state_eq g St x i _ a hs.1 hai hs.2
  calc
    _ ≤ (codes.image (fun c => rep c.1 c.2)).card := Finset.card_le_card hsub
    _ ≤ codes.card := Finset.card_image_le
    _ = 2 * (criticalChunks g x).card := by simp [codes, Nat.mul_comm]
    _ ≤ 2 * g.severity x := Nat.mul_le_mul_left 2 (criticalChunks_card_le g x)

end
end HypercubeRamsey.Lane_sol_s05_hist1b
