import HypercubeRamsey.S05.Even_setup_sol_s05_even
import HypercubeRamsey.S05.History_sol_s05_hist1e_apply

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {n m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)

private theorem count_flip_outside (C : Finset (Fin n)) (x : CubeVertex n)
    (a : Fin n) (ha : a ∉ C) :
    (C.filter fun b => flipVertex5 x a b = true).card = (C.filter fun b => x b = true).card := by
  congr 1
  apply Finset.ext
  intro b
  constructor
  · intro h
    obtain ⟨hb, hbit⟩ := Finset.mem_filter.mp h
    have hba : b ≠ a := by intro heq; subst b; exact ha hb
    exact Finset.mem_filter.mpr ⟨hb, by
      simpa only [flipVertex5, Function.update_of_ne hba] using hbit⟩
  · intro h
    obtain ⟨hb, hbit⟩ := Finset.mem_filter.mp h
    have hba : b ≠ a := by intro heq; subst b; exact ha hb
    exact Finset.mem_filter.mpr ⟨hb, by
      simpa only [flipVertex5, Function.update_of_ne hba] using hbit⟩

private theorem count_flip_same (C : Finset (Fin n)) (x : CubeVertex n) (a b : Fin n)
    (ha : a ∈ C) (hb : b ∈ C) (hab : x a = x b) :
    (C.filter fun c => flipVertex5 x a c = true).card = (C.filter fun c => flipVertex5 x b c = true).card := by
  have hflip (a : Fin n) (ha : a ∈ C) : C.filter (fun c => flipVertex5 x a c = true) =
      if x a then (C.filter fun c => x c = true).erase a else insert a (C.filter fun c => x c = true) := by
    ext c
    by_cases hc : c = a
    · subst c
      cases hbit : x a <;> simp [flipVertex5, hbit, ha]
    · cases hbit : x a <;> simp [flipVertex5, hbit, hc]
  rw [hflip a ha, hflip b hb]
  cases hbit : x b <;> simp [hab, hbit, ha, hb]

theorem coarse_flip_state_eq (x : CubeVertex n) (i : Fin coarseChunkCount5) (a b : Fin n)
    (ha : a ∈ g.coarseChunks i) (hb : b ∈ g.coarseChunks i) (hab : x a = x b) :
    St.stateOf (flipVertex5 x a) = St.stateOf (flipVertex5 x b) := by
  have hcoarse (j : Fin coarseChunkCount5) :
      g.coarseCount (flipVertex5 x a) j = g.coarseCount (flipVertex5 x b) j := by
    unfold ChunkGeometry5.coarseCount
    by_cases hj : j = i
    · subst j
      exact count_flip_same _ _ _ _ ha hb hab
    · have hna : a ∉ g.coarseChunks j := fun h =>
        Finset.disjoint_left.mp (g.chunks_disjoint.1 j i hj) h ha
      have hnb : b ∉ g.coarseChunks j := fun h =>
        Finset.disjoint_left.mp (g.chunks_disjoint.1 j i hj) h hb
      rw [count_flip_outside _ _ _ hna, count_flip_outside _ _ _ hnb]
  have hfine (j : Fin m) : g.fineCount (flipVertex5 x a) j = g.fineCount x j ∧
      g.fineCount (flipVertex5 x b) j = g.fineCount x j := by
    have hna : a ∉ g.fineChunks j := fun h => Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j) ha h
    have hnb : b ∉ g.fineChunks j := fun h => Finset.disjoint_left.mp (g.chunks_disjoint.2.1 i j) hb h
    exact ⟨Lane_sol_s05_h5l.fineCount_flip_outside g x a j hna,
      Lane_sol_s05_h5l.fineCount_flip_outside g x b j hnb⟩
  apply St.data_determine_state
  · intro c hc
    have hca : c ≠ a := by
      intro h
      subst c
      exact Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i) ha hc
    have hcb : c ≠ b := by
      intro h
      subst c
      exact Finset.disjoint_left.mp (g.chunks_disjoint.2.2.2.1 i) hb hc
    simp [flipVertex5, hca, hcb]
  · exact hcoarse
  · intro j
    rw [(hfine j).1, (hfine j).2]
  · unfold ChunkGeometry5.severity
    simp_rw [(hfine _).1, (hfine _).2]

set_option maxRecDepth 4096 in
theorem coarse_flip_states_card (x : CubeVertex n) :
    ((g.coarseCoords).image fun a => St.stateOf (flipVertex5 x a)).card ≤ 2 * coarseChunkCount5 := by
  letI : DecidableEq St.Site := St.siteDecEq
  letI : Fintype St.Site := St.siteFintype
  let rep (i : Fin coarseChunkCount5) (bit : Bool) :=
    if h : ∃ a ∈ g.coarseChunks i, x a = bit then
      St.stateOf (flipVertex5 x (Classical.choose h)) else St.stateOf x
  let codes := (Finset.univ : Finset (Fin coarseChunkCount5)).product (Finset.univ : Finset Bool)
  have hsub : (g.coarseCoords.image fun a => St.stateOf (flipVertex5 x a)) ⊆
      codes.image (fun c => rep c.1 c.2) := by
    intro s hs
    have hs' : ∃ a : Fin n, a ∈ g.coarseCoords ∧ St.stateOf (flipVertex5 x a) = s :=
      Finset.mem_image.mp hs
    obtain ⟨a, ha, heq⟩ := hs'
    subst s
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    have hex : ∃ b ∈ g.coarseChunks i, x b = x a := ⟨a, hai, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(i, x a), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    dsimp [rep]
    rw [dif_pos hex]
    have hh := Classical.choose_spec hex
    exact coarse_flip_state_eq g St x i _ a hh.1 hai hh.2
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp [codes, Nat.mul_comm]))

theorem severity_drop_distances (x : CubeVertex n) (a : Fin n) (i : Fin m)
    (ha : a ∈ g.fineChunks i) (hdrop : g.severity (flipVertex5 x a) < g.severity x) :
    Nat.dist (2 * g.fineCount x i) g.fineLength = 11 ∧
      Nat.dist (2 * g.fineCount (flipVertex5 x a) i) g.fineLength = 13 := by
  let y := flipVertex5 x a
  let A := Finset.univ.filter fun j : Fin m => Nat.dist (2 * g.fineCount x j) g.fineLength ≤ 11
  let B := Finset.univ.filter fun j : Fin m => Nat.dist (2 * g.fineCount y j) g.fineLength ≤ 11
  have hother (j : Fin m) (hj : j ≠ i) : g.fineCount y j = g.fineCount x j :=
    Lane_sol_s05_h5l.fine_counts_single_change g x a i ha j hj
  have hbefore : Nat.dist (2 * g.fineCount x i) g.fineLength ≤ 11 := by
    by_contra hnot
    have hsub : A ⊆ B := by
      intro j hj
      by_cases hji : j = i
      · subst j
        exact (hnot (Finset.mem_filter.mp hj).2).elim
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hother j hji]; exact (Finset.mem_filter.mp hj).2⟩
    exact (not_le_of_gt hdrop) (Finset.card_le_card hsub)
  have hafter : 11 < Nat.dist (2 * g.fineCount y i) g.fineLength := by
    by_contra hnot
    have hsub : A ⊆ B := by
      intro j hj
      by_cases hji : j = i
      · subst j
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hother j hji]; exact (Finset.mem_filter.mp hj).2⟩
    exact (not_le_of_gt hdrop) (Finset.card_le_card hsub)
  have hstep := Lane_sol_s05_h5l.fineCount_flip_inside g x a i ha
  obtain ⟨L, hL⟩ := g.fine_length_odd
  dsimp [y] at hafter
  simp only [Nat.dist] at hbefore hafter ⊢
  omega

theorem high_low_state_unique (x y z : CubeVertex n) (hxy : (cube n).Adj x y)
    (hxz : (cube n).Adj x z) (hx : J < g.severity x) (hy : g.severity y ≤ J) (hz : g.severity z ≤ J) :
    St.stateOf y = St.stateOf z := by
  obtain ⟨a, rfl⟩ := Lane_sol_s05_h5l.adjacent_flip x y hxy
  obtain ⟨b, rfl⟩ := Lane_sol_s05_h5l.adjacent_flip x z hxz
  have hdropa : g.severity (flipVertex5 x a) < g.severity x := lt_of_le_of_lt hy hx
  have hdropb : g.severity (flipVertex5 x b) < g.severity x := lt_of_le_of_lt hz hx
  have hsome (a : Fin n) (hdrop : g.severity (flipVertex5 x a) < g.severity x) : ∃ i, a ∈ g.fineChunks i := by
    by_contra hno
    have hcounts (i : Fin m) : g.fineCount (flipVertex5 x a) i = g.fineCount x i :=
      Lane_sol_s05_h5l.fineCount_flip_outside g x a i (fun hi => hno ⟨i, hi⟩)
    have heq : g.severity (flipVertex5 x a) = g.severity x := by
      unfold ChunkGeometry5.severity
      simp_rw [hcounts]
    exact (ne_of_lt hdrop) heq
  obtain ⟨i, hi⟩ := hsome a hdropa
  obtain ⟨j, hj⟩ := hsome b hdropb
  obtain ⟨ha0, ha1⟩ := severity_drop_distances g x a i hi hdropa
  obtain ⟨hb0, hb1⟩ := severity_drop_distances g x b j hj hdropb
  have hseva := (Lane_sol_s05_h5l.high_low_neighbor g J x (flipVertex5 x a) hxy hx hy).2.1
  have hsevb := (Lane_sol_s05_h5l.high_low_neighbor g J x (flipVertex5 x b) hxz hx hz).2.1
  exact Lane_sol_s05_hist1b.fine_outward_states_eq g St x i j a b hi hj ha0 ha1 hb0 hb1 (hseva.trans hsevb.symm)

theorem high_type_agree_coarse (x y : CubeVertex n) (hx : J < g.severity x) (hy : J < g.severity y)
    (hcoarse : ∀ a ∈ g.coarseCoords, x a = y a) : g.evenType J x = g.evenType J y := by
  have hk := Lane_sol_s05_h5l.key_agree_coarse g x y hcoarse
  have hC := Lane_sol_s05_h5l.coarseRange_agree g x y hcoarse
  simp only [ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, not_le.mpr hx, not_le.mpr hy,
    dite_false, ite_false, hk, hC]

def lowNeighborStates (b : OddRole5 n) : Finset St.Site :=
  ((Setup5.evenNbrs b).filter fun a => g.low J a.1).image fun a => St.stateOf a.1

theorem lowNeighborStates_card (b : OddRole5 n) (hb : ¬ g.low J b.1) :
    (lowNeighborStates g St b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨ha, hlow⟩ := Finset.mem_filter.mp ha
  obtain ⟨ha', hlow'⟩ := Finset.mem_filter.mp ha'
  have hadj := (Finset.mem_filter.mp ha).2
  have hadj' := (Finset.mem_filter.mp ha').2
  exact high_low_state_unique g St b.1 a.1 a'.1 hadj.symm hadj'.symm (by simpa [ChunkGeometry5.low] using hb)
    hlow hlow'

def highExceptionalStates (b : OddRole5 n) : Finset St.Site :=
  (g.coarseCoords.image fun a => St.stateOf (flipVertex5 b.1 a)) ∪ lowNeighborStates g St b

theorem highExceptionalStates_card (b : OddRole5 n) (hb : ¬ g.low J b.1) :
    (highExceptionalStates g St b).card ≤ 601 := by
  have hc := coarse_flip_states_card g St b.1
  have hl := lowNeighborStates_card g St b hb
  have hu := Finset.card_union_le (g.coarseCoords.image fun a => St.stateOf (flipVertex5 b.1 a))
    (lowNeighborStates g St b)
  unfold highExceptionalStates
  norm_num [coarseChunkCount5] at hc
  omega

theorem high_type_generic (b : OddRole5 n) (hb : ¬ g.low J b.1) (a : EvenRole5 n)
    (ha : a ∈ Setup5.evenNbrs b) (hstate : St.stateOf a.1 ∉ highExceptionalStates g St b) :
    g.evenType J a.1 = g.evenType J b.1 := by
  have hhigh : ¬ g.low J a.1 := by
    intro hlow
    apply hstate
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hlow⟩, rfl⟩
  obtain ⟨i, hi⟩ := Lane_sol_s05_hist1b.cube_adj_eq_flip (Finset.mem_filter.mp ha).2
  have hnot : i ∉ g.coarseCoords := by
    intro hcoarse
    apply hstate
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, hcoarse, congrArg St.stateOf hi.symm⟩
  have hcoarse : ∀ j ∈ g.coarseCoords, a.1 j = b.1 j := by
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hnot hj
    rw [hi]
    simp [flipVertex5, Function.update_of_ne hji]
  apply high_type_agree_coarse g a.1 b.1
    (by simpa [ChunkGeometry5.low] using hhigh) (by simpa [ChunkGeometry5.low] using hb) hcoarse

theorem high_observation_images_card {Id : Type*} [Fintype Id] [DecidableEq Id] [Nonempty Id]
    (b : OddRole5 n) (hb : ¬ g.low J b.1) :
    ((Finset.univ : Finset (St.Site → Id)).image fun μ =>
      (Setup5.evenNbrs b).image fun a => (μ (St.stateOf a.1), g.evenType J a.1)).card ≤
        2 ^ Fintype.card Id * Fintype.card Id ^ 601 := by
  have hh := Lane_sol_s05_hist1b.observation_images_card_le
    (A := EvenRole5 n) (B := St.Site) (C := EvenType5 n m J) (Id := Id) (Setup5.evenNbrs b)
    (fun a : EvenRole5 n => St.stateOf a.1) (fun a : EvenRole5 n => g.evenType J a.1) {g.evenType J b.1}
    (highExceptionalStates g St b) (fun a ha hs => by simp [high_type_generic g St b hb a ha hs])
  simp only [Finset.card_singleton, mul_one] at hh
  refine hh.trans (Nat.mul_le_mul_left _ ?_)
  exact Nat.pow_le_pow_right (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card Id))
    (highExceptionalStates_card g St b hb)

end
end HypercubeRamsey.Lane_sol_s05_even
