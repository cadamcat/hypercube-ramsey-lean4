import HypercubeRamsey.S16.Geometry_q_s16_geom
import Mathlib.LinearAlgebra.Pi
import Mathlib.GroupTheory.Index
import Mathlib.Logic.Equiv.Fintype
import HypercubeRamsey.Tools.CubeGeometry

/-! Binary coordinate subspaces and syndrome allocation helpers for L16.1a. -/
namespace HypercubeRamsey.Lane_sol_s16_syn

open Classical
open scoped BigOperators

abbrev Bits (h : ℕ) := Fin h → ZMod 2

def coordinateSubspace {h : ℕ} (I : Finset (Fin h)) : Submodule (ZMod 2) (Bits h) where
  carrier := {v | ∀ j, j ∉ I → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
  smul_mem' := by intro c x hx j hj; simp [hx j hj]

@[simp] theorem mem_coordinateSubspace {h : ℕ} (I : Finset (Fin h)) (v : Bits h) :
    v ∈ coordinateSubspace I ↔ ∀ j, j ∉ I → v j = 0 := Iff.rfl

noncomputable def coordinateEquiv {h : ℕ} (I : Finset (Fin h)) :
    (I → ZMod 2) ≃ coordinateSubspace I where
  toFun f := ⟨fun j => if hj : j ∈ I then f ⟨j, hj⟩ else 0, by
    intro j hj; simp [hj]⟩
  invFun v j := v.1 j
  left_inv f := by funext j; simp
  right_inv v := by
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ I
    · simp [hj]
    · simp [hj, v.2 j hj]

theorem coordinate_card {h : ℕ} (I : Finset (Fin h)) :
    Fintype.card (coordinateSubspace I) = 2 ^ I.card := by
  rw [← Fintype.card_congr (coordinateEquiv I)]
  simp [Fintype.card_fun]

def binarySyndrome {n h : ℕ} (ids : Fin n → Bits h) (z : CubePos n) : Bits h :=
  ∑ j, if z j = true then ids j else 0

theorem twice_eq_zero {h : ℕ} (a : Bits h) : a + a = 0 := by
  ext j
  change a j + a j = 0
  have hh : (2 : ZMod 2) = 0 := by decide
  simpa [two_mul] using congrArg (fun c : ZMod 2 => c * a j) hh

theorem binarySyndrome_flip {n h : ℕ} (ids : Fin n → Bits h) (z : CubePos n) (i : Fin n) :
    binarySyndrome ids (flipPos z i) = ids i + binarySyndrome ids z := by
  classical
  unfold binarySyndrome
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have he : (∑ j ∈ Finset.univ.erase i,
      if flipPos z i j = true then ids j else 0) =
      ∑ j ∈ Finset.univ.erase i, if z j = true then ids j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [flipPos, (Finset.mem_erase.mp hj).1]
  rw [he]
  cases hz : z i
  · simp [flipPos, hz, add_comm]
  · have ht : ids i + ((∑ j ∈ Finset.univ.erase i,
          if z j = true then ids j else 0) + ids i) =
        ∑ j ∈ Finset.univ.erase i, if z j = true then ids j else 0 := by
      calc
        _ = (∑ j ∈ Finset.univ.erase i, if z j = true then ids j else 0) +
            (ids i + ids i) := by abel
        _ = _ := by rw [twice_eq_zero, add_zero]
    simpa [flipPos, hz] using ht.symm


/-- An injective partial ID assignment in a compulsory set can be extended
while retaining every compulsory ID. -/
theorem allocate_ids {α : Type} [Fintype α] {n : ℕ}
    (A : Finset (Fin n)) (H : Finset α) (f : A ↪ α)
    (hf : ∀ a, f a ∈ H) (hH : H.card ≤ n) (hn : n ≤ Fintype.card α) :
    ∃ ids : Fin n ↪ α,
      (∀ a ∈ H, ∃ i, ids i = a) ∧ (∀ i : A, ids i = f i) := by
  classical
  obtain ⟨Z, hHZ, _, hZ⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ H) hH (by simpa using hn)
  have hZcard : Fintype.card Z = Fintype.card (Fin n) := by simp [hZ]
  let e : Fin n ≃ Z := (Fintype.card_eq.mp hZcard.symm).some
  let g : A → Z := fun i => ⟨f i, hHZ (hf i)⟩
  have hg : Function.Injective g := by
    intro a b hab
    exact f.injective (congrArg Subtype.val hab)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : A => e i.1) g
    (fun a b hab => Subtype.ext (e.injective hab)) hg
  let ids : Fin n ↪ α :=
    ((e.trans σ).toEmbedding).trans (Function.Embedding.subtype (· ∈ Z))
  refine ⟨ids, ?_, ?_⟩
  · intro a ha
    refine ⟨(e.trans σ).symm ⟨a, hHZ ha⟩, ?_⟩
    exact congrArg Subtype.val ((e.trans σ).apply_symm_apply _)
  · intro i
    exact congrArg Subtype.val (hσ i)

theorem coordinate_disjoint_difference {h : ℕ} (I : Finset (Fin h))
    (a b : coordinateSubspace (Finset.univ \ I))
    (hab : (a.1 - b.1) ∈ coordinateSubspace I) : a = b := by
  apply Subtype.ext
  funext j
  by_cases hj : j ∈ I
  · have ha := a.2 j (by simp [hj])
    have hb := b.2 j (by simp [hj])
    rw [ha, hb]
  · exact sub_eq_zero.mp (hab j hj)

/-- One half of the ambient binary group is the coordinate-zero hyperplane. -/
theorem hyperplane_card {h : ℕ} (j : Fin h) :
    Fintype.card (coordinateSubspace (Finset.univ.erase j)) = 2 ^ (h - 1) := by
  rw [coordinate_card]
  simp


noncomputable def binaryClass {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L) (z : CubePos n) : Option (Fin r) :=
  if hz : ¬ IsEvenRole z ∧ binarySyndrome ids z ∈ L then
    some (E.symm ⟨binarySyndrome ids z, hz.2⟩) else none

theorem binaryClass_eq_some {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L) (z : CubePos n) (t : Fin r) :
    binaryClass ids L E z = some t ↔
      ¬ IsEvenRole z ∧ binarySyndrome ids z = (E t).1 := by
  classical
  unfold binaryClass
  split_ifs with hz
  · simp only [Option.some.injEq]
    constructor
    · intro he
      refine ⟨hz.1, ?_⟩
      have hh := congrArg (fun x => (E x).1) he
      simpa using hh
    · rintro ⟨_, he⟩
      apply E.injective
      apply Subtype.ext
      simpa using he
  · simp only [Option.noConfusion, false_iff]
    rintro ⟨he, hs⟩
    exact hz ⟨he, hs ▸ (E t).2⟩

theorem flip_not_even {n : ℕ} (z : CubePos n) (i : Fin n) (hz : IsEvenRole z) :
    ¬ IsEvenRole (flipPos z i) := by
  have hh : IsEvenRole (flipPos z i) ↔ ¬ IsEvenRole z := cubeFlip_parity z i
  exact fun he => hh.mp he hz

theorem binaryClass_flip_eq_some {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L)
    (v : CubePos n) (hv : IsEvenRole v) (i : Fin n) (t : Fin r) :
    binaryClass ids L E (flipPos v i) = some t ↔
      ids i + binarySyndrome ids v = (E t).1 := by
  rw [binaryClass_eq_some, binarySyndrome_flip]
  exact and_iff_right (flip_not_even v i hv)

theorem binaryClass_flip_isSome {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L)
    (v : CubePos n) (hv : IsEvenRole v) (i : Fin n) :
    (binaryClass ids L E (flipPos v i)).isSome ↔
      ids i + binarySyndrome ids v ∈ L := by
  classical
  unfold binaryClass
  simp [flip_not_even v i hv, binarySyndrome_flip]

theorem one_neighbour_per_class {n h r : ℕ} (ids : Fin n → Bits h)
    (hi : Function.Injective ids) (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L)
    (v : CubePos n) (hv : IsEvenRole v) (t : Fin r) :
    (Finset.univ.filter fun i => binaryClass ids L E (flipPos v i) = some t).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi' j hj'
  apply hi
  apply add_right_cancel (b := binarySyndrome ids v)
  exact ((binaryClass_flip_eq_some ids L E v hv i t).mp (Finset.mem_filter.mp hi').2).trans
    ((binaryClass_flip_eq_some ids L E v hv j t).mp (Finset.mem_filter.mp hj').2).symm

theorem one_internal_late_neighbour {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ids i - ids j ∉ L)
    (v : CubePos n) (hv : IsEvenRole v) :
    (A.filter fun i => (binaryClass ids L E (flipPos v i)).isSome).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  apply hA i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
  have h1 := (binaryClass_flip_isSome ids L E v hv i).mp (Finset.mem_filter.mp hi).2
  have h2 := (binaryClass_flip_isSome ids L E v hv j).mp (Finset.mem_filter.mp hj).2
  convert L.sub_mem h1 h2 using 1 <;> abel


noncomputable def bitEquiv : Bool ≃ ZMod 2 :=
  Equiv.ofBijective (fun b => if b = true then 1 else 0) (by decide)

@[simp] theorem bitEquiv_apply (b : Bool) : bitEquiv b = if b = true then 1 else 0 := rfl

noncomputable def cubeBitEquiv (n : ℕ) : CubePos n ≃ Bits n :=
  Equiv.piCongrRight (fun _ => bitEquiv)

def jointSyndrome {n h : ℕ} (ids : Fin n → Bits h) :
    Bits n →+ (Bits h × ZMod 2) where
  toFun x := (∑ i, x i • ids i, ∑ i, x i)
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext <;> simp [add_smul, Finset.sum_add_distrib]

@[simp] theorem jointSyndrome_single {n h : ℕ} (ids : Fin n → Bits h) (i : Fin n) :
    jointSyndrome ids (Pi.single i 1) = (ids i, 1) := by
  apply Prod.ext <;> simp [jointSyndrome, Pi.single_apply]

theorem jointSyndrome_cube {n h : ℕ} (ids : Fin n → Bits h) (z : CubePos n) :
    (jointSyndrome ids (cubeBitEquiv n z)).1 = binarySyndrome ids z := by
  change (∑ i, (cubeBitEquiv n z) i • ids i) = binarySyndrome ids z
  apply Finset.sum_congr rfl
  intro i _
  change (if z i = true then (1 : ZMod 2) else 0) • ids i = _
  split_ifs <;> simp_all

theorem odd_iff_jointSyndrome {n h : ℕ} (ids : Fin n → Bits h) (z : CubePos n) :
    ¬ IsEvenRole z ↔ (jointSyndrome ids (cubeBitEquiv n z)).2 = 1 := by
  classical
  have hh : (jointSyndrome ids (cubeBitEquiv n z)).2 =
      ((Finset.univ.filter fun i => z i = true).card : ZMod 2) := by
    change (∑ i, if z i = true then (1 : ZMod 2) else 0) = _
    simp
  rw [hh]
  change ¬ Even _ ↔ _
  rw [← ZMod.natCast_eq_zero_iff_even]
  exact (by decide : ∀ x : ZMod 2, x ≠ 0 ↔ x = 1) _

/-- Covering a coordinate hyperplane and one exterior point makes the
joint syndrome/parity homomorphism surjective. -/
theorem jointSyndrome_surjective {n h : ℕ} (ids : Fin n → Bits h) (j : Fin h)
    (hcover : ∀ a : coordinateSubspace (Finset.univ.erase j), ∃ i, ids i = a.1)
    (hout : ∃ i, ids i j ≠ 0) : Function.Surjective (jointSyndrome ids) := by
  classical
  let f := jointSyndrome ids
  obtain ⟨iz, hiz⟩ := hcover 0
  have h01 : (0, (1 : ZMod 2)) ∈ f.range := by
    refine ⟨Pi.single iz 1, ?_⟩
    simpa [f, hiz] using jointSyndrome_single ids iz
  have hi0 : ∀ i, (ids i, (0 : ZMod 2)) ∈ f.range := by
    intro i
    have hh : (ids i, (1 : ZMod 2)) ∈ f.range :=
      ⟨Pi.single i 1, jointSyndrome_single ids i⟩
    simpa using f.range.sub_mem hh h01
  have hH0 : ∀ w : Bits h, w j = 0 → (w, (0 : ZMod 2)) ∈ f.range := by
    intro w hw
    have hw' : w ∈ coordinateSubspace (Finset.univ.erase j) := by
      intro l hl
      have hlj : l = j := by simpa using hl
      simpa [hlj] using hw
    obtain ⟨i, hi⟩ := hcover ⟨w, hw'⟩
    simpa [hi] using hi0 i
  obtain ⟨io, hio⟩ := hout
  have hio1 : ids io j = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hio
  have hAll : ∀ w : Bits h, (w, (0 : ZMod 2)) ∈ f.range := by
    intro w
    by_cases hw : w j = 0
    · exact hH0 w hw
    · have hw1 : w j = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hw
      have hwsub : (w - ids io) j = 0 := by simp [hw1, hio1]
      simpa using f.range.add_mem (hH0 (w - ids io) hwsub) (hi0 io)
  intro wp
  rcases wp with ⟨w, p⟩
  have hp : p = 0 ∨ p = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p
  rcases hp with rfl | rfl
  · exact hAll w
  · simpa using f.range.add_mem (hAll w) h01

/-- Equal fibers of a surjective additive homomorphism have the quotient
of the domain cardinality by the codomain cardinality. -/
theorem hom_fiber_card {α β : Type} [AddGroup α] [AddGroup β]
    [Fintype α] [Fintype β] (f : α →+ β) (hf : Function.Surjective f) (b : β) :
    Nat.card {a // f a = b} = Fintype.card α / Fintype.card β := by
  classical
  rw [Nat.card_eq_fintype_card]
  let F : β → ℕ := fun c => (Finset.univ.filter fun a => f a = c).card
  have hF : ∀ c, F c = F b := by
    intro c
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf c) (hf b)
  have hsum : Fintype.card α = Fintype.card β * F b := by
    have hh := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
      (f := f) (fun a _ => Finset.mem_univ (f a))
    change Fintype.card α = ∑ b, F b at hh
    simpa only [hF, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using hh
  rw [hsum]
  have hbcard : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨b⟩
  simpa [F, Fintype.card_subtype, Nat.mul_div_cancel_left _ hbcard] using
    (show F b = F b from rfl)


noncomputable def splitCoordinateEquiv {h : ℕ} (I : Finset (Fin h))
    (j : Fin h) (hj : j ∈ I) :
    coordinateSubspace I ≃ (coordinateSubspace (I.erase j) × ZMod 2) where
  toFun v := (⟨Function.update v.1 j 0, by
    intro l hl
    by_cases hlj : l = j
    · subst l; simp
    · have hlI : l ∉ I := by simpa [hlj] using hl
      simp [hlj, v.2 l hlI]⟩, v.1 j)
  invFun vc := ⟨Function.update vc.1.1 j vc.2, by
    intro l hl
    have hlj : l ≠ j := by intro he; subst l; exact hl hj
    have hlI : l ∉ I.erase j := by simp [hl]
    simp [hlj, vc.1.2 l hlI]⟩
  left_inv v := by
    apply Subtype.ext
    funext l
    by_cases hlj : l = j <;> simp [hlj]
  right_inv vc := by
    apply Prod.ext
    · apply Subtype.ext
      funext l
      by_cases hlj : l = j
      · subst l
        have hz := vc.1.2 j (by simp)
        simp [hz]
      · simp [hlj]
    · simp

noncomputable def finBitEquiv : Fin 2 ≃ ZMod 2 :=
  Equiv.ofBijective (fun i => (i.val : ZMod 2)) (by decide)

/-- Enumerate a subspace in pairs, alternating its two coordinate halves. -/
noncomputable def balancedEnum {h : ℕ} (I : Finset (Fin h)) (j : Fin h) (hj : j ∈ I) :
    Fin (2 ^ (I.card - 1) * 2) ≃ coordinateSubspace I := by
  classical
  let q := 2 ^ (I.card - 1)
  have hc : Fintype.card (coordinateSubspace (I.erase j)) = q := by
    rw [coordinate_card, Finset.card_erase_of_mem hj]
  let e : Fin q ≃ coordinateSubspace (I.erase j) :=
    (Fintype.card_eq.mp (by simpa using hc.symm)).some
  exact finProdFinEquiv.symm.trans ((e.prodCongr finBitEquiv).trans (splitCoordinateEquiv I j hj).symm)

theorem balancedEnum_coordinate {h : ℕ} (I : Finset (Fin h)) (j : Fin h) (hj : j ∈ I)
    (t : Fin (2 ^ (I.card - 1) * 2)) :
    (balancedEnum I j hj t).1 j = (t.val % 2 : ℕ) := by
  simp [balancedEnum, splitCoordinateEquiv, finProdFinEquiv, finBitEquiv]


def suffixSet (r j : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun t => r - j ≤ t.val

noncomputable def suffixNeighbourSet {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L) (v : CubePos n) (j : ℕ) :
    Finset (Fin n) := Finset.univ.filter fun i =>
      ∃ t ∈ suffixSet r j, binaryClass ids L E (flipPos v i) = some t

theorem suffixSet_card {r j : ℕ} (hj : j ≤ r) : (suffixSet r j).card = j := by
  classical
  let e : Fin j ≃ suffixSet r j := {
    toFun := fun x => ⟨⟨r - j + x.val, by omega⟩, by
      simp only [suffixSet, Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩
    invFun := fun t => ⟨t.1.val - (r - j), by
      have ht : r - j ≤ t.1.val := (Finset.mem_filter.mp t.2).2
      have hlt := t.1.isLt
      omega⟩
    left_inv := by intro x; apply Fin.ext; dsimp; omega
    right_inv := by
      intro t
      apply Subtype.ext
      apply Fin.ext
      have ht : r - j ≤ t.1.val := (Finset.mem_filter.mp t.2).2
      dsimp
      omega }
  simpa using (Fintype.card_congr e).symm

theorem suffixNeighbour_upper {n h r : ℕ} (ids : Fin n → Bits h)
    (hi : Function.Injective ids) (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L)
    (v : CubePos n) (hv : IsEvenRole v) {j : ℕ} (hj : j ≤ r) :
    (suffixNeighbourSet ids L E v j).card ≤ j := by
  classical
  let N := suffixNeighbourSet ids L E v j
  have hex : ∀ i : N, ∃ t : suffixSet r j,
      binaryClass ids L E (flipPos v i.1) = some t.1 := by
    intro i
    obtain ⟨t, ht, he⟩ := (Finset.mem_filter.mp i.2).2
    exact ⟨⟨t, ht⟩, he⟩
  let f : N → suffixSet r j := fun i => (hex i).choose
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hi
    apply add_right_cancel (b := binarySyndrome ids v)
    have h1 := (binaryClass_flip_eq_some ids L E v hv a.1 (f a).1).mp (hex a).choose_spec
    have h2 := (binaryClass_flip_eq_some ids L E v hv b.1 (f b).1).mp (hex b).choose_spec
    rw [hab] at h1
    exact h1.trans h2.symm
  have hh := Fintype.card_le_of_injective f hinj
  simpa [N, suffixSet_card hj] using hh

theorem adjacent_bit_sum (m : ℕ) :
    (m % 2 : ℕ) + ((m + 1) % 2 : ℕ) = (1 : ZMod 2) := by
  have hm := Nat.mod_lt m (by omega : 0 < 2)
  have hm' := Nat.mod_lt (m + 1) (by omega : 0 < 2)
  have he : (m % 2 = 0 ∧ (m + 1) % 2 = 1) ∨
      (m % 2 = 1 ∧ (m + 1) % 2 = 0) := by omega
  rcases he with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [h1,h2]

theorem suffixNeighbour_lower {n h r : ℕ} (ids : Fin n → Bits h)
    (L : Submodule (ZMod 2) (Bits h)) (E : Fin r ≃ L) (j0 : Fin h)
    (hcover : ∀ a : coordinateSubspace (Finset.univ.erase j0), ∃ i, ids i = a.1)
    (hE : ∀ t, (E t).1 j0 = (t.val % 2 : ℕ))
    (v : CubePos n) (hv : IsEvenRole v) {j : ℕ} (hj : j ≤ r) :
    j / 2 ≤ (suffixNeighbourSet ids L E v j).card := by
  classical
  let N := suffixNeighbourSet ids L E v j
  have hex : ∀ q : Fin (j / 2), ∃ i : N, ∃ t : Fin r,
      binaryClass ids L E (flipPos v i.1) = some t ∧
      (t.val = r - j + 2 * q.val ∨ t.val = r - j + 2 * q.val + 1) := by
    intro q
    have hq := q.isLt
    let a : Fin r := ⟨r - j + 2 * q.val, by omega⟩
    let b : Fin r := ⟨r - j + 2 * q.val + 1, by omega⟩
    have hbit : (E a).1 j0 + (E b).1 j0 = 1 := by
      rw [hE, hE]
      exact adjacent_bit_sum _
    have hmatch : (E a).1 j0 = binarySyndrome ids v j0 ∨
        (E b).1 j0 = binarySyndrome ids v j0 :=
      (by decide : ∀ x y c : ZMod 2, x + y = 1 → x = c ∨ y = c) _ _ _ hbit
    have hget : ∀ t : Fin r, (E t).1 j0 = binarySyndrome ids v j0 →
        (t.val = a.val ∨ t.val = b.val) →
        ∃ i : N, ∃ t' : Fin r,
          binaryClass ids L E (flipPos v i.1) = some t' ∧
          (t'.val = a.val ∨ t'.val = b.val) := by
      intro t ht hval
      let w := (E t).1 - binarySyndrome ids v
      have hw : w ∈ coordinateSubspace (Finset.univ.erase j0) := by
        intro l hl
        have hlj : l = j0 := by simpa using hl
        subst l
        simp [w, ht]
      obtain ⟨i, hi⟩ := hcover ⟨w, hw⟩
      have hc : binaryClass ids L E (flipPos v i) = some t := by
        apply (binaryClass_flip_eq_some ids L E v hv i t).mpr
        rw [hi]
        simp [w]
      have hts : t ∈ suffixSet r j := by
        simp only [suffixSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hval with ha | hb
        · rw [ha]; dsimp [a]; omega
        · rw [hb]; dsimp [b]; omega
      have hin : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, hts, hc⟩
      exact ⟨⟨i, hin⟩, t, hc, hval⟩
    rcases hmatch with ha | hb
    · simpa [a,b] using hget a ha (Or.inl rfl)
    · simpa [a,b] using hget b hb (Or.inr rfl)
  let f : Fin (j / 2) → N := fun q => (hex q).choose
  have hinj : Function.Injective f := by
    intro p q hpq
    obtain ⟨t, ht, htv⟩ := (hex p).choose_spec
    obtain ⟨u, hu, huv⟩ := (hex q).choose_spec
    have hi : (f p).1 = (f q).1 := congrArg Subtype.val hpq
    rw [hi] at ht
    have htu : t = u := Option.some.inj (ht.symm.trans hu)
    have hval := congrArg Fin.val htu
    apply Fin.ext
    omega
  simpa [N] using Fintype.card_le_of_injective f hinj


theorem binaryClass_fiber_card {n h : ℕ} (hn : 0 < n) (ids : Fin n → Bits h)
    (hsurj : Function.Surjective (jointSyndrome ids)) (w : Bits h) :
    Fintype.card {z : CubePos n // ¬ IsEvenRole z ∧ binarySyndrome ids z = w} =
      2 ^ (n - 1) / 2 ^ h := by
  classical
  let e : {z : CubePos n // ¬ IsEvenRole z ∧ binarySyndrome ids z = w} ≃
      {x : Bits n // jointSyndrome ids x = (w, 1)} :=
    Equiv.subtypeEquiv (cubeBitEquiv n) (by
      intro z
      rw [Prod.ext_iff, jointSyndrome_cube, ← odd_iff_jointSyndrome]
      exact and_comm)
  rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card,
    hom_fiber_card (jointSyndrome ids) hsurj (w, 1)]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Fintype.card_prod]
  have hn1 : n - 1 + 1 = n := by omega
  have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc
      2 ^ n = 2 ^ (n - 1 + 1) := by rw [hn1]
      _ = _ := by rw [pow_succ]
  rw [hp, Nat.mul_div_mul_right _ _ (by omega : 0 < 2)]

/-- The first d coordinates of a finite binary vector space. -/
def initialCoordinates (h d : ℕ) : Finset (Fin h) :=
  Finset.univ.filter fun j => j.val < d

theorem initialCoordinates_card {h d : ℕ} (hd : d ≤ h) :
    (initialCoordinates h d).card = d := by
  classical
  let e : Fin d ≃ initialCoordinates h d := {
    toFun := fun j => ⟨Fin.castLE hd j, by simp [initialCoordinates]⟩
    invFun := fun j => ⟨j.1.val, (Finset.mem_filter.mp j.2).2⟩
    left_inv := by intro j; rfl
    right_inv := by intro j; apply Subtype.ext; apply Fin.ext; rfl }
  simpa using (Fintype.card_congr e).symm

end HypercubeRamsey.Lane_sol_s16_syn
