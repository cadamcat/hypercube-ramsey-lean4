import HypercubeRamsey.S05.History_sol_s05_h5l_geom
import Mathlib.Data.Nat.Choose.Bounds

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical OAI.HypercubeRamsey

noncomputable section
set_option maxHeartbeats 800000

/-- Bin distance ignores the boundary bit, whose two choices are counted separately. -/
def coarseNear {n : ℕ} (R : ℕ) (i q : CoarseKey5 n) : Prop :=
  ∀ a, Nat.dist (i.1 a).val (q.1 a).val ≤ R

def coarseBall {n : ℕ} (R : ℕ) (i : CoarseKey5 n) : Finset (CoarseKey5 n) :=
  Finset.univ.filter (coarseNear R i)

theorem coarseNear_refl {n : ℕ} (R : ℕ) (i : CoarseKey5 n) : coarseNear R i i := by
  intro a
  simp

theorem coarseNear_symm {n : ℕ} {R : ℕ} {i q : CoarseKey5 n}
    (h : coarseNear R i q) : coarseNear R q i := by
  intro a
  simpa only [Nat.dist_comm] using h a

theorem coarseNear_trans {n : ℕ} {R S : ℕ} {i q z : CoarseKey5 n}
    (h : coarseNear R i q) (h' : coarseNear S q z) : coarseNear (R + S) i z := by
  intro a
  have h1 := h a
  have h2 := h' a
  unfold Nat.dist at *
  omega

private theorem near_values_card {n : ℕ} (R w : ℕ) :
    (Finset.univ.filter (fun z : Fin (n + 1) => Nat.dist w z.val ≤ R)).card ≤ 2 * R + 1 := by
  let S := Finset.univ.filter (fun z : Fin (n + 1) => Nat.dist w z.val ≤ R)
  have hs : S.image Fin.val ⊆ Finset.Icc (w - R) (w + R) := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    have hd := (Finset.mem_filter.mp ha).2
    simp only [Finset.mem_Icc]
    unfold Nat.dist at hd
    omega
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective S Fin.val_injective] at hc
  simp only [Nat.card_Icc] at hc
  change S.card ≤ _
  omega

theorem coarseBall_card {n : ℕ} (R : ℕ) (i : CoarseKey5 n) :
    (coarseBall R i).card ≤ 2 * (2 * R + 1) ^ coarseChunkCount5 := by
  let V : Fin coarseChunkCount5 → Finset (Fin (n + 1)) :=
    fun a => Finset.univ.filter fun z => Nat.dist (i.1 a).val z.val ≤ R
  let B := (Finset.univ.pi V).image
    (fun f : ∀ a : Fin coarseChunkCount5, a ∈ Finset.univ → Fin (n + 1) =>
      fun a => f a (Finset.mem_univ a))
  have hs : coarseBall R i ⊆ B.product Finset.univ := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
    apply Finset.mem_image.mpr
    refine ⟨fun a _ => q.1 a, ?_, rfl⟩
    simp only [Finset.mem_pi]
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq' a⟩
  have hB : B.card ≤ (2 * R + 1) ^ coarseChunkCount5 := by
    calc
      _ ≤ (Finset.univ.pi V).card := Finset.card_image_le
      _ = ∏ a : Fin coarseChunkCount5, (V a).card := by simp
      _ ≤ ∏ _a : Fin coarseChunkCount5, (2 * R + 1) :=
        Finset.prod_le_prod fun a _ => near_values_card R (i.1 a).val
      _ = _ := by simp
  calc
    _ ≤ (B.product Finset.univ).card := Finset.card_le_card hs
    _ = B.card * 2 := by simp
    _ ≤ (2 * R + 1) ^ coarseChunkCount5 * 2 := Nat.mul_le_mul_right _ hB
    _ = _ := Nat.mul_comm _ _

theorem coarseRange_near {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n)
    (q : CoarseKey5 n) (hq : q ∈ g.coarseRange x) : coarseNear 1 (g.key x) q := by
  have hh := g.coarseRange_subset_nearKeys5 x hq
  obtain ⟨hv, hb⟩ := Finset.mem_product.mp hh
  obtain ⟨f, hf, he⟩ := Finset.mem_image.mp hv
  intro a
  have hfa := Finset.mem_pi.mp hf a (Finset.mem_univ a)
  obtain ⟨d, hd, hval⟩ := Finset.mem_image.mp hfa
  have he' : f a (Finset.mem_univ a) = q.1 a := congrFun he a
  rw [← he', ← hval]
  change Nat.dist (g.coarseBin x a).val (binNeighborVal5 (g.coarseBin x a) d).val ≤ 1
  unfold binNeighborVal5
  split_ifs <;> simp only [Nat.dist] <;> omega

def signBall1 {m : ℕ} (t : CubeVertex m) : Finset (CubeVertex m) :=
  insert t (Finset.univ.image (flipVertex5 t))

def signBall2 {m : ℕ} (t : CubeVertex m) : Finset (CubeVertex m) :=
  (signBall1 t).biUnion signBall1

theorem signBall1_card {m : ℕ} (t : CubeVertex m) : (signBall1 t).card ≤ m + 1 := by
  have hi := Finset.card_insert_le t (Finset.univ.image (flipVertex5 t))
  have hf := Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := flipVertex5 t)
  simpa only [signBall1, Finset.card_univ, Fintype.card_fin] using hi.trans (Nat.add_le_add_right hf 1)

theorem signBall2_card {m : ℕ} (t : CubeVertex m) : (signBall2 t).card ≤ (m + 1) ^ 2 := by
  calc
    _ ≤ ∑ u ∈ signBall1 t, (signBall1 u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ signBall1 t, (m + 1) := Finset.sum_le_sum fun u _ => signBall1_card u
    _ = (signBall1 t).card * (m + 1) := by simp
    _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_right _ (signBall1_card t)
    _ = _ := (pow_two _).symm

theorem flip_twice {m : ℕ} (t : CubeVertex m) (a : Fin m) :
    flipVertex5 (flipVertex5 t a) a = t := by
  funext b
  by_cases hb : b = a
  · subst b
    simp [flipVertex5]
  · simp [flipVertex5, hb]

theorem signBall1_symm {m : ℕ} {t u : CubeVertex m} (h : u ∈ signBall1 t) :
    t ∈ signBall1 u := by
  rcases Finset.mem_insert.mp h with he | hf
  · subst u
    simp [signBall1]
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, flip_twice t a⟩

theorem signBall2_symm {m : ℕ} {t u : CubeVertex m} (h : u ∈ signBall2 t) :
    t ∈ signBall2 u := by
  obtain ⟨v, hv, hu⟩ := Finset.mem_biUnion.mp h
  exact Finset.mem_biUnion.mpr ⟨v, signBall1_symm hu, signBall1_symm hv⟩

theorem signBall1_subset2 {m : ℕ} (t : CubeVertex m) : signBall1 t ⊆ signBall2 t := by
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨t, by simp [signBall1], hu⟩

theorem adjacent_sign_ball {n m : ℕ} (g : ChunkGeometry5 n m)
    (x y : CubeVertex n) (hxy : (cube n).Adj x y) : g.sign y ∈ signBall1 (g.sign x) := by
  have hh := adjacent_sign_mem g x y hxy
  rcases Finset.mem_insert.mp hh with he | hf
  · exact Finset.mem_insert.mpr (Or.inl he)
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hf
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, he⟩))

theorem keyAt_low_data {n m J : ℕ} (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ)
    (k : CoarseKey5 n × CubeVertex m × Fin (J + 1)) (hk : keyAt5 J i t j = .inl k) :
    k.1 = i ∧ k.2.1 = t ∧ k.2.2.val = j := by
  unfold keyAt5 at hk
  split_ifs at hk with hj
  · have he := Sum.inl.inj hk
    rw [← he]
    exact ⟨rfl, rfl, rfl⟩

theorem low_type_scope_location {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : CubeVertex n) (k : CoarseKey5 n × CubeVertex m × Fin (J + 1))
    (hk : Sum.inl k ∈ g.typeKeys J x) :
    g.severity x ≤ J ∧ coarseNear 1 (g.key x) k.1 ∧
      k.2.1 ∈ signBall1 (g.sign x) ∧
      k.2.2.val ≤ g.severity x + 1 ∧ g.severity x ≤ k.2.2.val + 1 := by
  have hlo : g.severity x ≤ J := by
    by_contra h
    rw [ChunkGeometry5.typeKeys, ite_eq_right h] at hk
    obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hk
    cases he
  have hc := coarseRange_near g x k.1
    (Lane_sol_s05_h1.typeKeys_coarse_subset g J x (.inl k) hk)
  have hlev := Lane_sol_s05_h1.typeKeys_low_levels g J x hlo k hk
  have hsev : k.2.2.val ≤ g.severity x + 1 ∧ g.severity x ≤ k.2.2.val + 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlev
    omega
  refine ⟨hlo, hc, ?_, hsev⟩
  rw [ChunkGeometry5.typeKeys, ite_eq_left hlo] at hk
  rcases Finset.mem_union.mp hk with hk | hk
  · rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hk
      rw [(keyAt_low_data q (g.sign x) (g.severity x) k he).2.1]
      simp [signBall1]
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hk
      rw [(keyAt_low_data (g.key x) _ (g.severity x) k he).2.1]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
    rw [(keyAt_low_data (g.key x) (g.sign x) j k he).2.1]
    simp [signBall1]

/-- One low key can be touched only from a radius-two bin/sign/severity region. -/
def lowRegion {n m J : ℕ} (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ) :
    Finset (CoarseKey5 n × CubeVertex m × Fin (J + 1)) :=
  (coarseBall 2 i).product ((signBall2 t).product
    (Finset.univ.filter fun h : Fin (J + 1) => h.val ≤ j + 2 ∧ j ≤ h.val + 2))

theorem lowRegion_card {n m J : ℕ} (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ) :
    (@lowRegion n m J i t j).card ≤ (2 * 5 ^ coarseChunkCount5) * (m + 1) ^ 2 * 5 := by
  have hl : (Finset.univ.filter fun h : Fin (J + 1) => h.val ≤ j + 2 ∧ j ≤ h.val + 2).card ≤ 5 := by
    have he : (Finset.univ.filter fun h : Fin (J + 1) => h.val ≤ j + 2 ∧ j ≤ h.val + 2) =
        Finset.univ.filter (fun h => Nat.dist j h.val ≤ 2) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold Nat.dist
      omega
    rw [he]
    exact near_values_card 2 j
  calc
    _ = (coarseBall 2 i).card * ((signBall2 t).card *
        (Finset.univ.filter fun h : Fin (J + 1) => h.val ≤ j + 2 ∧ j ≤ h.val + 2).card) := by
      simp only [lowRegion, Finset.product_eq_sprod, Finset.card_product]
    _ ≤ (2 * 5 ^ coarseChunkCount5) * ((m + 1) ^ 2 * 5) := by
      exact Nat.mul_le_mul (coarseBall_card 2 i) (Nat.mul_le_mul (signBall2_card t) hl)
    _ = _ := by ring

section Records

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

abbrev GroupIndex := CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 3)

/-- A polynomial envelope shared by every alarm in a central group. -/
def groupScope (a : GroupIndex X) : Finset (LowCoordinates X) :=
  (coarseBall 2 a.1).product ((signBall2 a.2.1).product Finset.univ)

theorem groupScope_card (a : GroupIndex X) :
    (groupScope X a).card ≤
      (2 * 5 ^ coarseChunkCount5) * (X.p.m n + 1) ^ 2 * (X.p.J n + 1) := by
  calc
    _ = (coarseBall 2 a.1).card * ((signBall2 a.2.1).card * (X.p.J n + 1)) := by
      simp only [groupScope, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 * 5 ^ coarseChunkCount5) * ((X.p.m n + 1) ^ 2 * (X.p.J n + 1)) :=
      Nat.mul_le_mul (coarseBall_card 2 a.1)
        (Nat.mul_le_mul_right (X.p.J n + 1) (signBall2_card a.2.1))
    _ = _ := by ring

theorem groups_touching_card (k : LowCoordinates X) :
    (Finset.univ.filter fun a : GroupIndex X => k ∈ groupScope X a).card ≤
      (2 * 5 ^ coarseChunkCount5) * (X.p.m n + 1) ^ 2 * (X.p.J n + 3) := by
  have he : (Finset.univ.filter fun a : GroupIndex X => k ∈ groupScope X a) =
      (coarseBall 2 k.1).product ((signBall2 k.2.1).product Finset.univ) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, groupScope,
      Finset.product_eq_sprod, Finset.mem_product, and_true, coarseBall]
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨coarseNear_symm hc, signBall2_symm hs⟩
    · rintro ⟨hc, hs⟩
      exact ⟨coarseNear_symm hc, signBall2_symm hs⟩
  rw [he]
  calc
    _ = (coarseBall 2 k.1).card * ((signBall2 k.2.1).card * (X.p.J n + 3)) := by
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 * 5 ^ coarseChunkCount5) * ((X.p.m n + 1) ^ 2 * (X.p.J n + 3)) :=
      Nat.mul_le_mul (coarseBall_card 2 k.1)
        (Nat.mul_le_mul_right (X.p.J n + 3) (signBall2_card k.2.1))
    _ = _ := by ring

theorem roleKey_coarse (x : CubeVertex n) :
    (X.g.roleKey (X.p.J n) x).coarse = X.g.key x := by
  unfold ChunkGeometry5.roleKey
  split_ifs <;> rfl

theorem typeLowScope_group (x : CubeVertex n) (a : GroupIndex X)
    (hq : X.g.key x = a.1) (ht : X.g.sign x = a.2.1) :
    lowTypeScope X (X.g.evenType (X.p.J n) x) ⊆ groupScope X a := by
  intro k hk
  have hk' : Sum.inl k ∈ (X.g.evenType (X.p.J n) x).2.1 := by
    simpa only [lowTypeScope, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  have hloc := low_type_scope_location X.g (X.p.J n) x k hk' 
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
    Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
  · rw [← hq]
    intro b
    exact (hloc.2.1 b).trans (by omega)
  · rw [← ht]
    exact signBall1_subset2 _ hloc.2.2.1

theorem roleKey_low_data (x : CubeVertex n) (k : LowCoordinates X)
    (hk : X.g.roleKey (X.p.J n) x = .inl k) :
    X.g.key x = k.1 ∧ X.g.sign x = k.2.1 ∧ X.g.severity x = k.2.2.val := by
  unfold ChunkGeometry5.roleKey at hk
  split_ifs at hk with hlo
  · have he := Sum.inl.inj hk
    rw [← he]
    exact ⟨rfl, rfl, rfl⟩

private theorem observation_witness (r : X.AbsRecord) (y : OddRole5 n) (μ)
    (hr : X.RecordFrom r y μ) (c) (hc : c ∈ r.2.1) :
    ∃ a ∈ Setup5.evenNbrs y, c = (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1) := by
  have hh := Eq.mp (congrArg (fun S => c ∈ S) hr.2.1) hc
  have hm := by
    letI : DecidableEq (Fin (X.p.T n) × X.Ty) := Classical.decEq _
    exact Finset.mem_image.mp hh
  obtain ⟨a, ha, he⟩ := hm
  exact ⟨a, ha, he.symm⟩

private theorem reference_witness (r : X.AbsRecord) (y : OddRole5 n) (μ)
    (hr : X.RecordFrom r y μ) (c) (hc : c ∈ r.2.2.1) :
    ∃ a ∈ Setup5.evenNbrs y,
      c = (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1) := by
  have hh := Eq.mp (congrArg (fun S => c ∈ S) hr.2.2.1) hc
  have hm := by
    letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
    exact Finset.mem_image.mp hh
  obtain ⟨a, ha, he⟩ := hm
  refine ⟨a, ?_, he.symm⟩
  letI : DecidablePred (fun a : EvenRole5 n =>
      r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
        r.1.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome) :=
    fun a => @instDecidableAnd _ _ (Finset.decidableMem _ _) (inferInstance)
  exact Finset.mem_of_mem_filter a ha

theorem recordLowScope_region (r : X.AbsRecord) (y : OddRole5 n) (μ)
    (hr : X.RecordFrom r y μ) :
    recordLowScope X r ⊆ lowRegion (X.g.key y.1) (X.g.sign y.1) (X.g.severity y.1) := by
  have hocc : X.RecOccurs r := ⟨y, μ, hr⟩
  intro k hk
  have hh : Sum.inl k ∈ recordKeys X r := by
    simpa only [recordLowScope, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  simp only [recordKeys, Finset.mem_insert, Finset.mem_union] at hh
  have hmem (hc : coarseNear 2 (X.g.key y.1) k.1)
      (hs : k.2.1 ∈ signBall2 (X.g.sign y.1))
      (hj : k.2.2.val ≤ X.g.severity y.1 + 2 ∧ X.g.severity y.1 ≤ k.2.2.val + 2) :
      k ∈ lowRegion (X.g.key y.1) (X.g.sign y.1) (X.g.severity y.1) := by
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩,
      Finset.mem_product.mpr ⟨hs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩⟩
  rcases hh with ht | ho | hp
  · have hd := roleKey_low_data X y.1 (k) (hr.1.trans ht.symm)
    apply hmem
    · rw [← hd.1]
      exact coarseNear_refl _ _
    · rw [← hd.2.1]
      exact signBall1_subset2 _ (by simp [signBall1])
    · rw [← hd.2.2]
      omega
  · rw [occurring_record_arrays X r hocc] at ho
    obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp ho
    obtain ⟨a, ha, rfl⟩ := observation_witness X r y μ hr c hc
    have hloc := low_type_scope_location X.g (X.p.J n) a.1 k hkc
    have hadj : (cube n).Adj y.1 a.1 := (cube n).adj_symm (Finset.mem_filter.mp ha).2
    have hcoarse := coarseRange_near X.g y.1 (X.g.key a.1) (adjacent_key_mem X.g y.1 a.1 hadj)
    have hsign := adjacent_sign_ball X.g y.1 a.1 hadj
    have hsev := adjacent_severity X.g y.1 a.1 hadj
    apply hmem
    · exact coarseNear_trans hcoarse hloc.2.1
    · exact Finset.mem_biUnion.mpr ⟨X.g.sign a.1, hsign, hloc.2.2.1⟩
    · omega
  · obtain ⟨c, hc, hkc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := reference_witness X r y μ hr c hc
    have hopt : X.g.optionalKey (X.p.J n) a.1 = some (.inl k) :=
      Option.mem_def.mp (Option.mem_toFinset.mp hkc)
    have hsevA : X.g.severity a.1 = X.p.J n + 1 := by
      by_contra h
      simp [ChunkGeometry5.optionalKey, h] at hopt
    have hd : (X.g.key a.1, X.g.sign a.1,
        (⟨X.p.J n, Nat.lt_succ_self _⟩ : Fin (X.p.J n + 1))) = k := by
      simpa only [ChunkGeometry5.optionalKey, ite_eq_left hsevA,
        Option.some.injEq, Sum.inl.injEq] using hopt
    have hadj : (cube n).Adj y.1 a.1 := (cube n).adj_symm (Finset.mem_filter.mp ha).2
    have hsev := adjacent_severity X.g y.1 a.1 hadj
    apply hmem
    · rw [← congrArg Prod.fst hd]
      have hh := coarseRange_near X.g y.1 (X.g.key a.1) (adjacent_key_mem X.g y.1 a.1 hadj)
      intro b
      exact (hh b).trans (by omega)
    · rw [← congrArg (fun z : LowCoordinates X => z.2.1) hd]
      exact signBall1_subset2 _ (adjacent_sign_ball X.g y.1 a.1 hadj)
    · have hklev := congrArg (fun z : LowCoordinates X => z.2.2.val) hd
      dsimp only at hklev
      omega

theorem recordLowScope_card (r : X.AbsRecord) (hr : X.RecOccurs r) :
    (recordLowScope X r).card ≤
      (2 * 5 ^ coarseChunkCount5) * (X.p.m n + 1) ^ 2 * 5 := by
  obtain ⟨y, μ, hy⟩ := hr
  exact (Finset.card_le_card (recordLowScope_region X r y μ hy)).trans (lowRegion_card _ _ _)

theorem recordLowScope_group (r : X.AbsRecord) (a : GroupIndex X)
    (hr : X.RecOccursAt r a.2.1 a.2.2.val) (hq : r.1.coarse = a.1) :
    recordLowScope X r ⊆ groupScope X a := by
  obtain ⟨y, μ, hy, ht, hj⟩ := hr
  have hkey : X.g.key y.1 = a.1 := by
    rw [← roleKey_coarse X y.1, hy.1, hq]
  intro k hk
  have hreg := recordLowScope_region X r y μ hy hk
  obtain ⟨hc, hrest⟩ := Finset.mem_product.mp hreg
  obtain ⟨hs, hlev⟩ := Finset.mem_product.mp hrest
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩⟩
  · simpa only [hkey] using hc
  · simpa only [ht] using hs

theorem high_record_low_interface (r : X.AbsRecord) (y : OddRole5 n) (μ)
    (hr : X.RecordFrom r y μ) (hhigh : ∃ i, r.1 = .inr i)
    (hnonempty : (recordLowScope X r).Nonempty) :
    X.p.J n < X.g.severity y.1 ∧ X.g.severity y.1 ≤ X.p.J n + 2 := by
  obtain ⟨k, hk⟩ := hnonempty
  have hreg := recordLowScope_region X r y μ hr hk
  have hsev := (Finset.mem_filter.mp (Finset.mem_product.mp
    (Finset.mem_product.mp hreg).2).2).2
  have hkbound := k.2.2.isLt
  refine ⟨?_, by omega⟩
  obtain ⟨i, hi⟩ := hhigh
  by_contra h
  have hlo : X.g.severity y.1 ≤ X.p.J n := by omega
  have htarget := hr.1.trans hi
  simp only [ChunkGeometry5.roleKey, dite_eq_left hlo] at htarget
  cases htarget

end Records

end
end HypercubeRamsey.Lane_sol_s05_h5l
