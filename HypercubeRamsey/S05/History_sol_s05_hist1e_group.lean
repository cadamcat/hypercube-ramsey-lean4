import HypercubeRamsey.S05.History_sol_s05_hist1e_apply
import HypercubeRamsey.S05.History_sol_s05_h5l_counts
import HypercubeRamsey.S05.Bounds_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical OAI.HypercubeRamsey
open Lane_sol_s05_h5l
noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 1024

/-- Subsets of a fixed finite universe, with a bounded number of entries. -/
def sparseSubsets {A : Type*} [DecidableEq A] (U : Finset A) (k : ℕ) : Finset (Finset A) :=
  (Finset.range (k + 1)).biUnion U.powersetCard

theorem mem_sparseSubsets {A : Type*} [DecidableEq A] (U : Finset A) (k : ℕ) (S : Finset A) :
    S ∈ sparseSubsets U k ↔ S ⊆ U ∧ S.card ≤ k := by
  simp only [sparseSubsets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨h, hh, hS, he⟩
    exact ⟨hS, by omega⟩
  · rintro ⟨hS, hk⟩
    exact ⟨S.card, by omega, hS, rfl⟩

theorem sparseSubsets_card {A : Type*} [DecidableEq A] (U : Finset A) (k : ℕ) :
    (sparseSubsets U k).card ≤ (k + 1) * (U.card + 1) ^ k := by
  calc
    _ ≤ ∑ h ∈ Finset.range (k + 1), (U.powersetCard h).card := Finset.card_biUnion_le
    _ = ∑ h ∈ Finset.range (k + 1), U.card.choose h := by simp
    _ ≤ ∑ _h ∈ Finset.range (k + 1), (U.card + 1) ^ k := by
      apply Finset.sum_le_sum
      intro h hh
      have hk : h ≤ k := by have := Finset.mem_range.mp hh; omega
      exact (Nat.choose_le_pow _ _).trans ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega : 0 < U.card + 1) hk))
    _ = _ := by simp

/-- Split an observation image into arbitrary generic entries and a sparse exception image.
The exception budget counts states, rather than neighboring cube roles. -/
theorem joint_image_sparse {A B C Id : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype Id]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Id]
    (S : Finset A) (state : A → B) (sig : A → C) (μ : B → Id)
    (generic all : Finset C) (exceptional : Finset B) (k : ℕ)
    (hg : ∀ a ∈ S, state a ∉ exceptional → sig a ∈ generic)
    (ha : ∀ a ∈ S, sig a ∈ all)
    (hs : ∀ a ∈ S, ∀ b ∈ S, state a = state b → sig a = sig b)
    (hk : exceptional.card ≤ k) :
    S.image (fun a => (μ (state a), sig a)) ∈
      (((Finset.univ : Finset Id).product generic).powerset.product
        (sparseSubsets ((Finset.univ : Finset Id).product all) k)).image
          (fun d => d.1 ∪ d.2) := by
  let SG := S.filter fun a => state a ∉ exceptional
  let SE := S.filter fun a => state a ∈ exceptional
  let IG := SG.image fun a => (μ (state a), sig a)
  let IE := SE.image fun a => (μ (state a), sig a)
  have hG : IG ⊆ (Finset.univ : Finset Id).product generic := by
    intro c hc
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨haS, haE⟩ := Finset.mem_filter.mp ha'
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hg a haS haE⟩
  have hE : IE ⊆ (Finset.univ : Finset Id).product all := by
    intro c hc
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, ha a (Finset.mem_filter.mp ha').1⟩
  have hcard : IE.card ≤ exceptional.card := by
    by_cases hIE : IE.Nonempty
    · obtain ⟨c₀, _⟩ := hIE
      letI : Nonempty (Id × C) := ⟨c₀⟩
      let rep (b : B) : Id × C := if h : ∃ a ∈ SE, state a = b then
        (μ b, sig (Classical.choose h)) else c₀
      have hsub : IE ⊆ exceptional.image rep := by
        intro c hc
        obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp hc
        have hex : ∃ a' ∈ SE, state a' = state a := ⟨a, ha', rfl⟩
        refine Finset.mem_image.mpr ⟨state a, (Finset.mem_filter.mp ha').2, ?_⟩
        dsimp only [rep]
        rw [dif_pos hex]
        refine Prod.ext ?_ ?_
        · rfl
        · have hh := Classical.choose_spec hex
          exact hs _ (Finset.mem_filter.mp hh.1).1 a (Finset.mem_filter.mp ha').1 hh.2
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hIE]
  apply Finset.mem_image.mpr
  refine ⟨(IG, IE), Finset.mem_product.mpr
    ⟨Finset.mem_powerset.mpr hG, (mem_sparseSubsets _ _ _).2 ⟨hE, hcard.trans hk⟩⟩, ?_⟩
  change SG.image _ ∪ SE.image _ = S.image _
  rw [← Finset.image_union]
  congr 1
  ext a
  by_cases he : state a ∈ exceptional <;> simp [SG, SE, he]

/-- The flippable set can change at just the flipped fine chunk. -/
def nearFlippable {m : ℕ} (F : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  insert F (Finset.univ.biUnion fun i => {insert i F, F.erase i})

private theorem pair_card_le {A : Type*} [DecidableEq A] (a b : A) :
    ({a, b} : Finset A).card ≤ 2 := by
  calc
    _ ≤ ({b} : Finset A).card + 1 := Finset.card_insert_le _ _
    _ = _ := by simp

theorem nearFlippable_card {m : ℕ} (F : Finset (Fin m)) :
    (nearFlippable F).card ≤ 2 * m + 1 := by
  calc
    _ ≤ (Finset.univ.biUnion fun i => ({insert i F, F.erase i} : Finset _)).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ (∑ _i : Fin m, 2) + 1 := Nat.add_le_add_right
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => pair_card_le _ _)) 1
    _ = _ := by simp [Nat.mul_comm]

theorem flippable_flip_mem {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n) (a : Fin n) :
    g.flippable (flipVertex5 x a) ∈ nearFlippable (g.flippable x) := by
  by_cases hex : ∃ i, a ∈ g.fineChunks i
  · obtain ⟨i, hi⟩ := hex
    have he (j : Fin m) (hj : j ≠ i) :
        (j ∈ g.flippable (flipVertex5 x a)) ↔ j ∈ g.flippable x := by
      simp only [ChunkGeometry5.flippable, Finset.mem_filter, Finset.mem_univ, true_and,
        fine_counts_single_change g x a i hi j hj]
    by_cases hx : i ∈ g.flippable x <;> by_cases hy : i ∈ g.flippable (flipVertex5 x a)
    · have hF : g.flippable (flipVertex5 x a) = g.flippable x := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hx, hy]
        · exact he j hj
      simp [nearFlippable, hF]
    · have hF : g.flippable (flipVertex5 x a) = (g.flippable x).erase i := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hy]
        · simp [Finset.mem_erase, hj, he j hj]
      rw [hF]
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    · have hF : g.flippable (flipVertex5 x a) = insert i (g.flippable x) := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hy]
        · simp [Finset.mem_insert, hj, he j hj]
      rw [hF]
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, by simp⟩
    · have hF : g.flippable (flipVertex5 x a) = g.flippable x := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hx, hy]
        · exact he j hj
      simp [nearFlippable, hF]
  · push_neg at hex
    have hF : g.flippable (flipVertex5 x a) = g.flippable x := by
      ext j
      simp only [ChunkGeometry5.flippable, Finset.mem_filter, Finset.mem_univ, true_and,
        fineCount_flip_outside g x a j (hex j)]
    simp [nearFlippable, hF]

def neighboringLevels (j : ℕ) : Finset ℕ := {j, j + 1, j - 1}

theorem neighboringLevels_card (j : ℕ) : (neighboringLevels j).card ≤ 3 := by
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (pair_card_le _ _) 1)

theorem severity_flip_mem {n m : ℕ} (g : ChunkGeometry5 n m) (x : CubeVertex n) (a : Fin n) :
    g.severity (flipVertex5 x a) ∈ neighboringLevels (g.severity x) := by
  have h := severity_flip_bounds g x a
  simp only [neighboringLevels, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Reconstruct the type and optional key from the data that enter their definitions. -/
def signatureFromData {n m : ℕ} (J : ℕ) (q : CoarseKey5 n) (C : Finset (CoarseKey5 n))
    (t : CubeVertex m) (F : Finset (Fin m)) (j : ℕ) :
    EvenType5 n m J × Option (HiddenKey5 n m J) :=
  ((q, if j ≤ J then C.image (fun i => keyAt5 J i t j) ∪
      F.image (fun i => keyAt5 J q (flipVertex5 t i) j) ∪
      (({j + 1} : Finset ℕ) ∪ (if 0 < j then {j - 1} else ∅)).image (keyAt5 J q t)
    else C.image Sum.inr,
    if h : j ≤ J then some ⟨j, Nat.lt_succ_of_le h⟩ else none),
    if j = J + 1 then some (.inl (q, t, ⟨J, Nat.lt_succ_self J⟩)) else none)

theorem signatureFromData_eq {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) (x : CubeVertex n) :
    signatureFromData J (g.key x) (g.coarseRange x) (g.sign x) (g.flippable x) (g.severity x) =
      (g.evenType J x, g.optionalKey J x) := by
  rfl

def genericSignatures {n m : ℕ} (J : ℕ) (q : CoarseKey5 n) (t : CubeVertex m)
    (j : ℕ) (F : Finset (Fin m)) : Finset (EvenType5 n m J × Option (HiddenKey5 n m J)) :=
  (((coarseBall 1 q).product (coarseBall 2 q).powerset).product (neighboringLevels j)).image
    (fun d => signatureFromData J d.1.1 d.1.2 t F d.2)

def allSignatures {n m : ℕ} (J : ℕ) (q : CoarseKey5 n) (t : CubeVertex m)
    (j : ℕ) (F : Finset (Fin m)) : Finset (EvenType5 n m J × Option (HiddenKey5 n m J)) :=
  (((coarseBall 1 q).product (coarseBall 2 q).powerset).product
    ((signBall1 t).product ((nearFlippable F).product (neighboringLevels j)))).image
      (fun d => signatureFromData J d.1.1 d.1.2 d.2.1 d.2.2.1 d.2.2.2)

noncomputable def coarseCountBound (R : ℕ) : ℕ :=
  Classical.choose (show ∃ D : ℕ, 2 * (2 * R + 1) ^ coarseChunkCount5 ≤ D from
    ⟨2 * (2 * R + 1) ^ coarseChunkCount5, le_rfl⟩)

theorem coarseBall_card_bound {n : ℕ} (R : ℕ) (q : CoarseKey5 n) :
    (coarseBall R q).card ≤ coarseCountBound R :=
  (coarseBall_card R q).trans (Classical.choose_spec _)

@[irreducible] def signatureConstant : ℕ := coarseCountBound 1 * 2 ^ coarseCountBound 2 * 3

theorem genericSignatures_card {n m : ℕ} (J : ℕ) (q : CoarseKey5 n) (t : CubeVertex m)
    (j : ℕ) (F : Finset (Fin m)) : (genericSignatures J q t j F).card ≤ signatureConstant := by
  unfold signatureConstant
  calc
    _ ≤ _ := Finset.card_image_le
    _ = (coarseBall 1 q).card * 2 ^ (coarseBall 2 q).card * (neighboringLevels j).card := by simp
    _ ≤ coarseCountBound 1 * 2 ^ coarseCountBound 2 * 3 := by
      exact Nat.mul_le_mul (Nat.mul_le_mul (coarseBall_card_bound 1 q)
        (Nat.pow_le_pow_right (by omega : 0 < 2) (coarseBall_card_bound 2 q))) (neighboringLevels_card j)

theorem allSignatures_card {n m : ℕ} (J : ℕ) (q : CoarseKey5 n) (t : CubeVertex m)
    (j : ℕ) (F : Finset (Fin m)) :
    (allSignatures J q t j F).card ≤ signatureConstant * (m + 1) * (2 * m + 1) := by
  calc
    _ ≤ _ := Finset.card_image_le
    _ = (coarseBall 1 q).card * 2 ^ (coarseBall 2 q).card *
        ((signBall1 t).card * ((nearFlippable F).card * (neighboringLevels j).card)) := by simp
    _ ≤ coarseCountBound 1 * 2 ^ coarseCountBound 2 *
        ((m + 1) * ((2 * m + 1) * 3)) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul (coarseBall_card_bound 1 q)
        (Nat.pow_le_pow_right (by omega : 0 < 2) (coarseBall_card_bound 2 q)))
        (Nat.mul_le_mul (signBall1_card t) (Nat.mul_le_mul (nearFlippable_card F) (neighboringLevels_card j)))
    _ = _ := by unfold signatureConstant; ac_rfl

theorem neighbor_coarse_data {n m : ℕ} (g : ChunkGeometry5 n m) (x y : CubeVertex n)
    (h : (cube n).Adj x y) :
    g.key y ∈ coarseBall 1 (g.key x) ∧ g.coarseRange y ⊆ coarseBall 2 (g.key x) := by
  have hnear := coarseRange_near g x (g.key y) (adjacent_key_mem g x y h)
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear⟩, ?_⟩
  intro q hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, coarseNear_trans hnear (coarseRange_near g y q hq)⟩

theorem neighbor_allSignatures {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x y : CubeVertex n) (h : (cube n).Adj x y) :
    (g.evenType J y, g.optionalKey J y) ∈
      allSignatures J (g.key x) (g.sign x) (g.severity x) (g.flippable x) := by
  obtain ⟨a, hy⟩ := adjacent_flip x y h
  have hc := neighbor_coarse_data g x y h
  apply Finset.mem_image.mpr
  refine ⟨((g.key y, g.coarseRange y), (g.sign y, g.flippable y, g.severity y)), ?_,
    signatureFromData_eq g J y⟩
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_product.mpr ⟨hc.1, Finset.mem_powerset.mpr hc.2⟩,
    Finset.mem_product.mpr ⟨adjacent_sign_ball g x y h, Finset.mem_product.mpr ⟨?_, ?_⟩⟩⟩
  · rw [hy]; exact flippable_flip_mem g x a
  · rw [hy]; exact severity_flip_mem g x a

def criticalStates {n m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x : CubeVertex n) : Finset St.Site :=
  (((criticalChunks g x).biUnion g.fineChunks).image fun a => St.stateOf (flipVertex5 x a))

theorem neighbor_genericSignatures {n m J : ℕ} (g : ChunkGeometry5 n m) (St : CubeStates5 g J)
    (x y : CubeVertex n) (h : (cube n).Adj x y) (he : St.stateOf y ∉ criticalStates g St x) :
    (g.evenType J y, g.optionalKey J y) ∈
      genericSignatures J (g.key x) (g.sign x) (g.severity x) (g.flippable x) := by
  obtain ⟨a, hy⟩ := adjacent_flip x y h
  have hf : g.sign y = g.sign x ∧ g.flippable y = g.flippable x := by
    rw [hy]
    by_cases hex : ∃ i, a ∈ g.fineChunks i
    · obtain ⟨i, hi⟩ := hex
      apply fine_flip_noncritical g x i a hi
      intro hic
      apply he
      rw [hy]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_biUnion.mpr ⟨i, hic, hi⟩, rfl⟩
    · push_neg at hex
      have hcounts := fun i => fineCount_flip_outside g x a i (hex i)
      constructor
      · funext i
        simp only [ChunkGeometry5.sign, hcounts i]
      · ext i
        simp only [ChunkGeometry5.flippable, Finset.mem_filter, Finset.mem_univ, true_and, hcounts i]
  have hc := neighbor_coarse_data g x y h
  apply Finset.mem_image.mpr
  refine ⟨((g.key y, g.coarseRange y), g.severity y),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hc.1, Finset.mem_powerset.mpr hc.2⟩, ?_⟩, ?_⟩
  · rw [hy]; exact severity_flip_mem g x a
  · rw [← hf.1, ← hf.2]
    exact signatureFromData_eq g J y

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

def groupJointUniverse (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (F : Finset (Fin (X.p.m n))) : Finset (Finset (Fin (X.p.T n) × X.Ty × Option X.Key)) :=
  (((Finset.univ : Finset (Fin (X.p.T n))).product
    (genericSignatures (X.p.J n) q t j F)).powerset.product
    (sparseSubsets ((Finset.univ : Finset (Fin (X.p.T n))).product
      (allSignatures (X.p.J n) q t j F)) (2 * j))).image (fun d => d.1 ∪ d.2)

theorem groupJointUniverse_card (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (F : Finset (Fin (X.p.m n))) :
    (groupJointUniverse X q t j F).card ≤
      2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) *
        (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j) := by
  calc
    _ ≤ _ := Finset.card_image_le
    _ = 2 ^ (X.p.T n * (genericSignatures (X.p.J n) q t j F).card) *
        (sparseSubsets ((Finset.univ : Finset (Fin (X.p.T n))).product
          (allSignatures (X.p.J n) q t j F)) (2 * j)).card := by simp
    _ ≤ 2 ^ (X.p.T n * signatureConstant) *
        ((2 * j + 1) * (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j)) := by
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.mul_le_mul_left _ (genericSignatures_card _ _ _ _ _))
      · apply (sparseSubsets_card _ _).trans
        simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (Nat.add_le_add_right (Nat.mul_le_mul_left _ (allSignatures_card _ _ _ _ _)) 1) _)
    _ = _ := (Nat.mul_assoc _ _ _).symm

theorem joint_mem_groupUniverse (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n)) :
    ((Setup5.evenNbrs y).image fun a =>
      (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)) ∈
      groupJointUniverse X (X.g.key y.1) (X.g.sign y.1) (X.g.severity y.1) (X.g.flippable y.1) := by
  apply joint_image_sparse (Setup5.evenNbrs y) (fun a => X.St.stateOf a.1)
    (fun a => (X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)) μ
    _ _ (criticalStates X.g X.St y.1) _
  · intro a ha he
    exact neighbor_genericSignatures X.g X.St y.1 a.1 ((Finset.mem_filter.mp ha).2.symm) he
  · intro a ha
    exact neighbor_allSignatures X.g (X.p.J n) y.1 a.1 ((Finset.mem_filter.mp ha).2.symm)
  · intro a ha b hb he
    have h := X.St.state_determines a.1 b.1 he
    exact Prod.ext h.2.2.2.2.1 h.2.2.2.2.2.1
  · exact critical_flip_states_card_le X.g X.St y.1

/-- Canonical reconstruction used uniformly across centers in one group. -/
def recordFromJoint (ℓ : X.Key) (I : Finset (Fin (X.p.T n) × X.Ty × Option X.Key))
    (mask : Option (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound))) : X.AbsRecord :=
  (ℓ, I.image (fun c => (c.1, c.2.1)),
    I.filter (fun c => ℓ ∈ c.2.1.2.1 ∧ ℓ.isLeft = c.2.1.2.2.isSome), mask)

theorem recordFromJoint_eq (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n))
    (r : X.AbsRecord) (hr : X.RecordFrom r y μ) :
    recordFromJoint X r.1 ((Setup5.evenNbrs y).image fun a =>
      (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)) r.2.2.2 = r := by
  obtain ⟨hkey, hobs, href, hmask⟩ := hr
  refine Prod.ext ?_ ?_
  · rfl
  change _ = r.2
  apply Prod.ext
  · dsimp only [recordFromJoint]
    rw [hobs]
    simp only [Finset.image_image]
    rfl
  · apply Prod.ext
    · dsimp only [recordFromJoint]
      rw [href]
      ext c
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨a, ha, he⟩, hp⟩
        subst c
        exact ⟨a, ⟨ha, hp⟩, rfl⟩
      · rintro ⟨a, ⟨ha, hp⟩, he⟩
        subst c
        exact ⟨⟨a, ha, rfl⟩, hp⟩
    · rfl

/-- An enumerated mask is possible only for a low target at the interface. -/
theorem record_mask_interface (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n))
    (r : X.AbsRecord) (hr : X.RecordFrom r y μ) (c : Fin (X.p.T n) × X.Ty) (M : Finset (Fin X.blockBound))
    (hm : r.2.2.2 = some (c.1, c.2, M)) :
    r.1.isLeft ∧ r.1.level = X.p.J n ∧ M ∈ X.poolIdx.powersetCard (X.p.usedBlocks n) := by
  have hmask := hr.2.2.2
  rw [hm] at hmask
  obtain ⟨hl, a, ha, hK, hhigh, hi, hleg⟩ := hmask
  have hylo : X.g.severity y.1 ≤ X.p.J n := by
    rw [← hr.1] at hl
    by_contra hy
    simp [ChunkGeometry5.roleKey, hy] at hl
  have hain : ¬ X.g.severity a.1 ≤ X.p.J n := by
    rw [hK] at hhigh
    by_contra hh
    simp [ChunkGeometry5.evenType, hh] at hhigh
  obtain ⟨b, hb⟩ := cube_adj_eq_flip ((Finset.mem_filter.mp ha).2)
  have hsev := severity_flip_bounds X.g y.1 b
  rw [← hb] at hsev
  have hj : X.g.severity y.1 = X.p.J n := by omega
  refine ⟨hl, ?_, ?_⟩
  · rw [← hr.1]
    simp [ChunkGeometry5.roleKey, hylo, HiddenKey5.level, hj]
  · dsimp only [Setup5.LegitRef] at hleg
    rw [hhigh] at hleg
    exact Finset.mem_powersetCard.mpr ⟨hleg.2, hleg.1⟩

def groupMaskUniverse (ℓ : X.Key) (q : CoarseKey5 n) (t : CubeVertex (X.p.m n))
    (j : ℕ) (F : Finset (Fin (X.p.m n))) :
    Finset (Option (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound))) :=
  if ℓ.isLeft ∧ ℓ.level = X.p.J n then
    insert none ((((Finset.univ : Finset (Fin (X.p.T n))).product
      ((allSignatures (X.p.J n) q t j F).image Prod.fst)).product
        (X.poolIdx.powersetCard (X.p.usedBlocks n))).image (fun d => some (d.1.1, d.1.2, d.2)))
  else {none}

theorem mask_mem_groupUniverse (y : OddRole5 n) (μ : X.St.Site → Fin (X.p.T n))
    (r : X.AbsRecord) (hr : X.RecordFrom r y μ) :
    r.2.2.2 ∈ groupMaskUniverse X r.1 (X.g.key y.1) (X.g.sign y.1)
      (X.g.severity y.1) (X.g.flippable y.1) := by
  cases hm : r.2.2.2 with
  | none => unfold groupMaskUniverse; split_ifs <;> simp
  | some c =>
    have hi := record_mask_interface X y μ r hr (c.1, c.2.1) c.2.2 hm
    simp only [groupMaskUniverse, hi.1, hi.2.1, and_self, ite_true, Finset.mem_insert,
      Option.some_ne_none, false_or]
    have hh := hr.2.2.2
    rw [hm] at hh
    obtain ⟨_, a, ha, hK, hhigh, hid, hleg⟩ := hh
    refine Finset.mem_image.mpr ⟨((c.1, c.2.1), c.2.2), Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, hi.2.2⟩, rfl⟩
    rw [hK]
    exact Finset.mem_image.mpr ⟨_, neighbor_allSignatures X.g (X.p.J n) y.1 a.1
      ((Finset.mem_filter.mp ha).2.symm), rfl⟩

theorem groupMaskUniverse_card (ℓ : X.Key) (q : CoarseKey5 n) (t : CubeVertex (X.p.m n))
    (j : ℕ) (F : Finset (Fin (X.p.m n))) :
    (groupMaskUniverse X ℓ q t j F).card ≤
      if ℓ.isLeft ∧ ℓ.level = X.p.J n then
        1 + X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) *
          (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1 := by
  unfold groupMaskUniverse
  split_ifs with hi
  · calc
      _ ≤ _ := Finset.card_insert_le _ _
      _ ≤ (((Finset.univ : Finset (Fin (X.p.T n))).product
          ((allSignatures (X.p.J n) q t j F).image Prod.fst)).product
            (X.poolIdx.powersetCard (X.p.usedBlocks n))).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
      _ ≤ X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) *
          (X.poolIdx.card + 1) ^ X.p.usedBlocks n + 1 := by
        simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_powersetCard]
        apply Nat.add_le_add_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Finset.card_image_le.trans
          (allSignatures_card _ _ _ _ _))) ((Nat.choose_le_pow _ _).trans
          (Nat.pow_le_pow_left (Nat.le_succ _) _))
      _ = _ := Nat.add_comm _ _
  · simp

def groupRecordUniverse (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (F : Finset (Fin (X.p.m n))) : Finset X.AbsRecord :=
  ((groupJointUniverse X ℓ.coarse t j F).product (groupMaskUniverse X ℓ ℓ.coarse t j F)).image
    (fun d => recordFromJoint X ℓ d.1 d.2)

theorem roleKey_coarse (x : CubeVertex n) : (X.g.roleKey (X.p.J n) x).coarse = X.g.key x := by
  unfold ChunkGeometry5.roleKey
  split_ifs <;> rfl

theorem grouped_record_subset (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ) :
    (Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ) ⊆
      (smallSubsets (X.p.m n) j).biUnion (groupRecordUniverse X ℓ t j) := by
  intro r hr
  obtain ⟨⟨y, μ, hrec, hsign, hsev⟩, hkey⟩ := (Finset.mem_filter.mp hr).2
  have hq : X.g.key y.1 = ℓ.coarse := by rw [← roleKey_coarse X y.1, hrec.1, hkey]
  apply Finset.mem_biUnion.mpr
  refine ⟨X.g.flippable y.1, (mem_smallSubsets _).2 (by
    rw [← hsev]; exact flippable_card_le_severity X.g y.1), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(((Setup5.evenNbrs y).image fun a =>
    (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)),
      r.2.2.2), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [hq, hsign, hsev] using joint_mem_groupUniverse X y μ
  · simpa only [hkey, hq, hsign, hsev] using mask_mem_groupUniverse X y μ r hrec
  · rw [← hkey]
    exact recordFromJoint_eq X y μ r hrec

theorem grouped_record_card (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ) :
    (Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card ≤
      ((j + 1) * (X.p.m n + 1) ^ j) *
        (2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) *
          (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j)) *
        (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
          1 + X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) *
            (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1) := by
  calc
    _ ≤ _ := Finset.card_le_card (grouped_record_subset X ℓ t j)
    _ ≤ ∑ F ∈ smallSubsets (X.p.m n) j, (groupRecordUniverse X ℓ t j F).card := Finset.card_biUnion_le
    _ ≤ ∑ _F ∈ smallSubsets (X.p.m n) j,
        (2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) *
          (X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) + 1) ^ (2 * j)) *
          (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
            1 + X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1)) *
              (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1) := by
      apply Finset.sum_le_sum
      intro F hF
      exact Finset.card_image_le.trans (by
        simp only [Finset.product_eq_sprod, Finset.card_product]
        exact Nat.mul_le_mul (groupJointUniverse_card X _ _ _ _) (groupMaskUniverse_card X _ _ _ _ _))
    _ ≤ _ := by
      simp only [Finset.sum_const, smul_eq_mul]
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (smallSubsets_card _ _))

def farHighSignatures (q : CoarseKey5 n) : Finset (X.Ty × Option X.Key) :=
  ((coarseBall 1 q).product (coarseBall 2 q).powerset).image
    (fun d => ((d.1, d.2.image Sum.inr, none), none))

theorem farHighSignatures_card (q : CoarseKey5 n) :
    (farHighSignatures X q).card ≤ signatureConstant := by
  calc
    _ ≤ _ := Finset.card_image_le
    _ = (coarseBall 1 q).card * 2 ^ (coarseBall 2 q).card := by simp
    _ ≤ coarseCountBound 1 * 2 ^ coarseCountBound 2 :=
      Nat.mul_le_mul (coarseBall_card_bound 1 q)
        (Nat.pow_le_pow_right (by omega : 0 < 2) (coarseBall_card_bound 2 q))
    _ ≤ signatureConstant := by
      unfold signatureConstant
      exact Nat.le_mul_of_pos_right _ (by decide : 0 < 3)

theorem farHigh_record_card (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (hj : X.p.J n + 2 < j) :
    (Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card ≤
      2 ^ (X.p.T n * signatureConstant) := by
  let U := ((Finset.univ : Finset (Fin (X.p.T n))).product (farHighSignatures X ℓ.coarse)).powerset
  have hs : (Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ) ⊆
      U.image (fun I => recordFromJoint X ℓ I none) := by
    intro r hr
    obtain ⟨⟨y, μ, hrec, hsign, hsev⟩, hkey⟩ := (Finset.mem_filter.mp hr).2
    have hq : X.g.key y.1 = ℓ.coarse := by rw [← roleKey_coarse X y.1, hrec.1, hkey]
    have hy : ¬ X.g.severity y.1 ≤ X.p.J n := by omega
    have hleft : ¬ r.1.isLeft := by rw [← hrec.1]; simp [ChunkGeometry5.roleKey, hy]
    have hmask : r.2.2.2 = none := by
      cases hm : r.2.2.2 with
      | none => rfl
      | some c =>
        have hh := hrec.2.2.2
        rw [hm] at hh
        exact (hleft hh.1).elim
    apply Finset.mem_image.mpr
    refine ⟨((Setup5.evenNbrs y).image fun a =>
      (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)), ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro c hc
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hadj := (Finset.mem_filter.mp ha).2.symm
      obtain ⟨b, hb⟩ := adjacent_flip y.1 a.1 hadj
      have haSev := severity_flip_bounds X.g y.1 b
      rw [← hb] at haSev
      have haHi : ¬ X.g.severity a.1 ≤ X.p.J n := by omega
      have haOpt : X.g.severity a.1 ≠ X.p.J n + 1 := by omega
      have hdata := neighbor_coarse_data X.g y.1 a.1 hadj
      apply Finset.mem_image.mpr
      refine ⟨(X.g.key a.1, X.g.coarseRange a.1), ?_, ?_⟩
      · rw [← hq]
        exact Finset.mem_product.mpr ⟨hdata.1, Finset.mem_powerset.mpr hdata.2⟩
      · simp [ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, ChunkGeometry5.optionalKey, haHi, haOpt]
    · rw [← hkey, ← hmask]
      exact recordFromJoint_eq X y μ r hrec
  calc
    _ ≤ (U.image (fun I => recordFromJoint X ℓ I none)).card := Finset.card_le_card hs
    _ ≤ U.card := Finset.card_image_le
    _ = 2 ^ (X.p.T n * (farHighSignatures X ℓ.coarse).card) := by simp [U]
    _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < 2)
      (Nat.mul_le_mul_left _ (farHighSignatures_card X _))

theorem grouped_level_data (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (r : X.AbsRecord) (hr : X.RecOccursAt r t j) (hℓ : r.1 = ℓ) :
    (ℓ.isLeft → j = ℓ.level) ∧ (¬ ℓ.isLeft → ℓ.level = X.p.J n) := by
  obtain ⟨y, μ, hrec, hsign, hsev⟩ := hr
  rw [← hℓ, ← hrec.1]
  by_cases hy : X.g.severity y.1 ≤ X.p.J n
  · simp only [ChunkGeometry5.roleKey, dite_eq_left hy, HiddenKey5.level]; simp [hsev]
  · simp [ChunkGeometry5.roleKey, hy, HiddenKey5.level]

/-- A polynomial bound with an explicit mask factor. The coarse constant remains abstract
so kernel reduction does not enumerate the large finite coarse universe. -/
theorem record_card_polynomial (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (hm : 2 ≤ X.p.m n) (hD : signatureConstant ≤ X.p.m n) (hT : X.p.T n ≤ X.p.m n) :
    (Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card ≤
      2 ^ (X.p.T n * signatureConstant) * (X.p.m n + 1) ^ (50 * (ℓ.level + 1)) *
        (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
          (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1) := by
  let R := Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ
  by_cases hR : R.Nonempty
  · obtain ⟨r, hr⟩ := hR
    obtain ⟨hocc, hkey⟩ := (Finset.mem_filter.mp hr).2
    have hlevel := grouped_level_data X ℓ t j r hocc hkey
    by_cases hj : X.p.J n + 2 < j
    · have hcnt := farHigh_record_card X ℓ t j hj
      apply hcnt.trans
      have hp : 1 ≤ (X.p.m n + 1) ^ (50 * (ℓ.level + 1)) := Nat.one_le_pow _ _ (by omega)
      have hb : 1 ≤ (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
          (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1) := by
        split_ifs
        · exact Nat.one_le_pow _ _ (by omega)
        · rfl
      calc
        _ = 2 ^ (X.p.T n * signatureConstant) * 1 * 1 := by simp
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) hb
    · have hjl : j ≤ ℓ.level + 2 := by
        by_cases hl : ℓ.isLeft
        · have := hlevel.1 hl; omega
        · have := hlevel.2 hl; omega
      have hJ := Lane_sol_s05_h1.J_le_m X.p n (by omega)
      have hjm : j ≤ X.p.m n + 2 := by omega
      let M := X.p.m n + 1
      let A := X.p.T n * (signatureConstant * (X.p.m n + 1) * (2 * X.p.m n + 1))
      let B := (if ℓ.isLeft ∧ ℓ.level = X.p.J n then (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1)
      have hM : 3 ≤ M := by dsimp [M]; omega
      have hB : 1 ≤ B := by
        dsimp only [B]
        split_ifs
        · exact Nat.one_le_pow _ _ (by omega)
        · rfl
      have hA : A + 1 ≤ M ^ 6 := by
        have h2 : 2 * X.p.m n + 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
        have hTD : X.p.T n * signatureConstant ≤ M ^ 2 := by
          calc
            _ ≤ X.p.m n * X.p.m n := Nat.mul_le_mul hT hD
            _ ≤ M * M := Nat.mul_le_mul (by dsimp [M]; omega) (by dsimp [M]; omega)
            _ = _ := (pow_two _).symm
        have hA' : A ≤ M ^ 5 := by
          calc
            _ = (X.p.T n * signatureConstant) * M * (2 * X.p.m n + 1) := by dsimp [A, M]; ac_rfl
            _ ≤ M ^ 2 * M * M ^ 2 := Nat.mul_le_mul (Nat.mul_le_mul_right _ hTD) h2
            _ = M ^ 5 := by ring
        have h5 : 1 ≤ M ^ 5 := Nat.one_le_pow _ _ (by omega)
        calc
          _ ≤ M ^ 5 + 1 := Nat.add_le_add_right hA' 1
          _ ≤ M ^ 5 * M := by
            calc
              _ ≤ M ^ 5 * 2 := by omega
              _ ≤ _ := Nat.mul_le_mul_left _ (by omega : 2 ≤ M)
          _ = _ := (pow_succ M 5).symm
      have hsmall : j + 1 ≤ M ^ 2 := by dsimp [M]; nlinarith
      have htwice : 2 * j + 1 ≤ M ^ 3 := by
        have h2 : 2 * j + 1 ≤ 3 * M := by dsimp [M]; omega
        have hMM : 3 ≤ M ^ 2 := by nlinarith
        calc
          _ ≤ 3 * M := h2
          _ ≤ M ^ 2 * M := Nat.mul_le_mul_right _ hMM
          _ = M ^ 3 := (pow_succ M 2).symm
      have hmask : (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
          1 + A * (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1) ≤ M ^ 6 * B := by
        dsimp only [B]
        split_ifs with hi
        · have hh : 1 + A * (X.poolIdx.card + 1) ^ X.p.usedBlocks n ≤
              (A + 1) * (X.poolIdx.card + 1) ^ X.p.usedBlocks n := by
            have : 1 ≤ (X.poolIdx.card + 1) ^ X.p.usedBlocks n := Nat.one_le_pow _ _ (by omega)
            nlinarith
          exact hh.trans (Nat.mul_le_mul_right _ hA)
        · simpa using Nat.one_le_pow 6 M (by omega : 0 < M)
      apply (grouped_record_card X ℓ t j).trans
      change ((j + 1) * M ^ j) *
        (2 ^ (X.p.T n * signatureConstant) * (2 * j + 1) * (A + 1) ^ (2 * j)) *
        (if ℓ.isLeft ∧ ℓ.level = X.p.J n then 1 + A * (X.poolIdx.card + 1) ^ X.p.usedBlocks n else 1) ≤ _
      calc
        _ ≤ (M ^ 2 * M ^ j) *
            (2 ^ (X.p.T n * signatureConstant) * M ^ 3 * (M ^ 6) ^ (2 * j)) * (M ^ 6 * B) := by gcongr
        _ = 2 ^ (X.p.T n * signatureConstant) * M ^ (13 * j + 11) * B := by
          rw [← pow_mul]
          calc
            _ = 2 ^ (X.p.T n * signatureConstant) *
                (M ^ 2 * M ^ j * M ^ 3 * M ^ (6 * (2 * j)) * M ^ 6) * B := by ac_rfl
            _ = _ := by
              have he : 2 + j + 3 + 6 * (2 * j) + 6 = 13 * j + 11 := by omega
              simp only [← pow_add, he]
        _ ≤ _ := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by omega : 0 < M)
          omega
  · have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    change R.card ≤ _
    simp [he]

end
end HypercubeRamsey.Lane_sol_s05_hist1b
