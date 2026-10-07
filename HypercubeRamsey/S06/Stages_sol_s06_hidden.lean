import HypercubeRamsey.S06.Steps
import HypercubeRamsey.S06.Stages_q_s06_stages

namespace HypercubeRamsey.Lane_sol_s06_hidden

open Classical HypercubeRamsey.S06 OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

theorem card_product_explicit {A B : Type*} (s : Finset A) (t : Finset B) :
    (s.product t).card = s.card * t.card := Finset.card_product s t

private theorem lowObservations6_cases {W : Type*} [Fintype W] {m : ℕ}
    (R : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m) (F : Finset (Fin m))
    (ℓ : HiddenKey6 W m) (hℓ : ℓ ∈ lowObservations6 R h t F) :
    (∃ k ∈ keyNeighborhood6 R h, (k, t) = ℓ) ∨
      ∃ i ∈ F, (h, Function.update t i (!t i)) = ℓ := by
  classical
  simpa only [lowObservations6, Finset.mem_union, Finset.mem_image] using hℓ

/-- The elementary product estimate used in the local-lemma charge check. -/
theorem one_sub_sum_le_product {I : Type*} [DecidableEq I]
    (s : Finset I) (x : I → ℝ) (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have h0 := hx0 i (Finset.mem_insert_self _ _)
      have h1 := hx1 i (Finset.mem_insert_self _ _)
      have hh := mul_le_mul_of_nonneg_left
        (ih (fun j hj => hx0 j (Finset.mem_insert_of_mem hj))
          (fun j hj => hx1 j (Finset.mem_insert_of_mem hj))) (sub_nonneg.mpr h1)
      have hs : 0 ≤ ∑ j ∈ s, x j :=
        Finset.sum_nonneg fun j hj => hx0 j (Finset.mem_insert_of_mem hj)
      nlinarith [mul_nonneg h0 hs]

/-- A probability and a total neighboring charge of at most half suffice. -/
theorem probability_le_charge_product {I : Type*} [DecidableEq I]
    (s : Finset I) (p x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hp : p ≤ x / 2) (hdegree : (s.card : ℝ) * x ≤ 1 / 2) :
    p ≤ x * ∏ _i ∈ s, (1 - x) := by
  have hh := one_sub_sum_le_product s (fun _ => x) (fun _ _ => hx0) (fun _ _ => hx1)
  have hsum : (∑ _i ∈ s, x) = (s.card : ℝ) * x := by simp
  rw [hsum] at hh
  have hhalf : (1 / 2 : ℝ) ≤ ∏ _i ∈ s, (1 - x) := by linarith
  exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hhalf hx0])

theorem card_biUnion_le_uniform {I A : Type*} [DecidableEq A]
    (s : Finset I) (f : I → Finset A) (C : ℕ) (hf : ∀ i ∈ s, (f i).card ≤ C) :
    (s.biUnion f).card ≤ s.card * C := by
  calc
    _ ≤ ∑ i ∈ s, (f i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, C := Finset.sum_le_sum hf
    _ = _ := by simp

theorem overlap_neighbors_card_le {I V : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq V] (scope : I → Finset V) (inverse : V → Finset I)
    (hinc : ∀ i v, v ∈ scope i → i ∈ inverse v) (C D : ℕ)
    (hscope : ∀ i, (scope i).card ≤ C) (hinverse : ∀ v, (inverse v).card ≤ D) (i : I) :
    (Finset.univ.filter fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)).card ≤ C * D := by
  have hsub : (Finset.univ.filter fun j => i ≠ j ∧ ¬ Disjoint (scope i) (scope j)) ⊆
      (scope i).biUnion inverse := by
    intro j hj
    have hdis := (Finset.mem_filter.mp hj).2.2
    obtain ⟨v, hvi, hvj⟩ := Finset.not_disjoint_iff.mp hdis
    exact Finset.mem_biUnion.mpr ⟨v, hvi, hinc j v hvj⟩
  exact (Finset.card_le_card hsub).trans
    ((card_biUnion_le_uniform (scope i) inverse D (fun v _ => hinverse v)).trans
      (Nat.mul_le_mul_right D (hscope i)))

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- A closed bin neighborhood, expressed through the already bounded key relation. -/
def closedBinNeighbors (w : X.Bin) : Finset X.Bin := X.binsOf (X.C (w, .boundary))

theorem mem_closedBinNeighbors (w u : X.Bin) :
    u ∈ closedBinNeighbors X w ↔ w = u ∨ binAdjacent6 w u := by
  constructor
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨h, hh, rfl⟩
    have ha : keyAdjacent6 binAdjacent6 (w, .boundary) h := (Finset.mem_filter.mp hh).2
    rcases ha with ha | ha | ha
    · exact Or.inl (congrArg Prod.fst ha)
    · exact Or.inl ha
    · exact Or.inr ha.2.2
  · intro hu
    apply Finset.mem_image.mpr
    refine ⟨(u, KeyFlag6.boundary), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rcases hu with hu | hu
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr ⟨rfl, rfl, hu⟩)

theorem closedBinNeighbors_symm (w u : X.Bin) (hu : u ∈ closedBinNeighbors X w) :
    w ∈ closedBinNeighbors X u := by
  rw [mem_closedBinNeighbors] at hu ⊢
  rcases hu with hu | ⟨i, heq, hdist⟩
  · exact Or.inl hu.symm
  · exact Or.inr ⟨i, fun j hj => (heq j hj).symm, by simpa [Nat.dist_comm] using hdist⟩

theorem closedBinNeighbors_card_le (w : X.Bin) : (closedBinNeighbors X w).card ≤ 602 :=
  Finset.card_image_le.trans (X.g.flips.key_neighborhood_card (w, .boundary))

/-- Three bin-neighborhood steps cover the parent, tag and posterior windows of an alarm. -/
def coarseBinScope (w : X.Bin) : Finset X.Bin :=
  (closedBinNeighbors X w).biUnion fun u =>
    (closedBinNeighbors X u).biUnion (closedBinNeighbors X)

theorem coarseBinScope_symm (w u : X.Bin) (hu : u ∈ coarseBinScope X w) :
    w ∈ coarseBinScope X u := by
  rcases Finset.mem_biUnion.mp hu with ⟨a, ha, hu⟩
  rcases Finset.mem_biUnion.mp hu with ⟨b, hb, hu⟩
  exact Finset.mem_biUnion.mpr ⟨b, closedBinNeighbors_symm X b u hu,
    Finset.mem_biUnion.mpr ⟨a, closedBinNeighbors_symm X a b hb,
      closedBinNeighbors_symm X w a ha⟩⟩

theorem coarseBinScope_card_le (w : X.Bin) : (coarseBinScope X w).card ≤ 602 ^ 3 := by
  have hinner : ∀ u : X.Bin,
      ((closedBinNeighbors X u).biUnion (closedBinNeighbors X)).card ≤ 602 * 602 := by
    intro u
    exact (card_biUnion_le_uniform _ _ 602 (fun a _ => closedBinNeighbors_card_le X a)).trans
      (Nat.mul_le_mul_right _ (closedBinNeighbors_card_le X u))
  exact (card_biUnion_le_uniform _ _ (602 * 602) (fun u _ => hinner u)).trans
    (by simpa [pow_succ, pow_two, Nat.mul_assoc] using
      Nat.mul_le_mul_right (602 * 602) (closedBinNeighbors_card_le X w))

theorem coarse_overlap_degree_le (w : X.Bin) :
    (Finset.univ.filter fun u => w ≠ u ∧
      ¬ Disjoint (coarseBinScope X w) (coarseBinScope X u)).card ≤ 602 ^ 6 := by
  have hh := overlap_neighbors_card_le (coarseBinScope X) (coarseBinScope X)
    (fun u v hv => coarseBinScope_symm X u v hv) (602 ^ 3) (602 ^ 3)
    (coarseBinScope_card_le X) (coarseBinScope_card_le X) w
  norm_num at hh ⊢
  exact hh

def binScopeTwo (w : X.Bin) : Finset X.Bin :=
  (closedBinNeighbors X w).biUnion (closedBinNeighbors X)

theorem binScopeTwo_card_le (w : X.Bin) : (binScopeTwo X w).card ≤ 602 ^ 2 := by
  exact (card_biUnion_le_uniform _ _ 602 (fun u _ => closedBinNeighbors_card_le X u)).trans
    (by simpa [pow_two] using Nat.mul_le_mul_right 602 (closedBinNeighbors_card_le X w))

theorem binScopeTwo_symm (w u : X.Bin) (hu : u ∈ binScopeTwo X w) : u ∈ binScopeTwo X w ∧
    w ∈ binScopeTwo X u := by
  refine ⟨hu, ?_⟩
  rcases Finset.mem_biUnion.mp hu with ⟨a, ha, hu⟩
  exact Finset.mem_biUnion.mpr ⟨a, closedBinNeighbors_symm X a u hu,
    closedBinNeighbors_symm X w a ha⟩

theorem self_mem_closedBinNeighbors (w : X.Bin) : w ∈ closedBinNeighbors X w :=
  (mem_closedBinNeighbors X w w).mpr (Or.inl rfl)

theorem closedBinNeighbors_subset_two (w : X.Bin) : closedBinNeighbors X w ⊆ binScopeTwo X w := by
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨w, self_mem_closedBinNeighbors X w, hu⟩

def closedSignNeighbors {m : ℕ} (t : CubeVertex m) : Finset (CubeVertex m) :=
  insert t (Finset.univ.image (flipVertex6 t))

theorem closedSignNeighbors_card_le {m : ℕ} (t : CubeVertex m) :
    (closedSignNeighbors t).card ≤ m + 1 := by
  have hh : (Finset.univ.image (flipVertex6 t)).card ≤ m := by
    simpa using (Finset.card_image_le (f := flipVertex6 t) (s := (Finset.univ : Finset (Fin m))))
  exact (Finset.card_insert_le _ _).trans (by omega)

theorem flipVertex6_twice {m : ℕ} (t : CubeVertex m) (i : Fin m) :
    flipVertex6 (flipVertex6 t i) i = t := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [flipVertex6]
  · simp [flipVertex6, Function.update_of_ne hji]

theorem closedSignNeighbors_symm {m : ℕ} (t s : CubeVertex m)
    (hs : s ∈ closedSignNeighbors t) : t ∈ closedSignNeighbors s := by
  rcases Finset.mem_insert.mp hs with hs | hs
  · subst s
    exact Finset.mem_insert_self _ _
  · rcases Finset.mem_image.mp hs with ⟨i, _, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ _, flipVertex6_twice t i⟩)

theorem sign_mem_of_agree_except {m : ℕ} (t s : CubeVertex m) (i : Fin m)
    (hs : ∀ j, j ≠ i → t j = s j) : s ∈ closedSignNeighbors t := by
  by_cases hi : t i = s i
  · have heq : t = s := by
      funext j
      by_cases hji : j = i
      · simpa [hji] using hi
      · exact hs j hji
    rw [← heq]
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp only [flipVertex6, Function.update_self]
      cases hti : t i <;> cases hsi : s i <;> simp_all
    · simpa [flipVertex6, Function.update_of_ne hji] using hs j hji

def signScopeTwo {m : ℕ} (t : CubeVertex m) : Finset (CubeVertex m) :=
  (closedSignNeighbors t).biUnion closedSignNeighbors

theorem signScopeTwo_card_le {m : ℕ} (t : CubeVertex m) : (signScopeTwo t).card ≤ (m + 1) ^ 2 := by
  exact (card_biUnion_le_uniform _ _ (m + 1) (fun u _ => closedSignNeighbors_card_le u)).trans
    (by simpa [pow_two] using Nat.mul_le_mul_right (m + 1) (closedSignNeighbors_card_le t))

theorem signScopeTwo_symm {m : ℕ} (t s : CubeVertex m) (hs : s ∈ signScopeTwo t) :
    t ∈ signScopeTwo s := by
  rcases Finset.mem_biUnion.mp hs with ⟨a, ha, hs⟩
  exact Finset.mem_biUnion.mpr ⟨a, closedSignNeighbors_symm a s hs,
    closedSignNeighbors_symm t a ha⟩

theorem closedSignNeighbors_subset_two {m : ℕ} (t : CubeVertex m) :
    closedSignNeighbors t ⊆ signScopeTwo t := by
  intro s hs
  exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_insert_self _ _, hs⟩

theorem key_neighbor_bin_close (h k : X.Key) (hk : k ∈ X.C h) :
    k.1 ∈ closedBinNeighbors X h.1 := by
  rw [mem_closedBinNeighbors]
  have ha : keyAdjacent6 binAdjacent6 h k := (Finset.mem_filter.mp hk).2
  rcases ha with ha | ha | ha
  · exact Or.inl (congrArg Prod.fst ha)
  · exact Or.inl ha
  · exact Or.inr ha.2.2

theorem makeType_observations_close (h : X.Key) (t : CubeVertex X.m)
    (F : Finset (Fin X.m)) (j : ℕ) (ℓ : X.HKey)
    (hℓ : ℓ ∈ (makeType6 binAdjacent6 h t F j X.J).obs) :
    ℓ.1.1 ∈ closedBinNeighbors X h.1 ∧ ℓ.2 ∈ closedSignNeighbors t := by
  letI : DecidableEq X.HKey := Classical.decEq _
  by_cases hj : j ≤ X.J
  · change ℓ ∈ (makeType6 binAdjacent6 h t F j X.J).obs at hℓ
    simp only [makeType6, if_pos hj, Type6.obs] at hℓ
    have hcases : (∃ k ∈ keyNeighborhood6 binAdjacent6 h, (k, t) = ℓ) ∨
        ∃ i ∈ F, (h, Function.update t i (!t i)) = ℓ :=
      lowObservations6_cases binAdjacent6 h t F ℓ hℓ
    rcases hcases with hℓ | hℓ
    · rcases hℓ with ⟨k, hk, rfl⟩
      exact ⟨key_neighbor_bin_close X h k hk, Finset.mem_insert_self _ _⟩
    · rcases hℓ with ⟨i, hi, rfl⟩
      exact ⟨self_mem_closedBinNeighbors X h.1,
        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  · simp only [makeType6, if_neg hj, Type6.obs, highObservations6] at hℓ
    split_ifs at hℓ with heq
    · have heqℓ : ℓ = (h, t) := Finset.mem_singleton.mp hℓ
      subst ℓ
      exact ⟨self_mem_closedBinNeighbors X h.1, Finset.mem_insert_self _ _⟩
    · exact False.elim (Finset.notMem_empty _ hℓ)

theorem edge_signs_close (u v : CubeVertex n) (h : (cube n).Adj u v) :
    X.g.L.sign v ∈ closedSignNeighbors (X.g.L.sign u) := by
  let S : Finset (Fin n) := Finset.univ.filter fun q => u q ≠ v q
  have hcard : S.card = 1 := by
    change _root_.hammingDist u v = 1 at h
    simpa [S, _root_.hammingDist] using h
  obtain ⟨q, hS⟩ := Finset.card_eq_one.mp hcard
  have hq : u q ≠ v q := (Finset.mem_filter.mp (by rw [hS]; simp : q ∈ S)).2
  have hother : ∀ a, a ≠ q → u a = v a := by
    intro a ha
    by_contra hne
    have hh : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have heq : a = q := by simpa [hS] using hh
    exact ha heq
  by_cases hf : ∃ i, q ∈ X.g.L.fineChunks i
  · obtain ⟨i, hi⟩ := hf
    exact sign_mem_of_agree_except _ _ i (X.g.flips.fine_flip_sign u v i h ⟨q, hi, hq⟩)
  · have hagree : ∀ i a, a ∈ X.g.L.fineChunks i → u a = v a := by
      intro i a ha
      by_cases haq : a = q
      · subst a
        exact False.elim (hf ⟨i, ha⟩)
      · exact hother a haq
    have heq := (X.g.flips.nonfine_flip_fine u v h hagree).1
    rw [← heq]
    exact Finset.mem_insert_self _ _

theorem neighbor_state_sign_close (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
    X.g.L.stSign a ∈ closedSignNeighbors (X.g.L.stSign b) := by
  have hwitness : ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
      X.g.L.stateOf u = b ∧ X.g.L.stateOf v = a ∧ (cube n).Adj u v := by
    simpa only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  rcases hwitness with ⟨u, v, _, _, hub, hva, huv⟩
  have hbu : X.g.L.stSign b = X.g.L.sign u := by rw [← hub]; exact X.facts.sign_eq u
  have hav : X.g.L.stSign a = X.g.L.sign v := by rw [← hva]; exact X.facts.sign_eq v
  rw [hbu, hav]
  exact edge_signs_close X u v huv

/-- A radius-two envelope for every hidden key read by a grouped stage-three event. -/
def hiddenGroupEnvelope (gr : X.Bin × CubeVertex X.m) : Finset X.HKey :=
  ((binScopeTwo X gr.1).product (Finset.univ : Finset KeyFlag6)).product (signScopeTwo gr.2)

theorem hiddenGroupEnvelope_card_le (gr : X.Bin × CubeVertex X.m) :
    (hiddenGroupEnvelope X gr).card ≤ 2 * 602 ^ 2 * (X.m + 1) ^ 2 := by
  have hflag : Fintype.card KeyFlag6 = 2 := by decide
  simp only [hiddenGroupEnvelope, card_product_explicit, Finset.card_univ, hflag]
  have hh := Nat.mul_le_mul (binScopeTwo_card_le X gr.1) (signScopeTwo_card_le gr.2)
  convert Nat.mul_le_mul_left 2 hh using 1 <;> ring <;> rfl

theorem bad3HiddenScope_subset_envelope (gr : X.Bin × CubeVertex X.m) :
    Lane_q_s06_stages.bad3HiddenScope X gr ⊆ hiddenGroupEnvelope X gr := by
  intro ℓ hℓ
  have hparts : ℓ.1.1 ∈ binScopeTwo X gr.1 ∧ ℓ.2 ∈ signScopeTwo gr.2 := by
    rcases (Finset.mem_filter.mp hℓ).2 with
      ⟨x, _, hw, ht, hobs⟩ | ⟨b, hb, hw, ht, D, hD, hobs⟩
    · have hh := makeType_observations_close X (X.g.L.key x) (X.g.L.sign x)
        (X.g.L.flippable x) (X.g.L.severity x) ℓ hobs
      exact ⟨closedBinNeighbors_subset_two X gr.1 (hw ▸ hh.1),
        closedSignNeighbors_subset_two gr.2 (ht ▸ hh.2)⟩
    · rcases Finset.mem_union.mp hobs with hobs | htarget
      · rcases Finset.mem_biUnion.mp hobs with ⟨e, he, hobs⟩
        rcases Finset.mem_image.mp hD with ⟨φ, hφ, hφD⟩
        have he' : e ∈ X.descOf b φ := hφD ▸ he
        rcases Finset.mem_image.mp he' with ⟨a, ha, hea⟩
        have haNbr := a.property
        have hkeyNear := key_neighbor_bin_close X (X.g.L.stKey b) (X.g.L.stKey a.1)
          (S06.Lane_q_s06_steps2.neighbor_key_severity6 X haNbr).1
        have hsignNear := neighbor_state_sign_close X b a.1 haNbr
        have hobs' : ℓ ∈ (X.stType a.1).obs := by rw [← hea] at hobs; exact hobs
        have hh := makeType_observations_close X (X.g.L.stKey a.1) (X.g.L.stSign a.1)
          (X.g.L.stFlippable a.1) (X.g.L.stSeverity a.1) ℓ hobs'
        refine ⟨Finset.mem_biUnion.mpr ⟨(X.g.L.stKey a.1).1, hw ▸ hkeyNear, hh.1⟩,
          Finset.mem_biUnion.mpr ⟨X.g.L.stSign a.1, ht ▸ hsignNear, hh.2⟩⟩
      · have heq : ℓ = X.tgt b := by
          split_ifs at htarget with hm
          · exact Finset.mem_singleton.mp htarget
          · exact False.elim (Finset.notMem_empty _ htarget)
        subst ℓ
        exact ⟨closedBinNeighbors_subset_two X gr.1
          (hw ▸ self_mem_closedBinNeighbors X (X.g.L.stKey b).1),
          closedSignNeighbors_subset_two gr.2 (ht ▸ Finset.mem_insert_self _ _)⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hparts.1, Finset.mem_univ _⟩, hparts.2⟩

def hiddenGroupsReading (ℓ : X.HKey) : Finset (X.Bin × CubeVertex X.m) :=
  (binScopeTwo X ℓ.1.1).product (signScopeTwo ℓ.2)

theorem hiddenGroupsReading_card_le (ℓ : X.HKey) :
    (hiddenGroupsReading X ℓ).card ≤ 602 ^ 2 * (X.m + 1) ^ 2 := by
  rw [hiddenGroupsReading, card_product_explicit]
  exact Nat.mul_le_mul (binScopeTwo_card_le X ℓ.1.1) (signScopeTwo_card_le ℓ.2)

theorem group_mem_readers (gr : X.Bin × CubeVertex X.m) (ℓ : X.HKey)
    (hℓ : ℓ ∈ Lane_q_s06_stages.bad3HiddenScope X gr) : gr ∈ hiddenGroupsReading X ℓ := by
  have hh := Finset.mem_product.mp (bad3HiddenScope_subset_envelope X gr hℓ)
  have hbin := (Finset.mem_product.mp hh.1).1
  exact Finset.mem_product.mpr ⟨(binScopeTwo_symm X gr.1 ℓ.1.1 hbin).2,
    signScopeTwo_symm gr.2 ℓ.2 hh.2⟩

theorem hidden_overlap_degree_le (gr : X.Bin × CubeVertex X.m) :
    (Finset.univ.filter fun gr' => gr ≠ gr' ∧ ¬ Disjoint
      (Lane_q_s06_stages.bad3HiddenScope X gr) (Lane_q_s06_stages.bad3HiddenScope X gr')).card ≤
        2 * 602 ^ 4 * (X.m + 1) ^ 4 := by
  have hscope : ∀ gr, (Lane_q_s06_stages.bad3HiddenScope X gr).card ≤
      2 * 602 ^ 2 * (X.m + 1) ^ 2 := fun gr =>
    (Finset.card_le_card (bad3HiddenScope_subset_envelope X gr)).trans (hiddenGroupEnvelope_card_le X gr)
  have hh := overlap_neighbors_card_le (Lane_q_s06_stages.bad3HiddenScope X) (hiddenGroupsReading X)
    (group_mem_readers X) (2 * 602 ^ 2 * (X.m + 1) ^ 2) (602 ^ 2 * (X.m + 1) ^ 2)
    hscope (hiddenGroupsReading_card_le X) gr
  convert hh using 1 <;> ring

/-- Each independent bin variable consists of its candidate and its two base tags. -/
abbrev BinSample := Fin N × (KeyFlag6 → X.ι)

/-- Repackage the coarse sample as one variable per bin. -/
def coarseBinEquiv : X.Coarse ≃ (X.Bin → BinSample X) where
  toFun c w := (c.1 w, fun f => c.2 (w, f))
  invFun z := (fun w => (z w).1, fun h => (z h.1).2 h.2)
  left_inv c := by
    apply Prod.ext <;> rfl
  right_inv z := by
    funext w
    rfl

/-- The law of the candidate and two tags at one bin, at fixed entering parent. -/
def binSampleLaw (v : Fin N) (w : X.Bin) : FinProb (BinSample X) :=
  FinProb.bind (X.candLaw v) fun a =>
    FinProb.pi fun f : KeyFlag6 => X.tagLawAt (v, fun _ => a) (w, f)

private theorem tagLawAt_local_bin (v : Fin N) (A : X.Bin → Fin N) (w : X.Bin)
    (f : KeyFlag6) :
    X.tagLawAt (v, A) (w, f) = X.tagLawAt (v, fun _ => A w) (w, f) := by
  cases f <;> rfl

/-- The hierarchical coarse law is exactly the product of bin-triple laws. -/
theorem coarseLaw_weight_eq_bin_product (v : Fin N) (c : X.Coarse) :
    (X.coarseLaw v).w c =
      (FinProb.pi (binSampleLaw X v)).w (coarseBinEquiv X c) := by
  change (∏ w, (X.candLaw v).w (c.1 w)) *
      (∏ h : X.Key, (X.tagLawAt (v, c.1) h).w (c.2 h)) =
    ∏ w, (X.candLaw v).w (c.1 w) *
      ∏ f : KeyFlag6, (X.tagLawAt (v, fun _ => c.1 w) (w, f)).w (c.2 (w, f))
  rw [Fintype.prod_prod_type]
  simp_rw [tagLawAt_local_bin]
  exact (Finset.prod_mul_distrib).symm

/-- Transfer any coarse expectation to the independent bin-triple product. -/
theorem coarseLaw_expect_eq_bin_product (v : Fin N) (F : X.Coarse → ℝ) :
    (X.coarseLaw v).expect F =
      (FinProb.pi (binSampleLaw X v)).expect
        (fun z => F ((coarseBinEquiv X).symm z)) := by
  unfold FinProb.expect
  apply Fintype.sum_equiv (coarseBinEquiv X)
  intro c
  rw [coarseLaw_weight_eq_bin_product]
  simp

/-- Transfer probabilities, including alarm events, to the bin product. -/
theorem coarseLaw_pr_eq_bin_product (v : Fin N) (A : X.Coarse → Prop) :
    (X.coarseLaw v).pr A =
      (FinProb.pi (binSampleLaw X v)).pr
        (fun z => A ((coarseBinEquiv X).symm z)) := by
  rw [Lane_q_s06_stages.finprob_pr_eq_expect_indicator,
    Lane_q_s06_stages.finprob_pr_eq_expect_indicator]
  exact coarseLaw_expect_eq_bin_product X v (fun c => if A c then 1 else 0)

/-- Disjoint bin scopes imply independence under the raw coarse law. -/
theorem coarseLaw_pr_and_of_disjoint (v : Fin N) (A B : X.Coarse → Prop)
    (s t : Finset X.Bin)
    (hA : FinProb.DependsOn (fun z => A ((coarseBinEquiv X).symm z)) s)
    (hB : FinProb.DependsOn (fun z => B ((coarseBinEquiv X).symm z)) t)
    (hst : Disjoint s t) :
    (X.coarseLaw v).pr (fun c => A c ∧ B c) =
      (X.coarseLaw v).pr A * (X.coarseLaw v).pr B := by
  simp_rw [coarseLaw_pr_eq_bin_product]
  exact Lane_q_s06_stages.pi_pr_and_of_disjoint_depends
    (binSampleLaw X v) _ _ s t hA hB hst

/-- The local mass factorization needed by a sparse coarse certificate. -/
theorem coarseLaw_local_mass_factor {I : Type*} [Fintype I] [DecidableEq I]
    (v : Fin N) (scope : I → Finset X.Bin) (A : I → Finset X.Coarse)
    (hdep : ∀ i, FinProb.DependsOn
      (fun z => (coarseBinEquiv X).symm z ∈ A i) (scope i))
    (i : I) (s : Finset I) (hremote : ∀ j ∈ s, Disjoint (scope i) (scope j)) :
    LocalLemma.mass (X.coarseLaw v).w (A i ∩ LocalLemma.avoid A s) =
      (X.coarseLaw v).pr (fun c => c ∈ A i) *
        LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid A s) := by
  let B : I → Finset (X.Bin → BinSample X) := fun j =>
    Finset.univ.filter fun z => (coarseBinEquiv X).symm z ∈ A j
  have hB : ∀ j, FinProb.DependsOn (fun z => z ∈ B j) (scope j) := by
    intro j z z' hz
    apply propext
    have heq := hdep j z z' hz
    simpa [B] using iff_of_eq heq
  have hf := Lane_q_s06_stages.pi_local_mass_factor (binSampleLaw X v)
    I scope B i s hB hremote
  have hmass (U : Finset X.Coarse) :
      LocalLemma.mass (X.coarseLaw v).w U =
        (FinProb.pi (binSampleLaw X v)).pr
          (fun z => (coarseBinEquiv X).symm z ∈ U) := by
    rw [Lane_q_s06_stages.finprob_pr_finset_mass]
    exact coarseLaw_pr_eq_bin_product X v _
  rw [hmass, hmass, coarseLaw_pr_eq_bin_product]
  rw [Lane_q_s06_stages.finprob_pr_finset_mass,
    Lane_q_s06_stages.finprob_pr_finset_mass] at hf
  have havoid : ∀ z, z ∈ LocalLemma.avoid B s ↔
      (coarseBinEquiv X).symm z ∈ LocalLemma.avoid A s := by
    intro z
    simp [LocalLemma.avoid, B]
  have hinter : ∀ z, z ∈ B i ∩ LocalLemma.avoid B s ↔
      (coarseBinEquiv X).symm z ∈ A i ∩ LocalLemma.avoid A s := by
    intro z
    simp only [Finset.mem_inter]
    rw [havoid]
    simp [B]
  have hEi : ∀ z, z ∈ B i ↔ (coarseBinEquiv X).symm z ∈ A i := by
    intro z
    simp [B]
  rw [Lane_q_s06_stages.pr_congr _ hinter,
    Lane_q_s06_stages.pr_congr _ hEi,
    Lane_q_s06_stages.pr_congr _ havoid] at hf
  exact hf

/-- Agreement on all three variables at each bin in a local window. -/
def BaseAgree (s : Finset X.Bin) (b b' : X.Base) : Prop :=
  b.1 = b'.1 ∧ (∀ w ∈ s, b.2.1 w = b'.2.1 w) ∧
    ∀ h : X.Key, h.1 ∈ s → b.2.2 h = b'.2.2 h

theorem baseAgree_withTag (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (h : X.Key) (i : X.ι) :
    BaseAgree X s (X.withTag b h i) (X.withTag b' h i) := by
  refine ⟨hb.1, hb.2.1, ?_⟩
  intro k hk
  by_cases hkh : k = h
  · simp [Ctx6.withTag, hkh]
  · simpa [Ctx6.withTag, Function.update_of_ne hkh] using hb.2.2 k hk

theorem tagLawAt_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (h : X.Key) (hh : h.1 ∈ s) :
    X.tagLawAt (X.parOf b) h = X.tagLawAt (X.parOf b') h := by
  cases hf : h.2 <;>
    simp [Ctx6.tagLawAt, Ctx6.parOf, primaryName6, otherPrimaryName6, Par6.val,
      hf, hb.1, hb.2.1 h.1 hh]

theorem hidPost_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (h : X.Key) (hh : X.binsOf (X.C h) ⊆ s) :
    X.hidPost b h = X.hidPost b' h := by
  unfold Ctx6.hidPost
  congr 1
  funext y
  apply S06.Lane_sol_s06_steps1.hidWeight_local X h _ (Finset.Subset.refl _) b b'
  · exact fun _ => hb.1
  · exact fun _ w hw => hb.2.1 w (hh hw)
  · intro k hk
    exact hb.2.2 k (hh (Finset.mem_image.mpr ⟨k, hk, rfl⟩))

theorem hidPostDel_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (h k : X.Key) (hh : X.binsOf (X.C h) ⊆ s) :
    X.hidPostDel b h k = X.hidPostDel b' h k := by
  unfold Ctx6.hidPostDel
  congr 1
  funext y
  apply S06.Lane_sol_s06_steps1.hidWeight_local X h _ (Finset.erase_subset _ _) b b'
  · exact fun _ => hb.1
  · exact fun _ w hw => hb.2.1 w (hh hw)
  · intro l hl
    exact hb.2.2 l (hh (Finset.mem_image.mpr ⟨l, Finset.mem_of_mem_erase hl, rfl⟩))

theorem step1OK_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (h : X.Key) (hh : X.binsOf (X.C h) ⊆ s) :
    X.Step1OK b h ↔ X.Step1OK b' h := by
  unfold Ctx6.Step1OK Ctx6.Step1Cap Ctx6.Step1Del
  rw [hidPost_eq_of_baseAgree X s b b' hb h hh]
  simp only [hidPostDel_eq_of_baseAgree X s b b' hb h _ hh]

/-- The bin variables read by a Step 2 test and its raw hidden-scalar probability. -/
def step2CoarseScope (β : X.Ty) : Finset X.Bin :=
  insert β.key.1 (β.obs.biUnion fun ℓ => X.binsOf (X.C ℓ.1))

theorem observation_bins_subset (β : X.Ty) (s : Finset X.Bin)
    (hscope : step2CoarseScope X β ⊆ s) (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
    X.binsOf (X.C ℓ.1) ⊆ s := by
  intro w hw
  exact hscope (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hw⟩))

theorem tagGate_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (i : X.ι) :
    X.tagGate b β i ↔ X.tagGate b' β i := by
  unfold Ctx6.tagGate
  have hpost : ∀ ℓ ∈ β.obs, X.hidPostRep b ℓ.1 β.key i = X.hidPostRep b' ℓ.1 β.key i := by
    intro ℓ hℓ
    exact hidPost_eq_of_baseAgree X s _ _ (baseAgree_withTag X s b b' hb β.key i)
      ℓ.1 (observation_bins_subset X β s hscope ℓ hℓ)
  have hdel : ∀ ℓ ∈ β.obs, X.hidPostDel b ℓ.1 β.key = X.hidPostDel b' ℓ.1 β.key := by
    intro ℓ hℓ
    exact hidPostDel_eq_of_baseAgree X s b b' hb ℓ.1 β.key
      (observation_bins_subset X β s hscope ℓ hℓ)
  constructor <;> intro h ℓ hℓ y
  · simpa only [← hpost ℓ hℓ, ← hdel ℓ hℓ] using h ℓ hℓ y
  · simpa only [hpost ℓ hℓ, hdel ℓ hℓ] using h ℓ hℓ y

theorem tagWeight_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s)
    (Z : X.Hid) (obs : Finset X.HKey) (hobs : obs ⊆ β.obs) (i : X.ι) :
    X.tagWeight (b, Z) β obs i = X.tagWeight (b', Z) β obs i := by
  have hkey : β.key.1 ∈ s := hscope (Finset.mem_insert_self _ _)
  have htag := tagLawAt_eq_of_baseAgree X s b b' hb β.key hkey
  have hgate := propext (tagGate_iff_of_baseAgree X s b b' hb β hscope i)
  have hprod : (∏ ℓ ∈ obs,
      safeRatio6 ((X.hidPostRep b ℓ.1 β.key i).w (Z ℓ)) ((X.hidPostDel b ℓ.1 β.key).w (Z ℓ))) =
      ∏ ℓ ∈ obs,
        safeRatio6 ((X.hidPostRep b' ℓ.1 β.key i).w (Z ℓ)) ((X.hidPostDel b' ℓ.1 β.key).w (Z ℓ)) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hS := observation_bins_subset X β s hscope ℓ (hobs hℓ)
    have hpost := hidPost_eq_of_baseAgree X s _ _ (baseAgree_withTag X s b b' hb β.key i) ℓ.1 hS
    have hdel := hidPostDel_eq_of_baseAgree X s b b' hb ℓ.1 β.key hS
    change (X.hidPostRep b ℓ.1 β.key i) = (X.hidPostRep b' ℓ.1 β.key i) at hpost
    rw [hpost, hdel]
  unfold Ctx6.tagWeight
  rw [htag, hgate, hprod]

theorem tagMass_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s)
    (Z : X.Hid) (obs : Finset X.HKey) (hobs : obs ⊆ β.obs) :
    X.tagMass (b, Z) β obs = X.tagMass (b', Z) β obs := by
  apply Finset.sum_congr rfl
  intro i hi
  exact tagWeight_eq_of_baseAgree X s b b' hb β hscope Z obs hobs i

theorem step2Tests_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (Z : X.Hid) :
    X.Step2Tests (b, Z) β ↔ X.Step2Tests (b', Z) β := by
  have hfull := tagMass_eq_of_baseAgree X s b b' hb β hscope Z β.obs (Finset.Subset.refl _)
  have hdel : ∀ ℓ, X.tagMass (b, Z) β (β.obs.erase ℓ) = X.tagMass (b', Z) β (β.obs.erase ℓ) :=
    fun ℓ => tagMass_eq_of_baseAgree X s b b' hb β hscope Z (β.obs.erase ℓ) (Finset.erase_subset _ _)
  unfold Ctx6.Step2Tests
  simp only [hfull, hdel]

theorem step2Fail_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (Z : X.Hid) :
    X.Step2Fail (b, Z) β ↔ X.Step2Fail (b', Z) β := by
  have hkey : β.key.1 ∈ s := hscope (Finset.mem_insert_self _ _)
  have hI := hb.2.2 β.key hkey
  unfold Ctx6.Step2Fail
  rw [hI]
  exact and_congr (tagGate_iff_of_baseAgree X s b b' hb β hscope _)
    (not_congr (step2Tests_iff_of_baseAgree X s b b' hb β hscope Z))

theorem pi_expect_eq_of_kernels_on_scope {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P Q : ∀ i, FinProb (Ω i)) (s : Finset I) (F : (∀ i, Ω i) → ℝ) (ω₀ : ∀ i, Ω i)
    (hF : FinProb.DependsOn F s) (hPQ : ∀ i ∈ s, P i = Q i) :
    (FinProb.pi P).expect F = (FinProb.pi Q).expect F := by
  have hsub : FinProb.pi (fun i : {i // i ∈ s} => P i.1) =
      FinProb.pi (fun i : {i // i ∈ s} => Q i.1) := by
    congr 1
    funext i
    exact hPQ i.1 i.2
  rw [FinProb.pi_expect_depends P s F ω₀ hF, FinProb.pi_expect_depends Q s F ω₀ hF, hsub]

set_option maxHeartbeats 400000 in
theorem step2_raw_rate_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) :
    (X.hidLaw b).pr (fun Z => X.Step2Fail (b, Z) β) =
      (X.hidLaw b').pr (fun Z => X.Step2Fail (b', Z) β) := by
  let P : X.HKey → Law N := fun ℓ => X.hidPost b ℓ.1
  let Q : X.HKey → Law N := fun ℓ => X.hidPost b' ℓ.1
  let A : X.Hid → Prop := fun Z => X.Step2Fail (b', Z) β
  have hA : FinProb.DependsOn A β.obs := by
    intro Z Z' hZ
    exact propext (Lane_q_s06_stages.step2Fail_iff_of_agree X b' β Z Z' hZ)
  have hPQ : ∀ ℓ ∈ β.obs, P ℓ = Q ℓ := by
    intro ℓ hℓ
    exact hidPost_eq_of_baseAgree X s b b' hb ℓ.1 (observation_bins_subset X β s hscope ℓ hℓ)
  calc
    _ = (X.hidLaw b).pr (fun Z => X.Step2Fail (b', Z) β) :=
      Lane_q_s06_stages.pr_congr _ (step2Fail_iff_of_baseAgree X s b b' hb β hscope)
    _ = _ := Lane_q_s06_stages.pi_pr_eq_of_kernel_eq_on_depends P Q β.obs A hA hPQ

/-- Count the possible fine-coordinate sets at a fixed low severity. -/
theorem bounded_subsets_card_le {A : Type*} [DecidableEq A]
    (s : Finset A) (j : ℕ) :
    (s.powerset.filter fun t => t.card ≤ j).card ≤
      (j + 1) * (s.card + 1) ^ j := by
  have hsub : (s.powerset.filter fun t => t.card ≤ j) ⊆
      (Finset.range (j + 1)).biUnion (fun r => s.powersetCard r) := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨hts, htj⟩
    exact Finset.mem_biUnion.mpr ⟨t.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hts, rfl⟩⟩
  calc
    (s.powerset.filter fun t => t.card ≤ j).card ≤
        ((Finset.range (j + 1)).biUnion fun r => s.powersetCard r).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.range (j + 1), (s.powersetCard r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range (j + 1), (s.card + 1) ^ j := by
      apply Finset.sum_le_sum
      intro r hr
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (by omega : s.card ≤ s.card + 1) r).trans
          (Nat.pow_le_pow_right (by omega : 0 < s.card + 1)
            (by have := Finset.mem_range.mp hr; omega)))
    _ = (j + 1) * (s.card + 1) ^ j := by simp

theorem bounded_subsets_card_le_pow {A : Type*} [DecidableEq A]
    (s : Finset A) (j : ℕ) (hj : j ≤ s.card) :
    (s.powerset.filter fun t => t.card ≤ j).card ≤ (s.card + 1) ^ (j + 1) := by
  calc
    _ ≤ (j + 1) * (s.card + 1) ^ j := bounded_subsets_card_le s j
    _ ≤ (s.card + 1) * (s.card + 1) ^ j := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [pow_succ]; ac_rfl

theorem flippable_card_le_severity (x : CubeVertex n) :
    (X.g.L.flippable x).card ≤ X.g.L.severity x := by
  apply Finset.card_le_card
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨hi, heq⟩
  exact Finset.mem_filter.mpr ⟨hi, by omega⟩

theorem severity_le_m (x : CubeVertex n) : X.g.L.severity x ≤ X.m := by
  exact (Finset.card_filter_le _ _).trans (by simp [Ctx6.m])

/-- The low types at one bin, central sign and severity, including both key flags. -/
def lowGroupPatterns (gr : X.Bin × CubeVertex X.m) (j : ℕ) : Finset X.Ty :=
  ((Finset.univ : Finset KeyFlag6).product
    ((Finset.univ : Finset (Fin X.m)).powerset.filter fun F => F.card ≤ j)).image
      (fun q => makeType6 binAdjacent6 (gr.1, q.1) gr.2 q.2 j X.J)

theorem lowGroupPatterns_card_le (gr : X.Bin × CubeVertex X.m) (j : ℕ) (hj : j ≤ X.m) :
    (lowGroupPatterns X gr j).card ≤ 2 * (X.m + 1) ^ (j + 1) := by
  have hflag : Fintype.card KeyFlag6 = 2 := by decide
  calc
    _ ≤ ((Finset.univ : Finset KeyFlag6).product
        ((Finset.univ : Finset (Fin X.m)).powerset.filter fun F => F.card ≤ j)).card :=
      Finset.card_image_le
    _ = 2 * ((Finset.univ : Finset (Fin X.m)).powerset.filter fun F => F.card ≤ j).card := by
      rw [card_product_explicit]
      simp [hflag]
    _ ≤ 2 * (X.m + 1) ^ (j + 1) := by
      apply Nat.mul_le_mul_left
      simpa using bounded_subsets_card_le_pow (Finset.univ : Finset (Fin X.m)) j
        (by simpa using hj)

theorem evenType_mem_lowGroupPatterns (gr : X.Bin × CubeVertex X.m)
    (x : CubeVertex n) (hbin : (X.g.L.key x).1 = gr.1) (hsign : X.g.L.sign x = gr.2) :
    X.evenType x ∈ lowGroupPatterns X gr (X.g.L.severity x) := by
  apply Finset.mem_image.mpr
  refine ⟨((X.g.L.key x).2, X.g.L.flippable x), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨?_, flippable_card_le_severity X x⟩⟩
    exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  · simp only [Ctx6.evenType, hsign]
    congr 1
    exact Prod.ext hbin.symm rfl

/-- High types at one bin and sign have an empty list or one optional scalar. -/
def highGroupPatterns (gr : X.Bin × CubeVertex X.m) : Finset X.Ty :=
  ((Finset.univ : Finset KeyFlag6).product (Finset.univ : Finset Bool)).image
    (fun q => ((gr.1, q.1), Mode6.high, 0,
      if q.2 then {((gr.1, q.1), gr.2)} else ∅))

theorem highGroupPatterns_card_le (gr : X.Bin × CubeVertex X.m) :
    (highGroupPatterns X gr).card ≤ 4 := by
  have hflag : Fintype.card KeyFlag6 = 2 := by decide
  exact (Finset.card_image_le).trans (by simp [card_product_explicit, hflag])

theorem evenType_mem_highGroupPatterns (gr : X.Bin × CubeVertex X.m)
    (x : CubeVertex n) (hbin : (X.g.L.key x).1 = gr.1) (hsign : X.g.L.sign x = gr.2)
    (hhigh : ¬ X.g.L.severity x ≤ X.J) :
    X.evenType x ∈ highGroupPatterns X gr := by
  rcases hkey : X.g.L.key x with ⟨w, f⟩
  have hw : w = gr.1 := by simpa only [hkey] using hbin
  apply Finset.mem_image.mpr
  refine ⟨(f, decide (X.g.L.severity x = X.J + 1)),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
  simp only [Ctx6.evenType, makeType6, if_neg hhigh, hkey, hw, hsign, highObservations6]
  by_cases h : X.g.L.severity x = X.J + 1 <;> simp [h] <;> rfl

def lowOccGroupTypes (gr : X.Bin × CubeVertex X.m) (j : ℕ) : Finset X.Ty :=
  ((Finset.univ : Finset (CubeVertex n)).filter fun x =>
    IsEvenRole x ∧ (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      X.g.L.severity x = j ∧ j ≤ X.J).image X.evenType

theorem lowOccGroupTypes_card_le (gr : X.Bin × CubeVertex X.m)
    (j : ℕ) (hj : j ≤ X.m) :
    (lowOccGroupTypes X gr j).card ≤ 2 * (X.m + 1) ^ (j + 1) := by
  apply (Finset.card_le_card (show lowOccGroupTypes X gr j ⊆ lowGroupPatterns X gr j from ?_)).trans
    (lowGroupPatterns_card_le X gr j hj)
  intro β hβ
  rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
  obtain ⟨_, hxbin, hxsign, hxj, _⟩ := (Finset.mem_filter.mp hx).2
  simpa only [hxj] using evenType_mem_lowGroupPatterns X gr x hxbin hxsign

theorem evenType_u_low (x : CubeVertex n) (hlow : X.g.L.severity x ≤ X.J) :
    (X.evenType x).u = X.g.L.severity x + 1 := by
  have hj : X.g.L.severity x ≤ X.g.L.m := severity_le_m X x
  simp [Ctx6.evenType, makeType6, hlow, Type6.u, Type6.mode, Type6.sev,
    sevFin6, min_eq_left hj]

theorem evenType_u_high (x : CubeVertex n) (hhigh : ¬ X.g.L.severity x ≤ X.J) :
    (X.evenType x).u = 1 := by
  simp [Ctx6.evenType, makeType6, hhigh, Type6.u, Type6.mode]

theorem pr_finite_union_le {I Ω : Type*} [DecidableEq I] [Fintype Ω]
    (P : FinProb Ω) (s : Finset I) (A : I → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, P.pr (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert i s hi ih =>
      have heq : ∀ ω, (∃ j ∈ insert i s, A j ω) ↔ A i ω ∨ ∃ j ∈ s, A j ω := by
        intro ω
        simp
      rw [Lane_q_s06_stages.pr_congr _ heq, Finset.sum_insert hi]
      exact (FinProb.pr_union _ _ _).trans (add_le_add le_rfl ih)

theorem pr_finite_union_le_card {I Ω : Type*} [DecidableEq I] [Fintype Ω]
    (P : FinProb Ω) (s : Finset I) (A : I → Ω → Prop) (r : ℝ)
    (h : ∀ i ∈ s, P.pr (A i) ≤ r) :
    P.pr (fun ω => ∃ i ∈ s, A i ω) ≤ (s.card : ℝ) * r := by
  calc
    _ ≤ ∑ i ∈ s, P.pr (A i) := pr_finite_union_le P s A
    _ ≤ ∑ _i ∈ s, r := Finset.sum_le_sum fun i hi => h i hi
    _ = _ := by simp

/-- Step 2 pattern union at fixed bin, central sign and low severity. -/
theorem low_group_failure_probability (base : X.Base)
    (gr : X.Bin × CubeVertex X.m) (j : ℕ) (hj : j ≤ X.m) (r : ℝ) (hr : 0 ≤ r)
    (hprob : ∀ x : CubeVertex n, IsEvenRole x → (X.g.L.key x).1 = gr.1 →
      X.g.L.sign x = gr.2 → X.g.L.severity x = j → j ≤ X.J →
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x)) ≤ r) :
    (X.hidLaw base).pr (fun Z => ∃ x : CubeVertex n, IsEvenRole x ∧
      (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      X.g.L.severity x = j ∧ j ≤ X.J ∧ X.Step2Fail (base, Z) (X.evenType x)) ≤
        (2 * (X.m + 1) ^ (j + 1) : ℕ) * r := by
  have heq : ∀ Z : X.Hid, (∃ x : CubeVertex n, IsEvenRole x ∧
      (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      X.g.L.severity x = j ∧ j ≤ X.J ∧ X.Step2Fail (base, Z) (X.evenType x)) ↔
      ∃ β ∈ lowOccGroupTypes X gr j, X.Step2Fail (base, Z) β := by
    intro Z
    constructor
    · rintro ⟨x, he, hw, ht, hsev, hlow, hf⟩
      exact ⟨X.evenType x, Finset.mem_image.mpr ⟨x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hw, ht, hsev, hlow⟩, rfl⟩, hf⟩
    · rintro ⟨β, hβ, hf⟩
      rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
      obtain ⟨he, hw, ht, hsev, hlow⟩ := (Finset.mem_filter.mp hx).2
      exact ⟨x, he, hw, ht, hsev, hlow, hf⟩
  rw [Lane_q_s06_stages.pr_congr _ heq]
  apply (pr_finite_union_le_card (X.hidLaw base) (lowOccGroupTypes X gr j)
    (fun β Z => X.Step2Fail (base, Z) β) r ?_).trans
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast lowOccGroupTypes_card_le X gr j hj) hr
  · intro β hβ
    rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
    obtain ⟨he, hw, ht, hsev, hlow⟩ := (Finset.mem_filter.mp hx).2
    exact hprob x he hw ht hsev hlow

/-- High Step 2 groups contain at most four distinct tests, including the interface option. -/
theorem high_group_failure_probability (base : X.Base)
    (gr : X.Bin × CubeVertex X.m) (r : ℝ) (hr : 0 ≤ r)
    (hprob : ∀ x : CubeVertex n, IsEvenRole x → (X.g.L.key x).1 = gr.1 →
      X.g.L.sign x = gr.2 → (¬ X.g.L.severity x ≤ X.J) →
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x)) ≤ r) :
    (X.hidLaw base).pr (fun Z => ∃ x : CubeVertex n, IsEvenRole x ∧
      (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      (¬ X.g.L.severity x ≤ X.J) ∧ X.Step2Fail (base, Z) (X.evenType x)) ≤ 4 * r := by
  let s : Finset X.Ty := ((Finset.univ : Finset (CubeVertex n)).filter fun x =>
    IsEvenRole x ∧ (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      ¬ X.g.L.severity x ≤ X.J).image X.evenType
  have hcard : s.card ≤ 4 := by
    apply (Finset.card_le_card (show s ⊆ highGroupPatterns X gr from ?_)).trans
      (highGroupPatterns_card_le X gr)
    intro β hβ
    rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
    obtain ⟨_, hw, ht, hhigh⟩ := (Finset.mem_filter.mp hx).2
    exact evenType_mem_highGroupPatterns X gr x hw ht hhigh
  have heq : ∀ Z : X.Hid, (∃ x : CubeVertex n, IsEvenRole x ∧
      (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      (¬ X.g.L.severity x ≤ X.J) ∧ X.Step2Fail (base, Z) (X.evenType x)) ↔
      ∃ β ∈ s, X.Step2Fail (base, Z) β := by
    intro Z
    constructor
    · rintro ⟨x, he, hw, ht, hhigh, hf⟩
      exact ⟨X.evenType x, Finset.mem_image.mpr ⟨x,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hw, ht, hhigh⟩, rfl⟩, hf⟩
    · rintro ⟨β, hβ, hf⟩
      rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
      obtain ⟨he, hw, ht, hhigh⟩ := (Finset.mem_filter.mp hx).2
      exact ⟨x, he, hw, ht, hhigh, hf⟩
  rw [Lane_q_s06_stages.pr_congr _ heq]
  apply (pr_finite_union_le_card (X.hidLaw base) s
    (fun β Z => X.Step2Fail (base, Z) β) r ?_).trans
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hr
  · intro β hβ
    rcases Finset.mem_image.mp hβ with ⟨x, hx, rfl⟩
    obtain ⟨he, hw, ht, hhigh⟩ := (Finset.mem_filter.mp hx).2
    exact hprob x he hw ht hhigh

theorem sum_powers_le_two (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (q : ℕ) :
    ∑ j ∈ Finset.range q, r ^ j ≤ 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ']
      simp_rw [pow_succ]
      rw [← Finset.sum_mul]
      have hh := mul_le_mul_of_nonneg_right ih hr0
      simp only [pow_zero]
      linarith

theorem sum_positive_powers_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2) (q : ℕ) :
    ∑ j ∈ Finset.range q, r ^ (j + 1) ≤ 2 * r := by
  simp_rw [pow_succ]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_powers_le_two r hr0 hr1 q) hr0

/-- The full Step 2 group union, with all low severities and the optional high list. -/
theorem step2_group_failure_probability (base : X.Base)
    (gr : X.Bin × CubeVertex X.m) (q : ℝ) (hq0 : 0 ≤ q)
    (hq1 : ((X.m : ℝ) + 1) * q ≤ 1 / 2)
    (hprob : ∀ x : CubeVertex n, IsEvenRole x → (X.g.L.key x).1 = gr.1 →
      X.g.L.sign x = gr.2 →
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x)) ≤
        q ^ (X.evenType x).u) :
    (X.hidLaw base).pr (fun Z => ∃ x : CubeVertex n, IsEvenRole x ∧
      (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      X.Step2Fail (base, Z) (X.evenType x)) ≤ 8 * ((X.m : ℝ) + 1) * q := by
  let A : ℕ → X.Hid → Prop := fun j Z => ∃ x : CubeVertex n, IsEvenRole x ∧
    (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
    X.g.L.severity x = j ∧ j ≤ X.J ∧ X.Step2Fail (base, Z) (X.evenType x)
  let B : X.Hid → Prop := fun Z => ∃ x : CubeVertex n, IsEvenRole x ∧
    (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
    (¬ X.g.L.severity x ≤ X.J) ∧ X.Step2Fail (base, Z) (X.evenType x)
  have hsub : ∀ Z : X.Hid, (∃ x : CubeVertex n, IsEvenRole x ∧
      (X.g.L.key x).1 = gr.1 ∧ X.g.L.sign x = gr.2 ∧
      X.Step2Fail (base, Z) (X.evenType x)) →
      (∃ j ∈ Finset.range (X.m + 1), A j Z) ∨ B Z := by
    rintro Z ⟨x, he, hw, ht, hf⟩
    by_cases hlow : X.g.L.severity x ≤ X.J
    · left
      refine ⟨X.g.L.severity x, Finset.mem_range.mpr ?_, x, he, hw, ht, rfl, hlow, hf⟩
      have := severity_le_m X x
      omega
    · exact Or.inr ⟨x, he, hw, ht, hlow, hf⟩
  have hlow : ∀ j ∈ Finset.range (X.m + 1),
      (X.hidLaw base).pr (A j) ≤ (2 * (X.m + 1) ^ (j + 1) : ℕ) * q ^ (j + 1) := by
    intro j hj
    apply low_group_failure_probability X base gr j (by have := Finset.mem_range.mp hj; omega)
      (q ^ (j + 1)) (pow_nonneg hq0 _)
    intro x he hw ht hsev hmode
    have hh := hprob x he hw ht
    have hu : (X.evenType x).u = j + 1 := by
      rw [evenType_u_low X x (hsev ▸ hmode), hsev]
    simpa only [hu] using hh
  have hhigh : (X.hidLaw base).pr B ≤ 4 * q := by
    apply high_group_failure_probability X base gr q hq0
    intro x he hw ht hh
    simpa only [evenType_u_high X x hh, pow_one] using hprob x he hw ht
  let r : ℝ := ((X.m : ℝ) + 1) * q
  have hr0 : 0 ≤ r := mul_nonneg (by positivity) hq0
  have hsum : (∑ j ∈ Finset.range (X.m + 1),
      (2 * (X.m + 1) ^ (j + 1) : ℕ) * q ^ (j + 1)) ≤ 4 * r := by
    have heq : (∑ j ∈ Finset.range (X.m + 1),
        (2 * (X.m + 1) ^ (j + 1) : ℕ) * q ^ (j + 1)) =
        2 * ∑ j ∈ Finset.range (X.m + 1), r ^ (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [r, mul_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
        Nat.cast_ofNat]
      ring
    rw [heq]
    have hh := sum_positive_powers_le r hr0 hq1 (X.m + 1)
    linarith
  have hqr : q ≤ r := by
    dsimp [r]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ X.m by positivity) hq0]
  calc
    _ ≤ (X.hidLaw base).pr (fun Z => (∃ j ∈ Finset.range (X.m + 1), A j Z) ∨ B Z) :=
      Lane_q_s06_stages.pr_mono _ hsub
    _ ≤ (X.hidLaw base).pr (fun Z => ∃ j ∈ Finset.range (X.m + 1), A j Z) +
        (X.hidLaw base).pr B := FinProb.pr_union _ _ _
    _ ≤ (∑ j ∈ Finset.range (X.m + 1), (X.hidLaw base).pr (A j)) + 4 * q :=
      add_le_add (pr_finite_union_le _ _ _) hhigh
    _ ≤ (∑ j ∈ Finset.range (X.m + 1),
        (2 * (X.m + 1) ^ (j + 1) : ℕ) * q ^ (j + 1)) + 4 * q :=
      add_le_add (Finset.sum_le_sum hlow) le_rfl
    _ ≤ 8 * ((X.m : ℝ) + 1) * q := by dsimp [r] at hsum hqr; linarith

open Filter in
/-- Step 2 uses at most a quarter of the hidden-stage charge, eventually. -/
theorem eventually_step2_group_charge_budget (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∀ᶠ n : ℕ in atTop,
      8 * ((m₆ p₀ n : ℝ) + 1) * (n : ℝ) ^ (-(δ₂ / 8)) ≤
        (n : ℝ) ^ (-(δ₂ / 128)) / 4 := by
  have hα : 0 < α₆ p₀ := lt_min (by norm_num) (by linarith)
  have hαle : α₆ p₀ ≤ 1 / 10 ^ 12 := min_le_left _ _
  let a : ℝ := δ₂ / 8 - δ₂ / 128 - 2 * α₆ p₀
  have ha : 0 < a := by dsimp [a]; norm_num [δ₂] at *; linarith
  have htail := Lane_q_s06_stages.eventually_const_mul_nat_rpow_neg_lt
    (c := 32) ha (by norm_num : (0 : ℝ) < 1)
  have hceil := Lane_q_s06_stages.eventually_nat_ceil_rpow_add_two_le_double hα
  filter_upwards [htail, hceil, Filter.eventually_ge_atTop 2] with n hsmall hscale hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm : (m₆ p₀ n : ℝ) + 1 ≤ (n : ℝ) ^ (2 * α₆ p₀) := by
    dsimp [m₆]
    linarith
  have hpow : (n : ℝ) ^ (2 * α₆ p₀) * (n : ℝ) ^ (-(δ₂ / 8)) =
      (n : ℝ) ^ (-a) * (n : ℝ) ^ (-(δ₂ / 128)) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1
    dsimp [a]
    ring
  have hx : 0 ≤ (n : ℝ) ^ (-(δ₂ / 128)) := Real.rpow_nonneg hn0.le _
  calc
    _ ≤ 8 * (n : ℝ) ^ (2 * α₆ p₀) * (n : ℝ) ^ (-(δ₂ / 8)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num))
        (Real.rpow_nonneg hn0.le _)
    _ = (8 * (n : ℝ) ^ (-a)) * (n : ℝ) ^ (-(δ₂ / 128)) := by
      rw [mul_assoc, hpow, ← mul_assoc]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (show 8 * (n : ℝ) ^ (-a) ≤ 1 / 4 by linarith) hx]

open Filter in
theorem eventually_coarse_degree_charge_budget :
    ∀ᶠ n : ℕ in atTop,
      (602 ^ 6 : ℝ) * (n : ℝ) ^ (-(δ₁ / 8)) ≤ 1 / 2 := by
  have hh := Lane_q_s06_stages.eventually_const_mul_nat_rpow_neg_lt
    (c := (602 ^ 6 : ℝ)) (by norm_num [δ₁] : (0 : ℝ) < δ₁ / 8)
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hh] with n hn
  exact hn.le

open Filter in
theorem eventually_hidden_degree_charge_budget (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∀ᶠ n : ℕ in atTop,
      2 * 602 ^ 4 * ((m₆ p₀ n : ℝ) + 1) ^ 4 * (n : ℝ) ^ (-(δ₂ / 128)) ≤ 1 / 2 := by
  have hα : 0 < α₆ p₀ := lt_min (by norm_num) (by linarith)
  have hαle : α₆ p₀ ≤ 1 / 10 ^ 12 := min_le_left _ _
  let a : ℝ := δ₂ / 128 - 8 * α₆ p₀
  have ha : 0 < a := by dsimp [a]; norm_num [δ₂] at *; linarith
  have htail := Lane_q_s06_stages.eventually_const_mul_nat_rpow_neg_lt
    (c := 2 * 602 ^ 4) ha (by norm_num : (0 : ℝ) < 1 / 2)
  have hceil := Lane_q_s06_stages.eventually_nat_ceil_rpow_add_two_le_double hα
  filter_upwards [htail, hceil, Filter.eventually_ge_atTop 2] with n hsmall hscale hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hm : (m₆ p₀ n : ℝ) + 1 ≤ (n : ℝ) ^ (2 * α₆ p₀) := by dsimp [m₆]; linarith
  have hm4 : ((m₆ p₀ n : ℝ) + 1) ^ 4 ≤ ((n : ℝ) ^ (2 * α₆ p₀)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hm _
  have hpow : ((n : ℝ) ^ (2 * α₆ p₀)) ^ 4 * (n : ℝ) ^ (-(δ₂ / 128)) =
      (n : ℝ) ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    dsimp [a]
    norm_num
    ring
  calc
    _ ≤ 2 * 602 ^ 4 * ((n : ℝ) ^ (2 * α₆ p₀)) ^ 4 * (n : ℝ) ^ (-(δ₂ / 128)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm4 (by positivity))
        (Real.rpow_nonneg hn0.le _)
    _ = 2 * 602 ^ 4 * (n : ℝ) ^ (-a) := by rw [mul_assoc, hpow]
    _ ≤ _ := hsmall.le

/-- A complete graph gives a charge product over every other index. -/
theorem complete_neighbor_product {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (x : ℝ) :
    (∏ _j ∈ Finset.univ.filter (fun j : I => i ≠ j), (1 - x)) =
      (1 - x) ^ (Fintype.card I - 1) := by
  have heq : Finset.univ.filter (fun j : I => i ≠ j) = Finset.univ.erase i := by
    ext j
    simp [ne_comm]
  rw [heq, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
  rfl

theorem complete_remote_set_empty {I : Type*} [DecidableEq I]
    (i : I) (s : Finset I) (hi : i ∉ s) (hremote : ∀ j ∈ s, ¬ i ≠ j) : s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hij : i = j := not_ne_iff.mp (hremote j hj)
  exact hi (hij ▸ hj)

/-- The exact bound imposed by the previous complete-adjacency certificate shell. -/
theorem complete_local_bound_iff {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I] (P : FinProb Ω) (A : I → Finset Ω) (x : ℝ) :
    (∀ i (s : Finset I), i ∉ s → (∀ j ∈ s, ¬ i ≠ j) →
      LocalLemma.mass P.w (A i ∩ LocalLemma.avoid A s) ≤
        (x * ∏ _j ∈ Finset.univ.filter (fun j : I => i ≠ j), (1 - x)) *
          LocalLemma.mass P.w (LocalLemma.avoid A s)) ↔
      ∀ i, P.pr (fun ω => ω ∈ A i) ≤ x * (1 - x) ^ (Fintype.card I - 1) := by
  have hmass : LocalLemma.mass P.w (Finset.univ : Finset Ω) = 1 := P.sum_eq_one
  constructor
  · intro h i
    have hh := h i ∅ (by simp) (by simp)
    simp only [LocalLemma.avoid, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, Finset.filter_true_of_mem, Finset.inter_univ] at hh
    rw [hmass, mul_one, complete_neighbor_product,
      Lane_q_s06_stages.finprob_pr_finset_mass] at hh
    exact hh
  · intro h i s hi hr
    have hs := complete_remote_set_empty i s hi hr
    subst s
    simp only [LocalLemma.avoid, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, Finset.filter_true_of_mem, Finset.inter_univ]
    rw [hmass, mul_one, complete_neighbor_product,
      Lane_q_s06_stages.finprob_pr_finset_mass]
    exact h i

end
end HypercubeRamsey.Lane_sol_s06_hidden
