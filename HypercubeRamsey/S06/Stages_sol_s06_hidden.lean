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

private theorem reqNames6_cases {W : Type*} {m : ℕ} (β : Type6 W m) (nm : VarName6 W m)
    (hnm : nm ∈ reqNames6 β) :
    nm = .par (primaryName6 β.key) ∨ (∃ ℓ ∈ β.obs, VarName6.hid ℓ = nm) ∨
      (β.mode = .high ∧ nm = .par (otherPrimaryName6 β.key)) := by
  classical
  rcases Finset.mem_union.mp hnm with hnm | hnm
  · rcases Finset.mem_insert.mp hnm with hnm | hnm
    · exact Or.inl hnm
    · exact Or.inr (Or.inl (Finset.mem_image.mp hnm))
  · split_ifs at hnm with hm
    · exact Or.inr (Or.inr ⟨hm, Finset.mem_singleton.mp hnm⟩)
    · exact False.elim (Finset.notMem_empty _ hnm)

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

theorem binScopeTwo_subset_three (w : X.Bin) : binScopeTwo X w ⊆ coarseBinScope X w := by
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨w, self_mem_closedBinNeighbors X w, hu⟩

theorem closedBinNeighbors_subset_three (w : X.Bin) :
    closedBinNeighbors X w ⊆ coarseBinScope X w :=
  (closedBinNeighbors_subset_two X w).trans (binScopeTwo_subset_three X w)

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

def flippableNeighbors {m : ℕ} (F : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  insert F ((Finset.univ.image fun i => insert i F) ∪ (Finset.univ.image fun i => F.erase i))

theorem flippableNeighbors_card_le {m : ℕ} (F : Finset (Fin m)) :
    (flippableNeighbors F).card ≤ 2 * m + 1 := by
  have hins : (Finset.univ.image fun i : Fin m => insert i F).card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun i => insert i F))
  have hera : (Finset.univ.image fun i : Fin m => F.erase i).card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun i => F.erase i))
  have hunion := Finset.card_union_le (Finset.univ.image fun i : Fin m => insert i F)
    (Finset.univ.image fun i : Fin m => F.erase i)
  have houter := Finset.card_insert_le F
    ((Finset.univ.image fun i : Fin m => insert i F) ∪ (Finset.univ.image fun i : Fin m => F.erase i))
  dsimp [flippableNeighbors]
  omega

theorem flippable_mem_of_agree_except {m : ℕ} (F F' : Finset (Fin m)) (i : Fin m)
    (h : ∀ j, j ≠ i → (j ∈ F ↔ j ∈ F')) : F' ∈ flippableNeighbors F := by
  by_cases hi : i ∈ F
  · by_cases hi' : i ∈ F'
    · have heq : F = F' := by
        ext j
        by_cases hji : j = i
        · simp [hji, hi, hi']
        · exact h j hji
      rw [← heq]
      exact Finset.mem_insert_self _ _
    · have heq : F.erase i = F' := by
        ext j
        by_cases hji : j = i
        · simp [hji, hi']
        · simpa [hji] using h j hji
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩))
  · by_cases hi' : i ∈ F'
    · have heq : insert i F = F' := by
        ext j
        by_cases hji : j = i
        · simp [hji, hi']
        · simpa [hji] using h j hji
      exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩))
    · have heq : F = F' := by
        ext j
        by_cases hji : j = i
        · simp [hji, hi, hi']
        · exact h j hji
      rw [← heq]
      exact Finset.mem_insert_self _ _

theorem edge_flippable_close (u v : CubeVertex n) (h : (cube n).Adj u v) :
    X.g.L.flippable v ∈ flippableNeighbors (X.g.L.flippable u) := by
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
    apply flippable_mem_of_agree_except _ _ i
    intro j hj
    have hcount : X.g.L.fineCount u j = X.g.L.fineCount v j := by
      unfold ChunkLayout6.fineCount
      congr 1
      ext a
      by_cases ha : a ∈ X.g.L.fineChunks j
      · have haq : a ≠ q := by
          intro heq
          subst a
          exact (Finset.disjoint_left.mp (X.g.L.chunks_disjoint.2.2.1 i j hj.symm)) hi ha
        simp only [Finset.mem_filter]
        rw [hother a haq]
      · simp [ha]
    simp only [ChunkLayout6.flippable, Finset.mem_filter, Finset.mem_univ, true_and, hcount]
  · have hagree : ∀ i a, a ∈ X.g.L.fineChunks i → u a = v a := by
      intro i a ha
      by_cases haq : a = q
      · subst a
        exact False.elim (hf ⟨i, ha⟩)
      · exact hother a haq
    have heq := (X.g.flips.nonfine_flip_fine u v h hagree).2.1
    rw [← heq]
    exact Finset.mem_insert_self _ _

theorem neighbor_state_flippable_close (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
    X.g.L.stFlippable a ∈ flippableNeighbors (X.g.L.stFlippable b) := by
  have hwitness : ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
      X.g.L.stateOf u = b ∧ X.g.L.stateOf v = a ∧ (cube n).Adj u v := by
    simpa only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  rcases hwitness with ⟨u, v, _, _, hub, hva, huv⟩
  have hbu : X.g.L.stFlippable b = X.g.L.flippable u := by rw [← hub]; exact X.facts.flippable_eq u
  have hav : X.g.L.stFlippable a = X.g.L.flippable v := by rw [← hva]; exact X.facts.flippable_eq v
  rw [hbu, hav]
  exact edge_flippable_close X u v huv

def neighborTypeUniverse (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ) : Finset X.Ty :=
  (X.C h).biUnion fun k => (closedSignNeighbors t).biUnion fun s =>
    (flippableNeighbors F).biUnion fun F' =>
      ({j - 1, j, j + 1} : Finset ℕ).image fun j' => makeType6 binAdjacent6 k s F' j' X.J

set_option maxHeartbeats 400000 in
theorem neighborTypeUniverse_card_le (h : X.Key) (t : CubeVertex X.m)
    (F : Finset (Fin X.m)) (j : ℕ) :
    (neighborTypeUniverse X h t F j).card ≤ 4000 * (X.m + 1) ^ 2 := by
  have hsev : ({j - 1, j, j + 1} : Finset ℕ).card ≤ 3 := by
    have h1 := Finset.card_insert_le (j - 1) ({j, j + 1} : Finset ℕ)
    have h2 := Finset.card_insert_le j ({j + 1} : Finset ℕ)
    simp only [Finset.card_singleton] at h2
    omega
  let U (k : X.Key) (s : CubeVertex X.m) (F' : Finset (Fin X.m)) : Finset X.Ty :=
    ({j - 1, j, j + 1} : Finset ℕ).image fun j' => (makeType6 binAdjacent6 k s F' j' X.J : X.Ty)
  let V (k : X.Key) (s : CubeVertex X.m) : Finset X.Ty := (flippableNeighbors F).biUnion (U k s)
  let W (k : X.Key) : Finset X.Ty := (closedSignNeighbors t).biUnion (V k)
  have hinner : ∀ k s F', (U k s F').card ≤ 3 := by
    intro k s F'
    exact Finset.card_image_le.trans hsev
  have hF : ∀ k s, (V k s).card ≤ (2 * X.m + 1) * 3 := by
    intro k s
    exact (card_biUnion_le_uniform (flippableNeighbors F) (U k s) 3 (fun F' _ => hinner k s F')).trans
      (Nat.mul_le_mul_right 3 (flippableNeighbors_card_le F))
  have hsign : ∀ k, (W k).card ≤ (X.m + 1) * ((2 * X.m + 1) * 3) := by
    intro k
    exact (card_biUnion_le_uniform (closedSignNeighbors t) (V k) _ (fun s _ => hF k s)).trans
      (Nat.mul_le_mul_right _ (closedSignNeighbors_card_le t))
  have houter := (card_biUnion_le_uniform (X.C h) W _ (fun k _ => hsign k)).trans
    (Nat.mul_le_mul_right _ (X.g.flips.key_neighborhood_card h))
  have houter' : (neighborTypeUniverse X h t F j).card ≤ 602 * ((X.m + 1) * ((2 * X.m + 1) * 3)) := by
    simpa only [neighborTypeUniverse, W, V, U] using houter
  apply houter'.trans
  nlinarith

theorem neighbor_type_mem_universe (b a : X.State) (ha : a ∈ X.g.L.stNbr b) :
    X.stType a ∈ neighborTypeUniverse X (X.g.L.stKey b) (X.g.L.stSign b)
      (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by
  have hks := S06.Lane_q_s06_steps2.neighbor_key_severity6 X ha
  have hsev : X.g.L.stSeverity a ∈
      ({X.g.L.stSeverity b - 1, X.g.L.stSeverity b, X.g.L.stSeverity b + 1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hh := hks.2
    unfold Nat.dist at hh
    omega
  exact Finset.mem_biUnion.mpr ⟨X.g.L.stKey a, hks.1,
    Finset.mem_biUnion.mpr ⟨X.g.L.stSign a, neighbor_state_sign_close X b a ha,
      Finset.mem_biUnion.mpr ⟨X.g.L.stFlippable a, neighbor_state_flippable_close X b a ha,
        Finset.mem_image.mpr ⟨X.g.L.stSeverity a, hsev, rfl⟩⟩⟩⟩

def genericNeighborTypes (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ) : Finset X.Ty :=
  (X.C h).biUnion fun k =>
    ({j - 1, j, j + 1} : Finset ℕ).image fun j' => makeType6 binAdjacent6 k t F j' X.J

theorem genericNeighborTypes_eq_forms (b : X.State) :
    genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b) (X.g.L.stFlippable b) (X.g.L.stSeverity b) =
      S06.Lane_q_s06_steps2.neighborTypeForms6 X b := rfl

theorem genericNeighborTypes_card_le (h : X.Key) (t : CubeVertex X.m)
    (F : Finset (Fin X.m)) (j : ℕ) : (genericNeighborTypes X h t F j).card ≤ 1806 := by
  have hsev : ({j - 1, j, j + 1} : Finset ℕ).card ≤ 3 := by
    have h1 := Finset.card_insert_le (j - 1) ({j, j + 1} : Finset ℕ)
    have h2 := Finset.card_insert_le j ({j + 1} : Finset ℕ)
    simp only [Finset.card_singleton] at h2
    omega
  let f (k : X.Key) : Finset X.Ty :=
    ({j - 1, j, j + 1} : Finset ℕ).image fun j' => (makeType6 binAdjacent6 k t F j' X.J : X.Ty)
  have hf : ∀ k ∈ X.C h, (f k).card ≤ 3 := by
    intro k hk
    exact Finset.card_image_le.trans hsev
  have hh := (card_biUnion_le_uniform (X.C h) f 3 hf).trans
      (Nat.mul_le_mul_right 3 (X.g.flips.key_neighborhood_card h))
  simpa only [genericNeighborTypes, f, Nat.reduceMul] using hh

def exceptionalNeighborStates (b : X.State) : Finset (X.g.L.stNbr b) :=
  (Finset.univ.filter fun a => X.stMode a.1 ≠ X.stMode b) ∪
    (Finset.univ.filter fun a => (X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
      (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨ X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b))

theorem exceptionalNeighborStates_card_le (b : X.State) (hb : b ∈ X.g.L.oddStates) (hn : 4 ≤ n) :
    (exceptionalNeighborStates X b).card ≤ 1 + 21 * (X.J + 2) :=
  S06.Lane_q_s06_steps2.descriptorBadStates6_card X b hb hn

theorem neighbor_type_generic_or_exceptional (b : X.State) (a : X.g.L.stNbr b) :
    X.stType a.1 ∈ genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b)
      (X.g.L.stFlippable b) (X.g.L.stSeverity b) ∨ a ∈ exceptionalNeighborStates X b := by
  rw [genericNeighborTypes_eq_forms]
  by_cases hmode : X.stMode a.1 = X.stMode b
  · by_cases hsame : X.g.L.stSign a.1 = X.g.L.stSign b ∧ X.g.L.stFlippable a.1 = X.g.L.stFlippable b
    · exact Or.inl (S06.Lane_q_s06_steps2.neighbor_type_mem_forms6 X a.property hsame.1 hsame.2)
    · by_cases hrel : X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1
      · have hdiff : X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨ X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b := by
          by_cases hs : X.g.L.stSign a.1 = X.g.L.stSign b
          · right
            intro hf
            exact hsame ⟨hs, hf⟩
          · exact Or.inl hs
        exact Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrel, hdiff⟩))
      · have hhigh : X.stMode b = .high := by
          cases hm : X.stMode b
          · exact False.elim (hrel (Or.inl hm))
          · rfl
        have hfar : X.g.L.stSeverity a.1 ≠ X.J + 1 := fun h => hrel (Or.inr h)
        exact Or.inl (S06.Lane_q_s06_steps2.neighbor_type_mem_forms_high6 X a.property
          (hmode.trans hhigh) hfar)
  · exact Or.inr (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmode⟩))

def genericDescriptorPart (b : X.State) (D : Finset (Fin X.T × X.Ty)) : Finset (Fin X.T × X.Ty) :=
  D.filter fun e => e.2 ∈ genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b)
    (X.g.L.stFlippable b) (X.g.L.stSeverity b)

def exceptionalDescriptorPart (b : X.State) (D : Finset (Fin X.T × X.Ty)) : Finset (Fin X.T × X.Ty) :=
  D.filter fun e => e.2 ∉ genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b)
    (X.g.L.stFlippable b) (X.g.L.stSeverity b)

theorem descriptorParts_union (b : X.State) (D : Finset (Fin X.T × X.Ty)) :
    genericDescriptorPart X b D ∪ exceptionalDescriptorPart X b D = D := by
  ext e
  by_cases h : e.2 ∈ genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b)
    (X.g.L.stFlippable b) (X.g.L.stSeverity b) <;>
    simp [genericDescriptorPart, exceptionalDescriptorPart, h]

theorem genericDescriptorPart_subset (b : X.State) (D : Finset (Fin X.T × X.Ty)) :
    genericDescriptorPart X b D ⊆ (Finset.univ : Finset (Fin X.T)).product
      (genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b) (X.g.L.stFlippable b) (X.g.L.stSeverity b)) := by
  intro e he
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩

theorem descriptor_subset_universe (b : X.State) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs b) :
    D ⊆ (Finset.univ : Finset (Fin X.T)).product
      (neighborTypeUniverse X (X.g.L.stKey b) (X.g.L.stSign b) (X.g.L.stFlippable b) (X.g.L.stSeverity b)) := by
  intro e he
  rcases Finset.mem_image.mp hD with ⟨φ, hφ, hφD⟩
  have he' : e ∈ X.descOf b φ := by rw [hφD]; exact he
  rcases Finset.mem_image.mp he' with ⟨a, ha, hea⟩
  rw [← hea]
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, neighbor_type_mem_universe X b a.1 a.property⟩

theorem exceptionalDescriptorPart_card_le (b : X.State) (hb : b ∈ X.g.L.oddStates) (hn : 4 ≤ n)
    (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs b) :
    (exceptionalDescriptorPart X b D).card ≤ 1 + 21 * (X.J + 2) := by
  rcases Finset.mem_image.mp hD with ⟨φ, hφ, hφD⟩
  have hsub : exceptionalDescriptorPart X b D ⊆
      (exceptionalNeighborStates X b).image (fun a => (φ a, X.stType a.1)) := by
    intro e he
    obtain ⟨heD, heNot⟩ := Finset.mem_filter.mp he
    have he' : e ∈ X.descOf b φ := by rw [hφD]; exact heD
    rcases Finset.mem_image.mp he' with ⟨a, ha, hea⟩
    have hbad : a ∈ exceptionalNeighborStates X b := by
      rcases neighbor_type_generic_or_exceptional X b a with hgen | hbad
      · have hgen' : e.2 ∈ genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b)
          (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by rw [← hea]; exact hgen
        exact False.elim (heNot hgen')
      · exact hbad
    exact Finset.mem_image.mpr ⟨a, hbad, hea⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (exceptionalNeighborStates_card_le X b hb hn))

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

theorem baseAgree_of_binSamples (s : Finset X.Bin) (v : Fin N)
    (z z' : X.Bin → BinSample X) (hz : ∀ w ∈ s, z w = z' w) :
    BaseAgree X s (v, (coarseBinEquiv X).symm z) (v, (coarseBinEquiv X).symm z') := by
  refine ⟨rfl, ?_, ?_⟩
  · exact fun w hw => congrArg Prod.fst (hz w hw)
  · exact fun h hh => congrArg (fun q : BinSample X => q.2 h.2) (hz h.1 hh)

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

theorem posterior_bins_subset_three (w : X.Bin) (h : X.Key)
    (hh : h.1 ∈ closedBinNeighbors X w) : X.binsOf (X.C h) ⊆ coarseBinScope X w := by
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
  exact binScopeTwo_subset_three X w
    (Finset.mem_biUnion.mpr ⟨h.1, hh, key_neighbor_bin_close X h k hk⟩)

theorem makeType_coarse_scope_subset_three (w : X.Bin) (h : X.Key)
    (hh : h.1 ∈ closedBinNeighbors X w) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ) :
    step2CoarseScope X (makeType6 binAdjacent6 h t F j X.J) ⊆ coarseBinScope X w := by
  have hkey : (makeType6 binAdjacent6 h t F j X.J).key = h := by
    unfold makeType6
    split_ifs <;> rfl
  intro u hu
  rcases Finset.mem_insert.mp hu with hu | hu
  · subst u
    have hfirst := congrArg Prod.fst hkey
    exact hfirst.symm ▸ closedBinNeighbors_subset_three X w hh
  · rcases Finset.mem_biUnion.mp hu with ⟨ℓ, hℓ, hu⟩
    rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
    have hobs := makeType_observations_close X h t F j ℓ hℓ
    exact Finset.mem_biUnion.mpr ⟨h.1, hh, Finset.mem_biUnion.mpr
      ⟨ℓ.1.1, hobs.1, key_neighbor_bin_close X ℓ.1 k hk⟩⟩

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

theorem baseAgree_withPar (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (nm : ParentName6 X.Bin) (ξ : Fin N) :
    BaseAgree X s (X.withPar b nm ξ) (X.withPar b' nm ξ) := by
  cases nm with
  | initial => exact ⟨rfl, hb.2.1, hb.2.2⟩
  | candidate w =>
      refine ⟨hb.1, ?_, hb.2.2⟩
      intro u hu
      by_cases huw : u = w
      · simp [Ctx6.withPar, Ctx6.parOf, Par6.set, huw]
      · simpa [Ctx6.withPar, Ctx6.parOf, Par6.set, Function.update_of_ne huw] using hb.2.1 u hu

theorem primary_values_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (h : X.Key) (hh : h.1 ∈ s) :
    (X.parOf b).val (primaryName6 h) = (X.parOf b').val (primaryName6 h) ∧
      (X.parOf b).val (otherPrimaryName6 h) = (X.parOf b').val (otherPrimaryName6 h) := by
  cases hf : h.2 <;> simp [Ctx6.parOf, primaryName6, otherPrimaryName6, Par6.val, hf, hb.1, hb.2.1 h.1 hh]

theorem tagPost_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s)
    (Z : X.Hid) (obs : Finset X.HKey) (hobs : obs ⊆ β.obs) :
    X.tagPost (b, Z) β obs = X.tagPost (b', Z) β obs := by
  unfold Ctx6.tagPost
  congr 1
  funext i
  exact tagWeight_eq_of_baseAgree X s b b' hb β hscope Z obs hobs i

theorem Tβ_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (Z : X.Hid) :
    X.Tβ (b, Z) β = X.Tβ (b', Z) β :=
  tagPost_eq_of_baseAgree X s b b' hb β hscope Z β.obs (Finset.Subset.refl _)

theorem TβDel_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (Z : X.Hid) (ℓ : X.HKey) :
    X.TβDel (b, Z) β ℓ = X.TβDel (b', Z) β ℓ :=
  tagPost_eq_of_baseAgree X s b b' hb β hscope Z (β.obs.erase ℓ) (Finset.erase_subset _ _)

theorem required_values_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hkey : β.key.1 ∈ s) (Z : X.Hid)
    (nm : X.Name) (hnm : nm ∈ reqNames6 β) :
    X.varVal (b, Z) nm = X.varVal (b', Z) nm := by
  have hprimary := primary_values_eq_of_baseAgree X s b b' hb β.key hkey
  rcases reqNames6_cases β nm hnm with hnm | ⟨ℓ, hℓ, rfl⟩ | ⟨hm, hnm⟩
  · subst nm
    exact hprimary.1
  · rfl
  · subst nm
    exact hprimary.2

theorem labelLaw_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hkey : β.key.1 ∈ s) (Z : X.Hid)
    (names : Finset X.Name) (hnames : names ⊆ reqNames6 β) (i : X.ι) :
    X.labelLaw (b, Z) names i = X.labelLaw (b', Z) names i := by
  have hreq : X.reqNbhd (b, Z) names = X.reqNbhd (b', Z) names := by
    apply Finset.ext
    intro y
    simp only [Ctx6.reqNbhd, Finset.mem_filter, Finset.mem_univ, true_and]
    have hvalues : ∀ nm ∈ names, X.varVal (b, Z) nm = X.varVal (b', Z) nm :=
      fun nm hnm => required_values_eq_of_baseAgree X s b b' hb β hkey Z nm (hnames hnm)
    constructor <;> intro h nm hnm
    · simpa only [← hvalues nm hnm] using h nm hnm
    · simpa only [hvalues nm hnm] using h nm hnm
  unfold Ctx6.labelLaw
  rw [hreq]

theorem tupleLaw_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (Z : X.Hid) :
    X.tupleLaw (b, Z) β = X.tupleLaw (b', Z) β := by
  have htag := Tβ_eq_of_baseAgree X s b b' hb β hscope Z
  have hlabel : ∀ i, X.labelLaw (b, Z) (reqNames6 β) i = X.labelLaw (b', Z) (reqNames6 β) i :=
    fun i => labelLaw_eq_of_baseAgree X s b b' hb β (hscope (Finset.mem_insert_self _ _)) Z _
      (Finset.Subset.refl _) i
  unfold Ctx6.tupleLaw Ctx6.tupleLawOn
  rw [htag]
  congr 1
  funext i
  congr 1
  funext r
  exact hlabel i

theorem tupleRatio_eq_of_baseAgree (s : Finset X.Bin) (b b' bx bx' : X.Base)
    (hb : BaseAgree X s b b') (hbx : BaseAgree X s bx bx')
    (β : X.Ty) (hscope : step2CoarseScope X β ⊆ s) (Z Zx : X.Hid)
    (R R' : FinProb X.ι) (hR : R = R') (drop : X.Name) (o : X.Tuple) :
    X.tupleRatio (bx, Zx) (b, Z) β R drop o =
      X.tupleRatio (bx', Zx) (b', Z) β R' drop o := by
  have htag := Tβ_eq_of_baseAgree X s bx bx' hbx β hscope Zx
  have hkey := hscope (Finset.mem_insert_self _ _)
  have hnum := labelLaw_eq_of_baseAgree X s bx bx' hbx β hkey Zx (reqNames6 β)
    (Finset.Subset.refl _) o.1
  have hden := labelLaw_eq_of_baseAgree X s b b' hb β hkey Z ((reqNames6 β).erase drop)
    (Finset.erase_subset _ _) o.1
  unfold Ctx6.tupleRatio
  rw [htag, hR, hnum, hden]

section CoarseStepThree
variable {Id : Type} [Fintype Id] [DecidableEq Id]

def rate3CoarseScope (b : X.State) (D : Finset (Id × X.Ty)) : Finset X.Bin :=
  insert (X.g.L.stKey b).1
    (X.binsOf (X.locKeys D) ∪
      ((D.biUnion fun e => step2CoarseScope X e.2) ∪
        ((Lane_q_s06_stages.rate3HiddenScope X b D).biUnion fun ℓ => X.binsOf (X.C ℓ.1))))

theorem rate3_scope_type (b : X.State) (D : Finset (Id × X.Ty)) (s : Finset X.Bin)
    (hs : rate3CoarseScope X b D ⊆ s) (e : Id × X.Ty) (he : e ∈ D) :
    step2CoarseScope X e.2 ⊆ s := by
  intro u hu
  exact hs (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨e, he, hu⟩))))

theorem rate3_scope_hidden (b : X.State) (D : Finset (Id × X.Ty)) (s : Finset X.Bin)
    (hs : rate3CoarseScope X b D ⊆ s) (ℓ : X.HKey)
    (hℓ : ℓ ∈ Lane_q_s06_stages.rate3HiddenScope X b D) :
    X.binsOf (X.C ℓ.1) ⊆ s := by
  intro u hu
  exact hs (Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hu⟩))))

theorem rate3_scope_local_key (b : X.State) (D : Finset (Id × X.Ty)) (s : Finset X.Bin)
    (hs : rate3CoarseScope X b D ⊆ s) (h : X.Key) (hh : h ∈ X.locKeys D) : h.1 ∈ s :=
  hs (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h, hh, rfl⟩)))

theorem priorOf_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (Z : X.Hid) (nm : ParentName6 X.Bin) :
    X.priorOf (b, Z) nm = X.priorOf (b', Z) nm := by
  cases nm with
  | initial => rfl
  | candidate w => change X.candLaw b.1 = X.candLaw b'.1; rw [hb.1]

theorem lowGate_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (hm : X.stMode a = .low) (Z : X.Hid) (ξ : Fin N) :
    X.LowGate (b, Z) a D ξ ↔ X.LowGate (b', Z) a D ξ := by
  have htgt : X.tgt a ∈ Lane_q_s06_stages.rate3HiddenScope X a D := by
    simp [Lane_q_s06_stages.rate3HiddenScope, hm]
  have hpost := hidPost_eq_of_baseAgree X s b b' hb (X.tgt a).1
    (rate3_scope_hidden X a D s hs _ htgt)
  have htests : ∀ e ∈ D,
      X.Step2Tests (X.withHid (b, Z) (X.tgt a) ξ) e.2 ↔
        X.Step2Tests (X.withHid (b', Z) (X.tgt a) ξ) e.2 := by
    intro e he
    exact step2Tests_iff_of_baseAgree X s b b' hb e.2 (rate3_scope_type X a D s hs e he)
      (Function.update Z (X.tgt a) ξ)
  unfold Ctx6.LowGate Ctx6.Step1Cap
  rw [hpost]
  constructor <;> rintro ⟨hp, hc, ht⟩
  · exact ⟨hp, hc, fun e he => (htests e he).mp (ht e he)⟩
  · exact ⟨hp, hc, fun e he => (htests e he).mpr (ht e he)⟩

theorem lowLik_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (β : X.Ty)
    (hs : step2CoarseScope X β ⊆ s) (Z : X.Hid) (ξ : Fin N) (o : X.Tuple) :
    X.lowLik (b, Z) a ξ β o = X.lowLik (b', Z) a ξ β o := by
  exact tupleRatio_eq_of_baseAgree X s b b' b b' hb hb β hs Z
    (Function.update Z (X.tgt a) ξ) _ _ (TβDel_eq_of_baseAgree X s b b' hb β hs Z (X.tgt a))
    (.hid (X.tgt a)) o

theorem highGate_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (Z : X.Hid) (ξ : Fin N) :
    X.HighGate (b, Z) a D ξ ↔ X.HighGate (b', Z) a D ξ := by
  have hp := priorOf_eq_of_baseAgree X s b b' hb Z (X.tgtName a)
  have hbξ := baseAgree_withPar X s b b' hb (X.tgtName a) ξ
  have htests : ∀ e ∈ D,
      X.Step2Tests (X.withParH (b, Z) (X.tgtName a) ξ) e.2 ↔
        X.Step2Tests (X.withParH (b', Z) (X.tgtName a) ξ) e.2 := by
    intro e he
    exact step2Tests_iff_of_baseAgree X s _ _ hbξ e.2 (rate3_scope_type X a D s hs e he) Z
  have hstep1 : ∀ ℓ ∈ X.locHid D,
      X.Step1OK (X.withParH (b, Z) (X.tgtName a) ξ).1 ℓ.1 ↔
        X.Step1OK (X.withParH (b', Z) (X.tgtName a) ξ).1 ℓ.1 := by
    intro ℓ hℓ
    exact step1OK_iff_of_baseAgree X s _ _ hbξ ℓ.1
      (rate3_scope_hidden X a D s hs ℓ (Finset.mem_union_left _ hℓ))
  unfold Ctx6.HighGate
  rw [hp]
  constructor <;> rintro ⟨hpos, h1, h2⟩
  · exact ⟨hpos, fun ℓ hℓ => (hstep1 ℓ hℓ).mp (h1 ℓ hℓ), fun e he => (htests e he).mp (h2 e he)⟩
  · exact ⟨hpos, fun ℓ hℓ => (hstep1 ℓ hℓ).mpr (h1 ℓ hℓ), fun e he => (htests e he).mpr (h2 e he)⟩

theorem highLik_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (β : X.Ty)
    (hs : step2CoarseScope X β ⊆ s) (Z : X.Hid) (ξ : Fin N) (o : X.Tuple) :
    X.highLik (b, Z) a ξ β o = X.highLik (b', Z) a ξ β o := by
  exact tupleRatio_eq_of_baseAgree X s b b' _ _ hb
    (baseAgree_withPar X s b b' hb (X.tgtName a) ξ) β hs Z Z _ _ rfl (.par (X.tgtName a)) o

theorem locDensity_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (Z : X.Hid) (ξ : Fin N) :
    X.locDensity (b, Z) (X.tgtName a) D ξ = X.locDensity (b', Z) (X.tgtName a) D ξ := by
  have hbξ := baseAgree_withPar X s b b' hb (X.tgtName a) ξ
  have hkeys : ∀ h ∈ X.locKeys D, h.1 ∈ s := rate3_scope_local_key X a D s hs
  have hcand : (∏ u ∈ X.locBins D (X.tgtName a),
      (N : ℝ) * (X.candLaw (X.withPar b (X.tgtName a) ξ).1).w (b.2.1 u)) =
      ∏ u ∈ X.locBins D (X.tgtName a),
        (N : ℝ) * (X.candLaw (X.withPar b' (X.tgtName a) ξ).1).w (b'.2.1 u) := by
    apply Finset.prod_congr rfl
    intro u hu
    have huS : u ∈ s := hs (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_filter.mp hu).1))
    rw [hbξ.1, hb.2.1 u huS]
  have htags : (∏ h ∈ X.locKeys D,
      safeRatio6 ((X.tagLawAt (X.parOf (X.withPar b (X.tgtName a) ξ)) h).w (b.2.2 h)) (M.Λ (b.2.2 h))) =
      ∏ h ∈ X.locKeys D,
        safeRatio6 ((X.tagLawAt (X.parOf (X.withPar b' (X.tgtName a) ξ)) h).w (b'.2.2 h)) (M.Λ (b'.2.2 h)) := by
    apply Finset.prod_congr rfl
    intro h hh
    rw [tagLawAt_eq_of_baseAgree X s _ _ hbξ h (hkeys h hh), hb.2.2 h (hkeys h hh)]
  have hhidden : (∏ ℓ ∈ X.locHid D,
      (N : ℝ) * (X.hidPost (X.withPar b (X.tgtName a) ξ) ℓ.1).w (Z ℓ)) =
      ∏ ℓ ∈ X.locHid D,
        (N : ℝ) * (X.hidPost (X.withPar b' (X.tgtName a) ξ) ℓ.1).w (Z ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hidPost_eq_of_baseAgree X s _ _ hbξ ℓ.1
      (rate3_scope_hidden X a D s hs ℓ (Finset.mem_union_left _ hℓ))]
  unfold Ctx6.locDensity
  dsimp only
  rw [hcand, htags, hhidden]

theorem s3Weight_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (Z : X.Hid) (o : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.s3Weight (b, Z) a D o drop ξ = X.s3Weight (b', Z) a D o drop ξ := by
  cases hm : X.stMode a
  · have htgt : X.tgt a ∈ Lane_q_s06_stages.rate3HiddenScope X a D := by
      simp [Lane_q_s06_stages.rate3HiddenScope, hm]
    have hp := hidPost_eq_of_baseAgree X s b b' hb (X.tgt a).1
      (rate3_scope_hidden X a D s hs _ htgt)
    have hg := propext (lowGate_iff_of_baseAgree X s b b' hb a D hs hm Z ξ)
    simp only [Ctx6.s3Weight, hm, Ctx6.lowWeight]
    rw [hp, hg]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    split_ifs
    · rfl
    · exact lowLik_eq_of_baseAgree X s b b' hb a e.2 (rate3_scope_type X a D s hs e he) Z ξ (o e)
  · have hp := priorOf_eq_of_baseAgree X s b b' hb Z (X.tgtName a)
    have hg := propext (highGate_iff_of_baseAgree X s b b' hb a D hs Z ξ)
    have hl := locDensity_eq_of_baseAgree X s b b' hb a D hs Z ξ
    simp only [Ctx6.s3Weight, hm, Ctx6.highWeight]
    rw [hp, hg, hl]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    split_ifs
    · rfl
    · exact highLik_eq_of_baseAgree X s b b' hb a e.2 (rate3_scope_type X a D s hs e he) Z ξ (o e)

theorem s3Mass_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (Z : X.Hid) (o : X.Data Id) (drop : Option (Id × X.Ty)) :
    X.s3Mass (b, Z) a D o drop = X.s3Mass (b', Z) a D o drop := by
  apply Finset.sum_congr rfl
  intro ξ hξ
  exact s3Weight_eq_of_baseAgree X s b b' hb a D hs Z o drop ξ

theorem s3Fail_iff_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (Z : X.Hid) (o : X.Data Id) :
    X.S3Fail (b, Z) a D o ↔ X.S3Fail (b', Z) a D o := by
  have htgt : (X.g.L.stKey a).1 ∈ s := hs (Finset.mem_insert_self _ _)
  have htrue : X.trueTarget (b, Z) a = X.trueTarget (b', Z) a := by
    cases hm : X.stMode a
    · simp only [Ctx6.trueTarget, hm]
    · simp only [Ctx6.trueTarget, hm]
      exact (primary_values_eq_of_baseAgree X s b b' hb (X.g.L.stKey a) htgt).1
  have hgate : X.S3TrueGate (b, Z) a D ↔ X.S3TrueGate (b', Z) a D := by
    cases hm : X.stMode a
    · simp only [Ctx6.S3TrueGate, hm, htrue]
      exact lowGate_iff_of_baseAgree X s b b' hb a D hs hm Z _
    · simp only [Ctx6.S3TrueGate, hm, htrue]
      exact highGate_iff_of_baseAgree X s b b' hb a D hs Z _
  have htests : X.S3Tests (b, Z) a D o ↔ X.S3Tests (b', Z) a D o := by
    unfold Ctx6.S3Tests
    simp only [s3Mass_eq_of_baseAgree X s b b' hb a D hs Z o]
  exact and_congr hgate (not_congr htests)

set_option maxHeartbeats 400000 in
theorem s3_data_rate_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Id × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) (Z : X.Hid) :
    (X.dataLaw Id (b, Z)).pr (fun o => X.S3Fail (b, Z) a D o) =
      (X.dataLaw Id (b', Z)).pr (fun o => X.S3Fail (b', Z) a D o) := by
  let P : (Id × X.Ty) → FinProb X.Tuple := fun e => X.tupleLaw (b, Z) e.2
  let Q : (Id × X.Ty) → FinProb X.Tuple := fun e => X.tupleLaw (b', Z) e.2
  have hPQ : ∀ e ∈ D, P e = Q e := by
    intro e he
    exact tupleLaw_eq_of_baseAgree X s b b' hb e.2 (rate3_scope_type X a D s hs e he) Z
  calc
    _ = (X.dataLaw Id (b, Z)).pr (fun o => X.S3Fail (b', Z) a D o) :=
      Lane_q_s06_stages.pr_congr _ (s3Fail_iff_of_baseAgree X s b b' hb a D hs Z)
    _ = _ := Lane_q_s06_stages.pi_pr_eq_of_kernel_eq_on_depends P Q D
      (fun o => X.S3Fail (b', Z) a D o) (Lane_q_s06_stages.s3Fail_dependsOn_data X (b', Z) a D) hPQ

set_option maxHeartbeats 400000 in
theorem s3_base_rate_eq_of_baseAgree (s : Finset X.Bin) (b b' : X.Base)
    (hb : BaseAgree X s b b') (a : X.State) (D : Finset (Fin X.T × X.Ty))
    (hs : rate3CoarseScope X a D ⊆ s) :
    (X.hidLaw b).expect (fun Z => (X.dataLaw (Fin X.T) (b, Z)).pr (fun o => X.S3Fail (b, Z) a D o)) =
      (X.hidLaw b').expect (fun Z => (X.dataLaw (Fin X.T) (b', Z)).pr (fun o => X.S3Fail (b', Z) a D o)) := by
  let P : X.HKey → Law N := fun ℓ => X.hidPost b ℓ.1
  let Q : X.HKey → Law N := fun ℓ => X.hidPost b' ℓ.1
  let F : X.Hid → ℝ := fun Z =>
    (X.dataLaw (Fin X.T) (b', Z)).pr (fun o => X.S3Fail (b', Z) a D o)
  have hF : FinProb.DependsOn F (Lane_q_s06_stages.rate3HiddenScope X a D) :=
    fun Z Z' hZ => Lane_q_s06_stages.s3FailPr_eq_of_agree X b' a D Z Z' hZ
  have hPQ : ∀ ℓ ∈ Lane_q_s06_stages.rate3HiddenScope X a D, P ℓ = Q ℓ := by
    intro ℓ hℓ
    exact hidPost_eq_of_baseAgree X s b b' hb ℓ.1 (rate3_scope_hidden X a D s hs ℓ hℓ)
  calc
    _ = (X.hidLaw b).expect F := by
      apply Finset.sum_congr rfl
      intro Z hZ
      exact congrArg (fun r : ℝ => (X.hidLaw b).w Z * r)
        (s3_data_rate_eq_of_baseAgree X s b b' hb a D hs Z)
    _ = _ := pi_expect_eq_of_kernels_on_scope P Q (Lane_q_s06_stages.rate3HiddenScope X a D)
      F (fun _ => X.y₀) hF hPQ

theorem rate3CoarseScope_subset_three (a : X.State) (D : Finset (Fin X.T × X.Ty))
    (hD : D ∈ X.absDescs a) : rate3CoarseScope X a D ⊆ coarseBinScope X (X.g.L.stKey a).1 := by
  let w := (X.g.L.stKey a).1
  have htypes : ∀ e ∈ D, step2CoarseScope X e.2 ⊆ coarseBinScope X w := by
    intro e he
    rcases Finset.mem_image.mp hD with ⟨φ, hφ, hφD⟩
    have he' : e ∈ X.descOf a φ := by rw [hφD]; exact he
    rcases Finset.mem_image.mp he' with ⟨a', ha', hea'⟩
    rw [← hea']
    have hkey := key_neighbor_bin_close X (X.g.L.stKey a) (X.g.L.stKey a'.1)
      (S06.Lane_q_s06_steps2.neighbor_key_severity6 X a'.property).1
    exact makeType_coarse_scope_subset_three X w (X.g.L.stKey a'.1) hkey
      (X.g.L.stSign a'.1) (X.g.L.stFlippable a'.1) (X.g.L.stSeverity a'.1)
  have hhidden : ∀ ℓ ∈ Lane_q_s06_stages.rate3HiddenScope X a D,
      X.binsOf (X.C ℓ.1) ⊆ coarseBinScope X w := by
    intro ℓ hℓ
    rcases Finset.mem_union.mp hℓ with hℓ | hℓ
    · rcases Finset.mem_biUnion.mp hℓ with ⟨e, he, hobs⟩
      exact observation_bins_subset X e.2 _ (htypes e he) ℓ hobs
    · split_ifs at hℓ with hm
      · have heq : ℓ = X.tgt a := Finset.mem_singleton.mp hℓ
        subst ℓ
        exact posterior_bins_subset_three X w (X.g.L.stKey a) (self_mem_closedBinNeighbors X w)
      · exact False.elim (Finset.notMem_empty _ hℓ)
  have hkeys : ∀ k ∈ X.locKeys D, k.1 ∈ coarseBinScope X w := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · rcases Finset.mem_biUnion.mp hk with ⟨ℓ, hℓ, hk⟩
      exact hhidden ℓ (Finset.mem_union_left _ hℓ) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    · rcases Finset.mem_image.mp hk with ⟨e, he, rfl⟩
      exact htypes e he (Finset.mem_insert_self _ _)
  intro u hu
  rcases Finset.mem_insert.mp hu with hu | hu
  · subst u
    exact closedBinNeighbors_subset_three X w (self_mem_closedBinNeighbors X w)
  · rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
      exact hkeys k hk
    · rcases Finset.mem_union.mp hu with hu | hu
      · rcases Finset.mem_biUnion.mp hu with ⟨e, he, hu⟩
        exact htypes e he hu
      · rcases Finset.mem_biUnion.mp hu with ⟨ℓ, hℓ, hu⟩
        exact hhidden ℓ hℓ hu

def targetFields (a : X.State) : X.Key × Mode6 × CubeVertex X.g.L.m :=
  (X.g.L.stKey a, X.stMode a, X.g.L.stSign a)

theorem s3Weight_eq_of_targetFields (a a' : X.State) (ha : targetFields X a = targetFields X a')
    (H : X.Hist) (D : Finset (Id × X.Ty)) (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.s3Weight H a D o drop ξ = X.s3Weight H a' D o drop ξ := by
  have hkey : X.g.L.stKey a = X.g.L.stKey a' := congrArg Prod.fst ha
  have hmode : X.stMode a = X.stMode a' := congrArg (fun s => s.2.1) ha
  have hsign : X.g.L.stSign a = X.g.L.stSign a' := congrArg (fun s => s.2.2) ha
  have htgt : X.tgt a = X.tgt a' := Prod.ext hkey hsign
  have hname : X.tgtName a = X.tgtName a' := congrArg primaryName6 hkey
  unfold Ctx6.s3Weight
  rw [hmode]
  cases X.stMode a'
  · have hg : X.LowGate H a D ξ = X.LowGate H a' D ξ := by unfold Ctx6.LowGate; rw [htgt]
    simp only [Ctx6.lowWeight, Ctx6.lowLik, htgt, hg]
  · have hg : X.HighGate H a D ξ = X.HighGate H a' D ξ := by unfold Ctx6.HighGate; rw [hname]
    simp only [Ctx6.highWeight, Ctx6.highLik, hname, hg]

theorem s3Fail_iff_of_targetFields (a a' : X.State) (ha : targetFields X a = targetFields X a')
    (H : X.Hist) (D : Finset (Id × X.Ty)) (o : X.Data Id) :
    X.S3Fail H a D o ↔ X.S3Fail H a' D o := by
  have hkey : X.g.L.stKey a = X.g.L.stKey a' := congrArg Prod.fst ha
  have hmode : X.stMode a = X.stMode a' := congrArg (fun s => s.2.1) ha
  have hsign : X.g.L.stSign a = X.g.L.stSign a' := congrArg (fun s => s.2.2) ha
  have htgt : X.tgt a = X.tgt a' := Prod.ext hkey hsign
  have hname : X.tgtName a = X.tgtName a' := congrArg primaryName6 hkey
  have hgate : X.S3TrueGate H a D ↔ X.S3TrueGate H a' D := by
    unfold Ctx6.S3TrueGate Ctx6.trueTarget
    rw [hmode]
    cases X.stMode a'
    · simp only [Ctx6.LowGate, htgt]
    · simp only [Ctx6.HighGate, hname]
  have hmass (drop : Option (Id × X.Ty)) : X.s3Mass H a D o drop = X.s3Mass H a' D o drop := by
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact s3Weight_eq_of_targetFields X a a' ha H D o drop ξ
  have hmatching (β : X.Ty) : X.Matching a β ↔ X.Matching a' β := by
    simp only [Ctx6.Matching, hmode, hkey]
  simp only [Ctx6.S3Fail, Ctx6.S3Tests, hgate, hmass, hmatching]

theorem s3_data_rate_eq_of_targetFields (a a' : X.State) (ha : targetFields X a = targetFields X a')
    (H : X.Hist) (D : Finset (Id × X.Ty)) :
    (X.dataLaw Id H).pr (fun o => X.S3Fail H a D o) =
      (X.dataLaw Id H).pr (fun o => X.S3Fail H a' D o) :=
  Lane_q_s06_stages.pr_congr _ (s3Fail_iff_of_targetFields X a a' ha H D)

theorem far_high_hidden_scope_empty (a : X.State) (D : Finset (Fin X.T × X.Ty))
    (hD : D ∈ X.absDescs a) (hfar : X.J + 2 < X.g.L.stSeverity a) :
    Lane_q_s06_stages.rate3HiddenScope X a D = ∅ := by
  have hmode : X.stMode a = .high := by
    have hnot : ¬ X.g.L.stSeverity a ≤ X.J := by omega
    simp [Ctx6.stMode, modeOf6, hnot]
  have hobs : ∀ e ∈ D, e.2.obs = ∅ := by
    intro e he
    rcases Finset.mem_image.mp hD with ⟨φ, hφ, hφD⟩
    have he' : e ∈ X.descOf a φ := by rw [hφD]; exact he
    rcases Finset.mem_image.mp he' with ⟨a', ha', hea'⟩
    have hsev := (S06.Lane_q_s06_steps2.neighbor_key_severity6 X a'.property).2
    unfold Nat.dist at hsev
    have hfarA : X.J + 1 < X.g.L.stSeverity a'.1 := by omega
    have hnotLow : ¬ X.g.L.stSeverity a'.1 ≤ X.J := by omega
    have hnotFringe : X.g.L.stSeverity a'.1 ≠ X.J + 1 := by omega
    rw [← hea']
    simp only [Ctx6.stType, ChunkLayout6.stType, makeType6, if_neg hnotLow,
      Type6.obs, highObservations6, if_neg hnotFringe]
  have hloc : X.locHid D = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp hℓ with ⟨e, he, hℓ⟩
    rw [hobs e he] at hℓ
    exact Finset.notMem_empty _ hℓ
  simpa [Lane_q_s06_stages.rate3HiddenScope, Ctx6.locHid, hmode] using hloc

theorem s3_rate_eq_base_of_hidden_scope_empty (b : X.Base) (a : X.State)
    (D : Finset (Fin X.T × X.Ty)) (hEmpty : Lane_q_s06_stages.rate3HiddenScope X a D = ∅) (Z : X.Hid) :
    (X.dataLaw (Fin X.T) (b, Z)).pr (fun o => X.S3Fail (b, Z) a D o) =
      (X.hidLaw b).expect (fun Z' => (X.dataLaw (Fin X.T) (b, Z')).pr (fun o => X.S3Fail (b, Z') a D o)) := by
  let F : X.Hid → ℝ := fun Z' => (X.dataLaw (Fin X.T) (b, Z')).pr (fun o => X.S3Fail (b, Z') a D o)
  have hconst : ∀ Z', F Z' = F Z := by
    intro Z'
    apply Lane_q_s06_stages.s3FailPr_eq_of_agree X b a D Z' Z
    rw [hEmpty]
    intro ℓ hℓ
    exact False.elim (Finset.notMem_empty _ hℓ)
  have hmean : (X.hidLaw b).expect F = F Z := by
    calc
      _ = (X.hidLaw b).expect (fun _ => F Z) := by
        apply Finset.sum_congr rfl
        intro Z' hZ'
        exact congrArg (fun r : ℝ => (X.hidLaw b).w Z' * r) (hconst Z')
      _ = _ := FinProb.expect_const _ _
  exact hmean.symm

end CoarseStepThree

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

def localStep1Keys (w : X.Bin) : Finset X.Key :=
  X.step1Keys.filter fun h => h.1 ∈ closedBinNeighbors X w

theorem localStep1Keys_card_le (w : X.Bin) : (localStep1Keys X w).card ≤ 1204 := by
  have hsub : localStep1Keys X w ⊆ (closedBinNeighbors X w).product (Finset.univ : Finset KeyFlag6) := by
    intro h hh
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hh).2, Finset.mem_univ _⟩
  have hflag : Fintype.card KeyFlag6 = 2 := by decide
  calc
    _ ≤ ((closedBinNeighbors X w).product (Finset.univ : Finset KeyFlag6)).card := Finset.card_le_card hsub
    _ = (closedBinNeighbors X w).card * 2 := by rw [card_product_explicit]; simp [hflag]
    _ ≤ 1204 := by have hh := closedBinNeighbors_card_le X w; omega

theorem coarse_step1_group_probability (v : Fin N) (w : X.Bin) (r : ℝ) (hr : 0 ≤ r)
    (hprob : ∀ h ∈ X.step1Keys, (X.coarseLaw v).pr (fun c => ¬ X.Step1OK (v, c) h) ≤ r) :
    (X.coarseLaw v).pr (fun c => ∃ x : CubeVertex n, (X.g.L.key x).1 = w ∧
      ∃ h ∈ X.C (X.g.L.key x), ¬ X.Step1OK (v, c) h) ≤ 1204 * r := by
  have hsub : ∀ c : X.Coarse, (∃ x : CubeVertex n, (X.g.L.key x).1 = w ∧
      ∃ h ∈ X.C (X.g.L.key x), ¬ X.Step1OK (v, c) h) →
      ∃ h ∈ localStep1Keys X w, ¬ X.Step1OK (v, c) h := by
    rintro c ⟨x, hx, h, hh, hf⟩
    have hnear := key_neighbor_bin_close X (X.g.L.key x) h hh
    rw [hx] at hnear
    have hkey : h ∈ X.step1Keys := Finset.mem_biUnion.mpr ⟨X.g.L.key x,
      Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hh⟩
    exact ⟨h, Finset.mem_filter.mpr ⟨hkey, hnear⟩, hf⟩
  calc
    _ ≤ (X.coarseLaw v).pr (fun c => ∃ h ∈ localStep1Keys X w, ¬ X.Step1OK (v, c) h) :=
      Lane_q_s06_stages.pr_mono _ hsub
    _ ≤ ((localStep1Keys X w).card : ℝ) * r :=
      pr_finite_union_le_card _ _ _ r (fun h hh => hprob h (Finset.mem_filter.mp hh).1)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast localStep1Keys_card_le X w) hr

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
theorem eventually_coarse_step1_charge_budget :
    ∀ᶠ n : ℕ in atTop,
      1204 * (n : ℝ) ^ (-(δ₁ / 4)) ≤ (n : ℝ) ^ (-(δ₁ / 8)) / 4 := by
  have hh := Lane_q_s06_stages.eventually_const_mul_nat_rpow_neg_lt
    (c := 4816) (by norm_num [δ₁] : (0 : ℝ) < δ₁ / 8) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh, Filter.eventually_ge_atTop 2] with n hn hn2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) ^ (-(δ₁ / 4)) = ((n : ℝ) ^ (-(δ₁ / 8))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    norm_num
    ring
  rw [hpow]
  have hx : 0 ≤ (n : ℝ) ^ (-(δ₁ / 8)) := Real.rpow_nonneg hn0.le _
  nlinarith [mul_le_mul_of_nonneg_right hn.le hx]

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

def descriptorCodes (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ) :
    Finset (Finset (Fin X.T × X.Ty)) :=
  ((((Finset.univ : Finset (Fin X.T)).product (genericNeighborTypes X h t F j)).powerset).product
    ((Finset.range (1 + 21 * (X.J + 2) + 1)).biUnion fun r =>
      ((Finset.univ : Finset (Fin X.T)).product (neighborTypeUniverse X h t F j)).powersetCard r)).image
        (fun q => q.1 ∪ q.2)

theorem descriptorCodes_card_le (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ) :
    (descriptorCodes X h t F j).card ≤
      2 ^ (1806 * X.T) * (X.T * 4000 * (X.m + 1) ^ 2 + 2) ^ (2 * (1 + 21 * (X.J + 2))) := by
  let G : Finset (Fin X.T × X.Ty) :=
    (Finset.univ : Finset (Fin X.T)).product (genericNeighborTypes X h t F j)
  let A : Finset (Fin X.T × X.Ty) :=
    (Finset.univ : Finset (Fin X.T)).product (neighborTypeUniverse X h t F j)
  let B : ℕ := 1 + 21 * (X.J + 2)
  let Bs : Finset (Finset (Fin X.T × X.Ty)) := (Finset.range (B + 1)).biUnion fun r => A.powersetCard r
  have hG : G.card ≤ 1806 * X.T := by
    dsimp only [G]
    rw [card_product_explicit]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (Nat.mul_le_mul_left X.T (genericNeighborTypes_card_le X h t F j)).trans
      (by rw [Nat.mul_comm])
  have hA : A.card ≤ X.T * 4000 * (X.m + 1) ^ 2 := by
    dsimp only [A]
    rw [card_product_explicit]
    simp only [Finset.card_univ, Fintype.card_fin]
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left X.T (neighborTypeUniverse_card_le X h t F j)
  have hGs : G.powerset.card ≤ 2 ^ (1806 * X.T) := by
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hG
  have hBs : Bs.card ≤ (X.T * 4000 * (X.m + 1) ^ 2 + 2) ^ (2 * B) := by
    exact (S06.Lane_q_s06_steps2.smallPowersetCount6 A B).trans
      (Nat.pow_le_pow_left (Nat.add_le_add hA (Nat.le_refl 2)) (2 * B))
  calc
    (descriptorCodes X h t F j).card ≤ (G.powerset.product Bs).card := Finset.card_image_le
    _ = G.powerset.card * Bs.card := card_product_explicit _ _
    _ ≤ _ := Nat.mul_le_mul hGs hBs

theorem descriptor_mem_codes (b : X.State) (hb : b ∈ X.g.L.oddStates) (hn : 4 ≤ n)
    (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs b) :
    D ∈ descriptorCodes X (X.g.L.stKey b) (X.g.L.stSign b) (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by
  let G := genericDescriptorPart X b D
  let A := exceptionalDescriptorPart X b D
  have hG : G ∈ ((Finset.univ : Finset (Fin X.T)).product
      (genericNeighborTypes X (X.g.L.stKey b) (X.g.L.stSign b) (X.g.L.stFlippable b)
        (X.g.L.stSeverity b))).powerset := Finset.mem_powerset.mpr (genericDescriptorPart_subset X b D)
  have hAsub : A ⊆ ((Finset.univ : Finset (Fin X.T)).product
      (neighborTypeUniverse X (X.g.L.stKey b) (X.g.L.stSign b) (X.g.L.stFlippable b)
        (X.g.L.stSeverity b))) := by
    intro e he
    exact descriptor_subset_universe X b D hD (Finset.mem_filter.mp he).1
  have hAcard : A.card ≤ 1 + 21 * (X.J + 2) := exceptionalDescriptorPart_card_le X b hb hn D hD
  apply Finset.mem_image.mpr
  refine ⟨(G, A), Finset.mem_product.mpr ⟨hG, ?_⟩, descriptorParts_union X b D⟩
  exact Finset.mem_biUnion.mpr ⟨A.card, Finset.mem_range.mpr (by omega),
    Finset.mem_powersetCard.mpr ⟨hAsub, rfl⟩⟩

abbrev DescriptorShape := KeyFlag6 × Mode6 × Finset (Fin X.T × X.Ty)

def nearGroupDescriptorShapes (gr : X.Bin × CubeVertex X.m) : Finset (DescriptorShape X) :=
  (X.g.L.oddStates.filter fun b => (X.g.L.stKey b).1 = gr.1 ∧ X.g.L.stSign b = gr.2 ∧
    X.g.L.stSeverity b ≤ X.J + 2).biUnion fun b =>
      (X.absDescs b).image fun D => ((X.g.L.stKey b).2, X.stMode b, D)

def groupDescriptorShapeCodes (gr : X.Bin × CubeVertex X.m) : Finset (DescriptorShape X) :=
  ((Finset.univ : Finset KeyFlag6).product (Finset.univ : Finset Mode6)).biUnion fun fm =>
    (Finset.range (X.J + 3)).biUnion fun j =>
      ((Finset.range (X.J + 3)).biUnion fun r => (Finset.univ : Finset (Fin X.m)).powersetCard r).biUnion
        fun F => (descriptorCodes X (gr.1, fm.1) gr.2 F j).image fun D => (fm.1, fm.2, D)

def descriptorCodeCountBound : ℕ :=
  4 * (X.J + 3) * (X.m + 2) ^ (2 * (X.J + 2)) *
    (2 ^ (1806 * X.T) * (X.T * 4000 * (X.m + 1) ^ 2 + 2) ^ (2 * (1 + 21 * (X.J + 2))))

theorem groupDescriptorShapeCodes_card_le (gr : X.Bin × CubeVertex X.m) :
    (groupDescriptorShapeCodes X gr).card ≤ descriptorCodeCountBound X := by
  let C : ℕ := 2 ^ (1806 * X.T) *
    (X.T * 4000 * (X.m + 1) ^ 2 + 2) ^ (2 * (1 + 21 * (X.J + 2)))
  let Fs : Finset (Finset (Fin X.m)) :=
    (Finset.range (X.J + 3)).biUnion fun r => (Finset.univ : Finset (Fin X.m)).powersetCard r
  let f (fm : KeyFlag6 × Mode6) (j : ℕ) (F : Finset (Fin X.m)) : Finset (DescriptorShape X) :=
    (descriptorCodes X (gr.1, fm.1) gr.2 F j).image fun D => (fm.1, fm.2, D)
  have hf : ∀ fm j F, (f fm j F).card ≤ C := fun fm j F =>
    Finset.card_image_le.trans (descriptorCodes_card_le X (gr.1, fm.1) gr.2 F j)
  have hFs : Fs.card ≤ (X.m + 2) ^ (2 * (X.J + 2)) := by
    simpa [Fs] using S06.Lane_q_s06_steps2.smallPowersetCount6
      (Finset.univ : Finset (Fin X.m)) (X.J + 2)
  have hinner : ∀ fm j, (Fs.biUnion (f fm j)).card ≤ (X.m + 2) ^ (2 * (X.J + 2)) * C := by
    intro fm j
    exact (card_biUnion_le_uniform Fs (f fm j) C (fun F _ => hf fm j F)).trans
      (Nat.mul_le_mul_right C hFs)
  have hmid : ∀ fm,
      ((Finset.range (X.J + 3)).biUnion fun j => Fs.biUnion (f fm j)).card ≤
        (X.J + 3) * ((X.m + 2) ^ (2 * (X.J + 2)) * C) := by
    intro fm
    have hh := card_biUnion_le_uniform (Finset.range (X.J + 3))
      (fun j => Fs.biUnion (f fm j)) _ (fun j _ => hinner fm j)
    simpa only [Finset.card_range] using hh
  have hfm : ((Finset.univ : Finset KeyFlag6).product (Finset.univ : Finset Mode6)).card = 4 := by
    rw [card_product_explicit]
    have hflag : Fintype.card KeyFlag6 = 2 := by decide
    have hmode : Fintype.card Mode6 = 2 := by decide
    simp [hflag, hmode]
  have houter := card_biUnion_le_uniform
    ((Finset.univ : Finset KeyFlag6).product (Finset.univ : Finset Mode6))
    (fun fm => (Finset.range (X.J + 3)).biUnion fun j => Fs.biUnion (f fm j)) _ (fun fm _ => hmid fm)
  simpa only [groupDescriptorShapeCodes, descriptorCodeCountBound, Fs, f, C, hfm, Nat.mul_assoc] using houter

theorem state_flippable_card_le_severity (b : X.State) (hb : b ∈ X.g.L.oddStates) :
    (X.g.L.stFlippable b).card ≤ X.g.L.stSeverity b := by
  rcases Finset.mem_image.mp hb with ⟨x, hx, rfl⟩
  rw [X.facts.flippable_eq x, X.facts.severity_eq x]
  exact flippable_card_le_severity X x

theorem nearGroupDescriptorShapes_subset_codes (gr : X.Bin × CubeVertex X.m) (hn : 4 ≤ n) :
    nearGroupDescriptorShapes X gr ⊆ groupDescriptorShapeCodes X gr := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨b, hb, hq⟩
  rcases Finset.mem_filter.mp hb with ⟨hbOdd, hw, ht, hj⟩
  rcases Finset.mem_image.mp hq with ⟨D, hD, rfl⟩
  have hF : (X.g.L.stFlippable b).card ≤ X.J + 2 :=
    (state_flippable_card_le_severity X b hbOdd).trans hj
  apply Finset.mem_biUnion.mpr
  refine ⟨((X.g.L.stKey b).2, X.stMode b),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
    Finset.mem_biUnion.mpr ⟨X.g.L.stSeverity b, Finset.mem_range.mpr (by omega),
      Finset.mem_biUnion.mpr ⟨X.g.L.stFlippable b, ?_, ?_⟩⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨(X.g.L.stFlippable b).card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  · apply Finset.mem_image.mpr
    refine ⟨D, ?_, rfl⟩
    have hk : X.g.L.stKey b = (gr.1, (X.g.L.stKey b).2) := Prod.ext hw rfl
    have hc := descriptor_mem_codes X b hbOdd hn D hD
    rw [ht] at hc
    exact hk ▸ hc

theorem nearGroupDescriptorShapes_card_le (gr : X.Bin × CubeVertex X.m) (hn : 4 ≤ n) :
    (nearGroupDescriptorShapes X gr).card ≤ descriptorCodeCountBound X :=
  (Finset.card_le_card (nearGroupDescriptorShapes_subset_codes X gr hn)).trans
    (groupDescriptorShapeCodes_card_le X gr)

end
end HypercubeRamsey.Lane_sol_s06_hidden
