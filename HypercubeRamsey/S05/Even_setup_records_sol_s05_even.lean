import HypercubeRamsey.S05.Even_setup_local_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def actualId {h : X.HeightChoice5} (elig : X.CΩ h → h.hp.EligMap) (ω : X.CΩ h)
    (l₀ : h.hp.Loc) (s : X.St.Site) : h.hp.Loc :=
  (h.hp.selection (X.sites h) (Setup5.pos ω) (Setup5.act ω) (elig ω) (Setup5.tie ω) (X.St.oneHot s)).getD l₀

theorem valid_select_actualId (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n)
    (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc) (a : EvenRole5 n) (ha : a ∈ Setup5.evenNbrs b) :
    X.selLong (L.elig H) ω a = some (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1)) := by
  have hs := L.valid_select H ω b hb a ha
  cases hsel : X.selLong (L.elig H) ω a with
  | none => simp [hsel] at hs
  | some l =>
    have hId : actualId X (L.elig H) ω l₀ (X.St.stateOf a.1) = l := by
      change (X.selLong (L.elig H) ω a).getD l₀ = l
      rw [hsel]
      rfl
    rw [hId]

theorem actualRecord_observations (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc) :
    (X.actualRecord (L.elig H) H ω b).2.1 =
      (Setup5.evenNbrs b).image (fun a =>
        (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)) := by
  change (Setup5.evenNbrs b).biUnion _ = _
  calc
    _ = (Setup5.evenNbrs b).biUnion (fun a =>
        {(actualId X (L.elig H) ω l₀ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)}) := by
      apply Finset.biUnion_congr rfl
      intro a ha
      have hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a =
          some (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1)) := valid_select_actualId X L H ω b hb l₀ a ha
      rw [hs]
    _ = _ := Finset.biUnion_singleton

theorem actualRecord_refs (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc) :
    (X.actualRecord (L.elig H) H ω b).2.2.1 =
      ((Setup5.evenNbrs b).filter fun a =>
        X.g.roleKey (X.p.J n) b.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          (X.g.roleKey (X.p.J n) b.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome).image
      (fun a => (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
        X.g.optionalKey (X.p.J n) a.1)) := by
  change (Setup5.evenNbrs b).biUnion _ = _
  let pred := fun a : EvenRole5 n =>
    X.g.roleKey (X.p.J n) b.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
      (X.g.roleKey (X.p.J n) b.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome
  let f := fun a : EvenRole5 n =>
    (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
      X.g.optionalKey (X.p.J n) a.1)
  calc
    _ = (Setup5.evenNbrs b).biUnion (fun a => if pred a then {f a} else ∅) := by
      apply Finset.biUnion_congr rfl
      intro a ha
      have hs : X.selAt (L.elig H) ω L.ht.hp.Rlong a =
          some (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1)) := valid_select_actualId X L H ω b hb l₀ a ha
      rw [hs]
    _ = _ := by
      ext d
      change d ∈ (Setup5.evenNbrs b).biUnion (fun a => if pred a then {f a} else ∅) ↔
        d ∈ ((Setup5.evenNbrs b).filter pred).image f
      constructor
      · intro hd
        obtain ⟨a, ha, hda⟩ := Finset.mem_biUnion.mp hd
        by_cases hp : pred a
        · rw [if_pos hp] at hda
          exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hp⟩, (Finset.mem_singleton.mp hda).symm⟩
        · simp [hp] at hda
      · intro hd
        obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hd
        obtain ⟨ha, hp⟩ := Finset.mem_filter.mp ha
        apply Finset.mem_biUnion.mpr
        refine ⟨a, ha, ?_⟩
        rw [if_pos hp]
        exact Finset.mem_singleton.mpr heq.symm

def selectedIds (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n)
    (l₀ : L.ht.hp.Loc) : Finset L.ht.hp.Loc :=
  (Setup5.evenNbrs b).image (fun a => actualId X (L.elig H) ω l₀ (X.St.stateOf a.1))

theorem selectedIds_card (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc) :
    (selectedIds X L H ω b l₀).card ≤ X.p.T n := by
  have heq : selectedIds X L H ω b l₀ =
      ((Setup5.evenNbrs b).image (fun a => X.selLong (L.elig H) ω a)).image (fun l => l.getD l₀) := by
    simp only [selectedIds, Finset.image_image]
    rfl
  rw [heq]
  exact Finset.card_image_le.trans (L.valid_T H ω b hb)

theorem low_optional_none (v : CubeVertex n) (hv : X.g.low (X.p.J n) v) :
    X.g.optionalKey (X.p.J n) v = none := by
  have hsev : X.g.severity v ≤ X.p.J n := hv
  have hne : X.g.severity v ≠ X.p.J n + 1 := by omega
  simp [ChunkGeometry5.optionalKey, hne]

theorem selected_low_ref_mem {h : X.HeightChoice5} (H : X.KeyHist) (ω : X.CΩ h)
    (elig : X.CΩ h → h.hp.EligMap) (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h)
    (hadj : (cube n).Adj v.1 b.1) (hv : X.g.low (X.p.J n) v.1) (hb : X.g.low (X.p.J n) b.1)
    (hc : X.evenRefOf elig H ω v = some c) :
    (c.1, X.g.evenType (X.p.J n) v.1, c.2) ∈ X.refsOn H (X.actualRecord elig H ω b) (Setup5.arraysOf ω) := by
  letI : DecidableEq (X.Ty × Finset (Fin X.blockBound)) := Classical.decEq _
  have hkey : X.g.roleKey (X.p.J n) b.1 ∈ (X.g.evenType (X.p.J n) v.1).2.1 := by
    have hcover := (L5_1e_cover X.g (X.p.J n)).1 v.1 b.1 hadj
    rcases hcover with hkey | hopt
    · exact hkey
    · rw [low_optional_none X v.1 hv] at hopt
      cases hopt
  have hmode : (X.g.roleKey (X.p.J n) b.1).isLeft = (X.g.evenType (X.p.J n) v.1).2.2.isSome := by
    have hv' : X.g.severity v.1 ≤ X.p.J n := hv
    have hb' : X.g.severity b.1 ≤ X.p.J n := hb
    simp [ChunkGeometry5.roleKey, ChunkGeometry5.evenType, hv', hb']
  unfold Setup5.evenRefOf at hc
  obtain ⟨l, hl, he⟩ := Option.map_eq_some_iff.mp hc
  have hsel : X.selAt elig ω h.hp.Rlong v = some l := hl
  have hnb : v ∈ Setup5.evenNbrs b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
  unfold Setup5.refsOn
  apply Finset.mem_image.mpr
  refine ⟨(l, X.g.evenType (X.p.J n) v.1, X.g.optionalKey (X.p.J n) v.1), ?_, ?_⟩
  · change _ ∈ (Setup5.evenNbrs b).biUnion _
    apply Finset.mem_biUnion.mpr
    exact ⟨v, hnb, by simp [hsel, hkey, hmode]⟩
  · rw [← he]
    rfl

theorem high_low_optional_key (a : EvenRole5 n) (b : OddRole5 n)
    (hadj : (cube n).Adj a.1 b.1) (ha : ¬ X.g.low (X.p.J n) a.1) (hb : X.g.low (X.p.J n) b.1) :
    X.g.optionalKey (X.p.J n) a.1 = some (X.g.roleKey (X.p.J n) b.1) := by
  have hcover := (L5_1e_cover X.g (X.p.J n)).1 a.1 b.1 hadj
  rcases hcover with hkey | hopt
  · have ha' : ¬ X.g.severity a.1 ≤ X.p.J n := ha
    have hb' : X.g.severity b.1 ≤ X.p.J n := hb
    simp only [ChunkGeometry5.typeKeys, if_neg ha'] at hkey
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hkey
    have hflag := congrArg Sum.isLeft heq
    simp [ChunkGeometry5.roleKey, hb'] at hflag
  · exact hopt

def candidatePositions (L : X.CentreLayer5) (ω : X.CΩ L.ht) (b : OddRole5 n) : Finset L.ht.hp.Loc :=
  (Setup5.evenNbrs b).biUnion fun a => Finset.univ.filter fun l : L.ht.hp.Loc =>
    Setup5.pos ω l = true ∧ hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r

theorem selectedIds_candidate (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc) :
    selectedIds X L H ω b l₀ ⊆ candidatePositions X L ω b := by
  intro l hl
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
  have hsel := valid_select_actualId X L H ω b hb l₀ a ha
  have hshape := selection_some_shape L.ht.hp (X.sites L.ht) (Setup5.pos ω) (Setup5.act ω)
    (L.elig H ω) (Setup5.tie ω) (X.siteOf a) (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1))
    (L.elig_shape H ω (X.siteOf a)) hsel
  apply Finset.mem_biUnion.mpr
  exact ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshape⟩⟩

theorem neighbor_sites_distance (v a : EvenRole5 n) (b : OddRole5 n)
    (hv : v ∈ Setup5.evenNbrs b) (ha : a ∈ Setup5.evenNbrs b) :
    _root_.hammingDist (X.siteOf a) (X.siteOf v) ≤ 8 := by
  have hna : X.St.stateOf a.1 ∈ X.St.neighbors (X.St.stateOf b.1) := by
    apply (X.St.mem_neighbors _ _).mpr
    exact ⟨b.1, a.1, rfl, rfl, (Finset.mem_filter.mp ha).2.symm⟩
  have hnv : X.St.stateOf v.1 ∈ X.St.neighbors (X.St.stateOf b.1) := by
    apply (X.St.mem_neighbors _ _).mpr
    exact ⟨b.1, v.1, rfl, rfl, (Finset.mem_filter.mp hv).2.symm⟩
  exact X.St.even_distance _ _ _ hna hnv ⟨a.1, rfl, a.2⟩ ⟨v.1, rfl, v.2⟩

theorem candidatePositions_scope (L : X.CentreLayer5) (ω : X.CΩ L.ht) (v : EvenRole5 n)
    (b : OddRole5 n) (hv : v ∈ Setup5.evenNbrs b) :
    candidatePositions X L ω b ⊆ X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8) := by
  intro l hl
  obtain ⟨a, ha, hla⟩ := Finset.mem_biUnion.mp hl
  have hd : _root_.hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r := (Finset.mem_filter.mp hla).2.2
  have hsites := neighbor_sites_distance X v a b hv ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  change _root_.hammingDist l.1 (X.siteOf v) ≤ L.ht.hp.r + L.slack + 8
  calc
    _root_.hammingDist l.1 (X.siteOf v) ≤ _root_.hammingDist l.1 (X.siteOf a) +
        _root_.hammingDist (X.siteOf a) (X.siteOf v) := _root_.hammingDist_triangle _ _ _
    _ ≤ L.ht.hp.r + 8 := Nat.add_le_add hd hsites
    _ ≤ _ := by omega

theorem local_position_count (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n)
    (hb : L.valid H ω b) (a : EvenRole5 n) (ha : a ∈ Setup5.evenNbrs b) :
    ((Finset.univ.filter fun l : L.ht.hp.Loc =>
      Setup5.pos ω l = true ∧ hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r).card : ℝ) ≤
        (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam) := by
  have heq : ((Finset.univ.filter fun l : L.ht.hp.Loc =>
      Setup5.pos ω l = true ∧ hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r).card : ℝ) =
      ∑ j : Fin (L.ht.hp.H + 1), ((Finset.univ.filter fun u : CubeVertex L.ht.hp.d =>
        Setup5.pos ω (u, j) = true ∧ hammingDist u (X.siteOf a) ≤ L.ht.hp.r).card : ℝ) := by
    rw [← Finset.sum_boole, Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [Finset.sum_boole]
  rw [heq]
  calc
    _ ≤ ∑ _j : Fin (L.ht.hp.H + 1), 2 * L.ht.hp.lam :=
      Finset.sum_le_sum fun j _ => L.valid_counts H ω b hb a ha j
    _ = _ := by simp

theorem candidatePositions_card (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n)
    (hb : L.valid H ω b) :
    ((candidatePositions X L ω b).card : ℝ) ≤ (n : ℝ) * (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam) := by
  have hcard : (candidatePositions X L ω b).card ≤
      ∑ a ∈ Setup5.evenNbrs b, (Finset.univ.filter fun l : L.ht.hp.Loc =>
        Setup5.pos ω l = true ∧ hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r).card := Finset.card_biUnion_le
  have hcardR : ((candidatePositions X L ω b).card : ℝ) ≤
      ∑ a ∈ Setup5.evenNbrs b, ((Finset.univ.filter fun l : L.ht.hp.Loc =>
        Setup5.pos ω l = true ∧ hammingDist l.1 (X.siteOf a) ≤ L.ht.hp.r).card : ℝ) := by exact_mod_cast hcard
  refine hcardR.trans ?_
  calc
    _ ≤ ∑ _a ∈ Setup5.evenNbrs b, (L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam) :=
      Finset.sum_le_sum fun a ha => local_position_count X L H ω b hb a ha
    _ = ((Setup5.evenNbrs b).card : ℝ) * ((L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)) := by simp
    _ ≤ (n : ℝ) * ((L.ht.hp.H + 1 : ℕ) * (2 * L.ht.hp.lam)) := by
      have hlam : 0 ≤ L.ht.hp.lam := Real.rpow_nonneg (Nat.cast_nonneg n) 10
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hlam))
      exact_mod_cast Lane_sol_s05_hist1b.evenNbrs_card_le b
    _ = _ := by ring

def liftRecord {I I' : Type} (r : X.RecordOn I) (place : I → I') : X.RecordOn I' :=
  (r.1, r.2.1.image (fun c => (place c.1, c.2)),
    r.2.2.1.image (fun c => (place c.1, c.2.1, c.2.2)),
    r.2.2.2.map (fun c => (place c.1, c.2.1, c.2.2)))

theorem image_classical {A B : Type*} (d : DecidableEq B) (f : A → B) (S : Finset A) :
    @Finset.image A B d f S = @Finset.image A B (Classical.decEq B) f S := by
  have hd : d = Classical.decEq B := Subsingleton.elim _ _
  cases hd
  rfl

theorem liftRecord_from {I I' : Type} (r : X.RecordOn I) (place : I → I')
    (b : OddRole5 n) (μ : X.St.Site → I) (hr : X.RecordFrom r b μ) :
    X.RecordFrom (liftRecord X r place) b (place ∘ μ) := by
  rcases r with ⟨key, obs, refs, mask⟩
  obtain ⟨hk, ho, hd, hm⟩ := hr
  unfold Setup5.RecordFrom liftRecord
  dsimp only
  refine ⟨hk, ?_, ?_, ?_⟩
  · simp only [image_classical] at ho ⊢
    rw [ho]
    simp only [Finset.image_image, Function.comp_def, image_classical]
  · simp only [image_classical] at hd ⊢
    rw [hd]
    simp only [Finset.image_image, Function.comp_def, image_classical]
  · cases hmask : mask with
    | none => simpa only [hmask, Option.map_none] using hm
    | some c =>
      obtain ⟨i, K, M⟩ := c
      rw [hmask] at hm
      obtain ⟨hleft, a, ha, hK, hnone, hi, hlegit⟩ := hm
      simp only [Option.map_some]
      exact ⟨hleft, a, ha, hK, hnone, congrArg place hi, hlegit⟩

theorem record_mask_observed {I : Type} (r : X.RecordOn I) (b : OddRole5 n) (μ : X.St.Site → I)
    (hr : X.RecordFrom r b μ) (c : I × X.Ty) (M : Finset (Fin X.blockBound))
    (hc : r.2.2.2 = some (c.1, c.2, M)) : c ∈ r.2.1 := by
  letI : DecidableEq (I × X.Ty) := Classical.decEq _
  have hm := hr.2.2.2
  rw [hc] at hm
  obtain ⟨_, a, ha, hK, _, hi, _⟩ := hm
  have ho := hr.2.1
  simp only [image_classical] at ho
  rw [ho]
  have hmem : c ∈ @Finset.image _ _ (Classical.decEq (I × X.Ty))
      (fun a : EvenRole5 n => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)) (Setup5.evenNbrs b) := by
    exact Finset.mem_image.mpr ⟨a, ha, Prod.ext hi.symm hK.symm⟩
  exact hmem

theorem finite_id_factor {B : Type*} [DecidableEq B] (U : Finset B) (T : ℕ)
    (hcard : U.card ≤ T) (b₀ : B) (hb₀ : b₀ ∈ U) :
    ∃ (index : B → Fin T) (place : Fin T → B),
      (∀ b ∈ U, place (index b) = b) ∧ (∀ i, place i ∈ U) := by
  classical
  have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨b₀, hb₀⟩
  have hTpos : 0 < T := hUpos.trans_le hcard
  let e : U ≃ Fin U.card := U.equivFin
  let index : B → Fin T := fun b =>
    if hb : b ∈ U then Fin.castLE hcard (e ⟨b, hb⟩) else ⟨0, hTpos⟩
  let place : Fin T → B := fun i =>
    if hi : i.val < U.card then (e.symm ⟨i.val, hi⟩).1 else b₀
  refine ⟨index, place, ?_, ?_⟩
  · intro b hb
    have hi : (e ⟨b, hb⟩).val < U.card := (e ⟨b, hb⟩).isLt
    simp only [index, dif_pos hb, place, Fin.val_castLE, dif_pos hi]
    have hFin : (⟨(e ⟨b, hb⟩).val, hi⟩ : Fin U.card) = e ⟨b, hb⟩ := rfl
    rw [hFin, e.symm_apply_apply]
  · intro i
    dsimp [place]
    split_ifs with hi
    · exact (e.symm ⟨i.val, hi⟩).2
    · exact hb₀

theorem liftRecord_comp {I I' I'' : Type}
    (r : X.RecordOn I) (f : I → I') (g : I' → I'') :
    liftRecord X (liftRecord X r f) g = liftRecord X r (g ∘ f) := by
  unfold liftRecord
  simp only [Finset.image_image, Option.map_map]
  rfl

theorem liftRecord_eq_of_ids {I : Type} (r : X.RecordOn I) (f : I → I)
    (hobs : ∀ c ∈ r.2.1, f c.1 = c.1)
    (href : ∀ c ∈ r.2.2.1, f c.1 = c.1)
    (hmask : ∀ c, r.2.2.2 = some c → f c.1 = c.1) : liftRecord X r f = r := by
  have ho : r.2.1.image (fun c => (f c.1, c.2)) = r.2.1 := by
    have heq : r.2.1.image (fun c => (f c.1, c.2)) = r.2.1.image id :=
      Finset.image_congr (fun c hc => Prod.ext (hobs c hc) rfl)
    exact heq.trans Finset.image_id
  have hr : r.2.2.1.image (fun c => (f c.1, c.2.1, c.2.2)) = r.2.2.1 := by
    have heq : r.2.2.1.image (fun c => (f c.1, c.2.1, c.2.2)) = r.2.2.1.image id :=
      Finset.image_congr (fun c hc => Prod.ext (href c hc) rfl)
    exact heq.trans Finset.image_id
  have hm : r.2.2.2.map (fun c => (f c.1, c.2.1, c.2.2)) = r.2.2.2 := by
    cases hc : r.2.2.2 with
    | none => rfl
    | some c => simp only [Option.map_some]; congr 1; exact Prod.ext (hmask c hc) rfl
  unfold liftRecord
  rw [ho, hr, hm]

theorem valid_high_hits (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht) (b : OddRole5 n)
    (hb : L.valid H ω b) (a : EvenRole5 n) (ha : a ∈ Setup5.evenNbrs b)
    (hhigh : ¬ X.g.low (X.p.J n) a.1) (hblow : X.g.low (X.p.J n) b.1)
    (l : L.ht.hp.Loc) (hsel : X.selLong (L.elig H) ω a = some l)
    (k : CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 1))
    (hkey : X.g.roleKey (X.p.J n) b.1 = .inl k) :
    X.p.usedBlocks n ≤ (X.hitSet (Setup5.arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card := by
  have hopt := high_low_optional_key X a b (Finset.mem_filter.mp ha).2 hhigh hblow
  rw [hkey] at hopt
  exact L.valid_hits H ω b hb a ha l k hsel hopt

theorem first_hits_legit {I : Type} (a : X.ArraysOn I) (c : I × X.Ty) (y : Fin N)
    (htype : c.2.2.2 = none) (hcard : X.p.usedBlocks n ≤ (X.hitSet a c y).card) :
    X.LegitRef c.2 (X.firstK (X.hitSet a c y) (X.p.usedBlocks n)) := by
  unfold Setup5.LegitRef
  rw [htype]
  constructor
  · rw [Lane_sol_s05_1f.firstK_card, Nat.min_eq_left hcard]
  · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

theorem actualRecord_from_of_mask (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc)
    (hmask : match (X.actualRecord (L.elig H) H ω b).2.2.2 with
      | none => (X.actualRecord (L.elig H) H ω b).1.isLeft →
        ∀ a ∈ Setup5.evenNbrs b, (X.g.evenType (X.p.J n) a.1).2.2.isSome
      | some (i, K, M) => (X.actualRecord (L.elig H) H ω b).1.isLeft ∧
        ∃ a ∈ Setup5.evenNbrs b, K = X.g.evenType (X.p.J n) a.1 ∧ K.2.2 = none ∧
          i = actualId X (L.elig H) ω l₀ (X.St.stateOf a.1) ∧ X.LegitRef K M) :
    X.RecordFrom (X.actualRecord (L.elig H) H ω b) b (actualId X (L.elig H) ω l₀) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have ho := actualRecord_observations X L H ω b hb l₀
    simpa only [image_classical] using ho
  · have hr := actualRecord_refs X L H ω b hb l₀
    simpa only [image_classical, Setup5.actualRecord, Setup5.actualRecordAt] using hr
  · cases hx : (X.actualRecord (L.elig H) H ω b).2.2.2 with
    | none =>
      rw [hx] at hmask
      intro hl a ha
      exact hmask hl a ha
    | some c =>
      obtain ⟨i, K, M⟩ := c
      rw [hx] at hmask
      obtain ⟨hl, a, ha, hK, hn, hi, hlegit⟩ := hmask
      exact ⟨hl, a, ha, hK, hn, hi, hlegit⟩

theorem actualRecord_from (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (b : OddRole5 n) (hb : L.valid H ω b) (l₀ : L.ht.hp.Loc) :
    X.RecordFrom (X.actualRecord (L.elig H) H ω b) b (actualId X (L.elig H) ω l₀) := by
  apply actualRecord_from_of_mask X L H ω b hb l₀
  cases hkey : X.g.roleKey (X.p.J n) b.1 with
  | inr k => simp [Setup5.actualRecord, Setup5.actualRecordAt, hkey]
  | inl k =>
    have hblow : X.g.low (X.p.J n) b.1 := by
      by_contra hhigh
      have hsev : ¬ X.g.severity b.1 ≤ X.p.J n := hhigh
      simp [ChunkGeometry5.roleKey, hsev] at hkey
    by_cases hex : ∃ a ∈ Setup5.evenNbrs b,
        (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (X.selAt (L.elig H) ω L.ht.hp.Rlong a).isSome
    · let a := Classical.choose hex
      have ha := Classical.choose_spec hex
      have hsel : X.selAt (L.elig H) ω L.ht.hp.Rlong a =
          some (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1)) := valid_select_actualId X L H ω b hb l₀ a ha.1
      have hhigh : ¬ X.g.low (X.p.J n) a.1 := by
        intro hlow
        have hsev : X.g.severity a.1 ≤ X.p.J n := hlow
        have hnone := ha.2.1
        have hsome : (X.g.evenType (X.p.J n) a.1).2.2.isSome := by
          change (if h : X.g.severity a.1 ≤ X.p.J n then
            (some (⟨X.g.severity a.1, Nat.lt_succ_of_le h⟩ : Fin (X.p.J n + 1))) else none).isSome
          rw [dif_pos hsev]
          rfl
        rw [hnone] at hsome
        cases hsome
      have hhits := valid_high_hits X L H ω b hb a ha.1 hhigh hblow
        (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1)) hsel k hkey
      have hlegit := first_hits_legit X (Setup5.arraysOf ω)
        (actualId X (L.elig H) ω l₀ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)
        (X.lowCol H.2 k) ha.2.1 hhits
      simp only [Setup5.actualRecord, Setup5.actualRecordAt, hkey, dif_pos hex]
      rw [hsel]
      exact ⟨rfl, a, ha.1, rfl, ha.2.1, rfl, hlegit⟩
    · simp only [Setup5.actualRecord, Setup5.actualRecordAt, hkey, dif_neg hex]
      intro _ a ha
      cases htype : (X.g.evenType (X.p.J n) a.1).2.2 with
      | some j => simp [htype]
      | none =>
        apply (hex ⟨a, ha, htype, ?_⟩).elim
        exact L.valid_select H ω b hb a ha

theorem candidatePositions_local (L : X.CentreLayer5) (v : EvenRole5 n) (b : OddRole5 n)
    (hv : v ∈ Setup5.evenNbrs b) :
    FinProb.DependsOn (fun ω : X.CΩ L.ht => candidatePositions X L ω b)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8)) := by
  intro ω ω' hagree
  apply Finset.ext
  intro l
  constructor
  · intro hl
    have hscope := candidatePositions_scope X L ω v b hv hl
    have heq := hagree l hscope
    obtain ⟨a, ha, hla⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hla
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hd⟩⟩
    exact (congrArg (fun x : X.CVal L.ht => x.1) heq).symm.trans hp
  · intro hl
    have hscope := candidatePositions_scope X L ω' v b hv hl
    have heq := hagree l hscope
    obtain ⟨a, ha, hla⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨_, hp, hd⟩ := Finset.mem_filter.mp hla
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hd⟩⟩
    exact (congrArg (fun x : X.CVal L.ht => x.1) heq).trans hp

theorem liftRecord_inverse {I I' : Type} (r : X.RecordOn I) (index : I → I') (place : I' → I)
    (b : OddRole5 n) (μ : X.St.Site → I) (hr : X.RecordFrom r b μ)
    (hinv : ∀ a ∈ Setup5.evenNbrs b, place (index (μ (X.St.stateOf a.1))) = μ (X.St.stateOf a.1)) :
    liftRecord X (liftRecord X r index) place = r := by
  rw [liftRecord_comp]
  apply liftRecord_eq_of_ids X r (place ∘ index)
  · intro c hc
    have ho := hr.2.1
    simp only [image_classical] at ho
    rw [ho] at hc
    letI : DecidableEq (I × X.Ty) := Classical.decEq _
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hc
    have hi := congrArg Prod.fst heq
    rw [← hi]
    exact hinv a ha
  · intro c hc
    have hd := hr.2.2.1
    simp only [image_classical] at hd
    rw [hd] at hc
    letI : DecidableEq (I × X.Ty × Option X.Key) := Classical.decEq _
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hc
    have hi := congrArg Prod.fst heq
    rw [← hi]
    exact hinv a (Finset.mem_filter.mp ha).1
  · intro c hc
    have hm := hr.2.2.2
    rw [hc] at hm
    obtain ⟨_, a, ha, hK, hnone, hi, hlegit⟩ := hm
    rw [hi]
    exact hinv a ha

end
end HypercubeRamsey.Lane_sol_s05_even
