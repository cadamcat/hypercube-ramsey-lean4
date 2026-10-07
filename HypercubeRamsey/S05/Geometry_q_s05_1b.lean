import HypercubeRamsey.S05.Parents
import HypercubeRamsey.S06.ChunkGeometry_q_s06_front

set_option maxRecDepth 4096

/-!
Lane-local finite-coordinate facts for the chunk layout proof in `Geometry.lean`.
-/

namespace HypercubeRamsey.Lane_q_s05_1b

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

abbrev coarseChunkCount : ℕ := 300

def flipVertex {n : ℕ} (x : CubeVertex n) (a : Fin n) : CubeVertex n :=
  Function.update x a (!x a)

/-- Coordinate labels for 300 coarse blocks, `m` fine blocks, and the residual block. -/
abbrev PartIndex (k m ell r : ℕ) :=
  (Fin 300 × Fin k) ⊕ ((Fin m × Fin ell) ⊕ Fin r)

/-- An equivalence from cube coordinates to a block-index type of the same cardinality. -/
noncomputable def coordinateEquiv (n k m ell r : ℕ)
    (h : n = 300 * k + (m * ell + r)) : Fin n ≃ PartIndex k m ell r := by
  have hcard : Fintype.card (Fin n) = Fintype.card (PartIndex k m ell r) := by
    simp [PartIndex, Fintype.card_fin]
    omega
  exact Fintype.equivOfCardEq hcard

/-- The image of one coarse block under a coordinate equivalence. -/
def coarseBlock {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin 300) : Finset (Fin n) :=
  Finset.univ.image fun j : Fin k => e.symm (.inl (i, j))

/-- The image of one fine block under a coordinate equivalence. -/
def fineBlock {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin m) : Finset (Fin n) :=
  Finset.univ.image fun j : Fin ell => e.symm (.inr (.inl (i, j)))

/-- The residual coordinates under a coordinate equivalence. -/
def residualBlock {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r) : Finset (Fin n) :=
  Finset.univ.image fun j : Fin r => e.symm (.inr (.inr j))

theorem coarseBlock_card {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin 300) : (coarseBlock e i).card = k := by
  classical
  have hi : Function.Injective (fun j : Fin k => e.symm (.inl (i, j))) := by
    intro a b hab
    apply Fin.ext
    have hpair : (i, a) = (i, b) := Sum.inl.inj (e.symm.injective hab)
    exact congrArg Fin.val (congrArg Prod.snd hpair)
  dsimp [coarseBlock]
  rw [Finset.card_image_of_injective _ hi]
  simp

theorem fineBlock_card {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin m) : (fineBlock e i).card = ell := by
  classical
  have hi : Function.Injective (fun j : Fin ell => e.symm (.inr (.inl (i, j)))) := by
    intro a b hab
    apply Fin.ext
    have hinner : Sum.inl (i, a) = Sum.inl (i, b) := Sum.inr.inj (e.symm.injective hab)
    have hpair : (i, a) = (i, b) := Sum.inl.inj hinner
    exact congrArg Fin.val (congrArg Prod.snd hpair)
  dsimp [fineBlock]
  rw [Finset.card_image_of_injective _ hi]
  simp

theorem residualBlock_card {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r) :
    (residualBlock e).card = r := by
  classical
  have hi : Function.Injective (fun j : Fin r => e.symm (.inr (.inr j))) := by
    intro a b hab
    apply Fin.ext
    exact congrArg Fin.val (Sum.inr.inj (Sum.inr.inj (e.symm.injective hab)))
  dsimp [residualBlock]
  rw [Finset.card_image_of_injective _ hi]
  simp

theorem coarseBlocks_disjoint {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i j : Fin 300) (hij : i ≠ j) : Disjoint (coarseBlock e i) (coarseBlock e j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have h := congrArg e heq
  simp at h
  exact hij h.1.symm

theorem coarseFine_disjoint {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin 300) (j : Fin m) : Disjoint (coarseBlock e i) (fineBlock e j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have h := congrArg e heq
  simp at h

theorem fineBlocks_disjoint {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i j : Fin m) (hij : i ≠ j) : Disjoint (fineBlock e i) (fineBlock e j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have h := congrArg e heq
  simp at h
  exact hij h.1.symm

theorem coarseResidual_disjoint {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin 300) : Disjoint (coarseBlock e i) (residualBlock e) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have h := congrArg e heq
  simp at h

theorem fineResidual_disjoint {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r)
    (i : Fin m) : Disjoint (fineBlock e i) (residualBlock e) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a ha hb
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨v, hv, heq⟩
  have h := congrArg e heq
  simp at h

theorem blocks_cover {n k m ell r : ℕ} (e : Fin n ≃ PartIndex k m ell r) :
    (Finset.univ.biUnion (coarseBlock e) ∪ Finset.univ.biUnion (fineBlock e)) ∪
      residualBlock e = Finset.univ := by
  classical
  ext a
  constructor
  · intro _
    simp
  · intro ha
    cases hpart : e a with
    | inl p =>
        rcases p with ⟨i, j⟩
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_biUnion.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨j, Finset.mem_univ _, ?_⟩
        calc
          e.symm (.inl (i, j)) = e.symm (e a) := congrArg e.symm hpart.symm
          _ = a := e.symm_apply_apply a
    | inr q =>
        cases q with
        | inl p =>
            rcases p with ⟨i, j⟩
            apply Finset.mem_union.mpr
            left
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_biUnion.mpr
            refine ⟨i, Finset.mem_univ _, ?_⟩
            apply Finset.mem_image.mpr
            refine ⟨j, Finset.mem_univ _, ?_⟩
            calc
              e.symm (.inr (.inl (i, j))) = e.symm (e a) := congrArg e.symm hpart.symm
              _ = a := e.symm_apply_apply a
        | inr j =>
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_image.mpr
            refine ⟨j, Finset.mem_univ _, ?_⟩
            calc
              e.symm (.inr (.inr j)) = e.symm (e a) := congrArg e.symm hpart.symm
              _ = a := e.symm_apply_apply a


/-- A chunk-only view used to prove the severity estimate independently of the section layout record. -/
structure FineLayout (n : ℕ) where
  m : ℕ
  fineLength : ℕ
  coarseChunks : Fin 300 → Finset (Fin n)
  fineChunks : Fin m → Finset (Fin n)
  residual : Finset (Fin n)
  chunks_disjoint : (∀ i j, i ≠ j → Disjoint (coarseChunks i) (coarseChunks j)) ∧
    (∀ i j, Disjoint (coarseChunks i) (fineChunks j)) ∧
    (∀ i j, i ≠ j → Disjoint (fineChunks i) (fineChunks j)) ∧
    (∀ i, Disjoint (coarseChunks i) residual) ∧
    (∀ i, Disjoint (fineChunks i) residual)
  fine_length_lower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ fineLength
  fine_chunk_length : ∀ i, (fineChunks i).card = fineLength

namespace FineLayout

def fineCount {n : ℕ} (L : FineLayout n) (x : CubeVertex n) (i : Fin L.m) : ℕ :=
  ((L.fineChunks i).filter fun a => x a = true).card

def severity {n : ℕ} (L : FineLayout n) (x : CubeVertex n) : ℕ :=
  (Finset.univ.filter fun i : Fin L.m =>
    Nat.dist (2 * L.fineCount x i) L.fineLength ≤ 11).card

end FineLayout

/-- The Section 5 severity tail, proved for any disjoint fine chunk layout. -/
theorem fineSeverityTail (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 50) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : FineLayout n,
      L.m = ⌈(n : ℝ) ^ α⌉₊ → ∀ q, 1 ≤ q → q ≤ L.m →
      ((Finset.univ.filter fun x : CubeVertex n => q ≤ L.severity x).card : ℝ) /
        (2 : ℝ) ^ n ≤ (n : ℝ) ^ (-(13 / 100 : ℝ) * q) := by
  have hslack : 0 < 1 / 50 - α := by linarith
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, 92 < (n : ℝ) ^ (1 / 50 - α) := by
    have htend := (tendsto_rpow_atTop hslack).comp tendsto_natCast_atTop_atTop
    exact htend.eventually (Filter.eventually_gt_atTop 92)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop 2).and hevent)
  refine ⟨n₀, ?_⟩
  intro n hn L hL q hq1 hqm
  have hlarge := hn₀ n hn
  have hn2 : 2 ≤ n := hlarge.1
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnRpos : 0 < (n : ℝ) := by positivity
  have hnPow : 92 < (n : ℝ) ^ (1 / 50 - α) := hlarge.2
  let ell : ℕ := L.fineLength
  have hellR : (n : ℝ) ^ (3 / 10 : ℝ) ≤ (ell : ℝ) := by
    simpa [ell] using L.fine_length_lower
  have hellPos : 0 < ell := by
    have hpow : 1 ≤ (n : ℝ) ^ (3 / 10 : ℝ) := Real.one_le_rpow hnR (by norm_num)
    have hreal : (1 : ℝ) ≤ (ell : ℝ) := hpow.trans hellR
    exact_mod_cast (show (0 : ℝ) < (ell : ℝ) by linarith)
  let Coord (i : Fin L.m) := {a : Fin n // a ∈ L.fineChunks i}
  let weight (i : Fin L.m) (f : Coord i → Bool) :=
    HypercubeRamsey.Lane_q_s06_front.boolWeight f
  let severePatterns (i : Fin L.m) : Finset (Coord i → Bool) :=
    Finset.univ.filter fun f => Nat.dist (2 * weight i f) ell ≤ 11
  have hCoordCard (i : Fin L.m) : Fintype.card (Coord i) = ell := by
    simp [Coord, ell, Fintype.card_coe, L.fine_chunk_length i]
  have hWeightBound (i : Fin L.m) (f : Coord i → Bool) : weight i f ≤ ell := by
    calc
      weight i f ≤ Fintype.card (Coord i) := by
        exact Finset.card_filter_le _ _
      _ = ell := hCoordCard i
  have hLevelsCard (levels : Finset ℕ)
      (hle : levels ⊆ Finset.range (ell + 1))
      (hdist : ∀ q ∈ levels, Nat.dist (2 * q) ell ≤ 11) : levels.card ≤ 23 := by
    let R : Finset (Fin (ell + 12)) :=
      Finset.univ.filter fun r => Nat.dist r.val ell ≤ 11
    have hRcard : R.card ≤ 23 := by
      simpa [R, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (HypercubeRamsey.Lane_q_s06_front.finDistFilterCard_le
          (N := ell + 11) (r := 11) ⟨ell, by omega⟩)
    let f (q : ℕ) (hq : q ∈ levels) : Fin (ell + 12) :=
      ⟨2 * q, by
        have hqle : q ≤ ell := by
          have := Finset.mem_range.mp (hle hq)
          omega
        have h := hdist q hq
        unfold Nat.dist at h
        omega⟩
    have hImage :
        levels.attach.image (fun q => f q.1 q.2) ⊆ R := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨q, hq, rfl⟩
      have h := hdist q.1 q.2
      simp [R, f, h]
    have hfInj : Function.Injective (fun q : {q : ℕ // q ∈ levels} => f q.1 q.2) := by
      intro a b hab
      apply Subtype.ext
      have hval := congrArg Fin.val hab
      dsimp [f] at hval
      omega
    have hImageCard : (levels.attach.image (fun q => f q.1 q.2)).card = levels.card := by
      calc
        (levels.attach.image (fun q => f q.1 q.2)).card = levels.attach.card :=
          Finset.card_image_of_injective _ hfInj
        _ = levels.card := by simp
    calc
      levels.card = (levels.attach.image (fun q => f q.1 q.2)).card := hImageCard.symm
      _ ≤ R.card := Finset.card_le_card hImage
      _ ≤ 23 := hRcard
  have hLayer (i : Fin L.m) (q : ℕ) :
      (Finset.univ.filter fun f : Coord i → Bool => weight i f = q).card =
        Nat.choose ell q := by
    calc
      (Finset.univ.filter fun f : Coord i → Bool => weight i f = q).card =
          Fintype.card {f : Coord i → Bool // weight i f = q} := by
            symm
            simpa using (Fintype.card_subtype fun f : Coord i → Bool => weight i f = q)
      _ = Nat.choose (Fintype.card (Coord i)) q := by
            simpa [weight] using
              (HypercubeRamsey.Lane_q_s06_front.boolWeightLayerCard (Coord i) q)
      _ = Nat.choose ell q := by rw [hCoordCard]
  have hSevereCard (i : Fin L.m) :
      ((severePatterns i).card : ℝ) ≤ 46 * (2 : ℝ) ^ ell / Real.sqrt ell := by
    let levels : Finset ℕ := (Finset.range (ell + 1)).filter fun q =>
      Nat.dist (2 * q) ell ≤ 11
    let layer (q : ℕ) : Finset (Coord i → Bool) :=
      Finset.univ.filter fun f => weight i f = q
    have hlevels : levels.card ≤ 23 := by
      exact hLevelsCard levels (Finset.filter_subset _ _) (by
        intro q hq
        exact (Finset.mem_filter.mp hq).2)
    have hUnion : severePatterns i = levels.biUnion layer := by
      ext f
      simp only [severePatterns, Finset.mem_filter, Finset.mem_biUnion,
        Finset.mem_univ, true_and, levels, layer]
      constructor
      · intro hf
        refine ⟨weight i f, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_of_le (hWeightBound i f), hf⟩
        · rfl
      · rintro ⟨q, hq, rfl⟩
        exact hq.2
    have hcardNat :
        (severePatterns i).card ≤ ∑ q ∈ levels, (layer q).card := by
      rw [hUnion]
      exact Finset.card_biUnion_le
    have hcardReal :
        ((severePatterns i).card : ℝ) ≤ ∑ q ∈ levels, ((layer q).card : ℝ) := by
      exact_mod_cast hcardNat
    have hsumBound :
        (∑ q ∈ levels, ((layer q).card : ℝ)) ≤
          (levels.card : ℝ) * ((2 / Real.sqrt ell) * (2 : ℝ) ^ ell) := by
      calc
        (∑ q ∈ levels, ((layer q).card : ℝ)) ≤
            ∑ q ∈ levels, ((2 / Real.sqrt ell) * (2 : ℝ) ^ ell) :=
          Finset.sum_le_sum (fun q hq => by
            have hqle : q ≤ ell := by
              have hq' := (Finset.mem_filter.mp hq).1
              simp only [Finset.mem_range] at hq'
              omega
            have hcentral := centralBinomialUpper ell hellPos q hqle
            have hmul := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ ell)).1 hcentral
            rw [hLayer i q]
            push_cast at hmul ⊢
            nlinarith [hmul])
        _ = (levels.card : ℝ) * ((2 / Real.sqrt ell) * (2 : ℝ) ^ ell) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    have hlevelBound :
        (levels.card : ℝ) * ((2 / Real.sqrt ell) * (2 : ℝ) ^ ell) ≤
          23 * ((2 / Real.sqrt ell) * (2 : ℝ) ^ ell) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hlevels) (by positivity)
    calc
      ((severePatterns i).card : ℝ) ≤
          23 * ((2 / Real.sqrt ell) * (2 : ℝ) ^ ell) :=
        hcardReal.trans (hsumBound.trans hlevelBound)
      _ = 46 * (2 : ℝ) ^ ell / Real.sqrt ell := by ring
  let events (i : Fin L.m) := severePatterns i
  let localRate : ℝ := 46 / Real.sqrt ell
  have hlocalRate : 0 ≤ localRate := by dsimp [localRate]; positivity
  have hLocal (i : Fin L.m) (hi : i ∈ Finset.univ) :
      ((events i).card : ℝ) ≤ localRate * (2 : ℝ) ^ (L.fineChunks i).card := by
    change ((severePatterns i).card : ℝ) ≤ localRate * (2 : ℝ) ^ (L.fineChunks i).card
    rw [L.fine_chunk_length i]
    calc
      ((severePatterns i).card : ℝ) ≤ 46 * (2 : ℝ) ^ ell / Real.sqrt ell := hSevereCard i
      _ = localRate * (2 : ℝ) ^ ell := by dsimp [localRate]; ring
  have hFineDisjoint : ∀ i j, i ≠ j → Disjoint (L.fineChunks i) (L.fineChunks j) :=
    L.chunks_disjoint.2.2.1
  let selectedEvent (S : Finset (Fin L.m)) :=
    Finset.univ.filter fun x : CubeVertex n =>
      ∀ i ∈ S, (fun a : Coord i => x a.1) ∈ events i
  have hweightEq (i : Fin L.m) (x : CubeVertex n) :
      weight i (fun a : Coord i => x a.1) = L.fineCount x i := by
    have hcardAttach (S : Finset (Fin n)) (z : CubeVertex n) :
        (S.filter fun b => z b = true).card =
          (S.attach.filter fun b => z b.1 = true).card := by
      apply Finset.card_bij (fun b hb => ⟨b, (Finset.mem_filter.mp hb).1⟩)
      · intro b hb
        rcases Finset.mem_filter.mp hb with ⟨hbS, hzb⟩
        exact Finset.mem_filter.mpr ⟨by simp, hzb⟩
      · intro b hb c hc hbc
        exact congrArg Subtype.val hbc
      · intro c hc
        rcases Finset.mem_filter.mp hc with ⟨hcS, hzc⟩
        exact ⟨c.1, Finset.mem_filter.mpr ⟨c.2, hzc⟩, by apply Subtype.ext; rfl⟩
    unfold weight HypercubeRamsey.Lane_q_s06_front.boolWeight FineLayout.fineCount
    change (Finset.univ.filter fun a : Coord i => x a.1 = true).card = _
    rw [show (Finset.univ : Finset (Coord i)) = (L.fineChunks i).attach by simp [Coord]]
    exact (hcardAttach (L.fineChunks i) x).symm
  have hselected (S : Finset (Fin L.m)) :
      ((selectedEvent S).card : ℝ) / (2 : ℝ) ^ n ≤ localRate ^ S.card := by
    simpa [selectedEvent, events] using
      (HypercubeRamsey.Lane_q_s06_front.cubeBlockEventFraction_le
        (n := n) (m := L.m) L.fineChunks hFineDisjoint S events localRate
        hlocalRate (fun i hi => hLocal i (Finset.mem_univ i)))
  let active (x : CubeVertex n) :=
    Finset.univ.filter fun i : Fin L.m => Nat.dist (2 * L.fineCount x i) ell ≤ 11
  let badVertices := Finset.univ.filter fun x : CubeVertex n => q ≤ L.severity x
  let qsets : Finset (Finset (Fin L.m)) := Finset.univ.powersetCard q
  let qEventUnion := qsets.biUnion selectedEvent
  have hbadSubset : badVertices ⊆ qEventUnion := by
    intro x hx
    have hqActive : q ≤ (active x).card := by
      simpa [active, FineLayout.severity, ell] using (Finset.mem_filter.mp hx).2
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hqActive
    have hTmem : T ∈ qsets := by
      simp [qsets, hTsub, hTcard]
    have hxT : x ∈ selectedEvent T := by
      simp only [selectedEvent, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      have hactive := (Finset.mem_filter.mp (hTsub hi)).2
      change (fun a : Coord i => x a.1) ∈ Finset.univ.filter
        (fun f : Coord i → Bool => Nat.dist (2 * weight i f) ell ≤ 11)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hweightEq i x]
      exact hactive
    exact Finset.mem_biUnion.mpr ⟨T, hTmem, hxT⟩
  have hbadCard : badVertices.card ≤ ∑ S ∈ qsets, (selectedEvent S).card := by
    calc
      badVertices.card ≤ qEventUnion.card := Finset.card_le_card hbadSubset
      _ ≤ ∑ S ∈ qsets, (selectedEvent S).card := by
        simpa [qEventUnion] using (Finset.card_biUnion_le (s := qsets) (t := selectedEvent))
  have hqsetsCard : qsets.card = Nat.choose L.m q := by
    simp [qsets, Finset.card_powersetCard]
  have hqsetsMemCard (S : Finset (Fin L.m)) (hS : S ∈ qsets) : S.card = q := by
    simpa [qsets] using (Finset.mem_powersetCard.mp hS).2
  have hchoose : qsets.card ≤ L.m ^ q := by
    rw [hqsetsCard]
    exact Nat.choose_le_pow L.m q
  have hbadProbability :
      ((badVertices.card : ℝ) / (2 : ℝ) ^ n) ≤ (L.m : ℝ) ^ q * localRate ^ q := by
    have hbadCast : (badVertices.card : ℝ) ≤
        ∑ S ∈ qsets, ((selectedEvent S).card : ℝ) := by exact_mod_cast hbadCard
    calc
      (badVertices.card : ℝ) / (2 : ℝ) ^ n ≤
          (∑ S ∈ qsets, ((selectedEvent S).card : ℝ)) / (2 : ℝ) ^ n :=
            div_le_div_of_nonneg_right hbadCast (by positivity)
      _ = ∑ S ∈ qsets, ((selectedEvent S).card : ℝ) / (2 : ℝ) ^ n := by
            rw [Finset.sum_div]
      _ ≤ ∑ S ∈ qsets, localRate ^ S.card := by
            apply Finset.sum_le_sum
            intro S hS
            have hScard : S.card = q := hqsetsMemCard S hS
            simpa [hScard] using hselected S
      _ = ∑ S ∈ qsets, localRate ^ q := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [hqsetsMemCard S hS]
      _ = (qsets.card : ℝ) * localRate ^ q := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (L.m : ℝ) ^ q * localRate ^ q := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)
  have hmBound : (L.m : ℝ) ≤ 2 * (n : ℝ) ^ α := by
    have hceil : (L.m : ℝ) < (n : ℝ) ^ α + 1 := by
      rw [hL]
      exact Nat.ceil_lt_add_one (by positivity)
    have hpowOne : 1 ≤ (n : ℝ) ^ α := Real.one_le_rpow hnR (by linarith)
    linarith
  have hrootSquare : ((n : ℝ) ^ (3 / 20 : ℝ)) ^ 2 = (n : ℝ) ^ (3 / 10 : ℝ) := by
    calc
      ((n : ℝ) ^ (3 / 20 : ℝ)) ^ 2 =
          (n : ℝ) ^ (3 / 20 : ℝ) * (n : ℝ) ^ (3 / 20 : ℝ) := by ring
      _ = (n : ℝ) ^ ((3 / 20 : ℝ) + (3 / 20 : ℝ)) :=
          (Real.rpow_add hnRpos _ _).symm
      _ = (n : ℝ) ^ (3 / 10 : ℝ) := by congr 1 <;> norm_num
  have hroot : (n : ℝ) ^ (3 / 20 : ℝ) ≤ Real.sqrt (ell : ℝ) := by
    apply le_of_sq_le_sq
    · rw [hrootSquare, Real.sq_sqrt (by positivity : 0 ≤ (ell : ℝ))]
      exact hellR
    · positivity
  have hinv : 1 / Real.sqrt (ell : ℝ) ≤ (n : ℝ) ^ (-(3 / 20 : ℝ)) := by
    have hpositive : 0 < (n : ℝ) ^ (3 / 20 : ℝ) := by positivity
    have hrecip := one_div_le_one_div_of_le hpositive hroot
    have hneg : (n : ℝ) ^ (-(3 / 20 : ℝ)) =
        1 / (n : ℝ) ^ (3 / 20 : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hnRpos)]
      simp [one_div]
    simpa [hneg] using hrecip
  have hRateBound : (L.m : ℝ) * localRate ≤ (n : ℝ) ^ (-(13 / 100 : ℝ)) := by
    have hlocal : localRate ≤ 46 * (n : ℝ) ^ (-(3 / 20 : ℝ)) := by
      dsimp [localRate]
      calc
        46 / Real.sqrt (ell : ℝ) = 46 * (1 / Real.sqrt (ell : ℝ)) := by ring
        _ ≤ 46 * (n : ℝ) ^ (-(3 / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (by norm_num)
    have hexp : (n : ℝ) ^ (α - 3 / 20 : ℝ) * (n : ℝ) ^ (1 / 50 - α) =
        (n : ℝ) ^ (-(13 / 100 : ℝ)) := by
      rw [← Real.rpow_add hnRpos]
      congr 1 <;> ring
    calc
      (L.m : ℝ) * localRate ≤
          (2 * (n : ℝ) ^ α) * (46 * (n : ℝ) ^ (-(3 / 20 : ℝ))) :=
        mul_le_mul hmBound hlocal (by positivity) (by positivity)
      _ = 92 * ((n : ℝ) ^ α * (n : ℝ) ^ (-(3 / 20 : ℝ))) := by ring
      _ = 92 * (n : ℝ) ^ (α - 3 / 20 : ℝ) := by
        rw [← Real.rpow_add hnRpos]
        congr 1 <;> ring
      _ ≤ (n : ℝ) ^ (-(13 / 100 : ℝ)) := by
        calc
          92 * (n : ℝ) ^ (α - 3 / 20 : ℝ) ≤
              (n : ℝ) ^ (1 / 50 - α) * (n : ℝ) ^ (α - 3 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_of_lt hnPow) (by positivity)
          _ = (n : ℝ) ^ (-(13 / 100 : ℝ)) := by rw [mul_comm, hexp]
  have hpowQ :
      ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ q =
        (n : ℝ) ^ (-(13 / 100 : ℝ) * (q : ℝ)) := by
    calc
      ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ q =
          ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ (q : ℝ) :=
            (Real.rpow_natCast _ _).symm
      _ = (n : ℝ) ^ (-(13 / 100 : ℝ) * (q : ℝ)) :=
            (Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)) _ _).symm
  have hratePow : ((L.m : ℝ) * localRate) ^ q ≤
      ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ q :=
    pow_le_pow_left₀ (by positivity) hRateBound q
  have hbadProbabilityCombined :
      ((badVertices.card : ℝ) / (2 : ℝ) ^ n) ≤ ((L.m : ℝ) * localRate) ^ q := by
    calc
      ((badVertices.card : ℝ) / (2 : ℝ) ^ n) ≤
          (L.m : ℝ) ^ q * localRate ^ q := hbadProbability
      _ = ((L.m : ℝ) * localRate) ^ q := (mul_pow (L.m : ℝ) localRate q).symm
  calc
    ((badVertices.card : ℝ) / (2 : ℝ) ^ n) ≤
        ((L.m : ℝ) * localRate) ^ q := hbadProbabilityCombined
    _ ≤ (n : ℝ) ^ (-(13 / 100 : ℝ) * (q : ℝ)) := by
      rw [← hpowQ]
      exact hratePow


/-- The coarse-only layout data needed for the boundary probability estimate. -/
structure CoarseLayout (n : ℕ) where
  coarseChunks : Fin 300 → Finset (Fin n)
  bin : Fin 300 → ℕ → Fin (n + 1)
  coarseChunks_disjoint : ∀ i j, i ≠ j → Disjoint (coarseChunks i) (coarseChunks j)
  coarse_length : ∀ i, (coarseChunks i).card = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  bin_monotone : ∀ i a b, a ≤ b → (bin i a).val ≤ (bin i b).val
  bin_count : ∀ i,
    (((Finset.range ((coarseChunks i).card + 1)).image (bin i)).card : ℝ) ≤
      (n : ℝ) ^ (1 / 25 : ℝ) + 1

namespace CoarseLayout

def coarseCount {n : ℕ} (L : CoarseLayout n) (x : CubeVertex n) (i : Fin 300) : ℕ :=
  ((L.coarseChunks i).filter fun a => x a = true).card

def coarseBin {n : ℕ} (L : CoarseLayout n) (x : CubeVertex n) : Fin 300 → Fin (n + 1) :=
  fun i => L.bin i (L.coarseCount x i)

def boundary {n : ℕ} (L : CoarseLayout n) (x : CubeVertex n) : Prop :=
  ∃ i a, a ∈ L.coarseChunks i ∧ L.coarseBin (Lane_q_s05_1b.flipVertex x a) ≠ L.coarseBin x

end CoarseLayout

/-- Boundary probability for 300 coarse chunks with `n^.04+1` quantile bins. -/
theorem coarseBoundaryFraction :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ L : CoarseLayout n,
      ((Finset.univ.filter fun x : CubeVertex n => L.boundary x).card : ℝ) /
        (2 : ℝ) ^ n ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
  classical
  have heventX : ∀ᶠ n : ℕ in Filter.atTop, 4 < (n : ℝ) ^ (1 / 5 : ℝ) := by
    have htend := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp
      tendsto_natCast_atTop_atTop
    exact htend.eventually (Filter.eventually_gt_atTop 4)
  have heventC : ∀ᶠ n : ℕ in Filter.atTop, 4800 < (n : ℝ) ^ (1 / 100 : ℝ) := by
    have htend := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      tendsto_natCast_atTop_atTop
    exact htend.eventually (Filter.eventually_gt_atTop 4800)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop 2).and (heventX.and heventC))
  refine ⟨n₀, ?_⟩
  intro n hn L
  have hdata := hn₀ n hn
  have hn2 : 2 ≤ n := hdata.1
  have hpowX : 4 < (n : ℝ) ^ (1 / 5 : ℝ) := hdata.2.1
  have hpowC : 4800 ≤ (n : ℝ) ^ (1 / 100 : ℝ) := le_of_lt hdata.2.2
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnRpos : 0 < (n : ℝ) := by positivity
  let δ : ℝ := (n : ℝ) ^ (-(1 / 10 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ2 : δ * δ = (n : ℝ) ^ (-(1 / 5 : ℝ)) := by
    dsimp [δ]
    rw [← Real.rpow_add hnRpos]
    congr 1 <;> norm_num
  have hδProd : (n : ℝ) ^ (-(1 / 5 : ℝ)) *
      (n : ℝ) ^ (1 / 5 : ℝ) = (n : ℝ) ^ (0 : ℝ) := by
    rw [← Real.rpow_add hnRpos]
    congr 1 <;> norm_num
  have hδChunk : δ * δ * ((n : ℝ) ^ (1 / 5 : ℝ) / 2) = 1 / 2 := by
    rw [hδ2]
    calc
      (n : ℝ) ^ (-(1 / 5 : ℝ)) * ((n : ℝ) ^ (1 / 5 : ℝ) / 2) =
          ((n : ℝ) ^ (-(1 / 5 : ℝ)) * (n : ℝ) ^ (1 / 5 : ℝ)) / 2 := by ring
      _ = (n : ℝ) ^ (0 : ℝ) / 2 := by rw [hδProd]
      _ = 1 / 2 := by simp
  let ell (i : Fin coarseChunkCount) : ℕ := (L.coarseChunks i).card
  have hell (i : Fin coarseChunkCount) : ell i = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ :=
    L.coarse_length i
  have hellPos (i : Fin coarseChunkCount) : 0 < ell i := by
    rw [hell]
    apply Nat.floor_pos.mpr
    linarith
  have hellLower (i : Fin coarseChunkCount) :
      (n : ℝ) ^ (1 / 5 : ℝ) / 2 ≤ (ell i : ℝ) := by
    have hfloorReal : (ell i : ℝ) = ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊ := by
      exact_mod_cast hell i
    rw [hfloorReal]
    have hlt := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 5 : ℝ))
    linarith
  have hδEll (i : Fin coarseChunkCount) :
      1 / 2 ≤ δ * δ * (ell i : ℝ) := by
    have hmono := mul_le_mul_of_nonneg_left (hellLower i)
      (mul_nonneg hδ.le hδ.le)
    rw [hδChunk] at hmono
    nlinarith [hmono]
  have hCentral (i : Fin coarseChunkCount) :
      2 / Real.sqrt (ell i : ℝ) ≤ 4 * δ := by
    have hsqrtPos : 0 < Real.sqrt (ell i : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hellPos i)
    have hsqrtSq : Real.sqrt (ell i : ℝ) ^ 2 = (ell i : ℝ) :=
      Real.sq_sqrt (by exact_mod_cast Nat.zero_le (ell i))
    have hmul : 2 ≤ 4 * δ * Real.sqrt (ell i : ℝ) := by
      apply le_of_sq_le_sq
      · rw [mul_pow, hsqrtSq]
        nlinarith [hδEll i]
      · positivity
    exact (div_le_iff₀ hsqrtPos).2 (by simpa [mul_assoc] using hmul)
  have hcountEq (i : Fin coarseChunkCount) (x : CubeVertex n) :
      L.coarseCount x i =
        HypercubeRamsey.Lane_q_s06_front.cubeCountOn (L.coarseChunks i) x := by
    classical
    have hcardAttach (S : Finset (Fin n)) (z : CubeVertex n) :
        (S.filter fun b => z b = true).card =
          (S.attach.filter fun b => z b.1 = true).card := by
      apply Finset.card_bij (fun b hb => ⟨b, (Finset.mem_filter.mp hb).1⟩)
      · intro b hb
        rcases Finset.mem_filter.mp hb with ⟨hbS, hzb⟩
        exact Finset.mem_filter.mpr ⟨by simp, hzb⟩
      · intro b hb c hc hbc
        exact congrArg Subtype.val hbc
      · intro c hc
        rcases Finset.mem_filter.mp hc with ⟨hcS, hzc⟩
        exact ⟨c.1, Finset.mem_filter.mpr ⟨c.2, hzc⟩, by apply Subtype.ext; rfl⟩
    unfold CoarseLayout.coarseCount HypercubeRamsey.Lane_q_s06_front.cubeCountOn
    exact hcardAttach (L.coarseChunks i) x
  have hfiberEq (i : Fin coarseChunkCount) (q : ℕ) :
      (Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i = q).card =
        Nat.choose (ell i) q * 2 ^ (n - ell i) := by
    have hset : (Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i = q) =
        (Finset.univ.filter fun x : CubeVertex n =>
          HypercubeRamsey.Lane_q_s06_front.cubeCountOn (L.coarseChunks i) x = q) := by
      ext x
      simp [hcountEq]
    rw [hset]
    simpa [ell] using
      HypercubeRamsey.Lane_q_s06_front.cubeCountOn_card (L.coarseChunks i) q
  have hFiberProb (i : Fin coarseChunkCount) (q : ℕ) (hq : q ≤ ell i) :
      ((Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i = q).card : ℝ) /
          (2 : ℝ) ^ n ≤ 4 * δ := by
    have hellLe : ell i ≤ n := by
      simpa [ell, Fintype.card_fin] using Finset.card_le_univ (L.coarseChunks i)
    have hsum : ell i + (n - ell i) = n := Nat.add_sub_of_le hellLe
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ ell i * (2 : ℝ) ^ (n - ell i) := by
      calc
        (2 : ℝ) ^ n = (2 : ℝ) ^ (ell i + (n - ell i)) :=
          congrArg (fun k : ℕ => (2 : ℝ) ^ k) hsum.symm
        _ = (2 : ℝ) ^ ell i * (2 : ℝ) ^ (n - ell i) := by rw [pow_add]
    have hcentral := centralBinomialUpper (ell i) (hellPos i) q hq
    calc
      ((Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i = q).card : ℝ) /
          (2 : ℝ) ^ n =
        (Nat.choose (ell i) q : ℝ) / (2 : ℝ) ^ (ell i) := by
          rw [hfiberEq i q]
          push_cast
          rw [hpow]
          field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ 2 / Real.sqrt (ell i : ℝ) := hcentral
      _ ≤ 4 * δ := hCentral i
  let endpoints (i : Fin coarseChunkCount) :=
    HypercubeRamsey.Lane_q_s06_front.binTransitionEndpoints (ell i) (L.bin i)
  have hEndpointsCard (i : Fin coarseChunkCount) :
      ((endpoints i).card : ℝ) ≤ 2 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) := by
    have hcard := HypercubeRamsey.Lane_q_s06_front.binTransitionEndpoints_card_le
      (ell := ell i) (bin := L.bin i) (fun a b hab => L.bin_monotone i a b hab)
    have hcardR : ((endpoints i).card : ℝ) ≤
        2 * (((Finset.range (ell i + 1)).image (L.bin i)).card : ℝ) := by
      exact_mod_cast hcard
    exact hcardR.trans (mul_le_mul_of_nonneg_left (L.bin_count i) (by norm_num))
  have hEventProb (i : Fin coarseChunkCount) :
      ((Finset.univ.filter fun x : CubeVertex n =>
        L.coarseCount x i ∈ endpoints i).card : ℝ) / (2 : ℝ) ^ n ≤
          8 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ := by
    let F (q : ℕ) := Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i = q
    have hUnion : (Finset.univ.filter fun x : CubeVertex n =>
        L.coarseCount x i ∈ endpoints i) = (endpoints i).biUnion F := by
      ext x
      simp [F, Finset.mem_biUnion]
    have hcard :
        ((Finset.univ.filter fun x : CubeVertex n =>
          L.coarseCount x i ∈ endpoints i).card : ℝ) / (2 : ℝ) ^ n ≤
          ∑ q ∈ endpoints i, ((F q).card : ℝ) / (2 : ℝ) ^ n := by
      have hcardNat :
          (Finset.univ.filter fun x : CubeVertex n =>
            L.coarseCount x i ∈ endpoints i).card ≤
            ∑ q ∈ endpoints i, (F q).card := by
        rw [hUnion]
        exact Finset.card_biUnion_le
      have hcardReal :
          ((Finset.univ.filter fun x : CubeVertex n =>
            L.coarseCount x i ∈ endpoints i).card : ℝ) ≤
            ∑ q ∈ endpoints i, ((F q).card : ℝ) := by exact_mod_cast hcardNat
      calc
        ((Finset.univ.filter fun x : CubeVertex n =>
          L.coarseCount x i ∈ endpoints i).card : ℝ) / (2 : ℝ) ^ n ≤
            (∑ q ∈ endpoints i, ((F q).card : ℝ)) / (2 : ℝ) ^ n :=
          div_le_div_of_nonneg_right hcardReal (by positivity)
        _ = ∑ q ∈ endpoints i, ((F q).card : ℝ) / (2 : ℝ) ^ n := by
          rw [Finset.sum_div]
    have hsum : (∑ q ∈ endpoints i, ((F q).card : ℝ) / (2 : ℝ) ^ n) ≤
        (endpoints i).card * (4 * δ) := by
      calc
        (∑ q ∈ endpoints i, ((F q).card : ℝ) / (2 : ℝ) ^ n) ≤
            ∑ q ∈ endpoints i, 4 * δ := by
              apply Finset.sum_le_sum
              intro q hq
              have hqle : q ≤ ell i := by
                change q ∈ HypercubeRamsey.Lane_q_s06_front.binTransitionEndpoints
                  (ell i) (L.bin i) at hq
                simp [HypercubeRamsey.Lane_q_s06_front.binTransitionEndpoints,
                  HypercubeRamsey.Lane_q_s06_front.binTransitionSet] at hq
                rcases hq with hq | hq
                · exact Nat.le_of_lt hq.1
                · rcases hq with ⟨r, ⟨hrange, _, hqeq⟩⟩
                  omega
              simpa [F] using hFiberProb i q hqle
        _ = (endpoints i).card * (4 * δ) := by simp [Finset.sum_const, nsmul_eq_mul]
    calc
      ((Finset.univ.filter fun x : CubeVertex n =>
        L.coarseCount x i ∈ endpoints i).card : ℝ) / (2 : ℝ) ^ n ≤
          (endpoints i).card * (4 * δ) := hcard.trans hsum
      _ ≤ 2 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * (4 * δ) :=
          mul_le_mul_of_nonneg_right (hEndpointsCard i) (by positivity)
      _ = 8 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ := by ring
  let boundaryVertices := Finset.univ.filter fun x : CubeVertex n => L.boundary x
  let allCoarseEvents := Finset.univ.biUnion fun i : Fin coarseChunkCount =>
    Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i
  have hboundarySubset : boundaryVertices ⊆ allCoarseEvents := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨i, a, ha, hchange⟩
    let q := L.coarseCount x i
    let y := flipVertex x a
    have hcountStep : L.coarseCount y i = q + 1 ∨ L.coarseCount y i + 1 = q := by
      cases hxa : x a
      · left
        have hset : (L.coarseChunks i).filter (fun b => flipVertex x a b = true) =
            insert a ((L.coarseChunks i).filter (fun b => x b = true)) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [flipVertex, hxa, ha]
          · have hflip : flipVertex x a b = x b := by
              unfold flipVertex
              exact Function.update_of_ne hba (!x a) x
            simp [hba, hflip]
        have hnot : a ∉ (L.coarseChunks i).filter (fun b => x b = true) := by
          simp [hxa]
        have hcard := congrArg Finset.card hset
        rw [Finset.card_insert_of_notMem hnot] at hcard
        change ((L.coarseChunks i).filter (fun b => y b = true)).card =
          ((L.coarseChunks i).filter (fun b => x b = true)).card + 1
        simpa [y] using hcard
      · right
        have hset : (L.coarseChunks i).filter (fun b => x b = true) =
            insert a ((L.coarseChunks i).filter (fun b => flipVertex x a b = true)) := by
          ext b
          by_cases hba : b = a
          · subst b
            simp [flipVertex, hxa, ha]
          · have hflip : flipVertex x a b = x b := by
              unfold flipVertex
              exact Function.update_of_ne hba (!x a) x
            simp [hba, hflip]
        have hnot : a ∉ (L.coarseChunks i).filter (fun b => flipVertex x a b = true) := by
          simp [flipVertex, hxa]
        have hcard := congrArg Finset.card hset
        rw [Finset.card_insert_of_notMem hnot] at hcard
        change ((L.coarseChunks i).filter (fun b => y b = true)).card + 1 =
          ((L.coarseChunks i).filter (fun b => x b = true)).card
        simpa [y] using hcard.symm
    have hcountOther (j : Fin coarseChunkCount) (hji : j ≠ i) :
        L.coarseCount y j = L.coarseCount x j := by
      have hdisj := L.coarseChunks_disjoint j i hji
      have hnot : a ∉ L.coarseChunks j := by
        intro haJ
        exact (Finset.disjoint_left.mp hdisj) haJ ha
      unfold CoarseLayout.coarseCount
      apply congrArg Finset.card
      ext b
      by_cases hb : b ∈ L.coarseChunks j
      · have hba : b ≠ a := by intro heq; subst b; exact hnot hb
        simp [hb, hba, flipVertex, y]
      · simp [hb]
    have hbinAt : L.bin i (L.coarseCount y i) ≠ L.bin i q := by
      intro heq
      apply hchange
      funext j
      by_cases hji : j = i
      · subst j
        change L.bin i (L.coarseCount y i) = L.bin i q
        exact heq
      · change L.bin j (L.coarseCount y j) = L.bin j (L.coarseCount x j)
        exact congrArg (L.bin j) (hcountOther j hji)
    have hqle : q ≤ ell i := by
      dsimp [q, ell]
      unfold CoarseLayout.coarseCount
      exact Finset.card_filter_le _ _
    have hmemEnd : q ∈ endpoints i := by
      rcases hcountStep with hup | hdown
      · have ht : q ∈ HypercubeRamsey.Lane_q_s06_front.binTransitionSet (ell i) (L.bin i) := by
          have hyqle : L.coarseCount y i ≤ ell i := by
            dsimp [ell]
            unfold CoarseLayout.coarseCount
            exact Finset.card_filter_le _ _
          have hqLt : q < ell i := by omega
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_range.mpr hqLt, by simpa [hup] using hbinAt⟩
        exact Finset.mem_union.mpr (Or.inl ht)
      · have hrange : L.coarseCount y i < ell i := by
          omega
        have ht : L.coarseCount y i ∈
            HypercubeRamsey.Lane_q_s06_front.binTransitionSet (ell i) (L.bin i) := by
          have htrans : L.bin i (L.coarseCount y i + 1) ≠ L.bin i (L.coarseCount y i) := by
            intro heq
            apply hbinAt
            rw [← hdown]
            exact heq.symm
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_range.mpr hrange, htrans⟩
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        exact ⟨L.coarseCount y i, ht, by omega⟩
    change x ∈ Finset.univ.biUnion (fun j : Fin coarseChunkCount =>
      Finset.univ.filter fun z : CubeVertex n => L.coarseCount z j ∈ endpoints j)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmemEnd⟩⟩
  have hunionCard : boundaryVertices.card ≤
      ∑ i : Fin coarseChunkCount,
        (Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i).card := by
    calc
      boundaryVertices.card ≤ allCoarseEvents.card := Finset.card_le_card hboundarySubset
      _ ≤ ∑ i : Fin coarseChunkCount,
          (Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i).card :=
        Finset.card_biUnion_le
  have hunionFraction : (boundaryVertices.card : ℝ) / (2 : ℝ) ^ n ≤
      ∑ i : Fin coarseChunkCount,
        ((Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i).card : ℝ) /
          (2 : ℝ) ^ n := by
    have hcast : (boundaryVertices.card : ℝ) ≤
        ∑ i : Fin coarseChunkCount,
          ((Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i).card : ℝ) :=
      by exact_mod_cast hunionCard
    calc
      (boundaryVertices.card : ℝ) / (2 : ℝ) ^ n ≤
          (∑ i : Fin coarseChunkCount,
            ((Finset.univ.filter fun x : CubeVertex n =>
              L.coarseCount x i ∈ endpoints i).card : ℝ)) / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_right hcast (by positivity)
      _ = ∑ i : Fin coarseChunkCount,
          ((Finset.univ.filter fun x : CubeVertex n =>
            L.coarseCount x i ∈ endpoints i).card : ℝ) / (2 : ℝ) ^ n := by
          rw [Finset.sum_div]
  have hsumBound :
      (∑ i : Fin coarseChunkCount,
        ((Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i).card : ℝ) /
          (2 : ℝ) ^ n) ≤
        2400 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ := by
    calc
      (∑ i : Fin coarseChunkCount,
        ((Finset.univ.filter fun x : CubeVertex n => L.coarseCount x i ∈ endpoints i).card : ℝ) /
          (2 : ℝ) ^ n) ≤
        ∑ i : Fin coarseChunkCount, 8 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ := by
            apply Finset.sum_le_sum
            intro i hi
            exact hEventProb i
      _ = (Fintype.card (Fin coarseChunkCount) : ℝ) *
          (8 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = 2400 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ := by
            have hcard : Fintype.card (Fin coarseChunkCount) = 300 := by
              change Fintype.card (Fin 300) = 300
              exact Fintype.card_fin 300
            rw [hcard]
            norm_num
            ring
  have hproduct : (n : ℝ) ^ (1 / 25 : ℝ) * δ = (n : ℝ) ^ (-(3 / 50 : ℝ)) := by
    dsimp [δ]
    rw [← Real.rpow_add hnRpos]
    congr 1 <;> norm_num
  have hpowMono : δ ≤ (n : ℝ) ^ (-(3 / 50 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (-(1 / 10 : ℝ)) ≤ -(3 / 50 : ℝ))
    simpa [δ] using h
  have hmain : 2400 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ ≤
      (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
    have hsum : ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ ≤
        2 * (n : ℝ) ^ (-(3 / 50 : ℝ)) := by
      rw [add_mul, hproduct, one_mul]
      calc
        (n : ℝ) ^ (-(3 / 50 : ℝ)) + δ =
            δ + (n : ℝ) ^ (-(3 / 50 : ℝ)) := by ring
        _ ≤ (n : ℝ) ^ (-(3 / 50 : ℝ)) + (n : ℝ) ^ (-(3 / 50 : ℝ)) :=
          add_le_add_left hpowMono ((n : ℝ) ^ (-(3 / 50 : ℝ)))
        _ = 2 * (n : ℝ) ^ (-(3 / 50 : ℝ)) := by ring
    calc
      2400 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ ≤
          4800 * (n : ℝ) ^ (-(3 / 50 : ℝ)) := by
            calc
              2400 * ((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ ≤
                  2400 * (((n : ℝ) ^ (1 / 25 : ℝ) + 1) * δ) := by rw [mul_assoc]
              _ ≤ 2400 * (2 * (n : ℝ) ^ (-(3 / 50 : ℝ))) :=
                mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2400)
              _ = 4800 * (n : ℝ) ^ (-(3 / 50 : ℝ)) := by ring
      _ ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
        have hprod : (n : ℝ) ^ (1 / 100 : ℝ) * (n : ℝ) ^ (-(3 / 50 : ℝ)) =
            (n : ℝ) ^ (-(1 / 20 : ℝ)) := by
          rw [← Real.rpow_add hnRpos]
          congr 1 <;> norm_num
        calc
          4800 * (n : ℝ) ^ (-(3 / 50 : ℝ)) ≤
              (n : ℝ) ^ (1 / 100 : ℝ) * (n : ℝ) ^ (-(3 / 50 : ℝ)) :=
                mul_le_mul_of_nonneg_right hpowC (by positivity)
          _ = (n : ℝ) ^ (-(1 / 20 : ℝ)) := hprod
  exact hunionFraction.trans (hsumBound.trans hmain)


end HypercubeRamsey.Lane_q_s05_1b
