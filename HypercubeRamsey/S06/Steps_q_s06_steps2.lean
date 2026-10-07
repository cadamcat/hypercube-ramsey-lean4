import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S06.Step3Defs

set_option maxHeartbeats 400000

/-!
Lane-local finite normalization facts for Section 6 Step 3.
-/

namespace HypercubeRamsey
namespace S06
namespace Lane_q_s06_steps2

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

theorem smallPowersetCount6 {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (T : ℕ) :
    ((Finset.range (T + 1)).biUnion fun k => s.powersetCard k).card ≤
      (s.card + 2) ^ (2 * T) := by
  classical
  have hT : T + 1 ≤ 2 ^ T := by
    induction T with
    | zero => norm_num
    | succ T ih =>
        have hstep : T + 2 ≤ 2 * (T + 1) := by omega
        calc
          T + 2 ≤ 2 * (T + 1) := hstep
          _ ≤ 2 * 2 ^ T := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (T + 1) := by simp [pow_succ, Nat.mul_comm]
  have hchoose (k : ℕ) (hk : k ∈ Finset.range (T + 1)) :
      s.card.choose k ≤ (s.card + 1) ^ T := by
    have hkT : k ≤ T := by simpa using Finset.mem_range.mp hk
    calc
      s.card.choose k ≤ s.card ^ k := Nat.choose_le_pow _ _
      _ ≤ (s.card + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) _
      _ ≤ (s.card + 1) ^ T := Nat.pow_le_pow_right (Nat.succ_pos _) hkT
  have hsum :
      (∑ k ∈ Finset.range (T + 1), s.card.choose k) ≤
        (T + 1) * (s.card + 1) ^ T := by
    calc
      (∑ k ∈ Finset.range (T + 1), s.card.choose k) ≤
          ∑ k ∈ Finset.range (T + 1), (s.card + 1) ^ T := by
        apply Finset.sum_le_sum
        intro k hk
        exact hchoose k hk
      _ = (T + 1) * (s.card + 1) ^ T := by simp
  have hcard :
      ((Finset.range (T + 1)).biUnion fun k => s.powersetCard k).card ≤
        ∑ k ∈ Finset.range (T + 1), s.card.choose k := by
    calc
      ((Finset.range (T + 1)).biUnion fun k => s.powersetCard k).card ≤
          ∑ k ∈ Finset.range (T + 1), (s.powersetCard k).card := Finset.card_biUnion_le
      _ = ∑ k ∈ Finset.range (T + 1), s.card.choose k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.card_powersetCard]
  have hbase : 2 * (s.card + 1) ≤ (s.card + 2) * (s.card + 2) := by
    exact Nat.mul_le_mul (by omega) (by omega)
  calc
    ((Finset.range (T + 1)).biUnion fun k => s.powersetCard k).card ≤
        (T + 1) * (s.card + 1) ^ T := hcard.trans hsum
    _ ≤ 2 ^ T * (s.card + 1) ^ T := Nat.mul_le_mul_right _ hT
    _ = (2 * (s.card + 1)) ^ T := by rw [Nat.mul_pow]
    _ ≤ ((s.card + 2) * (s.card + 2)) ^ T := Nat.pow_le_pow_left hbase _
    _ = (s.card + 2) ^ (2 * T) := by rw [← pow_two, ← pow_mul]

theorem sigmaPatternCard6 {α β C : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [Fintype C] [DecidableEq C]
    (S : Finset (Finset α)) (T E : ℕ)
    (hS : ∀ s ∈ S, s.card ≤ T) (hβ : Fintype.card β ≤ 1806)
    (hC : Fintype.card C ≤ E) :
    Fintype.card (Σ s : {s // s ∈ S}, Finset (s.1 × β) × (C → s.1)) ≤
      S.card * (2 ^ (T * 1806)) * ((T + 1) ^ E) := by
  classical
  calc
    Fintype.card (Σ s : {s // s ∈ S}, Finset (s.1 × β) × (C → s.1)) =
        ∑ s : {s // s ∈ S}, Fintype.card (Finset (s.1 × β) × (C → s.1)) := by
      rw [Fintype.card_sigma]
    _ ≤ ∑ _s : {s // s ∈ S}, (2 ^ (T * 1806)) * ((T + 1) ^ E) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsCard := hS s.1 s.2
      have hpow1 : 2 ^ (s.1.card * Fintype.card β) ≤ 2 ^ (T * 1806) :=
        Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul hsCard hβ)
      have hsPlus : s.1.card ≤ T + 1 := by omega
      have hpow2 : s.1.card ^ Fintype.card C ≤ (T + 1) ^ E := by
        calc
          s.1.card ^ Fintype.card C ≤ (T + 1) ^ Fintype.card C :=
            Nat.pow_le_pow_left hsPlus _
          _ ≤ (T + 1) ^ E := Nat.pow_le_pow_right (by omega) hC
      have hcard' : Fintype.card (Finset (s.1 × β) × (C → s.1)) =
          (2 ^ (s.1.card * Fintype.card β)) * (s.1.card ^ Fintype.card C) := by
        simp [Fintype.card_prod, Fintype.card_finset, Fintype.card_fun, Fintype.card_coe]
      rw [hcard']
      exact Nat.mul_le_mul hpow1 hpow2
    _ = S.card * ((2 ^ (T * 1806)) * ((T + 1) ^ E)) := by simp
    _ = S.card * (2 ^ (T * 1806)) * ((T + 1) ^ E) := by ring

theorem natPow_eq_exp_log6 (b k : ℕ) (hb : 0 < b) :
    (b : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (b : ℝ)) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by exact_mod_cast hb), mul_comm]

noncomputable def DescCode6 {Id Ty σ : Type*} (S : Finset Id)
    (Tys : Finset Ty) (Bad : Finset σ) : Type _ :=
  Finset ({i // i ∈ S} × {t // t ∈ Tys}) × ({a // a ∈ Bad} → {i // i ∈ S})

noncomputable def decodeDescCode6 {Id Ty σ : Type*} [DecidableEq Id] [DecidableEq Ty]
    {S : Finset Id} {Tys : Finset Ty} {Bad : Finset σ} (τ : σ → Ty)
    (c : DescCode6 S Tys Bad) : Finset (Id × Ty) :=
  c.1.image (fun x => (x.1.1, x.2.1)) ∪
    (Finset.univ.image fun a : {a // a ∈ Bad} => ((c.2 a).1, τ a.1))

theorem exists_descCode6 {Id Ty σ : Type*} [Fintype σ]
    [DecidableEq Id] [DecidableEq Ty] [DecidableEq σ]
    (S : Finset Id) (Tys : Finset Ty) (Bad : Finset σ)
    (φ : σ → Id) (τ : σ → Ty) (D : Finset (Id × Ty))
    (hD : D = Finset.univ.image fun a : σ => (φ a, τ a))
    (hids : ∀ a, φ a ∈ S)
    (hclass : ∀ a, τ a ∈ Tys ∨ a ∈ Bad) :
    ∃ c : DescCode6 S Tys Bad, decodeDescCode6 τ c = D := by
  classical
  let GoodType := {t : Ty // t ∈ Tys}
  let BadType := {a : σ // a ∈ Bad}
  let Gen : Finset ({i // i ∈ S} × GoodType) :=
    (Finset.univ : Finset ({i // i ∈ S} × GoodType)).filter
      (fun x => (x.1.1, x.2.1) ∈ D)
  let badMap : BadType → {i // i ∈ S} := fun a => ⟨φ a.1, hids a.1⟩
  let c : DescCode6 S Tys Bad := ⟨Gen, badMap⟩
  have hdecode : decodeDescCode6 τ c = D := by
    apply Finset.ext
    intro e
    change e ∈ (c.1.image (fun x => (x.1.1, x.2.1)) ∪
        Finset.univ.image fun a : BadType => ((c.2 a).1, τ a.1)) ↔ e ∈ D
    constructor
    · intro he
      rcases Finset.mem_union.mp he with hgen | hbad
      · rcases Finset.mem_image.mp hgen with ⟨x, hx, hxe⟩
        rw [← hxe]
        exact (Finset.mem_filter.mp hx).2
      · rcases Finset.mem_image.mp hbad with ⟨a, ha, hxe⟩
        rw [← hxe, hD]
        exact Finset.mem_image.mpr ⟨a.1, Finset.mem_univ _, rfl⟩
    · intro he
      rw [hD] at he
      rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
      rcases hclass a with hgood | hbad
      · let x : {i // i ∈ S} × GoodType :=
          (⟨φ a, hids a⟩, ⟨τ a, hgood⟩)
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_image.mpr
        refine ⟨x, ?_, ?_⟩
        · change x ∈ Finset.univ.filter
            (fun y : {i // i ∈ S} × GoodType => (y.1.1, y.2.1) ∈ D)
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hD]
          apply Finset.mem_image.mpr
          exact ⟨a, Finset.mem_univ _, by simp [x]⟩
        · rfl
      · let a' : BadType := ⟨a, hbad⟩
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨a', Finset.mem_univ _, ?_⟩
        rfl
  exact ⟨c, hdecode⟩

private theorem edge_coord_in_chunks {n : ℕ} (L : ChunkLayout6 n)
    (u v : CubeVertex n) (h : (cube n).Adj u v) :
    ∃ q, u q ≠ v q ∧ (∀ j, j ≠ q → u j = v j) ∧
      ((∃ i, q ∈ L.coarseChunks i) ∨ (∃ i, q ∈ L.fineChunks i) ∨ q ∈ L.residual) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun q => u q ≠ v q
  have hcard : S.card = 1 := by
    change _root_.hammingDist u v = 1 at h
    simpa [S, _root_.hammingDist] using h
  obtain ⟨q, hS⟩ := Finset.card_eq_one.mp hcard
  have hmem : q ∈ S := by rw [hS]; simp
  have hq : u q ≠ v q := (Finset.mem_filter.mp hmem).2
  have hother : ∀ j, j ≠ q → u j = v j := by
    intro j hj
    by_contra hne
    have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have : j = q := by simpa [hS] using hmem
    exact hj this
  have hcover : q ∈
      (Finset.univ.biUnion L.coarseChunks ∪ Finset.univ.biUnion L.fineChunks) ∪ L.residual := by
    have hu : q ∈ Finset.univ := Finset.mem_univ q
    rw [← L.chunks_cover] at hu
    exact hu
  rcases Finset.mem_union.mp hcover with hcf | hr
  · rcases Finset.mem_union.mp hcf with hc | hf
    · rcases Finset.mem_biUnion.mp hc with ⟨i, hi, hqi⟩
      exact ⟨q, hq, hother, Or.inl ⟨i, hqi⟩⟩
    · rcases Finset.mem_biUnion.mp hf with ⟨i, hi, hqi⟩
      exact ⟨q, hq, hother, Or.inr (Or.inl ⟨i, hqi⟩)⟩
  · exact ⟨q, hq, hother, Or.inr (Or.inr hr)⟩

private theorem stNbr_witness6 {n : ℕ} (L : ChunkLayout6 n) (b a : State6 L)
    (ha : a ∈ L.stNbr b) :
    ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
      L.stateOf u = b ∧ L.stateOf v = a ∧ (cube n).Adj u v := by
  simpa only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] using ha

private theorem edge_key_severity {n : ℕ} (L : ChunkLayout6 n) (F : ChunkFlips6 L)
    (u v : CubeVertex n) (h : (cube n).Adj u v) :
    keyAdjacent6 binAdjacent6 (L.key u) (L.key v) ∧ Nat.dist (L.severity u) (L.severity v) ≤ 1 := by
  obtain ⟨q, hq, hother, _⟩ := edge_coord_in_chunks L u v h
  constructor
  · by_cases hc : ∃ i, q ∈ L.coarseChunks i
    · obtain ⟨i, hqi⟩ := hc
      exact F.coarse_flip_key u v h ⟨i, q, hqi, hq⟩
    · have hsame : ∀ i a, a ∈ L.coarseChunks i → u a = v a := by
        intro i a ha
        by_cases heq : a = q
        · subst a
          exact False.elim (hc ⟨i, ha⟩)
        · exact hother a heq
      exact Or.inl (F.noncoarse_flip_key u v h hsame)
  · by_cases hf : ∃ i, q ∈ L.fineChunks i
    · obtain ⟨i, hqi⟩ := hf
      exact F.fine_flip_severity u v h ⟨i, q, hqi, hq⟩
    · have hsame : ∀ i a, a ∈ L.fineChunks i → u a = v a := by
        intro i a ha
        by_cases heq : a = q
        · subst a
          exact False.elim (hf ⟨i, ha⟩)
        · exact hother a heq
      have hsev := (F.nonfine_flip_fine u v h hsame).2.2
      rw [hsev]
      simp

private def neighborSeverityVariants6 (j : ℕ) : Finset ℕ := {j - 1, j, j + 1}

private noncomputable def neighborTypeVariants6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (b : X.State)
    (h : CoarseKey6 (BinVector6 n)) : Finset X.Ty :=
  (neighborSeverityVariants6 (X.g.L.stSeverity b)).image
    (fun j => makeType6 binAdjacent6 h (X.g.L.stSign b) (X.g.L.stFlippable b) j X.J)

noncomputable def neighborTypeForms6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (b : X.State) : Finset X.Ty :=
  (X.C (X.g.L.stKey b)).biUnion (neighborTypeVariants6 X b)

theorem neighborTypeForms6_card {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (b : X.State) :
    (neighborTypeForms6 X b).card ≤ 3 * 602 := by
  classical
  let Js := neighborSeverityVariants6 (X.g.L.stSeverity b)
  have hJs : Js.card ≤ 3 := by
    simpa [Js, neighborSeverityVariants6] using (Finset.card_le_three
      (a := X.g.L.stSeverity b - 1) (b := X.g.L.stSeverity b)
      (c := X.g.L.stSeverity b + 1))
  calc
    (neighborTypeForms6 X b).card ≤
        ∑ h ∈ X.C (X.g.L.stKey b), (neighborTypeVariants6 X b h).card := by
      unfold neighborTypeForms6
      exact Finset.card_biUnion_le
    _ ≤ ∑ h ∈ X.C (X.g.L.stKey b), 3 := by
      apply Finset.sum_le_sum
      intro h hh
      calc
        (neighborTypeVariants6 X b h).card ≤ Js.card := by
          simpa [neighborTypeVariants6, neighborSeverityVariants6, Js] using
            (Finset.card_image_le :
              (Js.image (fun j : ℕ =>
                makeType6 binAdjacent6 h (X.g.L.stSign b) (X.g.L.stFlippable b) j X.J)).card ≤ Js.card)
        _ ≤ 3 := hJs
    _ = (X.C (X.g.L.stKey b)).card * 3 := by simp
    _ ≤ 602 * 3 := Nat.mul_le_mul_right _ (X.g.flips.key_neighborhood_card _)
    _ = 3 * 602 := by omega

theorem neighbor_key_severity6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    {b a : X.State} (ha : a ∈ X.g.L.stNbr b) :
    X.g.L.stKey a ∈ X.C (X.g.L.stKey b) ∧
      Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) ≤ 1 := by
  obtain ⟨u, v, huodd, hveven, hub, hva, hadj⟩ := stNbr_witness6 X.g.L b a ha
  have hedge := edge_key_severity X.g.L X.g.flips u v hadj
  have hku : X.g.L.key u = X.g.L.stKey b := by
    calc
      X.g.L.key u = X.g.L.stKey (X.g.L.stateOf u) := (X.facts.key_eq u).symm
      _ = X.g.L.stKey b := by rw [hub]
  have hkv : X.g.L.key v = X.g.L.stKey a := by
    calc
      X.g.L.key v = X.g.L.stKey (X.g.L.stateOf v) := (X.facts.key_eq v).symm
      _ = X.g.L.stKey a := by rw [hva]
  have hsu : X.g.L.severity u = X.g.L.stSeverity b := by
    calc
      X.g.L.severity u = X.g.L.stSeverity (X.g.L.stateOf u) := (X.facts.severity_eq u).symm
      _ = X.g.L.stSeverity b := by rw [hub]
  have hsv : X.g.L.severity v = X.g.L.stSeverity a := by
    calc
      X.g.L.severity v = X.g.L.stSeverity (X.g.L.stateOf v) := (X.facts.severity_eq v).symm
      _ = X.g.L.stSeverity a := by rw [hva]
  have hkey : keyAdjacent6 binAdjacent6 (X.g.L.stKey b) (X.g.L.stKey a) := by
    simpa [hku, hkv] using hedge.1
  have hkeymem : X.g.L.stKey a ∈ X.C (X.g.L.stKey b) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkey⟩
  have hsev : Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) ≤ 1 := by
    calc
      Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) =
          Nat.dist (X.g.L.severity v) (X.g.L.severity u) := by rw [hsv.symm, hsu.symm]
      _ = Nat.dist (X.g.L.severity u) (X.g.L.severity v) := Nat.dist_comm _ _
      _ ≤ 1 := hedge.2
  exact ⟨hkeymem, hsev⟩

theorem neighbor_type_mem_forms6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    {b a : X.State} (ha : a ∈ X.g.L.stNbr b)
    (hsign : X.g.L.stSign a = X.g.L.stSign b)
    (hflip : X.g.L.stFlippable a = X.g.L.stFlippable b) :
    X.stType a ∈ neighborTypeForms6 X b := by
  classical
  obtain ⟨u, v, huodd, hveven, hub, hva, hadj⟩ := stNbr_witness6 X.g.L b a ha
  have hedge := edge_key_severity X.g.L X.g.flips u v hadj
  have hkeyu := X.facts.key_eq u
  have hkeyv := X.facts.key_eq v
  have hsevU := X.facts.severity_eq u
  have hsevV := X.facts.severity_eq v
  have hku : X.g.L.key u = X.g.L.stKey b := by
    calc
      X.g.L.key u = X.g.L.stKey (X.g.L.stateOf u) := hkeyu.symm
      _ = X.g.L.stKey b := by rw [hub]
  have hkv : X.g.L.key v = X.g.L.stKey a := by
    calc
      X.g.L.key v = X.g.L.stKey (X.g.L.stateOf v) := hkeyv.symm
      _ = X.g.L.stKey a := by rw [hva]
  have hsu : X.g.L.severity u = X.g.L.stSeverity b := by
    calc
      X.g.L.severity u = X.g.L.stSeverity (X.g.L.stateOf u) := hsevU.symm
      _ = X.g.L.stSeverity b := by rw [hub]
  have hsv : X.g.L.severity v = X.g.L.stSeverity a := by
    calc
      X.g.L.severity v = X.g.L.stSeverity (X.g.L.stateOf v) := hsevV.symm
      _ = X.g.L.stSeverity a := by rw [hva]
  have hkey : keyAdjacent6 binAdjacent6 (X.g.L.stKey b) (X.g.L.stKey a) := by
    simpa [hku, hkv] using hedge.1
  have hkeymem : X.g.L.stKey a ∈ X.C (X.g.L.stKey b) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkey⟩
  have hsev : Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) ≤ 1 := by
    calc
      Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) =
          Nat.dist (X.g.L.severity v) (X.g.L.severity u) := by rw [hsv.symm, hsu.symm]
      _ = Nat.dist (X.g.L.severity u) (X.g.L.severity v) := Nat.dist_comm _ _
      _ ≤ 1 := hedge.2
  have hsevMem : X.g.L.stSeverity a ∈
      ({X.g.L.stSeverity b - 1, X.g.L.stSeverity b, X.g.L.stSeverity b + 1} : Finset ℕ) := by
    unfold Nat.dist at hsev
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  apply Finset.mem_biUnion.mpr
  refine ⟨X.g.L.stKey a, hkeymem, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨X.g.L.stSeverity a, hsevMem, ?_⟩
  simpa [Ctx6.stType, ChunkLayout6.stType, hsign, hflip] using rfl

theorem neighbor_type_mem_forms_high6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {b a : X.State} (ha : a ∈ X.g.L.stNbr b)
    (hmode : X.stMode a = .high) (hnot : X.g.L.stSeverity a ≠ X.J + 1) :
    X.stType a ∈ neighborTypeForms6 X b := by
  classical
  have ⟨hkeymem, hsev⟩ := neighbor_key_severity6 X ha
  have hsevMem : X.g.L.stSeverity a ∈
      ({X.g.L.stSeverity b - 1, X.g.L.stSeverity b, X.g.L.stSeverity b + 1} : Finset ℕ) := by
    unfold Nat.dist at hsev
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hJ : X.J < X.g.L.stSeverity a := by
    by_cases hle : X.g.L.stSeverity a ≤ X.J
    · simp [Ctx6.stMode, modeOf6, hle] at hmode
    · exact Nat.lt_of_not_ge hle
  have htype :
      makeType6 binAdjacent6 (X.g.L.stKey a) (X.g.L.stSign a)
          (X.g.L.stFlippable a) (X.g.L.stSeverity a) X.J =
        makeType6 binAdjacent6 (X.g.L.stKey a) (X.g.L.stSign b)
          (X.g.L.stFlippable b) (X.g.L.stSeverity a) X.J := by
    simp [makeType6, highObservations6, not_le_of_gt hJ, hnot]
  apply Finset.mem_biUnion.mpr
  refine ⟨X.g.L.stKey a, hkeymem, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨X.g.L.stSeverity a, hsevMem, ?_⟩
  simpa [Ctx6.stType, ChunkLayout6.stType] using htype.symm

theorem descOf_card_le_split {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (φ : X.g.L.stNbr b → Id)
    (S : Finset Id) (Tys : Finset X.Ty) (Bad : Finset (X.g.L.stNbr b))
    (hids : ∀ a, φ a ∈ S)
    (hclass : ∀ a, X.stType a.1 ∈ Tys ∨ a ∈ Bad) :
    (X.descOf b φ).card ≤ S.card * Tys.card + Bad.card := by
  classical
  have hsub : X.descOf b φ ⊆ S ×ˢ Tys ∪ Bad.image (fun a => (φ a, X.stType a.1)) := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    rcases hclass a with ht | hb
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_product.mpr ⟨hids a, ht⟩
    · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_image.mpr ⟨a, hb, rfl⟩
  calc
    (X.descOf b φ).card ≤ (S ×ˢ Tys ∪ Bad.image (fun a => (φ a, X.stType a.1))).card :=
      Finset.card_le_card hsub
    _ ≤ (S ×ˢ Tys).card + (Bad.image (fun a => (φ a, X.stType a.1))).card :=
      Finset.card_union_le _ _
    _ ≤ S.card * Tys.card + Bad.card := by
      rw [Finset.card_product]
      exact Nat.add_le_add_left (Finset.card_image_le) _

private def mergedField6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (s : X.State) (i : Fin X.g.L.m) : ℕ := (s.2.2.2.1 i).val

private def nearCoordsState6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (s : X.State) : Finset (Fin X.g.L.m) :=
  Finset.univ.filter fun i => Nat.dist (2 * mergedField6 X s i) X.g.L.fineLength ≤ 3

private def countCoordinate6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (s : X.State) (i : Fin X.g.L.m) : Fin (n + 1) := s.2.2.2.1 i

private def severityCoordinate6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (s : X.State) : Fin (X.g.L.m + 1) := s.2.2.2.2

private def potentialState6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.State) (i : Fin X.g.L.m) (s : X.State) : Prop :=
  s.1 = b.1 ∧ X.g.L.stKey s = X.g.L.stKey b ∧
    (∀ j, j ≠ i → mergedField6 X s j = mergedField6 X b j) ∧
      Nat.dist (mergedField6 X s i) (mergedField6 X b i) ≤ 3 ∧
      Nat.dist (X.g.L.stSeverity s) (X.g.L.stSeverity b) ≤ 1

private theorem mergedField_stateOf6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (x : CubeVertex n) (i : Fin X.g.L.m) :
    mergedField6 X (X.g.L.stateOf x) i = min (X.g.L.mergedCount x i) n := rfl

private theorem stSeverity_stateOf6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (x : CubeVertex n) :
    X.g.L.stSeverity (X.g.L.stateOf x) = min (X.g.L.severity x) X.g.L.m := rfl

noncomputable def potentialStates6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (b : X.State) (i : Fin X.g.L.m) : Finset (X.g.L.stNbr b) :=
  Finset.univ.filter fun s => potentialState6 X b i s.1

private theorem potentialStates6_card {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.State) (i : Fin X.g.L.m) :
    (potentialStates6 X b i).card ≤ 21 := by
  classical
  let Counts : Finset (Fin (n + 1)) :=
    Finset.univ.filter fun c => Nat.dist c.val (mergedField6 X b i) ≤ 3
  let Sevs : Finset (Fin (X.g.L.m + 1)) :=
    Finset.univ.filter fun j => Nat.dist j.val (X.g.L.stSeverity b) ≤ 1
  have hCounts : Counts.card ≤ 7 := by
    let code : Counts → Fin 7 := fun c =>
      ⟨c.1.val + 3 - mergedField6 X b i, by
        have hc := (Finset.mem_filter.mp c.2).2
        unfold Nat.dist at hc
        omega⟩
    have hinj : Function.Injective code := by
      intro c d h
      apply Subtype.ext
      apply Fin.ext
      have hc := (Finset.mem_filter.mp c.2).2
      have hd := (Finset.mem_filter.mp d.2).2
      unfold Nat.dist at hc hd
      have hval := congrArg Fin.val h
      dsimp [code] at hval
      omega
    have hcard := Fintype.card_le_of_injective code hinj
    simpa [Fintype.card_coe] using hcard
  have hSevs : Sevs.card ≤ 3 := by
    let code : Sevs → Fin 3 := fun j =>
      ⟨j.1.val + 1 - X.g.L.stSeverity b, by
        have hj := (Finset.mem_filter.mp j.2).2
        unfold Nat.dist at hj
        omega⟩
    have hinj : Function.Injective code := by
      intro j k h
      apply Subtype.ext
      apply Fin.ext
      have hj := (Finset.mem_filter.mp j.2).2
      have hk := (Finset.mem_filter.mp k.2).2
      unfold Nat.dist at hj hk
      have hval := congrArg Fin.val h
      dsimp [code] at hval
      omega
    have hcard := Fintype.card_le_of_injective code hinj
    simpa [Fintype.card_coe] using hcard
  let P := potentialStates6 X b i
  have hcode : Function.Injective (fun s : P =>
      ((⟨countCoordinate6 X s.1.1 i, by
        have hp := (Finset.mem_filter.mp s.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Counts, countCoordinate6, mergedField6] using hp.2.2.2.1⟩⟩ : Counts),
       (⟨severityCoordinate6 X s.1.1, by
        have hp := (Finset.mem_filter.mp s.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          simpa [Sevs, severityCoordinate6, ChunkLayout6.stSeverity] using hp.2.2.2.2⟩⟩ : Sevs))) := by
    intro s t h
    have hs := (Finset.mem_filter.mp s.2).2
    have ht := (Finset.mem_filter.mp t.2).2
    rcases hs with ⟨hrs, hks, hcs, hci, hss⟩
    rcases ht with ⟨hrt, hkt, hct, hti, hst⟩
    have hci' : countCoordinate6 X s.1.1 i = countCoordinate6 X t.1.1 i :=
      congrArg (fun z : Counts × Sevs => z.1.1) h
    have hsi' : severityCoordinate6 X s.1.1 = severityCoordinate6 X t.1.1 :=
      congrArg (fun z : Counts × Sevs => z.2.1) h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hrs.trans hrt.symm
    · apply Prod.ext
      · have hkey : X.g.L.stKey s.1.1 = X.g.L.stKey t.1.1 := hks.trans hkt.symm
        simpa [ChunkLayout6.stKey] using
          congrArg (fun k : CoarseKey6 (BinVector6 n) => k.1) hkey
      · apply Prod.ext
        · have hkey : X.g.L.stKey s.1.1 = X.g.L.stKey t.1.1 := hks.trans hkt.symm
          simpa [ChunkLayout6.stKey] using
            congrArg (fun k : CoarseKey6 (BinVector6 n) => k.2) hkey
        · apply Prod.ext
          · funext j
            by_cases hji : j = i
            · subst j
              exact hci'
            · apply Fin.ext
              have h1 := hcs j hji
              have h2 := hct j hji
              exact h1.trans h2.symm
          · exact hsi'
  have hPcard : P.card ≤ Counts.card * Sevs.card := by
    calc
      P.card = Fintype.card P := (Fintype.card_coe P).symm
      _ ≤ Fintype.card (Counts × Sevs) := Fintype.card_le_of_injective _ hcode
      _ = Counts.card * Sevs.card := by simp [Fintype.card_coe]
  calc
    (potentialStates6 X b i).card = P.card := rfl
    _ ≤ Counts.card * Sevs.card := hPcard
    _ ≤ 7 * 3 := Nat.mul_le_mul hCounts hSevs
    _ = 21 := by norm_num

theorem fine_length_le_n6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M) (hn : 4 ≤ n) :
    (X.g.L.fineLength : ℝ) ≤ n := by
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (3 / 10 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by norm_num)
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 2 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hprod : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 4) :=
          mul_nonneg (by positivity) (by linarith)
      nlinarith
  have hpow' : (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  calc
    (X.g.L.fineLength : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ) := X.g.L.fine_length_upper
    _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 2 * Real.sqrt (n : ℝ) := by rw [hpow']
    _ ≤ n := by nlinarith

private theorem fineCount_le_length6 {n : ℕ} (L : ChunkLayout6 n) (x : CubeVertex n) (i : Fin L.m) :
    L.fineCount x i ≤ L.fineLength := by
  unfold ChunkLayout6.fineCount
  calc
    ((L.fineChunks i).filter fun a => x a = true).card ≤ (L.fineChunks i).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = L.fineLength := L.fine_chunk_length i

private theorem fineCount_eq_of_agree6 {n : ℕ} (L : ChunkLayout6 n) (u v : CubeVertex n)
    (i : Fin L.m) (h : ∀ a, a ∈ L.fineChunks i → u a = v a) :
    L.fineCount u i = L.fineCount v i := by
  unfold ChunkLayout6.fineCount
  have hfilter : (L.fineChunks i).filter (fun a => u a = true) =
      (L.fineChunks i).filter (fun a => v a = true) := by
    ext a
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨ha, hval⟩
    · exact ⟨ha, by rw [← h a ha]; exact hval⟩
    · exact ⟨ha, by rw [h a ha]; exact hval⟩
  rw [hfilter]

private theorem fineCount_dist_one6 {n : ℕ} (L : ChunkLayout6 n) (u v : CubeVertex n)
    (q : Fin n) (i : Fin L.m) (hq : q ∈ L.fineChunks i)
    (hneq : u q ≠ v q) (hother : ∀ j, j ≠ q → u j = v j) :
    Nat.dist (L.fineCount u i) (L.fineCount v i) = 1 := by
  classical
  let A : Finset (Fin n) := (L.fineChunks i).filter fun a => u a = true
  let B : Finset (Fin n) := (L.fineChunks i).filter fun a => v a = true
  have hBA : u q = false ∧ v q = true ∨ u q = true ∧ v q = false := by
    cases hu : u q <;> cases hv : v q <;> simp_all
  rcases hBA with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hB : B = insert q A := by
      ext a
      by_cases haq : a = q
      · subst a
        simp [A, B, hq, hu, hv]
      · have hsame := hother a haq
        simp [A, B, hq, hu, hv, haq, hsame]
    have hqnot : q ∉ A := by simp [A, hq, hu]
    have hcard : B.card = A.card + 1 := by
      rw [hB, Finset.card_insert_of_notMem hqnot]
    change Nat.dist A.card B.card = 1
    rw [hcard]
    unfold Nat.dist
    omega
  · have hA : A = insert q B := by
      ext a
      by_cases haq : a = q
      · subst a
        simp [A, B, hq, hu, hv]
      · have hsame := hother a haq
        simp [A, B, hq, hu, hv, haq, hsame]
    have hqnot : q ∉ B := by simp [B, hq, hv]
    have hcard : A.card = B.card + 1 := by
      rw [hA, Finset.card_insert_of_notMem hqnot]
    change Nat.dist A.card B.card = 1
    rw [hcard]
    unfold Nat.dist
    omega

private theorem sign_change_near6 {n : ℕ} (L : ChunkLayout6 n) (u v : CubeVertex n)
    (i : Fin L.m) (hcount : Nat.dist (L.fineCount u i) (L.fineCount v i) = 1)
    (hsign : L.sign u i ≠ L.sign v i) :
    Nat.dist (2 * L.fineCount u i) L.fineLength ≤ 3 := by
  change decide (L.fineLength < 2 * L.fineCount u i) ≠
    decide (L.fineLength < 2 * L.fineCount v i) at hsign
  have hstep : L.fineCount v i = L.fineCount u i + 1 ∨
      L.fineCount u i = L.fineCount v i + 1 := by
    unfold Nat.dist at hcount
    omega
  obtain ⟨k, hodd⟩ := L.fine_length_odd
  rcases hstep with h | h
  · rw [h] at hsign
    by_cases h₀ : L.fineLength < 2 * L.fineCount u i
    · by_cases h₁ : L.fineLength < 2 * (L.fineCount u i + 1)
      · simp [h₀, h₁] at hsign
      · omega
    · by_cases h₁ : L.fineLength < 2 * (L.fineCount u i + 1)
      · have hdist : Nat.dist (2 * L.fineCount u i) L.fineLength = 1 := by
          unfold Nat.dist
          omega
        rw [hdist]
        norm_num
      · simp [h₀, h₁] at hsign
  · rw [h] at hsign ⊢
    by_cases h₀ : L.fineLength < 2 * (L.fineCount v i + 1)
    · by_cases h₁ : L.fineLength < 2 * L.fineCount v i
      · simp [h₀, h₁] at hsign
      · have hdist : Nat.dist (2 * (L.fineCount v i + 1)) L.fineLength = 1 := by
          unfold Nat.dist
          omega
        rw [hdist]
        norm_num
    · by_cases h₁ : L.fineLength < 2 * L.fineCount v i
      · omega
      · simp [h₀, h₁] at hsign

private theorem flippable_change_near6 {n : ℕ} (L : ChunkLayout6 n) (u v : CubeVertex n)
    (i : Fin L.m) (hcount : Nat.dist (L.fineCount u i) (L.fineCount v i) = 1)
    (hone : Nat.dist (2 * L.fineCount u i) L.fineLength = 1 ∨
      Nat.dist (2 * L.fineCount v i) L.fineLength = 1) :
    Nat.dist (2 * L.fineCount u i) L.fineLength ≤ 3 := by
  rcases hone with h | h
  · rw [h]
    norm_num
  · have htwice : Nat.dist (2 * L.fineCount u i) (2 * L.fineCount v i) = 2 := by
      rw [Nat.dist_mul_left, hcount]
    calc
      Nat.dist (2 * L.fineCount u i) L.fineLength ≤
      Nat.dist (2 * L.fineCount u i) (2 * L.fineCount v i) +
            Nat.dist (2 * L.fineCount v i) L.fineLength :=
        Nat.dist.triangle_inequality _ _ _
      _ = 3 := by rw [htwice, h]

private theorem changed_fine_coordinate_near6 {n : ℕ} (L : ChunkLayout6 n)
    (u v : CubeVertex n) (i : Fin L.m)
    (hcount : Nat.dist (L.fineCount u i) (L.fineCount v i) = 1)
    (hchange : L.sign u i ≠ L.sign v i ∨
      ((i ∈ L.flippable u) ≠ (i ∈ L.flippable v))) :
    Nat.dist (2 * L.fineCount u i) L.fineLength ≤ 3 := by
  rcases hchange with hsign | hflip
  · exact sign_change_near6 L u v i hcount hsign
  · have hone : Nat.dist (2 * L.fineCount u i) L.fineLength = 1 ∨
        Nat.dist (2 * L.fineCount v i) L.fineLength = 1 := by
      by_cases hu : Nat.dist (2 * L.fineCount u i) L.fineLength = 1
      · exact Or.inl hu
      · by_cases hv : Nat.dist (2 * L.fineCount v i) L.fineLength = 1
        · exact Or.inr hv
        · have heq : (i ∈ L.flippable u) = (i ∈ L.flippable v) := by
            apply propext
            simp [ChunkLayout6.flippable, hu, hv]
          exact False.elim (hflip heq)
    exact flippable_change_near6 L u v i hcount hone

private theorem mergedCount_le_length6 {n : ℕ} (L : ChunkLayout6 n) (x : CubeVertex n) (i : Fin L.m) :
    L.mergedCount x i ≤ L.fineLength := by
  have hc := fineCount_le_length6 L x i
  dsimp [ChunkLayout6.mergedCount]
  split_ifs <;> omega

private theorem merged_eq_fineCount_of_near6 {n : ℕ} (L : ChunkLayout6 n)
    (x : CubeVertex n) (i : Fin L.m)
    (hnear : Nat.dist (2 * L.fineCount x i) L.fineLength ≤ 3) :
    L.mergedCount x i = L.fineCount x i := by
  dsimp [ChunkLayout6.mergedCount]
  split_ifs <;> unfold Nat.dist at hnear <;> omega

private def mergedCountNum6 {n : ℕ} (L : ChunkLayout6 n) (c : ℕ) : ℕ :=
  if 2 * c = L.fineLength + 13 then c - 1
  else if 2 * c + 13 = L.fineLength then c + 1 else c

private theorem mergedCountNum6_succ {n : ℕ} (L : ChunkLayout6 n) (c : ℕ) :
    Nat.dist (mergedCountNum6 L (c + 1)) (mergedCountNum6 L c) ≤ 3 := by
  unfold mergedCountNum6
  split_ifs <;> unfold Nat.dist <;> omega

private theorem mergedCountNum6_dist {n : ℕ} (L : ChunkLayout6 n) {c d : ℕ}
    (hcd : Nat.dist c d = 1) : Nat.dist (mergedCountNum6 L c) (mergedCountNum6 L d) ≤ 3 := by
  have hstep : d = c + 1 ∨ c = d + 1 := by
    unfold Nat.dist at hcd
    omega
  rcases hstep with h | h
  · subst d
    simpa [Nat.dist_comm] using mergedCountNum6_succ L c
  · subst c
    simpa [Nat.dist_comm] using mergedCountNum6_succ L d

private theorem mergedCount_dist_le_three6 {n : ℕ} (L : ChunkLayout6 n) (u v : CubeVertex n)
    (i : Fin L.m) (h : Nat.dist (L.fineCount u i) (L.fineCount v i) = 1) :
    Nat.dist (L.mergedCount u i) (L.mergedCount v i) ≤ 3 := by
  simpa [ChunkLayout6.mergedCount, mergedCountNum6] using
    mergedCountNum6_dist L h

private theorem natDist_min_right {a b c : ℕ} :
    Nat.dist (min a c) (min b c) ≤ Nat.dist a b := by
  by_cases hac : a ≤ c
  · by_cases hbc : b ≤ c
    · simp [Nat.min_eq_left hac, Nat.min_eq_left hbc]
    · have hcb : c ≤ b := Nat.le_of_not_ge hbc
      unfold Nat.dist
      simp only [Nat.min_eq_left hac, Nat.min_eq_right hcb]
      omega
  · have hca : c ≤ a := Nat.le_of_not_ge hac
    by_cases hbc : b ≤ c
    · unfold Nat.dist
      simp only [Nat.min_eq_right hca, Nat.min_eq_left hbc]
      omega
    · have hcb : c ≤ b := Nat.le_of_not_ge hbc
      simp [Nat.min_eq_right hca, Nat.min_eq_right hcb]

private theorem near_card_le_severity6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.State) (hb : b ∈ X.g.L.oddStates) (hn : 4 ≤ n) :
    (nearCoordsState6 X b).card ≤ X.g.L.stSeverity b := by
  classical
  obtain ⟨u, hu, hstate⟩ := Finset.mem_image.mp hb
  have hlen := fine_length_le_n6 X hn
  have hnearSub : nearCoordsState6 X b ⊆ Finset.univ.filter fun i =>
      Nat.dist (2 * X.g.L.fineCount u i) X.g.L.fineLength ≤ 11 := by
    intro i hi
    have hiNear := (Finset.mem_filter.mp hi).2
    have hfield : mergedField6 X b i = X.g.L.mergedCount u i := by
      rw [← hstate]
      rw [mergedField_stateOf6]
      exact Nat.min_eq_left (mergedCount_le_length6 X.g.L u i |>.trans (by exact_mod_cast hlen))
    have hdist : Nat.dist (2 * X.g.L.fineCount u i) X.g.L.fineLength ≤ 11 := by
      have hd := hiNear
      rw [hfield] at hd
      dsimp [ChunkLayout6.mergedCount] at hd
      unfold Nat.dist at hd ⊢
      split_ifs at hd <;> omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩
  calc
    (nearCoordsState6 X b).card ≤
        (Finset.univ.filter fun i => Nat.dist (2 * X.g.L.fineCount u i) X.g.L.fineLength ≤ 11).card :=
      Finset.card_le_card hnearSub
    _ = X.g.L.severity u := by rfl
    _ = X.g.L.stSeverity b := by
      calc
        X.g.L.severity u = X.g.L.stSeverity (X.g.L.stateOf u) := (X.facts.severity_eq u).symm
        _ = X.g.L.stSeverity b := by rw [hstate]

private theorem edge_fine_state_data6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    {b a : X.State} (u v : CubeVertex n) (hub : X.g.L.stateOf u = b)
    (hva : X.g.L.stateOf v = a) (hadj : (cube n).Adj u v)
    (q : Fin n) (i : Fin X.g.L.m) (hqi : q ∈ X.g.L.fineChunks i)
    (hneq : u q ≠ v q) (hother : ∀ j, j ≠ q → u j = v j) :
    X.g.L.stKey a = X.g.L.stKey b ∧ a.1 = b.1 ∧
      (∀ j, j ≠ i → mergedField6 X a j = mergedField6 X b j) ∧
      Nat.dist (mergedField6 X a i) (mergedField6 X b i) ≤ 3 ∧
      Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) ≤ 1 := by
  have hqnotC : ∀ k, q ∉ X.g.L.coarseChunks k := by
    intro k hqk
    exact (Finset.disjoint_left.mp (X.g.L.chunks_disjoint.2.1 k i)) hqk hqi
  have hsameC : ∀ k x, x ∈ X.g.L.coarseChunks k → u x = v x := by
    intro k x hx
    by_cases hxq : x = q
    · subst x
      exact False.elim (hqnotC k hx)
    · exact hother x hxq
  have hkeyuv := X.g.flips.noncoarse_flip_key u v hadj hsameC
  have hku : X.g.L.key u = X.g.L.stKey b := by
    calc
      X.g.L.key u = X.g.L.stKey (X.g.L.stateOf u) := (X.facts.key_eq u).symm
      _ = X.g.L.stKey b := by rw [hub]
  have hkv : X.g.L.key v = X.g.L.stKey a := by
    calc
      X.g.L.key v = X.g.L.stKey (X.g.L.stateOf v) := (X.facts.key_eq v).symm
      _ = X.g.L.stKey a := by rw [hva]
  have hkey : X.g.L.stKey a = X.g.L.stKey b := by
    calc
      X.g.L.stKey a = X.g.L.key v := hkv.symm
      _ = X.g.L.key u := hkeyuv.symm
      _ = X.g.L.stKey b := hku
  have hqnotR : q ∉ X.g.L.residual :=
    (Finset.disjoint_left.mp (X.g.L.chunks_disjoint.2.2.2.2 i)) hqi
  have hresuv : (X.g.L.stateOf u).1 = (X.g.L.stateOf v).1 := by
    funext x
    have hxq : x.1 ≠ q := by
      intro hx
      have hqR : q ∈ X.g.L.residual := by simpa [hx] using x.2
      exact hqnotR hqR
    exact hother x.1 hxq
  have hres : a.1 = b.1 := by
    calc
      a.1 = (X.g.L.stateOf v).1 := by rw [← hva]
      _ = (X.g.L.stateOf u).1 := hresuv.symm
      _ = b.1 := by rw [hub]
  have hcounts : ∀ j, j ≠ i → mergedField6 X a j = mergedField6 X b j := by
    intro j hji
    have hqnot : q ∉ X.g.L.fineChunks j := by
      intro hqj
      exact (Finset.disjoint_left.mp
        (X.g.L.chunks_disjoint.2.2.1 i j (Ne.symm hji))) hqi hqj
    have hagree : ∀ x, x ∈ X.g.L.fineChunks j → u x = v x := by
      intro x hx
      by_cases hxq : x = q
      · subst x
        exact False.elim (hqnot hx)
      · exact hother x hxq
    have hfc := fineCount_eq_of_agree6 X.g.L u v j hagree
    have hmerge : X.g.L.mergedCount u j = X.g.L.mergedCount v j := by
      simp [ChunkLayout6.mergedCount, hfc]
    calc
      mergedField6 X a j = mergedField6 X (X.g.L.stateOf v) j := by rw [hva]
      _ = mergedField6 X (X.g.L.stateOf u) j := by
        rw [mergedField_stateOf6, mergedField_stateOf6]
        exact congrArg (fun c => min c n) hmerge.symm
      _ = mergedField6 X b j := by rw [hub]
  have hfc := fineCount_dist_one6 X.g.L u v q i hqi hneq hother
  have hmerge := mergedCount_dist_le_three6 X.g.L u v i hfc
  have hcountUV : Nat.dist (mergedField6 X (X.g.L.stateOf v) i)
      (mergedField6 X (X.g.L.stateOf u) i) ≤ 3 := by
    calc
      Nat.dist (mergedField6 X (X.g.L.stateOf v) i) (mergedField6 X (X.g.L.stateOf u) i) ≤
          Nat.dist (X.g.L.mergedCount v i) (X.g.L.mergedCount u i) := by
            rw [mergedField_stateOf6, mergedField_stateOf6]
            exact natDist_min_right
      _ = Nat.dist (X.g.L.mergedCount u i) (X.g.L.mergedCount v i) := Nat.dist_comm _ _
      _ ≤ 3 := hmerge
  have hcount : Nat.dist (mergedField6 X a i) (mergedField6 X b i) ≤ 3 := by
    calc
      Nat.dist (mergedField6 X a i) (mergedField6 X b i) =
          Nat.dist (mergedField6 X (X.g.L.stateOf v) i) (mergedField6 X (X.g.L.stateOf u) i) := by
            rw [hva, hub]
      _ ≤ 3 := hcountUV
  have hedge := (edge_key_severity X.g.L X.g.flips u v hadj).2
  have hsevUV : Nat.dist (X.g.L.stSeverity (X.g.L.stateOf v))
      (X.g.L.stSeverity (X.g.L.stateOf u)) ≤ 1 := by
    calc
      Nat.dist (X.g.L.stSeverity (X.g.L.stateOf v)) (X.g.L.stSeverity (X.g.L.stateOf u)) =
          Nat.dist (min (X.g.L.severity v) X.g.L.m) (min (X.g.L.severity u) X.g.L.m) := by
            rw [stSeverity_stateOf6, stSeverity_stateOf6]
      _ ≤ Nat.dist (X.g.L.severity v) (X.g.L.severity u) := natDist_min_right
      _ = Nat.dist (X.g.L.severity u) (X.g.L.severity v) := Nat.dist_comm _ _
      _ ≤ 1 := hedge
  have hsev : Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) ≤ 1 := by
    calc
      Nat.dist (X.g.L.stSeverity a) (X.g.L.stSeverity b) =
          Nat.dist (X.g.L.stSeverity (X.g.L.stateOf v))
            (X.g.L.stSeverity (X.g.L.stateOf u)) := by rw [hva, hub]
      _ ≤ 1 := hsevUV
  exact ⟨hkey, hres, hcounts, hcount, hsev⟩

private theorem changed_neighbor_state6 {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    {b a : X.State} (ha : a ∈ X.g.L.stNbr b)
    (hbad : X.g.L.stSign a ≠ X.g.L.stSign b ∨
      X.g.L.stFlippable a ≠ X.g.L.stFlippable b) (hn : 4 ≤ n) :
    ∃ i, i ∈ nearCoordsState6 X b ∧
      (⟨a, ha⟩ : X.g.L.stNbr b) ∈ potentialStates6 X b i := by
  classical
  obtain ⟨u, v, huodd, hveven, hub, hva, hadj⟩ := stNbr_witness6 X.g.L b a ha
  obtain ⟨q, hqdiff, hqother, hkind⟩ := edge_coord_in_chunks X.g.L u v hadj
  have hsignA : X.g.L.stSign a = X.g.L.sign v := by
    calc
      X.g.L.stSign a = X.g.L.stSign (X.g.L.stateOf v) := by rw [← hva]
      _ = X.g.L.sign v := X.facts.sign_eq v
  have hsignB : X.g.L.stSign b = X.g.L.sign u := by
    calc
      X.g.L.stSign b = X.g.L.stSign (X.g.L.stateOf u) := by rw [← hub]
      _ = X.g.L.sign u := X.facts.sign_eq u
  have hflipA : X.g.L.stFlippable a = X.g.L.flippable v := by
    calc
      X.g.L.stFlippable a = X.g.L.stFlippable (X.g.L.stateOf v) := by rw [← hva]
      _ = X.g.L.flippable v := X.facts.flippable_eq v
  have hflipB : X.g.L.stFlippable b = X.g.L.flippable u := by
    calc
      X.g.L.stFlippable b = X.g.L.stFlippable (X.g.L.stateOf u) := by rw [← hub]
      _ = X.g.L.flippable u := X.facts.flippable_eq u
  rcases hkind with hc | hrest
  · obtain ⟨k, hqC⟩ := hc
    have hsameFine : ∀ j x, x ∈ X.g.L.fineChunks j → u x = v x := by
      intro j x hx
      by_cases hxq : x = q
      · subst x
        exact False.elim ((Finset.disjoint_left.mp (X.g.L.chunks_disjoint.2.1 k j)) hqC hx)
      · exact hqother x hxq
    have hgood := X.g.flips.nonfine_flip_fine u v hadj hsameFine
    have hsignEq : X.g.L.stSign a = X.g.L.stSign b := by
      calc
        X.g.L.stSign a = X.g.L.sign v := hsignA
        _ = X.g.L.sign u := hgood.1.symm
        _ = X.g.L.stSign b := hsignB.symm
    have hflipEq : X.g.L.stFlippable a = X.g.L.stFlippable b := by
      calc
        X.g.L.stFlippable a = X.g.L.flippable v := hflipA
        _ = X.g.L.flippable u := hgood.2.1.symm
        _ = X.g.L.stFlippable b := hflipB.symm
    have : False := by
      rcases hbad with hs | hf
      · exact hs hsignEq
      · exact hf hflipEq
    exact False.elim this
  · rcases hrest with hfine | hr
    · obtain ⟨i, hqi⟩ := hfine
      have hcount := fineCount_dist_one6 X.g.L u v q i hqi hqdiff hqother
      have hnearRaw : Nat.dist (2 * X.g.L.fineCount u i) X.g.L.fineLength ≤ 3 := by
        rcases hbad with hs | hf
        · have hsignUV : X.g.L.sign u ≠ X.g.L.sign v := by
            intro heq
            exact hs (by
              calc
                X.g.L.stSign a = X.g.L.sign v := hsignA
                _ = X.g.L.sign u := heq.symm
                _ = X.g.L.stSign b := hsignB.symm)
          have hsignOff := X.g.flips.fine_flip_sign u v i hadj ⟨q, hqi, hqdiff⟩
          have hsignI : X.g.L.sign u i ≠ X.g.L.sign v i := by
            by_contra heq
            apply hsignUV
            funext j
            by_cases hji : j = i
            · subst j
              exact heq
            · exact hsignOff j hji
          exact changed_fine_coordinate_near6 X.g.L u v i hcount (Or.inl hsignI)
        · have hflipUV : X.g.L.flippable u ≠ X.g.L.flippable v := by
            intro heq
            exact hf (by
              calc
                X.g.L.stFlippable a = X.g.L.flippable v := hflipA
                _ = X.g.L.flippable u := heq.symm
                _ = X.g.L.stFlippable b := hflipB.symm)
          have hmemOff : ∀ j, j ≠ i →
              ((j ∈ X.g.L.flippable u) ↔ (j ∈ X.g.L.flippable v)) := by
            intro j
            intro hji
            have hqnot : q ∉ X.g.L.fineChunks j := by
              intro hqj
              exact (Finset.disjoint_left.mp
                (X.g.L.chunks_disjoint.2.2.1 i j (Ne.symm hji))) hqi hqj
            have hsame : ∀ x, x ∈ X.g.L.fineChunks j → u x = v x := by
              intro x hx
              by_cases hxq : x = q
              · subst x
                exact False.elim (hqnot hx)
              · exact hqother x hxq
            have hfc := fineCount_eq_of_agree6 X.g.L u v j hsame
            simpa [ChunkLayout6.flippable, hfc]
          have hmemI : (i ∈ X.g.L.flippable u) ≠ (i ∈ X.g.L.flippable v) := by
            by_contra hsame
            have hprop : (i ∈ X.g.L.flippable u) = (i ∈ X.g.L.flippable v) := hsame
            apply hflipUV
            apply Finset.ext
            intro j
            by_cases hji : j = i
            · subst j
              exact Iff.of_eq hprop
            · exact hmemOff j hji
          exact changed_fine_coordinate_near6 X.g.L u v i hcount (Or.inr hmemI)
      have hdata := edge_fine_state_data6 X u v hub hva hadj q i hqi hqdiff hqother
      have hlen := fine_length_le_n6 X hn
      have hcenterField : mergedField6 X b i = X.g.L.fineCount u i := by
        calc
          mergedField6 X b i = mergedField6 X (X.g.L.stateOf u) i := by rw [← hub]
          _ = X.g.L.mergedCount u i := by
            rw [mergedField_stateOf6]
            exact Nat.min_eq_left (mergedCount_le_length6 X.g.L u i |>.trans (by exact_mod_cast hlen))
          _ = X.g.L.fineCount u i := merged_eq_fineCount_of_near6 X.g.L u i hnearRaw
      have hnear : i ∈ nearCoordsState6 X b := by
        change i ∈ Finset.univ.filter
          (fun j => Nat.dist (2 * mergedField6 X b j) X.g.L.fineLength ≤ 3)
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hcenterField]
        exact hnearRaw
      have hpotential : potentialState6 X b i a :=
        ⟨hdata.2.1, hdata.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2⟩
      have hmem : (⟨a, ha⟩ : X.g.L.stNbr b) ∈ potentialStates6 X b i := by
        change (⟨a, ha⟩ : X.g.L.stNbr b) ∈
          Finset.univ.filter (fun s => potentialState6 X b i s.1)
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, hpotential⟩
      exact ⟨i, hnear, hmem⟩
    ·
      have hsameFine : ∀ j x, x ∈ X.g.L.fineChunks j → u x = v x := by
        intro j x hx
        by_cases hxq : x = q
        · subst x
          have hqnot : q ∉ X.g.L.fineChunks j :=
            (Finset.disjoint_right.mp (X.g.L.chunks_disjoint.2.2.2.2 j)) hr
          exact False.elim (hqnot hx)
        · exact hqother x hxq
      have hgood := X.g.flips.nonfine_flip_fine u v hadj hsameFine
      have hsignEq : X.g.L.stSign a = X.g.L.stSign b := by
        calc
          X.g.L.stSign a = X.g.L.sign v := hsignA
          _ = X.g.L.sign u := hgood.1.symm
          _ = X.g.L.stSign b := hsignB.symm
      have hflipEq : X.g.L.stFlippable a = X.g.L.stFlippable b := by
        calc
          X.g.L.stFlippable a = X.g.L.flippable v := hflipA
          _ = X.g.L.flippable u := hgood.2.1.symm
          _ = X.g.L.stFlippable b := hflipB.symm
      have : False := by
        rcases hbad with hs | hf
        · exact hs hsignEq
        · exact hf hflipEq
      exact False.elim this

theorem descriptorBadStates6_card {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (b : X.State) (hb : b ∈ X.g.L.oddStates)
    (hn : 4 ≤ n) :
    let Trans : Finset (X.g.L.stNbr b) := (Finset.univ : Finset (X.g.L.stNbr b)).filter
      (fun a => X.stMode a.1 ≠ X.stMode b)
    let Var : Finset (X.g.L.stNbr b) := (Finset.univ : Finset (X.g.L.stNbr b)).filter
      (fun a => (X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
        (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
          X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b))
    let Bad : Finset (X.g.L.stNbr b) := Trans ∪ Var
    Bad.card ≤ 1 + 21 * (X.J + 2) := by
  classical
  dsimp only
  let Trans : Finset (X.g.L.stNbr b) := Finset.univ.filter
    (fun a => X.stMode a.1 ≠ X.stMode b)
  let Var : Finset (X.g.L.stNbr b) := Finset.univ.filter
    (fun a => (X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
      (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
        X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b))
  let Potential : Finset (X.g.L.stNbr b) :=
    (nearCoordsState6 X b).biUnion fun i => potentialStates6 X b i
  have htrans : Trans.card ≤ 1 := by
    have hattach : Trans.card =
        ((X.g.L.stNbr b).filter fun a => X.stMode a ≠ X.stMode b).card := by
      have h := congrArg Finset.card
        (Finset.filter_attach (fun a : X.State => X.stMode a ≠ X.stMode b)
          (X.g.L.stNbr b))
      simpa [Trans] using h
    have hraw : ((X.g.L.stNbr b).filter fun a => X.stMode a ≠ X.stMode b).card ≤ 1 := by
      change ((X.g.L.stNbr b).filter
        (fun a => modeOf6 X.J (X.g.L.stSeverity a) ≠ modeOf6 X.J (X.g.L.stSeverity b))).card ≤ 1
      exact X.facts.low_high_one b
    rw [hattach]
    exact hraw
  have hvarSub : Var ⊆ Potential := by
    intro a ha
    have hp := (Finset.mem_filter.mp ha).2
    have hbad := hp.2
    obtain ⟨i, hi, hpot⟩ := changed_neighbor_state6 X a.2 hbad hn
    exact Finset.mem_biUnion.mpr ⟨i, hi, hpot⟩
  have hpotential : Potential.card ≤ (nearCoordsState6 X b).card * 21 := by
    calc
      Potential.card ≤ ∑ i ∈ nearCoordsState6 X b, (potentialStates6 X b i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ nearCoordsState6 X b, 21 := by
        apply Finset.sum_le_sum
        intro i hi
        exact potentialStates6_card X b i
      _ = (nearCoordsState6 X b).card * 21 := by simp
  have hVarCard : Var.card ≤ 21 * (X.J + 2) := by
    by_cases hlow : X.stMode b = .low
    · have hnearBound : (nearCoordsState6 X b).card ≤ X.J + 2 := by
        have hsev : X.g.L.stSeverity b ≤ X.J := by
          by_cases hle : X.g.L.stSeverity b ≤ X.J
          · exact hle
          · simp [Ctx6.stMode, modeOf6, hle] at hlow
        exact le_trans (near_card_le_severity6 X b hb hn) (by omega)
      calc
        Var.card ≤ Potential.card := Finset.card_le_card hvarSub
        _ ≤ (nearCoordsState6 X b).card * 21 := hpotential
        _ ≤ (X.J + 2) * 21 := Nat.mul_le_mul_right 21 hnearBound
        _ = 21 * (X.J + 2) := Nat.mul_comm _ _
    · by_cases hvar : Var.Nonempty
      · obtain ⟨a, ha⟩ := hvar
        have hp := (Finset.mem_filter.mp ha).2.1
        rcases hp with hlow | hboundary
        · have hsev : X.g.L.stSeverity b ≤ X.J := by
            by_cases hle : X.g.L.stSeverity b ≤ X.J
            · exact hle
            · simp [Ctx6.stMode, modeOf6, hle] at hlow
          have hnearBound : (nearCoordsState6 X b).card ≤ X.J + 2 :=
            le_trans (near_card_le_severity6 X b hb hn) (by omega)
          calc
            Var.card ≤ Potential.card := Finset.card_le_card hvarSub
            _ ≤ (nearCoordsState6 X b).card * 21 := hpotential
            _ ≤ (X.J + 2) * 21 := Nat.mul_le_mul_right 21 hnearBound
            _ = 21 * (X.J + 2) := Nat.mul_comm _ _
        · have hneigh := (neighbor_key_severity6 X a.2).2
          have hnearBound : (nearCoordsState6 X b).card ≤ X.J + 2 := by
            have htri := Nat.dist_tri_right (X.g.L.stSeverity a.1) (X.g.L.stSeverity b)
            rw [hboundary] at htri
            unfold Nat.dist at htri hneigh
            have hbound : X.g.L.stSeverity b ≤ X.J + 2 := by omega
            exact le_trans (near_card_le_severity6 X b hb hn) hbound
          calc
            Var.card ≤ Potential.card := Finset.card_le_card hvarSub
            _ ≤ (nearCoordsState6 X b).card * 21 := hpotential
            _ ≤ (X.J + 2) * 21 := Nat.mul_le_mul_right 21 hnearBound
            _ = 21 * (X.J + 2) := Nat.mul_comm _ _
      · have hempty : Var = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
          intro a ha
          exact hvar ⟨a, ha⟩)
        have hcard : Var.card = 0 := by simp [hempty]
        omega
  have hBadCard : (Trans ∪ Var).card ≤ Trans.card + Var.card := Finset.card_union_le _ _
  have : (Trans ∪ Var).card ≤ 1 + 21 * (X.J + 2) := by omega
  exact this

theorem normalize6_weight_bound {Ω : Type*} [Fintype Ω]
    (f g : Ω → ℝ) (fallback x : Ω) (ε C : ℝ)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hε : 0 < ε) (hC : 0 ≤ C)
    (hF : ε * (∑ z, g z) ≤ ∑ z, f z)
    (hG : 0 < ∑ z, g z)
    (hpoint : ∀ z, f z ≤ C * g z) :
    (normalize6 f fallback).w x ≤ (C / ε) * (normalize6 g fallback).w x := by
  have hmaxf : ∑ z, max 0 (f z) = ∑ z, f z := by
    apply Finset.sum_congr rfl
    intro z hz
    exact max_eq_right (hf z)
  have hmaxg : ∑ z, max 0 (g z) = ∑ z, g z := by
    apply Finset.sum_congr rfl
    intro z hz
    exact max_eq_right (hg z)
  have hsumf : 0 < ∑ z, max 0 (f z) := by
    rw [hmaxf]
    exact lt_of_lt_of_le (mul_pos hε hG) hF
  have hsumg : 0 < ∑ z, max 0 (g z) := by
    rw [hmaxg]
    exact hG
  have hden : ε * (∑ z, max 0 (g z)) ≤ ∑ z, max 0 (f z) := by
    simpa [hmaxf, hmaxg] using hF
  have hnum : 0 ≤ C * g x := mul_nonneg hC (hg x)
  unfold normalize6
  rw [dif_pos hsumf, dif_pos hsumg]
  change max 0 (f x) / (∑ z, max 0 (f z)) ≤
    (C / ε) * (max 0 (g x) / ∑ z, max 0 (g z))
  rw [max_eq_right (hf x), max_eq_right (hg x)]
  have hεG : 0 < ε * (∑ z, max 0 (g z)) := by
    rw [hmaxg]
    exact mul_pos hε hG
  have hfrac : C * g x / (∑ z, max 0 (f z)) ≤ C * g x / (ε * (∑ z, max 0 (g z))) := by
    apply (div_le_div_iff₀ hsumf hεG).2
    exact mul_le_mul_of_nonneg_left hden hnum
  calc
    f x / (∑ z, max 0 (f z)) ≤ C * g x / (∑ z, max 0 (f z)) :=
      div_le_div_of_nonneg_right (hpoint x) hsumf.le
    _ ≤ C * g x / (ε * (∑ z, max 0 (g z))) := hfrac
    _ = (C / ε) * (g x / (∑ z, max 0 (g z))) := by
      rw [hmaxg]
      field_simp

/-- A subdensity of mass below `ε` has at most `ε` mass under its reference law. -/
theorem subdensity_small_mass6 {Ω : Type*} [Fintype Ω]
    (Q : FinProb Ω) (m : Ω → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) :
    (∑ x, if m x < ε then Q.w x * m x else 0) ≤ ε := by
  calc
    (∑ x, if m x < ε then Q.w x * m x else 0) ≤ ∑ x, Q.w x * ε := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases h : m x < ε
      · simp only [if_pos h]
        exact mul_le_mul_of_nonneg_left (le_of_lt h) (Q.nonneg x)
      · simp only [if_neg h]
        exact mul_nonneg (Q.nonneg x) hε
    _ = ε := by simp [← Finset.sum_mul, Q.sum_eq_one]

/-- A subdensity smaller than `ε` times an integrable deleted density has mass at most `ε`. -/
theorem subdensity_ratio_small_mass6 {Ω : Type*} [Fintype Ω]
    (Q : FinProb Ω) (m mdel : Ω → ℝ) (ε : ℝ)
    (hmdel : ∀ x, 0 ≤ mdel x)
    (hε : 0 ≤ ε) (hdel : ∑ x, Q.w x * mdel x ≤ 1) :
    (∑ x, if m x < ε * mdel x then Q.w x * m x else 0) ≤ ε := by
  calc
    (∑ x, if m x < ε * mdel x then Q.w x * m x else 0) ≤
        ∑ x, Q.w x * (ε * mdel x) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases h : m x < ε * mdel x
      · simp only [if_pos h]
        exact mul_le_mul_of_nonneg_left (le_of_lt h) (Q.nonneg x)
      · simp only [if_neg h]
        exact mul_nonneg (Q.nonneg x) (mul_nonneg hε (hmdel x))
    _ = ∑ x, ε * (Q.w x * mdel x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = ε * (∑ x, Q.w x * mdel x) := by rw [← Finset.mul_sum]
    _ ≤ ε := by
      calc
        ε * (∑ x, Q.w x * mdel x) ≤ ε * 1 := mul_le_mul_of_nonneg_left hdel hε
        _ = ε := by ring

theorem mixture_subdensity_bound6 {Ξ Ω : Type*} [Fintype Ξ] [Fintype Ω]
    (π : FinProb Ξ) (Q : FinProb Ω) (P : Ξ → FinProb Ω)
    (gate : Ξ → Prop) (lik : Ξ → Ω → ℝ) (m θ : Ω → ℝ) (ε : ℝ)
    (hm : ∀ ω, m ω = ∑ ξ, if gate ξ then π.w ξ * lik ξ ω else 0)
    (hdom : ∀ ξ ω, gate ξ → (P ξ).w ω ≤ Q.w ω * lik ξ ω)
    (hsmall : (∑ ω, if m ω < θ ω then Q.w ω * m ω else 0) ≤ ε) :
    ∑ ξ, π.w ξ * (P ξ).pr (fun ω => gate ξ ∧ m ω < θ ω) ≤ ε := by
  classical
  calc
    (∑ ξ, π.w ξ * (P ξ).pr (fun ω => gate ξ ∧ m ω < θ ω)) ≤
        ∑ ξ, π.w ξ * ∑ ω, if gate ξ ∧ m ω < θ ω then Q.w ω * lik ξ ω else 0 := by
      apply Finset.sum_le_sum
      intro ξ hξ
      apply mul_le_mul_of_nonneg_left _ (π.nonneg ξ)
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω hω
      by_cases he : gate ξ ∧ m ω < θ ω
      · simp only [if_pos he]
        exact hdom ξ ω he.1
      · simp only [if_neg he]
        rfl
    _ = ∑ ω, if m ω < θ ω then Q.w ω * m ω else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hlt : m ω < θ ω
      · simp [hlt]
        rw [hm ω]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ hξ
        by_cases hg : gate ξ
        · simp only [if_pos hg]
          ring
        · simp [hg]
      · simp [hlt]
    _ ≤ ε := hsmall

/-- Products of coordinate likelihoods with integral at most one also have integral at most one. -/
theorem pi_product_density_le_one6 {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (Q : ∀ i, FinProb (Ω i)) (f : ∀ i, Ω i → ℝ)
    (hf : ∀ i x, 0 ≤ f i x)
    (hInt : ∀ i, ∑ x, (Q i).w x * f i x ≤ 1) :
    ∑ ω : ∀ i, Ω i, (∏ i, (Q i).w (ω i)) * (∏ i, f i (ω i)) ≤ 1 := by
  classical
  have hfactor : ∀ ω : ∀ i, Ω i,
      (∏ i, (Q i).w (ω i)) * (∏ i, f i (ω i)) =
        ∏ i, ((Q i).w (ω i) * f i (ω i)) := by
    intro ω
    rw [← Finset.prod_mul_distrib]
  calc
    (∑ ω : ∀ i, Ω i, (∏ i, (Q i).w (ω i)) * (∏ i, f i (ω i))) =
        ∑ ω : ∀ i, Ω i, ∏ i, ((Q i).w (ω i) * f i (ω i)) := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact hfactor ω
    _ = ∏ i, ∑ x, (Q i).w x * f i x :=
      (Fintype.prod_sum (fun i x => (Q i).w x * f i x)).symm
    _ ≤ 1 := by
      have hnonneg (i : ι) : 0 ≤ ∑ x, (Q i).w x * f i x :=
        Finset.sum_nonneg fun x hx => mul_nonneg ((Q i).nonneg x) (hf i x)
      have hprod : ∀ s : Finset ι, (∏ i ∈ s, ∑ x, (Q i).w x * f i x) ≤ 1 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi]
            exact mul_le_one₀ (hInt i)
              (Finset.prod_nonneg fun j hj => hnonneg j) ih
      simpa using hprod Finset.univ

private theorem tupleLawOn_weight6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (S : Finset X.Name)
    (T : FinProb X.ι) (o : X.Tuple) :
    (X.tupleLawOn H S T).w o = T.w o.1 * ∏ r, (X.labelLaw H S o.1).w (o.2 r) := by
  simp [Ctx6.tupleLawOn, FinProb.bind, FinProb.pi]

private theorem safeRatio_mul_of_ne6 {a b : ℝ} (hb : b ≠ 0) :
    b * safeRatio6 a b = a := by
  unfold safeRatio6
  rw [if_neg hb]
  field_simp

private theorem tupleLawOn_ratio6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (Hξ H : X.Hist)
    (Sraw Sref : Finset X.Name) (T Tref : FinProb X.ι) (o : X.Tuple)
    (hTag : Tref.w o.1 ≠ 0)
    (hLabel : ∀ r, (X.labelLaw H Sref o.1).w (o.2 r) ≠ 0) :
    (X.tupleLawOn Hξ Sraw T).w o =
      (X.tupleLawOn H Sref Tref).w o *
        (safeRatio6 (T.w o.1) (Tref.w o.1) *
          ∏ r, safeRatio6 ((X.labelLaw Hξ Sraw o.1).w (o.2 r))
            ((X.labelLaw H Sref o.1).w (o.2 r))) := by
  rw [tupleLawOn_weight6, tupleLawOn_weight6]
  have hTag' := safeRatio_mul_of_ne6 (a := T.w o.1) (b := Tref.w o.1) hTag
  have hLabels (r : Fin X.k) :=
    safeRatio_mul_of_ne6
      (a := (X.labelLaw Hξ Sraw o.1).w (o.2 r))
      (b := (X.labelLaw H Sref o.1).w (o.2 r)) (hLabel r)
  calc
    T.w o.1 * ∏ r, (X.labelLaw Hξ Sraw o.1).w (o.2 r) =
        (Tref.w o.1 * safeRatio6 (T.w o.1) (Tref.w o.1)) *
          ∏ r, (X.labelLaw Hξ Sraw o.1).w (o.2 r) := by rw [hTag']
    _ = (Tref.w o.1 * safeRatio6 (T.w o.1) (Tref.w o.1)) *
          ∏ r, ((X.labelLaw H Sref o.1).w (o.2 r) *
            safeRatio6 ((X.labelLaw Hξ Sraw o.1).w (o.2 r))
              ((X.labelLaw H Sref o.1).w (o.2 r))) := by
        congr 1
        apply Finset.prod_congr rfl
        intro r hr
        exact (hLabels r).symm
    _ = (Tref.w o.1 * ∏ r, (X.labelLaw H Sref o.1).w (o.2 r)) *
          (safeRatio6 (T.w o.1) (Tref.w o.1) *
            ∏ r, safeRatio6 ((X.labelLaw Hξ Sraw o.1).w (o.2 r))
              ((X.labelLaw H Sref o.1).w (o.2 r))) := by
        rw [Finset.prod_mul_distrib]
        ring

private theorem withHid_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (ℓ : X.HKey) (ξ : Fin N)
    (hbase : H.1 = H'.1) (hother : ∀ h, h ≠ ℓ → H.2 h = H'.2 h) :
    X.withHid H ℓ ξ = X.withHid H' ℓ ξ := by
  apply Prod.ext
  · exact hbase
  · funext h
    by_cases hh : h = ℓ
    · subst h
      simp [Ctx6.withHid]
    · simp [Ctx6.withHid, Function.update, hh, hother h hh]

private theorem finProb_ext_weight6 {Ω : Type*} [Fintype Ω]
    {P Q : FinProb Ω} (h : P.w = Q.w) : P = Q := by
  cases P with
  | mk w hnon hsum =>
    cases Q with
    | mk w' hnon' hsum' =>
      dsimp at h
      subst w'
      have hnonEq : hnon = hnon' := Subsingleton.elim _ _
      have hsumEq : hsum = hsum' := Subsingleton.elim _ _
      cases hnonEq
      cases hsumEq
      rfl

private theorem tagPost_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (β : X.Ty)
    (S : Finset X.HKey) (hbase : H.1 = H'.1)
    (hobs : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    X.tagPost H β S = X.tagPost H' β S := by
  have hweight : X.tagWeight H β S = X.tagWeight H' β S := by
    funext i
    unfold Ctx6.tagWeight
    rw [hbase]
    congr 1
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hobs ℓ hℓ]
  apply finProb_ext_weight6
  exact congrArg (fun w => (normalize6 w X.i₀).w) hweight

private theorem labelLaw_eq_of_varVal_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (S : Finset X.Name) (i : X.ι)
    (hval : ∀ nm ∈ S, X.varVal H nm = X.varVal H' nm) :
    X.labelLaw H S i = X.labelLaw H' S i := by
  have hnbhd : X.reqNbhd H S = X.reqNbhd H' S := by
    apply Finset.ext
    intro x
    simp only [Ctx6.reqNbhd, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx nm hnm
      rw [← hval nm hnm]
      exact hx nm hnm
    · intro hx nm hnm
      rw [hval nm hnm]
      exact hx nm hnm
  unfold Ctx6.labelLaw
  rw [hnbhd]

private theorem tupleLawOn_eq_of_labelLaw_eq6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (S : Finset X.Name)
    (T : FinProb X.ι) (hLabel : ∀ i, X.labelLaw H S i = X.labelLaw H' S i) :
    X.tupleLawOn H S T = X.tupleLawOn H' S T := by
  apply finProb_ext_weight6
  funext o
  rw [tupleLawOn_weight6, tupleLawOn_weight6]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  rw [hLabel]

theorem lowRef_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (b : X.State) (β : X.Ty)
    (hbase : H.1 = H'.1) (hother : ∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) :
    Ctx6.lowRef X H b β = Ctx6.lowRef X H' b β := by
  let drop : X.Name := .hid (X.tgt b)
  have htag : X.TβDel H β (X.tgt b) = X.TβDel H' β (X.tgt b) := by
    change X.tagPost H β (β.obs.erase (X.tgt b)) =
      X.tagPost H' β (β.obs.erase (X.tgt b))
    apply tagPost_eq_of_hidden_agree6 X H H' β (β.obs.erase (X.tgt b)) hbase
    intro h hh
    exact hother h (Finset.mem_erase.mp hh).1
  have hnames : ∀ nm, nm ∈ (reqNames6 β).erase drop →
      X.varVal H nm = X.varVal H' nm := by
    intro nm hnm
    cases nm with
    | par p => simp [Ctx6.varVal, hbase]
    | hid h =>
        have hne : h ≠ X.tgt b := by
          intro heq
          apply (Finset.mem_erase.mp hnm).1
          subst h
          rfl
        simpa [Ctx6.varVal] using hother h hne
  have hlabels : ∀ i, X.labelLaw H ((reqNames6 β).erase drop) i =
      X.labelLaw H' ((reqNames6 β).erase drop) i := by
    intro i
    exact labelLaw_eq_of_varVal_agree6 X H H' ((reqNames6 β).erase drop) i hnames
  unfold Ctx6.lowRef Ctx6.tupleRef
  rw [htag]
  exact tupleLawOn_eq_of_labelLaw_eq6 X H H' ((reqNames6 β).erase drop)
    (X.TβDel H' β (X.tgt b)) hlabels

theorem lowGate_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H H' : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (hbase : H.1 = H'.1) (hother : ∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) :
    Ctx6.LowGate X H b D ξ = Ctx6.LowGate X H' b D ξ := by
  have hwith := withHid_eq_of_hidden_agree6 X H H' (X.tgt b) ξ hbase hother
  simp [Ctx6.LowGate, hbase, hwith]

theorem lowLik_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H H' : X.Hist) (b : X.State)
    (β : X.Ty) (ξ : Fin N) (o : X.Tuple)
    (hbase : H.1 = H'.1) (hother : ∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) :
    Ctx6.lowLik X H b ξ β o = Ctx6.lowLik X H' b ξ β o := by
  have hwith := withHid_eq_of_hidden_agree6 X H H' (X.tgt b) ξ hbase hother
  have htag : X.TβDel H β (X.tgt b) = X.TβDel H' β (X.tgt b) := by
    change X.tagPost H β (β.obs.erase (X.tgt b)) =
      X.tagPost H' β (β.obs.erase (X.tgt b))
    apply tagPost_eq_of_hidden_agree6 X H H' β (β.obs.erase (X.tgt b)) hbase
    intro h hh
    exact hother h (Finset.mem_erase.mp hh).1
  have hnames : ∀ nm, nm ∈ (reqNames6 β).erase (.hid (X.tgt b)) →
      X.varVal H nm = X.varVal H' nm := by
    intro nm hnm
    cases nm with
    | par p => simp [Ctx6.varVal, hbase]
    | hid h =>
        have hne : h ≠ X.tgt b := by
          intro heq
          apply (Finset.mem_erase.mp hnm).1
          subst h
          rfl
        simpa [Ctx6.varVal] using hother h hne
  have hlabels : ∀ i, X.labelLaw H ((reqNames6 β).erase (.hid (X.tgt b))) i =
      X.labelLaw H' ((reqNames6 β).erase (.hid (X.tgt b))) i := by
    intro i
    exact labelLaw_eq_of_varVal_agree6 X H H' _ i hnames
  unfold Ctx6.lowLik Ctx6.tupleRatio
  rw [hwith, htag, hlabels]

theorem lowWeight_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H H' : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (hbase : H.1 = H'.1) (hother : ∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) :
    Ctx6.lowWeight X H b D o drop ξ = Ctx6.lowWeight X H' b D o drop ξ := by
  have hgate := lowGate_eq_of_hidden_agree6 X H H' b D ξ hbase hother
  have hfactor : (X.hidPost H.1 (X.tgt b).1).w ξ *
        (if X.LowGate H b D ξ then 1 else 0) =
      (X.hidPost H'.1 (X.tgt b).1).w ξ *
        (if X.LowGate H' b D ξ then 1 else 0) := by
    rw [hbase, hgate]
  have hprod :
      (∏ e ∈ D, if drop = some e then 1 else X.lowLik H b ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.lowLik H' b ξ e.2 (o e) := by
    apply Finset.prod_congr rfl
    intro e he
    by_cases hdrop : drop = some e
    · simp [hdrop]
    · simp [hdrop, lowLik_eq_of_hidden_agree6 X H H' b e.2 ξ (o e) hbase hother]
  unfold Ctx6.lowWeight
  rw [hfactor, hprod]

theorem s3Mass_low_eq_of_hidden_agree6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H H' : X.Hist) (b : X.State) (D : Finset (Id × X.Ty)) (o : X.Data Id)
    (drop : Option (Id × X.Ty)) (hmode : X.stMode b = .low)
    (hbase : H.1 = H'.1) (hother : ∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) :
    X.s3Mass H b D o drop = X.s3Mass H' b D o drop := by
  unfold Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ hξ
  simpa [Ctx6.s3Weight, hmode] using
    lowWeight_eq_of_hidden_agree6 X H H' b D o drop ξ hbase hother

private theorem pi_weight_split_qs6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
        (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 := by
        exact Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) *
          (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]
    _ = (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
          (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by rfl

theorem pi_expect_split6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split_qs6 P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

theorem pi_expect_prod6 {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  calc
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
        ∑ ω : (∀ i, Ω i), ∏ i, ((P i).w (ω i) * f i (ω i)) := by
      unfold FinProb.expect FinProb.pi
      apply Finset.sum_congr rfl
      intro ω hω
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ x, (P i).w x * f i x :=
      (Fintype.prod_sum fun i x => (P i).w x * f i x).symm
    _ = ∏ i, (P i).expect (f i) := by simp [FinProb.expect]

theorem pr_eq_expect_indicator6 {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω => if A ω then 1 else 0) := by
  classical
  simp [FinProb.pr, FinProb.expect, mul_ite]

theorem dataLaw_pr_depends6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (D : Finset (Id × X.Ty)) (A : X.Data Id → Prop)
    (hA : ∀ o o', (∀ e ∈ D, o e = o' e) → (A o ↔ A o'))
    (o₀ : X.Data Id) :
    (X.dataLaw Id H).pr A =
      (FinProb.pi (fun e : {e : Id × X.Ty // e ∈ D} => X.tupleLaw H e.1.2)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun e : Id × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => o₀ e.1))) := by
  classical
  let P : ∀ e : Id × X.Ty, FinProb X.Tuple := fun e => X.tupleLaw H e.2
  let f : X.Data Id → ℝ := fun o => if A o then 1 else 0
  have hf : FinProb.DependsOn f D := by
    intro o o' hagree
    have hiff := hA o o' hagree
    by_cases ho : A o
    · have ho' : A o' := hiff.mp ho
      simp [f, ho, ho']
    · have ho' : ¬ A o' := fun h' => ho (hiff.mpr h')
      simp [f, ho, ho']
  calc
    (X.dataLaw Id H).pr A = (X.dataLaw Id H).expect f :=
      (pr_eq_expect_indicator6 (X.dataLaw Id H) A)
    _ = (FinProb.pi P).expect f := by rfl
    _ = (FinProb.pi (fun e : {e : Id × X.Ty // e ∈ D} => P e.1)).expect
        (fun a => f ((Equiv.piEquivPiSubtypeProd (fun e : Id × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => o₀ e.1))) :=
        FinProb.pi_expect_depends P D f o₀ hf
    _ = (FinProb.pi (fun e : {e : Id × X.Ty // e ∈ D} => X.tupleLaw H e.1.2)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun e : Id × X.Ty => e ∈ D)
          (fun _ => X.Tuple)).symm (a, fun e => o₀ e.1))) := by
      simp [FinProb.pr, FinProb.expect, f, P]

theorem bind_pr6 {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1 ab.2) =
      ∑ a, P.w a * (K a).pr (A a) := by
  classical
  change (∑ ab : α × β, if A ab.1 ab.2 then P.w ab.1 * (K ab.1).w ab.2 else 0) =
    ∑ a, P.w a * ∑ b, if A a b then (K a).w b else 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, if A a b then P.w a * (K a).w b else 0) =
        ∑ b, P.w a * (if A a b then (K a).w b else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : A a b <;> simp [h]
    _ = P.w a * ∑ b, if A a b then (K a).w b else 0 := by rw [Finset.mul_sum]

theorem rawHistData_pr_expand6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (A : X.Hist → X.Data Id → Prop) :
    (X.rawHistData Id).pr (fun z => A z.1 z.2) =
      ∑ b : X.Base, X.baseLaw.w b *
        (X.hidLaw b).expect (fun z => (X.dataLaw Id (b, z)).pr (A (b, z))) := by
  classical
  rw [Ctx6.rawHistData, bind_pr6]
  rw [Ctx6.rawHist]
  change (∑ H : X.Base × X.Hid,
      (X.baseLaw.w H.1 * (X.hidLaw H.1).w H.2) *
        (X.dataLaw Id H).pr (A H)) = _
  rw [Fintype.sum_prod_type]
  unfold FinProb.expect
  calc
    (∑ b, ∑ z, (X.baseLaw.w b * (X.hidLaw b).w z) *
        (X.dataLaw Id (b, z)).pr (A (b, z))) =
      ∑ b, X.baseLaw.w b * ∑ z, (X.hidLaw b).w z *
        (X.dataLaw Id (b, z)).pr (A (b, z)) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          ring
    _ = ∑ b, X.baseLaw.w b *
        (X.hidLaw b).expect (fun z => (X.dataLaw Id (b, z)).pr (A (b, z))) := rfl

end Lane_q_s06_steps2
end S06
end HypercubeRamsey
