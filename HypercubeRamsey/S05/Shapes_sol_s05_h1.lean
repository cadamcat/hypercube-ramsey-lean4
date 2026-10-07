import HypercubeRamsey.S05.History_sol_s05_h1

namespace HypercubeRamsey.Lane_sol_s05_h1

open Classical
open scoped BigOperators

set_option synthInstance.maxSize 1024

noncomputable section

abbrev KeyCode := Bool × Fin 3 × CoarseCode

def slotLevel {J : ℕ} (j : Option (Fin (J + 1))) (s : Fin 3) : ℕ :=
  match j with
  | none => J
  | some j => if s.val = 0 then j.val else if s.val = 1 then j.val + 1 else j.val - 1

def slotOf {J : ℕ} (j : Option (Fin (J + 1))) (level : ℕ) : Fin 3 :=
  match j with
  | none => ⟨0, by decide⟩
  | some j => if level = j.val then ⟨0, by decide⟩
      else if level = j.val + 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩

def decodeKey {J : ℕ} (j : Option (Fin (J + 1))) (c : KeyCode) : ℕ :=
  if c.1 then slotLevel j c.2.1 else J

def LevelCompatible {n m J : ℕ} (j : Option (Fin (J + 1))) (ℓ : HiddenKey5 n m J) : Prop :=
  match ℓ with
  | .inr _ => True
  | .inl k => match j with
    | none => k.2.2.val = J
    | some j => k.2.2.val ∈ ({j.val, j.val + 1, j.val - 1} : Finset ℕ)

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

def keyCode (b : BinNaming n) (j : Option (Fin (X.p.J n + 1)))
    (ℓ : X.Key) (hℓ : binList5 ℓ.coarse ⊆ b.bins) : KeyCode :=
  (ℓ.isLeft, slotOf j ℓ.level, coarseCode b ℓ.coarse hℓ)

theorem decode_keyCode (b : BinNaming n) (j : Option (Fin (X.p.J n + 1)))
    (ℓ : X.Key) (hℓ : binList5 ℓ.coarse ⊆ b.bins) (hc : LevelCompatible j ℓ) :
    decodeKey j (keyCode X b j ℓ hℓ) = ℓ.level := by
  cases ℓ with
  | inr i => simp [decodeKey, keyCode, HiddenKey5.level]
  | inl k =>
    cases j with
    | none => simpa [decodeKey, keyCode, slotOf, slotLevel, HiddenKey5.level] using hc.symm
    | some j =>
      change k.2.2.val ∈ ({j.val, j.val + 1, j.val - 1} : Finset ℕ) at hc
      by_cases h0 : k.2.2.val = j.val
      · simp [decodeKey, keyCode, slotOf, slotLevel, HiddenKey5.level, h0]
      · by_cases h1 : k.2.2.val = j.val + 1
        · simp [decodeKey, keyCode, slotOf, slotLevel, HiddenKey5.level, h0, h1]
        · have h2 : k.2.2.val = j.val - 1 := by simpa [h0, h1] using hc
          simpa [decodeKey, keyCode, slotOf, slotLevel, HiddenKey5.level, h0, h1] using h2.symm

theorem keyCode_match (b b' : BinNaming n)
    (r : BinRename b.bins b'.bins b.labels b'.labels)
    (j : Option (Fin (X.p.J n + 1))) (ℓ ℓ' : X.Key)
    (hℓ : binList5 ℓ.coarse ⊆ b.bins) (hℓ' : binList5 ℓ'.coarse ⊆ b'.bins)
    (hc : keyCode X b j ℓ hℓ = keyCode X b' j ℓ' hℓ')
    (hcompat : LevelCompatible j ℓ) (hcompat' : LevelCompatible j ℓ') :
    PriorMatch X r.perm ℓ ℓ' ∧ colLen5 (X.p.s n) ℓ = colLen5 (X.p.s n) ℓ' := by
  have hl := congrArg (decodeKey j) hc
  rw [decode_keyCode X b j ℓ hℓ hcompat, decode_keyCode X b' j ℓ' hℓ' hcompat'] at hl
  have hcoarse : coarseCode b ℓ.coarse hℓ = coarseCode b' ℓ'.coarse hℓ' :=
    congrArg (fun c : KeyCode => c.2.2) hc
  have hkind : ℓ.isLeft = ℓ'.isLeft := congrArg Prod.fst hc
  exact ⟨priorMatch_of_code X b b' r ℓ ℓ' hℓ hℓ' hcoarse hl, colLen_of_kind X ℓ ℓ' hkind⟩

def histogram {A D : Type*} [Fintype A] (f : A → D) (M : ℕ)
    (hA : Fintype.card A ≤ M) : D → Fin (M + 1) :=
  fun d => ⟨Fintype.card {a // f a = d}, Nat.lt_succ_of_le
    ((Fintype.card_le_of_injective (fun a : {a // f a = d} => a.1) Subtype.val_injective).trans hA)⟩

theorem histogram_equiv {A B D : Type*} [Fintype A] [Fintype B]
    (f : A → D) (g : B → D) (M : ℕ) (hA : Fintype.card A ≤ M) (hB : Fintype.card B ≤ M)
    (h : histogram f M hA = histogram g M hB) : ∃ e : A ≃ B, ∀ a, g (e a) = f a := by
  apply equiv_of_histogram f g
  intro d
  exact congrArg Fin.val (congrFun h d)

theorem low_type_compatible (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (ℓ : X.Key) (hℓ : ℓ ∈ X.g.typeKeys (X.p.J n) x) :
    LevelCompatible (some ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩) ℓ := by
  cases ℓ with
  | inr i => trivial
  | inl k => exact typeKeys_low_levels X.g (X.p.J n) x hx k hℓ

theorem high_type_compatible (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (ℓ : X.Key) (hℓ : ℓ ∈ X.g.typeKeys (X.p.J n) x) :
    LevelCompatible none ℓ := by
  classical
  unfold ChunkGeometry5.typeKeys at hℓ
  rw [ite_eq_right hx] at hℓ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
  trivial

def coarseKeyBound : ℕ := coarseChunkCount5 * 4 + 1

theorem high_type_card_le (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) :
    (X.g.typeKeys (X.p.J n) x).card ≤ coarseKeyBound := by
  classical
  unfold ChunkGeometry5.typeKeys
  rw [ite_eq_right hx]
  exact Finset.card_image_le.trans (X.g.coarseRange_card_le x)

abbrev LowShape (m J : ℕ) := Fin (J + 1) × Finset (Fin shapeBinBound) ×
  CoarseCode × (KeyCode → Fin (coarseKeyBound + m + 3))

abbrev HighShape := Finset (Fin shapeBinBound) × CoarseCode ×
  (KeyCode → Fin (coarseKeyBound + 1))

def fixedShapeCount : ℕ := Fintype.card (Finset (Fin shapeBinBound)) * Fintype.card CoarseCode

theorem lowShape_card (m J : ℕ) :
    Fintype.card (LowShape m J) =
      (J + 1) * fixedShapeCount * (coarseKeyBound + m + 3) ^ Fintype.card KeyCode := by
  simp only [LowShape, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    fixedShapeCount, Nat.mul_assoc]

theorem highShape_card :
    Fintype.card HighShape = fixedShapeCount * (coarseKeyBound + 1) ^ Fintype.card KeyCode := by
  simp only [HighShape, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    fixedShapeCount, Nat.mul_assoc]

def lowShape (x : OAI.HypercubeRamsey.CubeVertex n) (hx : X.g.severity x ≤ X.p.J n) :
    LowShape (X.p.m n) (X.p.J n) :=
  let b := localNaming X.g x
  let j : Fin (X.p.J n + 1) := ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩
  (j, Finset.univ.image b.labels, coarseCode b (X.g.key x) (central_bins_subset X.g x),
    histogram (fun ℓ : X.g.typeKeys (X.p.J n) x => keyCode X b (some j) ℓ.1
      (typeKey_bins_subset X.g (X.p.J n) x ℓ.1 ℓ.2)) (coarseKeyBound + X.p.m n + 2)
        (by simpa only [Fintype.card_coe, coarseKeyBound] using typeKeys_card_le X.g (X.p.J n) x))

def highShape (x : OAI.HypercubeRamsey.CubeVertex n) (hx : ¬ X.g.severity x ≤ X.p.J n) : HighShape :=
  let b := localNaming X.g x
  (Finset.univ.image b.labels, coarseCode b (X.g.key x) (central_bins_subset X.g x),
    histogram (fun ℓ : X.g.typeKeys (X.p.J n) x => keyCode X b none ℓ.1
      (typeKey_bins_subset X.g (X.p.J n) x ℓ.1 ℓ.2)) coarseKeyBound
        (by simpa only [Fintype.card_coe] using high_type_card_le X x hx))

theorem lowShape_key_equiv (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (hx' : X.g.severity x' ≤ X.p.J n)
    (h : lowShape X x hx = lowShape X x' hx') :
    ∃ r : BinRename (localNaming X.g x).bins (localNaming X.g x').bins
        (localNaming X.g x).labels (localNaming X.g x').labels,
      ∃ es : X.g.typeKeys (X.p.J n) x ≃ X.g.typeKeys (X.p.J n) x',
        r.perm (X.g.key x).1 = (X.g.key x').1 ∧
        (∀ ℓ, PriorMatch X r.perm ℓ.1 (es ℓ).1) ∧
        (∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1) := by
  classical
  let b := localNaming X.g x
  let b' := localNaming X.g x'
  let j : Fin (X.p.J n + 1) := ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩
  let j' : Fin (X.p.J n + 1) := ⟨X.g.severity x', Nat.lt_succ_of_le hx'⟩
  let f (ℓ : X.g.typeKeys (X.p.J n) x) : KeyCode :=
    keyCode X b (some j) ℓ.1 (typeKey_bins_subset X.g (X.p.J n) x ℓ.1 ℓ.2)
  let f' (ℓ : X.g.typeKeys (X.p.J n) x') : KeyCode :=
    keyCode X b' (some j') ℓ.1 (typeKey_bins_subset X.g (X.p.J n) x' ℓ.1 ℓ.2)
  have hj : j = j' := congrArg Prod.fst h
  have hb : Finset.univ.image b.labels = Finset.univ.image b'.labels :=
    congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.2.1) h
  have hc : coarseCode b (X.g.key x) (central_bins_subset X.g x) =
      coarseCode b' (X.g.key x') (central_bins_subset X.g x') :=
    congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.2.2.1) h
  obtain ⟨r⟩ := binRename_exists b.bins b'.bins b.labels b'.labels hb
  have hhist := congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.2.2.2) h
  obtain ⟨es, hes⟩ := histogram_equiv f f' (coarseKeyBound + X.p.m n + 2)
    (by simpa only [Fintype.card_coe, coarseKeyBound] using typeKeys_card_le X.g (X.p.J n) x)
    (by simpa only [Fintype.card_coe, coarseKeyBound] using typeKeys_card_le X.g (X.p.J n) x') hhist
  have hm (ℓ : X.g.typeKeys (X.p.J n) x) : PriorMatch X r.perm ℓ.1 (es ℓ).1 ∧
      colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1 := by
    have he : keyCode X b (some j) ℓ.1 (typeKey_bins_subset X.g (X.p.J n) x ℓ.1 ℓ.2) =
        keyCode X b' (some j) (es ℓ).1
          (typeKey_bins_subset X.g (X.p.J n) x' (es ℓ).1 (es ℓ).2) := by
      simpa only [f, f', ← hj] using (hes ℓ).symm
    apply keyCode_match X b b' r (some j) ℓ.1 (es ℓ).1 _ _ he
    · exact low_type_compatible X x hx ℓ.1 ℓ.2
    · simpa only [hj] using low_type_compatible X x' hx' (es ℓ).1 (es ℓ).2
  refine ⟨r, es, (coarseCode_match b b' r (X.g.key x) (X.g.key x') _ _ hc).2.1,
    (fun ℓ => (hm ℓ).1), (fun ℓ => (hm ℓ).2)⟩

theorem lowShape_step2Rate (v : Fin N) (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (hx' : X.g.severity x' ≤ X.p.J n)
    (h : lowShape X x hx = lowShape X x' hx') :
    (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x')) =
      (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x)) := by
  classical
  obtain ⟨r, es, hi, hs, hl⟩ := lowShape_key_equiv X x x' hx hx' h
  let i := X.g.key x
  let i' := X.g.key x'
  let S := X.g.typeKeys (X.p.J n) x
  let S' := X.g.typeKeys (X.p.J n) x'
  let j : Fin (X.p.J n + 1) := ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩
  let j' : Fin (X.p.J n + 1) := ⟨X.g.severity x', Nat.lt_succ_of_le hx'⟩
  have hj : j = j' := congrArg Prod.fst h
  have hk : X.g.evenType (X.p.J n) x = (i, S, some j) := by
    simp only [ChunkGeometry5.evenType, dite_eq_left hx]
    rfl
  have hk' : X.g.evenType (X.p.J n) x' = (i', S', some j) := by
    change X.g.evenType (X.p.J n) x' = (i', S', some j)
    rw [hj]
    simp only [ChunkGeometry5.evenType, dite_eq_left hx']
    rfl
  have hg : X.gateKeys (i, S, some j) = S := by simp [Setup5.gateKeys]
  have hg' : X.gateKeys (i', S', some j) = S' := by simp [Setup5.gateKeys]
  let g := Finset.equivOfEq hg
  let g' := Finset.equivOfEq hg'
  let eg := g.trans (es.trans g'.symm)
  have hmatch : ∀ ℓ, PriorMatch X r.perm ℓ.1 (eg ℓ).1 := by
    intro ℓ
    simpa only [eg, Equiv.trans_apply, g, g', Finset.equivOfEq_apply_coe,
      Finset.equivOfEq_symm_apply_coe] using hs (g ℓ)
  rw [hk, hk']
  exact step2Rate_bin_equiv X v r.perm i i' S S' (some j) hi eg hmatch es hs hl

theorem highShape_key_equiv (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (hx' : ¬ X.g.severity x' ≤ X.p.J n)
    (h : highShape X x hx = highShape X x' hx') :
    ∃ r : BinRename (localNaming X.g x).bins (localNaming X.g x').bins
        (localNaming X.g x).labels (localNaming X.g x').labels,
      ∃ es : X.g.typeKeys (X.p.J n) x ≃ X.g.typeKeys (X.p.J n) x',
        r.perm (X.g.key x).1 = (X.g.key x').1 ∧
        (∀ ℓ, PriorMatch X r.perm ℓ.1 (es ℓ).1) ∧
        (∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1) := by
  classical
  let b := localNaming X.g x
  let b' := localNaming X.g x'
  let f (ℓ : X.g.typeKeys (X.p.J n) x) : KeyCode :=
    keyCode X b none ℓ.1 (typeKey_bins_subset X.g (X.p.J n) x ℓ.1 ℓ.2)
  let f' (ℓ : X.g.typeKeys (X.p.J n) x') : KeyCode :=
    keyCode X b' none ℓ.1 (typeKey_bins_subset X.g (X.p.J n) x' ℓ.1 ℓ.2)
  have hb : Finset.univ.image b.labels = Finset.univ.image b'.labels := congrArg Prod.fst h
  have hc : coarseCode b (X.g.key x) (central_bins_subset X.g x) =
      coarseCode b' (X.g.key x') (central_bins_subset X.g x') :=
    congrArg (fun c : HighShape => c.2.1) h
  obtain ⟨r⟩ := binRename_exists b.bins b'.bins b.labels b'.labels hb
  have hhist := congrArg (fun c : HighShape => c.2.2) h
  obtain ⟨es, hes⟩ := histogram_equiv f f' coarseKeyBound
    (by simpa only [Fintype.card_coe] using high_type_card_le X x hx)
    (by simpa only [Fintype.card_coe] using high_type_card_le X x' hx') hhist
  have hm (ℓ : X.g.typeKeys (X.p.J n) x) : PriorMatch X r.perm ℓ.1 (es ℓ).1 ∧
      colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1 := by
    exact keyCode_match X b b' r none ℓ.1 (es ℓ).1 _ _ (hes ℓ).symm
      (high_type_compatible X x hx ℓ.1 ℓ.2) (high_type_compatible X x' hx' (es ℓ).1 (es ℓ).2)
  exact ⟨r, es, (coarseCode_match b b' r (X.g.key x) (X.g.key x') _ _ hc).2.1,
    (fun ℓ => (hm ℓ).1), (fun ℓ => (hm ℓ).2)⟩

def insertMap {A : Type*} [DecidableEq A] (S S' : Finset A) (es : S ≃ S') (a a' : A)
    (k : ↥(insert a S : Finset A)) : ↥(insert a' S' : Finset A) :=
  if h : k.1 = a then ⟨a', Finset.mem_insert_self _ _⟩
  else let ks : S := ⟨k.1, (Finset.mem_insert.mp k.2).resolve_left h⟩
    ⟨(es ks).1, Finset.mem_insert_of_mem (es ks).2⟩

def insertEquiv {A : Type*} [DecidableEq A] (S S' : Finset A) (es : S ≃ S')
    (a a' : A) (ha : a ∉ S) (ha' : a' ∉ S') :
    ↥(insert a S : Finset A) ≃ ↥(insert a' S' : Finset A) where
  toFun := insertMap S S' es a a'
  invFun := insertMap S' S es.symm a' a
  left_inv k := by
    apply Subtype.ext
    by_cases hk : k.1 = a
    · simp [insertMap, hk]
    · let ks : S := ⟨k.1, (Finset.mem_insert.mp k.2).resolve_left hk⟩
      have hn : (es ks).1 ≠ a' := fun he => ha' (he ▸ (es ks).2)
      simp [insertMap, hk, ks, hn]
  right_inv k := by
    apply Subtype.ext
    by_cases hk : k.1 = a'
    · simp [insertMap, hk]
    · let ks : S' := ⟨k.1, (Finset.mem_insert.mp k.2).resolve_left hk⟩
      have hn : (es.symm ks).1 ≠ a := fun he => ha (he ▸ (es.symm ks).2)
      simp [insertMap, hk, ks, hn]

theorem insert_matches (e : Equiv.Perm (BinVector5 n)) (S S' : Finset X.Key) (es : S ≃ S')
    (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1 ∧
      colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1)
    (a a' : X.Key) (ha : a ∉ S) (ha' : a' ∉ S')
    (hm : PriorMatch X e a a' ∧ colLen5 (X.p.s n) a = colLen5 (X.p.s n) a') :
    ∃ ea : ↥(insert a S : Finset X.Key) ≃ ↥(insert a' S' : Finset X.Key),
      (∀ ℓ, PriorMatch X e ℓ.1 (ea ℓ).1) ∧
      (∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (ea ℓ).1) ∧
      (∀ ℓ : S, (ea ⟨ℓ.1, Finset.mem_insert_of_mem ℓ.2⟩).1 = (es ℓ).1) := by
  classical
  let ea := insertEquiv S S' es a a' ha ha'
  have hmatch (ℓ : ↥(insert a S : Finset X.Key)) : PriorMatch X e ℓ.1 (ea ℓ).1 ∧
      colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (ea ℓ).1 := by
    by_cases hℓ : ℓ.1 = a
    · have hout : (ea ℓ).1 = a' := by simp [ea, insertEquiv, insertMap, hℓ]
      simpa only [hℓ, hout] using hm
    · let k : S := ⟨ℓ.1, (Finset.mem_insert.mp ℓ.2).resolve_left hℓ⟩
      have hout : (ea ℓ).1 = (es k).1 := by simp [ea, insertEquiv, insertMap, hℓ, k]
      simpa only [hout] using hs k
  refine ⟨ea, (fun ℓ => (hmatch ℓ).1), (fun ℓ => (hmatch ℓ).2), ?_⟩
  intro ℓ
  have hn : ℓ.1 ≠ a := fun he => ha (he ▸ ℓ.2)
  simp [ea, insertEquiv, insertMap, hn]

theorem highShape_full_equiv (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (hx' : ¬ X.g.severity x' ≤ X.p.J n)
    (h : highShape X x hx = highShape X x' hx') :
    ∃ r : BinRename (localNaming X.g x).bins (localNaming X.g x').bins
        (localNaming X.g x).labels (localNaming X.g x').labels,
      ∃ es : X.g.typeKeys (X.p.J n) x ≃ X.g.typeKeys (X.p.J n) x',
        ∃ eg : X.gateKeys (X.g.key x, X.g.typeKeys (X.p.J n) x, none) ≃
            X.gateKeys (X.g.key x', X.g.typeKeys (X.p.J n) x', none),
          r.perm (X.g.key x).1 = (X.g.key x').1 ∧
          (∀ ℓ, PriorMatch X r.perm ℓ.1 (es ℓ).1) ∧
          (∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1) ∧
          (∀ ℓ, PriorMatch X r.perm ℓ.1 (eg ℓ).1) ∧
          (∀ t t', PriorMatch X r.perm
            (X.optKeyOf (X.g.evenType (X.p.J n) x) t)
            (X.optKeyOf (X.g.evenType (X.p.J n) x') t')) := by
  classical
  obtain ⟨r, es, hi, hs, hl⟩ := highShape_key_equiv X x x' hx hx' h
  let b := localNaming X.g x
  let b' := localNaming X.g x'
  have hc : coarseCode b (X.g.key x) (central_bins_subset X.g x) =
      coarseCode b' (X.g.key x') (central_bins_subset X.g x') :=
    congrArg (fun c : HighShape => c.2.1) h
  obtain ⟨hf, hb, hbins⟩ := coarseCode_match b b' r (X.g.key x) (X.g.key x') _ _ hc
  have ho : ∀ t t', PriorMatch X r.perm
      (X.optKeyOf (X.g.evenType (X.p.J n) x) t)
      (X.optKeyOf (X.g.evenType (X.p.J n) x') t') := by
    intro t t'
    exact ⟨rfl, hf, hb, hbins⟩
  let a := X.optKeyOf (X.g.evenType (X.p.J n) x) (fun _ => false)
  let a' := X.optKeyOf (X.g.evenType (X.p.J n) x') (fun _ => false)
  let S := X.g.typeKeys (X.p.J n) x
  let S' := X.g.typeKeys (X.p.J n) x'
  have ha : a ∉ S := by
    simp [a, S, Setup5.optKeyOf, ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, hx]
  have ha' : a' ∉ S' := by
    simp [a', S', Setup5.optKeyOf, ChunkGeometry5.evenType, ChunkGeometry5.typeKeys, hx']
  obtain ⟨ea, hea, hla, hlink⟩ := insert_matches X r.perm S S' es (fun ℓ => ⟨hs ℓ, hl ℓ⟩)
    a a' ha ha' ⟨ho _ _, rfl⟩
  have hg : X.gateKeys (X.g.key x, X.g.typeKeys (X.p.J n) x, none) = insert a S := by
    simp [Setup5.gateKeys, ChunkGeometry5.evenType, hx, a, S, Setup5.optKeyOf]
  have hg' : X.gateKeys (X.g.key x', X.g.typeKeys (X.p.J n) x', none) = insert a' S' := by
    simp [Setup5.gateKeys, ChunkGeometry5.evenType, hx', a', S', Setup5.optKeyOf]
  let g := Finset.equivOfEq hg
  let g' := Finset.equivOfEq hg'
  let eg := g.trans (ea.trans g'.symm)
  have hge : ∀ ℓ, PriorMatch X r.perm ℓ.1 (eg ℓ).1 := by
    intro ℓ
    simpa only [eg, Equiv.trans_apply, g, g', Finset.equivOfEq_apply_coe,
      Finset.equivOfEq_symm_apply_coe] using hea (g ℓ)
  exact ⟨r, es, eg, hi, hs, hl, hge, ho⟩

theorem highShape_step2Rate (v : Fin N) (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (hx' : ¬ X.g.severity x' ≤ X.p.J n)
    (h : highShape X x hx = highShape X x' hx') :
    (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x')) =
      (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x)) := by
  obtain ⟨r, es, eg, hi, hs, hl, hg, ho⟩ := highShape_full_equiv X x x' hx hx' h
  have hk : X.g.evenType (X.p.J n) x = (X.g.key x, X.g.typeKeys (X.p.J n) x, none) := by
    simp [ChunkGeometry5.evenType, hx]
  have hk' : X.g.evenType (X.p.J n) x' = (X.g.key x', X.g.typeKeys (X.p.J n) x', none) := by
    simp [ChunkGeometry5.evenType, hx']
  rw [hk, hk']
  exact step2Rate_bin_equiv X v r.perm _ _ _ _ none hi eg hg es hs hl

theorem optFail_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (U U' : X.Hidden) (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, none) ≃ X.gateKeys (i', S', none))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hls : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1)
    (hcs : ∀ ℓ : S, colEquiv X ℓ.1 (es ℓ).1 (hls ℓ) (U ℓ.1) = U' (es ℓ).1)
    (t t' : OAI.HypercubeRamsey.CubeVertex (X.p.m n))
    (ea : ↥(insert (X.optKeyOf (i, S, none) t) S : Finset X.Key) ≃
      ↥(insert (X.optKeyOf (i', S', none) t') S' : Finset X.Key))
    (ha : ∀ ℓ, PriorMatch X e ℓ.1 (ea ℓ).1)
    (hla : ∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (ea ℓ).1)
    (hca : ∀ ℓ, colEquiv X ℓ.1 (ea ℓ).1 (hla ℓ) (U ℓ.1) = U' (ea ℓ).1) :
    X.optFail ((b.1, renameCoarse X e b.2), U') (i', S', none) t' ↔
      X.optFail (b, U) (i, S, none) t := by
  have hm := blockMass_bin_equiv X e b U U' i i' S S' S S' none hi eg hg es hs hls hcs
  have ha := blockMass_bin_equiv X e b U U' i i' S S'
    (insert (X.optKeyOf (i, S, none) t) S) (insert (X.optKeyOf (i', S', none) t') S')
    none hi eg hg ea ha hla hca
  unfold Setup5.optFail
  dsimp only [Prod.fst, Prod.snd]
  rw [trueBlock_bin_equiv X e b i i' S S' none hi,
    blockGate_bin_equiv X e b i i' S S' none hi eg hg, hm, ha]

theorem optConditional_bin_equiv (e : Equiv.Perm (BinVector5 n)) (b : X.Base)
    (i i' : CoarseKey5 n) (S S' : Finset X.Key) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, none) ≃ X.gateKeys (i', S', none))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hls : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1)
    (t t' : OAI.HypercubeRamsey.CubeVertex (X.p.m n))
    (ea : ↥(insert (X.optKeyOf (i, S, none) t) S : Finset X.Key) ≃
      ↥(insert (X.optKeyOf (i', S', none) t') S' : Finset X.Key))
    (ha : ∀ ℓ, PriorMatch X e ℓ.1 (ea ℓ).1)
    (hla : ∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (ea ℓ).1)
    (hlink : ∀ ℓ : S, (ea ⟨ℓ.1, Finset.mem_insert_of_mem ℓ.2⟩).1 = (es ℓ).1) :
    (X.hiddenLaw (b.1, renameCoarse X e b.2)).pr
        (fun U => X.optFail ((b.1, renameCoarse X e b.2), U) (i', S', none) t') =
      (X.hiddenLaw b).pr (fun U => X.optFail (b, U) (i, S, none) t) := by
  classical
  symm
  apply pi_pr_local_equiv
    (fun ℓ => FinProb.pi fun _ => X.prior b ℓ)
    (fun ℓ => FinProb.pi fun _ => X.prior (b.1, renameCoarse X e b.2) ℓ)
    (insert (X.optKeyOf (i, S, none) t) S) (insert (X.optKeyOf (i', S', none) t') S')
    (fun _ _ => X.y₀) (fun _ _ => X.y₀) ea
    (fun ℓ => colEquiv X ℓ.1 (ea ℓ).1 (hla ℓ))
    (fun ℓ θ => colLaw_weight_equiv X e b ℓ.1 (ea ℓ).1 (ha ℓ) (hla ℓ) θ)
    _ _ (optFail_depends X b (i, S, none) t)
    (optFail_depends X (b.1, renameCoarse X e b.2) (i', S', none) t')
  intro U U' hca
  have hcs : ∀ ℓ : S, colEquiv X ℓ.1 (es ℓ).1 (hls ℓ) (U ℓ.1) = U' (es ℓ).1 := by
    intro ℓ
    have hc := hca ⟨ℓ.1, Finset.mem_insert_of_mem ℓ.2⟩
    simpa only [hlink ℓ] using hc
  exact (optFail_bin_equiv X e b U U' i i' S S' hi eg hg es hs hls hcs t t' ea ha hla hca).symm

theorem optRate_bin_equiv (v : Fin N) (e : Equiv.Perm (BinVector5 n))
    (i i' : CoarseKey5 n) (S S' : Finset X.Key) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, none) ≃ X.gateKeys (i', S', none))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hls : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1)
    (t t' : OAI.HypercubeRamsey.CubeVertex (X.p.m n))
    (ea : ↥(insert (X.optKeyOf (i, S, none) t) S : Finset X.Key) ≃
      ↥(insert (X.optKeyOf (i', S', none) t') S' : Finset X.Key))
    (ha : ∀ ℓ, PriorMatch X e ℓ.1 (ea ℓ).1)
    (hla : ∀ ℓ, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (ea ℓ).1)
    (hlink : ∀ ℓ : S, (ea ⟨ℓ.1, Finset.mem_insert_of_mem ℓ.2⟩).1 = (es ℓ).1) :
    (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) (i', S', none) t') =
      (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) (i, S, none) t) := by
  classical
  simp only [Setup5.keyLawAt, bind_pr]
  rw [expect_equiv (X.coarseLaw v) (X.coarseLaw v) (coarseEquiv X e)
    (coarseLaw_weight_equiv X v e)]
  congr 1
  funext c
  exact optConditional_bin_equiv X e (v, c) i i' S S' hi eg hg es hs hls t t' ea ha hla hlink

theorem highShape_optRate (v : Fin N) (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (hx' : ¬ X.g.severity x' ≤ X.p.J n)
    (h : highShape X x hx = highShape X x' hx')
    (t t' : OAI.HypercubeRamsey.CubeVertex (X.p.m n)) :
    (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x') t') =
      (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) (X.g.evenType (X.p.J n) x) t) := by
  classical
  obtain ⟨r, es, eg, hi, hs, hl, hg, ho⟩ := highShape_full_equiv X x x' hx hx' h
  let i := X.g.key x
  let i' := X.g.key x'
  let S := X.g.typeKeys (X.p.J n) x
  let S' := X.g.typeKeys (X.p.J n) x'
  let a := X.optKeyOf (i, S, none) t
  let a' := X.optKeyOf (i', S', none) t'
  have ha : a ∉ S := by simp [a, S, Setup5.optKeyOf, ChunkGeometry5.typeKeys, hx]
  have ha' : a' ∉ S' := by simp [a', S', Setup5.optKeyOf, ChunkGeometry5.typeKeys, hx']
  obtain ⟨ea, hea, hla, hlink⟩ := insert_matches X r.perm S S' es (fun ℓ => ⟨hs ℓ, hl ℓ⟩)
    a a' ha ha' ⟨ho t t', rfl⟩
  have hk : X.g.evenType (X.p.J n) x = (i, S, none) := by simp [ChunkGeometry5.evenType, hx, i, S]
  have hk' : X.g.evenType (X.p.J n) x' = (i', S', none) := by simp [ChunkGeometry5.evenType, hx', i', S']
  rw [hk, hk']
  exact optRate_bin_equiv X v r.perm i i' S S' hi eg hg es hs hl t t' ea hea hla hlink

theorem key_level_le (ℓ : X.Key) : ℓ.level ≤ X.p.J n := by
  cases ℓ with
  | inr i => exact Nat.le_refl _
  | inl k => exact Nat.le_of_lt_succ k.2.2.isLt

def capNaming (ℓ : X.Key) : BinNaming n :=
  namingOfBound (binList5 ℓ.coarse) (by
    have h := binList_card_le ℓ.coarse
    have hmul : 3 ^ coarseChunkCount5 ≤ shapeBinBound := by
      unfold shapeBinBound
      have hc : 1 ≤ coarseChunkCount5 * 4 + 1 := by omega
      simpa using Nat.mul_le_mul_right (3 ^ coarseChunkCount5) hc
    exact h.trans hmul)

def capCode (ℓ : X.Key) : LowShape (X.p.m n) (X.p.J n) :=
  let b := capNaming X ℓ
  (⟨ℓ.level, Nat.lt_succ_of_le (key_level_le X ℓ)⟩, Finset.univ.image b.labels,
    coarseCode b ℓ.coarse (Finset.Subset.refl _), fun _ => ⟨0, by omega⟩)

theorem capCode_rate (v : Fin N) (ℓ ℓ' : X.Key) (h : capCode X ℓ = capCode X ℓ') :
    (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ') =
      (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := by
  classical
  let b := capNaming X ℓ
  let b' := capNaming X ℓ'
  have hl : ℓ.level = ℓ'.level := congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.1.val) h
  have hb : Finset.univ.image b.labels = Finset.univ.image b'.labels :=
    congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.2.1) h
  have hc : coarseCode b ℓ.coarse (Finset.Subset.refl _) =
      coarseCode b' ℓ'.coarse (Finset.Subset.refl _) :=
    congrArg (fun c : LowShape (X.p.m n) (X.p.J n) => c.2.2.1) h
  obtain ⟨r⟩ := binRename_exists b.bins b'.bins b.labels b'.labels hb
  exact capRate_bin_equiv X v r.perm ℓ ℓ'
    (priorMatch_of_code X b b' r ℓ ℓ' _ _ hc hl)

theorem gateKey_bins_subset (x : OAI.HypercubeRamsey.CubeVertex n) (ℓ : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x)) :
    binList5 ℓ.coarse ⊆ localBins X.g x := by
  classical
  unfold Setup5.gateKeys at hℓ
  rcases Finset.mem_union.mp hℓ with hℓ | hℓ
  · exact typeKey_bins_subset X.g (X.p.J n) x ℓ hℓ
  · by_cases hn : (X.g.evenType (X.p.J n) x).2.2 = none
    · simp only [hn, ↓reduceIte, Finset.mem_singleton] at hℓ
      subst ℓ
      exact central_bins_subset X.g x
    · simp [hn] at hℓ

theorem low_gate_compatible (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (ℓ : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x)) :
    LevelCompatible (some ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩) ℓ := by
  have hg : X.gateKeys (X.g.evenType (X.p.J n) x) = X.g.typeKeys (X.p.J n) x := by
    simp [Setup5.gateKeys, ChunkGeometry5.evenType, hx]
  rw [hg] at hℓ
  exact low_type_compatible X x hx ℓ hℓ

theorem high_gate_compatible (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (ℓ : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x)) : LevelCompatible none ℓ := by
  classical
  unfold Setup5.gateKeys at hℓ
  rcases Finset.mem_union.mp hℓ with hℓ | hℓ
  · exact high_type_compatible X x hx ℓ hℓ
  · have hn : (X.g.evenType (X.p.J n) x).2.2 = none := by simp [ChunkGeometry5.evenType, hx]
    simp only [hn, ↓reduceIte, Finset.mem_singleton] at hℓ
    subst ℓ
    rfl

def lowComparisonCode (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (ℓ : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x)) : LowShape (X.p.m n) (X.p.J n) × KeyCode :=
  (lowShape X x hx, keyCode X (localNaming X.g x)
    (some ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩) ℓ (gateKey_bins_subset X x ℓ hℓ))

def highComparisonCode (x : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (ℓ : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x)) : HighShape × KeyCode :=
  (highShape X x hx, keyCode X (localNaming X.g x) none ℓ (gateKey_bins_subset X x ℓ hℓ))

theorem lowComparison_rate (v : Fin N) (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (hx' : X.g.severity x' ≤ X.p.J n) (ℓ ℓ' : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x))
    (hℓ' : ℓ' ∈ X.gateKeys (X.g.evenType (X.p.J n) x'))
    (h : lowComparisonCode X x hx ℓ hℓ = lowComparisonCode X x' hx' ℓ' hℓ') :
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ' (X.g.key x').1
        (X.p.typeSegs n (X.g.evenType (X.p.J n) x'))) =
      (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ (X.g.key x).1
        (X.p.typeSegs n (X.g.evenType (X.p.J n) x))) := by
  classical
  have hshape : lowShape X x hx = lowShape X x' hx' := congrArg Prod.fst h
  obtain ⟨r, es, hi, hs, hl⟩ := lowShape_key_equiv X x x' hx hx' hshape
  let j : Fin (X.p.J n + 1) := ⟨X.g.severity x, Nat.lt_succ_of_le hx⟩
  let j' : Fin (X.p.J n + 1) := ⟨X.g.severity x', Nat.lt_succ_of_le hx'⟩
  have hj : j = j' := congrArg Prod.fst hshape
  have hkey : keyCode X (localNaming X.g x) (some j) ℓ (gateKey_bins_subset X x ℓ hℓ) =
      keyCode X (localNaming X.g x') (some j) ℓ' (gateKey_bins_subset X x' ℓ' hℓ') := by
    simpa only [lowComparisonCode, ← hj] using congrArg Prod.snd h
  have hm := (keyCode_match X _ _ r (some j) ℓ ℓ' _ _ hkey
    (low_gate_compatible X x hx ℓ hℓ)
    (by simpa only [hj] using low_gate_compatible X x' hx' ℓ' hℓ')).1
  have hu : X.p.typeSegs n (X.g.evenType (X.p.J n) x) =
      X.p.typeSegs n (X.g.evenType (X.p.J n) x') := by
    simpa [Params5.typeSegs, ChunkGeometry5.evenType, hx, hx'] using
      congrArg (X.p.uSeg n) (congrArg Fin.val hj)
  simpa only [hi, hu] using step1Rate_bin_equiv X v r.perm ℓ ℓ' hm (X.g.key x).1
    (X.p.typeSegs n (X.g.evenType (X.p.J n) x))

theorem highComparison_rate (v : Fin N) (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (hx' : ¬ X.g.severity x' ≤ X.p.J n) (ℓ ℓ' : X.Key)
    (hℓ : ℓ ∈ X.gateKeys (X.g.evenType (X.p.J n) x))
    (hℓ' : ℓ' ∈ X.gateKeys (X.g.evenType (X.p.J n) x'))
    (h : highComparisonCode X x hx ℓ hℓ = highComparisonCode X x' hx' ℓ' hℓ') :
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ' (X.g.key x').1
        (X.p.typeSegs n (X.g.evenType (X.p.J n) x'))) =
      (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ (X.g.key x).1
        (X.p.typeSegs n (X.g.evenType (X.p.J n) x))) := by
  classical
  have hshape : highShape X x hx = highShape X x' hx' := congrArg Prod.fst h
  obtain ⟨r, es, hi, hs, hl⟩ := highShape_key_equiv X x x' hx hx' hshape
  have hkey := congrArg Prod.snd h
  have hm := (keyCode_match X _ _ r none ℓ ℓ' _ _ hkey
    (high_gate_compatible X x hx ℓ hℓ) (high_gate_compatible X x' hx' ℓ' hℓ')).1
  simpa [Params5.typeSegs, ChunkGeometry5.evenType, hx, hx', hi] using
    step1Rate_bin_equiv X v r.perm ℓ ℓ' hm (X.g.key x).1 (X.p.uStarSeg n)

theorem lowShape_keys_card (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : X.g.severity x ≤ X.p.J n) (hx' : X.g.severity x' ≤ X.p.J n)
    (h : lowShape X x hx = lowShape X x' hx') :
    (X.g.typeKeys (X.p.J n) x).card = (X.g.typeKeys (X.p.J n) x').card := by
  obtain ⟨r, es, _⟩ := lowShape_key_equiv X x x' hx hx' h
  simpa using Fintype.card_congr es

theorem highShape_keys_card (x x' : OAI.HypercubeRamsey.CubeVertex n)
    (hx : ¬ X.g.severity x ≤ X.p.J n) (hx' : ¬ X.g.severity x' ≤ X.p.J n)
    (h : highShape X x hx = highShape X x' hx') :
    (X.g.typeKeys (X.p.J n) x).card = (X.g.typeKeys (X.p.J n) x').card := by
  obtain ⟨r, es, _⟩ := highShape_key_equiv X x x' hx hx' h
  simpa using Fintype.card_congr es

end
end HypercubeRamsey.Lane_sol_s05_h1
