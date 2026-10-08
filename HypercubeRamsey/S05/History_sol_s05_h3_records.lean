import HypercubeRamsey.S05.History_sol_s05_h3

namespace HypercubeRamsey.Lane_sol_s05_h23

open Classical OAI.HypercubeRamsey Lane_q_s05_h23
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

theorem signShiftType_involutive (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    signShiftType5 X t (signShiftType5 X t K) = K := by
  change (K.1, (K.2.1.image (signShiftKey5 X t)).image (signShiftKey5 X t), K.2.2) = K
  rw [Finset.image_image]
  change (K.1, K.2.1.image (fun ℓ => signShiftKey5 X t (signShiftKey5 X t ℓ)), K.2.2) = K
  have he : (fun ℓ => signShiftKey5 X t (signShiftKey5 X t ℓ)) = id := by
    funext ℓ
    exact signShiftKey5_apply_apply X t ℓ
  rw [he, Finset.image_id]

noncomputable def signTypePerm (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) : X.Ty ≃ X.Ty where
  toFun := signShiftType5 X t
  invFun := signShiftType5 X t
  left_inv := signShiftType_involutive X t
  right_inv := signShiftType_involutive X t

theorem blockGate_signShift (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (z : X.Block K) :
    X.blockGate b (signShiftType5 X t K) z ↔ X.blockGate b K z := by
  classical
  cases hlevel : K.2.2 with
  | some j => exact blockGate_signShiftLow5 X b t K hlevel z
  | none =>
    let e := signShiftKey5 X t
    let φ : X.Key → Prop := fun ℓ => ∀ y, (X.priorRep b ℓ K.1.1 z).w y ≤
      Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n K)) *
        (X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)).w y
    have hφ (ℓ : X.Key) : φ (e ℓ) ↔ φ ℓ := by
      have hr := priorRep_irrel_sign5 X b (e ℓ) ℓ K.1.1 z
        (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)
      have hd := priorDel_irrel_sign5 X b (e ℓ) ℓ K.1.1 (X.p.typeSegs n K)
        (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)
      simp only [φ, hr, hd]
    have hS : (∀ ℓ ∈ K.2.1.image e, φ ℓ) ↔ ∀ ℓ ∈ K.2.1, φ ℓ := by
      simp only [Finset.forall_mem_image, hφ]
    have hgate : X.gateKeys K = K.2.1 ∪ {X.optKeyOf K default} := by
      simp only [Setup5.gateKeys, hlevel, ite_true, Setup5.optKeyOf] <;> rfl
    have hgate' : X.gateKeys (signShiftType5 X t K) =
        K.2.1.image e ∪ {X.optKeyOf K default} := by
      simp only [Setup5.gateKeys, signShiftType5, hlevel, ite_true, Setup5.optKeyOf, e] <;> rfl
    unfold Setup5.blockGate
    rw [hgate', hgate]
    change (∀ ℓ ∈ K.2.1.image e ∪ {X.optKeyOf K default}, φ ℓ) ↔
      (∀ ℓ ∈ K.2.1 ∪ {X.optKeyOf K default}, φ ℓ)
    simp only [Finset.forall_mem_union, Finset.mem_singleton, forall_eq, hS]

theorem blockWeight_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (S : Finset X.Key) (z : X.Block K) :
    X.blockWeight (signShiftHistory5 X t H) (signShiftType5 X t K)
      (S.image (signShiftKey5 X t)) z = X.blockWeight H K S z :=
  blockWeight_signShiftCore5 X H t K S z (propext (blockGate_signShift X H.1 t K z))

theorem blockLawOn_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (S : Finset X.Key) :
    X.blockLawOn (signShiftHistory5 X t H) (signShiftType5 X t K)
      (S.image (signShiftKey5 X t)) = X.blockLawOn H K S := by
  have hw : X.blockWeight (signShiftHistory5 X t H) (signShiftType5 X t K)
      (S.image (signShiftKey5 X t)) = X.blockWeight H K S := by
    funext z
    exact blockWeight_signShift X H t K S z
  unfold Setup5.blockLawOn
  rw [hw]
  rfl

theorem blockLaw_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    X.blockLaw (signShiftHistory5 X t H) (signShiftType5 X t K) = X.blockLaw H K :=
  blockLawOn_signShift X H t K K.2.1

theorem image_erase_signShift (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (S : Finset X.Key) (ℓ : X.Key) :
    (S.image (signShiftKey5 X t)).erase (signShiftKey5 X t ℓ) =
      (S.erase ℓ).image (signShiftKey5 X t) := by
  classical
  ext k
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, a, ha, rfl⟩
    exact ⟨a, ⟨fun h => hne (congrArg (signShiftKey5 X t) h), ha⟩, rfl⟩
  · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
    exact ⟨fun h => hne ((signShiftKey5 X t).injective h), a, ha, rfl⟩

theorem blockLawDel_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (ℓ : X.Key) :
    X.blockLawDel (signShiftHistory5 X t H) (signShiftType5 X t K)
      (signShiftKey5 X t ℓ) = X.blockLawDel H K ℓ := by
  unfold Setup5.blockLawDel
  change X.blockLawOn (signShiftHistory5 X t H) (signShiftType5 X t K)
    ((K.2.1.image (signShiftKey5 X t)).erase (signShiftKey5 X t ℓ)) = _
  rw [image_erase_signShift]
  exact blockLawOn_signShift X H t K (K.2.1.erase ℓ)

theorem array_double_shift {Id : Type} (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (a : X.ArraysOn Id) (id : Id) (K : X.Ty) :
    a (id, signShiftType5 X t (signShiftType5 X t K)) = a (id, K) := by
  rcases K with ⟨q, S, j⟩
  have hS : (S.image (signShiftKey5 X t)).image (signShiftKey5 X t) = S :=
    congrArg (fun K : X.Ty => K.2.1) (signShiftType_involutive X t (q, S, j))
  change a (id, (q, (S.image (signShiftKey5 X t)).image (signShiftKey5 X t), j)) =
    a (id, (q, S, j))
  let f : Finset X.Key → X.Array (q, S, j) := fun S' => a (id, (q, S', j))
  exact congrArg f hS

noncomputable def arraysSignPerm {Id : Type} (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) : X.ArraysOn Id ≃ X.ArraysOn Id where
  toFun a c := a (c.1, signShiftType5 X t c.2)
  invFun a c := a (c.1, signShiftType5 X t c.2)
  left_inv := by
    intro a
    funext c
    rcases c with ⟨id, K⟩
    exact array_double_shift X t a id K
  right_inv := by
    intro a
    funext c
    rcases c with ⟨id, K⟩
    exact array_double_shift X t a id K

theorem arraysSignPerm_apply {Id : Type} (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (a : X.ArraysOn Id) (id : Id) (K : X.Ty) :
    arraysSignPerm X t a (id, signShiftType5 X t K) = a (id, K) := by
  exact array_double_shift X t a id K

theorem recArrayLaw_signShift_weight (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (a : X.ArraysOn (Fin (X.p.T n))) :
    (X.recArrayLaw (signShiftHistory5 X t H)).w (arraysSignPerm X t a) =
      (X.recArrayLaw H).w a := by
  classical
  let e := (Equiv.refl (Fin (X.p.T n))).prodCongr (signTypePerm X t)
  change (∏ c : Fin (X.p.T n) × X.Ty, ∏ i : Fin (X.p.typeBlocks n c.2),
    (X.blockLaw (signShiftHistory5 X t H) c.2).w (arraysSignPerm X t a c i)) = _
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro c _
  change (∏ i : Fin (X.p.typeBlocks n c.2),
    (X.blockLaw (signShiftHistory5 X t H) (signShiftType5 X t c.2)).w
      (arraysSignPerm X t a (c.1, signShiftType5 X t c.2) i)) =
    ∏ i : Fin (X.p.typeBlocks n c.2), (X.blockLaw H c.2).w (a c i)
  rw [arraysSignPerm_apply, blockLaw_signShift]

def shiftHighRecord (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n))
    (r : X.AbsRecord) : X.AbsRecord :=
  (r.1, r.2.1.image (fun c => (c.1, signShiftType5 X t c.2)),
    r.2.2.1.image (fun c =>
      (c.1, signShiftType5 X t c.2.1, c.2.2.map (signShiftKey5 X t))), r.2.2.2)


theorem occurring_high_mask_none (X : Setup5 γ K' χ n N E G)
    (r : X.AbsRecord) (hr : X.RecOccurs r) (i : CoarseKey5 n) (hkey : r.1 = .inr i) :
    r.2.2.2 = none := by
  obtain ⟨y, μ, hrec⟩ := hr
  cases hm : r.2.2.2 with
  | none => rfl
  | some m =>
    have h := hrec.2.2.2
    rw [hm] at h
    have hl := h.1
    simp [hkey] at hl

theorem lowCol_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (k : LowKey5 X) :
    X.lowCol (hiddenSignShift5 X t H.2) (signShiftLowKey5 X t k) = X.lowCol H.2 k := by
  unfold Setup5.lowCol
  exact (hiddenSignShift5_apply_low X t H.2 (signShiftLowKey5 X t k) 0).trans
    (congrArg (fun k : LowKey5 X => H.2 (.inl k) (0 : Fin 1)) (signShiftLowKey5_apply_apply X t k))

theorem hitSet_signShift {Id : Type} (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (a : X.ArraysOn Id) (id : Id) (K : X.Ty) (y : Fin N) :
    X.hitSet (arraysSignPerm X t a) (id, signShiftType5 X t K) y = X.hitSet a (id, K) y := by
  unfold Setup5.hitSet
  rw [arraysSignPerm_apply]
  rfl

theorem refSubset_signShift {Id : Type} (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (a : X.ArraysOn Id) (id : Id) (K : X.Ty) (opt : Option X.Key) :
    X.refSubsetOn (signShiftHistory5 X t H) (arraysSignPerm X t a)
      (id, signShiftType5 X t K) (opt.map (signShiftKey5 X t)) =
      X.refSubsetOn H a (id, K) opt := by
  classical
  have hlevel' : (signShiftType5 X t K).2.2 = K.2.2 := rfl
  have hblocks : X.p.typeBlocks n (signShiftType5 X t K) = X.p.typeBlocks n K := rfl
  unfold Setup5.refSubsetOn
  rw [hlevel']
  cases hlevel : K.2.2 with
  | some j => rw [hblocks]
  | none =>
    cases opt with
    | none => rfl
    | some ℓ =>
      cases ℓ with
      | inr i => rfl
      | inl k =>
        have hkey : signShiftKey5 X t (.inl k) = .inl (signShiftLowKey5 X t k) := rfl
        simp only [Option.map_some, hkey]
        have hcol : X.lowCol (signShiftHistory5 X t H).2 (signShiftLowKey5 X t k) =
            X.lowCol H.2 k := lowCol_signShift X H t k
        rw [hcol, hitSet_signShift]


def obsSignMap (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n))
    (c : Fin (X.p.T n) × X.Ty) : Fin (X.p.T n) × X.Ty :=
  (c.1, signShiftType5 X t c.2)

def refSignMap (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n))
    (c : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)) :
    Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound) :=
  (c.1, signShiftType5 X t c.2.1, c.2.2)

theorem refsOn_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (a : X.ArraysOn (Fin (X.p.T n))) :
    X.refsOn (signShiftHistory5 X t H) (shiftHighRecord X t r) (arraysSignPerm X t a) =
      (X.refsOn H r a).image (refSignMap X t) := by
  unfold Setup5.refsOn shiftHighRecord
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro c _
  change (c.1, signShiftType5 X t c.2.1,
    X.refSubsetOn (signShiftHistory5 X t H) (arraysSignPerm X t a)
      (c.1, signShiftType5 X t c.2.1) (c.2.2.map (signShiftKey5 X t))) = _
  rw [refSubset_signShift]
  rfl

theorem refSignMap_injective (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n)) :
    Function.Injective (refSignMap X t) := by
  intro a b hab
  have htwice (c) : refSignMap X t (refSignMap X t c) = c := by
    simp only [refSignMap, signShiftType_involutive]
  exact (htwice a).symm.trans ((congrArg (refSignMap X t) hab).trans (htwice b))

theorem obsSignMap_injective (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n)) :
    Function.Injective (obsSignMap X t) := by
  intro a b hab
  have htwice (c) : obsSignMap X t (obsSignMap X t c) = c := by
    simp only [obsSignMap, signShiftType_involutive]
  exact (htwice a).symm.trans ((congrArg (obsSignMap X t) hab).trans (htwice b))


theorem withCol_high_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (i : CoarseKey5 n) (θ : Fin (X.p.s n) → Fin N) :
    signShiftHistory5 X t (X.withCol H (.inr i) θ) =
      X.withCol (signShiftHistory5 X t H) (.inr i) θ := by
  apply Prod.ext
  · rfl
  funext ℓ
  cases ℓ with
  | inl k =>
    change Function.update H.2 (.inr i) θ (.inl (signShiftLowKey5 X t k)) =
      Function.update (hiddenSignShift5 X t H.2) (.inr i) θ (.inl k)
    exact (Function.update_of_ne (show (Sum.inl (signShiftLowKey5 X t k) : X.Key) ≠ Sum.inr i by simp)
      θ H.2).trans (Function.update_of_ne (show (Sum.inl k : X.Key) ≠ Sum.inr i by simp)
        θ (hiddenSignShift5 X t H.2)).symm
  | inr j =>
    by_cases he : j = i
    · subst j
      change Function.update H.2 (.inr i) θ (.inr i) =
        Function.update (hiddenSignShift5 X t H.2) (.inr i) θ (.inr i)
      exact (Function.update_self (.inr i) θ H.2).trans
        (Function.update_self (.inr i) θ (hiddenSignShift5 X t H.2)).symm
    · change Function.update H.2 (.inr i) θ (.inr j) =
        Function.update (hiddenSignShift5 X t H.2) (.inr i) θ (.inr j)
      exact (Function.update_of_ne (Sum.inr_injective.ne he) θ H.2).trans
        (Function.update_of_ne (Sum.inr_injective.ne he) θ (hiddenSignShift5 X t H.2)).symm


theorem blockMass_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (S : Finset X.Key) :
    X.blockMass (signShiftHistory5 X t H) (signShiftType5 X t K)
      (S.image (signShiftKey5 X t)) = X.blockMass H K S := by
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z _
  exact blockWeight_signShift X H t K S z

theorem mem_signShift_keys_high (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (i : CoarseKey5 n) (S : Finset X.Key) :
    (.inr i : X.Key) ∈ S.image (signShiftKey5 X t) ↔ (.inr i : X.Key) ∈ S := by
  constructor
  · intro h
    obtain ⟨ℓ, hℓ, heq⟩ := Finset.mem_image.mp h
    have he : ℓ = .inr i := (signShiftKey5 X t).injective heq
    simpa only [he] using hℓ
  · intro h
    exact Finset.mem_image.mpr ⟨.inr i, h, rfl⟩

theorem candGateOn_high_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (i : CoarseKey5 n)
    (hkey : r.1 = .inr i) (hmask : r.2.2.2 = none)
    (a : X.ArraysOn (Fin (X.p.T n))) (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.candGateOn (signShiftHistory5 X t H) (shiftHighRecord X t r) (arraysSignPerm X t a) θ ↔
      X.candGateOn H r a θ := by
  classical
  rcases r with ⟨ℓ, data⟩
  change ℓ = .inr i at hkey
  subst ℓ
  change data.2.2 = none at hmask
  unfold Setup5.candGateOn shiftHighRecord
  have hn {α : Type} (x : α) : ((none : Option α) = some x) ↔ False := by
    constructor
    · intro h; cases h
    · intro h; exact h.elim
  have ht (α : Type) : (∀ _ : α, True) ↔ True := ⟨fun _ => trivial, fun _ _ => trivial⟩
  simp only [hmask, hn, false_implies, ht, and_true, Finset.forall_mem_image]
  change (∀ c ∈ data.1, (.inr i : X.Key) ∈ c.2.2.1.image (signShiftKey5 X t) →
      0 < X.blockMass (signShiftHistory5 X t H) (signShiftType5 X t c.2)
        ((c.2.2.1.image (signShiftKey5 X t)).erase (.inr i)) ∧
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n c.2)) * X.p.s n) *
        X.blockMass (signShiftHistory5 X t H) (signShiftType5 X t c.2)
          ((c.2.2.1.image (signShiftKey5 X t)).erase (.inr i)) ≤
        X.blockMass (X.withCol (signShiftHistory5 X t H) (.inr i) θ)
          (signShiftType5 X t c.2) (c.2.2.1.image (signShiftKey5 X t))) ↔ _
  have herase (S : Finset X.Key) : (S.image (signShiftKey5 X t)).erase (.inr i) =
      (S.erase (.inr i)).image (signShiftKey5 X t) := image_erase_signShift X t S (.inr i)
  simp only [mem_signShift_keys_high, herase, blockMass_signShift,
    ← withCol_high_signShift X H t i θ, blockMass_signShift]
  rfl


theorem InRef_signShift (X : Setup5 γ K' χ n N E G) (t : CubeVertex (X.p.m n))
    (ex : Option (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)))
    (c : Fin (X.p.T n) × X.Ty) (i : Fin (X.p.typeBlocks n c.2)) :
    X.InRef (ex.map (refSignMap X t)) (obsSignMap X t c) i ↔ X.InRef ex c i := by
  classical
  cases ex with
  | none =>
    unfold Setup5.InRef
    constructor <;> rintro ⟨e, he, _⟩ <;> cases he
  | some d =>
    unfold Setup5.InRef
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro ⟨e, he, hEq, hJ⟩
      subst e
      refine ⟨d, rfl, ?_, hJ⟩
      exact (obsSignMap_injective X t) hEq
    · rintro ⟨e, he, hEq, hJ⟩
      subst e
      refine ⟨refSignMap X t d, rfl, ?_, hJ⟩
      exact congrArg (obsSignMap X t) hEq


theorem obsLikOn_high_signShift (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (r : X.AbsRecord) (j : CoarseKey5 n)
    (hkey : r.1 = .inr j) (a : X.ArraysOn (Fin (X.p.T n)))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (ex : Option (Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound))) :
    X.obsLikOn (signShiftHistory5 X t H) (shiftHighRecord X t r)
      (arraysSignPerm X t a) θ (ex.map (refSignMap X t)) = X.obsLikOn H r a θ ex := by
  classical
  rcases r with ⟨ℓ, data⟩
  change ℓ = .inr j at hkey
  subst ℓ
  have hfilter :
      (data.1.image (obsSignMap X t)).filter
          (fun c => (.inr j : X.Key) ∈ c.2.2.1) =
        (data.1.filter (fun c => (.inr j : X.Key) ∈ c.2.2.1)).image (obsSignMap X t) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨d, hd, rfl⟩, hj⟩
      exact ⟨d, ⟨hd, (mem_signShift_keys_high X t j d.2.2.1).mp hj⟩, rfl⟩
    · rintro ⟨d, ⟨hd, hj⟩, rfl⟩
      exact ⟨⟨d, hd, rfl⟩, (mem_signShift_keys_high X t j d.2.2.1).mpr hj⟩
  unfold Setup5.obsLikOn
  change (∏ c ∈ (data.1.image (obsSignMap X t)).filter
      (fun c => (.inr j : X.Key) ∈ c.2.2.1), ∏ i : Fin (X.p.typeBlocks n c.2),
      if X.InRef (ex.map (refSignMap X t)) c i then 1 else
        ratio5 ((X.blockLaw (X.withCol (signShiftHistory5 X t H) (.inr j) θ) c.2).w
          (arraysSignPerm X t a c i))
          ((X.blockLawDel (signShiftHistory5 X t H) c.2 (.inr j)).w
            (arraysSignPerm X t a c i))) = _
  rw [hfilter, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro i _
    have href : X.InRef (ex.map (refSignMap X t)) (obsSignMap X t c) i =
        X.InRef ex c i := propext (InRef_signShift X t ex c i)
    rw [href]
    change (if X.InRef ex c i then 1 else
      ratio5 ((X.blockLaw (X.withCol (signShiftHistory5 X t H) (.inr j) θ)
        (signShiftType5 X t c.2)).w
        (arraysSignPerm X t a (c.1, signShiftType5 X t c.2) i))
        ((X.blockLawDel (signShiftHistory5 X t H) (signShiftType5 X t c.2)
          (signShiftKey5 X t (.inr j))).w
          (arraysSignPerm X t a (c.1, signShiftType5 X t c.2) i))) = _
    rw [← withCol_high_signShift X H t j θ, blockLaw_signShift,
      blockLawDel_signShift, arraysSignPerm_apply]
  · intro c _ d _ h
    exact obsSignMap_injective X t h

end
end HypercubeRamsey.Lane_sol_s05_h23
