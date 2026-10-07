import Mathlib

namespace HypercubeRamsey
namespace LinearCodePToolsCubeR

open Finset LinearMap Module Submodule

noncomputable instance instFintypeLinearMapBinary (h : ℕ) :
    Fintype ((Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) := by
  classical
  let D := (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2
  have hinj : Function.Injective (fun f : D => (f : (Fin h → ZMod 2) → ZMod 2)) := by
    intro f g hfg
    apply LinearMap.ext
    intro x
    exact congrFun hfg x
  letI : Finite D := Finite.of_injective (fun f : D => (f : (Fin h → ZMod 2) → ZMod 2)) hinj
  exact Fintype.ofFinite D

def support {h : ℕ} (x : Fin h → ZMod 2) : Finset (Fin h) :=
  Finset.univ.filter fun i => x i ≠ 0

def weight {h : ℕ} (x : Fin h → ZMod 2) : ℕ := (support x).card

def fromSupport {h : ℕ} (s : Finset (Fin h)) : Fin h → ZMod 2 :=
  fun i => if i ∈ s then 1 else 0

noncomputable def supportEquiv (h : ℕ) : (Fin h → ZMod 2) ≃ Finset (Fin h) where
  toFun := support
  invFun := fromSupport
  left_inv := by
    intro x
    funext i
    by_cases hx : x i = 0
    · simp [fromSupport, support, hx]
    · have hx1 : x i = 1 := by
        have hvals : x i = 0 ∨ x i = 1 := by
          have hv := ZMod.val_lt (x i)
          by_cases hz : (x i).val = 0
          · exact Or.inl ((ZMod.val_eq_zero (x i)).mp hz)
          · have hone : (x i).val = 1 := by omega
            exact Or.inr ((ZMod.val_eq_one (by norm_num : 1 < 2) (x i)).mp hone)
        exact hvals.resolve_left hx
      simp [fromSupport, support, hx, hx1]
  right_inv := by
    intro s
    ext i
    simp [fromSupport, support]

noncomputable def supportLayerEquiv (h j : ℕ) :
    {x : Fin h → ZMod 2 // weight x = j} ≃ Set.powersetCard (Fin h) j where
  toFun x := ⟨support x.1, x.2⟩
  invFun s := ⟨fromSupport s.1, by
    simpa [weight, support, fromSupport] using s.2⟩
  left_inv x := by
    apply Subtype.ext
    exact (supportEquiv h).left_inv x.1
  right_inv s := by
    apply Subtype.ext
    exact (supportEquiv h).right_inv s.1

lemma card_weightLayer (h j : ℕ) :
    Fintype.card {x : Fin h → ZMod 2 // weight x = j} = Nat.choose h j := by
  calc
    _ = Fintype.card (Set.powersetCard (Fin h) j) :=
      Fintype.card_congr (supportLayerEquiv h j)
    _ = Nat.choose h j := by
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
        Fintype.card_fin]

def weightBall (h w : ℕ) : Finset (Fin h → ZMod 2) :=
  Finset.univ.filter fun x => weight x ≤ w

lemma card_weightBall (h w : ℕ) :
    (weightBall h w).card = ∑ j ∈ Finset.range (w + 1), Nat.choose h j := by
  classical
  have hfilter : (weightBall h w).filter (fun x => weight x ∈ Finset.range (w + 1)) =
      weightBall h w := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, _⟩
      exact hw
    · intro hw
      refine ⟨hw, Finset.mem_range.mpr ?_⟩
      change x ∈ Finset.univ.filter (fun y : Fin h → ZMod 2 => weight y ≤ w) at hw
      have hxw := (Finset.mem_filter.mp hw).2
      omega
  calc
    (weightBall h w).card =
        ∑ j ∈ Finset.range (w + 1), ((weightBall h w).filter fun x => weight x = j).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter, hfilter]
    _ = ∑ j ∈ Finset.range (w + 1), Nat.choose h j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjrange : j < w + 1 := Finset.mem_range.mp hj
      have hjw : j ≤ w := by omega
      have hfiber : (weightBall h w).filter (fun x => weight x = j) =
          Finset.univ.filter (fun x : Fin h → ZMod 2 => weight x = j) := by
        ext x
        simp only [weightBall, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hfiber]
      calc
        (Finset.univ.filter (fun x : Fin h → ZMod 2 => weight x = j)).card =
            Fintype.card {x : Fin h → ZMod 2 // weight x = j} := by
          exact (Fintype.card_subtype (fun x : Fin h → ZMod 2 => weight x = j)).symm
        _ = Nat.choose h j := card_weightLayer h j

lemma finrank_binarySpace (h : ℕ) :
    Module.finrank (ZMod 2) (Fin h → ZMod 2) = h := by
  rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin h)), Fintype.card_fin]

lemma card_binaryVectorSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Fintype V] :
    Fintype.card V = 2 ^ Module.finrank (ZMod 2) V := by
  classical
  let b := Basis.ofVectorSpace (ZMod 2) V
  calc
    Fintype.card V = Fintype.card (ZMod 2) ^ Fintype.card (Basis.ofVectorSpaceIndex (ZMod 2) V) :=
      Module.card_fintype b
    _ = 2 ^ Module.finrank (ZMod 2) V := by
      rw [ZMod.card, ← Module.finrank_eq_card_basis b]

lemma card_binaryDual (h : ℕ) :
    Fintype.card ((Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) = 2 ^ h := by
  let V := Fin h → ZMod 2
  let D := V →ₗ[ZMod 2] ZMod 2
  have hV : Module.finrank (ZMod 2) V = h := finrank_binarySpace h
  have hD : Module.finrank (ZMod 2) D = h := by
    change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) = h
    rw [Subspace.dual_finrank_eq, hV]
  simpa [hD] using (card_binaryVectorSpace (V := D))

def evalAt {h : ℕ} (x : Fin h → ZMod 2) :
    ((Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun f => f x
  map_add' := by intro f g; rfl
  map_smul' := by intro c f; rfl

lemma evalKernelCard {h : ℕ} (x : Fin h → ZMod 2) (hx : x ≠ 0) :
    (Finset.univ.filter fun f : (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2 => f x = 0).card =
      2 ^ (h - 1) := by
  classical
  let V := Fin h → ZMod 2
  let D := V →ₗ[ZMod 2] ZMod 2
  let e := evalAt x
  have hV : Module.finrank (ZMod 2) V = h := finrank_binarySpace h
  have hD : Module.finrank (ZMod 2) D = h := by
    change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) = h
    rw [Subspace.dual_finrank_eq, hV]
  have hposV : 0 < Module.finrank (ZMod 2) V :=
    (Module.finrank_pos_iff_exists_ne_zero).2 ⟨x, hx⟩
  have hpos : 0 < h := by rw [← hV]; exact hposV
  have heSurj : Function.Surjective e := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hx
    intro y
    refine ⟨y • f, ?_⟩
    simp [e, evalAt, hf]
  have hrank : Module.finrank (ZMod 2) (LinearMap.range e) = 1 := by
    rw [LinearMap.range_eq_top.mpr heSurj, finrank_top, Module.finrank_self]
  have hnull : Module.finrank (ZMod 2) (LinearMap.ker e) = h - 1 := by
    have hrn := e.finrank_range_add_finrank_ker
    rw [hrank, hD] at hrn
    omega
  have hkernelType : Fintype.card (LinearMap.ker e) = 2 ^ (h - 1) := by
    simpa [hnull] using (card_binaryVectorSpace (V := LinearMap.ker e))
  have equiv : {f : D // f ∈ LinearMap.ker e} ≃ {f : D // f x = 0} :=
    Equiv.subtypeEquiv (Equiv.refl D) fun f => by simp [e, evalAt, LinearMap.mem_ker]
  calc
    _ = Fintype.card {f : D // f x = 0} := by
      exact (Fintype.card_subtype (fun f : D => f x = 0)).symm
    _ = Fintype.card {f : D // f ∈ LinearMap.ker e} :=
      (Fintype.card_congr equiv).symm
    _ = 2 ^ (h - 1) := hkernelType

lemma chooseNextRow {h r : ℕ}
    (rows : Fin r → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hrows : LinearIndependent (ZMod 2) rows) (hr : r < h)
    (B : Finset (Fin h → ZMod 2))
    (hB : ∀ x ∈ B, x ≠ 0 ∧ ∀ i, rows i x = 0) :
    ∃ f : (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      f ∉ Submodule.span (ZMod 2) (Set.range rows) ∧
      2 * (B.filter fun x => f x = 0).card ≤ B.card := by
  classical
  let D := (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2
  let S : Submodule (ZMod 2) D := Submodule.span (ZMod 2) (Set.range rows)
  let T : Finset D := Finset.univ.filter fun f => f ∉ S
  let Ss : Finset D := Finset.univ.filter fun f => f ∈ S
  have hSdim : Module.finrank (ZMod 2) S = r := by
    simpa using (finrank_span_eq_card hrows)
  have hScard : Fintype.card S = 2 ^ r := by
    simpa [hSdim] using (card_binaryVectorSpace (V := S))
  have hSfilter : Ss.card = Fintype.card S := by
    change (Finset.univ.filter (fun f : D => f ∈ S)).card =
      Fintype.card {f : D // f ∈ S}
    exact (Fintype.card_subtype (fun f : D => f ∈ S)).symm
  have hTcard : T.card = 2 ^ h - 2 ^ r := by
    have hsdiff : T = Finset.univ \ Ss := by
      ext f
      simp [T, Ss]
    rw [hsdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      card_binaryDual, hSfilter, hScard]
  have hpowlt : 2 ^ r < 2 ^ h := Nat.pow_lt_pow_right (by norm_num) hr
  have hTpos : 0 < T.card := by rw [hTcard]; omega
  by_cases hBempty : B = ∅
  · obtain ⟨f, hf⟩ := Finset.card_pos.mp hTpos
    refine ⟨f, (Finset.mem_filter.mp hf).2, ?_⟩
    simp [hBempty]
  · have hBpos : 0 < B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hBempty)
    have hpowEq : 2 ^ h = 2 * 2 ^ (h - 1) := by
      have heq : h - 1 + 1 = h := by omega
      calc
        2 ^ h = 2 ^ (h - 1 + 1) := by rw [heq]
        _ = 2 ^ (h - 1) * 2 := by rw [Nat.pow_succ]
        _ = 2 * 2 ^ (h - 1) := by ring
    have hr' : r ≤ h - 1 := by omega
    have hpowle : 2 ^ r ≤ 2 ^ (h - 1) := Nat.pow_le_pow_right (by norm_num) hr'
    have hratio : 2 * (2 ^ (h - 1) - 2 ^ r) < T.card := by
      rw [hTcard, hpowEq]
      have hbpos : 0 < 2 ^ r := Nat.pow_pos (by norm_num)
      omega
    have hpair :
        (∑ f ∈ T, (B.filter fun x => f x = 0).card) =
          ∑ x ∈ B, (T.filter fun f => f x = 0).card := by
      calc
        _ = ∑ f ∈ T, ∑ x ∈ B, if f x = 0 then 1 else 0 := by
          simp only [Finset.card_filter]
        _ = ∑ x ∈ B, ∑ f ∈ T, if f x = 0 then 1 else 0 := Finset.sum_comm
        _ = _ := by simp only [Finset.card_filter]
    have hcount (x : Fin h → ZMod 2) (hx : x ∈ B) :
        (T.filter fun f => f x = 0).card = 2 ^ (h - 1) - 2 ^ r := by
      have hx0 := (hB x hx).1
      have hvan := (hB x hx).2
      have hSker : S ≤ LinearMap.ker (evalAt x) := by
        apply Submodule.span_le.mpr
        rintro f ⟨i, rfl⟩
        simp [evalAt, hvan i]
      let Kx : Finset D := Finset.univ.filter fun f => f x = 0
      have hSsK : Ss ⊆ Kx := by
        intro f hf
        have hmemS : f ∈ S := (Finset.mem_filter.mp hf).2
        have hmemK : f ∈ LinearMap.ker (evalAt x) := hSker hmemS
        simpa [Kx, evalAt, LinearMap.mem_ker] using hmemK
      have hKcard : Kx.card = 2 ^ (h - 1) := by
        simpa [Kx] using evalKernelCard x hx0
      have hfilters : T.filter (fun f => f x = 0) = Kx \ Ss := by
        ext f
        simp [T, Ss, Kx, and_comm, and_left_comm]
      rw [hfilters, Finset.card_sdiff_of_subset hSsK, hKcard, hSfilter, hScard]
    have hpairEq :
        (∑ f ∈ T, (B.filter fun x => f x = 0).card) =
          B.card * (2 ^ (h - 1) - 2 ^ r) := by
      rw [hpair]
      calc
        _ = ∑ x ∈ B, (2 ^ (h - 1) - 2 ^ r) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hcount x hx
        _ = _ := by simp
    have hpairStrict :
        2 * (∑ f ∈ T, (B.filter fun x => f x = 0).card) < B.card * T.card := by
      calc
        _ = B.card * (2 * (2 ^ (h - 1) - 2 ^ r)) := by rw [hpairEq]; ring
        _ < B.card * T.card := Nat.mul_lt_mul_of_pos_left hratio hBpos
    have hexists : ∃ f ∈ T, 2 * (B.filter fun x => f x = 0).card < B.card := by
      by_contra hn
      push_neg at hn
      have hLower : B.card * T.card ≤
          ∑ f ∈ T, 2 * (B.filter fun x => f x = 0).card := by
        calc
          _ = ∑ f ∈ T, B.card := by simp [Nat.mul_comm]
          _ ≤ _ := Finset.sum_le_sum fun f hf => hn f hf
      have hsum :
          (∑ f ∈ T, 2 * (B.filter fun x => f x = 0).card) =
            2 * (∑ f ∈ T, (B.filter fun x => f x = 0).card) := by
        rw [← Finset.mul_sum]
      exact (Nat.not_lt_of_ge (hLower.trans_eq hsum)) hpairStrict
    obtain ⟨f, hfT, hfsmall⟩ := hexists
    refine ⟨f, (Finset.mem_filter.mp hfT).2, ?_⟩
    omega

def lowWords (h w : ℕ) : Finset (Fin h → ZMod 2) :=
  Finset.univ.filter fun x => x ≠ 0 ∧ weight x ≤ w

def badRows {h r : ℕ} (low : Finset (Fin h → ZMod 2))
    (rows : Fin r → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) : Finset (Fin h → ZMod 2) :=
  low.filter fun x => ∀ i, rows i x = 0

def snocRows {h r : ℕ} (f : (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (rows : Fin r → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    Fin (r + 1) → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (fun o : Option (Fin r) => o.casesOn' f rows) ∘ finSuccEquiv r

lemma badRows_snoc {h r : ℕ} (low : Finset (Fin h → ZMod 2))
    (f : (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (rows : Fin r → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    badRows low (snocRows f rows) = (badRows low rows).filter fun x => f x = 0 := by
  ext x
  have hrow : (∀ i : Fin (r + 1), snocRows f rows i x = 0) ↔
      f x = 0 ∧ ∀ i : Fin r, rows i x = 0 := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have h0 := h 0
        simpa [snocRows, finSuccEquiv_zero] using h0
      · intro i
        have hi := h i.succ
        simpa [snocRows, finSuccEquiv_succ] using hi
    · rintro ⟨hf, hrows⟩ i
      cases hi : finSuccEquiv r i with
      | none =>
          have hi0 : i = 0 := by simpa using hi
          subst i
          simpa [snocRows, finSuccEquiv_zero] using hf
      | some j =>
          have his : i = j.succ := by simpa using hi
          subst i
          simpa [snocRows, finSuccEquiv_succ] using hrows j
  simp [badRows, hrow, and_assoc, and_left_comm, and_comm]

lemma exists_goodRows {h m : ℕ} (hmh : m ≤ h)
    (low : Finset (Fin h → ZMod 2)) (hlow : low.card < 2 ^ m)
    (hlow0 : ∀ x ∈ low, x ≠ 0) :
    ∃ rows : Fin m → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2,
      LinearIndependent (ZMod 2) rows ∧ badRows low rows = ∅ := by
  classical
  have hbuild : ∀ r, r ≤ m →
      ∃ rows : Fin r → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2,
        LinearIndependent (ZMod 2) rows ∧ 2 ^ r * (badRows low rows).card ≤ low.card := by
    intro r
    induction r with
    | zero =>
        intro _
        let rows : Fin 0 → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2 := Fin.elim0
        refine ⟨rows, linearIndependent_empty_type, ?_⟩
        simp [badRows, rows]
    | succ r ih =>
        intro hrs
        have hrle : r ≤ m := by omega
        obtain ⟨rows, hrows, hbound⟩ := ih hrle
        have hrh : r < h := lt_of_lt_of_le (Nat.lt_succ_self r) (le_trans hrs hmh)
        let B := badRows low rows
        have hB (x : Fin h → ZMod 2) (hx : x ∈ B) :
            x ≠ 0 ∧ ∀ i, rows i x = 0 := by
          have hx' := Finset.mem_filter.mp hx
          exact ⟨hlow0 x hx'.1, hx'.2⟩
        obtain ⟨f, hfspan, hfsmall⟩ := chooseNextRow rows hrows hrh B hB
        let rows' := snocRows f rows
        have hrows' : LinearIndependent (ZMod 2) rows' := by
          apply (linearIndependent_equiv (finSuccEquiv r)).2
          exact LinearIndependent.option hrows hfspan
        have hB' : badRows low rows' = B.filter fun x => f x = 0 := by
          exact badRows_snoc low f rows
        refine ⟨rows', hrows', ?_⟩
        calc
          2 ^ (r + 1) * (badRows low rows').card =
              2 ^ r * (2 * (B.filter fun x => f x = 0).card) := by
                rw [Nat.pow_succ, hB']
                ring
          _ ≤ 2 ^ r * B.card := Nat.mul_le_mul_left _ hfsmall
          _ ≤ low.card := hbound
  obtain ⟨rows, hrows, hbound⟩ := hbuild m le_rfl
  have hbad0 : badRows low rows = ∅ := by
    apply Finset.card_eq_zero.mp
    by_contra hn
    have hpos : 1 ≤ (badRows low rows).card := Nat.one_le_iff_ne_zero.mpr hn
    have hge : 2 ^ m ≤ 2 ^ m * (badRows low rows).card := by
      calc
        2 ^ m = 2 ^ m * 1 := by simp
        _ ≤ 2 ^ m * (badRows low rows).card := Nat.mul_le_mul_left (2 ^ m) hpos
    omega
  exact ⟨rows, hrows, hbad0⟩

def rowMap {h m : ℕ} (rows : Fin m → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun := fun x i => rows i x
  map_add' := by intro x y; ext i; simp
  map_smul' := by intro c x; ext i; simp

def coordEval {m : ℕ} (i : Fin m) : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := fun y => y i
  map_add' := by intro x y; rfl
  map_smul' := by intro c y; rfl

lemma dualExpand {m : ℕ} (φ : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    φ = ∑ i : Fin m, φ (Pi.single i (1 : ZMod 2)) • coordEval i := by
  apply LinearMap.ext
  intro y
  have hy := pi_eq_sum_univ' y
  calc
    φ y = φ (∑ i : Fin m, y i • (Pi.single i (1 : ZMod 2) : Fin m → ZMod 2)) :=
      congrArg φ hy
    _ = ∑ i : Fin m, y i * φ (Pi.single i (1 : ZMod 2)) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i : Fin m, φ (Pi.single i (1 : ZMod 2)) * y i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i : Fin m, φ (Pi.single i (1 : ZMod 2)) • coordEval i) y := by
      simp [coordEval, smul_eq_mul]

lemma rowMap_surjective {h m : ℕ}
    (rows : Fin m → (Fin h → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hrows : LinearIndependent (ZMod 2) rows) : Function.Surjective (rowMap rows) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro φ ψ hφψ
  have hzero : (rowMap rows).dualMap (φ - ψ) = 0 := by
    rw [map_sub, hφψ]
    simp
  have hcomb : ∑ i : Fin m, (φ - ψ) (Pi.single i (1 : ZMod 2)) • rows i = 0 := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hzero x
    rw [LinearMap.dualMap_apply] at hx
    rw [dualExpand (φ - ψ)] at hx
    simpa [rowMap, coordEval, smul_eq_mul] using hx
  let c : Fin m → ZMod 2 := fun i => (φ - ψ) (Pi.single i 1)
  have hlin : Fintype.linearCombination (ZMod 2) rows c = 0 := by
    change ∑ i : Fin m, c i • rows i = 0
    simpa [c] using hcomb
  have hc : c = 0 := by
    apply hrows.fintypeLinearCombination_injective
    simpa using hlin
  have hφψ : φ - ψ = 0 := by
    apply LinearMap.ext
    intro y
    have hcoeff (i : Fin m) : (φ - ψ) (Pi.single i (1 : ZMod 2)) = 0 := by
      have hi := congrFun hc i
      simpa [c] using hi
    calc
      (φ - ψ) y = (∑ i : Fin m, (φ - ψ) (Pi.single i (1 : ZMod 2)) • coordEval i) y := by
        exact congrArg (fun g : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2 => g y)
          (dualExpand (φ - ψ))
      _ = ∑ i : Fin m, (φ - ψ) (Pi.single i (1 : ZMod 2)) * y i := by
        simp [coordEval, smul_eq_mul]
      _ = 0 := by simp [hcoeff]
  exact sub_eq_zero.mp hφψ

theorem varshamovAux (h m w : ℕ) (hmh : m ≤ h) (_wh : w ≤ h)
    (hvolume : (∑ j ∈ Finset.range (w + 1), Nat.choose h j) < 2 ^ m) :
    ∃ L : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      Function.Surjective L ∧ ∀ x, L x = 0 → x ≠ 0 → w < weight x := by
  classical
  have hlowcard : (lowWords h w).card < 2 ^ m := by
    have hzero : 0 ∈ weightBall h w := by simp [weightBall, weight, support]
    have hlow : lowWords h w = (weightBall h w).erase 0 := by
      ext x
      simp [lowWords, weightBall, Finset.mem_erase, and_comm]
    have hlowEraseCard : (lowWords h w).card = (weightBall h w).card - 1 := by
      rw [hlow, Finset.card_erase_of_mem hzero]
    rw [hlowEraseCard, card_weightBall h w]
    omega
  have hlow0 : ∀ x ∈ lowWords h w, x ≠ 0 := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  obtain ⟨rows, hrows, hbad⟩ := exists_goodRows hmh (lowWords h w) hlowcard hlow0
  let L := rowMap rows
  refine ⟨L, rowMap_surjective rows hrows, ?_⟩
  intro x hL hx
  by_contra hnot
  have hwt : weight x ≤ w := Nat.not_lt.mp hnot
  have hxlow : x ∈ lowWords h w := by
    simp [lowWords, hx, hwt]
  have hrowszero : ∀ i, rows i x = 0 := by
    intro i
    have hi := congrArg (fun y : Fin m → ZMod 2 => y i) hL
    simpa [L, rowMap] using hi
  have hxbad : x ∈ badRows (lowWords h w) rows := Finset.mem_filter.mpr ⟨hxlow, hrowszero⟩
  rw [hbad] at hxbad
  simpa using hxbad

end LinearCodePToolsCubeR
end HypercubeRamsey
