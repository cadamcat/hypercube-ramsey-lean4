import HypercubeRamsey.Tools.Binomial
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey.Lane_q_s06_front

open scoped BigOperators
open OAI.HypercubeRamsey

noncomputable section

private def halfMassNat (ell i : ℕ) : ℝ :=
  if hi : i < ell + 1 then halfBinomialMass ell ⟨i, hi⟩ else 0

private def prefixMass (ell j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, halfMassNat ell i

/-- Consecutive quantile labels for a binomial count. -/
def quantileLabel (ell : ℕ) (ε : ℝ) (q : ℕ) : ℕ :=
  Nat.floor (prefixMass ell (min q (ell + 1)) / ε)

private abbrev ChunkCoord (n : ℕ) (A : Finset (Fin n)) := {i : Fin n // i ∈ A}
private abbrev OutsideCoord (n : ℕ) (A : Finset (Fin n)) := {i : Fin n // i ∉ A}

private def splitCube {n : ℕ} (A : Finset (Fin n)) :
    CubeVertex n ≃ (ChunkCoord n A → Bool) × (OutsideCoord n A → Bool) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun p i := if hi : i ∈ A then p.1 ⟨i, hi⟩ else p.2 ⟨i, hi⟩
  left_inv x := by
    funext i
    by_cases hi : i ∈ A <;> simp [hi]
  right_inv p := by
    apply Prod.ext
    · funext i
      simp [i.2]
    · funext i
      simp [i.2]

def cubeCountOn {n : ℕ} (A : Finset (Fin n)) (x : CubeVertex n) : ℕ :=
  (A.attach.filter fun i => x i.1 = true).card

def boolWeight {ι : Type*} [Fintype ι] (f : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => f i = true).card

private def boolSupportEquiv (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun f := Finset.univ.filter fun i => f i = true
  invFun s i := decide (i ∈ s)
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv s := by
    ext i
    simp

theorem boolWeightLayerCard (ι : Type*) [Fintype ι] [DecidableEq ι] (q : ℕ) :
    Fintype.card {f : ι → Bool // boolWeight f = q} = Nat.choose (Fintype.card ι) q := by
  classical
  let eSupport := boolSupportEquiv ι
  let e : {f : ι → Bool // boolWeight f = q} ≃ {s : Finset ι // s.card = q} :=
    eSupport.subtypeEquiv (fun f => by rfl)
  let ps : Finset (Finset ι) := Finset.univ.powersetCard q
  have eSub : {s : Finset ι // s.card = q} ≃ {s : Finset ι // s ∈ ps} := by
    refine {
      toFun := fun s => ⟨s.1, by
        change s.1 ∈ Finset.univ.powersetCard q
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.2⟩⟩
      invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp (by
        change s.1 ∈ Finset.univ.powersetCard q
        exact s.2)).2⟩
      left_inv := by intro s; apply Subtype.ext; rfl
      right_inv := by intro s; apply Subtype.ext; rfl }
  calc
    _ = Fintype.card {s : Finset ι // s.card = q} := Fintype.card_congr e
    _ = Fintype.card {s : Finset ι // s ∈ ps} := Fintype.card_congr eSub
    _ = ps.card := Fintype.card_coe ps
    _ = Nat.choose (Fintype.card ι) q := by simp [ps, Finset.card_powersetCard]

/-- The number of cube vertices with a prescribed number of ones on `A`. -/
theorem cubeCountOn_card {n : ℕ} (A : Finset (Fin n)) (q : ℕ) :
    (Finset.univ.filter fun x : CubeVertex n => cubeCountOn A x = q).card =
      Nat.choose A.card q * 2 ^ (n - A.card) := by
  classical
  let I := ChunkCoord n A
  let O := OutsideCoord n A
  let split := splitCube A
  have hCount (x : CubeVertex n) : cubeCountOn A x = boolWeight (split x).1 := rfl
  have splitPredEquiv :
      {x : CubeVertex n // cubeCountOn A x = q} ≃
        {p : (I → Bool) × (O → Bool) // boolWeight p.1 = q} :=
    split.subtypeEquiv (fun x => by rw [hCount x])
  let prodEquiv :
      {p : (I → Bool) × (O → Bool) // boolWeight p.1 = q} ≃
        {f : I → Bool // boolWeight f = q} × (O → Bool) :=
    @Equiv.prodSubtypeFstEquivSubtypeProd (I → Bool) (O → Bool)
      (fun f => boolWeight f = q)
  have hIcard : Fintype.card I = A.card := by
    simp [I, ChunkCoord, Fintype.card_coe]
  have hOcard : Fintype.card O = n - A.card := by
    simpa [O, OutsideCoord, Fintype.card_coe] using
      (Fintype.card_subtype_compl (fun i : Fin n => i ∈ A))
  calc
    (Finset.univ.filter fun x : CubeVertex n => cubeCountOn A x = q).card =
        Fintype.card {x : CubeVertex n // cubeCountOn A x = q} := by
          symm
          simpa using (Fintype.card_subtype (fun x : CubeVertex n => cubeCountOn A x = q))
    _ = Fintype.card {p : (I → Bool) × (O → Bool) // boolWeight p.1 = q} :=
      Fintype.card_congr splitPredEquiv
    _ = Fintype.card {f : I → Bool // boolWeight f = q} * Fintype.card (O → Bool) := by
      rw [Fintype.card_congr prodEquiv, Fintype.card_prod]
    _ = Nat.choose A.card q * 2 ^ (n - A.card) := by
      rw [boolWeightLayerCard, Fintype.card_fun, Fintype.card_bool, hIcard, hOcard]

def binTransitionSet {k : ℕ} (ell : ℕ) (bin : ℕ → Fin k) : Finset ℕ :=
  (Finset.range ell).filter fun q => bin (q + 1) ≠ bin q

def binTransitionEndpoints {k : ℕ} (ell : ℕ) (bin : ℕ → Fin k) : Finset ℕ :=
  binTransitionSet ell bin ∪ (binTransitionSet ell bin).image Nat.succ

/-- A monotone bin sequence has at most one transition into each value. -/
theorem binTransitionEndpoints_card_le {k ell : ℕ} (bin : ℕ → Fin k)
    (hmono : ∀ a b, a ≤ b → (bin a).val ≤ (bin b).val) :
    (binTransitionEndpoints ell bin).card ≤
      2 * ((Finset.range (ell + 1)).image bin).card := by
  classical
  let T := binTransitionSet ell bin
  have hinj : Set.InjOn (fun q => bin (q + 1)) T := by
    intro q hq r hr heq
    by_contra hqr
    rcases lt_or_gt_of_ne hqr with hqr | hrq
    · have hleft := hmono (q + 1) r (by omega)
      have hright := hmono r (r + 1) (Nat.le_succ _)
      have htransition := (Finset.mem_filter.mp hr).2
      have hval : (bin (q + 1)).val = (bin (r + 1)).val := Fin.ext_iff.mp heq
      have hneq : (bin r).val ≠ (bin (r + 1)).val := by
        intro h
        exact htransition ((Fin.ext h).symm)
      have hstrict : (bin r).val < (bin (r + 1)).val :=
        Nat.lt_of_le_of_ne hright hneq
      have hlt := lt_of_le_of_lt hleft hstrict
      exact (Nat.ne_of_lt hlt) hval
    · have hleft := hmono (r + 1) q (by omega)
      have hright := hmono q (q + 1) (Nat.le_succ _)
      have htransition := (Finset.mem_filter.mp hq).2
      have hval : (bin (q + 1)).val = (bin (r + 1)).val := Fin.ext_iff.mp heq
      have hneq : (bin q).val ≠ (bin (q + 1)).val := by
        intro h
        exact htransition ((Fin.ext h).symm)
      have hstrict : (bin q).val < (bin (q + 1)).val :=
        Nat.lt_of_le_of_ne hright hneq
      have hlt := lt_of_le_of_lt hleft hstrict
      exact (Nat.ne_of_lt hlt) hval.symm
  have hImageSub :
      T.image (fun q => bin (q + 1)) ⊆ (Finset.range (ell + 1)).image bin := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨q, hq, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨q + 1, Finset.mem_range.mpr ?_, rfl⟩
    have hq' := (Finset.mem_filter.mp hq).1
    simp only [Finset.mem_range] at hq'
    omega
  have hTcard : T.card ≤ ((Finset.range (ell + 1)).image bin).card := by
    calc
      T.card = (T.image (fun q => bin (q + 1))).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.range (ell + 1)).image bin).card := Finset.card_le_card hImageSub
  have hEndpoints : (binTransitionEndpoints ell bin).card ≤ 2 * T.card := by
    dsimp [binTransitionEndpoints, T]
    calc
      (binTransitionSet ell bin ∪ (binTransitionSet ell bin).image Nat.succ).card ≤
          (binTransitionSet ell bin).card + ((binTransitionSet ell bin).image Nat.succ).card :=
        Finset.card_union_le _ _
      _ ≤ (binTransitionSet ell bin).card + (binTransitionSet ell bin).card := by
        exact Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * (binTransitionSet ell bin).card := by omega
  exact hEndpoints.trans (Nat.mul_le_mul_left 2 hTcard)

/-- A radius-`r` interval around a value contains at most `2r+1` members of a finite initial segment. -/
theorem finDistFilterCard_le {N r : ℕ} (c : Fin (N + 1)) :
    ((Finset.univ.filter fun x : Fin (N + 1) => Nat.dist x.val c.val ≤ r).card) ≤
      2 * r + 1 := by
  classical
  let S := Finset.univ.filter fun x : Fin (N + 1) => Nat.dist x.val c.val ≤ r
  have himage : S.image Fin.val ⊆ Finset.Icc (c.val - r) (c.val + r) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    have hdist := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_Icc]
    unfold Nat.dist at hdist
    have hx₁ : x.val - c.val ≤ r := by omega
    have hx₂ : c.val - x.val ≤ r := by omega
    constructor <;> omega
  calc
    S.card = (S.image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.Icc (c.val - r) (c.val + r)).card := Finset.card_le_card himage
    _ = c.val + r - (c.val - r) + 1 := by
      simp
      omega
    _ ≤ 2 * r + 1 := by
      by_cases hrc : r ≤ c.val
      · omega
      · have hcr : c.val - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt (lt_of_not_ge hrc))
        rw [hcr]
        omega

/-- A product bound for events on disjoint coordinate blocks of a Boolean cube. -/
theorem cubeBlockEventFraction_le {n m : ℕ}
    (chunks : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (chunks i) (chunks j))
    (S : Finset (Fin m))
    (events : ∀ i, Finset ({a : Fin n // a ∈ chunks i} → Bool))
    (b : ℝ) (hb : 0 ≤ b)
    (hlocal : ∀ i ∈ S,
      ((events i).card : ℝ) ≤ b * (2 : ℝ) ^ (chunks i).card) :
    ((Finset.univ.filter fun x : CubeVertex n =>
      ∀ i ∈ S, (fun a : {a : Fin n // a ∈ chunks i} => x a.1) ∈ events i).card : ℝ) /
        (2 : ℝ) ^ n ≤ b ^ S.card := by
  classical
  let U : Finset (Fin n) := Finset.univ.biUnion chunks
  let Outside := {a : Fin n // a ∉ U}
  let BlockCoord (i : Fin m) := {a : Fin n // a ∈ chunks i}
  let Pattern (i : Fin m) :=
    {f : BlockCoord i → Bool // if i ∈ S then f ∈ events i else True}
  let Config := ((i : Fin m) → Pattern i) × (Outside → Bool)
  let Good (x : CubeVertex n) :=
    ∀ i ∈ S, (fun a : BlockCoord i => x a.1) ∈ events i
  let encode (x : {x : CubeVertex n // Good x}) : Config :=
    ((fun i => ⟨fun a => x.1 a.1, by
      by_cases hi : i ∈ S
      · simpa [hi] using x.2 i hi
      · simp [hi]⟩),
      fun a => x.1 a.1)
  have hPair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint chunks := by
    intro i hi j hj hij
    exact hdisj i j hij
  have hUcard : U.card = ∑ i : Fin m, (chunks i).card := by
    exact Finset.card_biUnion hPair
  have hUle : U.card ≤ n := by
    simpa [U, Fintype.card_fin] using Finset.card_le_univ U
  have hOutsideCard : Fintype.card Outside = n - U.card := by
    have hcompl := Fintype.card_subtype_compl (fun a : Fin n => a ∈ U)
    have hUtype : Fintype.card {a : Fin n // a ∈ U} = U.card := by simp [Fintype.card_coe]
    calc
      Fintype.card Outside = n - Fintype.card {a : Fin n // a ∈ U} := by
        simpa [Outside] using hcompl
      _ = n - U.card := by rw [hUtype]
  have hPatternCard (i : Fin m) :
      Fintype.card (Pattern i) =
        if i ∈ S then (events i).card else 2 ^ (chunks i).card := by
    by_cases hi : i ∈ S
    · simp [Pattern, hi, Fintype.card_coe]
    · simp [Pattern, hi, BlockCoord, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_coe]
  have hEncodeInjective : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext a
    by_cases ha : a ∈ U
    · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
      have hblock : (fun z : BlockCoord i => x.1 z.1) =
          (fun z : BlockCoord i => y.1 z.1) := by
        have hpi : (encode x).1 i = (encode y).1 i :=
          congrFun (congrArg Prod.fst hxy) i
        exact congrArg Subtype.val hpi
      exact congrFun hblock ⟨a, hai⟩
    · have hout : (encode x).2 ⟨a, ha⟩ = (encode y).2 ⟨a, ha⟩ :=
        congrFun (congrArg Prod.snd hxy) ⟨a, ha⟩
      exact hout
  have hGoodCard :
      (Finset.univ.filter fun x : CubeVertex n => Good x).card ≤ Fintype.card Config := by
    calc
      (Finset.univ.filter fun x : CubeVertex n => Good x).card =
          Fintype.card {x : CubeVertex n // Good x} := by
            symm
            simpa using (Fintype.card_subtype Good)
      _ ≤ Fintype.card Config := Fintype.card_le_of_injective encode hEncodeInjective
  have hPatternFactor (i : Fin m) :
      (Fintype.card (Pattern i) : ℝ) ≤
        (if i ∈ S then b else 1) * (2 : ℝ) ^ (chunks i).card := by
    by_cases hi : i ∈ S
    · rw [hPatternCard, if_pos hi]
      simpa [hi] using hlocal i hi
    · rw [hPatternCard, if_neg hi]
      simp [hi]
  have hSprod : (∏ i : Fin m, (if i ∈ S then b else 1)) = b ^ S.card := by
    rw [Finset.prod_ite_mem]
    simp
  have hBlockPow :
      (∏ i : Fin m, (2 : ℝ) ^ (chunks i).card) = (2 : ℝ) ^ U.card := by
    calc
      (∏ i : Fin m, (2 : ℝ) ^ (chunks i).card) =
          (2 : ℝ) ^ (∑ i : Fin m, (chunks i).card) := by
            simpa using
              (Finset.prod_pow_eq_pow_sum (s := Finset.univ)
                (f := fun i : Fin m => (chunks i).card) (a := (2 : ℝ)))
      _ = (2 : ℝ) ^ U.card := by rw [← hUcard]
  have hPatternProd :
      (∏ i : Fin m, (Fintype.card (Pattern i) : ℝ)) ≤
        b ^ S.card * (2 : ℝ) ^ U.card := by
    calc
      (∏ i : Fin m, (Fintype.card (Pattern i) : ℝ)) ≤
          ∏ i : Fin m, ((if i ∈ S then b else 1) * (2 : ℝ) ^ (chunks i).card) :=
          Finset.prod_le_prod₀ (by intro i hi; positivity)
            (by intro i hi; exact hPatternFactor i)
      _ = (∏ i : Fin m, (if i ∈ S then b else 1)) *
            (∏ i : Fin m, (2 : ℝ) ^ (chunks i).card) := Finset.prod_mul_distrib
      _ = b ^ S.card * (2 : ℝ) ^ U.card := by rw [hSprod, hBlockPow]
  have hConfigCard :
      (Fintype.card Config : ℝ) =
        (∏ i : Fin m, (Fintype.card (Pattern i) : ℝ)) *
          (2 : ℝ) ^ (n - U.card) := by
    have hNat : Fintype.card Config =
        (∏ i : Fin m, Fintype.card (Pattern i)) * 2 ^ (n - U.card) := by
      dsimp [Config]
      rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_fun, Fintype.card_bool,
        hOutsideCard]
    rw [hNat]
    simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow, Nat.cast_ofNat]
  have hConfigBound : (Fintype.card Config : ℝ) ≤ b ^ S.card * (2 : ℝ) ^ n := by
    rw [hConfigCard]
    calc
      (∏ i : Fin m, (Fintype.card (Pattern i) : ℝ)) *
          (2 : ℝ) ^ (n - U.card) ≤
        (b ^ S.card * (2 : ℝ) ^ U.card) * (2 : ℝ) ^ (n - U.card) :=
          mul_le_mul_of_nonneg_right hPatternProd (by positivity)
      _ = b ^ S.card * (2 : ℝ) ^ n := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hUle]
  have hGoodReal :
      ((Finset.univ.filter fun x : CubeVertex n => Good x).card : ℝ) ≤
        (Fintype.card Config : ℝ) := by exact_mod_cast hGoodCard
  have hTarget :
      (Fintype.card Config : ℝ) / (2 : ℝ) ^ n ≤ b ^ S.card := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).2
    exact hConfigBound
  calc
    ((Finset.univ.filter fun x : CubeVertex n => Good x).card : ℝ) /
        (2 : ℝ) ^ n ≤ (Fintype.card Config : ℝ) / (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_right hGoodReal (by positivity)
    _ ≤ b ^ S.card := hTarget
private theorem prefixMass_succ (ell j : ℕ) :
    prefixMass ell (j + 1) = prefixMass ell j + halfMassNat ell j := by
  simp [prefixMass, Finset.sum_range_succ]

theorem quantileLabel_properties (ell : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hAtom : ∀ k : Fin (ell + 1), halfBinomialMass ell k ≤ ε) :
    (∀ a b, a ≤ b → quantileLabel ell ε a ≤ quantileLabel ell ε b) ∧
    (∀ a, quantileLabel ell ε (a + 1) ≤ quantileLabel ell ε a + 1) ∧
    (∀ q, quantileLabel ell ε q ≤ Nat.floor (1 / ε)) ∧
    (∀ j, (∑ q ∈ Finset.range (ell + 1),
      if quantileLabel ell ε q = j then (Nat.choose ell q : ℝ) else 0) ≤
        2 * ε * (2 : ℝ) ^ ell) ∧
    (((Finset.range (ell + 1)).image (quantileLabel ell ε)).card : ℝ) ≤ ε⁻¹ + 1 := by
  classical
  let w : Fin (ell + 1) → ℝ := halfBinomialMass ell
  have hw_nonneg (k : Fin (ell + 1)) : 0 ≤ w k := by
    dsimp [w, halfBinomialMass]
    positivity
  have hw_le (k : Fin (ell + 1)) : w k ≤ ε := by
    exact hAtom k
  let wNat : ℕ → ℝ := halfMassNat ell
  have hwNat_nonneg (i : ℕ) : 0 ≤ wNat i := by
    dsimp [wNat, halfMassNat]
    split_ifs with hi
    · exact hw_nonneg _
    · positivity
  have hwNat_le (i : ℕ) (hi : i ≤ ell) : wNat i ≤ ε := by
    have hlt : i < ell + 1 := by omega
    simpa [wNat, halfMassNat, hlt, w] using hw_le (⟨i, hlt⟩ : Fin (ell + 1))
  let cumMass : ℕ → ℝ := prefixMass ell
  have hprefix_nonneg (j : ℕ) : 0 ≤ cumMass j := by
    dsimp [cumMass, prefixMass]
    exact Finset.sum_nonneg fun i hi => hwNat_nonneg i
  have hprefix_mono : Monotone cumMass := by
    intro a b hab
    dsimp [cumMass, prefixMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (by
      intro i hi hnot
      exact hwNat_nonneg i)
  have hprefix_succ (j : ℕ) : cumMass (j + 1) = cumMass j + wNat j := by
    simpa [cumMass, wNat] using prefixMass_succ ell j
  have htotal : cumMass (ell + 1) = 1 := by
    dsimp [cumMass, prefixMass, halfMassNat]
    have hchoose : (∑ i ∈ Finset.range (ell + 1),
        (Nat.choose ell i : ℝ)) = (2 : ℝ) ^ ell := by
      exact_mod_cast Nat.sum_range_choose ell
    have hsum : (∑ i ∈ Finset.range (ell + 1),
        (Nat.choose ell i : ℝ) / (2 : ℝ) ^ ell) = 1 := by
      rw [← Finset.sum_div, hchoose]
      field_simp
    convert hsum using 1
    apply Finset.sum_congr rfl
    intro i hi
    have hlt : i < ell + 1 := Finset.mem_range.mp hi
    simp [hlt, halfBinomialMass]
  have hprefix_bound (j : ℕ) (hj : j ≤ ell + 1) : cumMass j ≤ 1 := by
    calc
      cumMass j ≤ cumMass (ell + 1) := hprefix_mono hj
      _ = 1 := htotal
  have hτ_spec (j : ℕ) :
      (quantileLabel ell ε j : ℝ) ≤ cumMass (min j (ell + 1)) / ε ∧
        cumMass (min j (ell + 1)) / ε < (quantileLabel ell ε j : ℝ) + 1 := by
    have h0 : 0 ≤ cumMass (min j (ell + 1)) / ε :=
      div_nonneg (hprefix_nonneg _) hε.le
    simpa [quantileLabel, cumMass] using (Nat.floor_eq_iff h0).mp rfl
  have hτ_mono : Monotone (quantileLabel ell ε) := by
    intro a b hab
    unfold quantileLabel
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hε.le
    exact hprefix_mono (min_le_min_right _ hab)
  have hτ_step (a : ℕ) : quantileLabel ell ε (a + 1) ≤ quantileLabel ell ε a + 1 := by
    by_cases ha : a < ell + 1
    · have hminA : min a (ell + 1) = a := Nat.min_eq_left (by omega)
      have hminB : min (a + 1) (ell + 1) = a + 1 := Nat.min_eq_left (by omega)
      have hstep := hprefix_succ a
      have hatom := hwNat_le a (by omega)
      have hupper := (hτ_spec a).2
      have hupper0 : cumMass a / ε < (quantileLabel ell ε a : ℝ) + 1 := by
        simpa [hminA] using hupper
      have hupper' : cumMass (a + 1) / ε <
          (quantileLabel ell ε a : ℝ) + 2 := by
        rw [hstep]
        rw [add_div]
        have hdivide : wNat a / ε ≤ 1 := by
          apply (div_le_iff₀ hε).2
          simpa using hatom
        linarith
      have hfloor : (quantileLabel ell ε (a + 1) : ℝ) ≤ cumMass (a + 1) / ε := by
        have hnonneg : 0 ≤ cumMass (a + 1) / ε :=
          div_nonneg (hprefix_nonneg _) hε.le
        have h := Nat.floor_le hnonneg
        simpa [quantileLabel, hminB, cumMass] using h
      have hlt : (quantileLabel ell ε (a + 1) : ℝ) <
          (quantileLabel ell ε a : ℝ) + 2 := by
        exact lt_of_le_of_lt hfloor hupper'
      have hltNat : quantileLabel ell ε (a + 1) < quantileLabel ell ε a + 2 := by
        exact_mod_cast hlt
      omega
    · have hminA : min a (ell + 1) = ell + 1 := Nat.min_eq_right (by omega)
      have hminB : min (a + 1) (ell + 1) = ell + 1 := Nat.min_eq_right (by omega)
      simp [quantileLabel, hminA, hminB]
  have hfiber_mass (j : ℕ) :
      (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
          quantileLabel ell ε k.val = j), halfBinomialMass ell k) ≤ 2 * ε := by
    let fiber : Finset (Fin (ell + 1)) :=
      Finset.univ.filter fun k => quantileLabel ell ε k.val = j
    by_cases hempty : fiber.Nonempty
    · let a := fiber.min' hempty
      let b := fiber.max' hempty
      have ha : a ∈ fiber := Finset.min'_mem _ _
      have hb : b ∈ fiber := Finset.max'_mem _ _
      have hta : quantileLabel ell ε a.val = j := (Finset.mem_filter.mp ha).2
      have htb : quantileLabel ell ε b.val = j := (Finset.mem_filter.mp hb).2
      have hab : a.val ≤ b.val := by
        exact_mod_cast Finset.min'_le fiber b hb
      have hfiber_interval (k : Fin (ell + 1)) : k ∈ fiber ↔
          a.val ≤ k.val ∧ k.val ≤ b.val := by
        constructor
        · intro hk
          exact ⟨by exact_mod_cast Finset.min'_le fiber k hk,
            by exact_mod_cast Finset.le_max' fiber k hk⟩
        · intro hk
          have hleft := hτ_mono hk.1
          have hright := hτ_mono hk.2
          rw [hta] at hleft
          rw [htb] at hright
          have htag : quantileLabel ell ε k.val = j := Nat.le_antisymm hright hleft
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htag⟩
      have hmassEq : (∑ k ∈ fiber, halfBinomialMass ell k) =
          cumMass (b.val + 1) - cumMass a.val := by
        rw [show fiber = Finset.univ.filter (fun k : Fin (ell + 1) =>
            a.val ≤ k.val ∧ k.val ≤ b.val) by
              ext k
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact hfiber_interval k]
        have hbij :
            (∑ k ∈ (Finset.univ.filter (fun k : Fin (ell + 1) =>
                a.val ≤ k.val ∧ k.val ≤ b.val)), halfBinomialMass ell k) =
              ∑ i ∈ Finset.Icc a.val b.val, wNat i := by
          apply Finset.sum_bij (fun k _ => k.val)
          · intro k hk
            exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hk).2
          · intro k₁ hk₁ k₂ hk₂ heq
            exact Fin.ext heq
          · intro i hi
            let k : Fin (ell + 1) := ⟨i, by
              have := Finset.mem_Icc.mp hi
              omega⟩
            refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.mem_Icc.mp hi⟩, ?_⟩
            rfl
          · intro k hk
            dsimp [wNat, halfMassNat]
            have hlt : k.val < ell + 1 := k.isLt
            simp [hlt, halfBinomialMass]
        rw [hbij]
        have hIco : Finset.Ico a.val (b.val + 1) = Finset.Icc a.val b.val := by
          ext i
          simp [Finset.mem_Ico, Finset.mem_Icc]
        have hsumIco : (∑ i ∈ Finset.Icc a.val b.val, wNat i) =
            (∑ i ∈ Finset.range (b.val + 1), wNat i) -
              (∑ i ∈ Finset.range a.val, wNat i) := by
          rw [← hIco]
          exact Finset.sum_Ico_eq_sub _ (by omega)
        simpa [cumMass, prefixMass] using hsumIco
      have hlow := (hτ_spec a.val).1
      have hupp := (hτ_spec b.val).2
      have hlow' : (j : ℝ) * ε ≤ cumMass a.val := by
        have hmin : min a.val (ell + 1) = a.val := Nat.min_eq_left (by omega)
        rw [hta, hmin] at hlow
        exact (le_div_iff₀ hε).mp hlow
      have hupp' : cumMass b.val < ((j : ℝ) + 1) * ε := by
        have hmin : min b.val (ell + 1) = b.val := Nat.min_eq_left (by omega)
        rw [htb, hmin] at hupp
        exact (div_lt_iff₀ hε).mp hupp
      have hstep : cumMass (b.val + 1) ≤ cumMass b.val + ε := by
        rw [hprefix_succ]
        nlinarith [hwNat_le b.val (by omega)]
      rw [hmassEq]
      linarith
    · have hfiber : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simp [fiber, hfiber]
      positivity
  have htotal_range (j : ℕ) : (∑ k ∈ Finset.range (ell + 1),
      if quantileLabel ell ε k = j then (Nat.choose ell k : ℝ) else 0) =
      (2 : ℝ) ^ ell *
        (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
          quantileLabel ell ε k.val = j), halfBinomialMass ell k) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun q : ℕ => if quantileLabel ell ε q = j then (Nat.choose ell q : ℝ) else 0)
      (ell + 1)]
    calc
      (∑ k : Fin (ell + 1),
          if quantileLabel ell ε k.val = j then (Nat.choose ell k.val : ℝ) else 0) =
          ∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
            quantileLabel ell ε k.val = j), (Nat.choose ell k.val : ℝ) := by
              rw [Finset.sum_filter]
      _ = (2 : ℝ) ^ ell *
          (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
            quantileLabel ell ε k.val = j), halfBinomialMass ell k) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              simp only [halfBinomialMass]
              field_simp
  have hbinom : ∀ j, (∑ q ∈ Finset.range (ell + 1),
      if quantileLabel ell ε q = j then (Nat.choose ell q : ℝ) else 0) ≤
        2 * ε * (2 : ℝ) ^ ell := by
    intro j
    rw [htotal_range j]
    calc
      (2 : ℝ) ^ ell *
          (∑ k ∈ (Finset.univ.filter fun k : Fin (ell + 1) =>
            quantileLabel ell ε k.val = j), halfBinomialMass ell k) ≤
        (2 : ℝ) ^ ell * (2 * ε) :=
          mul_le_mul_of_nonneg_left (hfiber_mass j) (by positivity)
      _ = 2 * ε * (2 : ℝ) ^ ell := by ring
  have hτ_bound (k : Fin (ell + 1)) :
      quantileLabel ell ε k.val ≤ Nat.floor (1 / ε) := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hε.le
    have hmin : min k.val (ell + 1) = k.val := Nat.min_eq_left (by omega)
    rw [hmin]
    exact hprefix_bound k.val (by omega)
  have hτ_bound_all (q : ℕ) : quantileLabel ell ε q ≤ Nat.floor (1 / ε) := by
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hε.le
    exact hprefix_bound (min q (ell + 1)) (min_le_right _ _)
  have htags : (Finset.range (ell + 1)).image (quantileLabel ell ε) ⊆
      Finset.range (Nat.floor (1 / ε) + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨k, hk, rfl⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hτ_bound ⟨k, Finset.mem_range.mp hk⟩)
  have hcount : ((Finset.range (ell + 1)).image (quantileLabel ell ε)).card ≤
      Nat.floor (1 / ε) + 1 := by
    calc
      ((Finset.range (ell + 1)).image (quantileLabel ell ε)).card ≤
          (Finset.range (Nat.floor (1 / ε) + 1)).card := Finset.card_le_card htags
      _ = Nat.floor (1 / ε) + 1 := by simp
  refine ⟨hτ_mono, hτ_step, hτ_bound_all, hbinom, ?_⟩
  calc
    (((Finset.range (ell + 1)).image (quantileLabel ell ε)).card : ℝ) ≤
        (Nat.floor (1 / ε) + 1 : ℝ) := by exact_mod_cast hcount
    _ = (Nat.floor (1 / ε) : ℝ) + 1 := by norm_cast
    _ ≤ ε⁻¹ + 1 := by
      have hf := Nat.floor_le (show 0 ≤ (1 : ℝ) / ε by positivity)
      simpa [one_div] using add_le_add_right hf (1 : ℝ)

end

end HypercubeRamsey.Lane_q_s06_front
