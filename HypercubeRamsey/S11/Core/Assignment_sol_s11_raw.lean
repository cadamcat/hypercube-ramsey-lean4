import HypercubeRamsey.S11.Core.Assignment_q_s11_tags

namespace HypercubeRamsey.Lane_sol_s11_raw

open HypercubeRamsey.S11.Core HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

private def pairFlip {n : ℕ} (v : CubeVertex n) (S : Finset (Fin n)) : CubeVertex n :=
  fun j => if j ∈ S then !v j else v j

private noncomputable def pairRole {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n)) : EvenRole n := by
  classical
  let S : Finset (Fin n) := P.1.image Subtype.val
  let hpair : ∃ a b : InnerCoord n, a ≠ b ∧ P.1 = {a, b} :=
    Finset.card_eq_two.mp P.2
  let a : InnerCoord n := Classical.choose hpair
  let b : InnerCoord n := Classical.choose (Classical.choose_spec hpair)
  have hab : a ≠ b := (Classical.choose_spec (Classical.choose_spec hpair)).1
  have hP : P.1 = {a, b} := (Classical.choose_spec (Classical.choose_spec hpair)).2
  have hS : S = {a.1, b.1} := by
    simp [S, hP]
  have hne : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  have hflip : pairFlip v.1 S = cubeFlip (cubeFlip v.1 a.1) b.1 := by
    funext j
    by_cases hja : j = a.1
    · subst j
      simp [pairFlip, S, hS, cubeFlip, Function.update_of_ne hne]
    · by_cases hjb : j = b.1
      · subst j
        simp [pairFlip, S, hS, cubeFlip, Function.update_of_ne (Ne.symm hne)]
      · simp_all [pairFlip, S, hS, cubeFlip,
          Function.update_of_ne hja, Function.update_of_ne hjb]
  refine ⟨pairFlip v.1 S, ?_⟩
  rw [hflip]
  have hfirst : ¬ IsEvenRole (cubeFlip v.1 a.1) := by
    intro he
    exact (cubeFlip_parity v.1 a.1).mp he v.2
  exact (cubeFlip_parity (cubeFlip v.1 a.1) b.1).mpr hfirst

private theorem pairRole_slice {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n)) :
    sliceOf (pairRole v P).1 = sliceOf v.1 := by
  classical
  funext j
  have hnot : j.1 ∉ P.1.image Subtype.val := by
    intro hj
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hj
    have hlt := a.2
    have hval : a.1 = j.1 := hEq
    omega
  simp [sliceOf, pairRole, pairFlip, hnot]

private theorem pairRole_support {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n)) :
    Finset.univ.filter (fun j : Fin n => v.1 j ≠ (pairRole v P).1 j) =
      P.1.image Subtype.val := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (v.1 j ≠ pairFlip v.1 (P.1.image Subtype.val) j) ↔
    j ∈ P.1.image Subtype.val
  by_cases hj : j ∈ P.1.image Subtype.val
  · have hflip : pairFlip v.1 (P.1.image Subtype.val) j = !v.1 j := by
      simp [pairFlip, hj]
    rw [hflip]
    constructor
    · intro _
      exact hj
    · intro _
      cases hv : v.1 j <;> simp [hv]
  · have hsame : pairFlip v.1 (P.1.image Subtype.val) j = v.1 j := by
      simp [pairFlip, hj]
    rw [hsame]
    constructor
    · intro h
      exact (h rfl).elim
    · intro h
      exact (hj h).elim

private noncomputable def localEvenRole {n : ℕ} (v : EvenRole n)
    (o : Option (Pair (InnerCoord n))) : EvenRole n :=
  match o with
  | none => v
  | some P => pairRole v P

private theorem pairFlip_pair {n : ℕ} (v : CubeVertex n) (a b : Fin n) (hab : a ≠ b) :
    pairFlip v {a, b} = cubeFlip (cubeFlip v a) b := by
  funext j
  by_cases hja : j = a
  · subst j
    simp [pairFlip, cubeFlip, Function.update_of_ne hab]
  · by_cases hjb : j = b
    · subst j
      simp [pairFlip, cubeFlip, Function.update_of_ne (Ne.symm hab)]
    · simp_all [pairFlip, cubeFlip, Function.update_of_ne hja, Function.update_of_ne hjb]

private theorem pairRole_eq_flip {n : ℕ} (v : EvenRole n) (P : Pair (InnerCoord n))
    (a b : InnerCoord n) (hab : a ≠ b) (hP : P.1 = {a, b}) :
    pairRole v P = evenNbr (oddNbr v a.1) b.1 := by
  apply Subtype.ext
  change pairFlip v.1 (P.1.image Subtype.val) = cubeFlip (cubeFlip v.1 a.1) b.1
  have himage : P.1.image Subtype.val = {a.1, b.1} := by simp [hP, hab]
  rw [himage]
  exact pairFlip_pair v.1 a.1 b.1 (by intro h; exact hab (Subtype.ext h))

private theorem localEvenRole_pair {n : ℕ} (v : EvenRole n) (a c : InnerCoord n)
    (hca : c ≠ a) :
    localEvenRole v (some ⟨{a, c}, Finset.card_pair (Ne.symm hca)⟩) =
      evenNbr (oddNbr v a.1) c.1 := by
  exact pairRole_eq_flip v _ a c (Ne.symm hca) rfl

private theorem localEvenRole_slice {n : ℕ} (v : EvenRole n)
    (o : Option (Pair (InnerCoord n))) :
    sliceOf (localEvenRole v o).1 = sliceOf v.1 := by
  cases o with
  | none => rfl
  | some P => exact pairRole_slice v P

private theorem innerFlip_slice {n : ℕ} (v : CubeVertex n) (a : InnerCoord n) :
    sliceOf (cubeFlip v a.1) = sliceOf v := by
  funext j
  have hne : a.1 ≠ j.1 := by
    intro heq
    have hlt := a.2
    have hge := j.2
    rw [heq] at hlt
    omega
  change Function.update v a.1 (!v a.1) j.1 = v j.1
  exact Function.update_of_ne (Ne.symm hne) _ _

private theorem outerFlip_slice {n : ℕ} (v : CubeVertex n) (j : OuterCoord n) :
    sliceOf (cubeFlip v j.1) = flipOuter (sliceOf v) j := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [sliceOf, cubeFlip, flipOuter]
  · have hne : j.1 ≠ k.1 := by
      intro heq
      exact hkj (Subtype.ext heq.symm)
    change Function.update v j.1 (!v j.1) k.1 =
      Function.update (sliceOf v) j (!v j.1) k
    rw [Function.update_of_ne (Ne.symm hne), Function.update_of_ne hkj]
    rfl

private theorem flipOuter_ne_self {n : ℕ} (s : OuterWord n) (j : OuterCoord n) :
    flipOuter s j ≠ s := by
  intro h
  have hj := congrFun h j
  simp [flipOuter] at hj

private theorem flipOuter_ne_of_ne {n : ℕ} (s : OuterWord n) (j k : OuterCoord n) (hjk : j ≠ k) :
    flipOuter s j ≠ flipOuter s k := by
  intro h
  have hj := congrFun h j
  simp [flipOuter, hjk] at hj

private theorem oddNbr_inner_slice {n : ℕ} (v : EvenRole n) (a : InnerCoord n) :
    sliceOf (oddNbr v a.1).1 = sliceOf v.1 := innerFlip_slice v.1 a

private theorem evenNbr_inner_slice {n : ℕ} (b : OddRole n) (a : InnerCoord n) :
    sliceOf (evenNbr b a.1).1 = sliceOf b.1 := innerFlip_slice b.1 a

private theorem oddNbr_outer_slice {n : ℕ} (v : EvenRole n) (j : OuterCoord n) :
    sliceOf (oddNbr v j.1).1 = flipOuter (sliceOf v.1) j := outerFlip_slice v.1 j

private theorem innerStarOf {n k N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (v : EvenRole n) (W : EvenRole n → Fin k → Fin N) (a : InnerCoord n) :
    starOf W (oddNbr v a.1) = ballStar (fun o => W (localEvenRole v o)) a := by
  funext c
  by_cases hc : c = a
  · subst c
    simp [starOf, oddNbr, evenNbr, localEvenRole, ballStar, cubeFlip]
  · have hpair := localEvenRole_pair v a c hc
    have hpair' : pairRole v ⟨{a, c}, Finset.card_pair (Ne.symm hc)⟩ =
        evenNbr (oddNbr v a.1) c.1 := by
      simpa [localEvenRole] using hpair
    simp only [starOf, oddNbr, evenNbr, ballStar, localEvenRole, dif_neg hc]
    exact (congrArg W hpair').symm

private noncomputable def oddStarScope {n : ℕ} (v : EvenRole n) : Option (OuterCoord n) → Finset (OddRole n)
  | none => Finset.univ.image fun a : InnerCoord n => oddNbr v a.1
  | some j => {oddNbr v j.1}

private noncomputable def evenStarScope {n : ℕ} (v : EvenRole n) :
    Option (OuterCoord n) → Finset (EvenRole n)
  | none => Finset.univ.image (localEvenRole v)
  | some j => Finset.univ.image fun a : InnerCoord n => evenNbr (oddNbr v j.1) a.1

private theorem oddScope_none_some_disjoint {n : ℕ} (v : EvenRole n) (j : OuterCoord n) :
    Disjoint (oddStarScope v none) (oddStarScope v (some j)) := by
  apply Finset.disjoint_left.mpr
  intro b hb₁ hb₂
  obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hb₁
  have hSingle : b = oddNbr v j.1 := Finset.mem_singleton.mp hb₂
  have hroles : oddNbr v a.1 = oddNbr v j.1 := hEq.trans hSingle
  have hs := congrArg (fun b : OddRole n => sliceOf b.1) hroles
  rw [oddNbr_inner_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_self (sliceOf v.1) j) hs.symm

private theorem oddScope_some_some_disjoint {n : ℕ} (v : EvenRole n) (j k : OuterCoord n)
    (hjk : j ≠ k) : Disjoint (oddStarScope v (some j)) (oddStarScope v (some k)) := by
  apply Finset.disjoint_left.mpr
  intro b hb₁ hb₂
  have hroles : oddNbr v j.1 = oddNbr v k.1 :=
    (Finset.mem_singleton.mp hb₁).symm.trans (Finset.mem_singleton.mp hb₂)
  have hs := congrArg (fun b : OddRole n => sliceOf b.1) hroles
  rw [oddNbr_outer_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_of_ne (sliceOf v.1) j k hjk) hs

private theorem oddScope_disjoint {n : ℕ} (v : EvenRole n) {o o' : Option (OuterCoord n)}
    (hoo' : o ≠ o') : Disjoint (oddStarScope v o) (oddStarScope v o') := by
  cases o with
  | none =>
    cases o' with
    | none => exact (hoo' rfl).elim
    | some j => exact oddScope_none_some_disjoint v j
  | some j =>
    cases o' with
    | none => exact disjoint_comm.mp (oddScope_none_some_disjoint v j)
    | some k =>
      have hjk : j ≠ k := by
        intro h
        exact hoo' (congrArg Option.some h)
      exact oddScope_some_some_disjoint v j k hjk

private theorem evenScope_none_some_disjoint {n : ℕ} (v : EvenRole n) (j : OuterCoord n) :
    Disjoint (evenStarScope v none) (evenStarScope v (some j)) := by
  apply Finset.disjoint_left.mpr
  intro u hu₁ hu₂
  obtain ⟨o, ho, hEq⟩ := Finset.mem_image.mp hu₁
  obtain ⟨a, ha, hEq'⟩ := Finset.mem_image.mp hu₂
  have huEq : localEvenRole v o = evenNbr (oddNbr v j.1) a.1 := hEq.trans hEq'.symm
  have hs := congrArg (fun u : EvenRole n => sliceOf u.1) huEq
  rw [localEvenRole_slice, evenNbr_inner_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_self (sliceOf v.1) j) hs.symm

private theorem evenScope_some_some_disjoint {n : ℕ} (v : EvenRole n) (j k : OuterCoord n)
    (hjk : j ≠ k) : Disjoint (evenStarScope v (some j)) (evenStarScope v (some k)) := by
  apply Finset.disjoint_left.mpr
  intro u hu₁ hu₂
  obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hu₁
  obtain ⟨b, hb, hEq'⟩ := Finset.mem_image.mp hu₂
  have hs := congrArg (fun u : EvenRole n => sliceOf u.1) (hEq.trans hEq'.symm)
  rw [evenNbr_inner_slice, oddNbr_outer_slice, evenNbr_inner_slice, oddNbr_outer_slice] at hs
  exact (flipOuter_ne_of_ne (sliceOf v.1) j k hjk) hs

private theorem evenScope_disjoint {n : ℕ} (v : EvenRole n) {o o' : Option (OuterCoord n)}
    (hoo' : o ≠ o') : Disjoint (evenStarScope v o) (evenStarScope v o') := by
  cases o with
  | none =>
    cases o' with
    | none => exact (hoo' rfl).elim
    | some j => exact evenScope_none_some_disjoint v j
  | some j =>
    cases o' with
    | none => exact disjoint_comm.mp (evenScope_none_some_disjoint v j)
    | some k =>
      have hjk : j ≠ k := by
        intro h
        exact hoo' (congrArg Option.some h)
      exact evenScope_some_some_disjoint v j k hjk


private theorem localEvenRole_injective {n : ℕ} (v : EvenRole n) :
    Function.Injective (localEvenRole v) := by
  classical
  intro o₁ o₂ h
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some P =>
      have hv : v.1 = (pairRole v P).1 := congrArg Subtype.val h
      have hempty :
          Finset.univ.filter (fun j : Fin n => v.1 j ≠ (pairRole v P).1 j) = ∅ := by
        simp [hv]
      rw [pairRole_support] at hempty
      have hpos : 0 < P.1.card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have hmem : a.1 ∈ P.1.image Subtype.val := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      rw [hempty] at hmem
      simp at hmem
  | some P =>
    cases o₂ with
    | none =>
      have hv : (pairRole v P).1 = v.1 := congrArg Subtype.val h
      have hempty :
          Finset.univ.filter (fun j : Fin n => v.1 j ≠ (pairRole v P).1 j) = ∅ := by
        simp [hv]
      rw [pairRole_support] at hempty
      have hpos : 0 < P.1.card := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
      have hmem : a.1 ∈ P.1.image Subtype.val := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      rw [hempty] at hmem
      simp at hmem
    | some Q =>
      have hroles : pairRole v P = pairRole v Q := h
      have hsets : P.1.image Subtype.val = Q.1.image Subtype.val := by
        have hh := congrArg (fun z : EvenRole n =>
          Finset.univ.filter (fun j : Fin n => v.1 j ≠ z.1 j)) hroles
        rw [pairRole_support, pairRole_support] at hh
        exact hh
      have hpq : P.1 = Q.1 := by
        apply Finset.ext
        intro a
        constructor
        · intro ha
          have hmem : a.1 ∈ Q.1.image Subtype.val := by
            rw [← hsets]
            exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
          obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
          have heq : a = b := Subtype.ext hba.symm
          simpa [heq] using hb
        · intro ha
          have hmem : a.1 ∈ P.1.image Subtype.val := by
            rw [hsets]
            exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
          obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
          have heq : a = b := Subtype.ext hba.symm
          simpa [heq] using hb
      exact congrArg some (Subtype.ext hpq)


private theorem pi_expect_prod_of_disjoint
    {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (F : I → (∀ i, Ω i) → ℝ) (S : I → Finset ι)
    (hdep : ∀ i, FinProb.DependsOn (F i) (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    (FinProb.pi P).expect (fun ω => ∏ i, F i ω) =
      ∏ i, (FinProb.pi P).expect (F i) := by
  classical
  let law : FinProb (∀ i, Ω i) := FinProb.pi P
  let prodOn (T : Finset I) (ω : ∀ i, Ω i) : ℝ := ∏ i ∈ T, F i ω
  have hFor : ∀ T : Finset I,
      law.expect (prodOn T) = ∏ i ∈ T, law.expect (F i) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp [prodOn, law, FinProb.expect, (FinProb.pi P).sum_eq_one]
    | @insert i T hi ih =>
      let scopeT : Finset ι := T.biUnion S
      have hdepT : FinProb.DependsOn (prodOn T) scopeT := by
        intro ω ω' hω
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j ω ω'
        intro k hk
        exact hω k (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩)
      have hscoped : Disjoint (S i) scopeT := by
        apply Finset.disjoint_left.mpr
        intro u hu huT
        obtain ⟨j, hj, huJ⟩ := Finset.mem_biUnion.mp huT
        have hij : i ≠ j := by
          intro heq
          subst j
          exact hi hj
        exact Finset.disjoint_left.mp (hdisj i j hij) hu huJ
      have hmul := FinProb.pi_expect_mul_of_disjoint P (F i) (prodOn T)
        (S i) scopeT (hdep i) hdepT hscoped
      have hprod (ω : ∀ i, Ω i) : prodOn (insert i T) ω = F i ω * prodOn T ω := by
        simp [prodOn, hi]
      calc
        law.expect (prodOn (insert i T)) = law.expect (fun ω => F i ω * prodOn T ω) := by
          congr 1
          funext ω
          exact hprod ω
        _ = law.expect (F i) * law.expect (prodOn T) := hmul
        _ = law.expect (F i) * ∏ j ∈ T, law.expect (F j) := by rw [ih]
        _ = ∏ j ∈ insert i T, law.expect (F j) := by simp [hi]
  simpa [law, prodOn] using hFor (Finset.univ : Finset I)


private theorem pi_expect_injective
    {ι J Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    [Fintype Ω] (P : ι → FinProb Ω) (η : J → ι) (hη : Function.Injective η)
    (G : (J → Ω) → ℝ) :
    (FinProb.pi P).expect (fun ω => G (fun j => ω (η j))) =
      (FinProb.pi (fun j => P (η j))).expect G := by
  classical
  let U : Finset ι := Finset.univ.image η
  let ηU : J → {u // u ∈ U} := fun j =>
    ⟨η j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a b hab
      exact hη (congrArg Subtype.val hab)
    · intro u
      obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp u.2
      exact ⟨j, Subtype.ext hEq⟩
  let e : J ≃ {u // u ∈ U} := Equiv.ofBijective ηU hηU
  let H (o : {u // u ∈ U} → Ω) : ℝ := G (fun j => o (ηU j))
  let ePi : (J → Ω) ≃ ({u // u ∈ U} → Ω) := {
    toFun := fun z u => z (e.symm u)
    invFun := fun z j => z (e j)
    left_inv := by intro z; funext j; simp
    right_inv := by intro z; funext u; simp }
  have hchange :
      (FinProb.pi (fun u : {u // u ∈ U} => P u.1)).expect H =
        (FinProb.pi (fun j => P (η j))).expect G := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro z hz
    have hprod' :
        (∏ j : J, (P (e j).1).w (ePi z (e j))) =
          ∏ u : {u // u ∈ U}, (P u.1).w (ePi z u) :=
      Fintype.prod_equiv e _ _ (by intro j; simp [ePi])
    have hprod :
        (∏ u : {u // u ∈ U}, (P u.1).w (ePi z u)) =
          ∏ j : J, (P (η j)).w (z j) := by
      simpa [e, ηU, ePi] using hprod'.symm
    have heval : H (ePi z) = G z := by simp [H, ePi, ηU, e]
    simpa only [FinProb.pi, hprod, heval]
  exact (FinProb.pi_marginal_expect P U H).trans hchange

private theorem oddNbr_injective {n : ℕ} (v : EvenRole n) :
    Function.Injective (oddNbr v) := by
  intro j k hjk
  by_contra hne
  have hcoord := congrFun (congrArg Subtype.val hjk) j
  cases hv : v.1 j <;> simp [oddNbr, cubeFlip, hv, Function.update_of_ne hne] at hcoord

private def joinedCoord {n : ℕ} : InnerCoord n ⊕ OuterCoord n → Fin n := Sum.elim Subtype.val Subtype.val

private theorem joinedCoord_injective {n : ℕ} :
    Function.Injective (@joinedCoord n) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext hab)
    | inr b => have ha := a.2; have hb := b.2; change a.1 = b.1 at hab; rw [hab] at ha; omega
  | inr a =>
    cases b with
    | inl b => have ha := a.2; have hb := b.2; change a.1 = b.1 at hab; rw [hab] at ha; omega
    | inr b => exact congrArg Sum.inr (Subtype.ext hab)

private theorem output_sum {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (t : OuterWord n → M.ι) (v : EvenRole n) (hS : SliceFacts M y₀)
    (W : EvenRole n → Fin (kTup n) → Fin N)
    (G : (InnerCoord n → Fin N) → (OuterCoord n → Fin N) → ℝ) :
    (∑ f, oddProdW M t W f * G (innerOut f v) (fun j => f (oddNbr v j.1))) =
      ∑ z : InnerCoord n → Fin N, ∑ y : OuterCoord n → Fin N,
        ((∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
          ∏ j, oddRowF M t W (oddNbr v j.1) (y j)) * G z y := by
  classical
  let Q (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b) }
  let η : InnerCoord n ⊕ OuterCoord n → OddRole n := fun j => oddNbr v (joinedCoord j)
  let H (u : InnerCoord n ⊕ OuterCoord n → Fin N) := G (fun a => u (.inl a)) (fun j => u (.inr j))
  have h := pi_expect_injective Q η ((oddNbr_injective v).comp joinedCoord_injective) H
  let e := Equiv.sumArrowEquivProdArrow (InnerCoord n) (OuterCoord n) (Fin N)
  calc
    _ = (FinProb.pi (fun j => Q (η j))).expect H := h
    _ = ∑ zy : (InnerCoord n → Fin N) × (OuterCoord n → Fin N),
        ((∏ a, oddRowF M t W (oddNbr v a.1) (zy.1 a)) *
          ∏ j, oddRowF M t W (oddNbr v j.1) (zy.2 j)) * G zy.1 zy.2 := by
      unfold FinProb.expect
      rw [← Equiv.sum_comp e.symm]
      apply Finset.sum_congr rfl
      intro zy hzy
      rcases zy with ⟨z, y⟩
      simp [FinProb.pi, Fintype.prod_sum_type, Q, η, joinedCoord, H, e, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
        Equiv.sumArrowEquivProdArrow_symm_apply_inr]
    _ = _ := Fintype.sum_prod_type _

private noncomputable def innerWeight {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (i : M.ι) (z : InnerCoord n → Fin N) : ℝ :=
  ∑ V : Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N,
    ballW E M.G (M.μ i) (y₀ i) V * outW E M.G (gS n) (M.μ i) (M.ν i) V z

private theorem inner_mean {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (t : OuterWord n → M.ι) (v : EvenRole n) (z : InnerCoord n → Fin N) :
    (rawTuples M y₀ t).expect (fun W => ∏ a, oddRowF M t W (oddNbr v a.1) (z a)) =
      innerWeight M y₀ (t (sliceOf v.1)) z := by
  classical
  let Q (u : EvenRole n) :=
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let H (V : Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) :=
    outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1))) V z
  have hpoint (W : EvenRole n → Fin (kTup n) → Fin N) :
      (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) = H (fun o => W (localEvenRole v o)) := by
    unfold H outW
    apply Finset.prod_congr rfl
    intro a ha
    unfold oddRowF
    rw [oddNbr_inner_slice, innerStarOf M v W a]
  have h := pi_expect_injective Q (localEvenRole v) (localEvenRole_injective v) H
  calc
    _ = (FinProb.pi Q).expect (fun W => H (fun o => W (localEvenRole v o))) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro W hW
      change (FinProb.pi Q).w W * (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) =
        (FinProb.pi Q).w W * H (fun o => W (localEvenRole v o))
      rw [hpoint]
    _ = (FinProb.pi (fun o => Q (localEvenRole v o))).expect H := h
    _ = _ := by
      simp [FinProb.pi, FinProb.expect, Q, H, localEvenRole_slice, innerWeight, ballW, tupW, tupLaw]

private theorem tuple_neighbor_mean {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (t : OuterWord n → M.ι) (v : EvenRole n)
    (z : InnerCoord n → Fin N) (y : OuterCoord n → Fin N) :
    (rawTuples M y₀ t).expect (fun W =>
      (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
        ∏ j, oddRowF M t W (oddNbr v j.1) (y j)) =
      innerWeight M y₀ (t (sliceOf v.1)) z *
        ∏ j, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) (y j) := by
  classical
  let Q (u : EvenRole n) :=
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let F : Option (OuterCoord n) → (EvenRole n → Fin (kTup n) → Fin N) → ℝ
    | none, W => ∏ a, oddRowF M t W (oddNbr v a.1) (z a)
    | some j, W => oddRowF M t W (oddNbr v j.1) (y j)
  have hdep (o : Option (OuterCoord n)) : FinProb.DependsOn (F o) (evenStarScope v o) := by
    cases o with
    | none =>
      intro W W' hWW
      apply Finset.prod_congr rfl
      intro a ha
      have hlocal : (fun o => W (localEvenRole v o)) = fun o => W' (localEvenRole v o) := by
        funext o
        exact hWW _ (Finset.mem_image.mpr ⟨o, Finset.mem_univ _, rfl⟩)
      have hstar : starOf W (oddNbr v a.1) = starOf W' (oddNbr v a.1) := by
        rw [innerStarOf M v W a, innerStarOf M v W' a, hlocal]
      simp [oddRowF, hstar]
    | some j =>
      intro W W' hWW
      have hstar : starOf W (oddNbr v j.1) = starOf W' (oddNbr v j.1) := by
        funext a
        exact hWW _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
      simp [F, oddRowF, hstar]
  have h := pi_expect_prod_of_disjoint Q F (evenStarScope v) hdep
    (fun _ _ hne => evenScope_disjoint v hne)
  calc
    _ = (FinProb.pi Q).expect (fun W => ∏ o, F o W) := by
      congr 1
      funext W
      simp [F, Fintype.prod_option]
    _ = ∏ o, (FinProb.pi Q).expect (F o) := h
    _ = _ := by
      rw [Fintype.prod_option]
      change (rawTuples M y₀ t).expect (fun W => ∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
        (∏ j, (rawTuples M y₀ t).expect (fun W => oddRowF M t W (oddNbr v j.1) (y j))) = _
      rw [inner_mean M y₀ t v z]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [HypercubeRamsey.Lane_q_s11_tags.raw_oddRow_mean, oddNbr_outer_slice]

private theorem expect_sum {Ω J : Type*} [Fintype Ω] [Fintype J]
    (P : FinProb Ω) (F : J → Ω → ℝ) :
    P.expect (fun ω => ∑ j, F j ω) = ∑ j, P.expect (F j) := by
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem expect_mul_const {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (F : Ω → ℝ) (c : ℝ) :
    P.expect (fun ω => F ω * c) = P.expect F * c := by
  simp [FinProb.expect, mul_assoc, Finset.sum_mul]

private theorem rawFail_sum {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (v : EvenRole n) (hS : SliceFacts M y₀) :
    rawFail M y₀ p t v =
      ∑ z : InnerCoord n → Fin N, ∑ y : OuterCoord n → Fin N,
        (innerWeight M y₀ (t (sliceOf v.1)) z *
          ∏ j, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) (y j)) *
        (if outerZ E M.G (piBar M y₀ p)
          (sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z) y < 1/2 then 1 else 0) := by
  classical
  let G (z : InnerCoord n → Fin N) (y : OuterCoord n → Fin N) : ℝ :=
    if outerZ E M.G (piBar M y₀ p) (sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z) y < 1/2
      then 1 else 0
  have hpoint (W : EvenRole n → Fin (kTup n) → Fin N) :
      massFailGiven M y₀ p t W v =
        ∑ z : InnerCoord n → Fin N, ∑ y : OuterCoord n → Fin N,
          ((∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
            ∏ j, oddRowF M t W (oddNbr v j.1) (y j)) * G z y := by
    unfold massFailGiven
    simp_rw [HypercubeRamsey.Lane_q_s11_tags.MassFail_iff_outerZ]
    exact output_sum M y₀ t v hS W G
  unfold rawFail
  simp_rw [hpoint, expect_sum, expect_mul_const, tuple_neighbor_mean]
  rfl

private def tagCoord {n : ℕ} (v : EvenRole n) : Option (OuterCoord n) → OuterWord n
  | none => sliceOf v.1
  | some j => flipOuter (sliceOf v.1) j

private theorem tagCoord_injective {n : ℕ} (v : EvenRole n) :
    Function.Injective (tagCoord v) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some j => exact ((flipOuter_ne_self (sliceOf v.1) j) hab.symm).elim
  | some j =>
    cases b with
    | none => exact ((flipOuter_ne_self (sliceOf v.1) j) hab).elim
    | some k =>
      congr 1
      by_contra hne
      exact flipOuter_ne_of_ne (sliceOf v.1) j k hne hab

private theorem tag_integrand_mean {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (v : EvenRole n) (A : M.ι → ℝ) (y : OuterCoord n → Fin N) :
    (rawTags M p).expect (fun t => A (t (sliceOf v.1)) *
      ∏ j, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) (y j)) =
      (∑ i, p.w i * A i) * ∏ j, piBar M y₀ p (y j) := by
  classical
  let F : Option (OuterCoord n) → M.ι → ℝ
    | none => A
    | some j => fun i => piRow M y₀ i (y j)
  have h := HypercubeRamsey.Lane_q_s11_tags.pi_expect_prod_on_injective_coords
    p (tagCoord v) (tagCoord_injective v) Finset.univ F
  calc
    _ = (rawTags M p).expect (fun t => ∏ o, F o (t (tagCoord v o))) := by
      congr 1
      funext t
      simp [F, tagCoord, Fintype.prod_option]
    _ = ∏ o, p.expect (F o) := by simpa [rawTags] using h
    _ = _ := by simp [Fintype.prod_option, F, FinProb.expect, piBar, mixW]

set_option maxHeartbeats 800000 in
private theorem raw_expect_eq {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (v : EvenRole n) (hS : SliceFacts M y₀) :
    (rawTags M p).expect (fun t => rawFail M y₀ p t v) =
      ∑ i, p.w i * ∑ z : InnerCoord n → Fin N, innerWeight M y₀ i z *
        outerFail E M.G (piBar M y₀ p) (sigmaW E M.G (gS n) (M.μ i) z) (OuterCoord n) := by
  classical
  let I (i : M.ι) (z : InnerCoord n → Fin N) (y : OuterCoord n → Fin N) : ℝ :=
    if outerZ E M.G (piBar M y₀ p) (sigmaW E M.G (gS n) (M.μ i) z) y < 1/2 then 1 else 0
  have hmean (z : InnerCoord n → Fin N) (y : OuterCoord n → Fin N) :
      (rawTags M p).expect (fun t =>
        (innerWeight M y₀ (t (sliceOf v.1)) z *
          ∏ j, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) (y j)) * I (t (sliceOf v.1)) z y) =
        ∑ i, p.w i * (innerWeight M y₀ i z * (outWt (piBar M y₀ p) y * I i z y)) := by
    calc
      _ = (rawTags M p).expect (fun t =>
          (innerWeight M y₀ (t (sliceOf v.1)) z * I (t (sliceOf v.1)) z y) *
            ∏ j, piRow M y₀ (t (flipOuter (sliceOf v.1) j)) (y j)) := by
        congr 1
        funext t
        exact mul_right_comm _ _ _
      _ = (∑ i, p.w i * (innerWeight M y₀ i z * I i z y)) * ∏ j, piBar M y₀ p (y j) :=
        tag_integrand_mean M y₀ p v (fun i => innerWeight M y₀ i z * I i z y) y
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        unfold outWt
        ac_rfl
  calc
    _ = ∑ z : InnerCoord n → Fin N, ∑ y : OuterCoord n → Fin N,
        ∑ i, p.w i * (innerWeight M y₀ i z * (outWt (piBar M y₀ p) y * I i z y)) := by
      simp_rw [rawFail_sum M y₀ p _ v hS, expect_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro y hy
      exact hmean z y
    _ = _ := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (OuterCoord n → Fin N)))
        (t := (Finset.univ : Finset M.ι))]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rfl

private noncomputable def ballLaw {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (i : M.ι) : FinProb (Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) :=
  FinProb.pi fun _ => tupLaw E M.G (M.μ i) (y₀ i) (kTup n)

private noncomputable def outLaw {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (hS : SliceFacts M y₀) (i : M.ι) (V : Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) :
    FinProb (InnerCoord n → Fin N) :=
  FinProb.pi fun a => {
    w := oddRowW E M.G (gS n) (M.μ i) (M.ν i) (ballStar V a)
    nonneg := (hS.rows i).row_nonneg (ballStar V a)
    sum_eq_one := (hS.rows i).row_sum (ballStar V a) }

private theorem innerWeight_nonneg {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (hS : SliceFacts M y₀) (i : M.ι) (z : InnerCoord n → Fin N) : 0 ≤ innerWeight M y₀ i z := by
  apply Finset.sum_nonneg
  intro V hV
  exact mul_nonneg ((ballLaw M y₀ i).nonneg V) ((outLaw M y₀ hS i V).nonneg z)

private theorem innerWeight_sum {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (hS : SliceFacts M y₀) (i : M.ι) : ∑ z, innerWeight M y₀ i z = 1 := by
  unfold innerWeight
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hsum (V : Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) :
      ∑ z, outW E M.G (gS n) (M.μ i) (M.ν i) V z = 1 :=
    (outLaw M y₀ hS i V).sum_eq_one
  simp_rw [hsum, mul_one]
  exact (ballLaw M y₀ i).sum_eq_one

private theorem innerWeight_sigmaFail {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (i : M.ι) :
    (∑ z : InnerCoord n → Fin N, innerWeight M y₀ i z *
      (if ∑ x, sigmaW E M.G (gS n) (M.μ i) z x = 1 then 0 else 1)) =
      sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) := by
  unfold innerWeight sigmaFail
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

private noncomputable def piBarLaw {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (hS : SliceFacts M y₀) : FinProb (Fin N) where
  w := piBar M y₀ p
  nonneg y := Finset.sum_nonneg (fun i hi => mul_nonneg (p.nonneg i) ((hS.rows i).pi_nonneg y))
  sum_eq_one := by
    unfold piBar mixW
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hsum (i : M.ι) : ∑ y, piRow M y₀ i y = 1 := (hS.rows i).pi_sum
    simp_rw [hsum, mul_one]
    exact p.sum_eq_one

private theorem outerFail_le_one {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (hS : SliceFacts M y₀) (σ : Fin N → ℝ) :
    outerFail E M.G (piBar M y₀ p) σ (OuterCoord n) ≤ 1 := by
  let Q : FinProb (OuterCoord n → Fin N) := FinProb.pi fun _ => piBarLaw M y₀ p hS
  calc
    _ = Q.expect (fun y => if outerZ E M.G (piBar M y₀ p) σ y < 1/2 then 1 else 0) := rfl
    _ ≤ Q.expect (fun _ => 1) := FinProb.expect_mono Q (by intro y; split_ifs <;> norm_num)
    _ = 1 := FinProb.expect_const Q 1

theorem raw_mass_bound {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ δ x₀ K R : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (hF : Fixed11 δ x₀ K n N E X Y κ M y₀ p)
    (hO : OuterTailAt δ x₀ K R n) (v : EvenRole n) :
    (rawTags M p).expect (fun t => rawFail M y₀ p t v) ≤
      (∑ i, p.w i * sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)) +
        (n : ℝ)^(-R) := by
  classical
  let ε := (n : ℝ)^(-R)
  have hε : 0 ≤ ε := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsite (i : M.ι) (hi : p.w i ≠ 0) :
      (∑ z : InnerCoord n → Fin N, innerWeight M y₀ i z *
        outerFail E M.G (piBar M y₀ p) (sigmaW E M.G (gS n) (M.μ i) z) (OuterCoord n)) ≤
        sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) + ε := by
    have hpoint (z : InnerCoord n → Fin N) :
        outerFail E M.G (piBar M y₀ p) (sigmaW E M.G (gS n) (M.μ i) z) (OuterCoord n) ≤
          (if ∑ x, sigmaW E M.G (gS n) (M.μ i) z x = 1 then 0 else 1) + ε := by
      by_cases hs : ∑ x, sigmaW E M.G (gS n) (M.μ i) z x = 1
      · simp only [hs, if_true, zero_add]
        exact hO M.G _ _ _
          (HypercubeRamsey.Lane_q_s11_tags.outerHyp_of_sigma_mass M y₀ p hF i hi z hs)
      · simp only [hs, if_false]
        exact le_trans (outerFail_le_one M y₀ p hF.slice _) (by linarith)
    calc
      _ ≤ ∑ z : InnerCoord n → Fin N, innerWeight M y₀ i z *
          ((if ∑ x, sigmaW E M.G (gS n) (M.μ i) z x = 1 then 0 else 1) + ε) := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hpoint z) (innerWeight_nonneg M y₀ hF.slice i z)
      _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [innerWeight_sigmaFail, ← Finset.sum_mul, innerWeight_sum M y₀ hF.slice i, one_mul]
  rw [raw_expect_eq M y₀ p v hF.slice]
  calc
    _ ≤ ∑ i, p.w i *
        (sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) + ε) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : p.w i = 0
      · simp [hp]
      · exact mul_le_mul_of_nonneg_left (hsite i hp) (p.nonneg i)
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, p.sum_eq_one, one_mul]

end HypercubeRamsey.Lane_sol_s11_raw
