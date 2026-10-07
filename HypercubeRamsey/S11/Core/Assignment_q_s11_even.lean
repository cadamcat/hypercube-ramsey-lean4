import HypercubeRamsey.S11.Core.Experiment

namespace HypercubeRamsey.Lane_q_s11_even

open HypercubeRamsey.S11.Core
open HypercubeRamsey OAI.HypercubeRamsey
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

private theorem pi_expect_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (g : Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => g (ω i)) = (P i).expect g := by
  classical
  let s : Finset ι := {i}
  let i0 : {j // j ∈ s} := ⟨i, by simp [s]⟩
  let eIndex : {j // j ∈ s} ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => i0
    left_inv := by
      intro j
      have hj : j.1 = i := Finset.mem_singleton.mp (by change j.1 ∈ ({i} : Finset ι); exact j.2)
      exact Subtype.ext hj.symm
    right_inv := by intro u; cases u; rfl
  }
  have indexEq (j : {j // j ∈ s}) : j.1 = i :=
    Finset.mem_singleton.mp (by change j.1 ∈ ({i} : Finset ι); exact j.2)
  let ePi : ((j : {j // j ∈ s}) → Ω j.1) ≃ Ω i := {
    toFun := fun a => a i0
    invFun := fun x j => Eq.mp (congrArg Ω (indexEq j).symm) x
    left_inv := by
      intro a
      funext j
      have hj : j = i0 := Subtype.ext (indexEq j)
      rw [hj]
      simp [i0, indexEq]
    right_inv := by
      intro x
      simp [i0, indexEq]
  }
  let gSub (a : (j : {j // j ∈ s}) → Ω j.1) : ℝ := g (a i0)
  have hMarg := FinProb.pi_marginal_expect P s gSub
  have hleft : (fun ω : (j : ι) → Ω j =>
      gSub (fun j : {j // j ∈ s} => ω j.1)) = fun ω : (j : ι) → Ω j => g (ω i) := by
    funext ω
    simp [gSub, i0]
  have hsub :
      (FinProb.pi (fun j : {j // j ∈ s} => P j.1)).expect gSub = (P i).expect g := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi.symm]
    apply Finset.sum_congr rfl
    intro x hx
    have hprod' :
        (∏ j : {j // j ∈ s}, (P j.1).w (ePi.symm x j)) =
          ∏ u : Unit, (P (eIndex.symm u).1).w (ePi.symm x (eIndex.symm u)) :=
      Fintype.prod_equiv eIndex _ _ (by
        intro j
        have hj : j = i0 := Subtype.ext (indexEq j)
        rw [hj]
        simp [eIndex])
    have hprod :
        (∏ u : Unit, (P (eIndex.symm u).1).w (ePi.symm x (eIndex.symm u))) = (P i).w x := by
      simp [eIndex, ePi, i0]
    simp only [FinProb.pi, hprod'.trans hprod]
    simp [gSub, ePi, i0]
  calc
    (FinProb.pi P).expect (fun ω => g (ω i)) =
        (FinProb.pi P).expect (fun ω => gSub (fun j => ω j.1)) := by rw [hleft]
    _ = (FinProb.pi (fun j : {j // j ∈ s} => P j.1)).expect gSub := hMarg
    _ = (P i).expect g := hsub

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

theorem meanOddRow_raw {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι)
    (b : OddRole n) (hS : SliceFacts M y₀) (y : Fin N) :
    (rawTuples M y₀ t).expect (fun W => oddRowF M t W b y) =
      piRow M y₀ (t (sliceOf b.1)) y := by
  classical
  let η : InnerCoord n → EvenRole n := fun a => evenNbr b a.1
  have hη : Function.Injective η := by
    intro a c hac
    apply Subtype.ext
    by_contra hne
    have hval : cubeFlip b.1 a.1 = cubeFlip b.1 c.1 := congrArg Subtype.val hac
    have hcoord := congrArg (fun z : CubeVertex n => z a.1) hval
    have hne' : a.1 ≠ c.1 := by
      intro heq
      exact hne heq
    cases hb : b.1 a.1 <;>
      simp [cubeFlip, hb, Function.update_of_ne hne'] at hcoord
  let U : Finset (EvenRole n) := Finset.univ.image η
  let ηU : InnerCoord n → {u // u ∈ U} := fun a =>
    ⟨η a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a c hac
      exact hη (congrArg Subtype.val hac)
    · intro u
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp u.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : InnerCoord n ≃ {u // u ∈ U} := Equiv.ofBijective ηU hηU
  let Q : EvenRole n → FinProb (Fin (kTup n) → Fin N) := fun u =>
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let G : (∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) → ℝ := fun V =>
    oddRowW E M.G (gS n) (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1)))
      (fun a => V (e a)) y
  have hpi := FinProb.pi_marginal_expect Q U G
  let QI : InnerCoord n → FinProb (Fin (kTup n) → Fin N) := fun a => Q (η a)
  have hchange :
      (FinProb.pi (fun u : {u // u ∈ U} => Q u.1)).expect G =
        (FinProb.pi QI).expect (fun V => oddRowW E M.G (gS n)
          (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) V y) := by
    classical
    let ePi : (∀ a : InnerCoord n, Fin (kTup n) → Fin N) ≃
        (∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) := {
      toFun := fun V u => V (e.symm u)
      invFun := fun V a => V (e a)
      left_inv := by intro V; funext a; simp
      right_inv := by intro V; funext u; simp
    }
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro V hV
    have hprod' :
        (∏ a : InnerCoord n, (Q (e a).1).w (ePi V (e a))) =
          ∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u) :=
      Fintype.prod_equiv e _ _ (by intro a; simp [ePi])
    have hprod :
        (∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u)) =
          ∏ a : InnerCoord n, (QI a).w (V a) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : G (ePi V) = oddRowW E M.G (gS n)
        (M.μ (t (sliceOf b.1))) (M.ν (t (sliceOf b.1))) V y := by
      simp [G, ePi]
    simpa only [FinProb.pi, hprod, heval]
  change (FinProb.pi Q).expect (fun W => G (fun u => W u.1)) = _
  rw [hpi, hchange]
  have hslice (a : InnerCoord n) : sliceOf (evenNbr b a.1).1 = sliceOf b.1 := by
    funext j
    have hne : a.1 ≠ j.1 := by
      intro heq
      have hlt := a.2
      have hge := j.2
      rw [heq] at hlt
      omega
    change Function.update b.1 a.1 (!b.1 a.1) j.1 = b.1 j.1
    exact Function.update_of_ne (Ne.symm hne) _ _
  simp [QI, Q, η, FinProb.expect, FinProb.pi, G, e, ηU,
    piRow, meanOddRow, starW, tupW, tupLaw, oddRowF, starOf, hslice]

theorem inner_output_sum {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (t : OuterWord n → M.ι)
    (v : EvenRole n) (W : EvenRole n → Fin (kTup n) → Fin N)
    (hS : SliceFacts M y₀) (x : Fin N) :
    ∑ f, oddProdW M t W f *
        ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x) =
      ∑ z : InnerCoord n → Fin N,
        (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
          ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x) := by
  classical
  let η : InnerCoord n → OddRole n := fun a => oddNbr v a.1
  have hη : Function.Injective η := by
    intro a c hac
    apply Subtype.ext
    by_contra hne
    have hval : cubeFlip v.1 a.1 = cubeFlip v.1 c.1 := congrArg Subtype.val hac
    have hcoord := congrArg (fun z : CubeVertex n => z a.1) hval
    have hne' : a.1 ≠ c.1 := by
      intro heq
      apply hne
      simp [heq]
    cases hv : v.1 a.1 <;>
      simp [cubeFlip, hv, Function.update_of_ne hne'] at hcoord
  let U : Finset (OddRole n) := Finset.univ.image η
  let ηU : InnerCoord n → {b // b ∈ U} := fun a =>
    ⟨η a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a c hac
      exact hη (congrArg Subtype.val hac)
    · intro b
      obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp b.2
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : InnerCoord n ≃ {b // b ∈ U} := Equiv.ofBijective ηU hηU
  let rowLaw (b : OddRole n) : FinProb (Fin N) := {
    w := oddRowF M t W b
    nonneg := (hS.rows (t (sliceOf b.1))).row_nonneg (starOf W b)
    sum_eq_one := (hS.rows (t (sliceOf b.1))).row_sum (starOf W b)
  }
  let rawOdd : FinProb (OddRole n → Fin N) := FinProb.pi rowLaw
  let restrict (f : OddRole n → Fin N) (b : {b // b ∈ U}) : Fin N := f b.1
  let innerFun (o : ∀ b : {b // b ∈ U}, Fin N) : ℝ :=
    (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (fun a => o (ηU a)) x
  let val (f : OddRole n → Fin N) : ℝ :=
    (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x
  have hval (f : OddRole n → Fin N) : val f = innerFun (restrict f) := by
    unfold val innerFun innerOut restrict
    congr 1
  have hMarginal := FinProb.pi_marginal_expect rowLaw U innerFun
  let QI (a : InnerCoord n) : FinProb (Fin N) := rowLaw (η a)
  let G (z : InnerCoord n → Fin N) : ℝ :=
    (N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x
  let ePi : (InnerCoord n → Fin N) ≃ ((b : {b // b ∈ U}) → Fin N) := {
    toFun := fun z b => z (e.symm b)
    invFun := fun z a => z (e a)
    left_inv := by intro z; funext a; simp
    right_inv := by intro z; funext b; simp
  }
  have hchange :
      (FinProb.pi (fun b : {b // b ∈ U} => rowLaw b.1)).expect innerFun =
        (FinProb.pi QI).expect G := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro z hz
    have hprod' :
        (∏ a : InnerCoord n, (rowLaw (e a).1).w (ePi z (e a))) =
          ∏ b : {b // b ∈ U}, (rowLaw b.1).w (ePi z b) :=
      Fintype.prod_equiv e _ _ (by intro a; simp [ePi])
    have hprod :
        (∏ b : {b // b ∈ U}, (rowLaw b.1).w (ePi z b)) =
          ∏ a : InnerCoord n, (QI a).w (z a) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : innerFun (ePi z) = G z := by
      simp [innerFun, G, ePi, ηU, e]
    simpa only [FinProb.pi, hprod, heval]
  calc
    ∑ f, oddProdW M t W f * val f = rawOdd.expect val := by
      simp [FinProb.expect, FinProb.pi, oddProdW, rawOdd, rowLaw, val]
    _ = rawOdd.expect (fun f => innerFun (restrict f)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      rw [hval]
    _ = (FinProb.pi (fun b : {b // b ∈ U} => rowLaw b.1)).expect innerFun := hMarginal
    _ = (FinProb.pi QI).expect G := hchange
    _ = ∑ z : InnerCoord n → Fin N,
        (∏ a, oddRowF M t W (oddNbr v a.1) (z a)) *
          ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x) := by
      simp [FinProb.expect, FinProb.pi, η, QI, rowLaw, G]

theorem internal_star_raw {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (t : OuterWord n → M.ι) (v : EvenRole n) (x : Fin N) (hS : SliceFacts M y₀) :
    (rawTuples M y₀ t).expect (fun W =>
      ∑ f, oddProdW M t W f *
        ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)) =
      (N : ℝ) * alphaRow M y₀ (t (sliceOf v.1)) x := by
  classical
  let η : Option (Pair (InnerCoord n)) → EvenRole n := localEvenRole v
  have hη : Function.Injective η := localEvenRole_injective v
  let U : Finset (EvenRole n) := Finset.univ.image η
  let ηU : Option (Pair (InnerCoord n)) → {u // u ∈ U} := fun o =>
    ⟨η o, Finset.mem_image.mpr ⟨o, Finset.mem_univ _, rfl⟩⟩
  have hηU : Function.Bijective ηU := by
    constructor
    · intro a b hab
      exact hη (congrArg Subtype.val hab)
    · intro u
      obtain ⟨o, ho, hEq⟩ := Finset.mem_image.mp u.2
      refine ⟨o, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : Option (Pair (InnerCoord n)) ≃ {u // u ∈ U} := Equiv.ofBijective ηU hηU
  let Q (u : EvenRole n) : FinProb (Fin (kTup n) → Fin N) :=
    tupLaw E M.G (M.μ (t (sliceOf u.1))) (y₀ (t (sliceOf u.1))) (kTup n)
  let QI (o : Option (Pair (InnerCoord n))) : FinProb (Fin (kTup n) → Fin N) := Q (η o)
  let restrict (W : EvenRole n → Fin (kTup n) → Fin N) (u : {u // u ∈ U}) := W u.1
  let G (V : ∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) : ℝ :=
    (N : ℝ) * ∑ z : InnerCoord n → Fin N,
      outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1)))
        (fun o => V (ηU o)) z * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x
  let H (V : Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) : ℝ :=
    (N : ℝ) * ∑ z : InnerCoord n → Fin N,
      outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1))) V z *
        sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x
  let ePi : (Option (Pair (InnerCoord n)) → Fin (kTup n) → Fin N) ≃
      (∀ u : {u // u ∈ U}, Fin (kTup n) → Fin N) := {
    toFun := fun V u => V (e.symm u)
    invFun := fun V o => V (e o)
    left_inv := by intro V; funext o; simp
    right_inv := by intro V; funext u; simp
  }
  have hchange :
      (FinProb.pi (fun u : {u // u ∈ U} => Q u.1)).expect G =
        (FinProb.pi QI).expect H := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp ePi]
    apply Finset.sum_congr rfl
    intro V hV
    have hprod' :
        (∏ o : Option (Pair (InnerCoord n)), (Q (e o).1).w (ePi V (e o))) =
          ∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u) :=
      Fintype.prod_equiv e _ _ (by intro o; simp [ePi])
    have hprod :
        (∏ u : {u // u ∈ U}, (Q u.1).w (ePi V u)) =
          ∏ o : Option (Pair (InnerCoord n)), (QI o).w (V o) := by
      simpa [QI, e, ηU, ePi] using hprod'.symm
    have heval : G (ePi V) = H V := by simp [G, H, ePi, ηU, e]
    simpa only [FinProb.pi, hprod, heval]
  have hstar (W : EvenRole n → Fin (kTup n) → Fin N) (a : InnerCoord n) :
      starOf W (oddNbr v a.1) = ballStar (fun o => W (η o)) a := by
    funext c
    by_cases hc : c = a
    · subst c
      simp [starOf, oddNbr, evenNbr, localEvenRole, η, ballStar, cubeFlip]
    · have hpair := localEvenRole_pair v a c hc
      simp [starOf, oddNbr, evenNbr, localEvenRole, η, ballStar, hc, hpair]
  have hpoint (W : EvenRole n → Fin (kTup n) → Fin N) :
      ∑ f, oddProdW M t W f *
          ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x) =
        G (restrict W) := by
    rw [inner_output_sum M y₀ t v W hS x]
    have hV : (fun o => W (ηU o).1) = fun o => W (η o) := by
      funext o
      rfl
    unfold G restrict outW
    rw [hV]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    have hprod :
        (∏ a : InnerCoord n, oddRowF M t W (oddNbr v a.1) (z a)) =
          ∏ a : InnerCoord n,
            oddRowW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1)))
              (ballStar (fun o => W (η o)) a) (z a) := by
      apply Finset.prod_congr rfl
      intro a ha
      change oddRowW E M.G (gS n) (M.μ (t (sliceOf (oddNbr v a.1).1)))
        (M.ν (t (sliceOf (oddNbr v a.1).1))) (starOf W (oddNbr v a.1)) (z a) = _
      rw [hstar]
      have hslice : sliceOf (oddNbr v a.1).1 = sliceOf v.1 := by
        funext j
        have hne : a.1 ≠ j.1 := by
          intro heq
          have hlt := a.2
          have hge := j.2
          rw [heq] at hlt
          omega
        change Function.update v.1 a.1 (!v.1 a.1) j.1 = v.1 j.1
        exact Function.update_of_ne (Ne.symm hne) _ _
      rw [hslice]
    rw [hprod]
    ring
  have hMarginal := FinProb.pi_marginal_expect Q U G
  calc
    (rawTuples M y₀ t).expect (fun W =>
      ∑ f, oddProdW M t W f *
        ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)) =
      (rawTuples M y₀ t).expect (fun W => G (restrict W)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro W hW
        change (rawTuples M y₀ t).w W *
            (∑ f, oddProdW M t W f *
              ((N : ℝ) * sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) (innerOut f v) x)) =
          (rawTuples M y₀ t).w W * G (restrict W)
        rw [hpoint W]
    _ = (FinProb.pi (fun u : {u // u ∈ U} => Q u.1)).expect G := hMarginal
    _ = (FinProb.pi QI).expect H := hchange
    _ = (N : ℝ) * alphaRow M y₀ (t (sliceOf v.1)) x := by
      have hfactor {Ω : Type} [Fintype Ω] (A B : Ω → ℝ) :
          ∑ ω, A ω * ((N : ℝ) * B ω) = (N : ℝ) * ∑ ω, A ω * B ω := by
        calc
          ∑ ω, A ω * ((N : ℝ) * B ω) = ∑ ω, (N : ℝ) * (A ω * B ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
          _ = (N : ℝ) * ∑ ω, A ω * B ω := by rw [← Finset.mul_sum]
      simpa [FinProb.expect, FinProb.pi, QI, Q, H, alphaRow, meanEvenRow,
        ballW, outW, tupLaw, tupW, localEvenRole_slice, η] using
        (hfactor (fun W => ballW E M.G (M.μ (t (sliceOf v.1)))
            (y₀ (t (sliceOf v.1))) W)
          (fun W => ∑ z : InnerCoord n → Fin N,
            outW E M.G (gS n) (M.μ (t (sliceOf v.1))) (M.ν (t (sliceOf v.1))) W z *
              sigmaW E M.G (gS n) (M.μ (t (sliceOf v.1))) z x))

end HypercubeRamsey.Lane_q_s11_even
