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

end HypercubeRamsey.Lane_q_s11_even
