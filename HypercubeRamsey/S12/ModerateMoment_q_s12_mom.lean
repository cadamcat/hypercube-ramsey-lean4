import HypercubeRamsey.S12.InteractionTails

namespace HypercubeRamsey.S12

open Classical
open Filter
open scoped BigOperators

private lemma iid_pi_weight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι) (ω : ∀ i, Ω i) :
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
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 :=
        Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) * (∏ i : {i // i ∉ s}, f i.1) := by
      rw [← hs, ← hnot]

private lemma iid_pi_expect_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (∑ ω, (∏ i, (P i).w (ω i)) * f ω) =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (∏ i : {i // i ∈ s}, (P i.1).w (a i)) *
            (∏ i : {i // i ∉ s}, (P i.1).w (b i)) *
              f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [iid_pi_weight_split P s (e.symm (a, b))]
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  ring

lemma weighted_event_exists_le_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (p : Ω → Prop) (q : ι → Ω → Prop)
    [DecidablePred p] [∀ a, DecidablePred (q a)]
    (hcover : ∀ x, p x → ∃ a, q a x) :
    ∑ x, (if p x then w x else 0) ≤
      ∑ a, ∑ x, (if q a x then w x else 0) := by
  classical
  calc
    ∑ x, (if p x then w x else 0) ≤
        ∑ x, ∑ a, (if q a x then w x else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hp : p x
      · obtain ⟨a, hax⟩ := hcover x hp
        rw [if_pos hp]
        calc
          w x = (if q a x then w x else 0) := by simp [hax]
          _ ≤ ∑ b, if q b x then w x else 0 := by
            let f : ι → ℝ := fun b => if q b x then w x else 0
            have hsingle : f a ≤ ∑ b ∈ (Finset.univ : Finset ι), f b :=
              Finset.single_le_sum
                (fun b hb => by
                  dsimp [f]
                  split_ifs with hq
                  · exact hw x
                  · exact le_rfl)
                (Finset.mem_univ a)
            simpa [f, hax] using hsingle
      · simp [hp]
        apply Finset.sum_nonneg
        intro a ha
        split_ifs with hq
        · exact hw x
        · exact le_rfl
    _ = ∑ a, ∑ x, (if q a x then w x else 0) := Finset.sum_comm

private def pairIndexEquiv {ι : Type*} [DecidableEq ι] (i₀ i₁ : ι) (h : i₀ ≠ i₁) :
    Fin 2 ≃ {i : ι // i ∈ (insert i₀ {i₁} : Finset ι)} where
  toFun j := if j.val = 0 then ⟨i₀, by simp⟩ else ⟨i₁, by simp⟩
  invFun i := if i.val = i₀ then 0 else 1
  left_inv j := by
    fin_cases j
    · simp
    · simp [Ne.symm h]
  right_inv i := by
    apply Subtype.ext
    rcases Finset.mem_insert.mp i.property with hi₀ | hi₁
    · simp [hi₀]
    · simp [Finset.mem_singleton] at hi₁
      simp [hi₁, Ne.symm h]

private def pairValueEquiv {ι N : Type*} [DecidableEq ι]
    (i₀ i₁ : ι) (h : i₀ ≠ i₁) :
    (∀ i : {i : ι // i ∈ (insert i₀ {i₁} : Finset ι)}, N) ≃ N × N where
  toFun a := (a ⟨i₀, by simp⟩, a ⟨i₁, by simp⟩)
  invFun p i := if i.val = i₀ then p.1 else p.2
  left_inv a := by
    funext i
    rcases Finset.mem_insert.mp i.property with hi₀ | hi₁
    · have heq : (⟨i₀, by simp⟩ : {i : ι // i ∈ (insert i₀ {i₁} : Finset ι)}) = i :=
        Subtype.ext hi₀.symm
      change (if i.val = i₀ then a ⟨i₀, by simp⟩ else a ⟨i₁, by simp⟩) = a i
      rw [if_pos hi₀]
      exact congrArg a heq
    · simp [Finset.mem_singleton] at hi₁
      have hnot : i.val ≠ i₀ := fun heq => h (heq.symm.trans hi₁)
      have heq : (⟨i₁, by simp⟩ : {i : ι // i ∈ (insert i₀ {i₁} : Finset ι)}) = i :=
        Subtype.ext hi₁.symm
      change (if i.val = i₀ then a ⟨i₀, by simp⟩ else a ⟨i₁, by simp⟩) = a i
      rw [if_neg hnot]
      exact congrArg a heq
  right_inv p := by
    rcases p with ⟨x, y⟩
    apply Prod.ext
    · change (if i₀ = i₀ then x else y) = x
      simp
    · change (if i₁ = i₀ then x else y) = y
      simp [Ne.symm h]

private lemma pair_prod_weight {ι N : Type*} [Fintype ι] [Fintype N] [DecidableEq ι]
    (τ : FinProb N) (i₀ i₁ : ι) (h : i₀ ≠ i₁)
    (a : ∀ i : {i : ι // i ∈ (insert i₀ {i₁} : Finset ι)}, N) :
    (∏ i, τ.w (a i)) = τ.w (a ⟨i₀, by simp⟩) * τ.w (a ⟨i₁, by simp⟩) := by
  classical
  let e := pairIndexEquiv i₀ i₁ h
  calc
    (∏ i, τ.w (a i)) = ∏ j : Fin 2, τ.w (a (e j)) := by
      symm
      exact Fintype.prod_equiv e _ _ (by intro j; rfl)
    _ = τ.w (a ⟨i₀, by simp⟩) * τ.w (a ⟨i₁, by simp⟩) := by
      rw [Fin.prod_univ_two]
      simp [e, pairIndexEquiv, h]

lemma interaction_event_mass_two_le {N u : ℕ}
    (τ : Law N) (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    (J : Finset (Fin u)) (i₀ i₁ : Fin u) (hJ₀ : i₀ ∈ J) (hJ₁ : i₁ ∈ J)
    (hneq : i₀ ≠ i₁) (t B : ℝ) (hB : 0 ≤ B) (gate : Fin N → Prop)
    (hgate : ∀ x, 0 < τ.w x → gate x)
    (hTail : ∀ xs : Fin u → Fin N,
      (∀ i ∈ J, i ≠ i₀ → i ≠ i₁ → gate (xs i)) →
      ∑ z, ∑ z',
        (if gate z ∧ gate z' ∧ t <
            |inter E c π J (Function.update (Function.update xs i₀ z) i₁ z')|
         then τ.w z * τ.w z' else 0) ≤ B) :
    ∑ xs : Fin u → Fin N,
      (if t < |inter E c π J xs| then prodW τ.w xs else 0) ≤ B := by
  classical
  have hN : Nonempty (Fin N) := by
    by_contra hN
    haveI : IsEmpty (Fin N) := ⟨fun x => hN ⟨x⟩⟩
    have hs : (∑ x : Fin N, τ.w x) = 0 := by simp
    rw [τ.sum_eq_one] at hs
    norm_num at hs
  let τP : FinProb (Fin N) := ⟨τ.w, τ.nonneg, τ.sum_eq_one⟩
  let P : Fin u → FinProb (Fin N) := fun _ => τP
  let s : Finset (Fin u) := insert i₀ {i₁}
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin u => i ∈ s) (fun _ => Fin N)
  let A := {i : Fin u // i ∈ s}
  let C := {i : Fin u // i ∉ s}
  let x₀ : Fin N := Classical.choice hN
  let a₀ : A → Fin N := fun _ => x₀
  let pairEquiv := pairValueEquiv (N := Fin N) i₀ i₁ hneq
  have hsplit :
      (∑ xs : Fin u → Fin N,
        prodW τ.w xs * (if t < |inter E c π J xs| then 1 else 0)) =
      ∑ a : A → Fin N, ∑ b : C → Fin N,
        (∏ i : A, τ.w (a i)) * (∏ i : C, τ.w (b i)) *
          (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) := by
    have hh := iid_pi_expect_split P s
      (fun xs : Fin u → Fin N => if t < |inter E c π J xs| then 1 else 0)
    simpa [P, τP, prodW, s, e, A, C] using hh
  have hcomp : ∑ b : C → Fin N, ∏ i : C, τ.w (b i) = 1 := by
    rw [← Fintype.prod_sum]
    simp [τ.sum_eq_one]
  have hpair (b : C → Fin N) (hb : 0 < ∏ i : C, τ.w (b i)) :
      ∑ a : A → Fin N,
        (∏ i : A, τ.w (a i)) *
          (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) ≤ B := by
    let base : Fin u → Fin N := e.symm (a₀, b)
    have hother : ∀ i ∈ J, i ≠ i₀ → i ≠ i₁ → gate (base i) := by
      intro i hi hne₀ hne₁
      have hiC : i ∉ s := by simp [s, hne₀, hne₁]
      let j : C := ⟨i, hiC⟩
      have hpos : 0 < τ.w (b j) := by
        by_contra hz
        have hz' : τ.w (b j) = 0 := le_antisymm (le_of_not_gt hz) (τ.nonneg _)
        have hzero : (∏ i : C, τ.w (b i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) hz'
        linarith
      have hbase : base i = b j := by
        simp [base, e, Equiv.piEquivPiSubtypeProd_symm_apply, hiC, j]
      rw [hbase]
      exact hgate _ hpos
    have htail := hTail base hother
    have hterm (z z' : Fin N) :
        τ.w z * τ.w z' *
            (if t < |inter E c π J
              (Function.update (Function.update base i₀ z) i₁ z')| then 1 else 0) ≤
          (if gate z ∧ gate z' ∧ t < |inter E c π J
              (Function.update (Function.update base i₀ z) i₁ z')|
           then τ.w z * τ.w z' else 0) := by
      by_cases hbad : t < |inter E c π J
          (Function.update (Function.update base i₀ z) i₁ z')|
      · by_cases hz0 : τ.w z = 0
        · simp [hz0]
        · by_cases hz'0 : τ.w z' = 0
          · simp [hz'0]
          · have hzpos : 0 < τ.w z := lt_of_le_of_ne (τ.nonneg z) (Ne.symm hz0)
            have hz'pos : 0 < τ.w z' := lt_of_le_of_ne (τ.nonneg z') (Ne.symm hz'0)
            simp [hbad, hgate z hzpos, hgate z' hz'pos]
      · simp [hbad]
    have hpairSum :
        ∑ a : A → Fin N,
          (∏ i : A, τ.w (a i)) *
            (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) ≤ B := by
      rw [← Equiv.sum_comp pairEquiv.symm
        (fun a : A → Fin N =>
          (∏ i : A, τ.w (a i)) *
            (if t < |inter E c π J (e.symm (a, b))| then 1 else 0))]
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ z : Fin N, ∑ z' : Fin N,
            τ.w z * τ.w z' *
              (if t < |inter E c π J
                (Function.update (Function.update base i₀ z) i₁ z')| then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro z hz
              apply Finset.sum_congr rfl
              intro z' hz'
              have hweight :
                  (∏ i : A, τ.w ((pairEquiv.symm (z, z')) i)) = τ.w z * τ.w z' := by
                change (∏ i : {i : Fin u // i ∈ (insert i₀ {i₁} : Finset (Fin u))},
                    τP.w ((pairValueEquiv (N := Fin N) i₀ i₁ hneq).symm (z, z') i)) =
                  τP.w z * τP.w z'
                have hw := pair_prod_weight τP i₀ i₁ hneq
                  ((pairValueEquiv (N := Fin N) i₀ i₁ hneq).symm (z, z'))
                have heq := (pairValueEquiv (N := Fin N) i₀ i₁ hneq).apply_symm_apply (z, z')
                have hfirst :
                    ((pairValueEquiv (N := Fin N) i₀ i₁ hneq).symm (z, z'))
                      ⟨i₀, by simp⟩ = z := by
                  simpa [pairValueEquiv] using congrArg Prod.fst heq
                have hsecond :
                    ((pairValueEquiv (N := Fin N) i₀ i₁ hneq).symm (z, z'))
                      ⟨i₁, by simp⟩ = z' := by
                  simpa [pairValueEquiv] using congrArg Prod.snd heq
                rw [hfirst, hsecond] at hw
                simpa only [τP] using hw
              have htuple : e.symm (pairEquiv.symm (z, z'), b) =
                  Function.update (Function.update base i₀ z) i₁ z' := by
                funext i
                by_cases hi₀ : i = i₀
                · subst i
                  simp [base, e, pairEquiv, pairValueEquiv, s, hneq]
                · by_cases hi₁ : i = i₁
                  · subst i
                    simp [base, e, pairEquiv, pairValueEquiv, s, hneq, hi₀]
                  · have hiC : i ∉ s := by simp [s, hi₀, hi₁]
                    simp [base, e, pairEquiv, pairValueEquiv, s,
                      Equiv.piEquivPiSubtypeProd_symm_apply, hiC, hi₀, hi₁]
              rw [hweight, htuple]
        _ ≤ ∑ z, ∑ z',
            (if gate z ∧ gate z' ∧ t < |inter E c π J
                (Function.update (Function.update base i₀ z) i₁ z')|
             then τ.w z * τ.w z' else 0) := by
              apply Finset.sum_le_sum
              intro z hz
              apply Finset.sum_le_sum
              intro z' hz'
              exact hterm z z'
        _ ≤ B := htail
    exact hpairSum
  have houter :
      ∑ b : C → Fin N,
        (∏ i : C, τ.w (b i)) *
          ∑ a : A → Fin N,
            (∏ i : A, τ.w (a i)) *
              (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) ≤ B := by
    calc
      _ ≤ ∑ b : C → Fin N, (∏ i : C, τ.w (b i)) * B := by
        apply Finset.sum_le_sum
        intro b hb
        by_cases hzero : (∏ i : C, τ.w (b i)) = 0
        · simp [hzero]
        · have hbpos : 0 < ∏ i : C, τ.w (b i) :=
            lt_of_le_of_ne (Finset.prod_nonneg fun i hi => τ.nonneg (b i)) (Ne.symm hzero)
          exact mul_le_mul_of_nonneg_left (hpair b hbpos) hbpos.le
      _ = B := by rw [← Finset.sum_mul, hcomp]; ring
  have hsplitOrder :
      (∑ a : A → Fin N, ∑ b : C → Fin N,
        (∏ i : A, τ.w (a i)) * (∏ i : C, τ.w (b i)) *
          (if t < |inter E c π J (e.symm (a, b))| then 1 else 0)) =
      ∑ b : C → Fin N, (∏ i : C, τ.w (b i)) *
        ∑ a : A → Fin N,
          (∏ i : A, τ.w (a i)) *
            (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.univ.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  calc
    _ = ∑ xs : Fin u → Fin N,
          prodW τ.w xs * (if t < |inter E c π J xs| then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hbad : t < |inter E c π J xs| <;> simp [hbad, prodW]
    _ = ∑ b : C → Fin N, (∏ i : C, τ.w (b i)) *
          ∑ a : A → Fin N,
            (∏ i : A, τ.w (a i)) *
              (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) := by
        rw [hsplit, hsplitOrder]
    _ ≤ B := houter

private def singletonIndexEquiv {ι : Type*} [DecidableEq ι] (i₀ : ι) :
    Fin 1 ≃ {i : ι // i ∈ ({i₀} : Finset ι)} where
  toFun _ := ⟨i₀, by simp⟩
  invFun _ := 0
  left_inv j := by fin_cases j <;> rfl
  right_inv j := by
    apply Subtype.ext
    exact (Finset.mem_singleton.mp j.property).symm

private def singletonAssignmentEquiv {ι N : Type*} [DecidableEq ι] (i₀ : ι) :
    (∀ i : {i : ι // i ∈ ({i₀} : Finset ι)}, N) ≃ N where
  toFun a := a ⟨i₀, by simp⟩
  invFun x := fun _ => x
  left_inv a := by
    funext i
    have hi : i.val = i₀ := Finset.mem_singleton.mp i.property
    have heq : (⟨i₀, by simp⟩ : {i : ι // i ∈ ({i₀} : Finset ι)}) = i :=
      Subtype.ext hi.symm
    exact congrArg a heq
  right_inv _ := rfl

private lemma singleton_prod_weight {ι N : Type*} [Fintype ι] [Fintype N]
    [DecidableEq ι] (τ : FinProb N) (i₀ : ι)
    (a : ∀ i : {i : ι // i ∈ ({i₀} : Finset ι)}, N) :
    (∏ i, τ.w (a i)) = τ.w (a ⟨i₀, by simp⟩) := by
  classical
  let e := singletonIndexEquiv i₀
  calc
    (∏ i, τ.w (a i)) = ∏ j : Fin 1, τ.w (a (e j)) := by
      symm
      exact Fintype.prod_equiv e _ _ (by intro j; rfl)
    _ = τ.w (a ⟨i₀, by simp⟩) := by
      rw [Fin.prod_univ_one]
      rfl

lemma interaction_event_mass_one_le {N u : ℕ}
    (τ : Law N) (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    (J : Finset (Fin u)) (i₀ : Fin u) (hJ₀ : i₀ ∈ J)
    (t B : ℝ) (gate : Fin N → Prop) (hgate : ∀ x, 0 < τ.w x → gate x)
    (hTail : ∀ xs : Fin u → Fin N,
      (∀ i ∈ J, i ≠ i₀ → gate (xs i)) →
      ∑ z ∈ Finset.univ.filter (fun z =>
        gate z ∧ t < |inter E c π J (Function.update xs i₀ z)|), τ.w z ≤ B) :
    ∑ xs : Fin u → Fin N,
      (if t < |inter E c π J xs| then prodW τ.w xs else 0) ≤ B := by
  classical
  have hN : Nonempty (Fin N) := by
    by_contra hN
    haveI : IsEmpty (Fin N) := ⟨fun x => hN ⟨x⟩⟩
    have hs : (∑ x : Fin N, τ.w x) = 0 := by simp
    rw [τ.sum_eq_one] at hs
    norm_num at hs
  let τP : FinProb (Fin N) := ⟨τ.w, τ.nonneg, τ.sum_eq_one⟩
  let P : Fin u → FinProb (Fin N) := fun _ => τP
  let s : Finset (Fin u) := {i₀}
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin u => i ∈ s) (fun _ => Fin N)
  let A := {i : Fin u // i ∈ s}
  let C := {i : Fin u // i ∉ s}
  let x₀ : Fin N := Classical.choice hN
  let a₀ : A → Fin N := fun _ => x₀
  let oneEquiv := singletonAssignmentEquiv (N := Fin N) i₀
  have hsplit :
      (∑ xs : Fin u → Fin N,
        prodW τ.w xs * (if t < |inter E c π J xs| then 1 else 0)) =
      ∑ a : A → Fin N, ∑ b : C → Fin N,
        (∏ i : A, τ.w (a i)) * (∏ i : C, τ.w (b i)) *
          (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) := by
    have hh := iid_pi_expect_split P s
      (fun xs : Fin u → Fin N => if t < |inter E c π J xs| then 1 else 0)
    simpa [P, τP, prodW, s, e, A, C] using hh
  have hcomp : ∑ b : C → Fin N, ∏ i : C, τ.w (b i) = 1 := by
    rw [← Fintype.prod_sum]
    simp [τ.sum_eq_one]
  have hpair (b : C → Fin N) (hb : 0 < ∏ i : C, τ.w (b i)) :
      ∑ a : A → Fin N,
        (∏ i : A, τ.w (a i)) *
          (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) ≤ B := by
    let base : Fin u → Fin N := e.symm (a₀, b)
    have hother : ∀ i ∈ J, i ≠ i₀ → gate (base i) := by
      intro i hi hne
      have hiC : i ∉ s := by simp [s, hne]
      let j : C := ⟨i, hiC⟩
      have hpos : 0 < τ.w (b j) := by
        by_contra hz
        have hz' : τ.w (b j) = 0 := le_antisymm (le_of_not_gt hz) (τ.nonneg _)
        have hzero : (∏ i : C, τ.w (b i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) hz'
        linarith
      have hbase : base i = b j := by
        simp [base, e, Equiv.piEquivPiSubtypeProd_symm_apply, hiC, j]
      rw [hbase]
      exact hgate _ hpos
    have htail := hTail base hother
    have htail' :
        ∑ z, (if gate z ∧ t < |inter E c π J (Function.update base i₀ z)|
          then τ.w z else 0) ≤ B := by
      simpa [Finset.sum_filter] using htail
    have hpairSum :
        ∑ a : A → Fin N,
          (∏ i : A, τ.w (a i)) *
            (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) ≤ B := by
      rw [← Equiv.sum_comp oneEquiv.symm
        (fun a : A → Fin N =>
          (∏ i : A, τ.w (a i)) *
            (if t < |inter E c π J (e.symm (a, b))| then 1 else 0))]
      have hweight : ∀ z : Fin N,
          ∏ i : A, τ.w ((oneEquiv.symm z) i) = τ.w z := by
        intro z
        exact singleton_prod_weight τP i₀ (oneEquiv.symm z)
      have htuple : ∀ z : Fin N,
          e.symm (oneEquiv.symm z, b) = Function.update base i₀ z := by
        intro z
        funext i
        by_cases hi : i = i₀
        · subst i
          simp [base, e, oneEquiv, singletonAssignmentEquiv, s]
        · have hiC : i ∉ s := by simp [s, hi]
          simp [base, e, oneEquiv, singletonAssignmentEquiv, s,
            Equiv.piEquivPiSubtypeProd_symm_apply, hi, hiC]
      calc
        _ = ∑ z : Fin N,
            τ.w z * (if t < |inter E c π J (Function.update base i₀ z)| then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [hweight z, htuple z]
        _ ≤ ∑ z : Fin N,
            (if gate z ∧ t < |inter E c π J (Function.update base i₀ z)|
             then τ.w z else 0) := by
              apply Finset.sum_le_sum
              intro z hz
              by_cases hbad : t < |inter E c π J (Function.update base i₀ z)|
              · by_cases hz0 : τ.w z = 0
                · simp [hbad, hz0]
                · have hzpos : 0 < τ.w z := lt_of_le_of_ne (τ.nonneg z) (Ne.symm hz0)
                  simp [hbad, hgate z hzpos]
              · simp [hbad]
        _ ≤ B := htail'
    exact hpairSum
  have houter :
      ∑ b : C → Fin N,
        (∏ i : C, τ.w (b i)) *
          ∑ a : A → Fin N,
            (∏ i : A, τ.w (a i)) *
              (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) ≤ B := by
    calc
      _ ≤ ∑ b : C → Fin N, (∏ i : C, τ.w (b i)) * B := by
        apply Finset.sum_le_sum
        intro b hb
        by_cases hzero : (∏ i : C, τ.w (b i)) = 0
        · simp [hzero]
        · have hbpos : 0 < ∏ i : C, τ.w (b i) :=
            lt_of_le_of_ne (Finset.prod_nonneg fun i hi => τ.nonneg (b i)) (Ne.symm hzero)
          exact mul_le_mul_of_nonneg_left (hpair b hbpos) hbpos.le
      _ = B := by rw [← Finset.sum_mul, hcomp]; ring
  have hsplitOrder :
      (∑ a : A → Fin N, ∑ b : C → Fin N,
        (∏ i : A, τ.w (a i)) * (∏ i : C, τ.w (b i)) *
          (if t < |inter E c π J (e.symm (a, b))| then 1 else 0)) =
      ∑ b : C → Fin N, (∏ i : C, τ.w (b i)) *
        ∑ a : A → Fin N,
          (∏ i : A, τ.w (a i)) *
            (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.univ.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  calc
    _ = ∑ xs : Fin u → Fin N,
          prodW τ.w xs * (if t < |inter E c π J xs| then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro xs hxs
        by_cases hbad : t < |inter E c π J xs| <;> simp [hbad, prodW]
    _ = ∑ b : C → Fin N, (∏ i : C, τ.w (b i)) *
          ∑ a : A → Fin N,
            (∏ i : A, τ.w (a i)) *
              (if t < |inter E c π J (e.symm (a, b))| then 1 else 0) := by
        rw [hsplit, hsplitOrder]
    _ ≤ B := houter

lemma interaction_powerset_sum_le {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N) (I : Finset (Fin u))
    (l : Fin d) (t : ℝ)
    (hπ : ∀ l, ∑ y, π l y = 1)
    (hdeg : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i))
    (hmoderate : ∀ J : Finset (Fin u), 2 ≤ J.card →
      |inter E c (π l) J xs| ≤ t)
    (ht : 0 ≤ t) :
    ∑ J ∈ I.powerset, inter E c (π l) J xs ≤ 1 + (2 : ℝ) ^ u * t := by
  classical
  have hempty : (∅ : Finset (Fin u)) ∈ I.powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset I)
  have hcent := (column_expansion E c π xs I hπ hdeg l).2
  have hterm : ∀ J ∈ I.powerset.erase ∅,
      inter E c (π l) J xs ≤ if 2 ≤ J.card then t else 0 := by
    intro J hJ
    rcases Finset.mem_erase.mp hJ with ⟨hne, hmem⟩
    by_cases hlarge : 2 ≤ J.card
    · simp [hlarge]
      exact (abs_le.mp (hmoderate J hlarge)).2
    · have hcardne : J.card ≠ 0 := by
        intro hz
        exact hne (Finset.card_eq_zero.mp hz)
      have hcardpos : 0 < J.card := Nat.pos_of_ne_zero hcardne
      have hcardone : J.card = 1 := by omega
      obtain ⟨i, rflJ⟩ := Finset.card_eq_one.mp hcardone
      have hsub : ({i} : Finset (Fin u)) ⊆ I := by
        rw [← rflJ]
        exact Finset.mem_powerset.mp hmem
      have hi : i ∈ I := hsub (Finset.mem_singleton_self i)
      have hzero := hcent i hi
      simpa [hlarge, rflJ] using (le_of_eq hzero)
  have hsum_erase :
      ∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs ≤
        ((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card * t := by
    calc
      ∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs ≤
          ∑ J ∈ I.powerset.erase ∅, (if 2 ≤ J.card then t else 0) :=
        Finset.sum_le_sum hterm
      _ = ((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card * t := by
        simp [Finset.sum_ite]
  have hcount : ((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card ≤ 2 ^ u := by
    have hsub : (I.powerset.erase ∅).filter (fun J => 2 ≤ J.card) ⊆ I.powerset :=
      (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hIcard : I.card ≤ u := by simpa using Finset.card_le_univ I
    calc
      ((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card ≤ I.powerset.card :=
        Finset.card_le_card hsub
      _ = 2 ^ I.card := Finset.card_powerset I
      _ ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) hIcard
  have hcount' :
      (((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card : ℝ) ≤ (2 : ℝ) ^ u := by
    exact_mod_cast hcount
  have hmul := mul_le_mul_of_nonneg_right hcount' ht
  calc
    ∑ J ∈ I.powerset, inter E c (π l) J xs =
        inter E c (π l) ∅ xs +
          ∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs := by
      symm
      exact Finset.add_sum_erase I.powerset (fun J => inter E c (π l) J xs) hempty
    _ ≤ 1 + ((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card * t := by
      rw [show inter E c (π l) ∅ xs = 1 by simp [inter, hπ l]]
      calc
        1 + ∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs =
            (∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs) + 1 := by ring
        _ ≤ (((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card * t) + 1 := by
          nlinarith [hsum_erase]
        _ = 1 + ((I.powerset.erase ∅).filter (fun J => 2 ≤ J.card)).card * t := by ring
    _ ≤ 1 + (2 : ℝ) ^ u * t := by linarith

lemma prodW_sum_eq_one {N u : ℕ} (τ : Law N) :
    ∑ xs : Fin u → Fin N, prodW τ.w xs = 1 := by
  classical
  change ∑ xs : Fin u → Fin N, ∏ i, τ.w (xs i) = 1
  rw [← Fintype.prod_sum]
  simp [τ.sum_eq_one]

lemma prodW_event_mass_le_one {N u : ℕ} (τ : Law N)
    (p : (Fin u → Fin N) → Prop) :
    ∑ xs : Fin u → Fin N, (if p xs then prodW τ.w xs else 0) ≤ 1 := by
  classical
  calc
    ∑ xs : Fin u → Fin N, (if p xs then prodW τ.w xs else 0) ≤
        ∑ xs : Fin u → Fin N, prodW τ.w xs := by
      apply Finset.sum_le_sum
      intro xs hxs
      split_ifs
      · rfl
      · exact Finset.prod_nonneg (fun i hi => τ.nonneg (xs i))
    _ = 1 := prodW_sum_eq_one τ

lemma posTerm_nonneg_of_nonneg_weights {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin d → Fin N → ℝ)
    (hπ : ∀ l y, 0 ≤ π l y) (I : Finset (Fin u)) (xs : Fin u → Fin N) :
    0 ≤ posTerm E c π I xs := by
  classical
  have hdeg (l : Fin d) (i : Fin u) : 0 ≤ deg E c (π l) (xs i) := by
    unfold deg
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hπ l y) (by unfold hit; split_ifs <;> norm_num)
  have hfactor (l : Fin d) (i : Fin u) (y : Fin N) :
      0 ≤ 1 + acoef E c (π l) (xs i) y := by
    have heq : 1 + acoef E c (π l) (xs i) y =
        hit E c (xs i) y / deg E c (π l) (xs i) := by
      unfold acoef
      ring
    rw [heq]
    have hh : 0 ≤ hit E c (xs i) y := by
      unfold hit
      split_ifs <;> norm_num
    by_cases hz : deg E c (π l) (xs i) = 0
    · simp [hz]
    · exact div_nonneg hh (le_of_lt (lt_of_le_of_ne (hdeg l i) (Ne.symm hz)))
  have hcol (l : Fin d) :
      0 ≤ ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y) := by
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (hπ l y)
    apply Finset.prod_nonneg
    intro i hi
    exact hfactor l i y
  change 0 ≤ ∏ l, ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)
  exact Finset.prod_nonneg (fun l hl => hcol l)

lemma Phi_abs_le_posTerm_sum {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin d → Fin N → ℝ)
    (hπ : ∀ l y, 0 ≤ π l y) (xs : Fin u → Fin N) :
    |Phi E c π xs| ≤ ∑ I : Finset (Fin u), posTerm E c π I xs := by
  classical
  unfold Phi
  calc
    |∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) * posTerm E c π I xs| ≤
        ∑ I : Finset (Fin u), |(-1 : ℝ) ^ (u - I.card) * posTerm E c π I xs| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ I : Finset (Fin u), posTerm E c π I xs := by
      apply Finset.sum_congr rfl
      intro I hI
      simp [abs_mul, abs_of_nonneg
        (posTerm_nonneg_of_nonneg_weights E c π hπ I xs)]

lemma prodW_mul_event_le {N u : ℕ} (τ : Law N)
    (p : (Fin u → Fin N) → Prop) (f : (Fin u → Fin N) → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ xs, 0 ≤ f xs)
    (hpoint : ∀ xs, (∀ i, 0 < τ.w (xs i)) → p xs → f xs ≤ B) :
    ∑ xs : Fin u → Fin N,
      (if p xs then prodW τ.w xs * f xs else 0) ≤ B := by
  classical
  have hw (xs : Fin u → Fin N) : 0 ≤ prodW τ.w xs := by
    unfold prodW
    apply Finset.prod_nonneg
    intro i hi
    exact τ.nonneg (xs i)
  have hterm (xs : Fin u → Fin N) :
      (if p xs then prodW τ.w xs * f xs else 0) ≤
        B * (if p xs then prodW τ.w xs else 0) := by
    by_cases hp : p xs
    · simp only [if_pos hp]
      by_cases hzero : prodW τ.w xs = 0
      · simp [hzero]
      · have hwp : 0 < prodW τ.w xs := lt_of_le_of_ne (hw xs) (Ne.symm hzero)
        have hcoords : ∀ i, 0 < τ.w (xs i) := by
          intro i
          by_contra hnot
          have hz : τ.w (xs i) = 0 := le_antisymm (le_of_not_gt hnot) (τ.nonneg _)
          have hprod : prodW τ.w xs = 0 := by
            unfold prodW
            exact Finset.prod_eq_zero (Finset.mem_univ i) hz
          exact (ne_of_gt hwp) hprod
        have hbnd := hpoint xs hcoords hp
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hbnd (hw xs)
    · simp [hp]
  calc
    ∑ xs : Fin u → Fin N, (if p xs then prodW τ.w xs * f xs else 0) ≤
        ∑ xs : Fin u → Fin N, B * (if p xs then prodW τ.w xs else 0) := by
      apply Finset.sum_le_sum
      intro xs hxs
      exact hterm xs
    _ = B * ∑ xs : Fin u → Fin N, if p xs then prodW τ.w xs else 0 := by
      change (∑ xs ∈ (Finset.univ : Finset (Fin u → Fin N)),
          B * (if p xs then prodW τ.w xs else 0)) =
        B * ∑ xs ∈ (Finset.univ : Finset (Fin u → Fin N)),
          if p xs then prodW τ.w xs else 0
      rw [Finset.univ.mul_sum]
    _ ≤ B := by
      have hm := prodW_event_mass_le_one τ p
      simpa using mul_le_mul_of_nonneg_left hm hB

lemma tendsto_rpow_mul_exp_neg_mul_rpow {ι : Type*} {l : Filter ι}
    {x : ι → ℝ} (hx : Tendsto x l atTop) {p s b : ℝ}
    (hp : 0 < p) (hb : 0 < b) :
    Tendsto (fun k => x k ^ s * Real.exp (-b * x k ^ p)) l (nhds 0) := by
  have hpow : Tendsto (fun y : ℝ => y ^ p) atTop atTop := tendsto_rpow_atTop hp
  have hpowx : Tendsto (fun k => x k ^ p) l atTop := hpow.comp hx
  have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / p) b hb).comp hpowx
  refine Tendsto.congr' ?_ hbase
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
  have heq : (x k ^ p) ^ (s / p) = x k ^ s := by
    calc
      (x k ^ p) ^ (s / p) = x k ^ (p * (s / p)) := by
        rw [← Real.rpow_mul hk.le]
      _ = x k ^ s := by congr 1 <;> field_simp [ne_of_gt hp]
  simp [heq]

lemma posTerm_moderate_pointwise_generic {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin d → Fin N → ℝ)
    (hπsum : ∀ l, ∑ y, π l y = 1) (hπnonneg : ∀ l y, 0 ≤ π l y)
    (xs : Fin u → Fin N) (I : Finset (Fin u)) (t : ℝ) (ht : 0 ≤ t)
    (hmoderate : Moderate E c π t xs) :
    posTerm E c π I xs ≤ Real.exp (((2 : ℝ) ^ u) * d * t) := by
  classical
  have hdeg_nonneg (l : Fin d) (i : Fin u) : 0 ≤ deg E c (π l) (xs i) := by
    unfold deg
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (hπnonneg l y)
    unfold hit
    split_ifs <;> norm_num
  have hfactor_nonneg (l : Fin d) (i : Fin u) (y : Fin N) :
      0 ≤ 1 + acoef E c (π l) (xs i) y := by
    have hratio : 1 + acoef E c (π l) (xs i) y =
        hit E c (xs i) y / deg E c (π l) (xs i) := by
      unfold acoef
      ring
    rw [hratio]
    have hhit : 0 ≤ hit E c (xs i) y := by
      unfold hit
      split_ifs <;> norm_num
    by_cases hz : deg E c (π l) (xs i) = 0
    · simp [hz]
    · exact div_nonneg hhit (le_of_lt (lt_of_le_of_ne (hdeg_nonneg l i) (Ne.symm hz)))
  let col : Fin d → ℝ := fun l =>
    ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)
  have hcol_nonneg (l : Fin d) : 0 ≤ col l := by
    dsimp [col]
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (hπnonneg l y)
    apply Finset.prod_nonneg
    intro i hi
    exact hfactor_nonneg l i y
  by_cases hzero : ∃ l : Fin d, ∃ i ∈ I, deg E c (π l) (xs i) = 0
  · obtain ⟨l₀, i, hi, hz⟩ := hzero
    have hfactor_zero (y : Fin N) : 1 + acoef E c (π l₀) (xs i) y = 0 := by
      simp [acoef, hz]
    have hprod_zero (y : Fin N) :
        ∏ i ∈ I, (1 + acoef E c (π l₀) (xs i) y) = 0 :=
      Finset.prod_eq_zero hi (hfactor_zero y)
    have hcol_zero : col l₀ = 0 := by
      dsimp [col]
      simp_rw [hprod_zero]
      simp
    have hwhole_zero : (∏ l, col l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ l₀) hcol_zero
    change Finset.univ.prod col ≤ Real.exp (((2 : ℝ) ^ u) * d * t)
    rw [hwhole_zero]
    positivity
  · have hdegpos : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i) := by
      intro l i hi
      have hne : deg E c (π l) (xs i) ≠ 0 := by
        intro hz
        exact hzero ⟨l, i, hi, hz⟩
      exact lt_of_le_of_ne (hdeg_nonneg l i) (Ne.symm hne)
    have hcol_le (l : Fin d) : col l ≤ Real.exp (((2 : ℝ) ^ u) * t) := by
      have hcolumns := column_expansion E c π xs I hπsum hdegpos
      have hsum := interaction_powerset_sum_le E c π xs I l t hπsum hdegpos
        (fun J hJ => hmoderate l J hJ) ht
      calc
        col l = ∑ J ∈ I.powerset, inter E c (π l) J xs := hcolumns l |>.1
        _ ≤ 1 + (2 : ℝ) ^ u * t := hsum
        _ ≤ Real.exp (((2 : ℝ) ^ u) * t) := by
          simpa [add_comm] using Real.add_one_le_exp (((2 : ℝ) ^ u) * t)
    have hprod_le : Finset.univ.prod col ≤
        Finset.univ.prod (fun l : Fin d => Real.exp (((2 : ℝ) ^ u) * t)) := by
      exact Finset.prod_le_prod₀
        (s := (Finset.univ : Finset (Fin d)))
        (fun l hl => hcol_nonneg l) (fun l hl => hcol_le l)
    change Finset.univ.prod col ≤ Real.exp (((2 : ℝ) ^ u) * d * t)
    calc
      Finset.univ.prod col ≤
          Finset.univ.prod (fun l : Fin d => Real.exp (((2 : ℝ) ^ u) * t)) := hprod_le
      _ = Real.exp (((2 : ℝ) ^ u) * d * t) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← Real.exp_nat_mul]
        congr 1
        ring

lemma moderate_posTerm_integral_bound {N d u : ℕ}
    (τ : Law N) (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (hπsum : ∀ l, ∑ y, π l y = 1)
    (hπnonneg : ∀ l y, 0 ≤ π l y) (I : Finset (Fin u)) (t : ℝ) (ht : 0 ≤ t) :
    ∑ xs : Fin u → Fin N,
      (if Moderate E c π t xs then prodW τ.w xs * posTerm E c π I xs else 0) ≤
        Real.exp (((2 : ℝ) ^ u) * d * t) := by
  apply prodW_mul_event_le τ (fun xs => Moderate E c π t xs)
    (fun xs => posTerm E c π I xs) (Real.exp (((2 : ℝ) ^ u) * d * t))
  · positivity
  · intro xs
    exact posTerm_nonneg_of_nonneg_weights E c π hπnonneg I xs
  · intro xs hsupport hmod
    exact posTerm_moderate_pointwise_generic E c π hπsum hπnonneg xs I t ht hmod

theorem moderate_posTerm_pointwise_helper (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ (S : InterSetting T k (κ.xs / 4)) (t : ℝ)
        (xs : Fin κ.u → Fin (T.S.N k)) (I : Finset (Fin κ.u)),
        (∀ i, 0 < S.τ.w (xs i)) →
        Moderate (T.S.E k) c (fun l => (S.π l).w) t xs →
        posTerm (T.S.E k) c (fun l => (S.π l).w) I xs ≤
          Real.exp (((2 : ℝ) ^ κ.u) * S.d * t) := by
  classical
  refine Filter.Eventually.of_forall ?_
  intro k S t xs I hsupport hmoderate
  have hdeg_nonneg (l : Fin S.d) (i : Fin κ.u) :
      0 ≤ deg (T.S.E k) c (S.π l).w (xs i) := by
    unfold deg
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg ((S.π l).nonneg y)
    unfold hit
    split_ifs <;> norm_num
  have hfactor_nonneg (l : Fin S.d) (i : Fin κ.u) (y : Fin (T.S.N k)) :
      0 ≤ 1 + acoef (T.S.E k) c (S.π l).w (xs i) y := by
    have hratio :
        1 + acoef (T.S.E k) c (S.π l).w (xs i) y =
          hit (T.S.E k) c (xs i) y / deg (T.S.E k) c (S.π l).w (xs i) := by
      unfold acoef
      ring
    rw [hratio]
    have hhit : 0 ≤ hit (T.S.E k) c (xs i) y := by
      unfold hit
      split_ifs <;> norm_num
    by_cases hz : deg (T.S.E k) c (S.π l).w (xs i) = 0
    · simp [hz]
    · have hp : 0 < deg (T.S.E k) c (S.π l).w (xs i) :=
        lt_of_le_of_ne (hdeg_nonneg l i) (Ne.symm hz)
      exact div_nonneg hhit hp.le
  let col : Fin S.d → ℝ := fun l =>
    ∑ y, (S.π l).w y *
      ∏ i ∈ I, (1 + acoef (T.S.E k) c (S.π l).w (xs i) y)
  have hcol_nonneg (l : Fin S.d) : 0 ≤ col l := by
    dsimp [col]
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg ((S.π l).nonneg y)
    apply Finset.prod_nonneg
    intro i hi
    exact hfactor_nonneg l i y
  by_cases hd : S.d = 0
  · change (∏ l, col l) ≤ Real.exp (((2 : ℝ) ^ κ.u) * S.d * t)
    simp [hd]
  · have hdpos : 0 < S.d := Nat.pos_of_ne_zero hd
    by_cases hzero : ∃ l : Fin S.d, ∃ i ∈ I,
        deg (T.S.E k) c (S.π l).w (xs i) = 0
    · obtain ⟨l₀, i, hi, hz⟩ := hzero
      have hfactor_zero (y : Fin (T.S.N k)) :
          1 + acoef (T.S.E k) c (S.π l₀).w (xs i) y = 0 := by
        simp [acoef, hz]
      have hprod_zero (y : Fin (T.S.N k)) :
          ∏ i ∈ I, (1 + acoef (T.S.E k) c (S.π l₀).w (xs i) y) = 0 :=
        Finset.prod_eq_zero hi (hfactor_zero y)
      have hcol_zero : col l₀ = 0 := by
        dsimp [col]
        simp_rw [hprod_zero]
        simp
      have hwhole_zero : (∏ l, col l) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l₀) hcol_zero
      change Finset.univ.prod col ≤ Real.exp (((2 : ℝ) ^ κ.u) * S.d * t)
      rw [hwhole_zero]
      positivity
    · have hdegpos : ∀ l i, i ∈ I →
          0 < deg (T.S.E k) c (S.π l).w (xs i) := by
        intro l i hi
        have hne : deg (T.S.E k) c (S.π l).w (xs i) ≠ 0 := by
          intro hz
          exact hzero ⟨l, i, hi, hz⟩
        exact lt_of_le_of_ne (hdeg_nonneg l i) (Ne.symm hne)
      have hP : 0 < κ.P := by
        have hp := hκ.P_big.2
        rw [hκ.Ac_eq] at hp
        omega
      have hR : 0 < κ.R := by
        rw [hκ.R_eq]
        exact pow_pos hP 2
      have hL : 0 < κ.L := by
        rw [hκ.L_eq]
        exact Nat.mul_pos (by decide) hR
      have hL2pos : 0 < κ.L ^ 2 := by
        rw [pow_two]
        exact Nat.mul_pos hL hL
      have hL2 : 1 ≤ κ.L ^ 2 := by omega
      have huLarge := hκ.u_rng.2
      have hu2 : 2 ≤ κ.u := by omega
      have ht : 0 ≤ t := by
        by_contra ht
        have htneg : t < 0 := lt_of_not_ge ht
        let l : Fin S.d := ⟨0, hdpos⟩
        let i₀ : Fin κ.u := ⟨0, by omega⟩
        let i₁ : Fin κ.u := ⟨1, by omega⟩
        let J : Finset (Fin κ.u) := {i₀, i₁}
        have hJ : 2 ≤ J.card := by simp [J, i₀, i₁]
        have habs := abs_nonneg (inter (T.S.E k) c (S.π l).w J xs)
        have hbound := hmoderate l J hJ
        linarith
      have hπnorm : ∀ l, ∑ y, (S.π l).w y = 1 := fun l => (S.π l).sum_eq_one
      have hcol_le (l : Fin S.d) : col l ≤
          Real.exp (((2 : ℝ) ^ κ.u) * t) := by
        have hcolumns := column_expansion (T.S.E k) c
          (fun l => (S.π l).w) xs I hπnorm hdegpos
        have hsum := interaction_powerset_sum_le (T.S.E k) c
          (fun l => (S.π l).w) xs I l t hπnorm hdegpos
          (fun J hJ => hmoderate l J hJ) ht
        calc
          col l = ∑ J ∈ I.powerset, inter (T.S.E k) c (S.π l).w J xs :=
            (hcolumns l).1
          _ ≤ 1 + (2 : ℝ) ^ κ.u * t := hsum
          _ ≤ Real.exp (((2 : ℝ) ^ κ.u) * t) := by
            simpa [add_comm] using Real.add_one_le_exp (((2 : ℝ) ^ κ.u) * t)
      have hprod_le : Finset.univ.prod col ≤
          Finset.univ.prod (fun l : Fin S.d => Real.exp (((2 : ℝ) ^ κ.u) * t)) := by
        exact Finset.prod_le_prod₀
          (s := (Finset.univ : Finset (Fin S.d)))
          (fun l hl => hcol_nonneg l) (fun l hl => hcol_le l)
      change Finset.univ.prod col ≤ Real.exp (((2 : ℝ) ^ κ.u) * S.d * t)
      calc
        Finset.univ.prod col ≤
            Finset.univ.prod (fun l : Fin S.d => Real.exp (((2 : ℝ) ^ κ.u) * t)) := hprod_le
        _ = Real.exp (((2 : ℝ) ^ κ.u) * S.d * t) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← Real.exp_nat_mul]
          congr 1
          ring

end HypercubeRamsey.S12

namespace HypercubeRamsey.S12.Lane_q_s12_mom

open Classical
open scoped BigOperators

/-- The alternating sum over supersets of `U` vanishes unless `U` is the full index set. -/
lemma alternating_superset_sum {α : Type*} [Fintype α] [DecidableEq α]
    (U : Finset α) :
    (∑ I : Finset α, if U ⊆ I then (-1 : ℝ) ^ (Fintype.card α - I.card) else 0) =
      if U = Finset.univ then 1 else 0 := by
  classical
  let V : Finset α := Finset.univ \ U
  have hfilter :
      (∑ I : Finset α, if U ⊆ I then (-1 : ℝ) ^ (Fintype.card α - I.card) else 0) =
        ∑ I ∈ (Finset.univ : Finset (Finset α)).filter (fun I => U ⊆ I),
          (-1 : ℝ) ^ (Fintype.card α - I.card) := by
    simp only [Finset.sum_filter]
  have hreindex :
      (∑ I ∈ (Finset.univ : Finset (Finset α)).filter (fun I => U ⊆ I),
        (-1 : ℝ) ^ (Fintype.card α - I.card)) =
        ∑ J ∈ V.powerset, (-1 : ℝ) ^ (V.card - J.card) := by
    classical
    apply Finset.sum_bij'
      (fun I _ => I \ U)
      (fun J _ => U ∪ J)
    · intro I hI
      have hUI : U ⊆ I := (Finset.mem_filter.mp hI).2
      change I \ U ∈ V.powerset
      rw [Finset.mem_powerset]
      intro x hx
      have hxI : x ∈ I := (Finset.mem_sdiff.mp hx).1
      have hxU : x ∉ U := (Finset.mem_sdiff.mp hx).2
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxU⟩
    · intro J hJ
      have hU : U ⊆ U ∪ J := Finset.subset_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩
    · intro I hI
      have hUI : U ⊆ I := (Finset.mem_filter.mp hI).2
      have hEq : U ∪ (I \ U) = I := Finset.union_sdiff_of_subset hUI
      simpa [hEq]
    · intro J hJ
      have hJV : J ⊆ V := Finset.mem_powerset.mp hJ
      have hJU : Disjoint J U := by
        rw [Finset.disjoint_left]
        intro x hxJ hxU
        have hxV := hJV hxJ
        exact (Finset.mem_sdiff.mp hxV).2 hxU
      exact Finset.union_sdiff_cancel_left hJU.symm
    · intro I hI
      have hUI : U ⊆ I := (Finset.mem_filter.mp hI).2
      have hcardU : U.card ≤ I.card := Finset.card_le_card hUI
      have hcardI : I.card ≤ Fintype.card α := by
        simpa using Finset.card_le_univ I
      have hcardV : V.card = Fintype.card α - U.card := by
        dsimp [V]
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ]
      have hcardJ : (I \ U).card = I.card - U.card :=
        Finset.card_sdiff_of_subset hUI
      rw [hcardV, hcardJ]
      congr 1
      omega
  have hpower :
      (∑ J ∈ V.powerset, (-1 : ℝ) ^ (V.card - J.card)) =
        ∏ x ∈ V, (1 + (-1 : ℝ)) := by
    classical
    symm
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro J hJ
    have hJV : J ⊆ V := Finset.mem_powerset.mp hJ
    rw [Finset.prod_const_one, Finset.prod_const,
      Finset.card_sdiff_of_subset hJV]
    simp
  have hVempty : V = ∅ ↔ U = Finset.univ := by
    constructor
    · intro hV
      apply Finset.eq_univ_iff_forall.mpr
      intro x
      by_contra hxU
      have hxV : x ∈ V := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxU⟩
      simpa [hV] using hxV
    · intro hU
      simp [V, hU]
  rw [hfilter, hreindex, hpower]
  by_cases hV : V = ∅
  · have hU : U = Finset.univ := hVempty.mp hV
    rw [hV]
    simp [hU]
  · have hVne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hV
    obtain ⟨x, hx⟩ := hVne
    rw [show 1 + (-1 : ℝ) = 0 by ring, Finset.prod_eq_zero hx]
    have hUne : U ≠ Finset.univ := fun hU => hV (hVempty.mpr hU)
    rw [if_neg hUne]
    rfl

/-- After the singleton interactions vanish, a column is one plus its higher interactions. -/
lemma column_sum_over_large_interactions {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N)
    (I : Finset (Fin u)) (l : Fin d)
    (hπ : ∀ l, ∑ y, π l y = 1)
    (hdeg : ∀ l i, i ∈ I → 0 < deg E c (π l) (xs i)) :
    (∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
      1 + ∑ J ∈ I.powerset.filter (fun J => 2 ≤ J.card),
        inter E c (π l) J xs := by
  classical
  let p : Finset (Fin u) → Prop := fun J => 2 ≤ J.card
  have hempty : (∅ : Finset (Fin u)) ∈ I.powerset :=
    Finset.mem_powerset.mpr (Finset.empty_subset I)
  have hcent := (column_expansion E c π xs I hπ hdeg l).2
  have hsmall (J : Finset (Fin u)) (hJ : J ∈ I.powerset.erase ∅)
      (hnot : ¬ p J) : inter E c (π l) J xs = 0 := by
    have hne : J ≠ ∅ := (Finset.mem_erase.mp hJ).1
    have hmem : J ∈ I.powerset := (Finset.mem_erase.mp hJ).2
    have hcardne : J.card ≠ 0 := by
      intro hz
      exact hne (Finset.card_eq_zero.mp hz)
    have hcardpos : 0 < J.card := Nat.pos_of_ne_zero hcardne
    have hcardone : J.card = 1 := by omega
    obtain ⟨i, rflJ⟩ := Finset.card_eq_one.mp hcardone
    have hsub : ({i} : Finset (Fin u)) ⊆ I := by
      rw [← rflJ]
      exact Finset.mem_powerset.mp hmem
    rw [rflJ]
    exact hcent i (hsub (Finset.mem_singleton_self i))
  have hlarge_subset :
      I.powerset.filter p ⊆ I.powerset.erase ∅ := by
    intro J hJ
    have hJP := (Finset.mem_filter.mp hJ).1
    have hsize := (Finset.mem_filter.mp hJ).2
    have hne : J ≠ ∅ := by
      intro hz
      subst J
      simp [p] at hsize
    exact Finset.mem_erase.mpr ⟨hne, hJP⟩
  have hsum_erase :
      (∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs) =
        ∑ J ∈ I.powerset.filter p, inter E c (π l) J xs := by
    symm
    apply Finset.sum_subset hlarge_subset
    intro J hJ hnot
    apply hsmall J hJ
    intro hp
    exact hnot (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hJ).2, hp⟩)
  calc
    _ = ∑ J ∈ I.powerset, inter E c (π l) J xs :=
      (column_expansion E c π xs I hπ hdeg l).1
    _ = inter E c (π l) ∅ xs +
          ∑ J ∈ I.powerset.erase ∅, inter E c (π l) J xs := by
      symm
      exact Finset.add_sum_erase I.powerset
        (fun J => inter E c (π l) J xs) hempty
    _ = 1 + ∑ J ∈ I.powerset.filter p, inter E c (π l) J xs := by
      rw [show inter E c (π l) ∅ xs = 1 by simp [inter, hπ l], hsum_erase]

lemma alternating_selected_interaction {u : ℕ}
    (U : Finset (Fin u)) (P : ℝ) :
    (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
      (if U ⊆ I then P else 0)) = if U = Finset.univ then P else 0 := by
  classical
  calc
    _ = P * ∑ I : Finset (Fin u),
        (if U ⊆ I then (-1 : ℝ) ^ (u - I.card) else 0) := by
      rw [Finset.univ.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      by_cases hUI : U ⊆ I <;> simp [hUI] <;> ring
    _ = P * (if U = Finset.univ then 1 else 0) := by
      have hsum := alternating_superset_sum (α := Fin u) U
      simpa [Fintype.card_fin] using congrArg (fun x : ℝ => P * x) hsum
    _ = _ := by by_cases hU : U = Finset.univ <;> simp [hU]

lemma product_interactions_expansion {d : ℕ} {α : Type*}
    [Fintype α] [DecidableEq α]
    (M : Fin d → α → ℝ) (opts : Finset α) :
    (∏ l : Fin d, (1 + ∑ J ∈ opts, M l J)) =
      ∑ K : Finset (Fin d),
        ∑ f : (∀ l : {l // l ∈ K}, α),
          (if ∀ l, f l ∈ opts then ∏ l, M l.1 (f l) else 0) := by
  classical
  calc
    (∏ l : Fin d, (1 + ∑ J ∈ opts, M l J)) =
        ∑ K : Finset (Fin d), ∏ l ∈ K, ∑ J ∈ opts, M l J := by
      simpa using
        (Finset.prod_one_add (s := (Finset.univ : Finset (Fin d)))
          (f := fun l => ∑ J ∈ opts, M l J))
    _ = ∑ K : Finset (Fin d),
        ∑ f : (∀ l : {l // l ∈ K}, α),
          (if ∀ l, f l ∈ opts then ∏ l, M l.1 (f l) else 0) := by
      apply Finset.sum_congr rfl
      intro K hK
      calc
        (∏ l ∈ K, ∑ J ∈ opts, M l J) =
            ∏ l : {l // l ∈ K}, ∑ J ∈ opts, M l.1 J := by
          exact (Finset.prod_coe_sort K (fun l => ∑ J ∈ opts, M l J)).symm
        _ = ∑ f ∈ Fintype.piFinset (fun _ : {l // l ∈ K} => opts),
              ∏ l, M l.1 (f l) := by
          exact Finset.prod_univ_sum
            (fun _ : {l // l ∈ K} => opts) (fun l J => M l.1 J)
        _ = ∑ f : (∀ l : {l // l ∈ K}, α),
              (if ∀ l, f l ∈ opts then ∏ l, M l.1 (f l) else 0) := by
          have hpi :
              Fintype.piFinset (fun _ : {l // l ∈ K} => opts) =
                Finset.univ.filter (fun f : (∀ l : {l // l ∈ K}, α) =>
                  ∀ l, f l ∈ opts) := by
            ext f
            simp [Fintype.mem_piFinset]
          rw [hpi, Finset.sum_filter]

def selected_interaction_union {d u : ℕ} (K : Finset (Fin d))
    (f : ∀ l : {l // l ∈ K}, Finset (Fin u)) : Finset (Fin u) :=
  Finset.univ.biUnion f

lemma selected_alternating_sum {u d : ℕ} (K : Finset (Fin d))
    (f : ∀ l : {l // l ∈ K}, Finset (Fin u)) (P : ℝ) :
    (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
      (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then P else 0)) =
        (if (∀ l, 2 ≤ (f l).card) ∧
            selected_interaction_union K f = Finset.univ then P else 0) := by
  classical
  have hvalid (I : Finset (Fin u)) :
      (∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card)) ↔
        (∀ l, 2 ≤ (f l).card) ∧ selected_interaction_union K f ⊆ I := by
    constructor
    · intro hf
      refine ⟨fun l => (Finset.mem_filter.mp (hf l)).2, ?_⟩
      change Finset.univ.biUnion f ⊆ I
      rw [Finset.biUnion_subset_iff_forall_subset]
      intro l hl
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp (hf l)).1
    · rintro ⟨hsize, hunion⟩ l
      change Finset.univ.biUnion f ⊆ I at hunion
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, hsize l⟩
      exact (Finset.biUnion_subset_iff_forall_subset.mp hunion) l (Finset.mem_univ l)
  have hsum :
      (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
        (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then P else 0)) =
      ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
        (if (∀ l, 2 ≤ (f l).card) ∧ selected_interaction_union K f ⊆ I then P else 0) := by
    apply Finset.sum_congr rfl
    intro I hI
    have hh := hvalid I
    have hif :
        (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then P else 0) =
          (if (∀ l, 2 ≤ (f l).card) ∧ selected_interaction_union K f ⊆ I
            then P else 0) :=
      if_congr hh rfl rfl
    exact congrArg (fun x : ℝ => (-1 : ℝ) ^ (u - I.card) * x) hif
  rw [hsum]
  by_cases hsize : ∀ l : {l // l ∈ K}, 2 ≤ (f l).card
  · calc
      (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          (if ((∀ l : {l // l ∈ K}, 2 ≤ (f l).card) ∧
              selected_interaction_union K f ⊆ I) then P else 0)) =
        ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          (if selected_interaction_union K f ⊆ I then P else 0) := by
            apply Finset.sum_congr rfl
            intro I hI
            simp [hsize]
      _ = if selected_interaction_union K f = Finset.univ then P else 0 :=
        alternating_selected_interaction _ P
      _ = if (∀ l, 2 ≤ (f l).card) ∧
          selected_interaction_union K f = Finset.univ then P else 0 := by
            simp [hsize]
  · have hsize' :
        ¬ (∀ (a : Fin d) (ha : a ∈ K), 2 ≤ (f ⟨a, ha⟩).card) := by
      intro h
      apply hsize
      intro l
      exact h l.1 l.2
    simp [hsize']

set_option maxHeartbeats 1000000 in
lemma Phi_cover_expansion {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N)
    (hπ : ∀ l, ∑ y, π l y = 1)
    (hdeg : ∀ l i, 0 < deg E c (π l) (xs i)) :
    Phi E c π xs =
      ∑ K : Finset (Fin d),
        ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
          (if (∀ l, 2 ≤ (f l).card) ∧
              selected_interaction_union K f = Finset.univ then
            ∏ l, inter E c (π l.1) (f l) xs else 0) := by
  classical
  have hcolumns (I : Finset (Fin u)) :
      (∏ l : Fin d,
        ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
        ∑ K : Finset (Fin d),
          ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
            (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then
              ∏ l, inter E c (π l.1) (f l) xs else 0) := by
    have hcol (l : Fin d) := column_sum_over_large_interactions E c π xs I l hπ
      (fun l i hi => hdeg l i)
    have hprod := product_interactions_expansion
      (fun l J => inter E c (π l) J xs)
      (I.powerset.filter (fun J => 2 ≤ J.card))
    calc
      (∏ l : Fin d,
        ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)) =
          ∏ l : Fin d,
            (1 + ∑ J ∈ I.powerset.filter (fun J => 2 ≤ J.card),
              inter E c (π l) J xs) := by
                apply Finset.prod_congr rfl
                intro l hl
                exact hcol l
      _ = _ := hprod
  unfold Phi posTerm
  calc
    _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∑ K : Finset (Fin d),
            ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
              (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then
                ∏ l, inter E c (π l.1) (f l) xs else 0) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [← hcolumns I]
    _ = ∑ K : Finset (Fin d),
          ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
            ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
              (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then
                ∏ l, inter E c (π l.1) (f l) xs else 0) := by
      calc
        _ = ∑ I : Finset (Fin u),
              ∑ K : Finset (Fin d),
                ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
                  (-1 : ℝ) ^ (u - I.card) *
                    (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then
                      ∏ l, inter E c (π l.1) (f l) xs else 0) := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [Finset.univ.mul_sum]
          apply Finset.sum_congr rfl
          intro K hK
          rw [Finset.univ.mul_sum]
        _ = ∑ K : Finset (Fin d),
              ∑ I : Finset (Fin u),
                ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
                  (-1 : ℝ) ^ (u - I.card) *
                    (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then
                      ∏ l, inter E c (π l.1) (f l) xs else 0) := by
          rw [Finset.sum_comm]
        _ = ∑ K : Finset (Fin d),
              ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
                ∑ I : Finset (Fin u),
                  (-1 : ℝ) ^ (u - I.card) *
                    (if ∀ l, f l ∈ I.powerset.filter (fun J => 2 ≤ J.card) then
                      ∏ l, inter E c (π l.1) (f l) xs else 0) := by
          apply Finset.sum_congr rfl
          intro K hK
          rw [Finset.sum_comm]
    _ = ∑ K : Finset (Fin d),
          ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
            (if (∀ l, 2 ≤ (f l).card) ∧
                selected_interaction_union K f = Finset.univ then
              ∏ l, inter E c (π l.1) (f l) xs else 0) := by
      apply Finset.sum_congr rfl
      intro K hK
      apply Finset.sum_congr rfl
      intro f hf
      simpa only [Subtype.forall] using selected_alternating_sum K f
        (∏ l, inter E c (π l.1) (f l) xs)

lemma Phi_cover_abs_bound {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N)
    (hπ : ∀ l, ∑ y, π l y = 1)
    (hdeg : ∀ l i, 0 < deg E c (π l) (xs i)) :
    |Phi E c π xs| ≤
      ∑ K : Finset (Fin d),
        ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
          (if (∀ l, 2 ≤ (f l).card) ∧
              selected_interaction_union K f = Finset.univ then
            |∏ l, inter E c (π l.1) (f l) xs| else 0) := by
  classical
  rw [Phi_cover_expansion E c π xs hπ hdeg]
  calc
    |∑ K : Finset (Fin d),
        ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
          (if (∀ l, 2 ≤ (f l).card) ∧
              selected_interaction_union K f = Finset.univ then
            ∏ l, inter E c (π l.1) (f l) xs else 0)| ≤
      ∑ K : Finset (Fin d),
        |∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
          (if (∀ l, 2 ≤ (f l).card) ∧
              selected_interaction_union K f = Finset.univ then
            ∏ l, inter E c (π l.1) (f l) xs else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K : Finset (Fin d),
        ∑ f : (∀ l : {l // l ∈ K}, Finset (Fin u)),
          |if (∀ l, 2 ≤ (f l).card) ∧
              selected_interaction_union K f = Finset.univ then
            ∏ l, inter E c (π l.1) (f l) xs else 0| := by
      apply Finset.sum_le_sum
      intro K hK
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro K hK
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hsel :
          (∀ l, 2 ≤ (f l).card) ∧ selected_interaction_union K f = Finset.univ
      · simp [hsel]
      · have hsel' :
            ¬ ((∀ (a : Fin d) (ha : a ∈ K), 2 ≤ (f ⟨a, ha⟩).card) ∧
                selected_interaction_union K f = Finset.univ) := by
          intro h'
          apply hsel
          exact ⟨fun l => h'.1 l.1 l.2, h'.2⟩
        simp [hsel, hsel']

lemma low_selection_count_bound {d u L n : ℕ} (hd : d ≤ n) (hn : 1 ≤ n) :
    (∑ K : Finset (Fin d),
      if K.card ≤ L then (2 ^ u) ^ K.card else 0) ≤
        (L + 1) * n ^ L * (2 ^ u) ^ L := by
  classical
  have hdecomp :
      (∑ K : Finset (Fin d),
        if K.card ≤ L then (2 ^ u) ^ K.card else 0) =
        ∑ z ∈ Finset.sigma (Finset.range (d + 1))
          (fun r => (Finset.univ : Finset (Fin d)).powersetCard r),
            if z.2.card ≤ L then (2 ^ u) ^ z.2.card else 0 := by
    apply Finset.sum_bij'
      (fun K _ => (⟨K.card, K⟩ : Sigma fun r : ℕ => Finset (Fin d)))
      (fun z _ => z.2)
    · intro K hK
      apply Finset.mem_sigma.mpr
      refine ⟨?_, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, rfl⟩⟩
      simp only [Finset.mem_range]
      have hKd : K.card ≤ d := by simpa using Finset.card_le_univ K
      exact Nat.lt_succ_of_le hKd
    · intro z hz
      exact Finset.mem_univ z.2
    · intro K hK
      rfl
    · intro z hz
      cases z with
      | mk r K =>
        simp only [Finset.mem_sigma] at hz
        have hcard := (Finset.mem_powersetCard.mp hz.2).2
        have hcard' : K.card = r := hcard
        subst r
        rfl
    · intro K hK
      rfl
  have hinner (r : ℕ) (hr : r ≤ L) :
      (∑ K ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
        if K.card ≤ L then (2 ^ u) ^ K.card else 0) ≤
          n ^ L * (2 ^ u) ^ L := by
    have hchoose : Nat.choose d r ≤ n ^ L := by
      calc
        Nat.choose d r ≤ d ^ r := Nat.choose_le_pow d r
        _ ≤ n ^ r := Nat.pow_le_pow_left hd r
        _ ≤ n ^ L := Nat.pow_le_pow_right hn hr
    have hpcount :
        ((Finset.univ : Finset (Fin d)).powersetCard r).card = Nat.choose d r := by
      simp [Finset.card_powersetCard]
    have hbase : 1 ≤ 2 ^ u := Nat.one_le_pow u 2 (by decide)
    have hpow : (2 ^ u) ^ r ≤ (2 ^ u) ^ L := Nat.pow_le_pow_right hbase hr
    calc
      _ = ((Finset.univ : Finset (Fin d)).powersetCard r).card * (2 ^ u) ^ r := by
        calc
          _ = ∑ K ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
                (2 ^ u) ^ r := by
              apply Finset.sum_congr rfl
              intro K hK
              have hKr : K.card = r := (Finset.mem_powersetCard.mp hK).2
              simp [hKr, hr]
          _ = _ := by simp
      _ ≤ n ^ L * (2 ^ u) ^ L := by
        rw [hpcount]
        exact Nat.mul_le_mul hchoose hpow
  have hfilterCount :
      ((Finset.range (d + 1)).filter (fun r => r ≤ L)).card ≤ L + 1 := by
    calc
      ((Finset.range (d + 1)).filter (fun r => r ≤ L)).card ≤
          (Finset.range (L + 1)).card := by
        have hsubset :
            (Finset.range (d + 1)).filter (fun r => r ≤ L) ⊆ Finset.range (L + 1) := by
          intro r hr
          have hrl := (Finset.mem_filter.mp hr).2
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hrl)
        exact Finset.card_le_card hsubset
      _ = L + 1 := by simp
  rw [hdecomp]
  rw [Finset.sum_sigma]
  calc
    _ ≤ ∑ r ∈ Finset.range (d + 1),
          (if r ≤ L then n ^ L * (2 ^ u) ^ L else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hrl : r ≤ L
      · simpa [hrl] using hinner r hrl
      · rw [if_neg hrl]
        have hzero :
            (∑ K ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
              if K.card ≤ L then (2 ^ u) ^ K.card else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro K hK
          have hKr : K.card = r := (Finset.mem_powersetCard.mp hK).2
          have hnot : ¬ K.card ≤ L := by omega
          simp [hnot]
        rw [hzero]
    _ = ((Finset.range (d + 1)).filter (fun r => r ≤ L)).card *
          (n ^ L * (2 ^ u) ^ L) := by simp [Finset.sum_ite]
    _ ≤ (L + 1) * n ^ L * (2 ^ u) ^ L := by
      calc
        _ ≤ (L + 1) * (n ^ L * (2 ^ u) ^ L) := Nat.mul_le_mul_right _ hfilterCount
        _ = _ := by ring

lemma sum_finset_sigma_card {d : ℕ} (F : Finset (Fin d) → ℝ) :
    (∑ K : Finset (Fin d), F K) =
      ∑ z ∈ Finset.sigma (Finset.range (d + 1))
        (fun r => (Finset.univ : Finset (Fin d)).powersetCard r), F z.2 := by
  classical
  apply Finset.sum_bij'
    (fun K _ => (⟨K.card, K⟩ : Sigma fun r : ℕ => Finset (Fin d)))
    (fun z _ => z.2)
  · intro K hK
    apply Finset.mem_sigma.mpr
    refine ⟨?_, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ K, rfl⟩⟩
    simp only [Finset.mem_range]
    have hKd : K.card ≤ d := by simpa using Finset.card_le_univ K
    exact Nat.lt_succ_of_le hKd
  · intro z hz
    exact Finset.mem_univ z.2
  · intro K hK
    rfl
  · intro z hz
    cases z with
    | mk r K =>
      simp only [Finset.mem_sigma] at hz
      have hcard := (Finset.mem_powersetCard.mp hz.2).2
      have hcard' : K.card = r := by simpa using hcard
      subst r
      rfl
  · intro K hK
    rfl

lemma high_selection_weight_bound {d L : ℕ} (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : (d : ℝ) * a ≤ 1) :
    (∑ K : Finset (Fin d), if L < K.card then a ^ K.card else 0) ≤
      ((d + 1 : ℕ) : ℝ) * ((d : ℝ) * a) ^ (L + 1) := by
  classical
  rw [sum_finset_sigma_card, Finset.sum_sigma]
  calc
    _ ≤ ∑ r ∈ Finset.range (d + 1), ((d : ℝ) * a) ^ (L + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases hLr : L < r
      · have hsum :
            (∑ K ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
              if L < K.card then a ^ K.card else 0) =
              ((Finset.univ : Finset (Fin d)).powersetCard r).card * a ^ r := by
          calc
            _ = ∑ K ∈ (Finset.univ : Finset (Fin d)).powersetCard r, a ^ r := by
              apply Finset.sum_congr rfl
              intro K hK
              have hKr : K.card = r := (Finset.mem_powersetCard.mp hK).2
              simp [hKr, hLr]
            _ = _ := by simp
        have hchoose :
            (((Finset.univ : Finset (Fin d)).powersetCard r).card : ℝ) ≤ (d : ℝ) ^ r := by
          rw [Finset.card_powersetCard, Finset.card_univ]
          rw [Fintype.card_fin]
          exact_mod_cast Nat.choose_le_pow d r
        have hchooseMul :
            (((Finset.univ : Finset (Fin d)).powersetCard r).card : ℝ) * a ^ r ≤
              ((d : ℝ) * a) ^ r := by
          calc
            _ ≤ (d : ℝ) ^ r * a ^ r := mul_le_mul_of_nonneg_right hchoose (pow_nonneg ha0 _)
            _ = ((d : ℝ) * a) ^ r := by rw [mul_pow]
        have hpow : ((d : ℝ) * a) ^ r ≤ ((d : ℝ) * a) ^ (L + 1) :=
          pow_le_pow_of_le_one (mul_nonneg (by positivity) ha0) ha1 (by omega)
        simpa [hLr] using hsum.trans_le (hchooseMul.trans hpow)
      · have hzero :
            (∑ s ∈ (Finset.univ : Finset (Fin d)).powersetCard r,
              if L < (⟨r, s⟩ : Sigma fun n : ℕ => Finset (Fin d)).2.card then
                a ^ (⟨r, s⟩ : Sigma fun n : ℕ => Finset (Fin d)).2.card else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro s hs
          have hscard : s.card = r := (Finset.mem_powersetCard.mp hs).2
          have hnot : ¬ L < s.card := by omega
          change (if L < s.card then a ^ s.card else 0) = 0
          simp [hnot]
        rw [hzero]
        exact pow_nonneg (mul_nonneg (by positivity) ha0) _
    _ = ((d + 1 : ℕ) : ℝ) * ((d : ℝ) * a) ^ (L + 1) := by simp

lemma selected_cover_has_large_interaction {d u L : ℕ}
    (hL : 0 < L) (hu : 10 * L ^ 2 < u)
    (K : Finset (Fin d))
    (f : ∀ l : {l // l ∈ K}, Finset (Fin u))
    (hK : K.card ≤ L)
    (hcover : selected_interaction_union K f = Finset.univ) :
    ∃ l : {l // l ∈ K}, 4 * L ≤ (f l).card := by
  classical
  by_contra h
  have hsmall (l : {l // l ∈ K}) : (f l).card ≤ 4 * L - 1 := by
    have hnot : ¬ 4 * L ≤ (f l).card := by
      intro hl
      exact h ⟨l, hl⟩
    omega
  have hsum :
      (∑ l : {l // l ∈ K}, (f l).card) ≤ K.card * (4 * L - 1) := by
    calc
      _ = ∑ l ∈ (Finset.univ : Finset {l // l ∈ K}), (f l).card := by
        rfl
      _ ≤ ∑ l ∈ (Finset.univ : Finset {l // l ∈ K}), (4 * L - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        exact hsmall l
      _ = K.card * (4 * L - 1) := by simp
  have hcardUnion :
      (selected_interaction_union K f).card ≤
        ∑ l : {l // l ∈ K}, (f l).card := by
    simpa only [selected_interaction_union, Finset.sum_attach] using
      (Finset.card_biUnion_le :
        (Finset.univ.biUnion f).card ≤
          ∑ l ∈ (Finset.univ : Finset {l // l ∈ K}), (f l).card)
  have hbound : K.card * (4 * L - 1) < u := by
    have hcoeff : 4 * L - 1 < 4 * L := by omega
    have hmul : L * (4 * L - 1) < L * (4 * L) :=
      Nat.mul_lt_mul_of_pos_left hcoeff hL
    have hquart : 4 * L ^ 2 < 10 * L ^ 2 := by
      have hsq : 0 < L ^ 2 := Nat.pow_pos hL
      omega
    calc
      K.card * (4 * L - 1) ≤ L * (4 * L - 1) := Nat.mul_le_mul_right _ hK
      _ < L * (4 * L) := hmul
      _ = 4 * L ^ 2 := by ring
      _ < 10 * L ^ 2 := hquart
      _ < u := hu
  have : u ≤ K.card * (4 * L - 1) := by
    calc
      u = (selected_interaction_union K f).card := by rw [hcover]; simp
      _ ≤ ∑ l : {l // l ∈ K}, (f l).card := hcardUnion
      _ ≤ K.card * (4 * L - 1) := hsum
  omega

lemma selected_interaction_product_abs_le {N d u : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N)
    (K : Finset (Fin d))
    (f : ∀ l : {l // l ∈ K}, Finset (Fin u))
    (l₀ : {l // l ∈ K}) (t : ℝ) (ht : t ≤ 1)
    (hsize : ∀ l, 2 ≤ (f l).card)
    (hmoderate : Moderate E c π t xs) :
    |∏ l : {l // l ∈ K}, inter E c (π l.1) (f l) xs| ≤
      |inter E c (π l₀.1) (f l₀) xs| := by
  classical
  let g : {l // l ∈ K} → ℝ := fun l => |inter E c (π l.1) (f l) xs|
  have hprod :
      ∏ l : {l // l ∈ K}, g l ≤
        ∏ l : {l // l ∈ K}, if l = l₀ then g l else 1 := by
    apply Finset.prod_le_prod₀
    · intro l hl
      exact abs_nonneg _
    · intro l hl
      by_cases hEq : l = l₀
      · simp [hEq]
      · simp only [if_neg hEq]
        have hbound := hmoderate l.1 (f l) (hsize l)
        exact hbound.trans ht
  have hR :
      (∏ l : {l // l ∈ K}, if l = l₀ then g l else 1) = g l₀ := by
    simp
  calc
    |∏ l : {l // l ∈ K}, inter E c (π l.1) (f l) xs| =
        ∏ l : {l // l ∈ K}, g l := by simp [g, Finset.abs_prod]
    _ ≤ ∏ l : {l // l ∈ K}, if l = l₀ then g l else 1 := hprod
    _ = |inter E c (π l₀.1) (f l₀) xs| := by simpa [g] using hR

end HypercubeRamsey.S12.Lane_q_s12_mom
