import HypercubeRamsey.S05.History
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.Height.Device
import HypercubeRamsey.S05.Centres_sol_s05_centres_support
import HypercubeRamsey.Tools.Concentration
import HypercubeRamsey.S05.History_sol_s05_1f_scales

namespace HypercubeRamsey.Lane_q_s05_j34

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

theorem pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (A : ∀ i, Ω i → Prop) :
    (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) = ∏ i, (P i).pr (A i) := by
  classical
  let f : ∀ i, Ω i → ℝ := fun i x => if A i x then (P i).w x else 0
  have hpoint : ∀ ω : (∀ i, Ω i),
      (if (∀ i, A i (ω i)) then ∏ i, (P i).w (ω i) else 0) = ∏ i, f i (ω i) := by
    intro ω
    by_cases h : ∀ i, A i (ω i)
    · simp [f, h]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      have hzero : ∏ i, f i (ω i) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [f, hi]
      have hnot : ¬ (∀ i, A i (ω i)) := fun hall => hi (hall i)
      simp [f, hnot, hzero]
  calc
    (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) =
        ∑ ω : (∀ i, Ω i), ∏ i, f i (ω i) := by
      unfold FinProb.pr FinProb.pi
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∀ i, A i (ω i)
      · simpa [h] using hpoint ω
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have hzero : ∏ i, f i (ω i) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [f, hi]
        have hnot : ¬ (∀ i, A i (ω i)) := fun hall => hi (hall i)
        simpa [hnot, hzero] using hpoint ω
    _ = ∏ i, ∑ x, f i x := by rw [← Fintype.prod_sum]
    _ = ∏ i, (P i).pr (A i) := by simp [f, FinProb.pr]

theorem pi_pr_forall_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (A : ∀ i, Ω i → Prop) (q : ι → ℝ)
    (hq : ∀ i, (P i).pr (A i) ≤ q i) :
    (FinProb.pi P).pr (fun ω => ∀ i, A i (ω i)) ≤ ∏ i, q i := by
  rw [pi_pr_forall]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact FinProb.pr_nonneg _ _
  · intro i hi
    exact hq i

theorem pi_pr_lower_count_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (A : ∀ i, Ω i → Prop) (s : ℕ)
    (hmean : 2 * (s : ℝ) ≤ ∑ i, (P i).pr (A i)) :
    (FinProb.pi P).pr (fun ω =>
      (Finset.univ.filter fun i => A i (ω i)).card < s) ≤ Real.exp (-(s : ℝ) / 4) := by
  classical
  let X : ∀ i, Ω i → ℝ := fun i ω => if A i ω then 1 else 0
  let μ : ℝ := ∑ i, (P i).expect (X i)
  have hμ : μ = ∑ i, (P i).pr (A i) := by
    dsimp [μ, X]
    congr 1
    funext i
    unfold FinProb.expect FinProb.pr
    simp
  have hMean : 2 * (s : ℝ) ≤ μ := by rw [hμ]; exact hmean
  have hX (i : ι) (ω : Ω i) : 0 ≤ X i ω ∧ X i ω ≤ 1 := by
    dsimp [X]
    split_ifs <;> norm_num
  have hsum (ω : ∀ i, Ω i) : ∑ i, X i (ω i) =
      ((Finset.univ.filter fun i => A i (ω i)).card : ℝ) := by
    have hcardNat : (Finset.univ.filter fun i => A i (ω i)).card =
        ∑ i, if A i (ω i) then (1 : ℕ) else 0 := by
      rw [Finset.card_filter]
    have hcardReal : (∑ i, if A i (ω i) then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun i => A i (ω i)).card : ℝ) := by
      exact_mod_cast hcardNat.symm
    simpa only [X] using hcardReal
  have hsubset : ∀ ω : (∀ i, Ω i), (Finset.univ.filter fun i => A i (ω i)).card < s →
      ∑ i, X i (ω i) ≤ (1 / 2 : ℝ) * μ := by
    intro ω hω
    rw [hsum ω]
    have hcast : ((Finset.univ.filter fun i => A i (ω i)).card : ℝ) ≤ s := by exact_mod_cast hω.le
    linarith
  have hCher := xChernoff_lower P X hX (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hCher' : (FinProb.pi P).pr (fun ω =>
      ∑ i, X i (ω i) ≤ (1 / 2 : ℝ) * μ) ≤ Real.exp (-μ / 8) := by
    convert hCher using 1 <;> norm_num [μ] <;> ring
  have hprob := FinProb.pr_mono (FinProb.pi P)
    (fun ω => (Finset.univ.filter fun i => A i (ω i)).card < s)
    (fun ω => ∑ i, X i (ω i) ≤ (1 / 2 : ℝ) * μ) hsubset
  have hexp : Real.exp (-μ / 8) ≤ Real.exp (-(s : ℝ) / 4) := by
    apply Real.exp_le_exp.mpr
    have hm : (s : ℝ) / 4 ≤ μ / 8 := by nlinarith
    linarith
  exact hprob.trans (hCher'.trans hexp)

theorem pr_density_le {Ω : Type*} [Fintype Ω] (P Q : FinProb Ω) (M : ℝ)
    (hM : 0 ≤ M) (hdom : ∀ ω, P.w ω ≤ M * Q.w ω) (A : Ω → Prop) :
    P.pr A ≤ M * Q.pr A := by
  classical
  unfold FinProb.pr
  calc
    (∑ ω, if A ω then P.w ω else 0) ≤
        ∑ ω, if A ω then M * Q.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hA : A ω
      · simp only [if_pos hA]
        exact hdom ω
      · simp [hA]
    _ = M * (∑ ω, if A ω then Q.w ω else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hA : A ω <;> simp [hA] <;> ring
    _ = M * Q.pr A := rfl

theorem pi_pr_large_count_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P Q : FinProb (∀ i, Ω i)) (M q υ : ℝ)
    (A : ∀ i, Ω i → Prop)
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hυ : 0 ≤ υ)
    (hdom : ∀ ω, P.w ω ≤ M * Q.w ω)
    (hQ : ∀ S : Finset ι,
      Q.pr (fun ω => ∀ i ∈ S, A i (ω i)) ≤ q ^ S.card) :
    P.pr (fun ω => υ * (Fintype.card ι : ℝ) <
      ((Finset.univ.filter fun i => A i (ω i)).card : ℝ)) ≤
        (2 : ℝ) ^ (Fintype.card ι) * M * q ^ (υ * (Fintype.card ι : ℝ)) := by
  classical
  let k := Fintype.card ι
  let low : (∀ i, Ω i) → Finset ι := fun ω =>
    Finset.univ.filter (fun i => A i (ω i))
  let big : Finset (Finset ι) := Finset.univ.filter fun S => υ * k < (S.card : ℝ)
  let bad : (∀ i, Ω i) → Prop := fun ω => υ * k < (low ω).card
  let allLow : Finset ι → (∀ i, Ω i) → Prop := fun S ω => ∀ i ∈ S, A i (ω i)
  let lowWeight : Finset ι → (∀ i, Ω i) → ℝ := fun S ω =>
    @ite ℝ (allLow S ω) (Classical.propDecidable (allLow S ω)) (Q.w ω) 0
  have hdomPr (B : (∀ i, Ω i) → Prop) : P.pr B ≤ M * Q.pr B :=
    pr_density_le P Q M hM hdom B
  have hQUnion : Q.pr bad ≤ ∑ S ∈ big, Q.pr (allLow S) := by
    unfold FinProb.pr
    calc
      (∑ ω, if bad ω then Q.w ω else 0) ≤
          ∑ ω, ∑ S ∈ big, lowWeight S ω := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hbad : bad ω
        · have hmem : low ω ∈ big := by
            simp only [big, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hbad
          have hall : allLow (low ω) ω := by
            intro i hi
            exact (Finset.mem_filter.mp hi).2
          have hnonneg (S : Finset ι) (hS : S ∈ big) : 0 ≤ lowWeight S ω := by
            dsimp [lowWeight]
            split_ifs
            · exact Q.nonneg ω
            · exact le_rfl
          have hsingle := Finset.single_le_sum hnonneg hmem
          simpa [hbad, lowWeight, hall] using hsingle
        · simp only [if_neg hbad]
          exact Finset.sum_nonneg fun S hS => by
            dsimp [lowWeight]
            split_ifs
            · exact Q.nonneg ω
            · exact le_rfl
      _ = ∑ S ∈ big, Q.pr (allLow S) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro S hS
        rfl
  have hBigCard : (big.card : ℝ) ≤ (2 : ℝ) ^ k := by
    have hcard : big.card ≤ Fintype.card (Finset ι) := Finset.card_le_univ big
    have hpow : Fintype.card (Finset ι) = 2 ^ k := by simp [k]
    exact_mod_cast hcard.trans_eq hpow
  have hQBound : Q.pr bad ≤ (2 : ℝ) ^ k * q ^ (υ * k) := by
    by_cases hq1 : q ≤ 1
    · have hsum : (∑ S ∈ big, Q.pr (allLow S)) ≤ ∑ S ∈ big, q ^ S.card := by
        apply Finset.sum_le_sum
        intro S hS
        exact hQ S
      have hsum' : (∑ S ∈ big, q ^ S.card) ≤ ∑ S ∈ big, q ^ (υ * k) := by
        apply Finset.sum_le_sum
        intro S hS
        have hexp : υ * k ≤ (S.card : ℝ) := le_of_lt (Finset.mem_filter.mp hS).2
        have hp : q ^ S.card ≤ q ^ (υ * k) := by
          rw [← Real.rpow_natCast q S.card]
          exact Real.rpow_le_rpow_of_exponent_ge' hq hq1
            (mul_nonneg hυ (Nat.cast_nonneg k)) hexp
        exact hp
      have hconst : (∑ S ∈ big, q ^ (υ * k)) = (big.card : ℝ) * q ^ (υ * k) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have hcardMul : (big.card : ℝ) * q ^ (υ * k) ≤ (2 : ℝ) ^ k * q ^ (υ * k) :=
        mul_le_mul_of_nonneg_right hBigCard (Real.rpow_nonneg hq (υ * k))
      calc
        Q.pr bad ≤ ∑ S ∈ big, Q.pr (allLow S) := hQUnion
        _ ≤ ∑ S ∈ big, q ^ S.card := hsum
        _ ≤ ∑ S ∈ big, q ^ (υ * k) := hsum'
        _ = (big.card : ℝ) * q ^ (υ * k) := hconst
        _ ≤ (2 : ℝ) ^ k * q ^ (υ * k) := hcardMul
    · have hqone : 1 ≤ q := le_of_not_ge hq1
      have hQbad : Q.pr bad ≤ 1 := by
        unfold FinProb.pr
        calc
          (∑ ω, if bad ω then Q.w ω else 0) ≤ ∑ ω, Q.w ω := by
            apply Finset.sum_le_sum
            intro ω hω
            by_cases hbad : bad ω
            · simp [hbad]
            · simp [hbad, Q.nonneg ω]
          _ = 1 := Q.sum_eq_one
      have htwo : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      have hqpow : 1 ≤ q ^ (υ * k) := Real.one_le_rpow hqone (mul_nonneg hυ (Nat.cast_nonneg k))
      have hprod : 1 ≤ (2 : ℝ) ^ k * q ^ (υ * k) := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ (2 : ℝ) ^ k * q ^ (υ * k) := mul_le_mul htwo hqpow (by norm_num) (by norm_num)
      exact hQbad.trans hprod
  calc
    P.pr bad ≤ M * Q.pr bad := hdomPr bad
    _ ≤ M * ((2 : ℝ) ^ k * q ^ (υ * k)) := mul_le_mul_of_nonneg_left hQBound hM
    _ = (2 : ℝ) ^ k * M * q ^ (υ * k) := by ring

theorem pr_prod_and {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) (B : β → Prop) :
    (P.prod Q).pr (fun ab => A ab.1 ∧ B ab.2) = P.pr A * Q.pr B := by
  classical
  unfold FinProb.pr
  simp only [FinProb.prod]
  calc
    _ =
        ∑ a, ∑ b, (if A a then P.w a else 0) * (if B b then Q.w b else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hA : A a <;> by_cases hB : B b <;> simp [hA, hB]
    _ = (∑ a, if A a then P.w a else 0) * (∑ b, if B b then Q.w b else 0) := by
      calc
        _ = ∑ a, (if A a then P.w a else 0) * (∑ b, if B b then Q.w b else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_mul]
    _ = P.pr A * Q.pr B := rfl

theorem pr_prod_snd5 {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : β → Prop) :
    (P.prod Q).pr (fun ab => A ab.2) = Q.pr A := by
  classical
  calc
    (P.prod Q).pr (fun ab => A ab.2) = P.pr (fun _ : α => True) * Q.pr A := by
      simpa using pr_prod_and P Q (fun _ => True) A
    _ = Q.pr A := by simp [FinProb.pr, P.sum_eq_one]

theorem prod_pr_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (E : α → β → Prop) :
    (FinProb.prod P Q).pr (fun ab => E ab.1 ab.2) =
      ∑ a, P.w a * Q.pr (E a) := by
  classical
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, if E a b then P.w a * Q.w b else 0) =
        ∑ b, P.w a * (if E a b then Q.w b else 0) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : E a b <;> simp [h, mul_assoc]
    _ = P.w a * ∑ b, if E a b then Q.w b else 0 := by rw [Finset.mul_sum]
    _ = P.w a * Q.pr (E a) := rfl

theorem map_equiv_weight {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinProb α) (e : α ≃ β) (b : β) :
    (FinProb.map P e).w b = P.w (e.symm b) := by
  classical
  unfold FinProb.map
  have hfun : (fun a : α => if e a = b then P.w a else 0) =
      fun a => if a = e.symm b then P.w a else 0 := by
    funext a
    by_cases h : e a = b
    · have hEq : a = e.symm b := by
        apply e.injective
        calc
          e a = b := h
          _ = e (e.symm b) := (e.apply_symm_apply b).symm
      simp [h, hEq]
    · have hNe : a ≠ e.symm b := by
        intro ha
        subst a
        exact h (e.apply_symm_apply b)
      simp only [if_neg h, if_neg hNe]
  change (∑ a, if e a = b then P.w a else 0) = P.w (e.symm b)
  rw [hfun]
  simp [Finset.sum_ite_eq']

theorem pi_prod_factor {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β] (P : FinProb α) (Q : FinProb β) :
    FinProb.map (FinProb.pi fun _ : ι => FinProb.prod P Q)
      (fun ω => (fun i => (ω i).1, fun i => (ω i).2)) =
        FinProb.prod (FinProb.pi fun _ : ι => P) (FinProb.pi fun _ : ι => Q) := by
  classical
  let e : (∀ i : ι, α × β) ≃ (ι → α) × (ι → β) := {
    toFun := fun ω => (fun i => (ω i).1, fun i => (ω i).2)
    invFun := fun ab i => (ab.1 i, ab.2 i)
    left_inv := by intro ω; funext i; exact Prod.ext rfl rfl
    right_inv := by intro ab; apply Prod.ext <;> funext i <;> rfl }
  change FinProb.map (FinProb.pi fun _ : ι => FinProb.prod P Q) e = _
  apply FinProb.ext
  intro ab
  rw [map_equiv_weight]
  simp [e, FinProb.pi, FinProb.prod, Finset.prod_mul_distrib]

def avgMarg5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (x : Fin N) : ℝ :=
  ((X.p.q0 * X.p.typeSegs n K : ℕ) : ℝ)⁻¹ *
    ∑ z, (X.blockLaw H K).w z * ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
      z e.1 e.2 = x).card : ℝ)

def priorHeavy5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty) (x : Fin N) : Prop :=
  X.blockConst K ^ X.p.KB < (N : ℝ) * avgMarg5 X H K x

def priorHeavyBlockCount5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty)
    (z : X.Block K) : ℕ :=
  ∑ i : Fin (X.p.typeSegs n K),
    (Finset.univ.filter fun e : Fin X.p.q0 => priorHeavy5 X H K (z i e)).card

theorem avgMarg_sum (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty)
    (hLen : 0 < X.p.q0 * X.p.typeSegs n K) :
    ∑ x : Fin N, avgMarg5 X H K x = 1 := by
  classical
  let L : ℝ := (X.p.q0 * X.p.typeSegs n K : ℕ)
  have hL : L ≠ 0 := by
    dsimp [L]
    exact_mod_cast hLen.ne'
  have hCount (z : X.Block K) :
      ∑ x : Fin N,
        ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
          z e.1 e.2 = x).card : ℝ) =
            (X.p.typeSegs n K : ℝ) * X.p.q0 := by
    calc
      _ = ∑ x : Fin N, ∑ e : Fin (X.p.typeSegs n K) × Fin X.p.q0,
            if z e.1 e.2 = x then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      _ = ∑ e : Fin (X.p.typeSegs n K) × Fin X.p.q0, ∑ x : Fin N,
            if z e.1 e.2 = x then (1 : ℝ) else 0 := by rw [Finset.sum_comm]
      _ = ∑ _e : Fin (X.p.typeSegs n K) × Fin X.p.q0, 1 := by
        apply Finset.sum_congr rfl
        intro e he
        simp
      _ = (X.p.typeSegs n K : ℝ) * X.p.q0 := by simp [Fintype.card_prod]
  unfold avgMarg5
  dsimp only [L] at hL ⊢
  have hswap :
      (∑ x : Fin N, ∑ z, (X.blockLaw H K).w z *
        ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
          z e.1 e.2 = x).card : ℝ)) =
      ∑ z, (X.blockLaw H K).w z * ∑ x : Fin N,
        ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
          z e.1 e.2 = x).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    rw [← Finset.mul_sum]
  calc
    _ = ((X.p.q0 * X.p.typeSegs n K : ℕ) : ℝ)⁻¹ *
        ∑ z, (X.blockLaw H K).w z *
          ∑ x : Fin N,
            ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
              z e.1 e.2 = x).card : ℝ) := by
      rw [← Finset.mul_sum]
      exact congrArg _ hswap
    _ = ((X.p.q0 * X.p.typeSegs n K : ℕ) : ℝ)⁻¹ *
        ∑ z, (X.blockLaw H K).w z * (X.p.q0 * X.p.typeSegs n K : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      rw [hCount]
      push_cast
      ring
    _ = 1 := by
      rw [← Finset.sum_mul, (X.blockLaw H K).sum_eq_one]
      field_simp [hL]
      push_cast
      ring

theorem priorHeavy_card_bound (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty)
    (hLen : 0 < X.p.q0 * X.p.typeSegs n K) :
    (((Finset.univ.filter fun x : Fin N => priorHeavy5 X H K x).card : ℝ) *
        X.blockConst K ^ X.p.KB) ≤ N := by
  classical
  let D : Finset (Fin N) := Finset.univ.filter fun x => priorHeavy5 X H K x
  let B : ℝ := X.blockConst K ^ X.p.KB
  have hB : 0 < B := by dsimp [B, Setup5.blockConst]; positivity
  have havgNonneg (x : Fin N) : 0 ≤ avgMarg5 X H K x := by
    unfold avgMarg5
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg ((X.blockLaw H K).nonneg z) (Nat.cast_nonneg _)
  have hsubset : (∑ x ∈ D, avgMarg5 X H K x) ≤ 1 := by
    have hsum : (∑ x ∈ D, avgMarg5 X H K x) ≤ ∑ x : Fin N, avgMarg5 X H K x := by
      calc
        _ = ∑ x : Fin N, if x ∈ D then avgMarg5 X H K x else 0 := by
          rw [← Finset.sum_filter]
          simp [D]
        _ ≤ ∑ x : Fin N, avgMarg5 X H K x := by
          apply Finset.sum_le_sum
          intro x hx
          split_ifs with h
          · rfl
          · exact havgNonneg x
    rw [avgMarg_sum X H K hLen] at hsum
    exact hsum
  have hterm (x : Fin N) (hx : x ∈ D) : B ≤ (N : ℝ) * avgMarg5 X H K x := by
    exact le_of_lt (Finset.mem_filter.mp hx).2
  have hsumB : (D.card : ℝ) * B ≤
      (N : ℝ) * (∑ x ∈ D, avgMarg5 X H K x) := by
    calc
      _ = ∑ x ∈ D, B := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ D, (N : ℝ) * avgMarg5 X H K x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hterm x hx
      _ = (N : ℝ) * (∑ x ∈ D, avgMarg5 X H K x) := by rw [Finset.mul_sum]
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (N : ℝ) * (∑ x ∈ D, avgMarg5 X H K x) := hsumB
    _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hsubset hN
    _ = (N : ℝ) := by ring

theorem priorHeavy_reference_coordinate_bound (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (hLen : 0 < X.p.q0 * X.p.typeSegs n K)
    (e : Fin X.p.q0) :
    X.S.reference.pr (fun w : Word5 N X.p.q0 => priorHeavy5 X H K (w e)) ≤
      K' / (X.blockConst K ^ X.p.KB) := by
  classical
  let D : Finset (Fin N) := Finset.univ.filter fun x => priorHeavy5 X H K x
  let B : ℝ := X.blockConst K ^ X.p.KB
  let M : FinProb (Fin N) := FinProb.map X.S.reference (fun w : Word5 N X.p.q0 => w e)
  have hN : 0 < (N : ℝ) := by exact_mod_cast (Fin.pos X.y₀)
  have hB : 0 < B := by dsimp [B, Setup5.blockConst]; positivity
  have hK' : 0 < K' := X.p.hK
  have hCardBound := priorHeavy_card_bound X H K hLen
  have hD : (D.card : ℝ) * B ≤ (N : ℝ) := by
    simpa [D, B] using hCardBound
  have hDle : (D.card : ℝ) ≤ (N : ℝ) / B := (le_div_iff₀ hB).2 hD
  have hAtoms (x : Fin N) : M.w x ≤ K' / N := by
    have hMarg : M.w x = wordMarginal5 X.S.reference e x := by
      rfl
    rw [hMarg]
    exact X.S.reference_coordinate_cap e x
  have hMargProb : M.pr (priorHeavy5 X H K) ≤ (D.card : ℝ) * (K' / (N : ℝ)) := by
    unfold FinProb.pr
    calc
      (∑ x, if priorHeavy5 X H K x then M.w x else 0) ≤
          ∑ x, if priorHeavy5 X H K x then K' / (N : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs with hh
        · exact hAtoms x
        · exact le_rfl
      _ = (D.card : ℝ) * (K' / (N : ℝ)) := by
        rw [← Finset.sum_filter]
        simp [D, Finset.sum_const, nsmul_eq_mul]
  have hMargFrac : (D.card : ℝ) * (K' / (N : ℝ)) ≤ K' / B := by
    calc
      _ ≤ ((N : ℝ) / B) * (K' / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hDle (div_nonneg hK'.le hN.le)
      _ = K' / B := by field_simp [ne_of_gt hB, ne_of_gt hN]
  have hmap := FinProb.map_pr X.S.reference (fun w : Word5 N X.p.q0 => w e)
    (priorHeavy5 X H K)
  calc
    X.S.reference.pr (fun w : Word5 N X.p.q0 => priorHeavy5 X H K (w e)) =
        M.pr (priorHeavy5 X H K) := hmap.symm
    _ ≤ (D.card : ℝ) * (K' / (N : ℝ)) := hMargProb
    _ ≤ K' / B := hMargFrac

theorem priorHeavy_reference_word_bound (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (hLen : 0 < X.p.q0 * X.p.typeSegs n K) :
    X.S.reference.pr (fun w : Word5 N X.p.q0 => ∃ j : Fin X.p.q0,
      priorHeavy5 X H K (w j)) ≤
        ((X.p.q0 : ℝ) * K') / (X.blockConst K ^ X.p.KB) := by
  classical
  have hUnion := FinProb.pr_exists_le_sum5 X.S.reference
    (fun j w => priorHeavy5 X H K (w j))
  calc
    X.S.reference.pr (fun w : Word5 N X.p.q0 => ∃ j : Fin X.p.q0,
        priorHeavy5 X H K (w j)) ≤
        ∑ j : Fin X.p.q0, X.S.reference.pr (fun w => priorHeavy5 X H K (w j)) := by
      simpa using hUnion
    _ ≤ ∑ _j : Fin X.p.q0, K' / (X.blockConst K ^ X.p.KB) := by
      apply Finset.sum_le_sum
      intro j hj
      exact priorHeavy_reference_coordinate_bound X H K hLen j
    _ = _ := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

theorem priorHeavy_block_tail_bound (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty)
    (hDensity : ∀ z, (X.blockLaw H K).w z ≤
      X.blockConst K ^ (X.p.q0 * X.p.typeSegs n K) * X.refBlock K z)
    (hLen : 0 < X.p.q0 * X.p.typeSegs n K)
    (υ q C : ℝ) (hυ : 0 ≤ υ) (hυpos : 0 < υ)
    (hq : 0 ≤ q) (hqPos : 0 < q) (hq1 : q ≤ 1)
    (hWord : X.S.reference.pr (fun w : Word5 N X.p.q0 => ∃ j : Fin X.p.q0,
      priorHeavy5 X H K (w j)) ≤ q)
    (hMargin : Real.log 2 + (X.p.q0 : ℝ) * Real.log (X.blockConst K) +
      υ * Real.log q ≤ -C) :
    (X.blockLaw H K).pr (fun z =>
      υ * (X.p.q0 * X.p.typeSegs n K : ℕ) <
        (priorHeavyBlockCount5 X H K z : ℝ)) ≤
      Real.exp (-C * (X.p.typeSegs n K : ℝ)) := by
  classical
  let u := X.p.typeSegs n K
  let Q : FinProb (Fin u → Word5 N X.p.q0) := FinProb.pi fun _ => X.S.reference
  let A : Fin u → Word5 N X.p.q0 → Prop := fun _ w =>
    ∃ j : Fin X.p.q0, priorHeavy5 X H K (w j)
  let badSeg (z : Fin u → Word5 N X.p.q0) : Finset (Fin u) :=
    Finset.univ.filter fun i => A i (z i)
  let heavyCount (z : Fin u → Word5 N X.p.q0) : ℕ :=
    priorHeavyBlockCount5 X H K z
  let heavyBad (z : Fin u → Word5 N X.p.q0) : Prop :=
    υ * (X.p.q0 * u : ℕ) < (heavyCount z : ℝ)
  have hQ (S : Finset (Fin u)) :
      Q.pr (fun z => ∀ i ∈ S, A i (z i)) ≤ q ^ S.card := by
    let A' : Fin u → Word5 N X.p.q0 → Prop := fun i w => i ∈ S → A i w
    have hcoord (i : Fin u) : X.S.reference.pr (A' i) ≤ if i ∈ S then q else 1 := by
      by_cases hi : i ∈ S
      · simpa [A', hi] using hWord
      · have htrue : X.S.reference.pr (fun _ : Word5 N X.p.q0 => True) = 1 := by
          simp [FinProb.pr, X.S.reference.sum_eq_one]
        simpa [A', hi] using htrue.le
    have hpi := pi_pr_forall_le (fun _ : Fin u => X.S.reference) A'
      (fun i => if i ∈ S then q else 1) hcoord
    have hEvent : (fun z : Fin u → Word5 N X.p.q0 => ∀ i, A' i (z i)) =
        (fun z => ∀ i ∈ S, A i (z i)) := by
      funext z
      apply propext
      simp [A']
    rw [hEvent]
    calc
      Q.pr (fun z => ∀ i, A' i (z i)) ≤
          ∏ i : Fin u, (if i ∈ S then q else 1) := by
        exact hpi
      _ = q ^ S.card := by simp [Finset.prod_ite]
  have hBaseNonneg : 0 ≤ X.blockConst K := by
    dsimp [Setup5.blockConst]
    exact Real.exp_nonneg _
  have hM : 0 ≤ X.blockConst K ^ (X.p.q0 * u) := pow_nonneg hBaseNonneg _
  have hdom (z : Fin u → Word5 N X.p.q0) :
      (X.blockLaw H K).w z ≤ X.blockConst K ^ (X.p.q0 * u) * Q.w z := by
    calc
      _ ≤ X.blockConst K ^ (X.p.q0 * u) * X.refBlock K z := hDensity z
      _ = X.blockConst K ^ (X.p.q0 * u) * Q.w z := by rfl
  have hGeneric := pi_pr_large_count_bound (X.blockLaw H K) Q
    (X.blockConst K ^ (X.p.q0 * u)) q υ A hM hq hυ hdom hQ
  have hCountBound (z : Fin u → Word5 N X.p.q0) :
      heavyCount z ≤ X.p.q0 * (badSeg z).card := by
    have hpiece (i : Fin u) :
        (Finset.univ.filter fun e : Fin X.p.q0 => priorHeavy5 X H K (z i e)).card ≤
          if i ∈ badSeg z then X.p.q0 else 0 := by
      by_cases hi : i ∈ badSeg z
      · simpa [hi, Fintype.card_fin] using
          (Finset.card_le_univ (Finset.univ.filter fun e : Fin X.p.q0 =>
            priorHeavy5 X H K (z i e)))
      · have hEmpty :
            (Finset.univ.filter fun e : Fin X.p.q0 => priorHeavy5 X H K (z i e)) = ∅ := by
          ext e
          simp [badSeg] at hi ⊢
          exact fun he => hi ⟨e, he⟩
        simp [hi, hEmpty]
    calc
      _ ≤ ∑ i : Fin u, (if i ∈ badSeg z then X.p.q0 else 0) :=
        Finset.sum_le_sum fun i hi => hpiece i
      _ = X.p.q0 * (badSeg z).card := by
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hImp (z : Fin u → Word5 N X.p.q0) (hz : heavyBad z) :
      υ * (Fintype.card (Fin u) : ℝ) < (badSeg z).card := by
    have hHeavy : υ * ((X.p.q0 : ℝ) * u) < (heavyCount z : ℝ) := by
      simpa [heavyBad, Nat.cast_mul, mul_assoc] using hz
    have hBound : (heavyCount z : ℝ) ≤ (X.p.q0 : ℝ) * (badSeg z).card := by
      exact_mod_cast hCountBound z
    have hq0pos : 0 < (X.p.q0 : ℝ) := by exact_mod_cast X.p.hq0.1
    have hrew : υ * ((X.p.q0 : ℝ) * u) = (X.p.q0 : ℝ) * (υ * (u : ℝ)) := by ring
    have hmul : (X.p.q0 : ℝ) * (υ * (u : ℝ)) <
        (X.p.q0 : ℝ) * (badSeg z).card := by
      calc
        _ = υ * ((X.p.q0 : ℝ) * (u : ℝ)) := by ring
        _ < (heavyCount z : ℝ) := hHeavy
        _ ≤ _ := hBound
    have hdiv : υ * (u : ℝ) < (badSeg z).card := by
      by_contra hnot
      have hle : (badSeg z).card ≤ υ * (u : ℝ) := by
        simpa [Fintype.card_fin] using (le_of_not_gt hnot)
      have hmul' := mul_le_mul_of_nonneg_left hle hq0pos.le
      exact (not_le_of_gt hmul) hmul'
    simpa using hdiv
  have hMono : (X.blockLaw H K).pr heavyBad ≤
      (X.blockLaw H K).pr (fun z => υ * (Fintype.card (Fin u) : ℝ) < (badSeg z).card) :=
    FinProb.pr_mono (X.blockLaw H K) heavyBad
      (fun z => υ * (Fintype.card (Fin u) : ℝ) < (badSeg z).card) hImp
  have htail :
      (X.blockLaw H K).pr (fun z => υ * (Fintype.card (Fin u) : ℝ) < (badSeg z).card) ≤
        (2 : ℝ) ^ u * (X.blockConst K ^ (X.p.q0 * u)) * q ^ (υ * (u : ℝ)) := by
    change (X.blockLaw H K).pr (fun z => υ * (Fintype.card (Fin u) : ℝ) <
      (Finset.univ.filter fun i : Fin u => A i (z i)).card) ≤ _
    simpa [A, u, Fintype.card_fin] using hGeneric
  have hBcPos : 0 < X.blockConst K := by
    dsimp [Setup5.blockConst]
    exact Real.exp_pos _
  have hFactor :
      (2 : ℝ) * (X.blockConst K ^ X.p.q0) * q ^ υ ≤ Real.exp (-C) := by
    let F : ℝ := (2 : ℝ) * X.blockConst K ^ X.p.q0 * q ^ υ
    have hpowPos : 0 < X.blockConst K ^ X.p.q0 := pow_pos hBcPos _
    have hqpowPos : 0 < q ^ υ := Real.rpow_pos_of_pos hqPos _
    have hFpos : 0 < F := by
      dsimp [F]
      exact mul_pos (mul_pos (by norm_num) hpowPos) hqpowPos
    have hlogF : Real.log F = Real.log 2 + (X.p.q0 : ℝ) * Real.log (X.blockConst K) +
        υ * Real.log q := by
      dsimp [F]
      calc
        _ = Real.log ((2 : ℝ) * (X.blockConst K ^ X.p.q0) * (q ^ υ)) := rfl
        _ = Real.log ((2 : ℝ) * (X.blockConst K ^ X.p.q0)) + Real.log (q ^ υ) :=
          Real.log_mul (by positivity) (ne_of_gt hqpowPos)
        _ = Real.log 2 + Real.log (X.blockConst K ^ X.p.q0) + Real.log (q ^ υ) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hpowPos)]
        _ = _ := by rw [Real.log_pow, Real.log_rpow hqPos]
    have hlogF' : Real.log F ≤ -C := by rw [hlogF]; exact hMargin
    have hFexp : F ≤ Real.exp (-C) := (Real.log_le_iff_le_exp hFpos).mp hlogF'
    simpa [F] using hFexp
  have hBlockPow : (X.blockConst K ^ X.p.q0) ^ u = X.blockConst K ^ (X.p.q0 * u) := by
    rw [← pow_mul]
  have hqPow : (q ^ υ) ^ u = q ^ (υ * (u : ℝ)) := by
    calc
      (q ^ υ) ^ u = (q ^ υ) ^ (u : ℝ) := by rw [Real.rpow_natCast]
      _ = q ^ (υ * (u : ℝ)) := (Real.rpow_mul hqPos.le υ (u : ℝ)).symm
  let F : ℝ := (2 : ℝ) * X.blockConst K ^ X.p.q0 * q ^ υ
  have hTermEq :
      (2 : ℝ) ^ u * (X.blockConst K ^ (X.p.q0 * u)) * q ^ (υ * (u : ℝ)) = F ^ u := by
    rw [← hBlockPow, ← hqPow]
    simp [F, mul_pow, mul_assoc]
  have hPowExp : F ^ u ≤ Real.exp (-C * (u : ℝ)) := by
    calc
      F ^ u ≤ Real.exp (-C) ^ u := pow_le_pow_left₀ (by positivity) hFactor u
      _ = Real.exp (-C * (u : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hfinal : (X.blockLaw H K).pr heavyBad ≤ Real.exp (-C * (u : ℝ)) := by
    calc
      (X.blockLaw H K).pr heavyBad ≤
          (2 : ℝ) ^ u * (X.blockConst K ^ (X.p.q0 * u)) * q ^ (υ * (u : ℝ)) := hMono.trans htail
      _ = F ^ u := hTermEq
      _ ≤ Real.exp (-C * (u : ℝ)) := hPowExp
  simpa [heavyBad, heavyCount, u, Nat.cast_sum] using hfinal

theorem pi_pr_coordinate_event_early {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (A : Ω i → Prop) :
    (FinProb.pi P).pr (fun ω => A (ω i)) = (P i).pr A := by
  classical
  let C : ∀ j, Ω j → Prop := fun j z => if h : j = i then A (h ▸ z) else True
  have hEvent : (fun ω : (∀ j, Ω j) => ∀ j, C j (ω j)) = (fun ω => A (ω i)) := by
    funext ω
    apply propext
    constructor
    · intro h
      have hh := h i
      simpa [C] using hh
    · intro h j
      by_cases hj : j = i
      · subst j
        simpa [C] using h
      · simp [C, hj]
  rw [← hEvent, pi_pr_forall]
  have hterm (j : ι) : (P j).pr (C j) = if j = i then (P i).pr A else 1 := by
    by_cases hj : j = i
    · subst j
      simp [C]
    · simp [C, hj, FinProb.pr, (P j).sum_eq_one]
  rw [Finset.prod_congr rfl fun j hj => hterm j]
  simp [FinProb.pr]

theorem array_some_heavy_block_tail5 (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty)
    (hDensity : ∀ z, (X.blockLaw H K).w z ≤
      X.blockConst K ^ (X.p.q0 * X.p.typeSegs n K) * X.refBlock K z)
    (hLen : 0 < X.p.q0 * X.p.typeSegs n K)
    (υ q C : ℝ) (hυ : 0 ≤ υ) (hυpos : 0 < υ)
    (hq : 0 ≤ q) (hqPos : 0 < q) (hq1 : q ≤ 1)
    (hWord : X.S.reference.pr (fun w : Word5 N X.p.q0 => ∃ j : Fin X.p.q0,
      priorHeavy5 X H K (w j)) ≤ q)
    (hMargin : Real.log 2 + (X.p.q0 : ℝ) * Real.log (X.blockConst K) +
      υ * Real.log q ≤ -C) :
    (FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K).pr
      (fun A : X.Array K => ∃ i, υ * (X.p.q0 * X.p.typeSegs n K : ℕ) <
        (priorHeavyBlockCount5 X H K (A i) : ℝ)) ≤
      (X.p.typeBlocks n K : ℝ) * Real.exp (-C * (X.p.typeSegs n K : ℝ)) := by
  classical
  let Q : FinProb (X.Array K) := FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K
  let Bad : X.Block K → Prop := fun z =>
    υ * (X.p.q0 * X.p.typeSegs n K : ℕ) < (priorHeavyBlockCount5 X H K z : ℝ)
  have hUnion := FinProb.pr_exists_le_sum5 Q (fun i A => Bad (A i))
  calc
    Q.pr (fun A => ∃ i, Bad (A i)) ≤
        ∑ i : Fin (X.p.typeBlocks n K), Q.pr (fun A => Bad (A i)) := hUnion
    _ = ∑ i : Fin (X.p.typeBlocks n K), (X.blockLaw H K).pr Bad := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pi_pr_coordinate_event_early (fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)
        i Bad
    _ ≤ ∑ _i : Fin (X.p.typeBlocks n K), Real.exp (-C * (X.p.typeSegs n K : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [Bad, priorHeavyBlockCount5] using
        priorHeavy_block_tail_bound X H K hDensity hLen υ q C hυ hυpos hq hqPos hq1
          hWord hMargin
    _ = (X.p.typeBlocks n K : ℝ) * Real.exp (-C * (X.p.typeSegs n K : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem heavy_ref_failure_imp_some_block5 (X : Setup5 γ K' χ n N E G)
    (H : X.KeyHist) (K : X.Ty) (A : X.Array K) (M : Finset (Fin X.blockBound))
    (υ : ℝ) (hυ : 0 ≤ υ) :
    (∑ i : Fin (X.p.typeBlocks n K),
      if ∃ j ∈ M, X.blockIdx K j = some i then
        priorHeavyBlockCount5 X H K (A i) else 0) >
      υ * (X.refLen K M : ℝ) →
    ∃ i : Fin (X.p.typeBlocks n K),
      υ * (X.p.q0 * X.p.typeSegs n K : ℕ) <
        (priorHeavyBlockCount5 X H K (A i) : ℝ) := by
  classical
  intro hfail
  by_contra hnone
  push_neg at hnone
  let S : Finset (Fin (X.p.typeBlocks n K)) :=
    Finset.univ.filter fun i => ∃ j ∈ M, X.blockIdx K j = some i
  have hterm (i : Fin (X.p.typeBlocks n K)) :
      (if ∃ j ∈ M, X.blockIdx K j = some i then
        (priorHeavyBlockCount5 X H K (A i) : ℝ) else 0) ≤
      if ∃ j ∈ M, X.blockIdx K j = some i then
        υ * (X.p.q0 * X.p.typeSegs n K : ℕ) else 0 := by
    by_cases hi : ∃ j ∈ M, X.blockIdx K j = some i
    · simp only [if_pos hi]
      have hh := hnone i
      simpa only [Nat.cast_mul] using hh
    · simp [hi]
  have hsum :
      (∑ i : Fin (X.p.typeBlocks n K),
        if ∃ j ∈ M, X.blockIdx K j = some i then
          priorHeavyBlockCount5 X H K (A i) else 0) ≤
      ∑ i : Fin (X.p.typeBlocks n K),
        if ∃ j ∈ M, X.blockIdx K j = some i then
          υ * (X.p.q0 * X.p.typeSegs n K : ℕ) else 0 :=
    by
      calc
        (↑(∑ i : Fin (X.p.typeBlocks n K),
          if ∃ j ∈ M, X.blockIdx K j = some i then
            priorHeavyBlockCount5 X H K (A i) else 0) : ℝ) =
          ∑ i : Fin (X.p.typeBlocks n K),
            if ∃ j ∈ M, X.blockIdx K j = some i then
              (priorHeavyBlockCount5 X H K (A i) : ℝ) else 0 := by
                simp [Nat.cast_sum]
        _ ≤ ∑ i : Fin (X.p.typeBlocks n K),
            if ∃ j ∈ M, X.blockIdx K j = some i then
              υ * (X.p.q0 * X.p.typeSegs n K : ℕ) else 0 :=
              Finset.sum_le_sum fun i hi => hterm i
  have hcardS : S.card ≤ M.card := by
    let f : S → {j // j ∈ M} := fun i =>
      ⟨Classical.choose (Finset.mem_filter.mp i.2).2,
        (Classical.choose_spec (Finset.mem_filter.mp i.2).2).1⟩
    have hf : Function.Injective f := by
      intro i i' heq
      apply Subtype.ext
      have hj : Classical.choose (Finset.mem_filter.mp i.2).2 =
          Classical.choose (Finset.mem_filter.mp i'.2).2 := congrArg Subtype.val heq
      have hi := (Classical.choose_spec (Finset.mem_filter.mp i.2).2).2
      have hi' := (Classical.choose_spec (Finset.mem_filter.mp i'.2).2).2
      have hsome : some i.1 = some i'.1 := by
        calc
          some i.1 = X.blockIdx K (Classical.choose (Finset.mem_filter.mp i.2).2) := hi.symm
          _ = X.blockIdx K (Classical.choose (Finset.mem_filter.mp i'.2).2) := by rw [hj]
          _ = some i'.1 := hi'
      exact Option.some.inj hsome
    have hfin := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe] using hfin
  have hS_cast : (S.card : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast hcardS
  have hconst :
      (∑ i : Fin (X.p.typeBlocks n K),
        if ∃ j ∈ M, X.blockIdx K j = some i then
          υ * (X.p.q0 * X.p.typeSegs n K : ℕ) else 0) =
      (υ * (X.p.q0 * X.p.typeSegs n K : ℕ)) * (S.card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [S]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hnonneg : 0 ≤ υ * (X.p.q0 * X.p.typeSegs n K : ℕ) :=
    mul_nonneg hυ (Nat.cast_nonneg _)
  have hfinal :
      (∑ i : Fin (X.p.typeBlocks n K),
        if ∃ j ∈ M, X.blockIdx K j = some i then
          priorHeavyBlockCount5 X H K (A i) else 0) ≤
      υ * (X.refLen K M : ℝ) := by
    calc
      _ ≤ (υ * (X.p.q0 * X.p.typeSegs n K : ℕ)) * (S.card : ℝ) := by
        rw [← hconst]
        exact hsum
      _ ≤ (υ * (X.p.q0 * X.p.typeSegs n K : ℕ)) * (M.card : ℝ) :=
        mul_le_mul_of_nonneg_left hS_cast hnonneg
      _ = υ * (X.refLen K M : ℝ) := by
        simp [Setup5.refLen]
        push_cast
        ring
  exact (not_lt_of_ge hfinal) hfail

theorem high_hitset_card_lower5 (X : Setup5 γ K' χ n N E G)
    (arrs : ∀ K : X.Ty, X.Array K) (K : X.Ty) (hHigh : K.2.2 = none)
    (y : Fin N) :
    (Finset.univ.filter fun i : Fin (X.p.typeBlocks n K) =>
      X.BlockHits K (arrs K i) y).card ≤
      (X.hitSet (fun c : Unit × X.Ty => arrs c.2) ((), K) y).card := by
  classical
  let good : Finset (Fin (X.p.typeBlocks n K)) :=
    Finset.univ.filter fun i => X.BlockHits K (arrs K i) y
  let A : X.ArraysOn Unit := fun c => arrs c.2
  let hit : Finset (Fin X.blockBound) := X.hitSet A ((), K) y
  have htype : X.p.typeBlocks n K = X.p.poolBlocks n := by
    simp [Params5.typeBlocks, hHigh]
  have hbound : X.p.typeBlocks n K ≤ X.blockBound := by
    rw [htype]
    exact Nat.le_max_left _ _
  let f : {i // i ∈ good} → {j // j ∈ hit} := fun i =>
    ⟨Fin.castLE hbound i.1, by
      apply Finset.mem_filter.mpr
      constructor
      · simp only [Setup5.poolIdx, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [htype, Fin.castLE] using i.1.isLt
      · refine ⟨i.1, ?_, ?_⟩
        · have hv : (Fin.castLE hbound i.1 : ℕ) < X.p.typeBlocks n K := by
            simpa using i.1.isLt
          simp [Setup5.blockIdx, hv, Fin.castLE]
        · exact (Finset.mem_filter.mp i.2).2⟩
  have hf : Function.Injective f := by
    intro i i' heq
    apply Subtype.ext
    apply Fin.ext
    have hv := congrArg (fun j : {j // j ∈ hit} => (j.1 : ℕ)) heq
    simpa [f, Fin.castLE] using hv
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, good, hit, A] using hcard

theorem colLik_le_of_gate_alias5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist) (K : X.Ty)
    (ell ell₀ : X.Key) (z : X.Block K)
    (θ : Fin (colLen5 (X.p.s n) ell) → Fin N)
    (hgateKey : ell₀ ∈ X.gateKeys K)
    (hcoarse : ell.coarse = ell₀.coarse) (hlevel : ell.level = ell₀.level)
    (hgate : X.blockGate H.1 K z) :
    X.colLik H.1 K ell z θ ≤
      Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) * colLen5 (X.p.s n) ell) := by
  classical
  let B := Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K))
  have hB : 0 ≤ B := Real.exp_nonneg _
  have hrep : X.priorRep H.1 ell K.1.1 z = X.priorRep H.1 ell₀ K.1.1 z := by
    unfold Setup5.priorRep
    congr 1
    funext y
    simp [Setup5.colWeight, hcoarse, hlevel]
  have hdel : X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K) =
      X.priorDel H.1 ell₀ K.1.1 (X.p.typeSegs n K) := by
    unfold Setup5.priorDel
    congr 1
    funext y
    simp [Setup5.colWeight, hcoarse, hlevel]
  have hratio (h : Fin (colLen5 (X.p.s n) ell)) :
      ratio5 ((X.priorRep H.1 ell K.1.1 z).w (θ h))
        ((X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).w (θ h)) ≤ B := by
    apply Lane_q_s05_hist1b.ratio5_le_of_mul_le
    · exact (X.priorRep H.1 ell K.1.1 z).nonneg (θ h)
    · exact (X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).nonneg (θ h)
    · exact hB
    · rw [hrep, hdel]
      exact hgate ell₀ hgateKey (θ h)
  unfold Setup5.colLik
  calc
    (∏ h : Fin (colLen5 (X.p.s n) ell),
        ratio5 ((X.priorRep H.1 ell K.1.1 z).w (θ h))
          ((X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).w (θ h))) ≤
      ∏ h : Fin (colLen5 (X.p.s n) ell), B := by
        apply Finset.prod_le_prod₀
        · intro h hh
          exact Lane_q_s05_hist1b.ratio5_nonneg
            ((X.priorRep H.1 ell K.1.1 z).nonneg (θ h))
            ((X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).nonneg (θ h))
        · intro h hh
          exact hratio h
    _ = B ^ colLen5 (X.p.s n) ell := by simp
    _ = Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K) *
          colLen5 (X.p.s n) ell) := by
        dsimp [B]
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

theorem optional_block_hit_lower5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (K : X.Ty) (t : CubeVertex (X.p.m n))
    (hbase : X.baseLaw.w H.1 ≠ 0) (hstep1 : X.Step1Pass H.1)
    (hstep2 : X.Step2Pass H) (hType : X.TypeOccurs K) (hOpt : X.OptOccurs K t)
    (hhigh : K.2.2 = none)
    (hprefix : X.p.typeSegs n K ≤ X.p.uSeg n ((X.optKeyOf K t).level + 1)) :
    (X.blockLaw H K).pr (fun z : X.Block K =>
      X.BlockHits K z (H.2 (X.optKeyOf K t)
        (Fin.cast (by simp [Setup5.optKeyOf, colLen5]) (0 : Fin 1)))) ≥
      Real.exp (-((X.p.a 1 + X.p.delta) *
        ((X.p.q0 : ℝ) * X.p.typeSegs n K))) := by
  classical
  let ell : X.Key := X.optKeyOf K t
  let y : Fin N := H.2 ell (Fin.cast (by simp [ell, Setup5.optKeyOf, colLen5]) (0 : Fin 1))
  let ell₀ : X.Key := .inl (K.1, (fun _ : Fin (X.p.m n) => false),
    ⟨X.p.J n, Nat.lt_succ_self _⟩)
  let oldMass : ℝ := X.blockMass H K K.2.1
  let newMass : ℝ := X.blockMass H K (insert ell K.2.1)
  let C : ℝ := Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K))
  have hellLow : ell = .inl (K.1, t, ⟨X.p.J n, Nat.lt_succ_self _⟩) := by
    simp [ell, Setup5.optKeyOf]
  have hellCoarse : ell.coarse = ell₀.coarse := by
    simp [ell₀, ell, Setup5.optKeyOf, HiddenKey5.coarse]
  have hellLevel : ell.level = ell₀.level := by
    simp [ell₀, ell, Setup5.optKeyOf, HiddenKey5.level]
  have hellGate : ell₀ ∈ X.gateKeys K := by
    simp [ell₀, Setup5.gateKeys, hhigh]
  have hgate : X.blockGate H.1 K (X.trueBlock H.1 K) :=
    Lane_q_s05_hist1b.blockGate_trueBlock_of_step1Pass X H K hType hstep1
  have hcov := L5_1e_cover X.g (X.p.J n)
  have hBounds : X.Step2Bounds H K :=
    Setup5.L5_1d_bounds n N E G X hcov.2 H hbase hstep1 K hType (hstep2.1 K hType)
  have hnotOpt : ¬ X.optFail H K t := hstep2.2 K t hOpt
  have hmassNonneg : 0 ≤ oldMass := by
    dsimp [oldMass, Setup5.blockMass]
    apply Finset.sum_nonneg
    intro z hz
    exact Lane_q_s05_hist1b.blockWeight_nonneg X H K K.2.1 z
  have hmassPos : 0 < oldMass := by
    by_contra hpos
    have hzero : oldMass = 0 := le_antisymm (le_of_not_gt hpos) hmassNonneg
    have hthreshold : 0 < Real.exp
        (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K : ℝ) *
          (∑ k ∈ K.2.1, (colLen5 (X.p.s n) k : ℝ)))) := Real.exp_pos _
    apply hstep2.1 K hType
    refine ⟨hgate, Or.inl ?_⟩
    rw [show X.blockMass H K K.2.1 = 0 by exact hzero]
    simpa [mul_assoc] using hthreshold
  have hOldMassLower :
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K : ℝ) *
        (∑ k ∈ K.2.1, (colLen5 (X.p.s n) k : ℝ)))) ≤ oldMass := by
    by_contra h
    have hlt := lt_of_not_ge h
    apply hstep2.1 K hType
    exact ⟨hgate, Or.inl (by simpa [oldMass, Setup5.blockMass] using hlt)⟩
  have hnewMassLower :
      Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) * oldMass ≤ newMass := by
    by_contra h
    have hlt := lt_of_not_ge h
    apply hnotOpt
    exact ⟨hgate, by simpa [Setup5.optFail, oldMass, newMass, ell, mul_assoc] using hlt⟩
  by_cases hellMem : ell ∈ K.2.1
  · have hSupport (z : X.Block K) (hz : (X.blockLaw H K).w z ≠ 0) :
        X.BlockHits K z y := hBounds.2.2 z hz ell hellMem _
    have hhit : (X.blockLaw H K).pr (fun z : X.Block K =>
        X.BlockHits K z y) = 1 := by
      unfold FinProb.pr
      calc
        (∑ z, if X.BlockHits K z y then (X.blockLaw H K).w z else 0) =
            ∑ z, (X.blockLaw H K).w z := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hw : (X.blockLaw H K).w z = 0
          · simp [hw]
          · simp [hSupport z hw]
        _ = 1 := (X.blockLaw H K).sum_eq_one
    have hExpLe : Real.exp (-((X.p.a 1 + X.p.delta) *
        ((X.p.q0 : ℝ) * X.p.typeSegs n K))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have ha1 : 0 < X.p.a 1 := by
        have horder := X.p.ha_order (0 : Fin 9) (1 : Fin 9) (by decide)
        have ha0 := X.p.ha0
        linarith
      have hcoef : 0 ≤ X.p.a 1 + X.p.delta :=
        add_nonneg ha1.le X.p.hdelta.1.le
      have hlen0 : 0 ≤ (X.p.q0 : ℝ) * X.p.typeSegs n K := by positivity
      exact neg_nonpos.mpr (mul_nonneg hcoef hlen0)
    have hhit' : (X.blockLaw H K).pr (fun z : X.Block K =>
        X.BlockHits K z (H.2 (X.optKeyOf K t)
          (Fin.cast (by simp [Setup5.optKeyOf, colLen5]) (0 : Fin 1)))) = 1 := by
      simpa [y, ell] using hhit
    exact hExpLe.trans_eq hhit'.symm
  · have hcoarseRep (y : Fin N) (z : X.Block K) :
        (X.priorRep H.1 ell K.1.1 z).w y =
          (X.priorRep H.1 ell₀ K.1.1 z).w y := by
      have hw : ∀ y, X.colWeight H.1 ell (X.replaceStream H.1.2.2 K.1.1 z)
          (fun _ _ => True) y =
          X.colWeight H.1 ell₀ (X.replaceStream H.1.2.2 K.1.1 z)
            (fun _ _ => True) y := by
        intro y
        simp [Setup5.colWeight, hellCoarse, hellLevel]
      have hLaw : X.priorRep H.1 ell K.1.1 z = X.priorRep H.1 ell₀ K.1.1 z := by
        unfold Setup5.priorRep
        congr 1
      exact congrArg (fun L : Law N => L.w y) hLaw
    have hcoarseDel (y : Fin N) :
        (X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).w y =
          (X.priorDel H.1 ell₀ K.1.1 (X.p.typeSegs n K)).w y := by
      have hw : ∀ y, X.colWeight H.1 ell H.1.2.2
          (fun w s => ¬ (w = K.1.1 ∧ (s : ℕ) < X.p.typeSegs n K)) y =
          X.colWeight H.1 ell₀ H.1.2.2
            (fun w s => ¬ (w = K.1.1 ∧ (s : ℕ) < X.p.typeSegs n K)) y := by
        intro y
        simp [Setup5.colWeight, hellCoarse, hellLevel]
      have hLaw : X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K) =
          X.priorDel H.1 ell₀ K.1.1 (X.p.typeSegs n K) := by
        unfold Setup5.priorDel
        congr 1
      exact congrArg (fun L : Law N => L.w y) hLaw
    have hNotMemKeys : ell ∉ K.2.1 := hellMem
    have hWeightIns (z : X.Block K) :
        X.blockWeight H K (insert ell K.2.1) z =
          X.blockWeight H K K.2.1 z * X.colLik H.1 K ell z (H.2 ell) := by
      unfold Setup5.blockWeight Setup5.colLik
      rw [Finset.prod_insert hNotMemKeys]
      ring
    have hNewMassEq : newMass =
        ∑ z, X.blockWeight H K K.2.1 z * X.colLik H.1 K ell z (H.2 ell) := by
      dsimp [newMass, Setup5.blockMass]
      apply Finset.sum_congr rfl
      intro z hz
      exact hWeightIns z
    have hLaw (z : X.Block K) : (X.blockLaw H K).w z =
        X.blockWeight H K K.2.1 z / oldMass := by
      simpa [oldMass, Setup5.blockLaw, Setup5.blockLawOn, Setup5.blockMass] using
        (Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg
          (fun z => X.blockWeight H K K.2.1 z) (X.fallbackBlock K) z
          (fun z => Lane_q_s05_hist1b.blockWeight_nonneg X H K K.2.1 z)
          (by simpa [oldMass, Setup5.blockMass] using hmassPos))
    have hExpEq : (X.blockLaw H K).expect (fun z => X.colLik H.1 K ell z (H.2 ell)) =
        newMass / oldMass := by
      unfold FinProb.expect
      calc
        _ = ∑ z, (X.blockWeight H K K.2.1 z / oldMass) *
              X.colLik H.1 K ell z (H.2 ell) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [hLaw z]
        _ = (∑ z, X.blockWeight H K K.2.1 z *
              X.colLik H.1 K ell z (H.2 ell)) / oldMass := by
          calc
            _ = ∑ z, (X.blockWeight H K K.2.1 z *
                X.colLik H.1 K ell z (H.2 ell)) / oldMass := by
              apply Finset.sum_congr rfl
              intro z hz
              field_simp [ne_of_gt hmassPos]
            _ = _ := by rw [Finset.sum_div]
        _ = newMass / oldMass := by rw [← hNewMassEq]
    have hExpLower :
        Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) ≤
          (X.blockLaw H K).expect (fun z => X.colLik H.1 K ell z (H.2 ell)) := by
      have hdiv := div_le_div_of_nonneg_right hnewMassLower hmassPos.le
      have hself :
          (Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) * oldMass) / oldMass =
            Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) := by
        field_simp [ne_of_gt hmassPos]
      rw [← hExpEq] at hdiv
      calc
        _ = (Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) * oldMass) / oldMass :=
          hself.symm
        _ ≤ _ := hdiv
    have hAliasGate (z : X.Block K) (hz : X.blockWeight H K K.2.1 z ≠ 0) :
        X.blockGate H.1 K z := by
      have hfac : X.blockBase H.1 K z * (if X.blockGate H.1 K z then (1 : ℝ) else 0) ≠ 0 := by
        have hweight := hz
        unfold Setup5.blockWeight at hweight
        exact (mul_ne_zero_iff.mp hweight).1
      have hgateFactor : (if X.blockGate H.1 K z then (1 : ℝ) else 0) ≠ 0 :=
        (mul_ne_zero_iff.mp hfac).2
      by_contra hnot
      simp [hnot] at hgateFactor
    have hcolBound (z : X.Block K) (hz : X.blockWeight H K K.2.1 z ≠ 0) :
        X.colLik H.1 K ell z (H.2 ell) ≤ C := by
      have h := colLik_le_of_gate_alias5 X H K ell ell₀ z (H.2 ell)
        hellGate hellCoarse hellLevel (hAliasGate z hz)
      have hcolLen : colLen5 (X.p.s n) ell = 1 := by
        simp [ell, Setup5.optKeyOf, colLen5]
      simpa [C, hcolLen] using h
    have hblockBase (z : X.Block K) (hz : X.blockWeight H K K.2.1 z ≠ 0) :
        X.blockBase H.1 K z ≠ 0 := by
      have hweight := hz
      unfold Setup5.blockWeight at hweight
      have hfac : X.blockBase H.1 K z * (if X.blockGate H.1 K z then (1 : ℝ) else 0) ≠ 0 :=
        (mul_ne_zero_iff.mp hweight).1
      exact (mul_ne_zero_iff.mp hfac).1
    have hhitOfCol (z : X.Block K) (hw : (X.blockLaw H K).w z ≠ 0)
        (hcol : X.colLik H.1 K ell z (H.2 ell) ≠ 0) : X.BlockHits K z y := by
      have hwOld : X.blockWeight H K K.2.1 z ≠ 0 := by
        intro hwzero
        apply hw
        rw [hLaw z, hwzero]
        simp
      have hratioNe (j : Fin (colLen5 (X.p.s n) ell)) :
          ratio5 ((X.priorRep H.1 ell K.1.1 z).w (H.2 ell j))
            ((X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).w (H.2 ell j)) ≠ 0 := by
        have hprod := hcol
        unfold Setup5.colLik at hprod
        exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ _)
      have hy : (X.priorRep H.1 ell K.1.1 z).w y ≠ 0 := by
        intro hzrep
        apply hratioNe (Fin.cast (by simp [ell, Setup5.optKeyOf, colLen5]) (0 : Fin 1))
        simp [ratio5, y, hzrep]
      have hcover : K.1.1 ∈ binList5 ell.coarse := by
        simp only [ell, Setup5.optKeyOf, HiddenKey5.coarse]
        unfold binList5
        split_ifs with h
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
        · simp
      exact Lane_sol_s05_centres.priorRep_block_hits X H K ell z y hbase
        (hblockBase z hwOld) hcover hprefix hy
    have hcolNonneg (z : X.Block K) : 0 ≤ X.colLik H.1 K ell z (H.2 ell) := by
      unfold Setup5.colLik
      apply Finset.prod_nonneg
      intro j hj
      exact Lane_q_s05_hist1b.ratio5_nonneg
        ((X.priorRep H.1 ell K.1.1 z).nonneg (H.2 ell j))
        ((X.priorDel H.1 ell K.1.1 (X.p.typeSegs n K)).nonneg (H.2 ell j))
    have hPoint (z : X.Block K) :
        (X.blockLaw H K).w z * X.colLik H.1 K ell z (H.2 ell) ≤
          C * (if X.BlockHits K z y then (X.blockLaw H K).w z else 0) := by
      by_cases hw : (X.blockLaw H K).w z = 0
      · simp [hw]
      · by_cases hh : X.BlockHits K z y
        · simp [hh]
          calc
            (X.blockLaw H K).w z * X.colLik H.1 K ell z (H.2 ell) =
                X.colLik H.1 K ell z (H.2 ell) * (X.blockLaw H K).w z := by ring
            _ ≤ C * (X.blockLaw H K).w z :=
              mul_le_mul_of_nonneg_right (hcolBound z (by
                intro hwzero
                apply hw
                rw [hLaw z, hwzero]
                simp)) ((X.blockLaw H K).nonneg z)
        · have hcol : X.colLik H.1 K ell z (H.2 ell) = 0 := by
            by_contra hne
            exact hh (hhitOfCol z hw hne)
          simp [hh, hcol]
    have hExpUpper :
        (X.blockLaw H K).expect (fun z => X.colLik H.1 K ell z (H.2 ell)) ≤
          (X.blockLaw H K).pr (fun z => X.BlockHits K z y) * C := by
      unfold FinProb.expect FinProb.pr
      calc
        _ ≤ ∑ z, C * (if X.BlockHits K z y then (X.blockLaw H K).w z else 0) :=
          Finset.sum_le_sum fun z hz => hPoint z
        _ = C * ∑ z, if X.BlockHits K z y then (X.blockLaw H K).w z else 0 := by
          rw [← Finset.mul_sum]
        _ = (∑ z, if X.BlockHits K z y then (X.blockLaw H K).w z else 0) * C := by ring
    have hCpos : 0 < C := by dsimp [C]; exact Real.exp_pos _
    have hprob :
        Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) / C ≤
          (X.blockLaw H K).pr (fun z => X.BlockHits K z y) := by
      apply (div_le_iff₀ hCpos).2
      exact le_trans hExpLower hExpUpper
    have hCeq : C = Real.exp (X.p.a 1 * ((X.p.q0 : ℝ) * X.p.typeSegs n K)) := rfl
    have hExpEq :
        Real.exp (-(X.p.delta * (X.p.q0 : ℝ) * X.p.uStarSeg n)) / C =
          Real.exp (-((X.p.a 1 + X.p.delta) * ((X.p.q0 : ℝ) * X.p.typeSegs n K))) := by
      rw [hCeq, show X.p.uStarSeg n = X.p.typeSegs n K by simp [Params5.typeSegs, hhigh]]
      rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
      congr 1
      ring
    rw [hExpEq] at hprob
    exact hprob

end

theorem pi_pr_coordinate_event {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (A : Ω i → Prop) :
    (FinProb.pi P).pr (fun ω => A (ω i)) = (P i).pr A := by
  classical
  let C : ∀ j, Ω j → Prop := fun j z => if h : j = i then A (h ▸ z) else True
  have hEvent : (fun ω : ∀ j, Ω j => ∀ j, C j (ω j)) = (fun ω => A (ω i)) := by
    funext ω
    apply propext
    constructor
    · intro h
      have hh := h i
      simpa [C] using hh
    · intro h j
      by_cases hj : j = i
      · subst j
        simpa [C] using h
      · simp [C, hj]
  rw [← hEvent, pi_pr_forall]
  have hterm (j : ι) : (P j).pr (C j) = if j = i then (P i).pr A else 1 := by
    by_cases hj : j = i
    · subst j
      simp [C]
    · simp [C, hj, FinProb.pr, (P j).sum_eq_one]
  rw [Finset.prod_congr rfl fun j hj => hterm j]
  simp [FinProb.pr]

theorem pi_pr_depends_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (i : ι) (A : (∀ j, Ω j) → Prop)
    (hA : ∀ ω ω', ω i = ω' i → (A ω ↔ A ω')) (ω₀ : ∀ j, Ω j) :
    (FinProb.pi P).pr A =
      (P i).pr (fun x => A (Function.update ω₀ i x)) := by
  classical
  let B : Ω i → Prop := fun x => A (Function.update ω₀ i x)
  have hEvent : A = (fun ω => B (ω i)) := by
    funext ω
    apply propext
    exact hA ω (Function.update ω₀ i (ω i)) (by simp)
  calc
    (FinProb.pi P).pr A = (FinProb.pi P).pr (fun ω => B (ω i)) := by
      exact congrArg (fun F : (∀ j, Ω j) → Prop => (FinProb.pi P).pr F) hEvent
    _ = (P i).pr B := pi_pr_coordinate_event P i B
    _ = (P i).pr (fun x => A (Function.update ω₀ i x)) := rfl

theorem pi_pr_dependsOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (S : Finset ι) (A : (∀ i, Ω i) → Prop)
    (ω₀ : ∀ i, Ω i) (hA : FinProb.DependsOn A S) :
    (FinProb.pi P).pr A =
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr
        (fun a => A ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm
          (a, fun i => ω₀ i.1))) := by
  classical
  let f : (∀ i, Ω i) → ℝ := fun ω => if A ω then 1 else 0
  have hdep : FinProb.DependsOn f S := by
    intro ω ω' h
    have hiff := hA ω ω' h
    simp [f, hiff]
  have hind : (FinProb.pi P).expect f = (FinProb.pi P).pr A := by
    unfold FinProb.expect FinProb.pr f
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : A ω <;> simp [h]
  rw [← hind, FinProb.pi_expect_depends P S f ω₀ hdep]
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω
  have hfinal :
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).expect
        (fun a => f (e.symm (a, fun i => ω₀ i.1))) =
      (FinProb.pi (fun i : {i // i ∈ S} => P i.1)).pr
        (fun a => A (e.symm (a, fun i => ω₀ i.1))) := by
    unfold FinProb.expect FinProb.pr f
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : A (e.symm (a, fun i => ω₀ i.1)) <;> simp [h]
  exact hfinal

theorem typeBlocks_tail_eventually5 (p : Params5 γ K' χ) (C : ℝ)
    (hC : p.Kh * (p.q0 : ℝ) + (p.q0 : ℝ) / p.eta +
      (p.q0 : ℝ) / p.K1 + 10 ≤ C) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ K : EvenType5 n (p.m n) (p.J n),
      (p.typeBlocks n K : ℝ) * Real.exp (-C * (p.typeSegs n K : ℝ)) ≤ Real.exp (-100) := by
  classical
  let q0 : ℝ := p.q0
  let Dlo : ℝ := 1 + 2 * p.K2 / p.K1
  let Dhi : ℝ := 2 * Real.exp (p.Kh * q0) + 1
  let L : ℝ := 1 + (q0 / (4 * p.K1)) * Real.log Dlo +
    (q0 / p.eta) * Real.log Dhi + 50 * q0 / (C * p.K1) +
      200 * q0 / (C * p.eta)
  have hq0 : 0 < q0 := by dsimp [q0]; exact_mod_cast p.hq0.1
  have hCpos : 0 < C := by
    have hterms : 0 ≤ p.Kh * q0 + q0 / p.eta + q0 / p.K1 + 10 := by positivity
    linarith [hC]
  have hDlo : 1 < Dlo := by
    have hratio : 0 < p.K2 / p.K1 := div_pos p.hK2 p.hK1
    dsimp [Dlo]
    linarith
  have hDhi : 1 < Dhi := by
    have he : 0 < Real.exp (p.Kh * q0) := Real.exp_pos _
    dsimp [Dhi]
    linarith
  have hDloLog : 0 ≤ Real.log Dlo := Real.log_nonneg hDlo.le
  have hDhiLog : 0 ≤ Real.log Dhi := Real.log_nonneg hDhi.le
  have hLpos : 0 < L := by
    have hcoef1 : 0 ≤ q0 / (4 * p.K1) := by positivity
    have hcoef2 : 0 ≤ q0 / p.eta := by positivity
    have hcoef3 : 0 ≤ 50 * q0 / (C * p.K1) := by positivity
    have hcoef4 : 0 ≤ 200 * q0 / (C * p.eta) := by positivity
    dsimp [L]
    nlinarith [mul_nonneg hcoef1 hDloLog, mul_nonneg hcoef2 hDhiLog]
  have hmT := Lane_sol_s05_h1.tendsto_m p
  have hlogT : Filter.Tendsto (fun n : ℕ => Real.log (p.m n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hmT
  have hscale : ∀ᶠ n : ℕ in Filter.atTop,
      1 < p.m n ∧ L ≤ Real.log (p.m n : ℝ) := by
    filter_upwards [hmT.eventually_gt_atTop 1, hlogT.eventually_ge_atTop L] with n hmn hln
    constructor
    · exact_mod_cast hmn
    · exact hln
  filter_upwards [hscale] with n hn
  rcases hn with ⟨hm, hlog⟩
  have hmR : (1 : ℝ) < (p.m n : ℝ) := by exact_mod_cast hm
  have hlogpos : 0 < Real.log (p.m n : ℝ) := Real.log_pos hmR
  have huStarLower : (p.eta / q0) * Real.log (p.m n : ℝ) ≤ p.uStarSeg n := by
    have hceil : p.eta * Real.log (p.m n : ℝ) / q0 ≤ (p.uStarSeg n : ℝ) := Nat.le_ceil _
    have heq : p.eta * Real.log (p.m n : ℝ) / q0 =
        (p.eta / q0) * Real.log (p.m n : ℝ) := by field_simp [ne_of_gt hq0]; ring
    rw [heq] at hceil
    exact hceil
  have huLowLower (j : ℕ) :
      (4 * p.K1 / q0) * Real.log (p.m n : ℝ) ≤ p.uSeg n j := by
    have hu := Lane_sol_s05_h5l.uSeg_lower p n j
    have hj : (4 : ℝ) ≤ (j : ℝ) + 4 := by exact_mod_cast (show 4 ≤ j + 4 by omega)
    have hmul := mul_le_mul_of_nonneg_right hj hlogpos.le
    have hmul' := mul_le_mul_of_nonneg_left hmul p.hK1.le
    have hu' : 4 * p.K1 * Real.log (p.m n : ℝ) ≤ q0 * p.uSeg n j := by
      calc
        _ = p.K1 * (4 * Real.log (p.m n : ℝ)) := by ring
        _ ≤ p.K1 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := hmul'
        _ ≤ q0 * p.uSeg n j := by simpa [q0] using hu
    have hq0' : 0 < q0 := hq0
    have heq : (4 * p.K1 / q0) * Real.log (p.m n : ℝ) =
        (4 * p.K1 * Real.log (p.m n : ℝ)) / q0 := by field_simp [ne_of_gt hq0']; ring
    rw [heq]
    exact (div_le_iff₀ hq0').2 (by simpa [q0] using hu')
  have huStarDhi : Real.log Dhi ≤ p.uStarSeg n := by
    have hcoef : 0 < q0 / p.eta := by positivity
    have hcoefLo : 0 ≤ q0 / (4 * p.K1) := by positivity
    have hcoefHi : 0 ≤ q0 / p.eta := by positivity
    have hLpiece : (q0 / p.eta) * Real.log Dhi ≤ L := by
      dsimp [L]
      nlinarith [mul_nonneg hcoefLo hDloLog, mul_nonneg hcoefHi hDhiLog]
    have hbound := (le_trans hLpiece hlog)
    have hmul := mul_le_mul_of_nonneg_left huStarLower hcoef.le
    have heq : (q0 / p.eta) * ((p.eta / q0) * Real.log (p.m n : ℝ)) =
        Real.log (p.m n : ℝ) := by
      field_simp [ne_of_gt hq0, ne_of_gt p.heta.1]
    rw [← heq]
    exact le_trans hbound hmul
  have huLowDlo (j : ℕ) : Real.log Dlo ≤ p.uSeg n j := by
    have hcoef : 0 < q0 / (4 * p.K1) := by positivity
    have hcoefLo : 0 ≤ q0 / (4 * p.K1) := by positivity
    have hcoefHi : 0 ≤ q0 / p.eta := by positivity
    have hLpiece : (q0 / (4 * p.K1)) * Real.log Dlo ≤ L := by
      dsimp [L]
      nlinarith [mul_nonneg hcoefLo hDloLog, mul_nonneg hcoefHi hDhiLog]
    have hbound := (le_trans hLpiece hlog)
    have hmul := mul_le_mul_of_nonneg_left (huLowLower j) hcoef.le
    have heq : (q0 / (4 * p.K1)) * ((4 * p.K1 / q0) * Real.log (p.m n : ℝ)) =
        Real.log (p.m n : ℝ) := by
      field_simp [ne_of_gt hq0, ne_of_gt p.hK1]
    rw [← heq]
    exact le_trans hbound hmul
  have huStar100 : 100 ≤ (C / 2) * (p.uStarSeg n : ℝ) := by
    have hcoef : 0 < C / 2 * (p.eta / q0) := by positivity
    have hcoefLo : 0 ≤ q0 / (4 * p.K1) := by positivity
    have hcoefHi : 0 ≤ q0 / p.eta := by positivity
    have hpiece : 200 * q0 / (C * p.eta) ≤ L := by
      dsimp [L]
      nlinarith [mul_nonneg hcoefLo hDloLog, mul_nonneg hcoefHi hDhiLog]
    have hbound := le_trans hpiece hlog
    have hmul := mul_le_mul_of_nonneg_left huStarLower hcoef.le
    have heq : (C / 2 * (p.eta / q0)) * (200 * q0 / (C * p.eta)) = 100 := by
      field_simp [ne_of_gt hCpos, ne_of_gt p.heta.1, ne_of_gt hq0]
      ring
    have hlog100 : 100 ≤ (C / 2 * (p.eta / q0)) * Real.log (p.m n : ℝ) := by
      calc
        _ = (C / 2 * (p.eta / q0)) * (200 * q0 / (C * p.eta)) := by rw [heq]
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hcoef.le
    have hmul' : (C / 2 * (p.eta / q0)) * Real.log (p.m n : ℝ) ≤
        (C / 2) * (p.uStarSeg n : ℝ) := by
      calc
        _ = (C / 2) * ((p.eta / q0) * Real.log (p.m n : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left huStarLower (by positivity)
    exact hlog100.trans hmul'
  have huLow100 (j : ℕ) : 100 ≤ (C / 2) * (p.uSeg n j : ℝ) := by
    have hcoef : 0 < C / 2 * (4 * p.K1 / q0) := by positivity
    have hcoefLo : 0 ≤ q0 / (4 * p.K1) := by positivity
    have hcoefHi : 0 ≤ q0 / p.eta := by positivity
    have hpiece : 50 * q0 / (C * p.K1) ≤ L := by
      dsimp [L]
      nlinarith [mul_nonneg hcoefLo hDloLog, mul_nonneg hcoefHi hDhiLog]
    have hbound := le_trans hpiece hlog
    have hmul := mul_le_mul_of_nonneg_left (huLowLower j) hcoef.le
    have heq : (C / 2 * (4 * p.K1 / q0)) * (50 * q0 / (C * p.K1)) = 100 := by
      field_simp [ne_of_gt hCpos, ne_of_gt p.hK1, ne_of_gt hq0]
      ring
    have hlog100 : 100 ≤ (C / 2 * (4 * p.K1 / q0)) * Real.log (p.m n : ℝ) := by
      calc
        _ = (C / 2 * (4 * p.K1 / q0)) * (50 * q0 / (C * p.K1)) := by rw [heq]
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hcoef.le
    have hmul' : (C / 2 * (4 * p.K1 / q0)) * Real.log (p.m n : ℝ) ≤
        (C / 2) * (p.uSeg n j : ℝ) := by
      calc
        _ = (C / 2) * ((4 * p.K1 / q0) * Real.log (p.m n : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (huLowLower j) (by positivity)
    exact hlog100.trans hmul'
  intro K
  cases hType : K.2.2 with
  | none =>
    have hSeg : p.typeSegs n K = p.uStarSeg n := by simp [Params5.typeSegs, hType]
    have hBlocks : p.typeBlocks n K = p.poolBlocks n := by simp [Params5.typeBlocks, hType]
    rw [hSeg, hBlocks]
    have hPool := Lane_sol_s05_1f.poolBlocks_power_upper p n hm
    have hDhiExp : Dhi ≤ Real.exp (p.uStarSeg n) := by
      have h := (Real.log_le_iff_le_exp (by dsimp [Dhi]; positivity)).mp huStarDhi
      simpa [Dhi] using h
    have hmPower : (p.m n : ℝ) ^ (3 / 100 : ℝ) ≤
        Real.exp ((3 / 100 : ℝ) * (q0 / p.eta) * p.uStarSeg n) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero (by omega)) : (0 : ℝ) < p.m n)]
      apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ (3 / 100 : ℝ) * (q0 / p.eta) := by positivity
      have hmul := mul_le_mul_of_nonneg_left huStarLower hcoef
      have heq : ((3 / 100 : ℝ) * (q0 / p.eta)) *
          ((p.eta / q0) * Real.log (p.m n : ℝ)) =
          (3 / 100 : ℝ) * Real.log (p.m n : ℝ) := by
        field_simp [ne_of_gt hq0, ne_of_gt p.heta.1]
        ring
      rw [← heq]
      exact hmul
    have hpoolBound : (p.poolBlocks n : ℝ) ≤
        Real.exp ((1 + (3 / 100 : ℝ) * (q0 / p.eta)) * p.uStarSeg n) := by
      calc
        _ ≤ Dhi * (p.m n : ℝ) ^ (3 / 100 : ℝ) := by simpa [Dhi, q0] using hPool
        _ ≤ Real.exp (p.uStarSeg n) *
            Real.exp ((3 / 100 : ℝ) * (q0 / p.eta) * p.uStarSeg n) :=
          mul_le_mul hDhiExp hmPower (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
    have hCgap : 1 + (3 / 100 : ℝ) * (q0 / p.eta) ≤ C / 2 := by
      have hbase : p.Kh * q0 + q0 / p.eta + q0 / p.K1 + 10 ≤ C := by
        simpa [q0] using hC
      have hratio : 0 ≤ q0 / p.eta := by positivity
      have hratio2 : 0 ≤ q0 / p.K1 := by positivity
      have hKhq : 0 ≤ p.Kh * q0 := by positivity
      nlinarith [hKhq]
    have hBlocksExp : (p.poolBlocks n : ℝ) ≤ Real.exp ((C / 2) * p.uStarSeg n) := by
      apply hpoolBound.trans
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCgap (Nat.cast_nonneg _))
    calc
      (p.poolBlocks n : ℝ) * Real.exp (-C * (p.uStarSeg n : ℝ)) ≤
          Real.exp ((C / 2) * p.uStarSeg n) * Real.exp (-C * (p.uStarSeg n : ℝ)) :=
        mul_le_mul_of_nonneg_right hBlocksExp (Real.exp_nonneg _)
      _ = Real.exp (-((C / 2) * p.uStarSeg n)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (-100) := Real.exp_le_exp.mpr (by linarith [huStar100])
  | some j =>
    have hSeg : p.typeSegs n K = p.uSeg n j.val := by simp [Params5.typeSegs, hType]
    have hBlocks : p.typeBlocks n K = p.lowBlocks n j.val := by simp [Params5.typeBlocks, hType]
    rw [hSeg, hBlocks]
    let x : ℝ := (j.val : ℝ) + 4
    let lm : ℝ := Real.log (p.m n : ℝ)
    let powm : ℝ := (p.m n : ℝ) ^ (1 / 50 : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    have hlm : 1 ≤ lm := by dsimp [lm]; exact le_trans (by norm_num) hlog
    have hlmpos : 0 < lm := lt_of_lt_of_le (by norm_num) hlm
    have hpowm : 1 ≤ powm := by
      dsimp [powm]
      exact Real.one_le_rpow (by exact_mod_cast (Nat.one_le_of_lt hm)) (by norm_num)
    have hden : 0 < q0 * p.uSeg n j.val := by
      have hqnat : 0 < p.q0 := p.hq0.1
      have hu : 0 < p.uSeg n j.val := Lane_sol_s05_h5l.uSeg_positive p n j.val hm
      dsimp [q0]
      exact mul_pos (by exact_mod_cast hqnat) (by exact_mod_cast hu)
    have hdenLower : p.K1 * x * lm ≤ q0 * p.uSeg n j.val := by
      simpa [q0, x, lm] using Lane_sol_s05_h5l.uSeg_lower p n j.val
    have hbase : 0 < p.K1 * x * lm := by positivity
    have hnumNonneg : 0 ≤ p.K2 * (x * lm + powm) := by positivity
    have hquot : p.K2 * (x * lm + powm) / (q0 * p.uSeg n j.val) ≤
        p.K2 * (x * lm + powm) / (p.K1 * x * lm) :=
      div_le_div_of_nonneg_left hnumNonneg hbase hdenLower
    have hquotEq : p.K2 * (x * lm + powm) / (p.K1 * x * lm) =
        (p.K2 / p.K1) * (1 + powm / (x * lm)) := by
      field_simp [ne_of_gt p.hK1, ne_of_gt hx, ne_of_gt hlmpos]
      <;> ring
    have hfrac : powm / (x * lm) ≤ powm / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      have hxlog : 4 ≤ x * lm := by
        dsimp [x, lm]
        nlinarith
      exact hxlog
    have hlowRaw : (p.lowBlocks n j.val : ℝ) ≤ Dlo * powm := by
      have hceil := Nat.ceil_lt_add_one (div_nonneg hnumNonneg hden.le)
      change (p.lowBlocks n j.val : ℝ) <
        p.K2 * (x * lm + powm) / (q0 * p.uSeg n j.val) + 1 at hceil
      have hrat := add_le_add_right (hquot.trans_eq hquotEq) 1
      have hrat' : p.K2 * (x * lm + powm) / (q0 * p.uSeg n j.val) + 1 ≤
          (p.K2 / p.K1) * (1 + powm / (x * lm)) + 1 := by
        simpa [add_comm] using hrat
      have hlow := le_trans hceil.le hrat'
      dsimp [Dlo]
      have hk : 0 ≤ p.K2 / p.K1 := by positivity
      nlinarith [hpowm, hfrac, hlow]
    have hDloExp : Dlo ≤ Real.exp (p.uSeg n j.val) := by
      have h := (Real.log_le_iff_le_exp (by dsimp [Dlo]; positivity)).mp (huLowDlo j.val)
      simpa [Dlo] using h
    have hpowmExp : powm ≤ Real.exp ((q0 / (200 * p.K1)) * p.uSeg n j.val) := by
      dsimp [powm]
      rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero (by omega)) : (0 : ℝ) < p.m n)]
      apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ q0 / (200 * p.K1) := by positivity
      have hmul := mul_le_mul_of_nonneg_left (huLowLower j.val) hcoef
      have heq : (q0 / (200 * p.K1)) *
          ((4 * p.K1 / q0) * Real.log (p.m n : ℝ)) =
          (1 / 50 : ℝ) * Real.log (p.m n : ℝ) := by
        field_simp [ne_of_gt hq0, ne_of_gt p.hK1]
        ring
      rw [← heq]
      exact hmul
    have hlowBound : (p.lowBlocks n j.val : ℝ) ≤
        Real.exp ((1 + q0 / (200 * p.K1)) * p.uSeg n j.val) := by
      calc
        _ ≤ Dlo * powm := hlowRaw
        _ ≤ Real.exp (p.uSeg n j.val) *
            Real.exp ((q0 / (200 * p.K1)) * p.uSeg n j.val) :=
          mul_le_mul hDloExp hpowmExp (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1 <;> ring
    have hCgap : 1 + q0 / (200 * p.K1) ≤ C / 2 := by
      have hbase : p.Kh * q0 + q0 / p.eta + q0 / p.K1 + 10 ≤ C := by
        simpa [q0] using hC
      have hratio : 0 ≤ q0 / p.K1 := by positivity
      have hratio' : 0 ≤ q0 / p.eta := by positivity
      have hKhq : 0 ≤ p.Kh * q0 := by positivity
      nlinarith [hKhq]
    have hBlocksExp : (p.lowBlocks n j.val : ℝ) ≤ Real.exp ((C / 2) * p.uSeg n j.val) := by
      apply hlowBound.trans
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCgap (Nat.cast_nonneg _))
    calc
      (p.lowBlocks n j.val : ℝ) * Real.exp (-C * (p.uSeg n j.val : ℝ)) ≤
          Real.exp ((C / 2) * p.uSeg n j.val) * Real.exp (-C * (p.uSeg n j.val : ℝ)) :=
        mul_le_mul_of_nonneg_right hBlocksExp (Real.exp_nonneg _)
      _ = Real.exp (-((C / 2) * p.uSeg n j.val)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (-100) := Real.exp_le_exp.mpr (by linarith [huLow100 j.val])

end HypercubeRamsey.Lane_q_s05_j34
