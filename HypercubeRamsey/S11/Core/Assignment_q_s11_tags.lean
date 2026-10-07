import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.Tools.Concentration_p_tools_conc
import HypercubeRamsey.S03.Clock.Inputs_p_clock_r1
import HypercubeRamsey.S11.Core.Experiment

namespace HypercubeRamsey.Lane_q_s11_tags

open Classical
open scoped BigOperators
open OAI.HypercubeRamsey

/-- Exponential-moment tail for independent indicators with a uniformly small success chance. -/
theorem independent_indicator_half_tail {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinProb α) {m : ℕ} (A : Fin m → α → Prop) (η : ℝ)
    (hsmall : η ≤ 1 / 255)
    (hA : ∀ j, P.pr (A j) ≤ η) :
    (FinProb.pi fun _ : Fin m => P).pr
      (fun ω => (m : ℝ) / 2 <
        ((Finset.univ.filter fun j : Fin m => A j (ω j)).card : ℕ)) ≤ (1 / 8 : ℝ) ^ m := by
  classical
  let Q : FinProb (∀ j : Fin m, α) := FinProb.pi fun _ : Fin m => P
  let c : (∀ j : Fin m, α) → ℕ := fun ω => (Finset.univ.filter fun j : Fin m => A j (ω j)).card
  let F : (∀ j : Fin m, α) → ℝ := fun ω => (256 : ℝ) ^ c ω
  have hFnonneg : ∀ ω, 0 ≤ F ω := fun ω => by positivity [F]
  have hsingle (j : Fin m) :
      P.expect (fun a => if A j a then (256 : ℝ) else 1) = 1 + 255 * P.pr (A j) := by
    classical
    have hcompl : P.pr (fun a => ¬ A j a) = 1 - P.pr (A j) := by
      have hpA : P.pr (A j) = ∑ a ∈ Finset.univ.filter (A j), P.w a := by
        unfold FinProb.pr
        rw [Finset.sum_filter]
      have hpNot : P.pr (fun a => ¬ A j a) =
          ∑ a ∈ Finset.univ.filter (fun a => ¬ A j a), P.w a := by
        unfold FinProb.pr
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : A j a <;> simp [h]
      have hsum :
          (∑ a ∈ Finset.univ.filter (A j), P.w a) +
            ∑ a ∈ Finset.univ.filter (fun a => ¬ A j a), P.w a = 1 := by
        simpa [P.sum_eq_one] using
          (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
            (p := A j) (f := fun a => P.w a))
      have hsplit : P.pr (A j) + P.pr (fun a => ¬ A j a) = 1 := by
        rw [hpA, hpNot]
        exact hsum
      linarith
    have hexpect : P.expect (fun a => if A j a then (256 : ℝ) else 1) =
        256 * P.pr (A j) + P.pr (fun a => ¬ A j a) := by
      unfold FinProb.expect FinProb.pr
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : A j a <;> simp [h] <;> ring
    rw [hexpect, hcompl]
    ring
  have hexpect : Q.expect F ≤ (2 : ℝ) ^ m := by
    rw [show F = (fun ω => ∏ j : Fin m, (if A j (ω j) then (256 : ℝ) else 1)) by
      funext ω
      dsimp [F, c]
      rw [Finset.prod_ite]
      simp]
    change (FinProb.pi (fun _ : Fin m => P)).expect
      (fun ω => ∏ j : Fin m, (if A j (ω j) then (256 : ℝ) else 1)) ≤ (2 : ℝ) ^ m
    have hprod := HypercubeRamsey.FinProb.expect_pi_prod
      (fun _ : Fin m => P) (fun j a => if A j a then (256 : ℝ) else 1)
    rw [hprod]
    change (Finset.univ.prod fun j : Fin m =>
      P.expect (fun a => if A j a then (256 : ℝ) else 1)) ≤ (2 : ℝ) ^ m
    have hleprod :
        Finset.univ.prod (fun j : Fin m => P.expect
          (fun a => if A j a then (256 : ℝ) else 1)) ≤
      Finset.univ.prod (fun _ : Fin m => (2 : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        have hge : 0 ≤ P.expect (fun a => if A j a then (256 : ℝ) else 1) := by
          unfold FinProb.expect
          apply Finset.sum_nonneg
          intro a ha
          apply mul_nonneg (P.nonneg a)
          change 0 ≤ (if A j a then (256 : ℝ) else 1)
          split_ifs <;> norm_num
        exact hge
      · intro j hj
        rw [hsingle j]
        have := hA j
        nlinarith [hsmall]
    exact le_trans hleprod (by simp)
  let q : ℕ := Nat.ceil ((m : ℝ) / 2)
  have hq : (m : ℝ) / 2 ≤ (q : ℝ) := by
    dsimp [q]
    exact Nat.le_ceil _
  have hden : (16 : ℝ) ^ m ≤ (256 : ℝ) ^ q := by
    have hmq : m ≤ 2 * q := by
      exact_mod_cast (by linarith : (m : ℝ) ≤ 2 * (q : ℝ))
    rw [show (256 : ℝ) = (16 : ℝ) ^ 2 by norm_num, ← pow_mul]
    exact_mod_cast (Nat.pow_le_pow_right (by omega) hmq)
  have hmark := FinProb.markov Q F ((256 : ℝ) ^ q) hFnonneg (by positivity)
  have hevent : ∀ ω, (m : ℝ) / 2 < (c ω : ℕ) → (256 : ℝ) ^ q ≤ F ω := by
    intro ω hcount
    have hqle : q ≤ c ω := by
      apply Nat.ceil_le.mpr
      exact_mod_cast le_of_lt hcount
    dsimp [F]
    exact_mod_cast Nat.pow_le_pow_right (by omega) hqle
  calc
    Q.pr (fun ω => (m : ℝ) / 2 < (c ω : ℕ)) ≤
        Q.pr (fun ω => (256 : ℝ) ^ q ≤ F ω) :=
      FinProb.pr_mono Q _ _ hevent
    _ ≤ Q.expect F / ((256 : ℝ) ^ q) := hmark
    _ ≤ (2 : ℝ) ^ m / ((256 : ℝ) ^ q) := by
      exact div_le_div_of_nonneg_right hexpect (by positivity)
    _ ≤ (1 / 8 : ℝ) ^ m := by
      have hpos : 0 < (16 : ℝ) ^ m := by positivity
      have hfrac : (2 : ℝ) ^ m / (16 : ℝ) ^ m = (1 / 8 : ℝ) ^ m := by
        rw [← div_pow]
        norm_num
      calc
        (2 : ℝ) ^ m / (256 : ℝ) ^ q ≤ (2 : ℝ) ^ m / (16 : ℝ) ^ m :=
          div_le_div_of_nonneg_left (by positivity) hpos hden
        _ = (1 / 8 : ℝ) ^ m := hfrac

private theorem pi_expect_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] (P : FinProb α) (i : ι) (g : α → ℝ) :
    (FinProb.pi fun _ : ι => P).expect (fun ω => g (ω i)) = P.expect g := by
  classical
  let f : ι → α → ℝ := fun j a => if j = i then g a else 1
  have hfun (ω : ι → α) : g (ω i) = ∏ j : ι, f j (ω j) := by
    dsimp [f]
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j hj hji
      simp [hji]
  calc
    (FinProb.pi fun _ : ι => P).expect (fun ω => g (ω i)) =
        (FinProb.pi fun _ : ι => P).expect (fun ω => ∏ j : ι, f j (ω j)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro ω hω
      simpa only [hfun]
    _ = ∏ j : ι, P.expect (f j) :=
      HypercubeRamsey.FinProb.expect_pi_prod (fun _ : ι => P) f
    _ = P.expect g := by
      dsimp [f]
      rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
      · simp
      · intro j hj hji
        simp [hji, FinProb.expect_const]

/-- Products of observations on distinct coordinates have independent expectations. -/
theorem pi_expect_prod_on_injective_coords {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {α : Type*} [Fintype α] (P : FinProb α)
    (f : κ → ι) (hf : Function.Injective f) (s : Finset κ) (g : κ → α → ℝ) :
    (FinProb.pi fun _ : ι => P).expect (fun ω => ∏ k ∈ s, g k (ω (f k))) =
      ∏ k ∈ s, P.expect (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.expect_const]
  | @insert a s ha ih =>
      let F : (ι → α) → ℝ := fun ω => ∏ k ∈ s, g k (ω (f k))
      let G : (ι → α) → ℝ := fun ω => g a (ω (f a))
      have hF : FinProb.DependsOn F (s.image f) := by
        intro ω ω' hagree
        dsimp [F]
        apply Finset.prod_congr rfl
        intro k hk
        rw [hagree (f k) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)]
      have hG : FinProb.DependsOn G {f a} := by
        intro ω ω' hagree
        dsimp [G]
        rw [hagree (f a) (Finset.mem_singleton_self _)]
      have hdisj : Disjoint (s.image f) ({f a} : Finset ι) := by
        apply Finset.disjoint_left.mpr
        intro i hi his
        rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
        have hka : k = a := hf (Finset.mem_singleton.mp his)
        subst k
        exact ha hk
      have hfactor := HypercubeRamsey.FinProb.pi_expect_mul_of_disjoint
        (fun _ : ι => P) F G (s.image f) {f a} hF hG hdisj
      have hcoordinate := pi_expect_coordinate P (f a) (g a)
      have hfun : (fun ω => ∏ k ∈ insert a s, g k (ω (f k))) =
          (fun ω => F ω * G ω) := by
        funext ω
        dsimp [F, G]
        rw [Finset.prod_insert ha]
        ring
      calc
        (FinProb.pi fun _ : ι => P).expect
            (fun ω => ∏ k ∈ insert a s, g k (ω (f k))) =
            (FinProb.pi fun _ : ι => P).expect (fun ω => F ω * G ω) := by rw [hfun]
        _ = (FinProb.pi fun _ : ι => P).expect F *
            (FinProb.pi fun _ : ι => P).expect G := hfactor
        _ = (∏ k ∈ s, P.expect (g k)) * P.expect (g a) := by rw [ih, hcoordinate]
        _ = ∏ k ∈ insert a s, P.expect (g k) := by
            rw [Finset.prod_insert ha]
            ring

private theorem expect_boosted_indicator {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) :
    P.expect (fun a => if A a then (256 : ℝ) else 1) =
      1 + 255 * P.pr A := by
  classical
  have hformula : P.expect (fun a => if A a then (256 : ℝ) else 1) =
      256 * P.pr A + P.pr (fun a => ¬ A a) := by
    unfold FinProb.expect FinProb.pr
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : A a <;> simp [h] <;> ring
  rw [hformula]
  linarith [HypercubeRamsey.Clock.finProb_pr_compl P A]

/-- Exponential-moment tail for rare indicators sampled at distinct coordinates of a larger product law. -/
theorem pi_pr_half_count_on_injective_coords {ι κ α : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α]
    (P : FinProb α) (f : κ → ι) (hf : Function.Injective f)
    (A : κ → α → Prop) (η : ℝ) (hsmall : η ≤ 1 / 255)
    (hA : ∀ j, P.pr (A j) ≤ η) :
    (FinProb.pi fun _ : ι => P).pr
      (fun ω => (Fintype.card κ : ℝ) / 2 <
        ((Finset.univ.filter fun j : κ => A j (ω (f j))).card : ℕ)) ≤
      (1 / 8 : ℝ) ^ (Fintype.card κ) := by
  classical
  let m : ℕ := Fintype.card κ
  let c : (ι → α) → ℕ := fun ω => (Finset.univ.filter fun j : κ => A j (ω (f j))).card
  let H : (ι → α) → ℝ := fun ω => ∏ j : κ, (if A j (ω (f j)) then (256 : ℝ) else 1)
  let Q : FinProb (ι → α) := FinProb.pi fun _ : ι => P
  have hpow (ω : ι → α) : H ω = (256 : ℝ) ^ c ω := by
    dsimp [H, c]
    rw [Finset.prod_ite]
    simp
  have hHnonneg : ∀ ω, 0 ≤ H ω := by
    intro ω
    unfold H
    apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> norm_num
  have hprod := pi_expect_prod_on_injective_coords P f hf Finset.univ
    (fun j a => if A j a then (256 : ℝ) else 1)
  have hbase : Q.expect H =
      ∏ j : κ, P.expect (fun a => if A j a then (256 : ℝ) else 1) := by
    simpa [Q, H] using hprod
  have hE : Q.expect H ≤ (2 : ℝ) ^ m := by
    rw [hbase]
    have hleprod :
        Finset.univ.prod (fun j : κ => P.expect
          (fun a => if A j a then (256 : ℝ) else 1)) ≤
          Finset.univ.prod (fun _ : κ => (2 : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        unfold FinProb.expect
        apply Finset.sum_nonneg
        intro a ha
        apply mul_nonneg (P.nonneg a)
        change 0 ≤ (if A j a then (256 : ℝ) else 1)
        split_ifs <;> norm_num
      · intro j hj
        rw [expect_boosted_indicator]
        have := hA j
        nlinarith [hsmall]
    exact le_trans hleprod (by simp [m])
  let q : ℕ := Nat.ceil ((m : ℝ) / 2)
  have hq : (m : ℝ) / 2 ≤ (q : ℝ) := by
    dsimp [q]
    exact Nat.le_ceil _
  have hden : (16 : ℝ) ^ m ≤ (256 : ℝ) ^ q := by
    have hmq : m ≤ 2 * q := by
      exact_mod_cast (by linarith : (m : ℝ) ≤ 2 * (q : ℝ))
    rw [show (256 : ℝ) = (16 : ℝ) ^ 2 by norm_num, ← pow_mul]
    exact_mod_cast (Nat.pow_le_pow_right (by omega) hmq)
  have hmark := FinProb.markov Q H ((256 : ℝ) ^ q) hHnonneg (by positivity)
  have hevent : ∀ ω, (m : ℝ) / 2 < (c ω : ℕ) → (256 : ℝ) ^ q ≤ H ω := by
    intro ω hcount
    have hqle : q ≤ c ω := by
      apply Nat.ceil_le.mpr
      exact_mod_cast le_of_lt hcount
    rw [hpow]
    exact_mod_cast Nat.pow_le_pow_right (by omega) hqle
  have hmain : Q.pr (fun ω => (m : ℝ) / 2 < (c ω : ℕ)) ≤ (1 / 8 : ℝ) ^ m := by
    calc
      Q.pr (fun ω => (m : ℝ) / 2 < (c ω : ℕ)) ≤
          Q.pr (fun ω => (256 : ℝ) ^ q ≤ H ω) :=
        FinProb.pr_mono Q _ _ hevent
      _ ≤ Q.expect H / ((256 : ℝ) ^ q) := hmark
      _ ≤ (2 : ℝ) ^ m / ((256 : ℝ) ^ q) := by
        exact div_le_div_of_nonneg_right hE (by positivity)
      _ ≤ (1 / 8 : ℝ) ^ m := by
        have hpos : 0 < (16 : ℝ) ^ m := by positivity
        have hfrac : (2 : ℝ) ^ m / (16 : ℝ) ^ m = (1 / 8 : ℝ) ^ m := by
          rw [← div_pow]
          norm_num
        calc
          (2 : ℝ) ^ m / (256 : ℝ) ^ q ≤ (2 : ℝ) ^ m / (16 : ℝ) ^ m :=
            div_le_div_of_nonneg_left (by positivity) hpos hden
          _ = (1 / 8 : ℝ) ^ m := hfrac
  simpa [m, Q] using hmain

theorem pi_pr_and_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : Type*} [Fintype α] (P : ∀ i : ι, FinProb α)
    (A B : (ι → α) → Prop) (s t : Finset ι)
    (hA : FinProb.DependsOn A s) (hB : FinProb.DependsOn B t) (hst : Disjoint s t) :
    (FinProb.pi P).pr (fun ω => A ω ∧ B ω) =
      (FinProb.pi P).pr A * (FinProb.pi P).pr B := by
  classical
  let Q : FinProb (ι → α) := FinProb.pi P
  let IA : (ι → α) → ℝ := fun ω => if A ω then 1 else 0
  let IB : (ι → α) → ℝ := fun ω => if B ω then 1 else 0
  have hIA : FinProb.DependsOn IA s := by
    intro ω ω' hagree
    change (if A ω then 1 else 0) = (if A ω' then 1 else 0)
    rw [hA ω ω' hagree]
  have hIB : FinProb.DependsOn IB t := by
    intro ω ω' hagree
    change (if B ω then 1 else 0) = (if B ω' then 1 else 0)
    rw [hB ω ω' hagree]
  have hAnd : Q.pr (fun ω => A ω ∧ B ω) = Q.expect (fun ω => IA ω * IB ω) := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h₁ : A ω <;> by_cases h₂ : B ω <;> simp [IA, IB, h₁, h₂]
  have hA' : Q.pr A = Q.expect IA := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : A ω <;> simp [IA, h]
  have hB' : Q.pr B = Q.expect IB := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : B ω <;> simp [IB, h]
  have hfactor := FinProb.pi_expect_mul_of_disjoint P IA IB s t hIA hIB hst
  calc
    Q.pr (fun ω => A ω ∧ B ω) = Q.expect (fun ω => IA ω * IB ω) := hAnd
    _ = Q.expect IA * Q.expect IB := hfactor
    _ = Q.pr A * Q.pr B := by rw [← hA', ← hB']


open HypercubeRamsey.S11.Core

private def xorCube {n : ℕ} (v w : CubeVertex n) : CubeVertex n :=
  fun j => Bool.xor (v j) (w j)

private theorem xorCube_even_of_even {n : ℕ} {v w : CubeVertex n}
    (hv : IsEvenRole v) (hw : IsEvenRole w) :
    IsEvenRole (xorCube v w) := by
  classical
  let A : Finset (Fin n) := Finset.univ.filter fun j => v j = true
  let B : Finset (Fin n) := Finset.univ.filter fun j => w j = true
  let I : Finset (Fin n) := A ∩ B
  let A' : Finset (Fin n) := A \ B
  let B' : Finset (Fin n) := B \ A
  have hset : (Finset.univ.filter fun j => xorCube v w j = true) = A' ∪ B' := by
    ext j
    by_cases hvj : v j = true <;> by_cases hwj : w j = true <;>
      simp [A, B, A', B', xorCube, hvj, hwj]
  have hdisj : Disjoint A' B' := by
    apply Finset.disjoint_left.mpr
    intro j hjA hjB
    simp only [A', B', Finset.mem_sdiff] at hjA hjB
    exact hjA.2 hjB.1
  have hcardA : A'.card + I.card = A.card := by
    simpa [A', I] using (Finset.card_sdiff_add_card_inter A B)
  have hcardB : B'.card + I.card = B.card := by
    simpa [B', I, Finset.inter_comm] using (Finset.card_sdiff_add_card_inter B A)
  have hcardX : (Finset.univ.filter fun j => xorCube v w j = true).card =
      A'.card + B'.card := by
    rw [hset, Finset.card_union_of_disjoint hdisj]
  rcases hv with ⟨a, ha⟩
  rcases hw with ⟨b, hb⟩
  have hAeven : A'.card + I.card = 2 * a := by rw [hcardA, ha]; ring
  have hBeven : B'.card + I.card = 2 * b := by rw [hcardB, hb]; ring
  refine ⟨a + b - I.card, ?_⟩
  rw [hcardX]
  omega

private theorem xorCube_right_twice {n : ℕ} (v d : CubeVertex n) :
    xorCube (xorCube v d) d = v := by
  funext j
  cases hv : v j <;> cases hd : d j <;> simp [xorCube, hv, hd]

private theorem xorCube_cubeFlip {n : ℕ} (v d : CubeVertex n) (j : Fin n) :
    xorCube (cubeFlip v j) d = cubeFlip (xorCube v d) j := by
  funext k
  by_cases h : k = j
  · subst k
    cases hv : v j <;> cases hd : d j <;> simp [xorCube, cubeFlip, hv, hd]
  · simp [xorCube, cubeFlip, h]

private theorem xorCube_slice_eq {n : ℕ} {v w : CubeVertex n}
    (hS : sliceOf v = sliceOf w) (x : CubeVertex n) :
    sliceOf (xorCube x (xorCube v w)) = sliceOf x := by
  funext j
  have hvw := congrFun hS j
  change v j.1 = w j.1 at hvw
  cases hx : x j.1 <;> cases hv : v j.1 <;> cases hw : w j.1 <;>
    simp_all [sliceOf, xorCube]

private theorem xorCube_preserves_even {n : ℕ} {d : CubeVertex n}
    (hd : IsEvenRole d) (v : CubeVertex n) :
    IsEvenRole (xorCube v d) ↔ IsEvenRole v := by
  constructor
  · intro hv
    have h := xorCube_even_of_even (v := xorCube v d) (w := d) hv hd
    rw [xorCube_right_twice] at h
    exact h
  · intro hv
    exact xorCube_even_of_even hv hd

private theorem flipOuter_injective {n : ℕ} (s : OuterWord n) :
    Function.Injective (flipOuter s) := by
  intro j k hjk
  by_contra hjk'
  have hval := congrFun hjk j
  simp [flipOuter, hjk'] at hval

theorem flipOuter_ne_self {n : ℕ} (s : OuterWord n) (j : OuterCoord n) :
    flipOuter s j ≠ s := by
  intro h
  have hval := congrFun h j
  cases hs : s j <;> simp [flipOuter, hs] at hval

/-- The high-degree tail among a slice's outer neighboring tags under one compatible tag. -/
theorem t2_neighbor_tail {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ δ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) (p : FinProb M.ι)
    (s : OuterWord n) (x : Fin N) (i : M.ι)
    (hcompat : CompatTag E M.G n δ M.μ (piRow M y₀) p i)
    (hx : (M.μ i).w x ≠ 0) :
    (rawTags M p).pr (fun t => (Fintype.card (OuterCoord n) : ℝ) / 2 <
      highCount M y₀ t s x) ≤ (1 / 8 : ℝ) ^ Fintype.card (OuterCoord n) := by
  let high : OuterCoord n → M.ι → Prop :=
    fun _ j => (4 / 5 : ℝ) < deg E M.G (piRow M y₀ j) x
  have hhigh : ∀ j : OuterCoord n, p.pr (high j) ≤ etaC := by
    intro j
    have h := hcompat.2.1 x hx
    simpa [high, FinProb.pr, Finset.sum_filter] using h
  have hsmall : etaC ≤ (1 : ℝ) / 255 := by norm_num [etaC]
  simpa [rawTags, highCount, high] using
    (pi_pr_half_count_on_injective_coords p (flipOuter s) (flipOuter_injective s)
      high etaC hsmall hhigh)

private noncomputable def outerCoordEquiv (n : ℕ) : OuterCoord n ≃ Fin (n - hIn n) where
  toFun j := ⟨j.1.val - hIn n, by omega⟩
  invFun k := ⟨⟨k.val + hIn n, Nat.add_lt_of_lt_sub k.isLt⟩, by
    change hIn n ≤ k.val + hIn n
    omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    simp
    omega
  right_inv k := by
    apply Fin.ext
    simp

theorem outerCoord_card (n : ℕ) : Fintype.card (OuterCoord n) = n - hIn n := by
  simpa using Fintype.card_congr (outerCoordEquiv n)

theorem hIn_le_half {n : ℕ} (hn : 4 ≤ n) : hIn n ≤ n / 2 := by
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hfloor : (hIn n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
    unfold hIn
    exact Nat.floor_le (by positivity)
  have hpow : (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hsqrt : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) / 2 := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [hnreal]
  have hreal : (hIn n : ℝ) ≤ (n : ℝ) / 2 := by linarith
  have hmul : 2 * (hIn n : ℝ) ≤ n := by nlinarith
  have hmulNat : 2 * hIn n ≤ n := by exact_mod_cast hmul
  omega

end HypercubeRamsey.Lane_q_s11_tags
