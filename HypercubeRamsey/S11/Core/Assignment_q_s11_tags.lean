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

private theorem pi_expect_glue_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (U : Finset ι) (f : (∀ i, Ω i) → ℝ) (ω₀ : ∀ i, Ω i)
    (hf : FinProb.DependsOn f U) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : U, Ω i.1), (∏ i : U, (P i.1).w (a i)) *
        f (S07.glue U ω₀ a) := by
  classical
  rw [FinProb.pi_expect_depends P U f ω₀ hf]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply hf _ _
  intro i hi
  simp [S07.glue, hi]

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

private def evenTranslate {n : ℕ} (d : CubeVertex n) (hd : IsEvenRole d) :
    EvenRole n ≃ EvenRole n where
  toFun v := ⟨xorCube v.1 d, (xorCube_preserves_even hd v.1).2 v.2⟩
  invFun v := ⟨xorCube v.1 d, (xorCube_preserves_even hd v.1).2 v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact xorCube_right_twice v.1 d
  right_inv v := by
    apply Subtype.ext
    exact xorCube_right_twice v.1 d

private def oddTranslate {n : ℕ} (d : CubeVertex n) (hd : IsEvenRole d) :
    OddRole n ≃ OddRole n where
  toFun v := ⟨xorCube v.1 d, fun he => v.2 ((xorCube_preserves_even hd v.1).mp he)⟩
  invFun v := ⟨xorCube v.1 d, fun he => v.2 ((xorCube_preserves_even hd v.1).mp he)⟩
  left_inv v := by
    apply Subtype.ext
    exact xorCube_right_twice v.1 d
  right_inv v := by
    apply Subtype.ext
    exact xorCube_right_twice v.1 d

private theorem evenTranslate_oddNbr {n : ℕ} (d : CubeVertex n) (hd : IsEvenRole d)
    (v : EvenRole n) (j : Fin n) :
    oddTranslate d hd (oddNbr v j) = oddNbr (evenTranslate d hd v) j := by
  apply Subtype.ext
  exact xorCube_cubeFlip v.1 d j

private theorem oddTranslate_evenNbr {n : ℕ} (d : CubeVertex n) (hd : IsEvenRole d)
    (b : OddRole n) (j : Fin n) :
    evenTranslate d hd (evenNbr b j) = evenNbr (oddTranslate d hd b) j := by
  apply Subtype.ext
  exact xorCube_cubeFlip b.1 d j

private def precompEquiv {α β : Type*} (e : α ≃ α) : (α → β) ≃ (α → β) where
  toFun f a := f (e a)
  invFun f a := f (e.symm a)
  left_inv f := by funext a; simp
  right_inv f := by funext a; simp

private theorem starOf_evenTranslate {n k N : ℕ}
    (d : CubeVertex n) (hd : IsEvenRole d) (W : EvenRole n → Fin k → Fin N) (b : OddRole n) :
    starOf (fun v => W (evenTranslate d hd v)) b = starOf W (oddTranslate d hd b) := by
  funext a
  funext l
  change W (evenTranslate d hd (evenNbr b a.1)) l =
    W (evenNbr (oddTranslate d hd b) a.1) l
  rw [oddTranslate_evenNbr]

private theorem xorCube_slice_eq_of_zero {n : ℕ} {d : CubeVertex n}
    (hd : sliceOf d = fun _ => false) (x : CubeVertex n) :
    sliceOf (xorCube x d) = sliceOf x := by
  funext j
  have hj := congrFun hd j
  have hj' : d j.1 = false := by simpa [sliceOf] using hj
  cases hx : x j.1 <;> simp [sliceOf, xorCube, hj', hx]

private theorem oddRowF_evenTranslate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (t : OuterWord n → M.ι)
    (d : CubeVertex n) (hd : IsEvenRole d) (hD : sliceOf d = fun _ => false)
    (W : EvenRole n → Fin (kTup n) → Fin N)
    (b : OddRole n) (y : Fin N) :
    oddRowF M t (fun v => W (evenTranslate d hd v)) b y =
      oddRowF M t W (oddTranslate d hd b) y := by
  have hslice : sliceOf (oddTranslate d hd b).1 = sliceOf b.1 := by
    simpa [oddTranslate] using xorCube_slice_eq_of_zero hD b.1
  have hstar := starOf_evenTranslate d hd W b
  unfold oddRowF
  rw [hslice, hstar]

private theorem oddProdW_evenTranslate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (t : OuterWord n → M.ι)
    (d : CubeVertex n) (hd : IsEvenRole d) (hD : sliceOf d = fun _ => false)
    (W : EvenRole n → Fin (kTup n) → Fin N)
    (f : OddRole n → Fin N) :
    oddProdW M t (fun v => W (evenTranslate d hd v)) (fun b => f (oddTranslate d hd b)) =
      oddProdW M t W f := by
  unfold oddProdW
  calc
    (∏ b, oddRowF M t (fun v => W (evenTranslate d hd v)) b
        (f (oddTranslate d hd b))) =
      ∏ b, oddRowF M t W (oddTranslate d hd b) (f (oddTranslate d hd b)) := by
        apply Finset.prod_congr rfl
        intro b hb
        rw [oddRowF_evenTranslate M t d hd hD]
    _ = ∏ b, oddRowF M t W b (f b) := by
      exact Fintype.prod_equiv (oddTranslate d hd) _ _ (by intro b; rfl)

private theorem evenRowF_evenTranslate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (d : CubeVertex n) (hd : IsEvenRole d)
    (hD : sliceOf d = fun _ => false) (f : OddRole n → Fin N)
    (v : EvenRole n) (x : Fin N) :
    evenRowF M y₀ p t (fun b => f (oddTranslate d hd b)) (evenTranslate d hd v) x =
      evenRowF M y₀ p t f v x := by
  have hslice : sliceOf (evenTranslate d hd v).1 = sliceOf v.1 := by
    simpa [evenTranslate] using xorCube_slice_eq_of_zero hD v.1
  have hoddNbr (j : Fin n) :
      oddTranslate d hd (oddNbr (evenTranslate d hd v) j) = oddNbr v j := by
    rw [evenTranslate_oddNbr]
    have hτ : evenTranslate d hd (evenTranslate d hd v) = v := by
      change (evenTranslate d hd).invFun ((evenTranslate d hd).toFun v) = v
      exact (evenTranslate d hd).left_inv v
    rw [hτ]
  have hinner :
      innerOut (fun b => f (oddTranslate d hd b)) (evenTranslate d hd v) = innerOut f v := by
    funext a
    exact congrArg f (hoddNbr a.1)
  unfold evenRowF
  rw [hslice, hinner]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simpa only [hoddNbr]

private theorem massFailGiven_evenTranslate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (d : CubeVertex n) (hd : IsEvenRole d)
    (hD : sliceOf d = fun _ => false) (W : EvenRole n → Fin (kTup n) → Fin N)
    (v : EvenRole n) :
    massFailGiven M y₀ p t (fun e => W (evenTranslate d hd e)) (evenTranslate d hd v)
        = massFailGiven M y₀ p t W v := by
  classical
  let eF : (OddRole n → Fin N) ≃ (OddRole n → Fin N) :=
    precompEquiv (oddTranslate d hd)
  have hMass (x : OddRole n → Fin N) :
      MassFail M y₀ p t (fun b => x (oddTranslate d hd b)) (evenTranslate d hd v) =
        MassFail M y₀ p t x v := by
    apply congrArg (fun z : ℝ => z < 1 / 2)
    apply Finset.sum_congr rfl
    intro y hy
    exact evenRowF_evenTranslate M y₀ p t d hd hD x v y
  unfold massFailGiven
  calc
    (∑ x : OddRole n → Fin N,
        oddProdW M t (fun e => W (evenTranslate d hd e)) x *
          (if MassFail M y₀ p t x (evenTranslate d hd v)
            then 1 else 0)) =
      ∑ x : OddRole n → Fin N,
        oddProdW M t (fun e => W (evenTranslate d hd e)) (eF x) *
          (if MassFail M y₀ p t (eF x) (evenTranslate d hd v) then 1 else 0) := by
        exact Fintype.sum_equiv eF.symm _ _ (by intro x; simp [eF, precompEquiv])
    _ = ∑ x : OddRole n → Fin N,
        oddProdW M t W x * (if MassFail M y₀ p t x v then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [show oddProdW M t (fun e => W (evenTranslate d hd e)) (eF x) =
            oddProdW M t W x by
              simpa [eF, precompEquiv] using oddProdW_evenTranslate M t d hd hD W x]
        have hfx : eF x = (fun b => x (oddTranslate d hd b)) := by
          funext b
          simp [eF, precompEquiv, oddTranslate]
        rw [hfx]
        rw [hMass x]

private theorem rawTuples_weight_evenTranslate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (t : OuterWord n → M.ι) (d : CubeVertex n) (hd : IsEvenRole d)
    (hD : sliceOf d = fun _ => false) (W : EvenRole n → Fin (kTup n) → Fin N) :
    (rawTuples M y₀ t).w (fun v => W (evenTranslate d hd v)) = (rawTuples M y₀ t).w W := by
  have hslice (v : EvenRole n) : sliceOf (evenTranslate d hd v).1 = sliceOf v.1 := by
    simpa [evenTranslate] using xorCube_slice_eq_of_zero hD v.1
  change (∏ v : EvenRole n,
      (tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n)).w
        (W (evenTranslate d hd v))) =
    ∏ v : EvenRole n,
      (tupLaw E M.G (M.μ (t (sliceOf v.1))) (y₀ (t (sliceOf v.1))) (kTup n)).w (W v)
  exact Fintype.prod_equiv (evenTranslate d hd) _ _ (by intro v; simp [hslice])

private theorem rawFail_evenTranslate {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (d : CubeVertex n) (hd : IsEvenRole d)
    (hD : sliceOf d = fun _ => false) (v : EvenRole n) :
    rawFail M y₀ p t (evenTranslate d hd v) = rawFail M y₀ p t v := by
  classical
  let eW : (EvenRole n → Fin (kTup n) → Fin N) ≃
      (EvenRole n → Fin (kTup n) → Fin N) := precompEquiv (evenTranslate d hd)
  have hsum :
      (∑ W, (rawTuples M y₀ t).w W * massFailGiven M y₀ p t W (evenTranslate d hd v)) =
        ∑ W, (rawTuples M y₀ t).w W * massFailGiven M y₀ p t W v := by
    calc
      (∑ W, (rawTuples M y₀ t).w W * massFailGiven M y₀ p t W (evenTranslate d hd v)) =
          ∑ W, (rawTuples M y₀ t).w (eW W) *
            massFailGiven M y₀ p t (eW W) (evenTranslate d hd v) := by
          exact Fintype.sum_equiv eW.symm _ _ (by intro W; simp [eW, precompEquiv])
      _ = ∑ W, (rawTuples M y₀ t).w W * massFailGiven M y₀ p t W v := by
          apply Finset.sum_congr rfl
          intro W hW
          have hWmap : eW W = (fun e => W (evenTranslate d hd e)) := rfl
          rw [hWmap, rawTuples_weight_evenTranslate M y₀ t d hd hD W]
          rw [massFailGiven_evenTranslate M y₀ p t d hd hD W v]
  unfold rawFail FinProb.expect
  exact hsum

theorem rawFail_same_slice {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (v w : EvenRole n)
    (hs : sliceOf v.1 = sliceOf w.1) :
    rawFail M y₀ p t v = rawFail M y₀ p t w := by
  classical
  let d : CubeVertex n := xorCube v.1 w.1
  have hd : IsEvenRole d := by simpa [d] using xorCube_even_of_even v.2 w.2
  have hD : sliceOf d = fun _ => false := by
    funext j
    have hj := congrFun hs j
    have hvw : v.1 j.1 = w.1 j.1 := by simpa [sliceOf] using hj
    change Bool.xor (v.1 j.1) (w.1 j.1) = false
    rw [← hvw]
    cases hv : v.1 j.1 <;> simp [Bool.xor, hv]
  have hmap : evenTranslate d hd v = w := by
    apply Subtype.ext
    funext j
    cases hv : v.1 j <;> cases hw : w.1 j <;> simp [evenTranslate, d, xorCube, hv, hw]
  calc
    rawFail M y₀ p t v = rawFail M y₀ p t (evenTranslate d hd v) :=
      (rawFail_evenTranslate M y₀ p t d hd hD v).symm
    _ = rawFail M y₀ p t w := by rw [hmap]

private theorem colDeg_nonneg {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (μ : Law N) (y : Fin N) : 0 ≤ colDeg E G μ y := by
  unfold colDeg
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg (μ.nonneg x)
  split_ifs <;> norm_num

private theorem lik_nonneg {N : ℕ} {I : Type} [Fintype I] {k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (μ : Law N)
    (ws : I → Fin k → Fin N) (y : Fin N) : 0 ≤ lik E G μ ws y := by
  unfold lik
  apply Finset.prod_nonneg
  intro a ha
  apply Finset.prod_nonneg
  intro j hj
  apply div_nonneg
  · unfold hit
    split_ifs <;> norm_num
  · exact colDeg_nonneg E G μ y

private theorem oddRowW_nonneg {N : ℕ} {I : Type} [Fintype I] {k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (g : ℝ) (μ ν : Law N)
    (ws : I → Fin k → Fin N) (y : Fin N) : 0 ≤ oddRowW E G g μ ν ws y := by
  unfold oddRowW
  split_ifs with hPass
  · exact div_nonneg (mul_nonneg (ν.nonneg y) (lik_nonneg E G μ ws y)) hPass.1.le
  · exact ν.nonneg y

private theorem oddRowW_sum_one {N : ℕ} {I : Type} [Fintype I] [DecidableEq I] {k : ℕ}
    (E : Fin N → Fin N → Prop) (G : Colour) (g : ℝ) (μ ν : Law N)
    (ws : I → Fin k → Fin N) : ∑ y, oddRowW E G g μ ν ws y = 1 := by
  classical
  unfold oddRowW
  split_ifs with hPass
  · calc
      (∑ y, ν.w y * lik E G μ ws y / normZ E G μ ν ws) =
          (∑ y, ν.w y * lik E G μ ws y) / normZ E G μ ν ws := by rw [Finset.sum_div]
      _ = normZ E G μ ν ws / normZ E G μ ν ws := rfl
      _ = 1 := div_self hPass.1.ne'
  · exact ν.sum_eq_one

private theorem oddRowF_sum_one {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (t : OuterWord n → M.ι)
    (W : EvenRole n → Fin (kTup n) → Fin N) (b : OddRole n) :
    ∑ y, oddRowF M t W b y = 1 := by
  unfold oddRowF
  exact oddRowW_sum_one E M.G (gS n) (M.μ (t (sliceOf b.1)))
    (M.ν (t (sliceOf b.1))) (starOf W b)

theorem rawFail_nonneg {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (v : EvenRole n) :
    0 ≤ rawFail M y₀ p t v := by
  unfold rawFail FinProb.expect massFailGiven oddProdW oddRowF
  apply Finset.sum_nonneg
  intro W hW
  apply mul_nonneg
  · exact (rawTuples M y₀ t).nonneg W
  · apply Finset.sum_nonneg
    intro f hf
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro b hb
      unfold oddRowW
      split_ifs with hPass
      · exact div_nonneg
          (mul_nonneg ((M.ν (t (sliceOf b.1))).nonneg (f b))
            (lik_nonneg E M.G (M.μ (t (sliceOf b.1))) (starOf W b) (f b))) hPass.1.le
      · exact (M.ν (t (sliceOf b.1))).nonneg (f b)
    · split_ifs <;> norm_num

private theorem outerHyp_of_sigma_mass {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ δ x₀ K : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (hF : Fixed11 δ x₀ K n N E X Y κ M y₀ p)
    (i : M.ι) (hi : p.w i ≠ 0) (z : InnerCoord n → Fin N)
    (hsigma : ∑ x, sigmaW E M.G (gS n) (M.μ i) z x = 1) :
    OuterHyp δ x₀ K n N E X Y M.G (piBar M y₀ p)
      (fun x => sigmaW E M.G (gS n) (M.μ i) z x)
      (Finset.univ.filter fun x => (M.μ i).w x ≠ 0) := by
  classical
  let C : Finset (Fin N) := commonSet E M.G (M.μ i) z
  let A : ℝ := (Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n)
  have hgate : (N : ℝ) * Real.exp (-A) ≤ (C.card : ℝ) := by
    by_contra hnot
    have hzero : ∑ x, sigmaW E M.G (gS n) (M.μ i) z x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hbad : ¬ (x ∈ C ∧ (N : ℝ) * Real.exp (-A) ≤ (C.card : ℝ)) := by
        intro h
        exact hnot h.2
      simp [sigmaW, C, A, hbad]
    rw [hsigma] at hzero
    norm_num at hzero
  have hNpos : 0 < (N : ℝ) := by
    have hN : 1 ≤ N := le_trans (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)) hF.host
    exact_mod_cast hN
  have hcardpos : 0 < (C.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hNpos (Real.exp_pos _)) hgate
  have hrowsum (y : Fin N) :
      piBar M y₀ p y = ∑ j, p.w j * piRow M y₀ j y := by
    rfl
  refine {
    host := hF.host
    disc := hF.disc
    pi_nonneg := ?_
    pi_sum := ?_
    pi_supp := ?_
    pi_cap := ?_
    S_sub := ?_
    degree := ?_
    noClique := ?_
    sigma_nonneg := ?_
    sigma_sum := hsigma
    sigma_supp := ?_
    sigma_cap := ?_ }
  · intro y
    rw [hrowsum y]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (p.nonneg j) ((hF.slice.rows j).pi_nonneg y)
  · unfold piBar mixW
    calc
      (∑ y, ∑ j, p.w j * piRow M y₀ j y) =
          ∑ j, ∑ y, p.w j * piRow M y₀ j y := by rw [Finset.sum_comm]
      _ = ∑ j, p.w j * ∑ y, piRow M y₀ j y := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.mul_sum]
      _ = ∑ j, p.w j * 1 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hr : ∑ y, piRow M y₀ j y = 1 := by
            simpa [piRow] using (hF.slice.rows j).pi_sum
          rw [hr]
      _ = 1 := by simp [p.sum_eq_one]
  · intro y hy
    have hex : ∃ j, p.w j ≠ 0 ∧ piRow M y₀ j y ≠ 0 := by
      by_contra hnex
      have hz : piBar M y₀ p y = 0 := by
        rw [hrowsum y]
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hp : p.w j = 0
        · simp [hp]
        · have hr : piRow M y₀ j y = 0 := by
            by_contra hne
            exact hnex ⟨j, hp, hne⟩
          simp [hr]
      exact hy hz
    obtain ⟨j, hjp, hjrow⟩ := hex
    have hν : (M.ν j).w y ≠ 0 := (hF.slice.rows j).pi_supp y hjrow
    by_contra hyY
    exact hν (M.ν_supp j y hyY)
  · intro y
    simpa [piBar] using hF.balanced.1 y
  · intro x hx
    have hμ : (M.μ i).w x ≠ 0 := by simpa [C] using (Finset.mem_filter.mp hx).2
    have hX : x ∈ X := by
      by_contra hxX
      exact hμ (M.μ_supp i x hxX)
    exact hX
  · intro x hx
    have hμ : (M.μ i).w x ≠ 0 := (Finset.mem_filter.mp hx).2
    simpa [piBar] using (hF.compat i hi).1 x hμ
  · simpa [piBar] using (hF.compat i hi).2.2
  · intro x
    unfold sigmaW
    split_ifs <;> positivity
  · intro x hx
    have hmem : x ∈ C := by
      by_contra hxC
      have hzero : sigmaW E M.G (gS n) (M.μ i) z x = 0 := by
        simp [sigmaW, C, A, hxC, hgate]
      exact hx hzero
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ x, (Finset.mem_filter.mp hmem).2.1⟩
  · intro x
    by_cases hx : x ∈ C
    · have hσ : sigmaW E M.G (gS n) (M.μ i) z x = (C.card : ℝ)⁻¹ := by
        simp [sigmaW, C, A, hx, hgate]
      rw [hσ]
      have hmul : (N : ℝ) ≤ (C.card : ℝ) * Real.exp A := by
        have hexp : Real.exp (-A) * Real.exp A = 1 := by
          rw [← Real.exp_add]
          simp
        calc
          (N : ℝ) = (N : ℝ) * (Real.exp (-A) * Real.exp A) := by rw [hexp]; ring
          _ = ((N : ℝ) * Real.exp (-A)) * Real.exp A := by ring
          _ ≤ (C.card : ℝ) * Real.exp A :=
            mul_le_mul_of_nonneg_right hgate (Real.exp_pos A).le
      have hmul' : (N : ℝ) ≤ Real.exp A * (C.card : ℝ) := by nlinarith [hmul]
      have hdiv : (N : ℝ) / (C.card : ℝ) ≤ Real.exp A :=
        (div_le_iff₀ hcardpos).2 hmul'
      calc
        (N : ℝ) * (C.card : ℝ)⁻¹ = (N : ℝ) / (C.card : ℝ) := by rw [div_eq_mul_inv]
        _ ≤ Real.exp A := hdiv
    · have hσ : sigmaW E M.G (gS n) (M.μ i) z x = 0 := by simp [sigmaW, C, hx]
      simpa [hσ] using (Real.exp_nonneg A)

theorem pr_pos_eq_zero_of_expect_nonpos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (hE : P.expect f ≤ 0) :
    P.pr (fun ω => 0 < f ω) = 0 := by
  classical
  have hnonneg : 0 ≤ P.expect f := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg (P.nonneg ω) (hf ω)
  have hzero : P.expect f = 0 := le_antisymm hE hnonneg
  have hweight (ω : Ω) (hω : 0 < f ω) : P.w ω = 0 := by
    have hterm : P.w ω * f ω ≤ P.expect f := by
      unfold FinProb.expect
      exact Finset.single_le_sum (s := Finset.univ) (f := fun z => P.w z * f z)
        (fun z hz => mul_nonneg (P.nonneg z) (hf z)) (Finset.mem_univ ω)
    have htermZero : P.w ω * f ω = 0 := by
      apply le_antisymm
      · simpa [hzero] using hterm
      · exact mul_nonneg (P.nonneg ω) (hf ω)
    exact (mul_eq_zero.mp htermZero).resolve_right (ne_of_gt hω)
  unfold FinProb.pr
  apply Finset.sum_eq_zero
  intro ω hω
  by_cases h : 0 < f ω
  · simp [h, hweight ω h]
  · simp [h]

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

private theorem wordDist_flipOuter {n : ℕ} (s : OuterWord n) (j : OuterCoord n) :
    wordDist s (flipOuter s j) = 1 := by
  have hset : (Finset.univ.filter fun k : OuterCoord n => s k ≠ flipOuter s j k) = {j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hkj : k = j
    · subst k
      cases h : s j <;> simp [flipOuter, h]
    · simp [flipOuter, hkj]
  unfold wordDist
  rw [hset]
  simp

/-- The second bad event at `s` reads only the radius-one outer-word ball. -/
theorem T2_dependsOn_wordBall {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (s : OuterWord n) :
    FinProb.DependsOn (fun t => T2 M y₀ t s) (wordBall s 1) := by
  intro t t' hagree
  have hs : s ∈ wordBall s 1 := by simp [wordBall, wordDist]
  have hcenter : t s = t' s := hagree s hs
  have hflip (j : OuterCoord n) : flipOuter s j ∈ wordBall s 1 := by
    simp [wordBall, wordDist_flipOuter]
  have hcount (x : Fin N) : highCount M y₀ t s x = highCount M y₀ t' s x := by
    unfold highCount
    have hset :
        (Finset.univ.filter fun j : OuterCoord n =>
          (4 / 5 : ℝ) < deg E M.G (piRow M y₀ (t (flipOuter s j))) x) =
        (Finset.univ.filter fun j : OuterCoord n =>
          (4 / 5 : ℝ) < deg E M.G (piRow M y₀ (t' (flipOuter s j))) x) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hagree (flipOuter s j) (hflip j)]
    rw [hset]
  apply propext
  unfold T2
  simp_rw [hcenter, hcount]

private theorem raw_compA_product_mean {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (z : Fin N) (m : ℕ) (s : Fin m → OuterWord n)
    (hsep : ∀ i j, i ≠ j → 3 ≤ wordDist (s i) (s j)) :
    (rawTags M p).expect (fun t => ∏ i, compA M y₀ t (s i) z) =
      ((N : ℝ) * piBar M y₀ p z) ^ m := by
  classical
  have hinj : Function.Injective s := by
    intro i j hij
    by_contra hne
    have hd := hsep i j hne
    simp [wordDist, hij] at hd
  have hmean : ∀ i : Fin m,
      p.expect (fun a => (N : ℝ) * piRow M y₀ a z) =
        (N : ℝ) * piBar M y₀ p z := by
    intro i
    unfold FinProb.expect piBar mixW
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  calc
    (rawTags M p).expect (fun t => ∏ i, compA M y₀ t (s i) z) =
        (FinProb.pi (fun _ : OuterWord n => p)).expect
          (fun t => ∏ i, (N : ℝ) * piRow M y₀ (t (s i)) z) := by
            simp [rawTags, compA]
    _ = ∏ i, p.expect (fun a => (N : ℝ) * piRow M y₀ a z) :=
      pi_expect_prod_on_injective_coords p s hinj Finset.univ
        (fun i a => (N : ℝ) * piRow M y₀ a z)
    _ = ∏ _i : Fin m, (N : ℝ) * piBar M y₀ p z := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hmean i
    _ = ((N : ℝ) * piBar M y₀ p z) ^ m := by simp

private def compBCoord {n : ℕ} (s : OuterWord n) : Option (OuterCoord n) → OuterWord n
  | none => s
  | some j => flipOuter s j

private theorem compBCoord_injective {n : ℕ} (s : OuterWord n) :
    Function.Injective (compBCoord s) := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j => exact False.elim ((flipOuter_ne_self s j) h.symm)
  | some i =>
      cases b with
      | none => exact False.elim ((flipOuter_ne_self s i) h)
      | some j => exact congrArg some (flipOuter_injective s h)

private theorem prod_option_factors {α β : Type} [Fintype α] [CommMonoid β]
    (f : Option α → β) :
    (∏ o : Option α, f o) = f none * ∏ a : α, f (some a) := by
  let e : Option α ≃ α ⊕ PUnit.{1} := Equiv.optionEquivSumPUnit.{0, 0} α
  calc
    (∏ o : Option α, f o) = ∏ u, f (e.symm u) :=
      Fintype.prod_equiv e _ _ (by intro o; simp [e])
    _ = (∏ a : α, f (some a)) * f none := by simp [e, Fintype.prod_sum_type]
    _ = f none * ∏ a : α, f (some a) := mul_comm _ _

private theorem raw_compB_mean_le {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (s : OuterWord n) (x : Fin N)
    (hα : 0 ≤ alphaBar M y₀ p x) (hπ : ∀ y, 0 ≤ piBar M y₀ p y) :
    (rawTags M p).expect (fun t => compB M y₀ p t s x) ≤
      (N : ℝ) * alphaBar M y₀ p x := by
  classical
  let D : ℝ := deg E M.G (piBar M y₀ p) x
  let F : Option (OuterCoord n) → M.ι → ℝ := fun o i =>
    match o with
    | none => (N : ℝ) * alphaRow M y₀ i x
    | some _ => deg E M.G (piRow M y₀ i) x / D
  have hprod (t : OuterWord n → M.ι) :
      (∏ o : Option (OuterCoord n), F o (t (compBCoord s o))) =
        compB M y₀ p t s x := by
    simp [F, compBCoord, compB, D]
  have hcenter :
      p.expect (fun i => (N : ℝ) * alphaRow M y₀ i x) =
        (N : ℝ) * alphaBar M y₀ p x := by
    unfold FinProb.expect alphaBar mixW
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdeg : p.expect (fun i => deg E M.G (piRow M y₀ i) x) = D := by
    unfold FinProb.expect D deg piBar mixW
    calc
      (∑ i, p.w i * ∑ y, piRow M y₀ i y * hit E M.G x y) =
          ∑ i, ∑ y, p.w i * piRow M y₀ i y * hit E M.G x y := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = ∑ y, ∑ i, p.w i * piRow M y₀ i y * hit E M.G x y := by rw [Finset.sum_comm]
      _ = ∑ y, (∑ i, p.w i * piRow M y₀ i y) * hit E M.G x y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.sum_mul]
  have hDnonneg : 0 ≤ D := by
    unfold D deg
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hπ y) (by unfold hit; split_ifs <;> norm_num)
  have hratio : ∀ j : OuterCoord n,
      p.expect (fun i => deg E M.G (piRow M y₀ i) x / D) = D / D := by
    intro j
    unfold FinProb.expect
    calc
      (∑ i, p.w i * (deg E M.G (piRow M y₀ i) x / D)) =
          (∑ i, p.w i * deg E M.G (piRow M y₀ i) x) / D := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = D / D := by
        change p.expect (fun i => deg E M.G (piRow M y₀ i) x) / D = D / D
        rw [hdeg]
  have hcoord (o : Option (OuterCoord n)) :
      p.expect (fun i => F o i) =
        (if o.isNone then (N : ℝ) * alphaBar M y₀ p x else D / D) := by
    cases o with
    | none => simpa [F] using hcenter
    | some j => simpa [F] using hratio j
  have hcoords (o : Option (OuterCoord n)) : 0 ≤ p.expect (fun i => F o i) := by
    cases o with
    | none => simpa [hcoord] using mul_nonneg (by positivity : 0 ≤ (N : ℝ)) hα
    | some j => simpa [hcoord] using div_nonneg hDnonneg hDnonneg
  have hprodMean :
      (rawTags M p).expect (fun t => ∏ o : Option (OuterCoord n), F o (t (compBCoord s o))) =
        ∏ o : Option (OuterCoord n), p.expect (fun i => F o i) := by
    unfold rawTags
    exact pi_expect_prod_on_injective_coords p (compBCoord s) (compBCoord_injective s)
      Finset.univ F
  have hcomp :
      (rawTags M p).expect (fun t => compB M y₀ p t s x) =
        ∏ o : Option (OuterCoord n), p.expect (fun i => F o i) := by
    calc
      (rawTags M p).expect (fun t => compB M y₀ p t s x) =
          (rawTags M p).expect
            (fun t => ∏ o : Option (OuterCoord n), F o (t (compBCoord s o))) := by
              have hfun : (fun t => compB M y₀ p t s x) =
                  (fun t => ∏ o : Option (OuterCoord n), F o (t (compBCoord s o))) := by
                funext t
                exact (hprod t).symm
              rw [hfun]
      _ = ∏ o : Option (OuterCoord n), p.expect (fun i => F o i) := hprodMean
  rw [hcomp]
  have hratio_le (j : OuterCoord n) :
      p.expect (fun i => deg E M.G (piRow M y₀ i) x / D) ≤ 1 := by
    rw [hratio j]
    by_cases hD : D = 0
    · simp [hD]
    · simp [hD]
  have hfactor :
      (∏ o : Option (OuterCoord n), p.expect (fun i => F o i)) =
        ((N : ℝ) * alphaBar M y₀ p x) *
          ∏ j : OuterCoord n,
            p.expect (fun i => deg E M.G (piRow M y₀ i) x / D) := by
    rw [prod_option_factors]
    simp [F, hcenter, hratio]
  rw [hfactor]
  have hprodle :
      (∏ j : OuterCoord n,
          p.expect (fun i => deg E M.G (piRow M y₀ i) x / D)) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun j hj => hcoords (some j)) (fun j hj => hratio_le j)
  have hC : 0 ≤ (N : ℝ) * alphaBar M y₀ p x := mul_nonneg (by positivity) hα
  calc
    ((N : ℝ) * alphaBar M y₀ p x) *
        ∏ j : OuterCoord n,
          p.expect (fun i => deg E M.G (piRow M y₀ i) x / D) ≤
      ((N : ℝ) * alphaBar M y₀ p x) * 1 := mul_le_mul_of_nonneg_left hprodle hC
    _ = (N : ℝ) * alphaBar M y₀ p x := by ring

private theorem wordDist_symm {n : ℕ} (s t : OuterWord n) : wordDist s t = wordDist t s := by
  unfold wordDist
  congr 1
  ext j
  simp [ne_comm]

private theorem wordDist_triangle {n : ℕ} (s t u : OuterWord n) :
    wordDist s u ≤ wordDist s t + wordDist t u := by
  let A := Finset.univ.filter fun j : OuterCoord n => s j ≠ u j
  let B := Finset.univ.filter fun j : OuterCoord n => s j ≠ t j
  let C := Finset.univ.filter fun j : OuterCoord n => t j ≠ u j
  have hsub : A ⊆ B ∪ C := by
    intro j hj
    have hsu : s j ≠ u j := (Finset.mem_filter.mp hj).2
    by_cases hst : s j ≠ t j
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hst⟩))
    · have htu : t j ≠ u j := by
        intro h
        have hstEq : s j = t j := by simpa using hst
        exact hsu (hstEq.trans h)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htu⟩))
  unfold wordDist
  change A.card ≤ B.card + C.card
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le B C)

private noncomputable def wordDiffSet {n : ℕ} (s t : OuterWord n) : Finset (OuterCoord n) :=
  Finset.univ.filter fun j => s j ≠ t j

private noncomputable def wordFromDiff {n : ℕ} (s : OuterWord n) (A : Finset (OuterCoord n)) : OuterWord n :=
  fun j => if j ∈ A then !s j else s j

private noncomputable def wordDiffEquiv {n : ℕ} (s : OuterWord n) : OuterWord n ≃ Finset (OuterCoord n) where
  toFun := wordDiffSet s
  invFun := wordFromDiff s
  left_inv := by
    intro t
    funext j
    by_cases hj : s j = t j
    · simp [wordFromDiff, wordDiffSet, hj]
    · have hmem : j ∈ wordDiffSet s t := by simp [wordDiffSet, hj]
      have hbool : t j = !s j := by
        cases hs : s j <;> cases ht : t j <;> simp_all
      simp [wordFromDiff, hmem, hbool]
  right_inv := by
    intro A
    ext j
    by_cases hj : j ∈ A <;> simp [wordDiffSet, wordFromDiff, hj]

private noncomputable def wordBallToSubsets {n r : ℕ} (s : OuterWord n) :
    {t : OuterWord n // wordDist s t ≤ r} ≃
      {A : Finset (OuterCoord n) // A.card ≤ r} where
  toFun t := ⟨wordDiffSet s t.1, by
    change (wordDiffSet s t.1).card ≤ r
    simpa [wordDiffSet, wordDist, ne_comm] using t.2⟩
  invFun A := ⟨wordFromDiff s A.1, by
    change (wordDiffSet s (wordFromDiff s A.1)).card ≤ r
    have hset : wordDiffSet s (wordFromDiff s A.1) = A.1 := by
      exact (wordDiffEquiv s).right_inv A.1
    rw [hset]
    exact A.2⟩
  left_inv := by
    intro t
    apply Subtype.ext
    exact (wordDiffEquiv s).left_inv t.1
  right_inv := by
    intro A
    apply Subtype.ext
    exact (wordDiffEquiv s).right_inv A.1

private def smallWordSubsetFiberEquiv {D : Type*} [Fintype D] [DecidableEq D] (r : ℕ)
    (i : Fin (r + 1)) :
    {A : {A : Finset D // A.card ≤ r} // (⟨A.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {A : Finset D // A.card = i.val} where
  toFun A := ⟨A.1.1, by
    have h := congrArg Fin.val A.2
    simpa using h⟩
  invFun A := ⟨⟨A.1, by rw [A.2]; omega⟩, by
    apply Fin.ext
    exact A.2⟩
  left_inv := by intro A; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro A; apply Subtype.ext; rfl

private def smallWordSubsetsEquiv {D : Type*} [Fintype D] [DecidableEq D] (r : ℕ) :
    {A : Finset D // A.card ≤ r} ≃
      Σ i : Fin (r + 1), {A : Finset D // A.card = i.val} := by
  let f : {A : Finset D // A.card ≤ r} → Fin (r + 1) :=
    fun A => ⟨A.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight (smallWordSubsetFiberEquiv r))

private theorem smallWordSubsets_card {D : Type*} [Fintype D] [DecidableEq D] (r : ℕ) :
    Fintype.card {A : Finset D // A.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose (Fintype.card D) i := by
  classical
  rw [Fintype.card_congr (smallWordSubsetsEquiv r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {A : Finset D // A.card = i.val} = Nat.choose (Fintype.card D) i.val := by
    let S : Finset (Finset D) := Finset.univ.powersetCard i.val
    let e : {A : Finset D // A.card = i.val} ≃ S :=
      { toFun := fun A => ⟨A.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, A.2⟩⟩
        invFun := fun A => ⟨A.1, (Finset.mem_powersetCard.mp A.2).2⟩
        left_inv := by intro A; apply Subtype.ext; rfl
        right_inv := by intro A; apply Subtype.ext; rfl }
    calc
      Fintype.card {A : Finset D // A.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose (Fintype.card D) i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem wordBall_card_formula {n r : ℕ} (s : OuterWord n) :
    (wordBall s r).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose (Fintype.card (OuterCoord n)) i := by
  classical
  have hcard : Fintype.card {t : OuterWord n // wordDist s t ≤ r} = (wordBall s r).card := by
    simpa [wordBall] using (Fintype.card_subtype (fun t : OuterWord n => wordDist s t ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (wordBallToSubsets s)).trans (smallWordSubsets_card r))

private theorem wordBall_card_two_le {n : ℕ} (s : OuterWord n) :
    ((wordBall s 2).card : ℝ) ≤ (Fintype.card (OuterCoord n) + 1 : ℝ) ^ 2 := by
  have hformula := wordBall_card_formula (r := 2) s
  rw [hformula]
  have hsum :
      (∑ i ∈ Finset.range (2 + 1), Nat.choose (Fintype.card (OuterCoord n)) i) =
        1 + Fintype.card (OuterCoord n) + Nat.choose (Fintype.card (OuterCoord n)) 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum]
  have hchoose := Nat.choose_le_pow (Fintype.card (OuterCoord n)) 2
  have hchooseR : (Nat.choose (Fintype.card (OuterCoord n)) 2 : ℝ) ≤
      (Fintype.card (OuterCoord n) : ℝ) ^ 2 := by exact_mod_cast hchoose
  push_cast
  nlinarith

private theorem wordDist_compBCoord_le_one {n : ℕ} (s : OuterWord n) (o : Option (OuterCoord n)) :
    wordDist s (compBCoord s o) ≤ 1 := by
  cases o with
  | none => simp [compBCoord, wordDist]
  | some j => rw [compBCoord, wordDist_flipOuter]

private theorem compBCoord_injective_separated {n m : ℕ} (s : Fin m → OuterWord n)
    (hsep : ∀ i j, i ≠ j → 3 ≤ wordDist (s i) (s j)) :
    Function.Injective (fun q : Fin m × Option (OuterCoord n) => compBCoord (s q.1) q.2) := by
  intro q r hqr
  by_contra hne
  by_cases hij : q.1 = r.1
  · apply hne
    apply Prod.ext hij
    exact compBCoord_injective (s q.1) (by simpa [hij] using hqr)
  · have hdist := hsep q.1 r.1 hij
    have hleft := wordDist_compBCoord_le_one (s q.1) q.2
    have hright := wordDist_compBCoord_le_one (s r.1) r.2
    have hright' : wordDist (compBCoord (s r.1) r.2) (s r.1) ≤ 1 := by
      rw [wordDist_symm]
      exact hright
    change compBCoord (s q.1) q.2 = compBCoord (s r.1) r.2 at hqr
    rw [← hqr] at hright'
    have htri := wordDist_triangle (s q.1) (compBCoord (s q.1) q.2) (s r.1)
    omega

private theorem raw_compB_product_mean_le {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ)
    (y₀ : M.ι → Fin N) (p : FinProb M.ι) (x : Fin N) (m : ℕ) (s : Fin m → OuterWord n)
    (hsep : ∀ i j, i ≠ j → 3 ≤ wordDist (s i) (s j))
    (hαrow : ∀ i, 0 ≤ alphaRow M y₀ i x)
    (hπrow : ∀ i y, 0 ≤ piRow M y₀ i y)
    (hαbar : 0 ≤ alphaBar M y₀ p x) (hπbar : ∀ y, 0 ≤ piBar M y₀ p y) :
    (rawTags M p).expect (fun t => ∏ i, compB M y₀ p t (s i) x) ≤
      ((N : ℝ) * alphaBar M y₀ p x) ^ m := by
  classical
  let D : ℝ := deg E M.G (piBar M y₀ p) x
  let F : Option (OuterCoord n) → M.ι → ℝ := fun o i =>
    match o with
    | none => (N : ℝ) * alphaRow M y₀ i x
    | some _ => deg E M.G (piRow M y₀ i) x / D
  have hprod (t : OuterWord n → M.ι) (i : Fin m) :
      (∏ o : Option (OuterCoord n), F o (t (compBCoord (s i) o))) =
        compB M y₀ p t (s i) x := by
    simp [F, compBCoord, compB, D]
  have hsite (i : Fin m) :
      (rawTags M p).expect (fun t => compB M y₀ p t (s i) x) =
        ∏ o : Option (OuterCoord n), p.expect (fun a => F o a) := by
    calc
      _ = (rawTags M p).expect
          (fun t => ∏ o : Option (OuterCoord n), F o (t (compBCoord (s i) o))) := by
            unfold FinProb.expect
            apply Finset.sum_congr rfl
            intro t ht
            change (rawTags M p).w t * compB M y₀ p t (s i) x =
              (rawTags M p).w t *
                (∏ o : Option (OuterCoord n), F o (t (compBCoord (s i) o)))
            rw [(hprod t i).symm]
      _ = ∏ o : Option (OuterCoord n), p.expect (fun a => F o a) := by
            unfold rawTags
            exact pi_expect_prod_on_injective_coords p (compBCoord (s i))
              (compBCoord_injective (s i)) Finset.univ F
  have hinj := compBCoord_injective_separated s hsep
  have hfactor :
      (rawTags M p).expect (fun t => ∏ i, compB M y₀ p t (s i) x) = ∏ i,
        (rawTags M p).expect (fun t => compB M y₀ p t (s i) x) := by
    calc
      _ = (rawTags M p).expect
          (fun t => ∏ q : Fin m × Option (OuterCoord n),
            F q.2 (t (compBCoord (s q.1) q.2))) := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro t ht
              change (rawTags M p).w t * (∏ i, compB M y₀ p t (s i) x) =
                (rawTags M p).w t *
                  (∏ q : Fin m × Option (OuterCoord n),
                    F q.2 (t (compBCoord (s q.1) q.2)))
              rw [show (∏ i : Fin m, compB M y₀ p t (s i) x) =
                  ∏ i : Fin m, ∏ o : Option (OuterCoord n),
                    F o (t (compBCoord (s i) o)) by
                    apply Finset.prod_congr rfl
                    intro i hi
                    exact (hprod t i).symm]
              rw [show (∏ i : Fin m, ∏ o : Option (OuterCoord n),
                    F o (t (compBCoord (s i) o))) =
                  ∏ q : Fin m × Option (OuterCoord n),
                    F q.2 (t (compBCoord (s q.1) q.2)) by
                    exact (Fintype.prod_prod_type'
                      (fun i o => F o (t (compBCoord (s i) o)))).symm]
      _ = ∏ q : Fin m × Option (OuterCoord n), p.expect (fun a => F q.2 a) := by
            unfold rawTags
            exact pi_expect_prod_on_injective_coords p
              (fun q : Fin m × Option (OuterCoord n) => compBCoord (s q.1) q.2)
              hinj Finset.univ (fun q a => F q.2 a)
      _ = ∏ i, (∏ o : Option (OuterCoord n), p.expect (fun a => F o a)) := by
            exact Fintype.prod_prod_type' (fun i o => p.expect (fun a => F o a))
      _ = ∏ i, (rawTags M p).expect (fun t => compB M y₀ p t (s i) x) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact (hsite i).symm
  have hDnonneg : 0 ≤ D := by
    unfold D deg
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hπbar y) (by unfold hit; split_ifs <;> norm_num)
  have hcomp_nonneg (t : OuterWord n → M.ι) (i : Fin m) :
      0 ≤ compB M y₀ p t (s i) x := by
    unfold compB
    apply mul_nonneg (mul_nonneg (by positivity) (hαrow (t (s i))))
    apply Finset.prod_nonneg
    intro j hj
    exact div_nonneg
      (show 0 ≤ deg E M.G (piRow M y₀ (t (flipOuter (s i) j))) x from by
        unfold deg
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg (hπrow _ y) (by unfold hit; split_ifs <;> norm_num)) hDnonneg
  have hsite0 (i : Fin m) :
      0 ≤ (rawTags M p).expect (fun t => compB M y₀ p t (s i) x) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg ((rawTags M p).nonneg t) (hcomp_nonneg t i)
  have hsitele (i : Fin m) :
      (rawTags M p).expect (fun t => compB M y₀ p t (s i) x) ≤
        (N : ℝ) * alphaBar M y₀ p x :=
    raw_compB_mean_le M y₀ p (s i) x hαbar hπbar
  rw [hfactor]
  calc
    (∏ i, (rawTags M p).expect (fun t => compB M y₀ p t (s i) x)) ≤
        ∏ _i : Fin m, ((N : ℝ) * alphaBar M y₀ p x) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hsite0 i
      · intro i hi
        exact hsitele i
    _ = ((N : ℝ) * alphaBar M y₀ p x) ^ m := by simp

private theorem MassFail_dependsOn_oddNbrs {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ : ℝ} (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N)
    (p : FinProb M.ι) (t : OuterWord n → M.ι) (v : EvenRole n) :
    FinProb.DependsOn (fun f => MassFail M y₀ p t f v)
      (Finset.univ.image (oddNbr v)) := by
  intro f f' hagree
  apply propext
  have hinner : innerOut f v = innerOut f' v := by
    funext a
    exact hagree (oddNbr v a.1) (Finset.mem_image.mpr ⟨a.1, Finset.mem_univ _, rfl⟩)
  have houter (j : OuterCoord n) : f (oddNbr v j.1) = f' (oddNbr v j.1) :=
    hagree (oddNbr v j.1) (Finset.mem_image.mpr ⟨j.1, Finset.mem_univ _, rfl⟩)
  have hrow (x : Fin N) : evenRowF M y₀ p t f v x = evenRowF M y₀ p t f' v x := by
    unfold evenRowF
    rw [hinner]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [houter j]
  unfold MassFail
  have hsum : (∑ x, evenRowF M y₀ p t f v x) =
      ∑ x, evenRowF M y₀ p t f' v x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hrow x
  exact Iff.of_eq (congrArg (fun q : ℝ => q < 1 / 2) hsum)

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
