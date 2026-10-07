import HypercubeRamsey.PartC.Core
import HypercubeRamsey.S03.Height.Device
import HypercubeRamsey.S03.Height.Scale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Lane-local finite probability and Hamming-ball facts for the concrete S14
primitive record law.
-/

namespace HypercubeRamsey.Lane_q_s14_hist

open Classical
open Filter
open OAI.HypercubeRamsey
open scoped BigOperators

private def diffSet {d : ℕ} (v u : CubeVertex d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def vertexOfDiff {d : ℕ} (v : CubeVertex d) (s : Finset (Fin d)) : CubeVertex d :=
  fun i => if i ∈ s then !(v i) else v i

private def diffEquiv {d : ℕ} (v : CubeVertex d) : CubeVertex d ≃ Finset (Fin d) where
  toFun := diffSet v
  invFun := vertexOfDiff v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [vertexOfDiff, diffSet, hi]
    · have hmem : i ∈ diffSet v u := by simp [diffSet, hi]
      have hbool : v i = !(u i) := by
        cases hu : u i <;> cases hv : v i <;> simp_all
      simp [vertexOfDiff, hmem, hbool]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s
    · simp [diffSet, vertexOfDiff, hi]
    · simp [diffSet, vertexOfDiff, hi]

private theorem diffSet_card {d : ℕ} (v u : CubeVertex d) :
    (diffSet v u).card = hammingDist u v := by
  simp [diffSet, hammingDist, ne_comm]

private def ballToSubsets {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨diffSet v u.1, by rw [diffSet_card]; exact u.2⟩
  invFun s := ⟨vertexOfDiff v s.1, by
    rw [← diffSet_card]
    simp [diffSet, vertexOfDiff]
    exact s.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    exact (diffEquiv v).left_inv u.1
  right_inv := by
    intro s
    apply Subtype.ext
    exact (diffEquiv v).right_inv s.1

private def smallSubsetFiberEquiv (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by
    have h := congrArg Fin.val s.2
    simpa using h⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by
    apply Fin.ext
    exact s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl

private def subsetsSmallEquiv (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) :=
    fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (smallSubsetFiberEquiv d r))

private theorem card_small_subsets (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (subsetsSmallEquiv d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S :=
        Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

theorem hammingBall_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans
    (card_small_subsets d r))

private def levelBallEquiv (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
    {u : CubeVertex d // hammingDist u v ≤ r} ≃
      {ℓ : CubeVertex d × Fin (H + 1) // ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r} where
  toFun u := ⟨(u.1, j), by simp [u.2]⟩
  invFun ℓ := ⟨ℓ.1.1, ℓ.2.2⟩
  left_inv := by intro u; apply Subtype.ext; rfl
  right_inv := by
    intro ℓ
    rcases ℓ with ⟨⟨u, k⟩, ⟨hk, hdist⟩⟩
    apply Subtype.ext
    exact Prod.ext rfl hk.symm

theorem levelBall_card (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
    (Finset.univ.filter (fun ℓ : CubeVertex d × Fin (H + 1) =>
      ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  calc
    (Finset.univ.filter (fun ℓ : CubeVertex d × Fin (H + 1) =>
      ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r)).card =
        Fintype.card {ℓ : CubeVertex d × Fin (H + 1) // ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r} := by
          symm
          exact Fintype.card_subtype _
    _ = Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} :=
          Fintype.card_congr (levelBallEquiv d H r j v).symm
    _ = (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card :=
          Fintype.card_subtype _
    _ = _ := hammingBall_card d r v

theorem pi_expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (FinLaw.pi P).E (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).E (f i) := by
  classical
  unfold FinLaw.E FinLaw.pi
  calc
    _ = ∑ ω : (∀ i, Ω i), ∏ i, (P i).w (ω i) * f i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      simpa using (Finset.prod_mul_distrib
        (s := (Finset.univ : Finset ι))
        (f := fun i => (P i).w (ω i)) (g := fun i => f i (ω i))).symm
    _ = ∏ i, ∑ x : Ω i, (P i).w x * f i x := by rw [Fintype.prod_sum]
    _ = _ := rfl

theorem bind_E_snd {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (f : β → ℝ) :
    (FinLaw.bind P K).E (fun z => f z.2) = ∑ a, P.w a * (K a).E f := by
  classical
  simp only [FinLaw.E, FinLaw.bind, Prod.fst, Prod.snd]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem bind_E_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (f : α → ℝ) :
    (FinLaw.bind P K).E (fun z => f z.1) = ∑ a, P.w a * f a := by
  classical
  simp only [FinLaw.E, FinLaw.bind, Prod.fst, Prod.snd]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, P.w a * (K a).w b * f a) =
        ∑ b, (P.w a * f a) * (K a).w b := by
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = (P.w a * f a) * ∑ b, (K a).w b := by rw [Finset.mul_sum]
    _ = P.w a * f a := by rw [(K a).sum_one]; ring

theorem E_const {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (c : ℝ) :
    P.E (fun _ => c) = c := by
  classical
  unfold FinLaw.E
  rw [← Finset.sum_mul, P.sum_one, one_mul]

theorem pr_exp_markov {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (X : Ω → ℝ) (s t : ℝ) (hs : 0 ≤ s) :
    P.pr (fun ω => t ≤ X ω) ≤
      Real.exp (-s * t) * P.E (fun ω => Real.exp (s * X ω)) := by
  classical
  unfold FinLaw.pr FinLaw.E
  calc
    (∑ ω, if t ≤ X ω then P.w ω else 0) ≤
        ∑ ω, P.w ω * Real.exp (s * (X ω - t)) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : t ≤ X ω
      · have he : 1 ≤ Real.exp (s * (X ω - t)) := by
          apply Real.one_le_exp_iff.mpr
          exact mul_nonneg hs (sub_nonneg.mpr h)
        simp only [if_pos h]
        simpa using (mul_le_mul_of_nonneg_left he (P.nonneg ω))
      · simp only [if_neg h]
        exact mul_nonneg (P.nonneg ω) (Real.exp_nonneg _)
    _ = Real.exp (-s * t) * ∑ ω, P.w ω * Real.exp (s * X ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [show s * (X ω - t) = -s * t + s * X ω by ring, Real.exp_add]
      ring

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg]

theorem pr_or_le {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A B : Ω → Prop) : P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB, P.nonneg]

theorem pr_exists_le_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : FinLaw Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  unfold FinLaw.pr
  calc
    _ ≤ ∑ ω, ∑ i, if A i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i, A i ω
      · obtain ⟨i, hi⟩ := hex
        have hsingle :
            (if A i ω then P.w ω else 0) ≤ ∑ k : ι, if A k ω then P.w ω else 0 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun k : ι => if A k ω then P.w ω else 0)
            (fun k hk => by
              by_cases hkA : A k ω
              · simp [hkA, P.nonneg]
              · simp [hkA]) (Finset.mem_univ i)
        have hbound : P.w ω ≤ ∑ k : ι, if A k ω then P.w ω else 0 := by
          calc
            P.w ω = (if A i ω then P.w ω else 0) := by simp [hi]
            _ ≤ ∑ k : ι, if A k ω then P.w ω else 0 := hsingle
        have hEx : ∃ k, A k ω := ⟨i, hi⟩
        simpa only [if_pos hEx] using hbound
      · have hfalse : ∀ i, ¬ A i ω := by
          intro i hAi
          exact hex ⟨i, hAi⟩
        have hsum : (∑ i : ι, if A i ω then P.w ω else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp [hfalse i]
        simp [hex, hsum]
    _ = ∑ i, ∑ ω, if A i ω then P.w ω else 0 := by rw [Finset.sum_comm]

theorem positive_pi_support_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) :
    (Finset.univ.filter fun ω : ∀ i, Ω i => 0 < ∏ i, (P i).w (ω i)).card ≤
      ∏ i, Fintype.card {x : Ω i // 0 < (P i).w x} := by
  classical
  let s : Finset (∀ i, Ω i) :=
    Finset.univ.filter fun ω => 0 < ∏ i, (P i).w (ω i)
  have hcoord (ω : ∀ i, Ω i) (hω : ω ∈ s) (i : ι) :
      0 < (P i).w (ω i) := by
    have hprod : 0 < ∏ j, (P j).w (ω j) := by
      simpa [s] using hω
    have hne : (P i).w (ω i) ≠ 0 := by
      intro hz
      have hzprod : (∏ j, (P j).w (ω j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hz
      rw [hzprod] at hprod
      norm_num at hprod
    exact lt_of_le_of_ne ((P i).nonneg (ω i)) (Ne.symm hne)
  let e : {ω : ∀ i, Ω i // ω ∈ s} → ∀ i, {x : Ω i // 0 < (P i).w x} :=
    fun ω i => ⟨ω.1 i, hcoord ω.1 ω.2 i⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  calc
    s.card = Fintype.card {ω : ∀ i, Ω i // ω ∈ s} := by
      symm
      exact Fintype.card_coe s
    _ ≤ Fintype.card (∀ i, {x : Ω i // 0 < (P i).w x}) :=
      Fintype.card_le_of_injective e he
    _ = ∏ i, Fintype.card {x : Ω i // 0 < (P i).w x} := by
      simp [Fintype.card_pi]

theorem small_finset_type_card_le_pow {α : Type*} [Fintype α] [DecidableEq α]
    (t : ℕ) (hα : 0 < Fintype.card α) :
    Fintype.card {s : Finset α // s.Nonempty ∧ s.card ≤ t} ≤
      (Fintype.card α + 1) ^ (2 * t) := by
  classical
  let d := Fintype.card α
  let e := Fintype.equivFin α
  let fe := Equiv.finsetCongr e
  have hcard_fe (s : Finset α) : (fe s).card = s.card := by
    simp [fe, Equiv.finsetCongr]
  have hcard_fe_symm (s : Finset (Fin d)) : (fe.symm s).card = s.card := by
    simp [fe, Equiv.finsetCongr]
  let finsetEquiv : {s : Finset α // s.card ≤ t} ≃
      {s : Finset (Fin d) // s.card ≤ t} := {
    toFun := fun s => ⟨fe s.1, by rw [hcard_fe]; exact s.2⟩
    invFun := fun s => ⟨fe.symm s.1, by rw [hcard_fe_symm]; exact s.2⟩
    left_inv := by intro s; apply Subtype.ext; exact fe.left_inv s.1
    right_inv := by intro s; apply Subtype.ext; exact fe.right_inv s.1
  }
  have hsmall : Fintype.card {s : Finset α // s.Nonempty ∧ s.card ≤ t} ≤
      Fintype.card {s : Finset α // s.card ≤ t} := by
    apply Fintype.card_le_of_injective (fun s => (⟨s.1, s.2.2⟩ : {s : Finset α // s.card ≤ t}))
    intro s s' h
    apply Subtype.ext
    exact congrArg (fun z : {s : Finset α // s.card ≤ t} => z.1) h
  have hsum : Fintype.card {s : Finset α // s.card ≤ t} =
      ∑ i ∈ Finset.range (t + 1), Nat.choose d i := by
    calc
      _ = Fintype.card {s : Finset (Fin d) // s.card ≤ t} := Fintype.card_congr finsetEquiv
      _ = _ := card_small_subsets d t
  have htwo : ∀ q : ℕ, q + 1 ≤ 2 ^ q := by
    intro q
    induction q with
    | zero => norm_num
    | succ t ih =>
        calc
          t + 1 + 1 ≤ 2 * (t + 1) := by omega
          _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (t + 1) := by rw [pow_succ]; ring
  have hbase : 2 ≤ d + 1 := by
    dsimp [d]
    omega
  calc
    Fintype.card {s : Finset α // s.Nonempty ∧ s.card ≤ t} ≤
        Fintype.card {s : Finset α // s.card ≤ t} := hsmall
    _ = ∑ i ∈ Finset.range (t + 1), Nat.choose d i := hsum
    _ ≤
        ∑ i ∈ Finset.range (t + 1), (d + 1) ^ t := by
          apply Finset.sum_le_sum
          intro i hi
          have hit : i ≤ t := by
            have := Finset.mem_range.mp hi
            omega
          calc
            Nat.choose d i ≤ d ^ i := Nat.choose_le_pow d i
            _ ≤ (d + 1) ^ t := by gcongr <;> omega
    _ = (t + 1) * (d + 1) ^ t := by simp
    _ ≤ 2 ^ t * (d + 1) ^ t := Nat.mul_le_mul_right _ (htwo t)
    _ ≤ (d + 1) ^ t * (d + 1) ^ t :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase t)
    _ = (d + 1) ^ (2 * t) := by rw [← pow_add]; congr 1 <;> omega

theorem topScale_le_nat_bound (n : ℕ) (σ ζ : ℝ)
    (hσ : 0 < σ) (hσζ : σ < ζ) (hζ : ζ < 1) :
    topScale n σ ζ ≤ (n + 2) ^ (n + 1) * (n ^ 2 + 1) := by
  classical
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hR : 1 ≤ R₀ := by simp [R₀]
  have hM : 2 ≤ M := by simp [M]
  have hexp_pos : 0 < 1 - ζ := by linarith
  have htarget_real : (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn, Real.zero_rpow hexp_pos.ne']
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      calc
        (n : ℝ) ^ (1 - ζ) ≤ (n : ℝ) ^ 1 :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = n := by rw [Real.rpow_one]
  have htarget : target ≤ n + 1 := by
    dsimp [target]
    apply Nat.ceil_le.mpr
    have hnReal : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    exact htarget_real.trans hnReal
  have hpow : target ≤ M ^ target * R₀ := by
    calc
      target ≤ 2 ^ target := (Nat.lt_pow_self (by norm_num : 1 < 2)).le
      _ ≤ M ^ target := Nat.pow_le_pow_left hM target
      _ ≤ M ^ target * R₀ := Nat.le_mul_of_pos_right _ (by omega)
  have hexists : ∃ j, target ≤ M ^ j * R₀ := ⟨target, hpow⟩
  have hfind : Nat.find hexists ≤ target := Nat.find_min' hexists hpow
  have hMle : M ≤ n + 2 := by
    dsimp [M]
    apply max_le
    · omega
    · rw [Nat.ceil_le]
      by_cases hn : n = 0
      · simp [hn, Real.zero_rpow hσ.ne']
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
        have hp : (n : ℝ) ^ σ ≤ (n : ℝ) := by
          calc
            (n : ℝ) ^ σ ≤ (n : ℝ) ^ 1 :=
              Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hσζ, hζ])
            _ = n := by rw [Real.rpow_one]
        have hnReal : (n : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast Nat.le_add_right n 2
        exact hp.trans hnReal
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    by_cases hn : n = 0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn))
  have hlog_le : Real.log (n : ℝ) ≤ n := by
    simpa [Real.rpow_one] using Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < 1)
  have hRle : R₀ ≤ n ^ 2 + 1 := by
    dsimp [R₀]
    apply max_le
    · omega
    · rw [Nat.ceil_le]
      have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
      exact_mod_cast hsq.trans (by norm_num : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 + 1)
  unfold topScale
  change M ^ Nat.find _ * R₀ ≤ _
  calc
    M ^ Nat.find _ * R₀ ≤ M ^ target * R₀ := by
      gcongr
    _ ≤ (n + 2) ^ (n + 1) * (n ^ 2 + 1) := by
      gcongr <;> omega

theorem eventually_const_mul_rpow_le_rpow {a b c : ℝ}
    (hab : a < b) (hc : 0 < c) :
    ∀ᶠ x in Filter.atTop, c * x ^ a ≤ x ^ b := by
  have hdec : Tendsto (fun x : ℝ => x ^ (a - b)) Filter.atTop (nhds 0) := by
    have hpos : 0 < b - a := sub_pos.mpr hab
    convert tendsto_rpow_neg_atTop hpos using 1 <;> congr 1 <;> ring
  have hratio : ∀ᶠ x : ℝ in Filter.atTop, x ^ (a - b) < c⁻¹ :=
    hdec.eventually (Iio_mem_nhds (inv_pos.mpr hc))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hratio] with x hx hxratio
  have hxpow : x ^ a = x ^ b * x ^ (a - b) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc
    c * x ^ a = (c * x ^ b) * x ^ (a - b) := by rw [hxpow]; ring
    _ ≤ (c * x ^ b) * c⁻¹ := by
      exact mul_le_mul_of_nonneg_left hxratio.le
        (mul_nonneg hc.le (Real.rpow_nonneg (le_of_lt hx) _))
    _ = x ^ b := by field_simp

end HypercubeRamsey.Lane_q_s14_hist
