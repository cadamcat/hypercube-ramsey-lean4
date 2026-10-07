import HypercubeRamsey.PartC.Core
import HypercubeRamsey.S03.Height.Device

/-!
Lane-local finite probability and Hamming-ball facts for the concrete S14
primitive record law.
-/

namespace HypercubeRamsey.Lane_q_s14_hist

open Classical
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

end HypercubeRamsey.Lane_q_s14_hist
