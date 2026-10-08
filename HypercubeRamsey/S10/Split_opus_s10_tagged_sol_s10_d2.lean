import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

/-! Position concentration, fixed-list failures, masks and greedy marking for d2. -/

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
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
    (diffSet v u).card = _root_.hammingDist u v := by
  simp [diffSet, _root_.hammingDist, ne_comm]

private def ballToSubsets {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // _root_.hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
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
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem hammingBall_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // _root_.hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => _root_.hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans (card_small_subsets d r))

def positionCount (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : ℝ :=
  (((Finset.univ.filter (fun u : CubeVertex p.d =>
    P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)).card : ℕ) : ℝ)

def positionBad (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : Prop :=
  positionCount p P v j < (998 / 1000 : ℝ) * p.lam ∨ (1002 / 1000 : ℝ) * p.lam < positionCount p P v j

private def levelBallEquiv (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
    {u : CubeVertex d // _root_.hammingDist u v ≤ r} ≃
      {ℓ : CubeVertex d × Fin (H + 1) // ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ r} where
  toFun u := ⟨(u.1, j), by simp [u.2]⟩
  invFun ℓ := ⟨ℓ.1.1, ℓ.2.2⟩
  left_inv := by intro u; apply Subtype.ext; rfl
  right_inv := by
    intro ℓ
    rcases ℓ with ⟨⟨u, k⟩, ⟨hk, hdist⟩⟩
    apply Subtype.ext
    exact Prod.ext rfl hk.symm

private theorem levelBall_card (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
    (Finset.univ.filter (fun ℓ : CubeVertex d × Fin (H + 1) =>
      ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  calc
    (Finset.univ.filter (fun ℓ : CubeVertex d × Fin (H + 1) =>
      ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ r)).card =
        Fintype.card {ℓ : CubeVertex d × Fin (H + 1) // ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ r} := by
          symm
          exact Fintype.card_subtype _
    _ = Fintype.card {u : CubeVertex d // _root_.hammingDist u v ≤ r} :=
          Fintype.card_congr (levelBallEquiv d H r j v).symm
    _ = (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card :=
          Fintype.card_subtype _
    _ = _ := hammingBall_card d r v

private lemma finProb_pr_or_le {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (A B : Ω → Prop) :
    μ.pr (fun ω => A ω ∨ B ω) ≤ μ.pr A + μ.pr B := by
  classical
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω <;> by_cases hB : B ω <;>
    simp [hA, hB, μ.nonneg]

private lemma finProb_pr_mono {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : μ.pr A ≤ μ.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, μ.nonneg]

private lemma finProb_pr_exists_le_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (μ : FinProb Ω) (A : ι → Ω → Prop) :
    μ.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, μ.pr (A i) := by
  classical
  unfold FinProb.pr
  calc
    _ ≤ ∑ ω, ∑ i, if A i ω then μ.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i, A i ω
      · obtain ⟨i, hi⟩ := hex
        have hsingle :
            (if A i ω then μ.w ω else 0) ≤ ∑ k : ι, if A k ω then μ.w ω else 0 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun k : ι => if A k ω then μ.w ω else 0)
            (fun k hk => by
              by_cases hkA : A k ω
              · simp [hkA, μ.nonneg]
              · simp [hkA]) (Finset.mem_univ i)
        have hbound : μ.w ω ≤ ∑ k : ι, if A k ω then μ.w ω else 0 := by
          calc
            μ.w ω = (if A i ω then μ.w ω else 0) := by simp [hi]
            _ ≤ ∑ k : ι, if A k ω then μ.w ω else 0 := hsingle
        have hex' : ∃ k, A k ω := ⟨i, hi⟩
        simpa [hex'] using hbound
      · have hfalse : ∀ i, ¬ A i ω := by
          intro i hAi
          exact hex ⟨i, hAi⟩
        have hsum : (∑ i : ι, if A i ω then μ.w ω else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp [hfalse i]
        simp [hex, hsum]
    _ = ∑ i, ∑ ω, if A i ω then μ.w ω else 0 := by
      rw [Finset.sum_comm]

private theorem finProb_pi_expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  unfold FinProb.expect FinProb.pi
  calc
    _ = ∑ ω : (∀ i, Ω i), ∏ i, (P i).w (ω i) * f i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      simpa using (Finset.prod_mul_distrib
        (s := (Finset.univ : Finset ι))
        (f := fun i => (P i).w (ω i)) (g := fun i => f i (ω i))).symm
    _ = ∏ i, ∑ x : Ω i, (P i).w x * f i x := by
      rw [Fintype.prod_sum]
    _ = _ := rfl

private lemma finProb_pr_exp_markov {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (X : Ω → ℝ) (s t : ℝ) (hs : 0 ≤ s) :
    μ.pr (fun ω => t ≤ X ω) ≤
      Real.exp (-s * t) * μ.expect (fun ω => Real.exp (s * X ω)) := by
  classical
  unfold FinProb.pr FinProb.expect
  calc
    (∑ ω, if t ≤ X ω then μ.w ω else 0) ≤
        ∑ ω, μ.w ω * Real.exp (s * (X ω - t)) := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases h : t ≤ X ω
      · have he : 1 ≤ Real.exp (s * (X ω - t)) := by
          apply Real.one_le_exp_iff.mpr
          exact mul_nonneg hs (sub_nonneg.mpr h)
        simp only [if_pos h]
        simpa using (mul_le_mul_of_nonneg_left he (μ.nonneg ω))
      · simp only [if_neg h]
        exact mul_nonneg (μ.nonneg ω) (Real.exp_nonneg _)
    _ = Real.exp (-s * t) * ∑ ω, μ.w ω * Real.exp (s * X ω) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [show s * (X ω - t) = -s * t + s * X ω by ring, Real.exp_add]
      ring

private theorem position_exp_mgf_le (p : HDParams) (hlam : 0 < p.lam)
    (hV : 0 < p.V) (hprob : p.lam / (p.V : ℝ) ≤ 1)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) (s : ℝ) :
    p.posLaw.expect (fun P => Real.exp (s * ∑ ℓ : p.Loc,
      if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then if P ℓ then 1 else 0 else 0)) ≤
        Real.exp (p.lam * (Real.exp s - 1)) := by
  classical
  let q : ℝ := p.lam / (p.V : ℝ)
  let X : p.Loc → Bool → ℝ := fun ℓ b =>
    if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then if b then 1 else 0 else 0
  have hq0 : 0 ≤ q := by dsimp [q]; exact div_nonneg hlam.le (Nat.cast_nonneg _)
  have hq1 : q ≤ 1 := by simpa [q] using hprob
  have hcoord (ℓ : p.Loc) :
      (FinProb.bernoulli q).expect (fun b => Real.exp (s * X ℓ b)) =
        if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
          1 + q * (Real.exp s - 1) else 1 := by
    by_cases h : ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r
    · simp [FinProb.expect, FinProb.bernoulli, X, h, hq0, hq1] <;> ring
    · simp [FinProb.expect, FinProb.bernoulli, X, h, hq0, hq1]
  have hprod :
      p.posLaw.expect (fun P => Real.exp (s * ∑ ℓ : p.Loc, X ℓ (P ℓ))) =
        ∏ ℓ : p.Loc, (FinProb.bernoulli q).expect (fun b => Real.exp (s * X ℓ b)) := by
    calc
      _ = p.posLaw.expect (fun P => ∏ ℓ : p.Loc, Real.exp (s * X ℓ (P ℓ))) := by
        congr 1
        funext P
        rw [Finset.mul_sum, Real.exp_sum]
      _ = _ := by
        simpa [HDParams.posLaw] using
          (finProb_pi_expect_prod (fun _ : p.Loc => FinProb.bernoulli q)
            (fun ℓ b => Real.exp (s * X ℓ b)))
  have hprodFactors :
      p.posLaw.expect (fun P => Real.exp (s * ∑ ℓ : p.Loc, X ℓ (P ℓ))) =
        ∏ ℓ : p.Loc, if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
          1 + q * (Real.exp s - 1) else 1 := by
    simpa only [hcoord] using hprod
  have hfactor (ℓ : p.Loc) :
      0 ≤ (if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
        1 + q * (Real.exp s - 1) else 1) := by
    by_cases h : ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r
    · rw [if_pos h]
      have heq : 1 + q * (Real.exp s - 1) = 1 - q + q * Real.exp s := by ring
      rw [heq]
      positivity
    · simp [h]
  have hprodLe :
      (∏ ℓ : p.Loc, if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
        1 + q * (Real.exp s - 1) else 1) ≤
        ∏ ℓ : p.Loc, Real.exp (if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
          q * (Real.exp s - 1) else 0) := by
    apply Finset.prod_le_prod₀
    · intro ℓ hℓ
      exact hfactor ℓ
    · intro ℓ hℓ
      by_cases h : ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r
      · simp only [if_pos h]
        have := Real.add_one_le_exp (q * (Real.exp s - 1))
        nlinarith
      · simp [h]
  have hcard :
      (Finset.univ.filter (fun ℓ : p.Loc =>
        ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r)).card = p.V := by
    simpa [HDParams.Loc, HDParams.V] using levelBall_card p.d p.H p.r j v
  have hindicator :
      (∑ ℓ : p.Loc,
        if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) = p.V := by
    have hcast :
        (∑ ℓ : p.Loc,
          if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) =
          ((Finset.univ.filter (fun ℓ : p.Loc =>
            ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r)).card : ℝ) := by
      simpa using (Finset.natCast_card_filter
        (fun ℓ : p.Loc => ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r)
        (Finset.univ : Finset p.Loc))
    rw [hcast]
    exact_mod_cast hcard
  have hsum :
      (∑ ℓ : p.Loc,
        if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
          q * (Real.exp s - 1) else 0) = p.lam * (Real.exp s - 1) := by
    calc
      _ = (∑ ℓ : p.Loc,
          if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) *
            (q * (Real.exp s - 1)) := by
          calc
            _ = ∑ ℓ : p.Loc,
                (if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) *
                  (q * (Real.exp s - 1)) := by
                    apply Finset.sum_congr rfl
                    intro ℓ hℓ
                    by_cases h : ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r <;> simp [h]
            _ = _ := by rw [Finset.sum_mul]
      _ = p.lam * (Real.exp s - 1) := by
          rw [hindicator]
          dsimp [q]
          have hVne : (p.V : ℝ) ≠ 0 := (Nat.cast_pos.mpr hV).ne'
          field_simp [hVne]
  calc
    p.posLaw.expect (fun P => Real.exp (s * ∑ ℓ : p.Loc, X ℓ (P ℓ))) ≤
        ∏ ℓ : p.Loc, if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then
          1 + q * (Real.exp s - 1) else 1 := le_of_eq hprodFactors
    _ ≤ ∏ ℓ : p.Loc, Real.exp
          (if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then q * (Real.exp s - 1) else 0) := hprodLe
    _ = Real.exp (∑ ℓ : p.Loc,
          if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then q * (Real.exp s - 1) else 0) := by
          symm
          rw [Real.exp_sum]
    _ = Real.exp (p.lam * (Real.exp s - 1)) := by rw [hsum]

/-- Relative `.002` position concentration at a fixed site and level. -/
theorem position_bad_tail (p : HDParams) (hlam : 0 < p.lam)
    (hV : 0 < p.V) (hprob : p.lam / (p.V : ℝ) ≤ 1)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    p.posLaw.pr (fun P => positionBad p P v j) ≤
      2 * Real.exp (-p.lam / 2000000) := by
  classical
  let X : p.Loc → Bool → ℝ := fun ℓ b =>
    if ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r then if b then 1 else 0 else 0
  have hcount (P : p.Loc → Bool) :
      positionCount p P v j = ∑ ℓ : p.Loc, X ℓ (P ℓ) := by
    have hnatNat :
        (Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)).card =
          ∑ u : CubeVertex p.d,
            if _root_.hammingDist u v ≤ p.r then if P (u, j) = true then 1 else 0 else 0 := by
      rw [Finset.card_eq_sum_ite
        (s := Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r))
        (t := Finset.univ) (Finset.subset_univ _)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine Finset.sum_congr rfl ?_
      intro u hu
      by_cases hd : _root_.hammingDist u v ≤ p.r <;> by_cases hp : P (u, j) = true <;>
        simp [hd, hp]
    have hnat :
        ((Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)).card : ℝ) =
          ∑ u : CubeVertex p.d,
            if _root_.hammingDist u v ≤ p.r then if P (u, j) = true then (1 : ℝ) else 0 else 0 := by
      exact_mod_cast hnatNat
    rw [positionCount, hnat, Fintype.sum_prod_type]
    simp only [X]
    refine Finset.sum_congr rfl ?_
    intro u hu
    rw [Finset.sum_eq_single j]
    · by_cases hd : _root_.hammingDist u v ≤ p.r <;> simp [hd]
    · intro k hk hkj
      simp [hkj]
    · simp
  have hExpPos : Real.exp (1 / 1000 : ℝ) ≤ 1000 / 999 := by
    have hlog := Real.log_le_sub_one_of_pos
      (x := ((1000 : ℝ) / 999)⁻¹) (inv_pos.mpr (by norm_num))
    rw [Real.log_inv] at hlog
    have hlog' : 1 / 1000 ≤ Real.log ((1000 : ℝ) / 999) := by
      norm_num at hlog ⊢
      linarith
    calc
      Real.exp (1 / 1000 : ℝ) ≤ Real.exp (Real.log ((1000 : ℝ) / 999)) :=
        Real.exp_le_exp.mpr hlog'
      _ = 1000 / 999 := Real.exp_log (by norm_num)
  have hExpNeg : Real.exp (-(1 / 1000 : ℝ)) ≤ 1000 / 1001 := by
    have h : (1001 : ℝ) / 1000 ≤ Real.exp (1 / 1000) := by
      have := Real.add_one_le_exp (1 / 1000 : ℝ)
      linarith
    calc
      Real.exp (-(1 / 1000 : ℝ)) = (Real.exp (1 / 1000))⁻¹ := by rw [Real.exp_neg]
      _ ≤ ((1001 : ℝ) / 1000)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h
      _ = 1000 / 1001 := by norm_num
  have hupper :
      p.posLaw.pr (fun P => (1002 / 1000 : ℝ) * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) ≤
        Real.exp (-p.lam / 2000000) := by
    have hmark := finProb_pr_exp_markov p.posLaw
      (fun P => ∑ ℓ : p.Loc, X ℓ (P ℓ)) (1 / 1000)
      ((1002 / 1000 : ℝ) * p.lam) (by norm_num)
    have hmgf := position_exp_mgf_le p hlam hV hprob v j (1 / 1000)
    have hcoef : -(1 / 1000 : ℝ) * (1002 / 1000) +
        (Real.exp (1 / 1000) - 1) ≤ -(1 / 2000000 : ℝ) := by
      linarith [hExpPos]
    calc
      p.posLaw.pr (fun P => (1002 / 1000 : ℝ) * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) ≤
          Real.exp (-(1 / 1000 : ℝ) * ((1002 / 1000 : ℝ) * p.lam)) *
            p.posLaw.expect (fun P => Real.exp ((1 / 1000 : ℝ) * ∑ ℓ : p.Loc, X ℓ (P ℓ))) := hmark
      _ ≤ Real.exp (-(1 / 1000 : ℝ) * ((1002 / 1000 : ℝ) * p.lam)) *
          Real.exp (p.lam * (Real.exp (1 / 1000) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ ≤ Real.exp (-p.lam / 2000000) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hterm := mul_le_mul_of_nonneg_left hcoef hlam.le
        nlinarith [hterm]
  have hlower :
      p.posLaw.pr (fun P => ∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ (998 / 1000 : ℝ) * p.lam) ≤
        Real.exp (-p.lam / 2000000) := by
    have hEvent :
        (fun P : p.Loc → Bool => ∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ (998 / 1000 : ℝ) * p.lam) =
          (fun P => -((998 / 1000 : ℝ) * p.lam) ≤ -(∑ ℓ : p.Loc, X ℓ (P ℓ))) := by
      funext P
      apply propext
      constructor <;> intro h <;> linarith
    rw [hEvent]
    have hmark := finProb_pr_exp_markov p.posLaw
      (fun P => -(∑ ℓ : p.Loc, X ℓ (P ℓ))) (1 / 1000)
      (-((998 / 1000 : ℝ) * p.lam)) (by norm_num)
    have hmgf := position_exp_mgf_le p hlam hV hprob v j (-(1 / 1000 : ℝ))
    have hmgf' : p.posLaw.expect
        (fun P => Real.exp ((1 / 1000 : ℝ) * (-(∑ ℓ : p.Loc, X ℓ (P ℓ))))) ≤
          Real.exp (p.lam * (Real.exp (-(1 / 1000 : ℝ)) - 1)) := by
      simpa [neg_mul] using hmgf
    have hcoef : (1 / 1000 : ℝ) * (998 / 1000) +
        (Real.exp (-(1 / 1000 : ℝ)) - 1) ≤ -(1 / 2000000 : ℝ) := by
      linarith [hExpNeg]
    calc
      p.posLaw.pr (fun P => -((998 / 1000 : ℝ) * p.lam) ≤ -(∑ ℓ : p.Loc, X ℓ (P ℓ))) ≤
          Real.exp (-(1 / 1000 : ℝ) * (-((998 / 1000 : ℝ) * p.lam))) *
            p.posLaw.expect (fun P => Real.exp ((1 / 1000 : ℝ) *
              (-(∑ ℓ : p.Loc, X ℓ (P ℓ))))) := hmark
      _ ≤ Real.exp (-(1 / 1000 : ℝ) * (-((998 / 1000 : ℝ) * p.lam))) *
          Real.exp (p.lam * (Real.exp (-(1 / 1000 : ℝ)) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf' (Real.exp_nonneg _)
      _ ≤ Real.exp (-p.lam / 2000000) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hterm := mul_le_mul_of_nonneg_left hcoef hlam.le
        nlinarith [hterm]
  have hsubset (P : p.Loc → Bool) : positionBad p P v j →
      (∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ (998 / 1000 : ℝ) * p.lam) ∨
        (1002 / 1000 : ℝ) * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ) := by
    intro h
    rcases h with h | h
    · left
      rw [← hcount P]
      exact le_of_lt h
    · right
      rw [← hcount P]
      exact le_of_lt h
  have hbad := finProb_pr_mono p.posLaw (fun P => positionBad p P v j)
    (fun P => (∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ (998 / 1000 : ℝ) * p.lam) ∨
      (1002 / 1000 : ℝ) * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) hsubset
  have hunion := finProb_pr_or_le p.posLaw
    (fun P => ∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ (998 / 1000 : ℝ) * p.lam)
    (fun P => (1002 / 1000 : ℝ) * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ))
  calc
    p.posLaw.pr (fun P => positionBad p P v j) ≤ _ := hbad.trans hunion
    _ ≤ Real.exp (-p.lam / 2000000) + Real.exp (-p.lam / 2000000) := add_le_add hlower hupper
    _ = 2 * Real.exp (-p.lam / 2000000) := by ring


set_option maxHeartbeats 1000000 in
/-- Simultaneous relative `.002` concentration over a finite set of sites. -/
theorem position_counts_union (p : HDParams) (Sites : p.Sites)
    (hlam : 0 < p.lam) (hV : 0 < p.V)
    (hprob : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.pr (fun P => ∃ v ∈ Sites, ∃ j : Fin (p.H + 1), positionBad p P v j) ≤
      2 * (Sites.card : ℝ) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 2000000) := by
  classical
  let ι := {v : CubeVertex p.d // v ∈ Sites} × Fin (p.H + 1)
  have hcard : Fintype.card ι = Sites.card * (p.H + 1) := by
    simp [ι, Fintype.card_coe]
  have hEq :
      (fun P : p.Loc → Bool => ∃ v ∈ Sites, ∃ j : Fin (p.H + 1), positionBad p P v j) =
        (fun P => ∃ x : ι, positionBad p P x.1.1 x.2) := by
    funext P
    apply propext
    constructor
    · rintro ⟨v, hv, j, hbad⟩
      exact ⟨⟨⟨v, hv⟩, j⟩, hbad⟩
    · rintro ⟨⟨⟨v, hv⟩, j⟩, hbad⟩
      exact ⟨v, hv, j, hbad⟩
  rw [hEq]
  calc
    p.posLaw.pr (fun P => ∃ x : ι, positionBad p P x.1.1 x.2) ≤
        ∑ x : ι, p.posLaw.pr (fun P => positionBad p P x.1.1 x.2) :=
      @finProb_pr_exists_le_sum (p.Loc → Bool) ι inferInstance inferInstance
        p.posLaw (fun x P => positionBad p P x.1.1 x.2)
    _ ≤ ∑ _x : ι, 2 * Real.exp (-p.lam / 2000000) := by
      apply Finset.sum_le_sum
      intro x hx
      exact position_bad_tail p hlam hV hprob x.1.1 x.2
    _ = 2 * (Sites.card : ℝ) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 2000000) := by
      simp [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      ring

private theorem fixed_list_premises_mono
    {k r s : ℕ} {wν w cap z bound : ℝ}
    (hs : s ≤ r)
    (hwidth : wν + Real.log 4 + 2 * (k : ℝ) * (r : ℝ) ≤ w)
    (hlog : Real.log ((r : ℝ) + 1) ≤ cap)
    (herror : ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) * Real.exp z ≤ bound) :
    wν + Real.log 4 + 2 * (k : ℝ) * (s : ℝ) ≤ w ∧
      Real.log ((s : ℝ) + 1) ≤ cap ∧
      ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) * Real.exp z ≤ bound := by
  have hsR : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
  have hsPlus : (s : ℝ) + 1 ≤ (r : ℝ) + 1 := by linarith
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hsNonneg : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hsize : 2 * (k : ℝ) * (s : ℝ) ≤ 2 * (k : ℝ) * (r : ℝ) :=
    mul_le_mul_of_nonneg_left hsR (by positivity)
  have hprod : ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) ≤
      ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) := by
    calc
      ((s : ℝ) + 1) * (k : ℝ) * (s : ℝ) ≤
          ((r : ℝ) + 1) * (k : ℝ) * (s : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsPlus hk) hsNonneg
      _ ≤ ((r : ℝ) + 1) * (k : ℝ) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hsR (by positivity)
  refine ⟨by linarith, (Real.log_le_log (by positivity) hsPlus).trans hlog, ?_⟩
  exact (mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg z)).trans herror

/-- A single constant controls every list of at most the Section 10 block count,
including masked mixtures whose aggregate is bounded by `4ν`. -/
theorem fixed_list_failures_eventually (η₀ ζ δ : ℝ)
    (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) :
    ∃ c₅ : ℝ, 0 < c₅ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (N q : ℕ) (I : Type*) [Fintype I] [DecidableEq I]
        (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
        (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N) (μ : I → Law N),
        (∀ i, (μ i).SupportedIn X ∧ (μ i).WidthLE ((n : ℝ) ^ δ)) →
        ν.WidthLE ((n : ℝ) ^ δ) → (∀ j, (D j).SupportedIn Y) →
        (∀ y, ∑ j, ρ.w j * (D j).w y ≤ 4 * ν.w y) →
        DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
        ∀ S : Finset I, S.card ≤ p10_1kFixedListBlockCount n δ →
        (Fin (p10_1kTupleListLength n δ) → Fin N) →
        (p10_1kIdTupleArrayLaw (k := p10_1kTupleListLength n δ) μ).pr (fun W =>
          fixedListFailure E G ρ D (fun b => μ (S.equivFin.symm b).1)
            ((n : ℝ) ^ (-δ)) (fun b => W (S.equivFin.symm b).1)) ≤
          Real.exp (-c₅ * ((n : ℝ) ^ (-δ)) ^ 2 * p10_1kTupleListLength n δ) := by
  obtain ⟨c₅, hc₅, htest⟩ := p10_1c_fixed_list_squared_mass_test
  refine ⟨c₅, hc₅, ?_⟩
  have hbasic := p10_1k_fixedList_basic_premises_eventually η₀ ζ δ hη₀ hζ hδ hδsmall
  have herror := p10_1k_fixedList_exceptional_premise_eventually η₀ ζ δ hη₀ hζ hδ hδsmall
  filter_upwards [hbasic, herror] with n hbasic herror
  intro N q I _ _ E X Y G ρ D ν μ hμ hν hD hagg hdisc S hS defaultTuple
  obtain ⟨hε, hεa, ha, hwidth, hlog⟩ := hbasic
  obtain ⟨hwidth', hlog', herror'⟩ := fixed_list_premises_mono hS hwidth hlog herror
  apply p10_1kIdTupleArrayLaw_fixedListFailure_bound μ S S.card S.equivFin.symm
    E G ρ D ((n : ℝ) ^ (-δ)) _ defaultTuple
  rw [← p10_1k_fixedListFailureWeight_eq_pr]
  exact htest N S.card (p10_1kTupleListLength n δ) q E X Y G ρ D ν
    (fun b => μ (S.equivFin.symm b).1) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀))
    ((n : ℝ) ^ (-δ)) ((n : ℝ) ^ δ) ((n : ℝ) ^ δ)
    (fun b => hμ _) hν hD hagg hdisc hε hεa ha hwidth' hlog' herror'

/-- Union over pairwise disjoint choices from an arbitrary menu; the menu itself
need not consist of pairwise disjoint lists. -/
theorem disjoint_failure_union_bound
    {N k : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (μ : I → Law N) (n L : ℕ) (S : Fin L → Finset I)
    (F : Fin L → (I → Fin k → Fin N) → Prop)
    (hdepends : ∀ ℓ W W', (∀ id ∈ S ℓ, W id = W' id) → (F ℓ W ↔ F ℓ W'))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hprob : ∀ ℓ, (p10_1kIdTupleArrayLaw μ).pr (F ℓ) ≤ ε) :
    (p10_1kIdTupleArrayLaw μ).pr (fun W => ∃ choose : Fin n → Fin L,
      (∀ i j, i ≠ j → Disjoint (S (choose i)) (S (choose j))) ∧
      ∀ i, F (choose i) W) ≤ (L : ℝ) ^ n * ε ^ n := by
  classical
  let P := p10_1kIdTupleArrayLaw (k := k) μ
  let A (choose : Fin n → Fin L) (W : I → Fin k → Fin N) : Prop :=
    (∀ i j, i ≠ j → Disjoint (S (choose i)) (S (choose j))) ∧ ∀ i, F (choose i) W
  have hchoice (choose : Fin n → Fin L) : P.pr (A choose) ≤ ε ^ n := by
    by_cases hd : ∀ i j, i ≠ j → Disjoint (S (choose i)) (S (choose j))
    · have hfactor := p10_1kIdTupleArrayLaw_disjoint_events μ n n
        (fun i => S (choose i)) (fun i => F (choose i))
        (fun i => hdepends (choose i)) hd id Function.injective_id
      have heq : P.pr (A choose) = ∏ i : Fin n, P.pr (F (choose i)) := by
        have hAeq : A choose = (fun W => ∀ i, F (choose i) W) := by
          funext W
          exact propext (and_iff_right hd)
        rw [hAeq]
        exact hfactor
      rw [heq]
      calc
        (∏ i : Fin n, P.pr (F (choose i))) ≤ ∏ _i : Fin n, ε := by
          apply Finset.prod_le_prod₀
          · intro i _
            unfold FinProb.pr
            exact Finset.sum_nonneg fun W _ => by
              split_ifs <;> simp [P.nonneg W]
          · intro i _
            exact hprob (choose i)
        _ = ε ^ n := by simp
    · have heq : P.pr (A choose) = 0 := by simp [A, hd, FinProb.pr]
      rw [heq]
      exact pow_nonneg hε _
  calc
    P.pr (fun W => ∃ choose, A choose W) ≤ ∑ choose, P.pr (A choose) :=
      finProb_pr_exists_le_sum P A
    _ ≤ ∑ _choose : Fin n → Fin L, ε ^ n :=
      Finset.sum_le_sum fun choose _ => hchoice choose
    _ = (L : ℝ) ^ n * ε ^ n := by simp

/-- Conditioning on clusters of prior mass at least one half and restricting
those clusters to a half-mass mask costs at most four in the mixture. -/
theorem half_mask_aggregate_le {N q : ℕ}
    (ρ : FinProb (Fin q)) (D : Fin q → Law N) (ν : Law N)
    (F : Finset (Fin N)) (R : Finset (Fin q))
    (hR : (1 / 2 : ℝ) ≤ ρ.pr (fun j => j ∈ R))
    (hmask : ∀ j ∈ R, (1 / 2 : ℝ) ≤ lawMassOn (D j) F)
    (hagg : ∀ y, ∑ j, ρ.w j * (D j).w y ≤ ν.w y) :
    ∀ y, ∑ j,
      (ρ.cond (fun j => j ∈ R) (lt_of_lt_of_le (by norm_num) hR)).w j *
        (if h : j ∈ R then Law.restrict (D j) F
          (lt_of_lt_of_le (by norm_num) (hmask j h)) else D j).w y ≤ 4 * ν.w y := by
  classical
  intro y
  let ρ' := ρ.cond (fun j => j ∈ R) (lt_of_lt_of_le (by norm_num) hR)
  have hterm (j : Fin q) :
      ρ'.w j *
        (if h : j ∈ R then Law.restrict (D j) F
          (lt_of_lt_of_le (by norm_num) (hmask j h)) else D j).w y ≤
        4 * (ρ.w j * (D j).w y) := by
    by_cases hj : j ∈ R
    · rw [dif_pos hj]
      have hprior : ρ'.w j = ρ.w j / ρ.pr (fun j => j ∈ R) := by
        simp [ρ', FinProb.cond, hj]
      have hpriorBound : ρ'.w j ≤ 2 * ρ.w j := by
        rw [hprior]
        apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hR)).2
        have hp : (1 : ℝ) ≤ 2 * ρ.pr (fun j => j ∈ R) := by linarith
        calc
          ρ.w j = 1 * ρ.w j := by ring
          _ ≤ (2 * ρ.pr (fun j => j ∈ R)) * ρ.w j :=
            mul_le_mul_of_nonneg_right hp (ρ.nonneg j)
          _ = 2 * ρ.w j * ρ.pr (fun j => j ∈ R) := by ring
      have hmaskAtom := p10_1k_restrict_atom_le_two (D j) F (hmask j hj) y
      calc
        ρ'.w j * (Law.restrict (D j) F _).w y ≤
            (2 * ρ.w j) * (Law.restrict (D j) F _).w y :=
          mul_le_mul_of_nonneg_right hpriorBound ((Law.restrict (D j) F _).nonneg y)
        _ ≤ (2 * ρ.w j) * (2 * (D j).w y) :=
          mul_le_mul_of_nonneg_left hmaskAtom
            (mul_nonneg (by norm_num) (ρ.nonneg j))
        _ = 4 * (ρ.w j * (D j).w y) := by ring
    · have hprior : ρ'.w j = 0 := by simp [ρ', FinProb.cond, hj]
      rw [hprior, zero_mul]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (ρ.nonneg j) ((D j).nonneg y))
  calc
    (∑ j, ρ'.w j *
        (if h : j ∈ R then Law.restrict (D j) F
          (lt_of_lt_of_le (by norm_num) (hmask j h)) else D j).w y) ≤
        ∑ j, 4 * (ρ.w j * (D j).w y) := Finset.sum_le_sum fun j _ => hterm j
    _ = 4 * ∑ j, ρ.w j * (D j).w y := by rw [Finset.mul_sum]
    _ ≤ 4 * ν.w y := mul_le_mul_of_nonneg_left (hagg y) (by norm_num)

/-- The greedy scan is the union of a pairwise disjoint subfamily of its input.
The scan function is supplied by its two defining equations. -/
theorem greedy_union_subfamily {α : Type*} [DecidableEq α]
    (scan : List (Finset α) → Finset α → Finset α)
    (hnil : ∀ used, scan [] used = used)
    (hcons : ∀ S rest used, scan (S :: rest) used =
      if Disjoint S used then scan rest (used ∪ S) else scan rest used)
    (L : List (Finset α)) (used : Finset α) :
    ∃ A : Finset (Finset α), (A : Set (Finset α)).Pairwise Disjoint ∧
      (∀ S ∈ A, S ∈ L ∧ Disjoint S used) ∧
      scan L used = used ∪ A.biUnion id := by
  classical
  induction L generalizing used with
  | nil => exact ⟨∅, by simp, by simp, by simp [hnil]⟩
  | cons S rest ih =>
    by_cases hd : Disjoint S used
    · obtain ⟨A, hA, hmem, heq⟩ := ih (used ∪ S)
      refine ⟨insert S A, ?_, ?_, ?_⟩
      · rw [Finset.coe_insert]
        refine (Set.pairwise_insert_of_symm (r := Disjoint)
          (a := S) (s := (A : Set (Finset α)))).2 ⟨hA, ?_⟩
        intro B hB hBS
        exact ((Finset.disjoint_union_right.mp (hmem B hB).2).2).symm
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact ⟨by simp, hd⟩
        · exact ⟨by simp [(hmem B hB).1],
            (Finset.disjoint_union_right.mp (hmem B hB).2).1⟩
      · rw [hcons, if_pos hd, heq]
        simp only [Finset.biUnion_insert, id_eq]
        exact Finset.union_assoc _ _ _
    · obtain ⟨A, hA, hmem, heq⟩ := ih used
      refine ⟨A, hA, ?_, ?_⟩
      · intro B hB
        exact ⟨by simp [(hmem B hB).1], (hmem B hB).2⟩
      · rw [hcons, if_neg hd, heq]

/-- Every nonempty input list meets the union marked by the maximal greedy scan. -/
theorem greedy_union_hits {α : Type*} [DecidableEq α]
    (scan : List (Finset α) → Finset α → Finset α)
    (hnil : ∀ used, scan [] used = used)
    (hcons : ∀ S rest used, scan (S :: rest) used =
      if Disjoint S used then scan rest (used ∪ S) else scan rest used)
    (L : List (Finset α)) (used : Finset α) (S : Finset α)
    (hS : S ∈ L) (hne : S.Nonempty) : ¬ Disjoint S (scan L used) := by
  classical
  have hsub (L : List (Finset α)) (used : Finset α) : used ⊆ scan L used := by
    obtain ⟨A, _, _, heq⟩ := greedy_union_subfamily scan hnil hcons L used
    rw [heq]
    exact Finset.subset_union_left
  induction L generalizing used with
  | nil => simp at hS
  | cons B rest ih =>
    rw [hcons]
    rcases List.mem_cons.mp hS with rfl | hS
    · split_ifs with hd
      · intro hout
        obtain ⟨a, ha⟩ := hne
        have hin : a ∈ scan rest (used ∪ S) :=
          hsub rest (used ∪ S) (Finset.mem_union_right used ha)
        exact Finset.disjoint_left.mp hout ha hin
      · intro hout
        exact hd (Finset.disjoint_of_subset_right (hsub rest used) hout)
    · split_ifs <;> exact ih _ hS

/-- A bound on the chosen subfamily's size controls the number of marked IDs. -/
theorem greedy_union_card_bound {α : Type*} [DecidableEq α]
    (scan : List (Finset α) → Finset α → Finset α)
    (hnil : ∀ used, scan [] used = used)
    (hcons : ∀ S rest used, scan (S :: rest) used =
      if Disjoint S used then scan rest (used ∪ S) else scan rest used)
    (L : List (Finset α)) (R B : ℕ)
    (hsize : ∀ S ∈ L, S.card ≤ R)
    (hfamily : ∀ A : Finset (Finset α), (A : Set (Finset α)).Pairwise Disjoint →
      (∀ S ∈ A, S ∈ L) → A.card ≤ B) :
    (scan L ∅).card ≤ B * R := by
  classical
  obtain ⟨A, hA, hmem, heq⟩ := greedy_union_subfamily scan hnil hcons L ∅
  have hcard := hfamily A hA (fun S hS => (hmem S hS).1)
  rw [heq, Finset.empty_union]
  calc
    (A.biUnion id).card ≤ ∑ S ∈ A, S.card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ A, R := Finset.sum_le_sum fun S hS => hsize S (hmem S hS).1
    _ = A.card * R := by simp
    _ ≤ B * R := Nat.mul_le_mul_right R hcard

/-- Absence of `n` pairwise disjoint input lists bounds every disjoint subfamily. -/
theorem disjoint_subfamily_card_lt {α : Type*} [DecidableEq α]
    (L : List (Finset α)) (n : ℕ)
    (hno : ¬ ∃ f : Fin n → Finset α,
      (∀ i, f i ∈ L) ∧ ∀ i j, i ≠ j → Disjoint (f i) (f j))
    (A : Finset (Finset α)) (hA : (A : Set (Finset α)).Pairwise Disjoint)
    (hmem : ∀ S ∈ A, S ∈ L) : A.card < n := by
  classical
  by_contra hn
  have hnA : n ≤ A.card := Nat.le_of_not_gt hn
  let e : Fin n ↪ {S // S ∈ A} := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa using hnA))
  apply hno
  refine ⟨fun i => (e i).1, fun i => hmem _ (e i).2, ?_⟩
  intro i j hij
  apply hA (e i).2 (e j).2
  intro heq
  exact hij (e.injective (Subtype.ext heq))

end HypercubeRamsey.Lane_sol_s10_d2
