import HypercubeRamsey.S03.Height.Device

namespace HypercubeRamsey

open OAI.HypercubeRamsey

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
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem hammingBall_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans (card_small_subsets d r))

private def positionCount (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : ℝ :=
  (((Finset.univ.filter (fun u : CubeVertex p.d =>
    P (u, j) = true ∧ hammingDist u v ≤ p.r)).card : ℕ) : ℝ)

private def positionBad (p : HDParams) (P : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : Prop :=
  positionCount p P v j < p.lam / 2 ∨ 2 * p.lam < positionCount p P v j

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

private theorem levelBall_card (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
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
      if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then if P ℓ then 1 else 0 else 0)) ≤
        Real.exp (p.lam * (Real.exp s - 1)) := by
  classical
  let q : ℝ := p.lam / (p.V : ℝ)
  let X : p.Loc → Bool → ℝ := fun ℓ b =>
    if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then if b then 1 else 0 else 0
  have hq0 : 0 ≤ q := by dsimp [q]; exact div_nonneg hlam.le (Nat.cast_nonneg _)
  have hq1 : q ≤ 1 := by simpa [q] using hprob
  have hcoord (ℓ : p.Loc) :
      (FinProb.bernoulli q).expect (fun b => Real.exp (s * X ℓ b)) =
        if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
          1 + q * (Real.exp s - 1) else 1 := by
    by_cases h : ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r
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
        ∏ ℓ : p.Loc, if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
          1 + q * (Real.exp s - 1) else 1 := by
    simpa only [hcoord] using hprod
  have hfactor (ℓ : p.Loc) :
      0 ≤ (if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
        1 + q * (Real.exp s - 1) else 1) := by
    by_cases h : ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r
    · rw [if_pos h]
      have heq : 1 + q * (Real.exp s - 1) = 1 - q + q * Real.exp s := by ring
      rw [heq]
      positivity
    · simp [h]
  have hprodLe :
      (∏ ℓ : p.Loc, if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
        1 + q * (Real.exp s - 1) else 1) ≤
        ∏ ℓ : p.Loc, Real.exp (if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
          q * (Real.exp s - 1) else 0) := by
    apply Finset.prod_le_prod₀
    · intro ℓ hℓ
      exact hfactor ℓ
    · intro ℓ hℓ
      by_cases h : ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r
      · simp only [if_pos h]
        have := Real.add_one_le_exp (q * (Real.exp s - 1))
        nlinarith
      · simp [h]
  have hcard :
      (Finset.univ.filter (fun ℓ : p.Loc =>
        ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r)).card = p.V := by
    simpa [HDParams.Loc, HDParams.V] using levelBall_card p.d p.H p.r j v
  have hindicator :
      (∑ ℓ : p.Loc,
        if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) = p.V := by
    have hcast :
        (∑ ℓ : p.Loc,
          if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) =
          ((Finset.univ.filter (fun ℓ : p.Loc =>
            ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r)).card : ℝ) := by
      simpa using (Finset.natCast_card_filter
        (fun ℓ : p.Loc => ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r)
        (Finset.univ : Finset p.Loc))
    rw [hcast]
    exact_mod_cast hcard
  have hsum :
      (∑ ℓ : p.Loc,
        if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
          q * (Real.exp s - 1) else 0) = p.lam * (Real.exp s - 1) := by
    calc
      _ = (∑ ℓ : p.Loc,
          if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) *
            (q * (Real.exp s - 1)) := by
          calc
            _ = ∑ ℓ : p.Loc,
                (if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then (1 : ℝ) else 0) *
                  (q * (Real.exp s - 1)) := by
                    apply Finset.sum_congr rfl
                    intro ℓ hℓ
                    by_cases h : ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r <;> simp [h]
            _ = _ := by rw [Finset.sum_mul]
      _ = p.lam * (Real.exp s - 1) := by
          rw [hindicator]
          dsimp [q]
          have hVne : (p.V : ℝ) ≠ 0 := (Nat.cast_pos.mpr hV).ne'
          field_simp [hVne]
  calc
    p.posLaw.expect (fun P => Real.exp (s * ∑ ℓ : p.Loc, X ℓ (P ℓ))) ≤
        ∏ ℓ : p.Loc, if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then
          1 + q * (Real.exp s - 1) else 1 := le_of_eq hprodFactors
    _ ≤ ∏ ℓ : p.Loc, Real.exp
          (if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then q * (Real.exp s - 1) else 0) := hprodLe
    _ = Real.exp (∑ ℓ : p.Loc,
          if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then q * (Real.exp s - 1) else 0) := by
          symm
          rw [Real.exp_sum]
    _ = Real.exp (p.lam * (Real.exp s - 1)) := by rw [hsum]

private theorem position_bad_tail (p : HDParams) (hlam : 0 < p.lam)
    (hV : 0 < p.V) (hr : p.r ≤ p.d) (hprob : p.lam / (p.V : ℝ) ≤ 1)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    p.posLaw.pr (fun P => positionBad p P v j) ≤ 2 * Real.exp (-p.lam / 12) := by
  classical
  let X : p.Loc → Bool → ℝ := fun ℓ b =>
    if ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r then if b then 1 else 0 else 0
  have hcount (P : p.Loc → Bool) :
      positionCount p P v j = ∑ ℓ : p.Loc, X ℓ (P ℓ) := by
    have hnatNat :
        (Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ hammingDist u v ≤ p.r)).card =
          ∑ u : CubeVertex p.d,
            if hammingDist u v ≤ p.r then if P (u, j) = true then 1 else 0 else 0 := by
      rw [Finset.card_eq_sum_ite
        (s := Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ hammingDist u v ≤ p.r))
        (t := Finset.univ) (Finset.subset_univ _)]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine Finset.sum_congr rfl ?_
      intro u hu
      by_cases hd : hammingDist u v ≤ p.r <;> by_cases hp : P (u, j) = true <;>
        simp [hd, hp]
    have hnat :
        ((Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ hammingDist u v ≤ p.r)).card : ℝ) =
          ∑ u : CubeVertex p.d,
            if hammingDist u v ≤ p.r then if P (u, j) = true then (1 : ℝ) else 0 else 0 := by
      exact_mod_cast hnatNat
    rw [positionCount, hnat]
    rw [Fintype.sum_prod_type]
    simp only [X]
    refine Finset.sum_congr rfl ?_
    intro u hu
    rw [Finset.sum_eq_single j]
    · by_cases hd : hammingDist u v ≤ p.r
      · simp [hd]
      · simp [hd]
    · intro k hk hkj
      simp [hkj]
    · simp
  have hExpThird : Real.exp (1 / 3 : ℝ) ≤ 3 / 2 := by
    have hlog := Real.log_le_sub_one_of_pos
      (x := ((3 : ℝ) / 2)⁻¹) (inv_pos.mpr (by norm_num))
    rw [Real.log_inv] at hlog
    have hlog' : 1 / 3 ≤ Real.log ((3 : ℝ) / 2) := by
      norm_num at hlog ⊢
      linarith
    calc
      Real.exp (1 / 3 : ℝ) ≤ Real.exp (Real.log ((3 : ℝ) / 2)) :=
        Real.exp_le_exp.mpr hlog'
      _ = 3 / 2 := Real.exp_log (by norm_num)
  have hExpNegHalf : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    have hhalf : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
      have h := Real.add_one_le_exp (1 / 2 : ℝ)
      norm_num at h ⊢
      linarith
    calc
      Real.exp (-(1 / 2 : ℝ)) = (Real.exp (1 / 2))⁻¹ := by rw [Real.exp_neg]
      _ ≤ ((3 : ℝ) / 2)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr hhalf
      _ = 2 / 3 := by norm_num
  have hupper :
      p.posLaw.pr (fun P => 2 * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) ≤
        Real.exp (-p.lam / 6) := by
    have hmark := finProb_pr_exp_markov p.posLaw
      (fun P => ∑ ℓ : p.Loc, X ℓ (P ℓ)) (1 / 3) (2 * p.lam) (by norm_num)
    have hmgf := position_exp_mgf_le p hlam hV hprob v j (1 / 3)
    have hcoef : -(1 / 3 : ℝ) * 2 + (Real.exp (1 / 3) - 1) ≤ -(1 / 6 : ℝ) := by
      norm_num
      linarith [hExpThird]
    calc
      p.posLaw.pr (fun P => 2 * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) ≤
          Real.exp (-(1 / 3 : ℝ) * (2 * p.lam)) *
            p.posLaw.expect (fun P => Real.exp ((1 / 3 : ℝ) * ∑ ℓ : p.Loc, X ℓ (P ℓ))) := hmark
      _ ≤ Real.exp (-(1 / 3 : ℝ) * (2 * p.lam)) *
          Real.exp (p.lam * (Real.exp (1 / 3) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _)
      _ ≤ Real.exp (-p.lam / 6) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hterm := mul_le_mul_of_nonneg_left hcoef hlam.le
        nlinarith [hterm]
  have hlower :
      p.posLaw.pr (fun P => ∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ p.lam / 2) ≤
        Real.exp (-p.lam / 12) := by
    have hEvent :
        (fun P : p.Loc → Bool => ∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ p.lam / 2) =
          (fun P => -(p.lam / 2) ≤ -(∑ ℓ : p.Loc, X ℓ (P ℓ))) := by
      funext P
      apply propext
      constructor <;> intro h <;> linarith
    rw [hEvent]
    have hmark := finProb_pr_exp_markov p.posLaw
      (fun P => -(∑ ℓ : p.Loc, X ℓ (P ℓ))) (1 / 2) (-(p.lam / 2)) (by norm_num)
    have hmgf := position_exp_mgf_le p hlam hV hprob v j (-(1 / 2 : ℝ))
    have hmgf' : p.posLaw.expect
        (fun P => Real.exp ((1 / 2 : ℝ) * (-(∑ ℓ : p.Loc, X ℓ (P ℓ))))) ≤
          Real.exp (p.lam * (Real.exp (-(1 / 2 : ℝ)) - 1)) := by
      simpa [neg_mul] using hmgf
    have hcoef : (1 / 4 : ℝ) + (Real.exp (-(1 / 2 : ℝ)) - 1) ≤ -(1 / 12 : ℝ) := by
      have : Real.exp (-(1 / 2 : ℝ)) - 1 ≤ 2 / 3 - 1 := sub_le_sub_right hExpNegHalf 1
      norm_num
      linarith
    calc
      p.posLaw.pr (fun P => -(p.lam / 2) ≤ -(∑ ℓ : p.Loc, X ℓ (P ℓ))) ≤
          Real.exp (-(1 / 2 : ℝ) * (-(p.lam / 2))) *
            p.posLaw.expect (fun P => Real.exp ((1 / 2 : ℝ) *
              (-(∑ ℓ : p.Loc, X ℓ (P ℓ))))) := hmark
      _ ≤ Real.exp (-(1 / 2 : ℝ) * (-(p.lam / 2))) *
          Real.exp (p.lam * (Real.exp (-(1 / 2 : ℝ)) - 1)) :=
        mul_le_mul_of_nonneg_left hmgf' (Real.exp_nonneg _)
      _ ≤ Real.exp (-p.lam / 12) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hterm := mul_le_mul_of_nonneg_left hcoef hlam.le
        nlinarith [hterm]
  have hsubset (P : p.Loc → Bool) : positionBad p P v j →
      (∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ p.lam / 2) ∨
        2 * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ) := by
    intro h
    rcases h with h | h
    · left
      rw [← hcount P]
      exact le_of_lt h
    · right
      rw [← hcount P]
      exact le_of_lt h
  have hbad := finProb_pr_mono p.posLaw (fun P => positionBad p P v j)
    (fun P => (∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ p.lam / 2) ∨
      2 * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) hsubset
  have hunion := finProb_pr_or_le p.posLaw
    (fun P => ∑ ℓ : p.Loc, X ℓ (P ℓ) ≤ p.lam / 2)
    (fun P => 2 * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ))
  calc
    p.posLaw.pr (fun P => positionBad p P v j) ≤ _ := hbad.trans hunion
    _ ≤ Real.exp (-p.lam / 12) + Real.exp (-p.lam / 12) := add_le_add hlower (by
      calc
        p.posLaw.pr (fun P => 2 * p.lam ≤ ∑ ℓ : p.Loc, X ℓ (P ℓ)) ≤ Real.exp (-p.lam / 6) := hupper
        _ ≤ Real.exp (-p.lam / 12) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hlam])
    _ = 2 * Real.exp (-p.lam / 12) := by ring

set_option maxHeartbeats 1000000 in
private theorem position_counts_union (p : HDParams) (Sites : p.Sites)
    (hlam : 0 < p.lam) (hV : 0 < p.V) (hr : p.r ≤ p.d)
    (hprob : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.pr (fun P => ∃ v ∈ Sites, ∃ j : Fin (p.H + 1), positionBad p P v j) ≤
      2 * (Sites.card : ℝ) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 12) := by
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
      @finProb_pr_exists_le_sum (p.Loc → Bool) ι inferInstance inferInstance p.posLaw
        (fun x P => positionBad p P x.1.1 x.2)
    _ ≤ ∑ _x : ι, 2 * Real.exp (-p.lam / 12) := by
      apply Finset.sum_le_sum
      intro x hx
      exact position_bad_tail p hlam hV hr hprob x.1.1 x.2
    _ = 2 * (Sites.card : ℝ) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 12) := by
      simp [Finset.sum_const, nsmul_eq_mul, hcard]
      push_cast
      ring

private def tieMinEvent (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (A : p.Loc → Bool) (τ : p.Ties) (ℓ : p.Loc) : Prop :=
  A ℓ = true ∧ ∀ m ∈ S, A m = true → p.priority τ x ℓ ≤ p.priority τ x m

private def actSwapEquiv (p : HDParams) (a b : p.Loc) :
    (p.Loc → Bool) ≃ (p.Loc → Bool) where
  toFun A := fun ℓ => A (Equiv.swap a b ℓ)
  invFun A := fun ℓ => A (Equiv.swap a b ℓ)
  left_inv := by intro A; funext ℓ; simp
  right_inv := by intro A; funext ℓ; simp

private noncomputable def locIndexSwap (p : HDParams) (a b : p.Loc) :
    Equiv.Perm (Fin (Fintype.card p.Loc)) :=
  (Fintype.equivFin p.Loc).symm.trans ((Equiv.swap a b).trans (Fintype.equivFin p.Loc))

private theorem locIndexSwap_apply (p : HDParams) (a b ℓ : p.Loc) :
    locIndexSwap p a b (Fintype.equivFin p.Loc ℓ) =
      Fintype.equivFin p.Loc (Equiv.swap a b ℓ) := by
  simp [locIndexSwap, Equiv.trans_apply]

private noncomputable def tieSwap (p : HDParams) (x a b : p.Loc) (τ : p.Ties) : p.Ties :=
  Function.update τ x ((locIndexSwap p a b).trans (τ x))

private theorem tieSwap_involutive (p : HDParams) (x a b : p.Loc) (τ : p.Ties) :
    tieSwap p x a b (tieSwap p x a b τ) = τ := by
  funext y
  by_cases hy : y = x
  · subst y
    apply Equiv.ext
    intro k
    simp [tieSwap, locIndexSwap, Equiv.trans_apply]
  · simp [tieSwap, hy]

private noncomputable def tieSwapEquiv (p : HDParams) (x a b : p.Loc) : p.Ties ≃ p.Ties where
  toFun := tieSwap p x a b
  invFun := tieSwap p x a b
  left_inv := tieSwap_involutive p x a b
  right_inv := tieSwap_involutive p x a b

private noncomputable def sampleSwapEquiv (p : HDParams) (x a b : p.Loc) :
    ((p.Loc → Bool) × p.Ties) ≃ ((p.Loc → Bool) × p.Ties) :=
  Equiv.prodCongr (actSwapEquiv p a b) (tieSwapEquiv p x a b)

private theorem tieSwap_priority (p : HDParams) (x a b ℓ : p.Loc) (τ : p.Ties) :
    p.priority (tieSwap p x a b τ) x ℓ = p.priority τ x (Equiv.swap a b ℓ) := by
  simp [HDParams.priority, tieSwap, locIndexSwap_apply]

private theorem actSwap_weight (p : HDParams) (a b : p.Loc) (A : p.Loc → Bool) :
    p.actLaw.w (actSwapEquiv p a b A) = p.actLaw.w A := by
  change (∏ ℓ : p.Loc,
      (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w
        (A (Equiv.swap a b ℓ))) =
    ∏ ℓ : p.Loc, (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w (A ℓ)
  exact Fintype.prod_equiv (Equiv.swap a b)
    (fun ℓ => (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w
      (A (Equiv.swap a b ℓ)))
    (fun ℓ => (FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)).w (A ℓ))
    (fun _ => rfl)

private theorem tieSwap_weight (p : HDParams) (x a b : p.Loc) (τ : p.Ties) :
    p.tieLaw.w (tieSwap p x a b τ) = p.tieLaw.w τ := by
  simp [HDParams.tieLaw, FinProb.pi, FinProb.uniformAll]

private theorem sampleSwap_weight (p : HDParams) (x a b : p.Loc)
    (ω : (p.Loc → Bool) × p.Ties) :
    (p.actLaw.prod p.tieLaw).w (sampleSwapEquiv p x a b ω) =
      (p.actLaw.prod p.tieLaw).w ω := by
  rcases ω with ⟨A, τ⟩
  change p.actLaw.w (actSwapEquiv p a b A) * p.tieLaw.w (tieSwap p x a b τ) =
    p.actLaw.w A * p.tieLaw.w τ
  rw [actSwap_weight, tieSwap_weight]

private theorem swap_mem_iff (p : HDParams) (S : Finset p.Loc) (a b : p.Loc)
    (ha : a ∈ S) (hb : b ∈ S) (m : p.Loc) :
    m ∈ S ↔ Equiv.swap a b m ∈ S := by
  by_cases hma : m = a
  · subst m
    simp [ha, hb]
  · by_cases hmb : m = b
    · subst m
      simp [ha, hb]
    · rw [Equiv.swap_apply_of_ne_of_ne hma hmb]

private theorem tieMinEvent_swap (p : HDParams) (S : Finset p.Loc) (x a b : p.Loc)
    (ha : a ∈ S) (hb : b ∈ S) (ω : (p.Loc → Bool) × p.Ties) :
    tieMinEvent p S x (sampleSwapEquiv p x a b ω).1
        (sampleSwapEquiv p x a b ω).2 a ↔
      tieMinEvent p S x ω.1 ω.2 b := by
  rcases ω with ⟨A, τ⟩
  change tieMinEvent p S x (actSwapEquiv p a b A) (tieSwap p x a b τ) a ↔
    tieMinEvent p S x A τ b
  constructor
  · rintro ⟨hactive, hmin⟩
    refine ⟨?_, ?_⟩
    · simpa [actSwapEquiv] using hactive
    · intro m hm hAm
      have hm' : Equiv.swap a b m ∈ S := (swap_mem_iff p S a b ha hb m).mp hm
      have hAm' : (actSwapEquiv p a b A) (Equiv.swap a b m) = true := by
        simpa [actSwapEquiv, Equiv.swap_apply_self] using hAm
      have h := hmin (Equiv.swap a b m) hm' hAm'
      simpa [tieSwap_priority, Equiv.swap_apply_self] using h
  · rintro ⟨hactive, hmin⟩
    refine ⟨?_, ?_⟩
    · simpa [actSwapEquiv] using hactive
    · intro m hm hAm
      have hm' : Equiv.swap a b m ∈ S := (swap_mem_iff p S a b ha hb m).mp hm
      have hAm' : A (Equiv.swap a b m) = true := by
        simpa [actSwapEquiv, Equiv.swap_apply_self] using hAm
      have h := hmin (Equiv.swap a b m) hm' hAm'
      simpa [tieSwap_priority, Equiv.swap_apply_self] using h

private theorem finProb_pr_eq_of_equiv {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    (e : Ω ≃ Ω) (A B : Ω → Prop)
    (hweight : ∀ ω, μ.w (e ω) = μ.w ω)
    (hevent : ∀ ω, A (e ω) ↔ B ω) : μ.pr A = μ.pr B := by
  classical
  calc
    μ.pr A = ∑ ω, if A (e ω) then μ.w (e ω) else 0 := by
      unfold FinProb.pr
      rw [← Equiv.sum_comp e]
    _ = μ.pr B := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hB : B ω
      · have hA : A (e ω) := (hevent ω).mpr hB
        simp [hA, hB, hweight]
      · have hA : ¬ A (e ω) := fun h => hB ((hevent ω).mp h)
        simp [hA, hB, hweight]

private theorem tieMinEvent_unique (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (A : p.Loc → Bool) (τ : p.Ties) {a b : p.Loc}
    (ha : a ∈ S) (hb : b ∈ S)
    (hA : tieMinEvent p S x A τ a) (hB : tieMinEvent p S x A τ b) : a = b := by
  have hab : p.priority τ x a ≤ p.priority τ x b := hA.2 b hb hB.1
  have hba : p.priority τ x b ≤ p.priority τ x a := hB.2 a ha hA.1
  apply (Fintype.equivFin p.Loc).injective
  apply (τ x).injective
  simpa [HDParams.priority] using le_antisymm hab hba

open Classical in
private theorem tieMin_count_le_one (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (A : p.Loc → Bool) (τ : p.Ties) :
    (∑ ℓ ∈ S, if tieMinEvent p S x A τ ℓ then (1 : ℝ) else 0) ≤ 1 := by
  classical
  rw [Finset.sum_boole]
  have hcard : (S.filter (fun ℓ => tieMinEvent p S x A τ ℓ)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact tieMinEvent_unique p S x A τ
      (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  exact_mod_cast hcard

private theorem tieMin_probability_sum_le_one (p : HDParams) (S : Finset p.Loc)
    (x : p.Loc) :
    (∑ ℓ ∈ S, (p.actLaw.prod p.tieLaw).pr
      (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ)) ≤ 1 := by
  classical
  let μ := p.actLaw.prod p.tieLaw
  calc
    _ = ∑ ω, μ.w ω *
          (∑ ℓ ∈ S, if tieMinEvent p S x ω.1 ω.2 ℓ then (1 : ℝ) else 0) := by
      unfold FinProb.pr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      by_cases h : tieMinEvent p S x ω.1 ω.2 ℓ <;> simp [h, μ]
    _ ≤ ∑ ω, μ.w ω := by
      apply Finset.sum_le_sum
      intro ω hω
      have hcount := tieMin_count_le_one p S x ω.1 ω.2
      exact mul_le_of_le_one_right (μ.nonneg ω) hcount
    _ = 1 := μ.sum_eq_one

private theorem tieMin_probability_eq (p : HDParams) (S : Finset p.Loc) (x : p.Loc)
    (a b : p.Loc) (ha : a ∈ S) (hb : b ∈ S) :
    (p.actLaw.prod p.tieLaw).pr
        (fun ω => tieMinEvent p S x ω.1 ω.2 a) =
      (p.actLaw.prod p.tieLaw).pr
        (fun ω => tieMinEvent p S x ω.1 ω.2 b) := by
  let μ := p.actLaw.prod p.tieLaw
  exact finProb_pr_eq_of_equiv μ (sampleSwapEquiv p x a b)
    (fun ω => tieMinEvent p S x ω.1 ω.2 a)
    (fun ω => tieMinEvent p S x ω.1 ω.2 b)
    (sampleSwap_weight p x a b)
    (tieMinEvent_swap p S x a b ha hb)

private theorem tieMin_probability_le_inv (p : HDParams) (S : Finset p.Loc)
    (x ℓ₀ : p.Loc) (hℓ₀ : ℓ₀ ∈ S) :
    (p.actLaw.prod p.tieLaw).pr
      (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) ≤ (S.card : ℝ)⁻¹ := by
  have hsum := tieMin_probability_sum_le_one p S x
  have hsumEq :
      (∑ ℓ ∈ S, (p.actLaw.prod p.tieLaw).pr
        (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ)) =
        (S.card : ℝ) * (p.actLaw.prod p.tieLaw).pr
          (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) := by
    calc
      _ = ∑ ℓ ∈ S, (p.actLaw.prod p.tieLaw).pr
          (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            exact tieMin_probability_eq p S x ℓ ℓ₀ hℓ hℓ₀
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ℓ₀, hℓ₀⟩)
  have hmul : (S.card : ℝ) * (p.actLaw.prod p.tieLaw).pr
      (fun ω => tieMinEvent p S x ω.1 ω.2 ℓ₀) ≤ 1 := by
    rw [← hsumEq]
    exact hsum
  rw [← one_div]
  rw [le_div_iff₀ hcard]
  nlinarith [hmul]

private theorem selected_zero_is_min (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (v : CubeVertex p.d) (ℓ₀ : p.Loc)
    (hheight : p.height Sites P A E p.Rlong v = 0)
    (hselect : p.selection Sites P A E τ v = some ℓ₀) :
    tieMinEvent p (E v ⟨0, by omega⟩) (v, ⟨0, by omega⟩) A τ ℓ₀ := by
  classical
  by_cases hH : 0 < p.H
  · simp [HDParams.selection, HDParams.selectionAt, hheight, hH] at hselect
    rcases hselect with ⟨_, ⟨hne, hchosen⟩⟩
    let j0 : Fin (p.H + 1) := ⟨0, by omega⟩
    let active : Finset p.Loc := (E v j0).filter (fun ℓ => A ℓ = true)
    let priorities := active.image (p.priority τ (v, j0))
    have hneP : priorities.Nonempty := by
      rcases hne with ⟨ℓ, hℓ⟩
      exact ⟨p.priority τ (v, j0) ℓ, Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩⟩
    let q := priorities.min' hneP
    have hmem : ∃ ℓ, ℓ ∈ active ∧ p.priority τ (v, j0) ℓ = q :=
      Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    have hchosen' : Classical.choose hmem = ℓ₀ := by
      simpa [active, priorities, q, j0] using hchosen
    rcases Classical.choose_spec hmem with ⟨hactive, hrank⟩
    rw [hchosen'] at hactive hrank
    refine ⟨(Finset.mem_filter.mp hactive).2, ?_⟩
    intro m hm hAm
    have hmActive : m ∈ active := by
      simp only [active, Finset.mem_filter]
      exact ⟨hm, hAm⟩
    calc
      p.priority τ (v, j0) ℓ₀ = q := hrank
      _ ≤ p.priority τ (v, j0) m :=
        Finset.min'_le priorities (p.priority τ (v, j0) m)
          (Finset.mem_image.mpr ⟨m, hmActive, rfl⟩)
  · simp [HDParams.selection, HDParams.selectionAt, hheight, hH] at hselect

private theorem height_selection_tie_aux (p : HDParams) (hlam : 0 < p.lam)
    (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ₀ : p.Loc)
    (hlegal : p.LegalAt P E v ⟨0, by omega⟩) (hℓ : ℓ₀ ∈ E v ⟨0, by omega⟩) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ₀) ≤ 3 / p.lam := by
  classical
  let j0 : Fin (p.H + 1) := ⟨0, by omega⟩
  let S : Finset p.Loc := E v j0
  have hlegal' : p.LegalAt P E v j0 := by simpa [j0] using hlegal
  have hsize : p.lam / 3 ≤ (S.card : ℝ) := by
    simpa [S] using hlegal'.2
  have hℓS : ℓ₀ ∈ S := by simpa [S, j0] using hℓ
  have hcardpos : 0 < (S.card : ℝ) :=
    lt_of_lt_of_le (by nlinarith [hlam]) hsize
  have hsubset (ω : (p.Loc → Bool) × p.Ties) :
      (p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ₀) →
      tieMinEvent p S (v, j0) ω.1 ω.2 ℓ₀ := by
    rintro ⟨hh, hs⟩
    exact selected_zero_is_min p Sites P ω.1 E ω.2 v ℓ₀ hh hs
  have hmono := finProb_pr_mono (p.actLaw.prod p.tieLaw)
    (fun ω => p.height Sites P ω.1 E p.Rlong v = 0 ∧
      p.selection Sites P ω.1 E ω.2 v = some ℓ₀)
    (fun ω => tieMinEvent p S (v, j0) ω.1 ω.2 ℓ₀) hsubset
  have hmin := tieMin_probability_le_inv p S (v, j0) ℓ₀ hℓS
  have hrecip : (S.card : ℝ)⁻¹ ≤ 3 / p.lam := by
    rw [← one_div]
    rw [div_le_div_iff₀ hcardpos hlam]
    nlinarith [hsize]
  exact hmono.trans (hmin.trans hrecip)

theorem height_position_counts_p_height_small (p : HDParams) (Sites : p.Sites)
    (hlam : 0 < p.lam) (hV : 0 < p.V) (hr : p.r ≤ p.d)
    (hprob : p.lam / (p.V : ℝ) ≤ 1) :
    p.posLaw.pr (fun P => ∃ v ∈ Sites, ∃ j : Fin (p.H + 1),
      let count := (Finset.univ.filter (fun u : CubeVertex p.d =>
        P (u, j) = true ∧ hammingDist u v ≤ p.r)).card
      ((count : ℝ) < p.lam / 2 ∨ 2 * p.lam < (count : ℝ))) ≤
      2 * (Sites.card : ℝ) * ((p.H + 1 : ℕ) : ℝ) * Real.exp (-p.lam / 12) := by
  simpa [positionBad, positionCount] using position_counts_union p Sites hlam hV hr hprob

theorem height_selection_tie_p_height_small (p : HDParams) (hlam : 0 < p.lam)
    (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites)
    (v : CubeVertex p.d) (ℓ₀ : p.Loc)
    (hlegal : p.LegalAt P E v ⟨0, by omega⟩) (hℓ : ℓ₀ ∈ E v ⟨0, by omega⟩) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some ℓ₀) ≤ 3 / p.lam :=
  height_selection_tie_aux p hlam P E Sites v ℓ₀ hlegal hℓ

end HypercubeRamsey
