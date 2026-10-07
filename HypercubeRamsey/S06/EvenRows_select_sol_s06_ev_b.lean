import HypercubeRamsey.S06.EvenRows_sol_s06_ev_b

namespace HypercubeRamsey.S06.Lane_sol_s06_ev_b
open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section

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

theorem allLevelBall_card (p : HDParams) (v : CubeVertex p.d) :
    (Finset.univ.filter (fun c : p.Loc => hammingDist c.1 v ≤ p.r)).card = p.V * (p.H + 1) := by
  classical
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  change (∑ u : CubeVertex p.d, ∑ _j : Fin (p.H + 1), if hammingDist u v ≤ p.r then 1 else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hball : (∑ u : CubeVertex p.d, if hammingDist u v ≤ p.r then 1 else 0) = p.V := by
    have hcard : (Finset.univ.filter (fun u : CubeVertex p.d => hammingDist u v ≤ p.r)).card = p.V :=
      hammingBall_card p.d p.r v
    rw [Finset.card_filter] at hcard
    exact hcard
  rw [hball]
  exact Nat.mul_comm _ _


theorem position_forcing (p : HDParams) (c : p.Loc) (P : p.Loc → Bool) :
    (if P c = true then p.posLaw.w P else 0) =
      max 0 (min (p.lam / (p.V : ℝ)) 1) * (p.posLawForced (some c)).w P := by
  classical
  have hrest : (∏ i ∈ Finset.univ.erase c,
      (FinProb.bernoulli (p.lam / (p.V : ℝ))).w (P i)) =
      ∏ i ∈ Finset.univ.erase c,
        (if some c = some i then FinProb.bernoulli 1 else
          FinProb.bernoulli (p.lam / (p.V : ℝ))).w (P i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : c ≠ i := Ne.symm (Finset.ne_of_mem_erase hi)
    simp [hne]
  have hraw := Finset.mul_prod_erase (s := Finset.univ)
    (f := fun i => (FinProb.bernoulli (p.lam / (p.V : ℝ))).w (P i)) (Finset.mem_univ c)
  have hforced := Finset.mul_prod_erase (s := Finset.univ)
    (f := fun i => (if some c = some i then FinProb.bernoulli 1 else
      FinProb.bernoulli (p.lam / (p.V : ℝ))).w (P i)) (Finset.mem_univ c)
  change (if P c = true then ∏ i, (FinProb.bernoulli (p.lam / (p.V : ℝ))).w (P i) else 0) =
    max 0 (min (p.lam / (p.V : ℝ)) 1) *
      ∏ i, (if some c = some i then FinProb.bernoulli 1 else
        FinProb.bernoulli (p.lam / (p.V : ℝ))).w (P i)
  rw [← hraw, ← hforced, hrest]
  cases hP : P c <;> simp [hP, FinProb.bernoulli]

private theorem power_reaches (M R t : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ j, t ≤ M ^ j * R := by
  induction t with
  | zero => exact ⟨0, by omega⟩
  | succ t ih =>
    obtain ⟨j, hj⟩ := ih
    have hp : 1 ≤ M ^ j * R := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))
    refine ⟨j + 1, ?_⟩
    rw [pow_succ]
    nlinarith

theorem topScale_bound {n : ℕ} (hn : 2 ≤ n) {σ ζ : ℝ}
    (hσ : σ ≤ 1) (hζ : 0 ≤ ζ) : topScale n σ ζ ≤ 4 * n ^ 2 := by
  let R : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let t : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogLe : Real.log (n : ℝ) ≤ n := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hR : R ≤ n ^ 2 := by
    apply max_le (by nlinarith)
    apply Nat.ceil_le.mpr
    push_cast
    nlinarith

  have hM : M ≤ 2 * n := by
    apply max_le (by omega)
    apply Nat.ceil_le.mpr
    have hp : (n : ℝ) ^ σ ≤ n := by
      simpa using Real.rpow_le_rpow_of_exponent_le hnR hσ
    push_cast
    linarith
  have ht : t ≤ n := by
    apply Nat.ceil_le.mpr
    simpa using Real.rpow_le_rpow_of_exponent_le hnR (by linarith : 1 - ζ ≤ 1)
  let hex : ∃ j, t ≤ M ^ j * R := power_reaches M R t (le_max_left _ _) (le_max_left _ _)
  change M ^ Nat.find hex * R ≤ 4 * n ^ 2
  by_cases hj : Nat.find hex = 0
  · simp only [hj, pow_zero, one_mul]
    nlinarith [hR]
  · have hprev : M ^ (Nat.find hex - 1) * R < t :=
      lt_of_not_ge (Nat.find_min hex (by omega))
    have hpow : M ^ Nat.find hex * R = M * (M ^ (Nat.find hex - 1) * R) := by
      have hi : Nat.find hex = (Nat.find hex - 1) + 1 := by omega
      conv_lhs => rw [hi]
      rw [pow_succ]
      ring
    rw [hpow]
    nlinarith

theorem selection_mem (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (c : p.Loc)
    (hs : p.selection Sites P A E τ v = some c) :
    ∃ j : Fin (p.H + 1), c ∈ E v j ∧ j.val = p.height Sites P A E p.Rlong v := by
  classical
  unfold HDParams.selection at hs
  dsimp only [HDParams.selectionAt] at hs
  split_ifs at hs with hj hbad hne
  all_goals try cases hs
  let j : Fin (p.H + 1) := ⟨p.height Sites P A E p.Rlong v, by omega⟩
  let active := (E v j).filter fun i => A i = true
  let priorities := active.image fun i => p.priority τ (v, j) i
  have hmem := Finset.mem_image.mp (Finset.min'_mem priorities hne)
  exact ⟨j, (Finset.mem_filter.mp (Classical.choose_spec hmem).1).1, rfl⟩

theorem legal_zero_selection (p : HDParams) (hlam : 0 < p.lam)
    (P : p.Loc → Bool) (E : p.EligMap) (Sites : p.Sites) (v : CubeVertex p.d) (c : p.Loc) :
    (p.actLaw.prod p.tieLaw).pr (fun ω =>
      p.LegalAt P E v 0 ∧ p.height Sites P ω.1 E p.Rlong v = 0 ∧
        p.selection Sites P ω.1 E ω.2 v = some c) ≤ 3 / p.lam := by
  classical
  by_cases hl : p.LegalAt P E v 0
  · by_cases hc : c ∈ E v 0
    · simpa [hl] using height_selection_tie p hlam P E Sites v c hl hc
    · have hz : (p.actLaw.prod p.tieLaw).pr (fun ω =>
          p.LegalAt P E v 0 ∧ p.height Sites P ω.1 E p.Rlong v = 0 ∧
            p.selection Sites P ω.1 E ω.2 v = some c) = 0 := by
        apply pr_zero_of_supp6
        intro ω _ h
        obtain ⟨j, hj, hheight⟩ := selection_mem p Sites P ω.1 E ω.2 v c h.2.2
        have hj0 : j = 0 := Fin.ext (hheight.trans h.2.1)
        exact hc (by simpa [hj0] using hj)
      rw [hz]
      positivity
  · simp [FinProb.pr, hl]
    positivity

theorem pr_force_le {Ω : Type*} [Fintype Ω] (p : HDParams) (c : p.Loc)
    (hlam : 0 ≤ p.lam) (T : FinProb Ω) (B : (p.Loc → Bool) × Ω → Prop)
    (hB : ∀ ω, B ω → ω.1 c = true) :
    (p.posLaw.prod T).pr B ≤ (p.lam / (p.V : ℝ)) * ((p.posLawForced (some c)).prod T).pr B := by
  classical
  let q := max 0 (min (p.lam / (p.V : ℝ)) 1)
  have heq : (p.posLaw.prod T).pr B = q * ((p.posLawForced (some c)).prod T).pr B := by
    unfold FinProb.pr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases h : B ω
    · simp only [if_pos h, FinProb.prod]
      have hh := position_forcing p c ω.1
      rw [if_pos (hB ω h)] at hh
      rw [hh]
      ring
    · simp [h]
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (pr_nonneg6 _ _)
  exact max_le (div_nonneg hlam (Nat.cast_nonneg _)) (min_le_left _ _)

theorem pr_assoc {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    (P : FinProb α) (Q : FinProb β) (R : FinProb δ) (B : (α × β) × δ → Prop) :
    ((P.prod Q).prod R).pr B =
      (P.prod (Q.prod R)).pr (fun w => B ((w.1, w.2.1), w.2.2)) := by
  classical
  simp only [FinProb.pr, FinProb.prod]
  simp_rw [Fintype.sum_prod_type, mul_assoc]

theorem pr_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (B : α → Prop) :
    (P.prod Q).pr (fun w => B w.1) = P.pr B := by
  exact pr_bind_fst6 P (fun _ => Q) B

theorem expect_indicator {α : Type*} [Fintype α] (P : FinProb α) (B : α → Prop) :
    P.expect (fun w => if B w then 1 else 0) = P.pr B := by
  classical
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro w hw
  by_cases h : B w <;> simp [h]

theorem pr_prod_le {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (B : α × β → Prop) (b : ℝ)
    (h : ∀ a, Q.pr (fun x => B (a, x)) ≤ b) : (P.prod Q).pr B ≤ b := by
  rw [Lane_q_s06_even.pr_prod_eq_sum_even]
  calc
    (∑ a, P.w a * Q.pr (fun x => B (a, x))) ≤ ∑ a, P.w a * b :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)
    _ = b := by rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem forced_selection_sum (p : HDParams) (hlam : 0 < p.lam)
    (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    {Aux : Type*} [Fintype Aux] (Q : FinProb Aux)
    (Es : p.Loc → (p.Loc → Bool) → Aux → p.EligMap)
    (B : p.Loc → (((p.Loc → Bool) × Aux) × (p.Loc → Bool)) × p.Ties → Prop)
    (hB : ∀ c P o A τ, B c (((P, o), A), τ) →
      P c = true ∧ p.Legal P (Es c P o) (p.domBall Sites v p.Rlong) ∧
        p.selection Sites P A (Es c P o) τ v = some c)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hpos : ∀ c, (((p.posLawForced (some c)).prod Q).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (Es c ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites ω.1.1 ω.2 (Es c ω.1.1 ω.1.2) p.Rlong v) ≤ ε) :
    ∑ c, (((p.posLaw.prod Q).prod p.actLaw).prod p.tieLaw).pr (B c) ≤
      3 + p.lam * (p.H + 1) * ε := by
  classical
  have hvdom : v ∈ p.domBall Sites v p.Rlong := by simp [HDParams.domBall, hv]
  let raw := ((p.posLaw.prod Q).prod p.actLaw).prod p.tieLaw
  let forced := fun c => (((p.posLawForced (some c)).prod Q).prod p.actLaw).prod p.tieLaw
  let height := fun c (w : (((p.Loc → Bool) × Aux) × (p.Loc → Bool)) × p.Ties) =>
    p.height Sites w.1.1.1 w.1.2 (Es c w.1.1.1 w.1.1.2) p.Rlong v
  have hball (c) (w) (hw : B c w) : hammingDist c.1 v ≤ p.r := by
    have h := hB c w.1.1.1 w.1.1.2 w.1.2 w.2 hw
    obtain ⟨j, hj, _⟩ := selection_mem p Sites _ _ _ _ v c h.2.2
    exact (h.2.1 v hvdom j).1 c hj |>.2.2
  have hlevel (c) (w) (hw : B c w) (hh : height c w = 0) : c.2 = 0 := by
    have h := hB c w.1.1.1 w.1.1.2 w.1.2 w.2 hw
    obtain ⟨j, hj, hheight⟩ := selection_mem p Sites _ _ _ _ v c h.2.2
    have hj0 : j = 0 := Fin.ext (hheight.trans hh)
    exact ((h.2.1 v hvdom j).1 c hj).2.1.trans hj0
  have hforce (c) : raw.pr (B c) ≤ p.lam / (p.V : ℝ) * (forced c).pr (B c) := by
    dsimp [raw, forced]
    rw [pr_assoc, pr_assoc, pr_assoc, pr_assoc]
    apply pr_force_le p c hlam.le
    intro w hw
    exact (hB c w.1 w.2.1 w.2.2.1 w.2.2.2 hw).1
  have hzero (c) : (forced c).pr (fun w => B c w ∧ height c w = 0) ≤
      if c.2 = 0 ∧ hammingDist c.1 v ≤ p.r then 3 / p.lam else 0 := by
    by_cases hc : c.2 = 0 ∧ hammingDist c.1 v ≤ p.r
    · rw [if_pos hc]
      dsimp [forced]
      rw [pr_assoc]
      apply pr_prod_le
      intro w
      apply le_trans _ (legal_zero_selection p hlam w.1 (Es c w.1 w.2) Sites v c)
      apply pr_mono6
      intro ω h
      have hh := hB c w.1 w.2 ω.1 ω.2 h.1
      exact ⟨hh.2.1 v hvdom 0, h.2, hh.2.2⟩
    · rw [if_neg hc]
      apply le_of_eq
      apply pr_zero_of_supp6
      intro w _ ⟨hb, hh⟩
      exact hc ⟨hlevel c w hb hh, hball c w hb⟩
  have hpositive (c) : (forced c).pr (fun w => B c w ∧ 0 < height c w) ≤
      if hammingDist c.1 v ≤ p.r then ε else 0 := by
    by_cases hc : hammingDist c.1 v ≤ p.r
    · rw [if_pos hc]
      apply le_trans _ (hpos c)
      rw [← pr_fst (((p.posLawForced (some c)).prod Q).prod p.actLaw) p.tieLaw]
      apply pr_mono6
      intro w ⟨hb, hh⟩
      exact ⟨(hB c w.1.1.1 w.1.1.2 w.1.2 w.2 hb).2.1, hh⟩
    · rw [if_neg hc]
      apply le_of_eq
      apply pr_zero_of_supp6
      intro w _ h
      exact hc (hball c w h.1)
  have hsplit (c) : (forced c).pr (B c) ≤
      (if c.2 = 0 ∧ hammingDist c.1 v ≤ p.r then 3 / p.lam else 0) +
        (if hammingDist c.1 v ≤ p.r then ε else 0) := by
    calc
      (forced c).pr (B c) ≤ (forced c).pr (fun w =>
          (B c w ∧ height c w = 0) ∨ (B c w ∧ 0 < height c w)) :=
        pr_mono6 _ (fun w hb => by
          by_cases hh : height c w = 0
          · exact Or.inl ⟨hb, hh⟩
          · exact Or.inr ⟨hb, Nat.pos_of_ne_zero hh⟩)
      _ ≤ (forced c).pr (fun w => B c w ∧ height c w = 0) +
          (forced c).pr (fun w => B c w ∧ 0 < height c w) := pr_or_le6 _ _ _
      _ ≤ _ := add_le_add (hzero c) (hpositive c)
  have hV : (0 : ℝ) < p.V := by
    have hcard : (Finset.univ.filter (fun c : p.Loc =>
        c.2 = 0 ∧ hammingDist c.1 v ≤ p.r)).card = p.V :=
      levelBall_card p.d p.H p.r (0 : Fin (p.H + 1)) v
    have hmem : (v, (0 : Fin (p.H + 1))) ∈ Finset.univ.filter
        (fun c : p.Loc => c.2 = 0 ∧ hammingDist c.1 v ≤ p.r) := by simp [HypercubeRamsey.hammingDist]
    exact_mod_cast (hcard ▸ Finset.card_pos.mpr ⟨_, hmem⟩ : 0 < p.V)
  have hsum0 : (∑ c : p.Loc, if c.2 = 0 ∧ hammingDist c.1 v ≤ p.r then 3 / p.lam else 0) =
      (p.V : ℝ) * (3 / p.lam) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [levelBall_card p.d p.H p.r (0 : Fin (p.H + 1)) v]
    rfl
  have hsumPos : (∑ c : p.Loc, if hammingDist c.1 v ≤ p.r then ε else 0) =
      (p.V : ℝ) * (p.H + 1) * ε := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, allLevelBall_card, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    (∑ c, raw.pr (B c)) ≤ ∑ c, p.lam / (p.V : ℝ) *
        ((if c.2 = 0 ∧ hammingDist c.1 v ≤ p.r then 3 / p.lam else 0) +
          (if hammingDist c.1 v ≤ p.r then ε else 0)) :=
      Finset.sum_le_sum fun c _ => (hforce c).trans
        (mul_le_mul_of_nonneg_left (hsplit c) (by positivity))
    _ = p.lam / (p.V : ℝ) * ((p.V : ℝ) * (3 / p.lam) + (p.V : ℝ) * (p.H + 1) * ε) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hsum0, hsumPos]
    _ = 3 + p.lam * (p.H + 1) * ε := by field_simp [hV.ne', hlam.ne']


theorem eventually_height_error (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      5 * (n : ℝ) ^ (12 : ℕ) * Real.exp (-(n : ℝ) ^ c) ≤ 1 := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (12 / c) 1 (by norm_num)).comp hpow
  have heq (n : ℕ) : ((n : ℝ) ^ c) ^ (12 / c) = (n : ℝ) ^ (12 : ℕ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    rw [show c * (12 / c) = 12 by field_simp]
    norm_cast
  have hlim' : Tendsto (fun n : ℕ => 5 * (n : ℝ) ^ (12 : ℕ) *
      Real.exp (-(n : ℝ) ^ c)) atTop (nhds 0) := by
    have hh := hlim.const_mul 5
    simpa [heq, mul_assoc] using hh
  obtain ⟨n₀, h⟩ := eventually_atTop.mp (hlim'.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  exact ⟨n₀, fun n hn => (h n hn).le⟩

end
end HypercubeRamsey.S06.Lane_sol_s06_ev_b
