import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56
import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

namespace HypercubeRamsey.Lane_sol_s10_d56

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

theorem hammingBall_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // _root_.hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => _root_.hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => _root_.hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans (card_small_subsets d r))


/-- Summing named selection weights over all levels costs 1/.99 plus the height error. -/
theorem selectionCap_sum_mean_le (p : HDParams) (hlam : 0 < p.lam)
    (hV : 0 < p.V) (Sites : p.Sites) (v : CubeVertex p.d) (hv : v ∈ Sites)
    (hball : (Finset.univ.filter fun u : CubeVertex p.d =>
      _root_.hammingDist u v ≤ p.r).card = p.V)
    (hq1 : p.lam / (p.V : ℝ) ≤ 1) (ε : ℝ)
    (hbound : ∀ ℓ : p.Loc, 0 < ℓ.2.val →
      ∀ Esel : (p.Loc → Bool) → p.EligMap,
      ((p.posLawForced (some ℓ)).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
        0 < p.height Sites ω.1 ω.2 (Esel ω.1) p.Rlong v) ≤ ε) :
    (∑ ℓ : p.Loc, p.posLaw.expect (selectionCap p Sites v ℓ)) ≤
      1 / (99 / 100 : ℝ) + (p.H : ℝ) * p.lam * ε := by
  classical
  let q : ℝ := p.lam / (p.V : ℝ)
  let B : Finset (CubeVertex p.d) := Finset.univ.filter fun u => _root_.hammingDist u v ≤ p.r
  let coeff : Fin (p.H + 1) → ℝ := fun j =>
    if j.val = 0 then q * (1 / ((99 / 100 : ℝ) * p.lam)) else q * ε
  have hq0 : 0 ≤ q := div_nonneg hlam.le (Nat.cast_nonneg _)
  have hweight (ℓ : p.Loc) : p.posLaw.expect (selectionCap p Sites v ℓ) ≤
      if ℓ.1 ∈ B then coeff ℓ.2 else 0 := by
    by_cases hb : ℓ.1 ∈ B
    · rw [ite_eq_left hb]
      by_cases hj : ℓ.2.val = 0
      · dsimp [coeff]
        rw [ite_eq_left hj]
        exact selectionCap_zero_mean_le p hlam Sites v hv ℓ hj hq1
      · dsimp [coeff]
        rw [ite_eq_right hj]
        exact selectionCap_positive_mean_le p Sites v hv ℓ (by omega) hq0 hq1 ε
            (hbound ℓ (by omega))
    · rw [ite_eq_right hb]
      have hfar : ¬ _root_.hammingDist ℓ.1 v ≤ p.r := by
        simpa [B] using hb
      have hz (P : p.Loc → Bool) : selectionCap p Sites v ℓ P = 0 :=
        selectionCap_eq_zero_of_not_position p Sites v hv ℓ P (fun h => hfar h.2)
      simp [FinProb.expect, hz]
  calc
    (∑ ℓ : p.Loc, p.posLaw.expect (selectionCap p Sites v ℓ)) ≤
        ∑ ℓ : p.Loc, if ℓ.1 ∈ B then coeff ℓ.2 else 0 :=
      Finset.sum_le_sum fun ℓ _ => hweight ℓ
    _ = (p.V : ℝ) * ∑ j : Fin (p.H + 1), coeff j := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast (show (Finset.univ ∩ B).card = p.V by simpa [B] using hball)
    _ = (p.V : ℝ) * (q * (1 / ((99 / 100 : ℝ) * p.lam)) + (p.H : ℝ) * (q * ε)) := by
      congr 1
      rw [Fin.sum_univ_succ]
      simp [coeff]
    _ = 1 / (99 / 100 : ℝ) + (p.H : ℝ) * p.lam * ε := by
      have hVreal : (p.V : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hV)
      dsimp [q]
      field_simp
      <;> ring


/-- Section 10's concrete parameters inherit the uniform forced-center height estimate. -/
theorem s10_positive_height_eventually (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let p := p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites)
        (forced : Option p.Loc) (Esel : (p.Loc → Bool) → p.EligMap),
        ((p.posLawForced forced).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
          0 < p.height Sites ω.1 ω.2 (Esel ω.1) p.Rlong v) ≤
            Real.exp (-(n : ℝ) ^ c) := by
  have hp := p10_1k_heightAdmissible δ hδ hδsmall
  let reg := p10_1k_heightRegime δ hδ hδsmall
  obtain ⟨c, hc, nPos, hpos⟩ :=
    HypercubeRamsey.height_selection_positive 10 (50 * δ) (140 * δ) δ (8 * δ)
      (1 - δ) (20 * δ) (1 / 2) 1 6 hp reg
  obtain ⟨nDim, hdim⟩ := Filter.eventually_atTop.mp
    (p10_1kHeightParams_dimension_eventually 1 1 δ (by norm_num) (by norm_num) hδ
      (by simpa using hδsmall))
  refine ⟨c, hc, max nPos nDim, ?_⟩
  intro n hn
  dsimp only
  let m : ℕ := ⌊(n : ℝ) ^ (200 * δ)⌋₊
  let p : HDParams := p10_1kHeightParams n m δ
  have hd := hdim n (le_trans (le_max_right _ _) hn)
  have hreg : reg.ok p.n p.d p.r := by
    simpa [p, reg, p10_1kHeightParams, p10_1k_heightRegime] using
      p10_1kHeightParams_subRegime_ok n m δ hδ hδsmall
  have hlam : p.lam = (p.n : ℝ) ^ (10 : ℝ) := by
    dsimp [p, p10_1kHeightParams]
    exact (Real.rpow_natCast _ 10).symm
  have hupper : (p.d : ℝ) ≤ 1 * (p.n : ℝ) := by
    simpa [p, p10_1kHeightParams] using hd.2
  intro Sites v hv forced Esel
  let U : FinProb Unit := FinProb.uniformAll ⟨()⟩
  have hh := hpos p rfl rfl hlam rfl rfl
    (le_trans (le_max_left _ _) hn) hd.1 hupper hreg Sites v hv forced U
    (fun P _ => Esel P)
  have hunit := pr_prod_unit_middle (p.posLawForced forced) p.actLaw
    (fun P A => p.Legal P (Esel P) (p.domBall Sites v p.Rlong) ∧
      0 < p.height Sites P A (Esel P) p.Rlong v)
  change ((p.posLawForced forced).prod p.actLaw).pr (fun ω =>
    p.Legal ω.1 (Esel ω.1) (p.domBall Sites v p.Rlong) ∧
    0 < p.height Sites ω.1 ω.2 (Esel ω.1) p.Rlong v) ≤ Real.exp (-(n : ℝ) ^ c)
  rw [← hunit]
  exact hh

/-- The total external-slice weight has the paper's sharp 1/.99+o(1) form. -/
theorem s10_external_weight_sum_eventually (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀,
      let p := p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites),
        (∑ ℓ : p.Loc, p.posLaw.expect (selectionCap p Sites v ℓ)) ≤
          1 / (99 / 100 : ℝ) + (p.H : ℝ) * p.lam * Real.exp (-(n : ℝ) ^ c) := by
  obtain ⟨c, hc, nPos, hpos⟩ := s10_positive_height_eventually δ hδ hδsmall
  obtain ⟨nVol, hvol⟩ := Filter.eventually_atTop.mp
    (p10_1kHeightParams_activity_le_volume_eventually 1 1 δ
      (by norm_num) (by norm_num) hδ (by simpa using hδsmall))
  refine ⟨c, hc, max 2 (max nPos nVol), ?_⟩
  intro n hn
  dsimp only
  let p := p10_1kHeightParams n ⌊(n : ℝ) ^ (200 * δ)⌋₊ δ
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hposn := hpos n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hvoln := hvol n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlam : 0 < p.lam := by
    dsimp [p, p10_1kHeightParams]
    exact pow_pos hnreal _
  have hVreal : 0 < (p.V : ℝ) := lt_of_lt_of_le hlam hvoln
  have hV : 0 < p.V := by exact_mod_cast hVreal
  have hq1 : p.lam / (p.V : ℝ) ≤ 1 := (div_le_one hVreal).2 hvoln
  intro Sites v hv
  exact selectionCap_sum_mean_le p hlam hV Sites v hv
    (hammingBall_card p.d p.r v) hq1 (Real.exp (-(n : ℝ) ^ c))
    (fun ℓ hℓ Esel => hposn Sites v hv (some ℓ) Esel)

end HypercubeRamsey.Lane_sol_s10_d56
