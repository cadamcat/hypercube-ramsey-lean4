import HypercubeRamsey.S05.Even_load_selection_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

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

def levelBall (p : HDParams) (v : CubeVertex p.d) (j : Fin (p.H + 1)) : Finset p.Loc :=
  Finset.univ.filter fun l => l.2 = j ∧ _root_.hammingDist l.1 v ≤ p.r

theorem levelBall_volume (p : HDParams) (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
    (levelBall p v j).card = p.V := by
  exact levelBall_card p.d p.H p.r j v

theorem height_ball_volume_positive (p : HDParams) : 0 < p.V := by
  have hh := Finset.single_le_sum (fun i _ => Nat.zero_le (Nat.choose p.d i))
    (Finset.mem_range.mpr (Nat.zero_lt_succ p.r))
  change Nat.choose p.d 0 ≤ p.V at hh
  simpa using lt_of_lt_of_le (by norm_num : 0 < Nat.choose p.d 0) hh

theorem sum_selection_rates (p : HDParams) (v : CubeVertex p.d) (hlam : 0 < p.lam)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ j : Fin (p.H + 1), ∑ _l ∈ levelBall p v j,
      max 0 (min (p.lam / (p.V : ℝ)) 1) * (if j.val = 0 then 3 / p.lam else ε)) ≤
        3 + ((p.H + 1 : ℕ) : ℝ) * p.lam * ε := by
  let a : ℝ := max 0 (min (p.lam / (p.V : ℝ)) 1)
  have ha0 : 0 ≤ a := le_max_left _ _
  have hV : (0 : ℝ) < p.V := by exact_mod_cast height_ball_volume_positive p
  have ha : a ≤ p.lam / (p.V : ℝ) :=
    max_le (div_nonneg hlam.le hV.le) (min_le_left _ _)
  have haV : a * p.V ≤ p.lam := (le_div_iff₀ hV).mp ha
  have hj0 : (⟨0, by omega⟩ : Fin (p.H + 1)).val = 0 := rfl
  have hsum : (∑ j : Fin (p.H + 1), if j.val = 0 then 3 / p.lam else ε) ≤
      3 / p.lam + ((p.H + 1 : ℕ) : ℝ) * ε := by
    calc
      _ ≤ ∑ j : Fin (p.H + 1), ((if j.val = 0 then 3 / p.lam else 0) + ε) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j.val = 0 <;> simp [h] <;> linarith
      _ = _ := by
        rw [Finset.sum_add_distrib]
        have heq (j : Fin (p.H + 1)) : j.val = 0 ↔ j = ⟨0, by omega⟩ := by
          constructor
          · intro h; exact Fin.ext h
          · intro h; rw [h]
        simp_rw [heq]
        simp
  calc
    _ = a * (p.V : ℝ) * ∑ j : Fin (p.H + 1), if j.val = 0 then 3 / p.lam else ε := by
      simp only [Finset.sum_const, nsmul_eq_mul, levelBall_volume]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [a]
      ring
    _ ≤ a * (p.V : ℝ) * (3 / p.lam + ((p.H + 1 : ℕ) : ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg ha0 hV.le)
    _ ≤ p.lam * (3 / p.lam + ((p.H + 1 : ℕ) : ℝ) * ε) :=
      mul_le_mul_of_nonneg_right haV (by positivity)
    _ = _ := by
      field_simp [hlam.ne']
      <;> ring

end
end HypercubeRamsey.Lane_sol_s05_even
