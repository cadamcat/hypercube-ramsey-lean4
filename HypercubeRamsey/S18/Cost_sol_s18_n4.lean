import HypercubeRamsey.S18.Terminal_sol_s18_n4
import HypercubeRamsey.S18.Leaf_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical Filter
open scoped BigOperators

/-- The stated scope bound and touching charge already pay an inverse-dimension
comparison cost. Only the actual test forcing and its scope count remain. -/
theorem terminalTestCostEventually
    {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), S18.TerminalRiskBound D δ →
      ∀ L : S18.LeafCoupling D δ,
        (∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4) ∧
        (∀ i, (∑ j, if L.adjacent i j then
          2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2) ∧
        ∀ (domains : Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)))
          (images : Finset (Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i))
          (tapes : Finset D.geom.Cell),
          ((domains.card + images.card + tapes.card : ℕ) : ℝ) ≤
            Real.rpow (T.S.n k : ℝ)
              (10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ)) →
          (∏ i ∈ Finset.univ.filter (fun i =>
              ¬ Disjoint (L.domains i) domains ∨ ¬ Disjoint (L.images i) images ∨
                ¬ Disjoint (L.tapes i) tapes),
            (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹) ≤
            1 + (T.S.n k : ℝ)⁻¹ := by
  filter_upwards [terminalScaleEventually κ T] with k hscale
  intro PT hPT D hrisk L
  obtain ⟨hn8, hTs1, hr⟩ := hscale D
  have hn8r : 8 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn8
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have hn1 : 1 ≤ (T.S.n k : ℝ) := by linarith
  have hPr : 100 * ((κ.Ac : ℝ) + 10) ≤ (κ.P : ℝ) := by exact_mod_cast hκ.P_big.2
  have hmul := mul_le_mul_of_nonneg_right hPr (Nat.cast_nonneg D.encoding.Ts)
  have hAcTs : 0 ≤ (κ.Ac : ℝ) * D.encoding.Ts := by positivity
  have hbudget : 30 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
      (κ.P : ℝ) * D.encoding.Ts / 3 ≤ -3 := by
    push_cast
    nlinarith
  have hchargeexp : 20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
      (κ.P : ℝ) * D.encoding.Ts / 3 ≤ -1 := by
    have hs0 : 0 ≤ (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hleafexp : -((κ.P : ℝ) * D.encoding.Ts / 3) ≤ -1 := by
    have hs0 : 0 ≤ (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hinv : (T.S.n k : ℝ)⁻¹ ≤ 1 / 8 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hn8r
  have hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4 := by
    intro i
    have hp := (Lane_q_s18_n4.leafProbabilityBound D δ hrisk L i).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 hleafexp)
    rw [Real.rpow_neg_one] at hp
    linarith
  have hcharge : ∀ i, (∑ j, if L.adjacent i j then
      2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2 := by
    intro i
    have hh := (L.touching_charge i).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hchargeexp)
        (by norm_num : (0 : ℝ) ≤ 2))
    rw [Real.rpow_neg_one] at hh
    linarith
  refine ⟨hprob, hcharge, ?_⟩
  intro domains images tapes hscope
  let touched := Finset.univ.filter (fun i =>
    ¬ Disjoint (L.domains i) domains ∨ ¬ Disjoint (L.images i) images ∨ ¬ Disjoint (L.tapes i) tapes)
  let q := fun i => 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i)
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    dsimp [q]
    apply mul_nonneg (by norm_num)
    unfold FinLaw.pr
    exact Finset.sum_nonneg (fun x _ => by split_ifs <;> simp [D.encoding.permLaw.nonneg])
  have hq1 : ∀ i, q i < 1 := by
    intro i
    have hi := hprob i
    dsimp [q]
    linarith
  have hsum : (∑ i ∈ touched, q i) ≤ 2 * (T.S.n k : ℝ) ^ (-3 : ℝ) := by
    calc
      _ ≤ ((domains.card + images.card + tapes.card : ℕ) : ℝ) *
          (2 * Real.rpow (T.S.n k : ℝ)
            (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
              (κ.P : ℝ) * D.encoding.Ts / 3)) := by
        simpa [touched, q, Finset.sum_filter] using leafTestTouchingCharge D δ L domains images tapes
      _ ≤ Real.rpow (T.S.n k : ℝ)
          (10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ)) *
          (2 * Real.rpow (T.S.n k : ℝ)
            (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
              (κ.P : ℝ) * D.encoding.Ts / 3)) :=
        mul_le_mul_of_nonneg_right hscope
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = 2 * Real.rpow (T.S.n k : ℝ)
          (30 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
            (κ.P : ℝ) * D.encoding.Ts / 3) := by
        rw [mul_left_comm]
        congr 1
        have he : 10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) +
            (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
              (κ.P : ℝ) * D.encoding.Ts / 3) =
            30 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
              (κ.P : ℝ) * D.encoding.Ts / 3 := by ring
        exact (Real.rpow_add hnpos _ _).symm.trans (congrArg (Real.rpow (T.S.n k : ℝ)) he)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hbudget) (by norm_num)
  have hsmall : 2 * (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ (T.S.n k : ℝ)⁻¹ / (1 + (T.S.n k : ℝ)⁻¹) := by
    have hneg3 : (T.S.n k : ℝ) ^ (-3 : ℝ) = ((T.S.n k : ℝ) ^ (3 : ℕ))⁻¹ := by
      exact (Real.rpow_neg hnpos.le (3 : ℝ)).trans
        (congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (T.S.n k : ℝ) (3 : ℕ)))
    rw [hneg3]
    have heq : (T.S.n k : ℝ)⁻¹ / (1 + (T.S.n k : ℝ)⁻¹) = 1 / ((T.S.n k : ℝ) + 1) := by
      field_simp
    rw [heq]
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hcube := mul_le_mul_of_nonneg_right hn1 (sq_nonneg (T.S.n k : ℝ))
    nlinarith
  exact reciprocalAvoidanceProductLe touched q _ (inv_nonneg.mpr hnpos.le)
    (fun i _ => hq0 i) (fun i _ => hq1 i) (hsum.trans hsmall)

end HypercubeRamsey.Lane_sol_s18_n4
