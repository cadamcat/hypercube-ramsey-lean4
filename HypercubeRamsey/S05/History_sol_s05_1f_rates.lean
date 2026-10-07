import HypercubeRamsey.S05.History_sol_s05_1f_constants

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
variable {γ K' χ : ℝ}

/-- Positive total rates are defined even on tuples that are not Params5. -/
def pathDelta (x : Pre15) : ℝ := if 0 < x.1.2.2.2.1 then x.1.2.2.2.1 else 1

theorem pathDelta_pos (x : Pre15) : 0 < pathDelta x := by
  unfold pathDelta
  split_ifs with h
  · exact h
  · norm_num

def pathEta (x : Pre15) : ℝ := pathDelta x / 100

def pathL0 (x : Pre15) : ℝ := 100 * (|x.1.1 3| + pathDelta x + 1) / pathDelta x

def lowRate (x : Pre15) : ℝ := pathDelta x / 2

def highRate (x : Pre15) : ℝ := min (pathDelta x / 32)
  (min ((pathEta x) ^ 2 / 64) ((pathDelta x) ^ 2 / (64 * (pathL0 x) ^ 2)))

theorem pathL0_pos (x : Pre15) : 0 < pathL0 x := by
  unfold pathL0
  exact div_pos (mul_pos (by norm_num) (by have := pathDelta_pos x; have := abs_nonneg (x.1.1 3); linarith))
    (pathDelta_pos x)

theorem rates_pos (x : Pre15) : 0 < lowRate x ∧ 0 < highRate x := by
  have hd := pathDelta_pos x
  have hη : 0 < pathEta x := div_pos hd (by norm_num)
  have hL := pathL0_pos x
  refine ⟨div_pos hd (by norm_num), lt_min (div_pos hd (by norm_num)) ?_⟩
  exact lt_min (div_pos (sq_pos_of_pos hη) (by norm_num))
    (div_pos (sq_pos_of_pos hd) (mul_pos (by norm_num) (sq_pos_of_pos hL)))

theorem pathDelta_params (p : Params5 γ K' χ) : pathDelta p.pre1 = p.delta := by
  simp [pathDelta, Params5.pre1, Params5.pre0, p.hdelta.1]

theorem pathL0_params (p : Params5 γ K' χ) : pathL0 p.pre1 =
    100 * (|p.a 3| + p.delta + 1) / p.delta := by
  unfold pathL0
  rw [pathDelta_params]
  rfl

/-- A request for the density cap only reads constants fixed before K_D. -/
def atomCoefficientBeforeD (x : Pre35) : ℝ :=
  x.1.1.2.1 * (6 * x.1.2 + x.1.1.1.2.2.2.2.2.2.2) +
    x.1.1.1.1 2 * (1 + 6 * x.2 + 5 * x.1.2 + x.1.1.1.2.2.2.2.2.2.2) +
      x.1.1.1.2.2.2.1

def highRequest : ParamReq5 where
  Kcap _ := 0
  Kpp _ := 0
  Kh _ := 0
  K1 _ := 0
  K2 _ := 0
  KD x := 4 * (|atomCoefficientBeforeD x| + 1) / pathEta x.1.1
  Ks x := 16 * (((2 * highTypeBudget : ℕ) + 6) : ℝ) *
      (Real.log ((3 + (pathDelta x.1.1.1 / 100)⁻¹) * (((2 * highTypeBudget : ℕ) + 6) : ℝ)) + 2) /
      highRate x.1.1.1
  KB _ := 0
  alpha _ := 1 / 50
  alpha_pos _ := by norm_num

theorem atomCoefficientBeforeD_params (p : Params5 γ K' χ) :
    atomCoefficientBeforeD p.pre3 = highAtomCoefficient p := by rfl

/-- The selected clipping and normalization constants fit in the a₃→a₄ gap. -/
theorem high_cost_budget (p : Params5 γ K' χ) (k : ℝ) (hk : 1 / p.delta ≤ k) :
    (1 + p.delta / 100) *
      (((p.a 3 + p.delta) * k) / (1 - p.delta / 50) +
        Real.log (1 / (1 - p.delta / 50))) ≤ p.a 4 * k := by
  have hlog2 : Real.log 2 < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at hh
    exact hh
  have h3 : 0 < p.a 3 := by
    have hh := p.ha_order (0 : Fin 9) (3 : Fin 9) (by decide)
    rw [p.ha0] at hh; linarith
  have h3lt : p.a 3 < 1 := by
    have hh := p.ha_order (3 : Fin 9) (8 : Fin 9) (by decide)
    linarith [p.hgap.1, p.hgap.2.1, p.hgap.2.2]
  have hδ : p.delta < 1 / 100 := by
    have hh := p.hdelta_a (0 : Fin 9) (3 : Fin 9) (by decide)
    rw [p.ha0] at hh; linarith
  have hden : 0 < 1 - p.delta / 50 := by linarith [p.hdelta.1]
  have hlog := Real.log_le_sub_one_of_pos (x := 1 / (1 - p.delta / 50))
    (div_pos (by norm_num) hden)
  have hgap := p.hdelta_a (3 : Fin 9) (4 : Fin 9) (by decide)
  have hkpos : 0 < k := (div_pos (by norm_num) p.hdelta.1).trans_le hk
  have hkδ : 1 ≤ p.delta * k := by
    have hh := (div_le_iff₀ p.hdelta.1).mp hk
    nlinarith
  have hfactor : (1 + p.delta / 100) * (p.a 3 + p.delta) /
      (1 - p.delta / 50) ≤ p.a 3 + 2 * p.delta := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [p.hdelta.1]
  have hnorm : (1 + p.delta / 100) * Real.log (1 / (1 - p.delta / 50)) ≤ p.delta := by
    have hlog' : Real.log (1 / (1 - p.delta / 50)) ≤ p.delta / (50 * (1 - p.delta / 50)) := by
      apply hlog.trans_eq
      have hdiff : (50 : ℝ) - p.delta ≠ 0 := by linarith
      field_simp [hden.ne', hdiff]
      ring
    have hh := mul_le_mul_of_nonneg_left hlog' (show 0 ≤ 1 + p.delta / 100 by linarith [p.hdelta.1])
    apply hh.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 50) hden)).mpr
    nlinarith [p.hdelta.1]
  have hcost := mul_le_mul_of_nonneg_right hfactor hkpos.le
  have hδk : p.delta ≤ p.delta * k := by
    have hkle : 1 ≤ k := by nlinarith
    exact le_mul_of_one_le_right p.hdelta.1.le hkle
  calc
    _ = (1 + p.delta / 100) * (p.a 3 + p.delta) / (1 - p.delta / 50) * k +
        (1 + p.delta / 100) * Real.log (1 / (1 - p.delta / 50)) := by ring
    _ ≤ (p.a 3 + 2 * p.delta) * k + p.delta := add_le_add hcost hnorm
    _ ≤ (p.a 3 + 3 * p.delta) * k := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [p.hdelta.1] : p.a 3 + 3 * p.delta ≤ p.a 4) hkpos.le


/-- Absorb the negative-log, two Azuma and finite-grid terms into a fixed rate. -/
theorem high_finite_tail_absorption (s k D δ η L0 c grid r : ℝ)
    (hs : 0 < s) (hk : 0 < k) (hD : 0 < D) (hδ : 0 < δ) (hη : 0 < η) (hL : 0 < L0)
    (hc : 0 < c) (hc3 : c ≤ 3)
    (hcCost : c ≤ δ ^ 2 / (8 * L0 ^ 2)) (hcDensity : c ≤ η ^ 2 / 8)
    (hg : 0 ≤ grid) (hr : 0 ≤ r)
    (hgrid : grid * (r + 1) ≤ Real.exp (c * s / 2))
    (habsorb : 4 * Real.log 3 ≤ c * s) :
    Real.exp (s * Real.log 2 - 8 * s / 2) +
      Real.exp (-2 * ((η * D / 2) * s) ^ 2 / (s * (2 * D) ^ 2)) +
      grid * (r * Real.exp (s * Real.log 2 - 8 * s / 2) +
        Real.exp (-2 * ((δ * k / 2) * s) ^ 2 / (s * (2 * (L0 * k)) ^ 2))) ≤
          Real.exp (-(c * s / 4)) := by
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)).trans_eq (by norm_num)
  have hn : Real.exp (s * Real.log 2 - 8 * s / 2) ≤ Real.exp (-(c * s)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcostEq : -2 * ((δ * k / 2) * s) ^ 2 / (s * (2 * (L0 * k)) ^ 2) =
      -(δ ^ 2 / (8 * L0 ^ 2) * s) := by field_simp [hs.ne', hk.ne', hL.ne']; ring
  have hdenEq : -2 * ((η * D / 2) * s) ^ 2 / (s * (2 * D) ^ 2) = -(η ^ 2 / 8 * s) := by
    field_simp [hs.ne', hD.ne']; ring
  have hcost : Real.exp (-2 * ((δ * k / 2) * s) ^ 2 / (s * (2 * (L0 * k)) ^ 2)) ≤
      Real.exp (-(c * s)) := by
    rw [hcostEq]
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hcCost hs.le)
  have hden : Real.exp (-2 * ((η * D / 2) * s) ^ 2 / (s * (2 * D) ^ 2)) ≤
      Real.exp (-(c * s)) := by
    rw [hdenEq]
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hcDensity hs.le)
  have hgridTail : grid * (r * Real.exp (-(c * s)) + Real.exp (-(c * s))) ≤
      Real.exp (-(c * s / 2)) := by
    calc
      _ = grid * (r + 1) * Real.exp (-(c * s)) := by ring
      _ ≤ Real.exp (c * s / 2) * Real.exp (-(c * s)) :=
        mul_le_mul_of_nonneg_right hgrid (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsmaller : Real.exp (-(c * s)) ≤ Real.exp (-(c * s / 2)) :=
    Real.exp_le_exp.mpr (by have hh := mul_pos hc hs; linarith)
  calc
    _ ≤ Real.exp (-(c * s)) + Real.exp (-(c * s)) +
        grid * (r * Real.exp (-(c * s)) + Real.exp (-(c * s))) :=
      add_le_add (add_le_add hn hden) (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hn hr) hcost) hg)
    _ ≤ 3 * Real.exp (-(c * s / 2)) := by nlinarith [hgridTail, hsmaller]
    _ = Real.exp (Real.log 3 - c * s / 2) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end
end HypercubeRamsey.Lane_sol_s05_1f
