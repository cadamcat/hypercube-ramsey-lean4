import HypercubeRamsey.Framework.Law

/-!
# L7.1b: cell filters and deletion comparisons
-/

namespace HypercubeRamsey.S07

open Classical

/-- A second-side label passes a finite list of first-side anchors in colour `G`. -/
def passesAnchors {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (L : List (Fin N)) (y : Fin N) : Prop := ∀ x ∈ L, Hits E G x y

/-- Unnormalized mass remaining after restricting to labels that hit every listed anchor. -/
noncomputable def filterMass {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) : ℝ :=
  ∑ y, if passesAnchors E G L y then ν.w y else 0

/-- The law filtered to common neighbours of a list, with zero fallback at zero mass. -/
noncomputable def filt {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (y : Fin N) : ℝ :=
  if _h : 0 < filterMass E G ν L then
    if passesAnchors E G L y then ν.w y / filterMass E G ν L else 0
  else 0

/-- L7.1b (07:70–114): a positive-mass filter is a probability supported on labels passing its list. -/
theorem filt_probability_and_support {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (hL : 0 < filterMass E G ν L) :
    (∀ y, 0 ≤ filt E G ν L y) ∧
    (∑ y, filt E G ν L y = 1) ∧
    (∀ y, filt E G ν L y ≠ 0 → passesAnchors E G L y) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro y
    simp only [filt, dif_pos hL]
    split_ifs
    · exact div_nonneg (ν.nonneg y) hL.le
    · exact le_rfl
  · have hterm (y : Fin N) :
        filt E G ν L y = (if passesAnchors E G L y then ν.w y else 0) /
          filterMass E G ν L := by
      by_cases hp : passesAnchors E G L y <;> simp [filt, hL, hp]
    calc
      (∑ y, filt E G ν L y) =
          (∑ y, if passesAnchors E G L y then ν.w y else 0) /
            filterMass E G ν L := by
        simp_rw [hterm]
        rw [← Finset.sum_div]
      _ = 1 := by
        rw [← div_self (ne_of_gt hL)]
        rfl
  · intro y hy
    by_contra hpass
    have hz : filt E G ν L y = 0 := by
      simp [filt, hL, hpass]
    exact hy hz

/-- Deleting one anchor changes the normalized filtered law by at most the inverse retained fraction. -/
theorem filt_delete_bound {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (w : Fin N) (θ : ℝ)
    (hθ : 0 < θ) (hw : w ∈ L)
    (hDel : 0 < filterMass E G ν (L.erase w))
    (hFull : 0 < filterMass E G ν L)
    (hretained : θ * filterMass E G ν (L.erase w) ≤ filterMass E G ν L) :
    ∀ y, filt E G ν L y ≤ θ⁻¹ * filt E G ν (L.erase w) y := by
  classical
  intro y
  by_cases hpass : passesAnchors E G L y
  · have hpassDel : passesAnchors E G (L.erase w) y := by
      intro x hx
      exact hpass x (List.mem_of_mem_erase hx)
    have hleft : filt E G ν L y = ν.w y / filterMass E G ν L := by
      simp [filt, hFull, hpass]
    have hright : filt E G ν (L.erase w) y =
        ν.w y / filterMass E G ν (L.erase w) := by
      simp [filt, hDel, hpassDel]
    have hθdel : 0 < θ * filterMass E G ν (L.erase w) :=
      mul_pos hθ hDel
    have hmul := mul_le_mul_of_nonneg_left hretained (ν.nonneg y)
    calc
      filt E G ν L y = ν.w y / filterMass E G ν L := hleft
      _ ≤ ν.w y / (θ * filterMass E G ν (L.erase w)) :=
        (div_le_div_iff₀ hFull hθdel).2 (by nlinarith)
      _ = θ⁻¹ * (ν.w y / filterMass E G ν (L.erase w)) := by
        field_simp [ne_of_gt hθ, ne_of_gt hDel]
      _ = θ⁻¹ * filt E G ν (L.erase w) y := by rw [hright]
  · have hleft : filt E G ν L y = 0 := by simp [filt, hFull, hpass]
    have hnonneg : 0 ≤ filt E G ν (L.erase w) y :=
      (filt_probability_and_support E G ν (L.erase w) hDel).1 y
    rw [hleft]
    exact mul_nonneg (inv_nonneg.mpr hθ.le) hnonneg

/-- L7.1b's cap consequence for a valid cell row; `L` is the ordered cross-and-own anchor list. -/
theorem cell_row_cap_of_retention {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (ν : Law N) (L : List (Fin N)) (n s : ℕ) (d c : ℝ)
    (hn : 2 ≤ n) (hN : 0 < N)
    (hraw : ∀ y, ν.w y ≤ Real.exp ((n : ℝ) ^ (d / 2)) / N)
    (hretained : (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(2 * c * (s : ℝ))) ≤
      filterMass E G ν L) :
    ∀ y, filt E G ν L y ≤
      Real.exp ((n : ℝ) ^ (d / 2) + 2 * c * (s : ℝ) * Real.log (n : ℝ) + 1) / N := by
  classical
  let t : ℝ := 2 * c * (s : ℝ)
  let θ : ℝ := (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-t)
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hpow2 : (n : ℝ) ^ (-2 : ℝ) ≤ (1 / 4 : ℝ) := by
    calc
      (n : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hnreal (by norm_num)
      _ = (1 / 4 : ℝ) := by
        rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
  have hfactor : (3 / 4 : ℝ) ≤ 1 - (n : ℝ) ^ (-2 : ℝ) := by linarith
  have hfactor_pos : 0 < 1 - (n : ℝ) ^ (-2 : ℝ) := by linarith
  have hpow_pos : 0 < (n : ℝ) ^ (-t) := Real.rpow_pos_of_pos hnpos _
  have hθ_pos : 0 < θ := mul_pos hfactor_pos hpow_pos
  have hretained' : θ ≤ filterMass E G ν L := by simpa [θ, t] using hretained
  have hmass_pos : 0 < filterMass E G ν L := lt_of_lt_of_le hθ_pos hretained'
  have hpow_inv : ((n : ℝ) ^ (-t))⁻¹ = Real.exp (t * Real.log (n : ℝ)) := by
    rw [Real.rpow_def_of_pos hnpos]
    rw [← Real.exp_neg]
    congr 1
    ring
  have hfactor_inv : (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ ≤ (4 / 3 : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 4) hfactor
    calc
      (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ ≤ (3 / 4 : ℝ)⁻¹ := by
        simpa only [one_div] using h
      _ = (4 / 3 : ℝ) := by norm_num
  have hfactor_exp : (4 / 3 : ℝ) ≤ Real.exp 1 := by
    have htwo : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    linarith
  have hθ_inv : θ⁻¹ ≤ Real.exp (t * Real.log (n : ℝ) + 1) := by
    have hθinv_eq : θ⁻¹ =
        (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ * ((n : ℝ) ^ (-t))⁻¹ := by
      simp [θ]
      exact mul_comm _ _
    rw [hθinv_eq, hpow_inv]
    calc
      (1 - (n : ℝ) ^ (-2 : ℝ))⁻¹ * Real.exp (t * Real.log (n : ℝ)) ≤
          Real.exp 1 * Real.exp (t * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_right (hfactor_inv.trans hfactor_exp) (Real.exp_nonneg _)
      _ = Real.exp (t * Real.log (n : ℝ) + 1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hmass_nonneg : 0 ≤ filterMass E G ν L := hmass_pos.le
  intro y
  by_cases hpass : passesAnchors E G L y
  · have hleft : filt E G ν L y = ν.w y / filterMass E G ν L := by
      simp [filt, hmass_pos, hpass]
    have hcross : ν.w y * θ ≤
        (Real.exp ((n : ℝ) ^ (d / 2)) / N) * filterMass E G ν L := by
      calc
        ν.w y * θ ≤ ν.w y * filterMass E G ν L :=
          mul_le_mul_of_nonneg_left hretained' (ν.nonneg y)
        _ ≤ (Real.exp ((n : ℝ) ^ (d / 2)) / N) * filterMass E G ν L :=
          mul_le_mul_of_nonneg_right (hraw y) hmass_nonneg
    have hratio : ν.w y / filterMass E G ν L ≤
        (Real.exp ((n : ℝ) ^ (d / 2)) / N) / θ :=
      (div_le_div_iff₀ hmass_pos hθ_pos).2 hcross
    calc
      filt E G ν L y = ν.w y / filterMass E G ν L := hleft
      _ ≤ (Real.exp ((n : ℝ) ^ (d / 2)) / N) / θ := hratio
      _ = (Real.exp ((n : ℝ) ^ (d / 2)) / N) * θ⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (Real.exp ((n : ℝ) ^ (d / 2)) / N) *
          Real.exp (t * Real.log (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hθ_inv (by positivity)
      _ = Real.exp ((n : ℝ) ^ (d / 2) + 2 * c * (s : ℝ) *
          Real.log (n : ℝ) + 1) / N := by
        rw [div_mul_eq_mul_div, ← Real.exp_add]
        congr 1
        simp [t]
        ring
  · have hnonneg : 0 ≤ filt E G ν L y :=
      (filt_probability_and_support E G ν L hmass_pos).1 y
    have hupper : 0 ≤ Real.exp ((n : ℝ) ^ (d / 2) +
        2 * c * (s : ℝ) * Real.log (n : ℝ) + 1) / N := by positivity
    have hzero : filt E G ν L y = 0 := by simp [filt, hmass_pos, hpass]
    rw [hzero]
    exact hupper

end HypercubeRamsey.S07
