import HypercubeRamsey.S05.History_sol_s05_1f_budgets

namespace HypercubeRamsey.Lane_sol_s05_1f
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Averaging the coordinate laws gives the actual index–label law. -/
def coordinatePair {s : ℕ} (P : Fin s → Law N) (hs : 0 < s) : FinProb (Fin s × Fin N) where
  w := fun hy => (P hy.1).w hy.2 / (s : ℝ)
  nonneg hy := div_nonneg ((P hy.1).nonneg _) (Nat.cast_nonneg _)
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_div, FinProb.sum_eq_one]
    simp [hs.ne']

theorem coordinatePair_expect {s : ℕ} (P : Fin s → Law N) (hs : 0 < s)
    (f : Fin s × Fin N → ℝ) :
    (coordinatePair P hs).expect f = (∑ h, (P h).expect (fun y => f (h, y))) / (s : ℝ) := by
  simp only [FinProb.expect, coordinatePair, Fintype.sum_prod_type]
  simp_rw [div_mul_eq_mul_div]
  simp_rw [← Finset.sum_div]

theorem coordinatePair_support {s : ℕ} (P : Fin s → Law N) (hs : 0 < s)
    (h : Fin s) (y : Fin N) :
    (coordinatePair P hs).w (h, y) ≠ 0 ↔ (P h).w y ≠ 0 := by
  change (P h).w y / (s : ℝ) ≠ 0 ↔ _
  simp [hs.ne']

/-- Any smoothed deletion law has positive weight at every label. -/
theorem smooth_weight_pos (Q : Law N) (y : Fin N) : 0 < (X.smooth Q).w y := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos X.y₀
  exact div_pos (add_pos_of_nonneg_of_pos (Q.nonneg y) (inv_pos.mpr hN)) (by norm_num)

/-- Every convex price is dominated by one point of a finite integer box grid. -/
theorem finite_box_price_rounding {I : Type*} [Fintype I] [Nonempty I]
    (P : FinProb I) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : I → Fin (⌈(1 + ε⁻¹) * Fintype.card I⌉₊ + 1),
      (0 < ∑ i, (a i).val) ∧
      ∀ i, P.w i ≤ (1 + ε) * ((a i).val : ℝ) / (∑ j, (a j).val : ℕ) := by
  obtain ⟨b, hb, hsum, hdom⟩ := Lane_sol_s05_hist1b.finite_price_rounding P ε hε
  have hsumNat : (∑ i, b i) ≤ ⌈(1 + ε⁻¹) * Fintype.card I⌉₊ := by
    exact_mod_cast hsum.trans (Nat.le_ceil _)
  have hbi (i) : b i < ⌈(1 + ε⁻¹) * Fintype.card I⌉₊ + 1 := by
    have hh := Finset.single_le_sum (f := b) (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
    omega
  refine ⟨fun i => ⟨b i, hbi i⟩, hb, ?_⟩
  intro i
  simpa only [mul_div_assoc] using hdom i

/-- The finite clipped-grid tests imply every original price direction, with
one normalization loss and the coordinatewise grid multiplier. -/
theorem finite_grid_price_law {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]
    (P : FinProb Ω) (Q : I → FinProb Ω) (D L B η β ε A : ℝ)
    (hQ : ∀ i ω, 0 < (Q i).w ω)
    (hD : 0 ≤ D) (hL : 0 < L) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hβ : η + B / L ≤ β) (hβ1 : β < 1) (hε : 0 < ε)
    (hcost : (1 + ε) * (B / (1 - β) + Real.log (1 / (1 - β))) ≤ A)
    (hdensity : P.pr (fun ω => D < P.w ω) ≤ η)
    (hgrid : ∀ a : I → Fin (⌈(1 + ε⁻¹) * Fintype.card I⌉₊ + 1),
      0 < ∑ i, (a i).val →
      P.expect (fun ω => min L (∑ i,
        ((a i).val : ℝ) / (∑ j, (a j).val : ℕ) *
          max 0 (Real.log (P.w ω / (Q i).w ω)))) ≤ B) :
    ∀ price : I → ℝ, (∀ i, 0 ≤ price i) → (∑ i, price i = 1) →
      ∃ R : FinProb Ω,
        (∀ ω, R.w ω ≤ D / (1 - β)) ∧
        (∀ ω, R.w ω ≠ 0 → P.w ω ≠ 0) ∧
        (∑ i, price i * R.expect (fun ω => max 0 (Real.log (R.w ω / (Q i).w ω)))) ≤ A := by
  intro price hp hs
  have hne : Nonempty I := by
    by_contra h
    haveI : IsEmpty I := ⟨fun i => h ⟨i⟩⟩
    simp at hs
  letI := hne
  let priceLaw : FinProb I := ⟨price, hp, hs⟩
  obtain ⟨a, ha, hdom⟩ := finite_box_price_rounding priceLaw ε hε
  let grid := fun i : I => ((a i).val : ℝ) / (∑ j, (a j).val : ℕ)
  have hgridNonneg (i) : 0 ≤ grid i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hgridSum : ∑ i, grid i = 1 := by
    dsimp [grid]
    rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_self (by exact_mod_cast ha.ne')
  obtain ⟨R, hcap, hsupp, hbound⟩ := finite_clipped_price_law P Q grid D L B η β
    hgridNonneg hgridSum hQ hD hL hB hη hβ hβ1 hdensity (hgrid a ha)
  refine ⟨R, hcap, hsupp, ?_⟩
  calc
    _ ≤ ∑ i, (1 + ε) * grid i *
        R.expect (fun ω => max 0 (Real.log (R.w ω / (Q i).w ω))) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right (by simpa [priceLaw, grid, mul_div_assoc] using hdom i)
      exact Finset.sum_nonneg fun ω _ => mul_nonneg (R.nonneg ω) (le_max_left _ _)
    _ = (1 + ε) * (∑ i, grid i * R.expect
        (fun ω => max 0 (Real.log (R.w ω / (Q i).w ω)))) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ (1 + ε) * (B / (1 - β) + Real.log (1 / (1 - β))) :=
      mul_le_mul_of_nonneg_left hbound (by linarith)
    _ ≤ A := hcost

/-- The density-good coordinate-pair law supplies HighCapped even when
there are no deletion references. -/
theorem high_capped_of_density (H : X.KeyHist) (r : X.AbsRecord)
    (a : X.ArraysOn (Fin (X.p.T n))) (hs : 0 < colLen5 (X.p.s n) r.1)
    (hgood : 1 / 2 ≤ (coordinatePair (X.highSource H r a) hs).pr (fun hy =>
      (coordinatePair (X.highSource H r a) hs).w hy ≤
        Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N))) :
    X.HighCapped H r a := by
  obtain ⟨R, hcap, hsupp⟩ := Lane_sol_s05_hist1b.finite_capped_support
    (coordinatePair (X.highSource H r a) hs) (⟨0, hs⟩, X.y₀)
    (Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N))
    (div_nonneg (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) hgood
  refine ⟨R, ?_, ?_⟩
  · intro h y; simpa only [mul_div_assoc] using hcap (h, y)
  · intro h y hR; exact (coordinatePair_support _ hs h y).mp (hsupp (h, y) hR)


/-- The concrete Step 3 high-row feasibility follows from a density budget and
clipped predictable tests on the finite box grid. -/
theorem high_price_feasible_of_grid (H : X.KeyHist) (r : X.AbsRecord)
    (hr : X.RecOccurs r) (hh : r.1.isRight) (a : X.ArraysOn (Fin (X.p.T n)))
    (hs : 0 < colLen5 (X.p.s n) r.1) (L B η β ε : ℝ)
    (hL : 0 < L) (hB : 0 ≤ B) (hη : 0 ≤ η) (hβ : η + B / L ≤ β)
    (hβhalf : β ≤ 1 / 2) (hε : 0 < ε)
    (hcost : (1 + ε) * (B / (1 - β) + Real.log (1 / (1 - β))) ≤
      X.p.a 4 * (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ))
    (hdensity : (coordinatePair (X.highSource H r a) hs).pr (fun hy =>
      Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N) <
        (coordinatePair (X.highSource H r a) hs).w hy) ≤ η)
    (hgrid : ∀ b : {c // c ∈ X.refsOn H r a} →
      Fin (⌈(1 + ε⁻¹) * Fintype.card {c // c ∈ X.refsOn H r a}⌉₊ + 1),
      0 < ∑ c, (b c).val →
      (coordinatePair (X.highSource H r a) hs).expect (fun hy => min L (∑ c,
        ((b c).val : ℝ) / (∑ d, (b d).val : ℕ) *
          max 0 (Real.log ((X.highSource H r a hy.1).w hy.2 /
            (X.highDeleted H r a c.1 hy.1).w hy.2)))) ≤ B) :
    X.HighPriceFeasible H r a := by
  let P := coordinatePair (X.highSource H r a) hs
  let Q := fun c : {c // c ∈ X.refsOn H r a} => coordinatePair (X.highDeleted H r a c.1) hs
  let D := Real.exp (X.p.DH n) / ((colLen5 (X.p.s n) r.1 : ℝ) * N)
  have hsR : (0 : ℝ) < colLen5 (X.p.s n) r.1 := by exact_mod_cast hs
  have hQ (c : {c // c ∈ X.refsOn H r a}) (hy) : 0 < (Q c).w hy := by
    exact div_pos (smooth_weight_pos X _ hy.2) hsR
  have hD : 0 ≤ D := div_nonneg (Real.exp_pos _).le
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hratio (c : {c // c ∈ X.refsOn H r a}) (hy : Fin (colLen5 (X.p.s n) r.1) × Fin N) :
      P.w hy / (Q c).w hy =
        (X.highSource H r a hy.1).w hy.2 / (X.highDeleted H r a c.1 hy.1).w hy.2 := by
    change (_ / (colLen5 (X.p.s n) r.1 : ℝ)) /
      (_ / (colLen5 (X.p.s n) r.1 : ℝ)) = _
    rw [div_div_div_cancel_right₀ hsR.ne']
  have hgrid' := hgrid
  simp_rw [← hratio] at hgrid'
  intro price hp hsum
  obtain ⟨R, hcap, hsupp, hbound⟩ := finite_grid_price_law P Q D L B η β ε
    (X.p.a 4 * (X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) : ℕ))
    hQ hD hL hB hη hβ (by linarith) hε hcost hdensity hgrid' price hp hsum
  refine ⟨R, ?_, ?_, ?_⟩
  · intro h y
    apply (hcap (h, y)).trans
    calc
      D / (1 - β) ≤ D / (1 / 2) := div_le_div_of_nonneg_left hD (by norm_num) (by linarith)
      _ = _ := by dsimp [D]; ring
  · intro h y hR
    exact (coordinatePair_support _ hs h y).mp (hsupp (h, y) hR)
  · have hlen (c : {c // c ∈ X.refsOn H r a}) :
        X.refLen c.1.2.1 c.1.2.2 = X.p.usedBlocks n * (X.p.q0 * X.p.uStarSeg n) :=
      highRefs_length X r hr hh c.1 (refsOn_high_subset X H r hr hh a c.2)
    simp only [highDeletionCost5, FinProb.expect, Fintype.sum_prod_type, Q, coordinatePair] at hbound
    simp_rw [hlen]
    rw [← Finset.sum_mul, hsum, one_mul]
    exact hbound

end
end HypercubeRamsey.Lane_sol_s05_1f
