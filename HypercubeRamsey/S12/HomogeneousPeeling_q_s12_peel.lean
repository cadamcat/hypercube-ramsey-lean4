import HypercubeRamsey.S12.Defs

namespace HypercubeRamsey.S12

open HypercubeRamsey
open Classical
open scoped BigOperators

/-- A fixed-sign family with small pair correlations cannot contain the
independent-set size used in the Section 12 Ramsey argument. -/
theorem corr_sign_independent_false {N : ℕ}
    (E : Fin N → Fin N → Prop) (c : Colour) (π : Law N) (g : Fin N → ℝ)
    (C : Finset (Fin N)) (u : ℕ) (ξ θ σ : ℝ)
    (hξ : 0 < ξ) (hθ : 0 ≤ θ)
    (hθsmall : 3 * θ < ξ ^ 2 / 4 ^ (u + 3))
    (hsize : (4 ^ (u + 3) / ξ ^ 2) < C.card)
    (hσ : σ ^ 2 = 1)
    (hgnorm : (∑ y, π.w y * g y ^ 2) ≤ (4 : ℝ) ^ u)
    (hproj : ∀ z ∈ C, ξ / 4 < σ * (∑ y, π.w y * fv E c z y * g y))
    (hpair : ∀ z ∈ C, ∀ z' ∈ C, z ≠ z' → corr E c π.w z z' ≤ 3 * θ) :
    False := by
  classical
  let m : ℝ := C.card
  have hFpos : 0 < (4 : ℝ) ^ (u + 3) := by positivity
  have hξ2pos : 0 < ξ ^ 2 := sq_pos_of_pos hξ
  have hm : 0 < m := lt_trans (div_pos hFpos hξ2pos) hsize
  have hfvSq : ∀ z y, (fv E c z y) ^ 2 = 1 := by
    intro z y
    unfold fv hit
    split_ifs <;> norm_num
  have hcorrSelf : ∀ z, corr E c π.w z z = 1 := by
    intro z
    unfold corr
    calc
      (∑ y, π.w y * fv E c z y * fv E c z y) = ∑ y, π.w y := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          π.w y * fv E c z y * fv E c z y =
              π.w y * (fv E c z y) ^ 2 := by ring
          _ = π.w y := by rw [hfvSq z y]; ring
      _ = 1 := π.sum_eq_one
  have hpairInner (z z' : Fin N) :
      (∑ y, π.w y * (σ * fv E c z y) * (σ * fv E c z' y)) =
        corr E c π.w z z' := by
    calc
      (∑ y, π.w y * (σ * fv E c z y) * (σ * fv E c z' y)) =
          ∑ y, π.w y * fv E c z y * fv E c z' y := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          π.w y * (σ * fv E c z y) * (σ * fv E c z' y) =
              π.w y * (σ ^ 2 * fv E c z y * fv E c z' y) := by ring
          _ = π.w y * (1 * fv E c z y * fv E c z' y) := by rw [hσ]
          _ = _ := by ring
      _ = corr E c π.w z z' := by rfl
  let sfun (y : Fin N) := ∑ z ∈ C, σ * fv E c z y
  let a : ℝ := ∑ y, π.w y * g y * sfun y
  let f (y : Fin N) := Real.sqrt (π.w y) * g y
  let gvec (y : Fin N) := Real.sqrt (π.w y) * sfun y
  have haEq : a = ∑ z ∈ C, σ * (∑ y, π.w y * fv E c z y * g y) := by
    dsimp [a, sfun]
    calc
      (∑ y, π.w y * g y * ∑ z ∈ C, σ * fv E c z y) =
          ∑ y, ∑ z ∈ C, π.w y * g y * (σ * fv E c z y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
      _ = ∑ z ∈ C, ∑ y, π.w y * g y * (σ * fv E c z y) := by
        rw [Finset.sum_comm]
      _ = ∑ z ∈ C, σ * (∑ y, π.w y * fv E c z y * g y) := by
        apply Finset.sum_congr rfl
        intro z hz
        calc
          (∑ y, π.w y * g y * (σ * fv E c z y)) =
              ∑ y, σ * (π.w y * fv E c z y * g y) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
          _ = σ * (∑ y, π.w y * fv E c z y * g y) := by
            rw [← Finset.mul_sum]
  have hfSq : (∑ y, f y ^ 2) ≤ (4 : ℝ) ^ u := by
    calc
      (∑ y, f y ^ 2) = ∑ y, π.w y * (g y) ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [f]
        calc
          (Real.sqrt (π.w y) * g y) ^ 2 =
              (Real.sqrt (π.w y)) ^ 2 * (g y) ^ 2 := by ring
          _ = π.w y * (g y) ^ 2 := by
            rw [Real.sq_sqrt (π.nonneg y)]
      _ ≤ (4 : ℝ) ^ u := hgnorm
  let B : ℝ := ∑ y, π.w y * (sfun y) ^ 2
  have hgSq : (∑ y, gvec y ^ 2) = B := by
    dsimp [gvec, B]
    apply Finset.sum_congr rfl
    intro y hy
    calc
      (Real.sqrt (π.w y) * sfun y) ^ 2 =
          (Real.sqrt (π.w y)) ^ 2 * (sfun y) ^ 2 := by ring
      _ = π.w y * (sfun y) ^ 2 := by
        rw [Real.sq_sqrt (π.nonneg y)]
  have haCauchy : (∑ y, f y * gvec y) = a := by
    dsimp [f, gvec, a]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [sfun]
    calc
      Real.sqrt (π.w y) * g y *
          (Real.sqrt (π.w y) * ∑ z ∈ C, σ * fv E c z y) =
          (Real.sqrt (π.w y) * Real.sqrt (π.w y)) *
            (g y * ∑ z ∈ C, σ * fv E c z y) := by ring
      _ = π.w y * (g y * ∑ z ∈ C, σ * fv E c z y) := by
        calc
          (Real.sqrt (π.w y) * Real.sqrt (π.w y)) *
              (g y * ∑ z ∈ C, σ * fv E c z y) =
            (Real.sqrt (π.w y)) ^ 2 *
              (g y * ∑ z ∈ C, σ * fv E c z y) := by rw [pow_two]
          _ = _ := by rw [Real.sq_sqrt (π.nonneg y)]
      _ = π.w y * g y * ∑ z ∈ C, σ * fv E c z y := by ring
  have haSq : a ^ 2 ≤ (4 : ℝ) ^ u * B := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f gvec
    have hBnonneg : 0 ≤ B := by
      dsimp [B]
      apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg (π.nonneg y) (sq_nonneg _)
    calc
      a ^ 2 ≤ (∑ y, f y ^ 2) * (∑ y, gvec y ^ 2) := by
        simpa [haCauchy] using hc
      _ ≤ (4 : ℝ) ^ u * B := by
        rw [hgSq]
        exact mul_le_mul_of_nonneg_right hfSq hBnonneg
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by
    dsimp [m] at hm
    exact_mod_cast hm)
  have haLower : m * (ξ / 4) < a := by
    rw [haEq]
    calc
      m * (ξ / 4) = ∑ z ∈ C, ξ / 4 := by simp [m, mul_comm]
      _ < ∑ z ∈ C, σ * (∑ y, π.w y * fv E c z y * g y) := by
        apply Finset.sum_lt_sum
        · intro z hz
          exact (hproj z hz).le
        · obtain ⟨z, hz⟩ := hCnonempty
          exact ⟨z, hz, hproj z hz⟩
  have hBexpand : B =
      (∑ z ∈ C, ∑ z' ∈ C, corr E c π.w z z') := by
    dsimp [B, sfun]
    calc
      (∑ y, π.w y * (∑ z ∈ C, σ * fv E c z y) ^ 2) =
          ∑ y, ∑ z ∈ C, ∑ z' ∈ C,
            π.w y * (σ * fv E c z y) * (σ * fv E c z' y) := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          π.w y * (∑ z ∈ C, σ * fv E c z y) ^ 2 =
              π.w y * ((∑ z ∈ C, σ * fv E c z y) *
                (∑ z ∈ C, σ * fv E c z y)) := by rw [pow_two]
          _ = π.w y * (∑ z ∈ C, ∑ z' ∈ C,
              (σ * fv E c z y) * (σ * fv E c z' y)) := by
            rw [Finset.sum_mul_sum]
          _ = ∑ z ∈ C, π.w y *
              (∑ z' ∈ C, (σ * fv E c z y) * (σ * fv E c z' y)) := by
            rw [Finset.mul_sum]
          _ = ∑ z ∈ C, ∑ z' ∈ C,
              π.w y * (σ * fv E c z y) * (σ * fv E c z' y) := by
            apply Finset.sum_congr rfl
            intro z hz
            calc
              π.w y *
                  (∑ z' ∈ C, (σ * fv E c z y) * (σ * fv E c z' y)) =
                π.w y * ((σ * fv E c z y) *
                  ∑ z' ∈ C, σ * fv E c z' y) := by
                congr 1
                rw [← Finset.mul_sum]
              _ = (π.w y * (σ * fv E c z y)) *
                  ∑ z' ∈ C, σ * fv E c z' y := by ring
              _ = ∑ z' ∈ C,
                  (π.w y * (σ * fv E c z y)) * (σ * fv E c z' y) := by
                rw [Finset.mul_sum]
              _ = _ := by
                apply Finset.sum_congr rfl
                intro z' hz'
                ring
      _ = ∑ z ∈ C, ∑ z' ∈ C, ∑ y,
            π.w y * (σ * fv E c z y) * (σ * fv E c z' y) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.sum_comm]
      _ = ∑ z ∈ C, ∑ z' ∈ C, corr E c π.w z z' := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro z' hz'
        exact hpairInner z z'
  have hpoint : ∀ z ∈ C, ∀ z' ∈ C,
      corr E c π.w z z' ≤ 3 * θ + (if z = z' then (1 : ℝ) else 0) := by
    intro z hz z' hz'
    by_cases heq : z = z'
    · subst z'
      rw [hcorrSelf]
      simp
      linarith [hθ]
    · simp [heq]
      exact hpair z hz z' hz' heq
  have hdiag (z : Fin N) (hz : z ∈ C) :
      (∑ z' ∈ C, if z = z' then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq_of_mem C z (fun _ => (1 : ℝ)) hz]
  have hpairSum :
      (∑ z ∈ C, ∑ z' ∈ C, corr E c π.w z z') ≤ m + 3 * θ * m ^ 2 := by
    calc
      (∑ z ∈ C, ∑ z' ∈ C, corr E c π.w z z') ≤
          ∑ z ∈ C, ∑ z' ∈ C,
            (3 * θ + (if z = z' then (1 : ℝ) else 0)) := by
        apply Finset.sum_le_sum
        intro z hz
        apply Finset.sum_le_sum
        intro z' hz'
        exact hpoint z hz z' hz'
      _ = (∑ z ∈ C, ∑ z' ∈ C, 3 * θ) +
          (∑ z ∈ C, ∑ z' ∈ C, if z = z' then (1 : ℝ) else 0) := by
        simp_rw [Finset.sum_add_distrib]
      _ = 3 * θ * m ^ 2 + m := by
        have hconst : (∑ z ∈ C, ∑ z' ∈ C, 3 * θ) = 3 * θ * m ^ 2 := by
          simp [m] <;> ring
        have hdiagTotal : (∑ z ∈ C, ∑ z' ∈ C,
            if z = z' then (1 : ℝ) else 0) = m := by
          calc
            (∑ z ∈ C, ∑ z' ∈ C, if z = z' then (1 : ℝ) else 0) =
                ∑ z ∈ C, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hdiag z hz
            _ = m := by simp [m]
        rw [hconst, hdiagTotal]
      _ = m + 3 * θ * m ^ 2 := by ring
  have hBupper : B ≤ m + 3 * θ * m ^ 2 := by
    rw [hBexpand]
    exact hpairSum
  have haSqUpper : a ^ 2 ≤ (4 : ℝ) ^ u * (m + 3 * θ * m ^ 2) :=
    le_trans haSq (mul_le_mul_of_nonneg_left hBupper (by positivity))
  have hsqStrict : (m * (ξ / 4)) ^ 2 < a ^ 2 := by
    have haNonneg : 0 ≤ a := le_trans (by positivity) haLower.le
    exact (sq_lt_sq₀ (by positivity) haNonneg).2 haLower
  have hdiv : (ξ / 4) ^ 2 < (4 : ℝ) ^ u / m + 3 * (4 : ℝ) ^ u * θ := by
    have hpoly : (m * (ξ / 4)) ^ 2 < (4 : ℝ) ^ u * (m + 3 * θ * m ^ 2) :=
      lt_of_lt_of_le hsqStrict haSqUpper
    have hm2 : 0 < m ^ 2 := pow_pos hm 2
    have hmne : m ≠ 0 := ne_of_gt hm
    have hleft : (m * (ξ / 4)) ^ 2 / m ^ 2 = (ξ / 4) ^ 2 := by
      field_simp [hmne] <;> ring
    have hright : ((4 : ℝ) ^ u * (m + 3 * θ * m ^ 2)) / m ^ 2 =
        (4 : ℝ) ^ u / m + 3 * (4 : ℝ) ^ u * θ := by
      field_simp [hmne] <;> ring
    have hdiv := div_lt_div_of_pos_right hpoly hm2
    rw [hleft, hright] at hdiv
    exact hdiv
  have hFpos : 0 < (4 : ℝ) ^ (u + 3) := by positivity
  have hξ2pos : 0 < ξ ^ 2 := sq_pos_of_pos hξ
  have hApos : 0 < (4 : ℝ) ^ (u + 3) / ξ ^ 2 := div_pos hFpos hξ2pos
  have hinv : 1 / m < ξ ^ 2 / (4 : ℝ) ^ (u + 3) := by
    calc
      1 / m < 1 / ((4 : ℝ) ^ (u + 3) / ξ ^ 2) :=
        one_div_lt_one_div_of_lt hApos hsize
      _ = ξ ^ 2 / (4 : ℝ) ^ (u + 3) := by field_simp [ne_of_gt hξ2pos, ne_of_gt hFpos]
  have hsmall : (4 : ℝ) ^ u / m + 3 * (4 : ℝ) ^ u * θ < (ξ / 4) ^ 2 := by
    have hKpos : 0 < (4 : ℝ) ^ u := by positivity
    have hFbound : 32 * (4 : ℝ) ^ u ≤ (4 : ℝ) ^ (u + 3) := by
      rw [pow_add]
      have hp : 0 ≤ (4 : ℝ) ^ u := by positivity
      nlinarith
    have hlt : (4 : ℝ) ^ u / m + 3 * (4 : ℝ) ^ u * θ <
        2 * (4 : ℝ) ^ u * ξ ^ 2 / (4 : ℝ) ^ (u + 3) := by
      calc
        (4 : ℝ) ^ u / m + 3 * (4 : ℝ) ^ u * θ =
            (4 : ℝ) ^ u * (1 / m) + (4 : ℝ) ^ u * (3 * θ) := by ring
        _ < (4 : ℝ) ^ u * (ξ ^ 2 / (4 : ℝ) ^ (u + 3)) +
            (4 : ℝ) ^ u * (ξ ^ 2 / (4 : ℝ) ^ (u + 3)) :=
          add_lt_add (mul_lt_mul_of_pos_left hinv hKpos)
            (mul_lt_mul_of_pos_left hθsmall hKpos)
        _ = 2 * (4 : ℝ) ^ u * ξ ^ 2 / (4 : ℝ) ^ (u + 3) := by ring
    have hsmall' : 2 * (4 : ℝ) ^ u * ξ ^ 2 / (4 : ℝ) ^ (u + 3) ≤ ξ ^ 2 / 16 := by
      rw [div_le_iff₀ hFpos]
      have hp := mul_le_mul_of_nonneg_right hFbound hξ2pos.le
      nlinarith
    have hquarter : ξ ^ 2 / 16 = (ξ / 4) ^ 2 := by ring
    calc
      (4 : ℝ) ^ u / m + 3 * (4 : ℝ) ^ u * θ <
          2 * (4 : ℝ) ^ u * ξ ^ 2 / (4 : ℝ) ^ (u + 3) := hlt
      _ ≤ ξ ^ 2 / 16 := hsmall'
      _ = (ξ / 4) ^ 2 := hquarter
  exact (not_lt_of_ge hsmall.le hdiv)

end HypercubeRamsey.S12
