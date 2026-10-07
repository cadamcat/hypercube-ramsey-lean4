import HypercubeRamsey.S12.Defs

namespace HypercubeRamsey.Lane_q_s12_peel

open HypercubeRamsey
open HypercubeRamsey.S12
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

/-- Deleting coordinates from a homogeneous positive product term costs one
inverse degree factor for each deleted label and column. -/
theorem posTerm_delete {N d u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (xs : Fin u → Fin N) (I K : Finset (Fin u))
    (hdeg : ∀ i ∈ I, 0 < deg E c π.w (xs i)) :
    posTerm E c (fun _ : Fin d => π.w) I xs ≤
      (∏ i ∈ I \ K, Real.rpow (deg E c π.w (xs i)) (-(d : ℝ))) *
        posTerm E c (fun _ : Fin d => π.w) (I ∩ K) xs := by
  classical
  let A := I \ K
  let B := I ∩ K
  let factor : ℝ := ∏ i ∈ A, (1 / deg E c π.w (xs i))
  have hcoef (i : Fin u) (hi : i ∈ I) (y : Fin N) :
      1 + acoef E c π.w (xs i) y = hit E c (xs i) y / deg E c π.w (xs i) := by
    unfold acoef
    ring
  have hratio (i : Fin u) (hi : i ∈ I) (y : Fin N) :
      0 ≤ hit E c (xs i) y / deg E c π.w (xs i) ∧
        hit E c (xs i) y / deg E c π.w (xs i) ≤ 1 / deg E c π.w (xs i) := by
    have hhit : 0 ≤ hit E c (xs i) y ∧ hit E c (xs i) y ≤ 1 := by
      unfold hit
      split_ifs <;> norm_num
    have hd := hdeg i hi
    exact ⟨div_nonneg hhit.1 hd.le, div_le_div_of_nonneg_right hhit.2 hd.le⟩
  have hdegUpper (i : Fin u) (hi : i ∈ I) : deg E c π.w (xs i) ≤ 1 := by
    unfold deg
    calc
      (∑ y, π.w y * hit E c (xs i) y) ≤ ∑ y, π.w y := by
        apply Finset.sum_le_sum
        intro y hy
        have hhit : hit E c (xs i) y ≤ 1 := by
          unfold hit
          split_ifs <;> norm_num
        calc
          π.w y * hit E c (xs i) y ≤ π.w y * 1 :=
            mul_le_mul_of_nonneg_left hhit (π.nonneg y)
          _ = π.w y := by ring
      _ = 1 := π.sum_eq_one
  have hprod (y : Fin N) :
      (∏ i ∈ I, hit E c (xs i) y / deg E c π.w (xs i)) ≤
        factor * (∏ i ∈ B, hit E c (xs i) y / deg E c π.w (xs i)) := by
    have hA : (∏ i ∈ A, hit E c (xs i) y / deg E c π.w (xs i)) ≤ factor := by
      dsimp [factor, A]
      apply Finset.prod_le_prod₀
      · intro i hi
        exact (hratio i (Finset.mem_sdiff.mp hi).1 y).1
      · intro i hi
        exact (hratio i (Finset.mem_sdiff.mp hi).1 y).2
    have hBnonneg : 0 ≤ ∏ i ∈ B, hit E c (xs i) y / deg E c π.w (xs i) := by
      apply Finset.prod_nonneg
      intro i hi
      exact (hratio i (Finset.mem_inter.mp hi).1 y).1
    calc
      (∏ i ∈ I, hit E c (xs i) y / deg E c π.w (xs i)) =
          (∏ i ∈ A, hit E c (xs i) y / deg E c π.w (xs i)) *
            ∏ i ∈ B, hit E c (xs i) y / deg E c π.w (xs i) := by
        rw [← Finset.sdiff_union_inter I K,
          Finset.prod_union (Finset.disjoint_sdiff_inter I K)]
      _ ≤ factor * ∏ i ∈ B, hit E c (xs i) y / deg E c π.w (xs i) :=
        mul_le_mul_of_nonneg_right hA hBnonneg
  have hcol (J : Finset (Fin u)) (hJ : J ⊆ I) :
      (∑ y, π.w y * ∏ i ∈ J, (1 + acoef E c π.w (xs i) y)) ≤
        factor * (∑ y, π.w y * ∏ i ∈ J ∩ K, (1 + acoef E c π.w (xs i) y)) := by
    calc
      (∑ y, π.w y * ∏ i ∈ J, (1 + acoef E c π.w (xs i) y)) ≤
          ∑ y, π.w y * (factor * ∏ i ∈ J ∩ K,
            hit E c (xs i) y / deg E c π.w (xs i)) := by
        apply Finset.sum_le_sum
        intro y hy
        have hcoefJ : ∀ i ∈ J,
            1 + acoef E c π.w (xs i) y = hit E c (xs i) y / deg E c π.w (xs i) :=
          fun i hi => hcoef i (hJ hi) y
        have hprodCoefJ :
            (∏ i ∈ J, (1 + acoef E c π.w (xs i) y)) =
              ∏ i ∈ J, hit E c (xs i) y / deg E c π.w (xs i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hcoefJ i hi
        rw [hprodCoefJ]
        have hprodJ :
            (∏ i ∈ J, hit E c (xs i) y / deg E c π.w (xs i)) ≤
              factor * ∏ i ∈ J ∩ K, hit E c (xs i) y / deg E c π.w (xs i) := by
          have hAsmall :
              (∏ i ∈ J \ K, hit E c (xs i) y / deg E c π.w (xs i)) ≤
                ∏ i ∈ J \ K, (1 / deg E c π.w (xs i)) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact (hratio i (hJ (Finset.mem_sdiff.mp hi).1) y).1
            · intro i hi
              exact (hratio i (hJ (Finset.mem_sdiff.mp hi).1) y).2
          have hsub : J \ K ⊆ I \ K := by
            intro i hi
            exact Finset.mem_sdiff.mpr
              ⟨hJ (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
          have hAsup :
              (∏ i ∈ J \ K, (1 / deg E c π.w (xs i))) ≤ factor := by
            dsimp [factor, A]
            apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
            · intro i hi
              exact div_nonneg (by norm_num) (hdeg i (hJ (Finset.mem_sdiff.mp hi).1)).le
            · intro i hi hni
              have hd := hdeg i (Finset.mem_sdiff.mp hi).1
              exact (le_div_iff₀ hd).2 (by simpa using hdegUpper i (Finset.mem_sdiff.mp hi).1)
          have hA :
              (∏ i ∈ J \ K, hit E c (xs i) y / deg E c π.w (xs i)) ≤ factor :=
            hAsmall.trans hAsup
          have hBnonneg : 0 ≤ ∏ i ∈ J ∩ K, hit E c (xs i) y / deg E c π.w (xs i) := by
            apply Finset.prod_nonneg
            intro i hi
            exact (hratio i (hJ (Finset.mem_inter.mp hi).1) y).1
          calc
            (∏ i ∈ J, hit E c (xs i) y / deg E c π.w (xs i)) =
                (∏ i ∈ J \ K, hit E c (xs i) y / deg E c π.w (xs i)) *
                  ∏ i ∈ J ∩ K, hit E c (xs i) y / deg E c π.w (xs i) := by
              calc
                _ = (∏ i ∈ J ∩ K, hit E c (xs i) y / deg E c π.w (xs i)) *
                    ∏ i ∈ J \ K, hit E c (xs i) y / deg E c π.w (xs i) :=
                  (Finset.prod_inter_mul_prod_sdiff J K _).symm
                _ = _ := by ring
            _ ≤ factor * ∏ i ∈ J ∩ K, hit E c (xs i) y / deg E c π.w (xs i) :=
              mul_le_mul_of_nonneg_right hA hBnonneg
        exact mul_le_mul_of_nonneg_left hprodJ (π.nonneg y)
      _ = ∑ y, factor *
          (π.w y * ∏ i ∈ J ∩ K, (1 + acoef E c π.w (xs i) y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        have hcoefB : ∀ i ∈ J ∩ K,
            1 + acoef E c π.w (xs i) y = hit E c (xs i) y / deg E c π.w (xs i) := by
          intro i hi
          exact hcoef i (hJ (Finset.mem_inter.mp hi).1) y
        have hprodCoefB :
            (∏ i ∈ J ∩ K, (1 + acoef E c π.w (xs i) y)) =
              ∏ i ∈ J ∩ K, hit E c (xs i) y / deg E c π.w (xs i) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hcoefB i hi
        rw [← hprodCoefB]
        ring
      _ = factor * (∑ y, π.w y * ∏ i ∈ J ∩ K,
            (1 + acoef E c π.w (xs i) y)) := by rw [← Finset.mul_sum]
  have hcolNonneg (J : Finset (Fin u)) (hJ : J ⊆ I) :
      0 ≤ ∑ y, π.w y * ∏ i ∈ J, (1 + acoef E c π.w (xs i) y) := by
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (π.nonneg y)
    apply Finset.prod_nonneg
    intro i hi
    rw [hcoef i (hJ hi) y]
    exact (hratio i (hJ hi) y).1
  have hdelete :
      (∏ l : Fin d, ∑ y, π.w y * ∏ i ∈ I, (1 + acoef E c π.w (xs i) y)) ≤
        factor ^ d * ∏ l : Fin d, ∑ y, π.w y *
          ∏ i ∈ B, (1 + acoef E c π.w (xs i) y) := by
    calc
      (∏ l : Fin d, ∑ y, π.w y * ∏ i ∈ I, (1 + acoef E c π.w (xs i) y)) ≤
          ∏ l : Fin d, factor * (∑ y, π.w y *
            ∏ i ∈ B, (1 + acoef E c π.w (xs i) y)) := by
        apply Finset.prod_le_prod₀
        · intro l hl
          exact hcolNonneg I (by intro i hi; exact hi)
        · intro l hl
          exact hcol I (by intro i hi; exact hi)
      _ = factor ^ d * ∏ l : Fin d, ∑ y, π.w y *
          ∏ i ∈ B, (1 + acoef E c π.w (xs i) y) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hfactorEq : factor ^ d = ∏ i ∈ A,
      Real.rpow (deg E c π.w (xs i)) (-(d : ℝ)) := by
    dsimp [factor]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    have hd := hdeg i (Finset.mem_sdiff.mp hi).1
    calc
      (1 / deg E c π.w (xs i)) ^ d = (deg E c π.w (xs i) ^ d)⁻¹ := by
        rw [one_div_pow]
        simp [div_eq_mul_inv]
      _ = Real.rpow (deg E c π.w (xs i)) (-(d : ℝ)) := by
        have hr := Real.rpow_neg hd.le (d : ℝ)
        rw [Real.rpow_natCast] at hr
        exact hr.symm
  dsimp [posTerm, A, B]
  rw [hfactorEq] at hdelete
  exact hdelete

theorem posTerm_nonneg {N d u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin d → Law N) (I : Finset (Fin u)) (xs : Fin u → Fin N) :
    0 ≤ posTerm E c (fun l => (π l).w) I xs := by
  classical
  unfold posTerm
  apply Finset.prod_nonneg
  intro l hl
  apply Finset.sum_nonneg
  intro y hy
  apply mul_nonneg ((π l).nonneg y)
  apply Finset.prod_nonneg
  intro i hi
  have hhit : 0 ≤ hit E c (xs i) y := by
    unfold hit
    split_ifs <;> norm_num
  have hdeg : 0 ≤ deg E c (π l).w (xs i) := by
    unfold deg
    apply Finset.sum_nonneg
    intro y' hy'
    exact mul_nonneg ((π l).nonneg y') (by
      unfold hit
      split_ifs <;> norm_num)
  have hcoef : 1 + acoef E c (π l).w (xs i) y =
      hit E c (xs i) y / deg E c (π l).w (xs i) := by
    unfold acoef
    ring
  rw [hcoef]
  exact div_nonneg hhit hdeg

theorem posTerm_delete_compl {N d u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (xs : Fin u → Fin N) (I K : Finset (Fin u))
    (hdeg : ∀ i, 0 < deg E c π.w (xs i))
    (hdegUpper : ∀ i, deg E c π.w (xs i) ≤ 1) :
    posTerm E c (fun _ : Fin d => π.w) I xs ≤
      (∏ i ∈ Kᶜ, Real.rpow (deg E c π.w (xs i)) (-(d : ℝ))) *
        posTerm E c (fun _ : Fin d => π.w) (I ∩ K) xs := by
  classical
  have hsmall : posTerm E c (fun _ : Fin d => π.w) I xs ≤
      (∏ i ∈ I \ K, Real.rpow (deg E c π.w (xs i)) (-(d : ℝ))) *
        posTerm E c (fun _ : Fin d => π.w) (I ∩ K) xs := by
    exact posTerm_delete (d := d) E c π xs I K (fun i hi => hdeg i)
  have hsubset : I \ K ⊆ Kᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
  have hfactor : (∏ i ∈ I \ K, Real.rpow (deg E c π.w (xs i)) (-(d : ℝ))) ≤
      ∏ i ∈ Kᶜ, Real.rpow (deg E c π.w (xs i)) (-(d : ℝ)) := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsubset
    · intro i hi
      exact Real.rpow_nonneg (hdeg i).le _
    · intro i hi hnot
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hdeg i) (hdegUpper i)
        (neg_nonpos.mpr (Nat.cast_nonneg d))
  exact le_trans hsmall
    (mul_le_mul_of_nonneg_right hfactor (posTerm_nonneg E c (fun _ : Fin d => π) (I ∩ K) xs))

/-- Interactions commute with restricting a tuple along a finite embedding. -/
theorem inter_map_embedding {N u v : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (e : Fin v ↪ Fin u) (J : Finset (Fin v))
    (xs : Fin u → Fin N) :
    inter E c π (J.map e) xs = inter E c π J (fun i => xs (e i)) := by
  classical
  unfold inter
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  rw [Finset.prod_map]

/-- Homogeneous positive product terms commute with restricting a tuple along an embedding. -/
theorem posTerm_map_embedding {N d u v : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (e : Fin v ↪ Fin u) (J : Finset (Fin v))
    (xs : Fin u → Fin N) :
    posTerm E c (fun _ : Fin d => π) (J.map e) xs =
      posTerm E c (fun _ : Fin d => π) J (fun i => xs (e i)) := by
  classical
  unfold posTerm
  apply Finset.prod_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  rw [Finset.prod_map]

/-- Every finite tuple has a largest coordinate set on which all interactions
remain moderate. -/
def ModerateOn {N u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (ξ : ℝ) (xs : Fin u → Fin N) (K : Finset (Fin u)) : Prop :=
  ∀ J : Finset (Fin u), J ⊆ K → 2 ≤ J.card → |inter E c π J xs| ≤ ξ

theorem exists_maximal_moderateOn {N u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (ξ : ℝ) (xs : Fin u → Fin N) :
    ∃ K : Finset (Fin u), ModerateOn E c π ξ xs K ∧
      ∀ K', ModerateOn E c π ξ xs K' → K'.card ≤ K.card := by
  classical
  let good : Finset (Finset (Fin u)) :=
    Finset.univ.filter (fun K => ModerateOn E c π ξ xs K)
  have hgood : good.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro J hJ hJcard
    have hJempty : J = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro i hi
      have hf : False := by simpa using hJ hi
      exact hf)
    subst J
    simp at hJcard
  obtain ⟨K, hKmem, hKmax⟩ := Finset.exists_max_image good Finset.card hgood
  refine ⟨K, (Finset.mem_filter.mp hKmem).2, ?_⟩
  intro K' hK'
  exact hKmax K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK'⟩)

theorem moderateOn_insert_not {N u : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (ξ : ℝ) (xs : Fin u → Fin N)
    (K : Finset (Fin u)) (hKmax : ∀ K', ModerateOn E c π ξ xs K' → K'.card ≤ K.card)
    (i : Fin u) (hi : i ∉ K) : ¬ ModerateOn E c π ξ xs (insert i K) := by
  intro hIns
  have hcard := Finset.card_insert_of_notMem hi
  have hle := hKmax (insert i K) hIns
  omega

end HypercubeRamsey.Lane_q_s12_peel
