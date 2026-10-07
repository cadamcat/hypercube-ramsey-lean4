import HypercubeRamsey.S03.Height.Split_opus_height_sol_hs_ovl

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_hs_ovl

open OAI.HypercubeRamsey Lane_p_height_main

theorem geometry_linear {p : HDParams} (x y : HDState p) (R K : ℕ) (L : ℝ)
    (hD : 1 ≤ p.D) (hR : 1 ≤ R) (hr : 0 < p.r) (hL : 1 ≤ L)
    (hK : 200 * (12 + 6 * (p.D : ℝ)) * L ≤ K)
    (hsep : K * R ≤ hdScaleDistance p.D x y)
    (hRD : 3 * (p.r + (2 * p.D * R + p.D)) ≤ p.d)
    (huL : (p.d : ℝ) / p.r ≤ Real.exp L)
    (hαL : ((p.r + (2 * p.D * R + p.D) : ℕ) : ℝ) /
      ((p.d - (p.r + (2 * p.D * R + p.D)) + 1 : ℕ) : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)))
    (hBL : ((p.r + (2 * p.D * R + p.D) + 1 : ℕ) : ℝ) ≤ Real.exp ((R : ℝ) * L)) :
    ((hdChildCenterDomain x (2 * R) ∩ hdChildCenterDomain y (2 * R)).card : ℝ) ≤
      (p.V : ℝ) * Real.exp (-4 * (R : ℝ)) := by
  have hKr : (40 : ℝ) ≤ K := by
    have hd : (1 : ℝ) ≤ p.D := by exact_mod_cast hD
    nlinarith
  have hK40 : 40 ≤ K := by exact_mod_cast hKr
  have hgap : 2 * (2 * R) < K * R := by nlinarith
  have hT : p.D * (2 * R) + p.D = 2 * p.D * R + p.D := by ring
  have hRD' : 3 * (p.r + (p.D * (2 * R) + p.D)) ≤ p.d := by simpa [hT] using hRD
  have hRT : p.r + (p.D * (2 * R) + p.D) ≤ p.d := by omega
  have hraw := hdChildCenterDomain_overlap_linear_bound_of_sep_scale x y (2 * R) (K * R)
    (by omega) hsep hgap (by omega) hr hRT hRD'
  rw [hT] at hraw
  have hnum := overlap_decay_linear hD hR hL hK (by positivity) huL (by positivity) hαL
    (by positivity) hBL
  calc
    _ ≤ _ := hraw
    _ = (p.V : ℝ) * ((4 * (R : ℝ) + 1) *
        (1 + ((2 * p.D * R + p.D : ℕ) : ℝ) * ((p.d : ℝ) / p.r) ^ (2 * p.D * R + p.D)) *
        (Real.exp (-((p.D * (K * R - 1) : ℕ) : ℝ) / 50) +
          ((p.r + (2 * p.D * R + p.D) + 1 : ℕ) : ℝ) *
            (((p.r + (2 * p.D * R + p.D) : ℕ) : ℝ) /
              ((p.d - (p.r + (2 * p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                (p.D * (K * R - 1) / 10))) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)

theorem geometry_sublinear {p : HDParams} (x y : HDState p) (R K : ℕ) (L δ : ℝ)
    (hD : 1 ≤ p.D) (hR : 1 ≤ R) (hr : 0 < p.r) (hL : 1 ≤ L) (hδ : 0 < δ)
    (hδL : 8 ≤ δ * L) (hK40 : 40 ≤ K)
    (hK : 100 * (12 + 6 * (p.D : ℝ)) ≤ δ * K)
    (hsep : K * R ≤ hdScaleDistance p.D x y)
    (hRD : 3 * (p.r + (2 * p.D * R + p.D)) ≤ p.d)
    (huL : (p.d : ℝ) / p.r ≤ Real.exp L)
    (hαL : ((p.r + (2 * p.D * R + p.D) : ℕ) : ℝ) /
      ((p.d - (p.r + (2 * p.D * R + p.D)) + 1 : ℕ) : ℝ) ≤ Real.exp (-δ * L))
    (hBL : ((p.r + (2 * p.D * R + p.D) + 1 : ℕ) : ℝ) ≤ Real.exp ((R : ℝ) * L)) :
    ((hdChildCenterDomain x (2 * R) ∩ hdChildCenterDomain y (2 * R)).card : ℝ) ≤
      (p.V : ℝ) * Real.exp (-4 * (R : ℝ)) := by
  have hgap : 2 * (2 * R) < K * R := by nlinarith
  by_cases hvert : Nat.dist x.2 y.2 ≤ 2 * (2 * R)
  · have hs := hdScaleSeparated_spatial_distance_lower (by omega : 0 < p.D) hsep hvert hgap
    have hsep3 : 3 ≤ p.D * (K * R - 1) := by
      have hlow := Nat.le_mul_of_pos_left (K * R - 1) (by omega : 0 < p.D)
      have hkr := Nat.le_mul_of_pos_right K (by omega : 0 < R)
      omega
    have hT : p.D * (2 * R) + p.D = 2 * p.D * R + p.D := by ring
    have hRD' : 3 * (p.r + (p.D * (2 * R) + p.D)) ≤ p.d := by simpa [hT] using hRD
    have hRT : p.r + (p.D * (2 * R) + p.D) ≤ p.d := by omega
    have hraw := hdChildCenterDomain_overlap_sublinear_bound_of_sep_scale x y (2 * R) (K * R)
      (by omega) hsep hgap (by omega) hr hRT hRD' hsep3
    rw [hT] at hraw
    have hnum := overlap_decay_sublinear hD hR hL hδ hδL hK40 hK hs
      (by positivity) huL (by positivity) hαL (by positivity) hBL
    calc
      _ ≤ _ := hraw
      _ = (p.V : ℝ) * ((4 * (R : ℝ) + 1) *
          (1 + ((2 * p.D * R + p.D : ℕ) : ℝ) * ((p.d : ℝ) / p.r) ^ (2 * p.D * R + p.D)) *
          (((p.r + (2 * p.D * R + p.D) + 1 : ℕ) : ℝ) *
            (((p.r + (2 * p.D * R + p.D) : ℕ) : ℝ) /
              ((p.d - (p.r + (2 * p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                (p.D * (K * R - 1) / 10) +
            (2 : ℝ) ^ (_root_.hammingDist x.1 y.1) *
              (((p.r + (2 * p.D * R + p.D) : ℕ) : ℝ) /
                ((p.d - (p.r + (2 * p.D * R + p.D)) + 1 : ℕ) : ℝ)) ^
                  (_root_.hammingDist x.1 y.1 / 3))) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnum (Nat.cast_nonneg _)
  · have hdisj := hdChildCenterDomain_disjoint_levels x y (2 * R) (by omega)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdisj]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem linear_volume_eventually (D : ℕ) (σ ζ c_d C_d c_r : ℝ)
    (hD : 1 ≤ D) (hcd : 0 < c_d) (hζ : 0 < ζ ∧ ζ < 1) (hcr : 0 < c_r) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ N : ℕ, ∀ p : HDParams,
      p.D = D → c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n →
      c_r * p.d ≤ p.r → 4 * p.r ≤ p.d → N ≤ p.n →
      ∀ i : ℕ, i < hdScaleIndex p.n σ ζ → ∀ x y : HDState p,
        K * hdScaleRadius p.n σ i ≤ hdScaleDistance p.D x y →
        ((hdChildCenterDomain x (2 * hdScaleRadius p.n σ i) ∩
          hdChildCenterDomain y (2 * hdScaleRadius p.n σ i)).card : ℝ) ≤
            (p.V : ℝ) * Real.exp (-4 * (hdScaleRadius p.n σ i : ℝ)) := by
  let L := max 1 (Real.log (1 / c_r))
  have hL : 1 ≤ L := le_max_left _ _
  have hinv : 1 / c_r ≤ Real.exp L := by
    calc
      _ = Real.exp (Real.log (1 / c_r)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_max_right _ _)
  obtain ⟨K, hK⟩ := exists_nat_ge (200 * (12 + 6 * (D : ℝ)) * L)
  have hK1 : 1 ≤ K := by
    have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have : (1 : ℝ) ≤ K := by nlinarith
    exact_mod_cast this
  obtain ⟨NE, hE⟩ := radius_environment_eventually σ C_d
  obtain ⟨NT, hT⟩ := hdScaleRadius_child_enlargement_le_dimension_eventually
    (2 * D) σ ζ c_d (by omega) hcd hζ
  refine ⟨K, hK1, max NE NT, ?_⟩
  intro p hpD hdlo hdhi hrlo hrhi hn i hi x y hsep
  obtain ⟨hn2, hlog, hnC, hdimexp⟩ := hE p.n p.d i (by omega) hdhi
  let R := hdScaleRadius p.n σ i
  let T := 2 * p.D * R + p.D
  have hR : 1 ≤ R := (radius_lower p.n σ i).1
  have hdim : 0 < (p.d : ℝ) := by
    have hnpos : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
    exact lt_of_lt_of_le (mul_pos hcd hnpos) hdlo
  have hrpos : 0 < (p.r : ℝ) := lt_of_lt_of_le (mul_pos hcr hdim) hrlo
  have hrnat : 0 < p.r := by exact_mod_cast hrpos
  have hTdim : 12 * T ≤ p.d := by
    have ht := hT p.n p.d i (by omega) hdlo hi
    have hh : (12 : ℝ) * (T : ℝ) ≤ (p.d : ℝ) := by
      dsimp [T, R]
      rw [hpD]
      push_cast at ht ⊢
      nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
    exact_mod_cast hh
  have hRD : 3 * (p.r + T) ≤ p.d := by omega
  have hRT : p.r + T ≤ p.d := by omega
  have hu : (p.d : ℝ) / p.r ≤ 1 / c_r := by
    apply (div_le_div_iff₀ hrpos hcr).2
    nlinarith
  have hden : (0 : ℝ) < ((p.d - (p.r + T) + 1 : ℕ) : ℝ) := by positivity
  have hα : ((p.r + T : ℕ) : ℝ) /
      ((p.d - (p.r + T) + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).2
    have hdenNat : 2 * (p.r + T) ≤ p.d - (p.r + T) + 1 := by omega
    have hdenReal : 2 * ((p.r + T : ℕ) : ℝ) ≤ ((p.d - (p.r + T) + 1 : ℕ) : ℝ) :=
      by exact_mod_cast hdenNat
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  have hBL : ((p.r + T + 1 : ℕ) : ℝ) ≤ Real.exp ((R : ℝ) * L) := by
    calc
      _ ≤ ((p.d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : p.r + T + 1 ≤ p.d + 1)
      _ ≤ Real.exp (R : ℝ) := hdimexp
      _ ≤ _ := Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg R))
  exact geometry_linear x y R K L (by omega) hR hrnat hL (by simpa [hpD] using hK)
    hsep hRD (hu.trans hinv) (hα.trans hhalf) hBL

theorem sublinear_volume_eventually (D : ℕ) (σ ζ c_d C_d ρ : ℝ)
    (hD : 1 ≤ D) (hcd : 0 < c_d) (hζ : 0 < ζ ∧ ζ < 1) (hρ : 0 < ρ ∧ ρ < 1) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ N : ℕ, ∀ p : HDParams,
      p.D = D → c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n →
      p.r = ⌊(p.n : ℝ) ^ (1 - ρ)⌋₊ → N ≤ p.n →
      ∀ i : ℕ, i < hdScaleIndex p.n σ ζ → ∀ x y : HDState p,
        K * hdScaleRadius p.n σ i ≤ hdScaleDistance p.D x y →
        ((hdChildCenterDomain x (2 * hdScaleRadius p.n σ i) ∩
          hdChildCenterDomain y (2 * hdScaleRadius p.n σ i)).card : ℝ) ≤
            (p.V : ℝ) * Real.exp (-4 * (hdScaleRadius p.n σ i : ℝ)) := by
  let E : ℝ := min ρ ζ / 2
  let δ : ℝ := E / 2
  let C : ℝ := 1 + 6 * (D : ℝ)
  have hE : 0 < E := by dsimp [E]; exact div_pos (lt_min hρ.1 hζ.1) (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hEρ : 2 * E ≤ ρ := by dsimp [E]; linarith [min_le_left ρ ζ]
  have hEζ : 2 * E ≤ ζ := by dsimp [E]; linarith [min_le_right ρ ζ]
  obtain ⟨K, hK⟩ := exists_nat_ge (max 40 (100 * (12 + 6 * (D : ℝ)) / δ))
  have hK40 : 40 ≤ K := by
    exact_mod_cast (le_max_left _ _).trans hK
  have hKδ : 100 * (12 + 6 * (D : ℝ)) ≤ δ * K := by
    have := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hK)
    nlinarith
  obtain ⟨NE, henv⟩ := radius_environment_eventually σ C_d
  obtain ⟨NP, hpow⟩ := exists_nat_rpow_ge (e := E) (C := 6 * C / c_d) hE
  obtain ⟨NL, hlog⟩ := exists_nat_log_ge (8 / E)
  refine ⟨K, by omega, max NE (max NP NL), ?_⟩
  intro p hpD hdlo hdhi hpr hn i hi x y hsep
  obtain ⟨hn2, hnlog, hnC, hdimexp⟩ := henv p.n p.d i (by omega) hdhi
  have hn0 : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
  let R := hdScaleRadius p.n σ i
  let T := 2 * p.D * R + p.D
  let L := 2 * Real.log (p.n : ℝ)
  let Q := (p.n : ℝ) ^ E
  have hR := (radius_lower p.n σ i).1
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hδL : 8 ≤ δ * L := by
    have hh := (div_le_iff₀ hE).mp (hlog p.n (by omega))
    dsimp [δ, L]
    nlinarith
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hn0 E
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hn1 hE.le
  have hcoef : 6 * C ≤ c_d * Q := by
    have hh := (div_le_iff₀ hcd).mp (hpow p.n (by omega))
    dsimp [Q]
    nlinarith
  have hpowζ : 1 ≤ (p.n : ℝ) ^ (1 - ζ) := Real.one_le_rpow hn1 (by linarith [hζ.2])
  have hpowρ : 1 ≤ (p.n : ℝ) ^ (1 - ρ) := Real.one_le_rpow hn1 (by linarith [hρ.2])
  have hr1 : 1 ≤ p.r := by
    rw [hpr]
    have := Nat.floor_mono hpowρ
    simpa using this
  have hr0 : (0 : ℝ) < p.r := by exact_mod_cast (by omega : 0 < p.r)
  have hrle : (p.r : ℝ) ≤ (p.n : ℝ) ^ (1 - ρ) := by
    rw [hpr]
    exact Nat.floor_le (by positivity)
  have hRup := radius_upper hn2 hζ hi
  have hTle : (T : ℝ) ≤ 6 * (D : ℝ) * (p.n : ℝ) ^ (1 - ζ) := by
    dsimp [T, R]
    rw [hpD]
    push_cast
    nlinarith [show (0 : ℝ) ≤ D from Nat.cast_nonneg D]
  have hpowρE : (p.n : ℝ) ^ (1 - ρ) ≤ (p.n : ℝ) ^ (1 - 2 * E) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpowζE : (p.n : ℝ) ^ (1 - ζ) ≤ (p.n : ℝ) ^ (1 - 2 * E) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hrad : ((p.r + T : ℕ) : ℝ) ≤ C * (p.n : ℝ) ^ (1 - 2 * E) := by
    have hT' := mul_le_mul_of_nonneg_left hpowζE (by positivity : 0 ≤ 6 * (D : ℝ))
    dsimp [C]
    push_cast
    nlinarith [hTle, hrle.trans hpowρE]
  have hpowEq : (p.n : ℝ) ^ (1 - 2 * E) * Q = (p.n : ℝ) ^ (1 - E) := by
    dsimp [Q]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hpowEq2 : Q * (p.n : ℝ) ^ (1 - E) = (p.n : ℝ) := by
    dsimp [Q]
    rw [← Real.rpow_add hn0]
    have : E + (1 - E) = 1 := by ring
    rw [this, Real.rpow_one]
  have hradQ : 6 * ((p.r + T : ℕ) : ℝ) * Q ≤ c_d * (p.n : ℝ) := by
    calc
      _ ≤ 6 * (C * (p.n : ℝ) ^ (1 - 2 * E)) * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (by norm_num)) hQpos.le
      _ = 6 * C * (p.n : ℝ) ^ (1 - E) := by
        calc
          _ = 6 * C * ((p.n : ℝ) ^ (1 - 2 * E) * Q) := by ring
          _ = _ := by rw [hpowEq]
      _ ≤ (c_d * Q) * (p.n : ℝ) ^ (1 - E) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by rw [mul_assoc, hpowEq2]
  have hrad0 : (0 : ℝ) ≤ ((p.r + T : ℕ) : ℝ) := Nat.cast_nonneg _
  have hRDreal : 6 * ((p.r + T : ℕ) : ℝ) ≤ (p.d : ℝ) := by
    nlinarith [hradQ, hdlo, mul_le_mul_of_nonneg_left hQ1 (by positivity : 0 ≤ 6 * ((p.r + T : ℕ) : ℝ))]
  have hRD6 : 6 * (p.r + T) ≤ p.d := by exact_mod_cast hRDreal
  have hRD : 3 * (p.r + T) ≤ p.d := by omega
  have hden0 : (0 : ℝ) < ((p.d - (p.r + T) + 1 : ℕ) : ℝ) := by positivity
  have hden : ((p.d : ℝ) / 2) ≤ ((p.d - (p.r + T) + 1 : ℕ) : ℝ) := by
    have hn : p.d ≤ 2 * (p.d - (p.r + T) + 1) := by omega
    have hh : (p.d : ℝ) ≤ 2 * ((p.d - (p.r + T) + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hα : ((p.r + T : ℕ) : ℝ) / ((p.d - (p.r + T) + 1 : ℕ) : ℝ) ≤ 1 / Q := by
    apply (div_le_div_iff₀ hden0 hQpos).2
    nlinarith [hradQ, hdlo]
  have hinv : 1 / Q = Real.exp (-δ * L) := by
    dsimp [Q]
    rw [Real.rpow_def_of_pos hn0, one_div, ← Real.exp_neg]
    congr 1
    dsimp [δ, L]
    ring
  have hdim2 : (p.d : ℝ) ≤ (p.n : ℝ) ^ 2 := by nlinarith [hdhi, hnC]
  have hnexp : (p.n : ℝ) ^ 2 = Real.exp L := by
    dsimp [L]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hn0]
  have hu : (p.d : ℝ) / p.r ≤ Real.exp L := by
    calc
      _ ≤ (p.d : ℝ) := (div_le_iff₀ hr0).2 (by
        have hh : (1 : ℝ) ≤ p.r := by exact_mod_cast hr1
        simpa using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg p.d))
      _ ≤ (p.n : ℝ) ^ 2 := hdim2
      _ = _ := hnexp
  have hBL : ((p.r + T + 1 : ℕ) : ℝ) ≤ Real.exp ((R : ℝ) * L) := by
    calc
      _ ≤ ((p.d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : p.r + T + 1 ≤ p.d + 1)
      _ ≤ Real.exp (R : ℝ) := hdimexp
      _ ≤ _ := Real.exp_le_exp.mpr (by simpa using mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg R))
  exact geometry_sublinear x y R K L δ (by omega) hR (by omega) hL hδ hδL hK40
    (by simpa [hpD] using hKδ) hsep hRD hu (by rw [← hinv]; exact hα) hBL

theorem volume_decay_eventually (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ N : ℕ, ∀ p : HDParams,
      p.D = D → c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      N ≤ p.n → ∀ i : ℕ, i < hdScaleIndex p.n σ ζ → ∀ x y : HDState p,
        K * hdScaleRadius p.n σ i ≤ hdScaleDistance p.D x y →
        ((hdChildCenterDomain x (2 * hdScaleRadius p.n σ i) ∩
          hdChildCenterDomain y (2 * hdScaleRadius p.n σ i)).card : ℝ) ≤
            (p.V : ℝ) * Real.exp (-4 * (hdScaleRadius p.n σ i : ℝ)) := by
  have hζ : 0 < ζ ∧ ζ < 1 := ⟨lt_trans hp.hsz.1 hp.hsz.2.1, hp.hsz.2.2.1⟩
  cases reg with
  | lin c_r hcr =>
      obtain ⟨K, hK, N, hN⟩ := linear_volume_eventually D σ ζ c_d C_d c_r hp.hD hp.hd.1 hζ hcr.1
      refine ⟨K, hK, N, ?_⟩
      intro p hpD hdlo hdhi hreg hn
      exact hN p hpD hdlo hdhi hreg.1 hreg.2 hn
  | sub ρ hρ =>
      exact sublinear_volume_eventually D σ ζ c_d C_d ρ hp.hD hp.hd.1 hζ ⟨hρ.1, hρ.2.1⟩

end HypercubeRamsey.Lane_sol_hs_ovl
