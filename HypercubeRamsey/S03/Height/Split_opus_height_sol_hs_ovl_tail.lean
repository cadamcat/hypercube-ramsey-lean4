import HypercubeRamsey.S03.Height.Split_opus_height_sol_hs_ovl_geometry

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_hs_ovl

open OAI.HypercubeRamsey Lane_p_height_main

theorem tail_environment_eventually (J₀ b₀ b σ : ℝ)
    (hJ : 0 < J₀) (hσ : 0 < σ ∧ σ < 1) (hbJ : b ≤ J₀) (hb₀J : b₀ ≤ J₀)
    (hbσ : 0 ≤ b - 2 * σ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i h K q : ℕ, 1 ≤ K → 0 < q →
      (q : ℝ) ≤ (hdScaleMultiplier n σ : ℝ) /
        (16 * ((h + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1)) →
      let R := hdScaleRadius n σ i
      let e := (n : ℝ) ^ (b - 2 * σ)
      1 ≤ e ∧
      (n : ℝ) ^ J₀ * Real.exp (-4 * (R : ℝ)) ≤ Real.exp (-3 * (R : ℝ)) ∧
      (n : ℝ) ^ b₀ * Real.exp (-4 * (R : ℝ)) ≤ Real.exp (-3 * (R : ℝ)) ∧
      e ≤ (1 / (20 * ((h + 1 : ℕ) : ℝ))) * (n : ℝ) ^ J₀ / (q : ℝ) ∧
      e ≤ (1 / (20 * ((h + 1 : ℕ) : ℝ))) * (n : ℝ) ^ b / (q : ℝ) ∧
      (q : ℝ) ^ 2 ≤ Real.exp (e * (R : ℝ)) := by
  obtain ⟨NL, hlog⟩ := exists_nat_log_ge (max 4 J₀)
  obtain ⟨NP, hpow⟩ := exists_nat_rpow_ge (e := σ) (C := 2) hσ.1
  refine ⟨max 2 (max NL NP), ?_⟩
  intro n hn i h K q hK hq hqbound
  let R := hdScaleRadius n σ i
  let e := (n : ℝ) ^ (b - 2 * σ)
  let t := (n : ℝ) ^ σ
  let H : ℝ := ((h + 1 : ℕ) : ℝ)
  have hn2 : 2 ≤ n := by omega
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hl := hlog n (by omega)
  have hl4 : 4 ≤ Real.log (n : ℝ) := (le_max_left _ _).trans hl
  have hlJ : J₀ ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hl
  have hl0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have ht2 : 2 ≤ t := hpow n (by omega)
  have he1 : 1 ≤ e := Real.one_le_rpow hn1 hbσ
  have he0 : 0 ≤ e := by linarith
  have htN : t ≤ (n : ℝ) := by
    calc
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hσ.2.le
      _ = _ := Real.rpow_one _
  have hM : (hdScaleMultiplier n σ : ℝ) ≤ 2 * t := by
    unfold hdScaleMultiplier
    rw [Nat.cast_max]
    apply max_le
    · norm_num
      linarith
    · have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le σ)
      dsimp [t]
      linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hden : 20 * H * (q : ℝ) ≤ 2 * t := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 16 * H * (2 * (K : ℝ) + 1))).mp hqbound
    have hcoeff : 20 * H ≤ 16 * H * (2 * (K : ℝ) + 1) := by nlinarith
    have hmul2 := mul_le_mul_of_nonneg_right hcoeff hqr.le
    nlinarith [hM]
  have hpowEq : (n : ℝ) ^ b = e * t * t := by
    dsimp [e, t]
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1
    ring
  have hdenE : e * (20 * H * (q : ℝ)) ≤ (n : ℝ) ^ b := by
    rw [hpowEq]
    have hh := mul_le_mul_of_nonneg_left hden he0
    nlinarith [mul_le_mul_of_nonneg_left (show 2 * t ≤ t * t by nlinarith) he0]
  have hτb : e ≤ (1 / (20 * H)) * (n : ℝ) ^ b / (q : ℝ) := by
    have hh : e ≤ (n : ℝ) ^ b / (20 * H * (q : ℝ)) :=
      (le_div_iff₀ (by positivity)).2 hdenE
    have heq : (n : ℝ) ^ b / (20 * H * (q : ℝ)) =
        (1 / (20 * H)) * (n : ℝ) ^ b / (q : ℝ) := by ring
    rwa [heq] at hh
  have hτJ : e ≤ (1 / (20 * H)) * (n : ℝ) ^ J₀ / (q : ℝ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 hbJ
    have hh : e ≤ (n : ℝ) ^ J₀ / (20 * H * (q : ℝ)) :=
      (le_div_iff₀ (by positivity)).2 (hdenE.trans hp)
    have heq : (n : ℝ) ^ J₀ / (20 * H * (q : ℝ)) =
        (1 / (20 * H)) * (n : ℝ) ^ J₀ / (q : ℝ) := by ring
    rwa [heq] at hh
  have hRlow : Real.log (n : ℝ) ^ 2 ≤ (R : ℝ) := (radius_lower n σ i).2
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hmeanJ : (n : ℝ) ^ J₀ * Real.exp (-4 * (R : ℝ)) ≤ Real.exp (-3 * (R : ℝ)) := by
    rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlJ hl0]
  have hmeanb₀ : (n : ℝ) ^ b₀ * Real.exp (-4 * (R : ℝ)) ≤ Real.exp (-3 * (R : ℝ)) :=
    le_trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hb₀J)
      (Real.exp_pos _).le) hmeanJ
  have hqN : (q : ℝ) ≤ 2 * (n : ℝ) := by
    have hdenom : 1 ≤ 16 * H * (2 * (K : ℝ) + 1) := by
      have hh : (1 : ℝ) ≤ H := by dsimp [H]; exact_mod_cast (by omega : 1 ≤ h + 1)
      nlinarith
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * H * (2 * (K : ℝ) + 1))).mp hqbound
    have hqM : (q : ℝ) ≤ (hdScaleMultiplier n σ : ℝ) := by nlinarith
    linarith
  have hcard : (q : ℝ) ^ 2 ≤ Real.exp (e * (R : ℝ)) := by
    have hn4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    calc
      (q : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by nlinarith
      _ ≤ (n : ℝ) ^ 4 := by
        have hh := mul_le_mul_of_nonneg_right hn4 (sq_nonneg (n : ℝ))
        nlinarith
      _ = Real.exp (4 * Real.log (n : ℝ)) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hn0]
      _ ≤ Real.exp (R : ℝ) := by apply Real.exp_le_exp.mpr; nlinarith
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact ⟨he1, hmeanJ, hmeanb₀, hτJ, hτb, hcard⟩

theorem position_regions_tail {p : HDParams} {J : Type*}
    (I : Finset J) (T : J → Finset p.Loc) (τ e : ℝ) (R : ℕ)
    (hV : 0 < (p.V : ℝ)) (hlam : 0 ≤ p.lam)
    (hP1 : p.lam / (p.V : ℝ) ≤ 1) (he : 0 ≤ e) (hτ : e ≤ τ)
    (hmean : p.lam * Real.exp (-4 * (R : ℝ)) ≤ Real.exp (-3 * (R : ℝ)))
    (hcard : (I.card : ℝ) ≤ Real.exp (e * (R : ℝ)))
    (hvol : ∀ j ∈ I, ((T j).card : ℝ) ≤ (p.V : ℝ) * Real.exp (-4 * (R : ℝ))) :
    p.posLaw.pr (fun P => ∃ j ∈ I, τ < (((T j).filter (fun ℓ => P ℓ = true)).card : ℝ)) ≤
      Real.exp (-(e * (R : ℝ))) := by
  classical
  have hP0 : 0 ≤ p.lam / (p.V : ℝ) := div_nonneg hlam hV.le
  apply threshold_tail p.posLaw I _ (p.lam * Real.exp (-4 * (R : ℝ))) τ e (R : ℝ)
    (by positivity) (Nat.cast_nonneg _) he hτ hmean hcard
  intro j hj k
  have hm : ((T j).card : ℝ) * (p.lam / (p.V : ℝ)) ≤
      p.lam * Real.exp (-4 * (R : ℝ)) := by
    calc
      _ ≤ ((p.V : ℝ) * Real.exp (-4 * (R : ℝ))) * (p.lam / (p.V : ℝ)) :=
        mul_le_mul_of_nonneg_right (hvol j hj) hP0
      _ = _ := by field_simp [hV.ne']
  calc
    _ ≤ ((T j).card : ℝ) ^ k * (p.lam / (p.V : ℝ)) ^ k :=
      position_count_ge_prob_bound hP0 hP1 (T j) k
    _ = (((T j).card : ℝ) * (p.lam / (p.V : ℝ))) ^ k := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hm k

theorem active_regions_tail {p : HDParams} {J : Type*}
    (I : Finset J) (T : J → Finset p.Loc) (τ e : ℝ) (R : ℕ)
    (hV : 0 < (p.V : ℝ)) (hlam : 0 < p.lam)
    (hP1 : p.lam / (p.V : ℝ) ≤ 1) (hA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1)
    (he : 0 ≤ e) (hτ : e ≤ τ)
    (hmean : (p.n : ℝ) ^ p.b₀ * Real.exp (-4 * (R : ℝ)) ≤ Real.exp (-3 * (R : ℝ)))
    (hcard : (I.card : ℝ) ≤ Real.exp (e * (R : ℝ)))
    (hvol : ∀ j ∈ I, ((T j).card : ℝ) ≤ (p.V : ℝ) * Real.exp (-4 * (R : ℝ))) :
    (p.posLaw.prod p.actLaw).pr (fun ω => ∃ j ∈ I,
      τ < (((T j).filter (fun ℓ => ω.1 ℓ = true ∧ ω.2 ℓ = true)).card : ℝ)) ≤
        Real.exp (-(e * (R : ℝ))) := by
  classical
  have hP0 : 0 ≤ p.lam / (p.V : ℝ) := div_nonneg hlam.le hV.le
  have hA0 : 0 ≤ (p.n : ℝ) ^ p.b₀ / p.lam := div_nonneg (by positivity) hlam.le
  have hrate : p.lam / (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) =
      (p.n : ℝ) ^ p.b₀ / (p.V : ℝ) := by field_simp [hlam.ne', hV.ne']
  apply threshold_tail (p.posLaw.prod p.actLaw) I _
    ((p.n : ℝ) ^ p.b₀ * Real.exp (-4 * (R : ℝ))) τ e (R : ℝ)
    (by positivity) (Nat.cast_nonneg _) he hτ hmean hcard
  intro j hj k
  have hm : ((T j).card : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) ≤
      (p.n : ℝ) ^ p.b₀ * Real.exp (-4 * (R : ℝ)) := by
    calc
      _ ≤ ((p.V : ℝ) * Real.exp (-4 * (R : ℝ))) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) :=
        mul_le_mul_of_nonneg_right (hvol j hj) (by positivity)
      _ = _ := by field_simp [hV.ne']
  calc
    _ ≤ ((T j).card : ℝ) ^ k *
        (p.lam / (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) ^ k :=
      active_count_ge_prob_bound hP0 hP1 hA0 hA1 (T j) k
    _ = (((T j).card : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ))) ^ k := by rw [hrate, mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hm k

end HypercubeRamsey.Lane_sol_hs_ovl
