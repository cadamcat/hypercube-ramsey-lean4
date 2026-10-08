import HypercubeRamsey.S05.Even_scales_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000

variable {γ K' χ : ℝ}

theorem history_length_upper (p : Params5 γ K' χ) (n : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ p.m n) :
    (p.s n : ℝ) ≤ (10 * p.Ks + 1) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ p.m n := by exact_mod_cast hm
  have hmn : (p.m n : ℝ) ≤ n := by exact_mod_cast m_le_n p n hn
  have hKs0 := p.hKs.le
  have hraw0 : 0 ≤ p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) :=
    mul_nonneg (mul_nonneg hKs0 (Nat.cast_nonneg _)) (Real.log_nonneg hmR)
  have hs : (p.s n : ℝ) ≤ p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) + 1 :=
    (Nat.ceil_lt_add_one hraw0).le
  have hJ : (p.J n : ℝ) ≤ (p.m n : ℝ) ^ (1 / 20 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hlog : Real.log (p.m n : ℝ) ≤ 10 * (p.m n : ℝ) ^ (1 / 10 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ p.m n) (by norm_num : (0 : ℝ) < 1 / 10)
  have hraw : p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ) ≤
      10 * p.Ks * (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ p.Ks * ((p.m n : ℝ) ^ (1 / 20 : ℝ)) *
          (10 * (p.m n : ℝ) ^ (1 / 10 : ℝ)) := by
        gcongr
      _ = 10 * p.Ks * (p.m n : ℝ) ^ (3 / 20 : ℝ) := by
        rw [show (3 / 20 : ℝ) = 1 / 20 + 1 / 10 by norm_num,
          Real.rpow_add (by linarith : (0 : ℝ) < p.m n)]
        ring
      _ ≤ 10 * p.Ks * (n : ℝ) ^ (1 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Real.rpow_le_rpow (by positivity) hmn (by norm_num)).trans
          (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have ht : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  nlinarith

theorem eventual_m_quarter (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ (p.m n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (23 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 23 / 100)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hp.eventually_ge_atTop 2] with n hn hlarge
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hceil : (p.m n : ℝ) ≤ (n : ℝ) ^ p.alpha + 1 :=
    (Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le _)).le
  have hp1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 50 : ℝ) := Real.one_le_rpow hnR (by norm_num)
  have hp2 : (n : ℝ) ^ p.alpha ≤ (n : ℝ) ^ (1 / 50 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR p.halpha.2.le
  have hmult := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (n : ℝ) ^ (1 / 50 : ℝ))
  rw [← Real.rpow_add hn0] at hmult
  norm_num at hmult
  exact ⟨hn, by linarith⟩

theorem posterior_exponent_gap (p : Params5 γ K' χ) : 0 < p.tau0 - p.a 6 - p.delta := by
  have h68 := p.ha_order 6 8 (by decide)
  have hδ := p.hdelta.2
  have hmin := min_le_left (p.tau0 - p.a 8) (p.tau1 - p.tau0)
  linarith [p.hgap.1]

def blockDensityCoeff (p : Params5 γ K' χ) : ℝ := p.Kpp * (1 + 1204 * (10 * p.Ks + 1))

theorem blockDensityCoeff_pos (p : Params5 γ K' χ) : 0 < blockDensityCoeff p := by
  unfold blockDensityCoeff
  have hKs := p.hKs
  have hKpp := p.hKpp
  positivity

theorem eventual_density_coefficient (p : Params5 γ K' χ) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ n ∧ 2 ≤ p.m n ∧ (p.m n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) ∧
      blockDensityCoeff p * (n : ℝ) ^ (1 / 2 : ℝ) + (n : ℝ) ^ γ ≤
        (p.tau0 - p.a 6 - p.delta) * n := by
  let c := p.tau0 - p.a 6 - p.delta
  have hc : 0 < c := posterior_exponent_gap p
  have hC : 0 < blockDensityCoeff p := blockDensityCoeff_pos p
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have hγ : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - γ)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith [p.hγ.2])).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventual_m_quarter p, (Lane_sol_s05_h1.tendsto_m p).eventually_ge_atTop 2,
    hp.eventually_ge_atTop (2 * blockDensityCoeff p / c),
    hγ.eventually_ge_atTop (2 / c)] with n hn hm hlarge hlargeγ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := (div_le_iff₀ hc).mp hlarge
  have hbγ := (div_le_iff₀ hc).mp hlargeγ
  have hpMul := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ))
  have hγMul := mul_le_mul_of_nonneg_right hbγ (by positivity : 0 ≤ (n : ℝ) ^ γ)
  have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = n := by
    rw [← Real.rpow_add hnR]
    norm_num
  have hprod : (n : ℝ) ^ (1 - γ) * (n : ℝ) ^ γ = n := by
    rw [← Real.rpow_add hnR]
    simp
  have hhalf : 2 * blockDensityCoeff p * (n : ℝ) ^ (1 / 2 : ℝ) ≤ c * n := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * c * (n : ℝ) ^ (1 / 2 : ℝ) := hpMul
      _ = _ := by rw [mul_right_comm, hsq]; ring
  have hother : 2 * (n : ℝ) ^ γ ≤ c * n := by
    calc
      _ ≤ (n : ℝ) ^ (1 - γ) * c * (n : ℝ) ^ γ := hγMul
      _ = _ := by rw [mul_right_comm, hprod]; ring
  refine ⟨hn.1, by exact_mod_cast hm, hn.2, ?_⟩
  dsimp [c] at hhalf hother
  linarith

theorem block_coefficient_bound {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G) (v : EvenRole5 n)
    (hn : 1 ≤ n) (hm : 1 ≤ X.p.m n)
    (hmn : (X.p.m n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ)) :
    X.p.Kpp * (1 + ∑ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1,
      (colLen5 (X.p.s n) ℓ : ℝ)) ≤ blockDensityCoeff X.p * (n : ℝ) ^ (1 / 2 : ℝ) := by
  let t := (n : ℝ) ^ (1 / 4 : ℝ)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 1 ≤ t := Real.one_le_rpow hnR (by norm_num)
  have hlen := history_length_upper X.p n hn hm
  have hC0 : 0 < 10 * X.p.Ks + 1 := by linarith [X.p.hKs]
  have hkey : ((X.g.evenType (X.p.J n) v.1).2.1.card : ℝ) ≤ 1204 * t := by
    have hh := Lane_sol_s05_h1.typeKeys_card_le X.g (X.p.J n) v.1
    change (X.g.typeKeys (X.p.J n) v.1).card ≤ _ at hh
    have hhR : ((X.g.typeKeys (X.p.J n) v.1).card : ℝ) ≤ 1203 + (X.p.m n : ℝ) := by
      have hNat : (X.g.typeKeys (X.p.J n) v.1).card ≤ 1203 + X.p.m n := by
        norm_num [coarseChunkCount5] at hh
        omega
      exact_mod_cast hNat
    change ((X.g.typeKeys (X.p.J n) v.1).card : ℝ) ≤ _
    dsimp [t] at ht ⊢
    linarith
  have hcol (ℓ : X.Key) : (colLen5 (X.p.s n) ℓ : ℝ) ≤ (10 * X.p.Ks + 1) * t := by
    cases ℓ with
    | inl k => simp only [colLen5, Nat.cast_one]; nlinarith [X.p.hKs]
    | inr k => exact hlen
  have hsum : (∑ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, (colLen5 (X.p.s n) ℓ : ℝ)) ≤
      1204 * (10 * X.p.Ks + 1) * t ^ 2 := by
    calc
      _ ≤ ∑ _ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, (10 * X.p.Ks + 1) * t :=
        Finset.sum_le_sum fun ℓ _ => hcol ℓ
      _ = ((X.g.evenType (X.p.J n) v.1).2.1.card : ℝ) * ((10 * X.p.Ks + 1) * t) := by simp
      _ ≤ (1204 * t) * ((10 * X.p.Ks + 1) * t) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = _ := by ring
  have ht2 : t ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have h1 : 1 ≤ t ^ 2 := by nlinarith
  have hK0 := X.p.hKpp.le
  unfold blockDensityCoeff
  rw [← ht2]
  nlinarith [mul_le_mul_of_nonneg_left hsum hK0]

end
end HypercubeRamsey.Lane_sol_s05_even
