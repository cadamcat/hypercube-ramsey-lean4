import HypercubeRamsey.S03.Height.Selection_p_height_main

set_option maxHeartbeats 400000

namespace HypercubeRamsey.Lane_sol_hs_ovl

open OAI.HypercubeRamsey Lane_p_height_main
open scoped BigOperators

theorem pow_exp_bound {u L : ℝ} (hu : 0 ≤ u) (h : u ≤ Real.exp L) (k : ℕ) :
    u ^ k ≤ Real.exp (L * (k : ℝ)) := by
  calc
    u ^ k ≤ (Real.exp L) ^ k := pow_le_pow_left₀ hu h k
    _ = Real.exp (L * (k : ℝ)) := by rw [mul_comm L, Real.exp_nat_mul]

theorem enlargement_factor {D R : ℕ} {L u : ℝ}
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hL : 1 ≤ L)
    (hu : 0 ≤ u) (huL : u ≤ Real.exp L) :
    (4 * (R : ℝ) + 1) * (1 + ((2 * D * R + D : ℕ) : ℝ) * u ^ (2 * D * R + D)) ≤
      Real.exp ((4 + 6 * (D : ℝ)) * (R : ℝ) * L) := by
  let T := 2 * D * R + D
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hT : (T : ℝ) ≤ 3 * (D : ℝ) * R := by
    dsimp [T]
    push_cast
    have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hp := pow_exp_bound hu huL T
  have he1 : (1 : ℝ) ≤ Real.exp (L * (T : ℝ)) :=
    Real.one_le_exp (mul_nonneg hL0 hT0)
  have hsum : 1 + (T : ℝ) * u ^ T ≤ Real.exp (2 * L * (T : ℝ)) := by
    calc
      1 + (T : ℝ) * u ^ T ≤ (1 + (T : ℝ)) * Real.exp (L * (T : ℝ)) := by
        nlinarith [mul_le_mul_of_nonneg_left hp hT0]
      _ ≤ Real.exp (T : ℝ) * Real.exp (L * (T : ℝ)) :=
        mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp (T : ℝ)) (Real.exp_pos _).le
      _ = Real.exp ((T : ℝ) + L * (T : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2 * L * (T : ℝ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hfront : 4 * (R : ℝ) + 1 ≤ Real.exp (4 * (R : ℝ) * L) := by
    calc
      _ ≤ Real.exp (4 * (R : ℝ)) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ Real.exp (4 * (R : ℝ) * L) * Real.exp (2 * L * (T : ℝ)) :=
      mul_le_mul hfront hsum (by positivity) (Real.exp_pos _).le
    _ = Real.exp (4 * (R : ℝ) * L + 2 * L * (T : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hT hL0]

theorem threshold_tail {Ω J : Type*} [Fintype Ω] (Q : FinProb Ω)
    (I : Finset J) (count : J → Ω → ℕ) (mean τ e R : ℝ)
    (hmean0 : 0 ≤ mean) (hR : 0 ≤ R) (he : 0 ≤ e) (hτ : e ≤ τ)
    (hmean : mean ≤ Real.exp (-3 * R))
    (hcard : (I.card : ℝ) ≤ Real.exp (e * R))
    (htail : ∀ j ∈ I, ∀ k : ℕ,
      Q.pr (fun ω => k ≤ count j ω) ≤ mean ^ k) :
    Q.pr (fun ω => ∃ j ∈ I, τ < (count j ω : ℝ)) ≤ Real.exp (-(e * R)) := by
  classical
  let k := ⌊τ⌋₊ + 1
  have hτ0 : 0 ≤ τ := he.trans hτ
  have hk : τ ≤ (k : ℝ) := by simpa [k] using (Nat.lt_floor_add_one τ).le
  have hcover : ∀ j ω, τ < (count j ω : ℝ) → k ≤ count j ω := by
    intro j ω h
    dsimp [k]
    exact Nat.succ_le_iff.mpr ((Nat.floor_lt hτ0).mpr h)
  have hprob : ∀ j ∈ I, Q.pr (fun ω => τ < (count j ω : ℝ)) ≤
      Real.exp (-3 * R * e) := by
    intro j hj
    calc
      _ ≤ Q.pr (fun ω => k ≤ count j ω) :=
        finprob_pr_mono _ _ _ (hcover j)
      _ ≤ mean ^ k := htail j hj k
      _ ≤ Real.exp (-3 * R * (k : ℝ)) := pow_exp_bound hmean0 hmean k
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [he.trans (hτ.trans hk)]
  calc
    _ ≤ ∑ j ∈ I, Q.pr (fun ω => τ < (count j ω : ℝ)) :=
      finprob_pr_finset_exists_le Q I _
    _ ≤ ∑ j ∈ I, Real.exp (-3 * R * e) :=
      Finset.sum_le_sum (fun j hj => hprob j hj)
    _ = (I.card : ℝ) * Real.exp (-3 * R * e) := by simp
    _ ≤ Real.exp (e * R) * Real.exp (-3 * R * e) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (e * R + -3 * R * e) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem separation_arith {D R K : ℕ} (hD : 1 ≤ D) (hR : 1 ≤ R) (hK : 40 ≤ K) :
    (K : ℝ) * R / 2 ≤ ((D * (K * R - 1) : ℕ) : ℝ) ∧
    (K : ℝ) * R / 40 ≤ ((D * (K * R - 1) / 10 : ℕ) : ℝ) := by
  have hKR : 40 ≤ K * R := le_trans hK (Nat.le_mul_of_pos_right _ (by omega))
  have hlowNat : K * R - 1 ≤ D * (K * R - 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hlow : (K : ℝ) * R - 1 ≤ ((D * (K * R - 1) : ℕ) : ℝ) := by
    have hcast : ((K * R - 1 : ℕ) : ℝ) = (K : ℝ) * R - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ K * R)]
      push_cast
      rfl
    rw [← hcast]
    exact_mod_cast hlowNat
  have hKRreal : (40 : ℝ) ≤ (K : ℝ) * R := by exact_mod_cast hKR
  have hfloorNat : D * (K * R - 1) ≤ 10 * (D * (K * R - 1) / 10) + 9 := by omega
  have hfloor : ((D * (K * R - 1) : ℕ) : ℝ) ≤
      10 * ((D * (K * R - 1) / 10 : ℕ) : ℝ) + 9 := by exact_mod_cast hfloorNat
  constructor <;> linarith

theorem two_terms_decay {R : ℕ} {L A F v w : ℝ}
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hF0 : 0 ≤ F)
    (hF : F ≤ Real.exp (A * (R : ℝ) * L))
    (hv : v ≤ Real.exp (-(A + 6) * (R : ℝ) * L))
    (hw : w ≤ Real.exp (-(A + 6) * (R : ℝ) * L)) :
    F * (v + w) ≤ Real.exp (-4 * (R : ℝ)) := by
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have htwo : (2 : ℝ) ≤ Real.exp (2 * (R : ℝ)) := by
    calc
      2 ≤ 2 * (R : ℝ) + 1 := by linarith
      _ ≤ _ := Real.add_one_le_exp _
  calc
    _ ≤ F * (2 * Real.exp (-(A + 6) * (R : ℝ) * L)) :=
      mul_le_mul_of_nonneg_left (by linarith) hF0
    _ ≤ Real.exp (A * (R : ℝ) * L) *
        (2 * Real.exp (-(A + 6) * (R : ℝ) * L)) :=
      mul_le_mul_of_nonneg_right hF (by positivity)
    _ = 2 * Real.exp (-6 * (R : ℝ) * L) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (2 * (R : ℝ)) * Real.exp (-6 * (R : ℝ) * L) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (2 * (R : ℝ) + -6 * (R : ℝ) * L) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem overlap_decay_linear {D R K : ℕ} {L u α B : ℝ}
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hL : 1 ≤ L)
    (hK : 200 * (12 + 6 * (D : ℝ)) * L ≤ K)
    (hu : 0 ≤ u) (huL : u ≤ Real.exp L)
    (hα : 0 ≤ α) (hαL : α ≤ Real.exp (-(1 / 2 : ℝ)))
    (hB : 0 ≤ B) (hBL : B ≤ Real.exp ((R : ℝ) * L)) :
    (4 * (R : ℝ) + 1) * (1 + ((2 * D * R + D : ℕ) : ℝ) * u ^ (2 * D * R + D)) *
      (Real.exp (-((D * (K * R - 1) : ℕ) : ℝ) / 50) +
        B * α ^ (D * (K * R - 1) / 10)) ≤ Real.exp (-4 * (R : ℝ)) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hK40 : 40 ≤ K := by
    have hk : (40 : ℝ) ≤ K := by nlinarith
    exact_mod_cast hk
  obtain ⟨hlow, hm⟩ := separation_arith hD hR hK40
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hKR := mul_le_mul_of_nonneg_right hK hR0
  apply two_terms_decay hR hL (by positivity) (enlargement_factor hD hR hL hu huL)
  · apply Real.exp_le_exp.mpr
    nlinarith [hKR]
  · calc
      B * α ^ (D * (K * R - 1) / 10) ≤
          Real.exp ((R : ℝ) * L) * Real.exp (-(1 / 2 : ℝ) *
            ((D * (K * R - 1) / 10 : ℕ) : ℝ)) :=
        mul_le_mul hBL (pow_exp_bound hα hαL _) (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((R : ℝ) * L + -(1 / 2 : ℝ) *
            ((D * (K * R - 1) / 10 : ℕ) : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [hKR]

theorem overlap_decay_sublinear {D R K s : ℕ} {L δ u α B : ℝ}
    (hD : 1 ≤ D) (hR : 1 ≤ R) (hL : 1 ≤ L) (hδ : 0 < δ)
    (hδL : 8 ≤ δ * L) (hK40 : 40 ≤ K)
    (hK : 100 * (12 + 6 * (D : ℝ)) ≤ δ * K)
    (hs : D * (K * R - 1) ≤ s)
    (hu : 0 ≤ u) (huL : u ≤ Real.exp L)
    (hα : 0 ≤ α) (hαL : α ≤ Real.exp (-δ * L))
    (hB : 0 ≤ B) (hBL : B ≤ Real.exp ((R : ℝ) * L)) :
    (4 * (R : ℝ) + 1) * (1 + ((2 * D * R + D : ℕ) : ℝ) * u ^ (2 * D * R + D)) *
      (B * α ^ (D * (K * R - 1) / 10) + (2 : ℝ) ^ s * α ^ (s / 3)) ≤
        Real.exp (-4 * (R : ℝ)) := by
  obtain ⟨hlow, hm⟩ := separation_arith hD hR hK40
  have hsr : ((D * (K * R - 1) : ℕ) : ℝ) ≤ s := by exact_mod_cast hs
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hKr : (40 : ℝ) ≤ K := by exact_mod_cast hK40
  have hs12 : 12 ≤ s := by
    have : (12 : ℝ) ≤ s := by nlinarith
    exact_mod_cast this
  have hfloorNat : s ≤ 3 * (s / 3) + 2 := by omega
  have hfloor : (s : ℝ) ≤ 3 * ((s / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast hfloorNat
  have hsf : (s : ℝ) / 4 ≤ ((s / 3 : ℕ) : ℝ) := by
    have hsreal : (12 : ℝ) ≤ s := by exact_mod_cast hs12
    linarith
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hL0 : 0 ≤ L := by linarith
  have hδL0 : 0 ≤ δ * L := by linarith
  have hkm := mul_le_mul_of_nonneg_right hK (mul_nonneg hR0 hL0)
  have hmm := mul_le_mul_of_nonneg_left hm hδL0
  have hsm := mul_le_mul_of_nonneg_left (hlow.trans hsr) hδL0
  apply two_terms_decay hR hL (by positivity) (enlargement_factor hD hR hL hu huL)
  · calc
      B * α ^ (D * (K * R - 1) / 10) ≤
          Real.exp ((R : ℝ) * L) * Real.exp (-δ * L *
            ((D * (K * R - 1) / 10 : ℕ) : ℝ)) :=
        mul_le_mul hBL (pow_exp_bound hα hαL _) (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((R : ℝ) * L + -δ * L *
            ((D * (K * R - 1) / 10 : ℕ) : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [hmm, hkm]
  · have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      norm_num at this ⊢
      exact this
    have hf := mul_le_mul_of_nonneg_left hsf hδL0
    have hlarge := mul_le_mul_of_nonneg_right hδL (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    calc
      (2 : ℝ) ^ s * α ^ (s / 3) ≤
          Real.exp (1 * (s : ℝ)) * Real.exp (-δ * L * ((s / 3 : ℕ) : ℝ)) :=
        mul_le_mul (pow_exp_bound (by norm_num) htwo s) (pow_exp_bound hα hαL _)
          (by positivity) (Real.exp_pos _).le
      _ = Real.exp (1 * (s : ℝ) + -δ * L * ((s / 3 : ℕ) : ℝ)) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [hf, hlarge, hsm, hkm]

theorem radius_lower (n : ℕ) (σ : ℝ) (i : ℕ) :
    1 ≤ hdScaleRadius n σ i ∧ Real.log (n : ℝ) ^ 2 ≤ (hdScaleRadius n σ i : ℝ) := by
  have hM : 0 < hdScaleMultiplier n σ := by unfold hdScaleMultiplier; omega
  have hpow : 0 < hdScaleMultiplier n σ ^ i := pow_pos hM i
  have hbase : 1 ≤ heightBaseRadius n := by unfold heightBaseRadius; omega
  have hbR : heightBaseRadius n ≤ hdScaleRadius n σ i :=
    Nat.le_mul_of_pos_left _ hpow
  refine ⟨hbase.trans hbR, ?_⟩
  calc
    _ ≤ (⌈Real.log (n : ℝ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (heightBaseRadius n : ℝ) := by
      apply Nat.cast_le.mpr
      exact Nat.le_max_right 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
    _ ≤ _ := by exact_mod_cast hbR

theorem radius_upper {n i : ℕ} {σ ζ : ℝ} (hn : 2 ≤ n)
    (hζ : 0 < ζ ∧ ζ < 1) (hi : i < hdScaleIndex n σ ζ) :
    (hdScaleRadius n σ i : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hpow1 : 1 ≤ (n : ℝ) ^ (1 - ζ) :=
    Real.one_le_rpow hn1 (by linarith [hζ.2])
  have hlt := (hdScaleIndex_spec n σ ζ).2 i hi
  have hltR : (hdScaleRadius n σ i : ℝ) < (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) :=
    by exact_mod_cast hlt
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le (1 - ζ))
  linarith

theorem radius_environment_eventually (σ C_d : ℝ) :
    ∃ N : ℕ, ∀ n d i : ℕ, N ≤ n → (d : ℝ) ≤ C_d * n →
      2 ≤ n ∧ 2 ≤ Real.log (n : ℝ) ∧ C_d + 1 ≤ (n : ℝ) ∧
      ((d + 1 : ℕ) : ℝ) ≤ Real.exp (hdScaleRadius n σ i : ℝ) := by
  obtain ⟨Nlog, hl⟩ := exists_nat_log_ge 2
  obtain ⟨Npow, hp⟩ := exists_nat_rpow_ge (e := (1 : ℝ)) (C := C_d + 1) (by norm_num)
  refine ⟨max 2 (max Nlog Npow), ?_⟩
  intro n d i hn hd
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hlog : 2 ≤ Real.log (n : ℝ) := hl n (by omega)
  have hpow : C_d + 1 ≤ (n : ℝ) := by simpa using hp n (by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  refine ⟨hn2, hlog, hpow, ?_⟩
  have hdim : ((d + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc
    _ ≤ (n : ℝ) ^ 2 := hdim
    _ = Real.exp (2 * Real.log (n : ℝ)) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hn0]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hR := (radius_lower n σ i).2
      nlinarith

end HypercubeRamsey.Lane_sol_hs_ovl
