import HypercubeRamsey.S06.OddLoads_sol_s06_loadA

namespace HypercubeRamsey.Lane_sol_s06_loadD

open OAI.HypercubeRamsey Classical Filter
open HypercubeRamsey.S06
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

private theorem geometric_tail_le (r : ℝ) (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) (m : ℕ) :
    ∑ q ∈ Finset.range m, r ^ (q + 1) ≤ 2 * r := by
  have hS : 0 ≤ ∑ q ∈ Finset.range m, r ^ q :=
    Finset.sum_nonneg fun q _ => pow_nonneg hr q
  have hid := geom_sum_mul_neg r m
  have hpow := pow_nonneg hr m
  have hmul := mul_le_mul_of_nonneg_left hr' hS
  have hbound : ∑ q ∈ Finset.range m, r ^ q ≤ 2 := by nlinarith
  calc
    _ = r * ∑ q ∈ Finset.range m, r ^ q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [pow_succ]
      ring
    _ ≤ r * 2 := mul_le_mul_of_nonneg_left hbound hr
    _ = _ := by ring

theorem severity_le (x : CubeVertex n) : X.g.L.severity x ≤ X.m := by
  unfold ChunkLayout6.severity
  exact (Finset.card_filter_le (Finset.univ : Finset (Fin X.g.L.m))
    (fun i => Nat.dist (2 * X.g.L.fineCount x i) X.g.L.fineLength ≤ 11)).trans
      (by simp [Ctx6.m])

theorem evenType_u_le (x : CubeVertex n) :
    (X.evenType x).u ≤ X.g.L.severity x + 1 := by
  unfold Ctx6.evenType makeType6
  split_ifs
  · simp only [Type6.u, Type6.mode, Type6.sev, sevFin6]
    exact Nat.add_le_add_right (min_le_left _ _) 1
  · simp [Type6.u, Type6.mode]

theorem evenType_u_zero (x : CubeVertex n) (hx : X.g.L.severity x = 0) :
    (X.evenType x).u = 1 := by
  simp [Ctx6.evenType, makeType6, hx, Type6.u, Type6.mode, Type6.sev, sevFin6]

/-- A severity tail controls the entire positive-severity contribution, including high rows. -/
theorem positive_severity_average_le (f : CubeVertex n → ℝ) (hK : 0 ≤ K)
    (hcap : ∀ x, f x ≤ (n : ℝ) ^ (d₂ * (X.g.L.severity x + 1)) * K)
    (hn : 1 ≤ n) (hsmall : (n : ℝ) ^ (d₂ - 13 / 100) ≤ 1 / 2) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
      (if 0 < X.g.L.severity x then f x else 0) ≤
        2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hterm (x : CubeVertex n) :
      (if 0 < X.g.L.severity x then f x else 0) ≤
        ∑ q ∈ Finset.range X.m,
          if q + 1 ≤ X.g.L.severity x then (n : ℝ) ^ (d₂ * (q + 2)) * K else 0 := by
    by_cases hx : 0 < X.g.L.severity x
    · rw [if_pos hx]
      let q := X.g.L.severity x - 1
      have hq : q ∈ Finset.range X.m := by
        have := severity_le X x
        simp only [Finset.mem_range]
        dsimp [q]
        omega
      have hqeq : q + 1 = X.g.L.severity x := by dsimp [q]; omega
      calc
        f x ≤ (n : ℝ) ^ (d₂ * (X.g.L.severity x + 1)) * K := hcap x
        _ = (if q + 1 ≤ X.g.L.severity x then (n : ℝ) ^ (d₂ * (q + 2)) * K else 0) := by
          rw [if_pos (by omega)]
          have heq : (X.g.L.severity x : ℝ) + 1 = (q : ℝ) + 2 := by
            exact_mod_cast (by omega : X.g.L.severity x + 1 = q + 2)
          rw [heq]
        _ ≤ _ := by
          apply Finset.single_le_sum (f := fun q : ℕ =>
            if q + 1 ≤ X.g.L.severity x then (n : ℝ) ^ (d₂ * (q + 2)) * K else 0) ?_ hq
          intro q _
          split_ifs <;> positivity
    · rw [if_neg hx]
      exact Finset.sum_nonneg fun q _ => by split_ifs <;> positivity
  have htail (q : ℕ) (hq : q ∈ Finset.range X.m) :
      ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
        (if q + 1 ≤ X.g.L.severity x then (n : ℝ) ^ (d₂ * (q + 2)) * K else 0) ≤
          K * (n : ℝ) ^ d₂ * ((n : ℝ) ^ (d₂ - 13 / 100)) ^ (q + 1) := by
    have hcount := X.g.severity_tail (q + 1) (by omega)
      (by simpa [Ctx6.m] using (Nat.succ_le_of_lt (Finset.mem_range.mp hq)))
    have hcount' : ((2 : ℝ) ^ n)⁻¹ *
        ((Finset.univ.filter fun x : CubeVertex n => q + 1 ≤ X.g.L.severity x).card : ℝ) ≤
          (n : ℝ) ^ (-(13 / 100 : ℝ) * (q + 1)) := by
      simpa [div_eq_mul_inv, mul_comm] using hcount
    calc
      _ = (((2 : ℝ) ^ n)⁻¹ *
          ((Finset.univ.filter fun x : CubeVertex n => q + 1 ≤ X.g.L.severity x).card : ℝ)) *
            ((n : ℝ) ^ (d₂ * (q + 2)) * K) := by
        rw [← Finset.sum_filter]
        simp
        ring
      _ ≤ (n : ℝ) ^ (-(13 / 100 : ℝ) * (q + 1)) *
            ((n : ℝ) ^ (d₂ * (q + 2)) * K) :=
          mul_le_mul_of_nonneg_right hcount' (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, mul_assoc,
          ← Real.rpow_add hnpos]
        rw [mul_comm K, ← mul_assoc, ← Real.rpow_add hnpos]
        congr 2 <;> push_cast <;> ring
  calc
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n, ∑ q ∈ Finset.range X.m,
        if q + 1 ≤ X.g.L.severity x then (n : ℝ) ^ (d₂ * (q + 2)) * K else 0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hterm x) (by positivity)
    _ = ∑ q ∈ Finset.range X.m, ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
        if q + 1 ≤ X.g.L.severity x then (n : ℝ) ^ (d₂ * (q + 2)) * K else 0 := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ q ∈ Finset.range X.m,
        K * (n : ℝ) ^ d₂ * ((n : ℝ) ^ (d₂ - 13 / 100)) ^ (q + 1) :=
      Finset.sum_le_sum htail
    _ = (K * (n : ℝ) ^ d₂) * ∑ q ∈ Finset.range X.m,
        ((n : ℝ) ^ (d₂ - 13 / 100)) ^ (q + 1) := by rw [Finset.mul_sum]
    _ ≤ (K * (n : ℝ) ^ d₂) * (2 * (n : ℝ) ^ (d₂ - 13 / 100)) :=
      mul_le_mul_of_nonneg_left
        (geometric_tail_le _ (by positivity) hsmall _) (by positivity)
    _ = _ := by
      rw [show 2 * d₂ - 13 / 100 = d₂ + (d₂ - 13 / 100) by ring, Real.rpow_add hnpos]
      ring

/-- The rows to which the coarse-stage moments will be applied. -/
def InteriorZero (x : CubeVertex n) : Prop :=
  ¬ X.g.L.boundary x ∧ X.g.L.severity x = 0

/-- Boundary rows at severity zero and all positive severities have a vanishing total cap. -/
theorem outside_interiorZero_average_le (f : CubeVertex n → ℝ) (hK : 0 ≤ K)
    (hcap : ∀ x, f x ≤ (n : ℝ) ^ (d₂ * (X.g.L.severity x + 1)) * K)
    (hn : 1 ≤ n) (hsmall : (n : ℝ) ^ (d₂ - 13 / 100) ≤ 1 / 2) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
      (if InteriorZero X x then 0 else f x) ≤
        K * (n : ℝ) ^ (d₂ - 1 / 20) + 2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpoint (x : CubeVertex n) :
      (if InteriorZero X x then 0 else f x) ≤
        (if X.g.L.boundary x then (n : ℝ) ^ d₂ * K else 0) +
        (if 0 < X.g.L.severity x then f x else 0) := by
    by_cases hx : 0 < X.g.L.severity x
    · have hx' : X.g.L.severity x ≠ 0 := by omega
      simp only [InteriorZero, hx', and_false, ite_false, hx, ite_true]
      have hb : 0 ≤ (if X.g.L.boundary x then (n : ℝ) ^ d₂ * K else 0) := by
        split_ifs <;> positivity
      linarith
    · have hs : X.g.L.severity x = 0 := by omega
      by_cases hb : X.g.L.boundary x
      · simpa [InteriorZero, hs, hb] using hcap x
      · simp [InteriorZero, hs, hb]
  have hboundary : ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
      (if X.g.L.boundary x then (n : ℝ) ^ d₂ * K else 0) ≤
        K * (n : ℝ) ^ (d₂ - 1 / 20) := by
    calc
      _ = (((Finset.univ.filter X.g.L.boundary).card : ℝ) / (2 : ℝ) ^ n) *
          ((n : ℝ) ^ d₂ * K) := by
        rw [← Finset.sum_filter]
        simp
        ring
      _ ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) * ((n : ℝ) ^ d₂ * K) :=
        mul_le_mul_of_nonneg_right X.g.boundary_fraction (by positivity)
      _ = _ := by
        rw [← mul_assoc, ← Real.rpow_add hnpos,
          show -(1 / 20 : ℝ) + d₂ = d₂ - 1 / 20 by ring]
        ring
  calc
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
        ((if X.g.L.boundary x then (n : ℝ) ^ d₂ * K else 0) +
          (if 0 < X.g.L.severity x then f x else 0)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpoint x) (by positivity)
    _ = ((2 : ℝ) ^ n)⁻¹ * (∑ x : CubeVertex n,
          if X.g.L.boundary x then (n : ℝ) ^ d₂ * K else 0) +
        ((2 : ℝ) ^ n)⁻¹ * (∑ x : CubeVertex n,
          if 0 < X.g.L.severity x then f x else 0) := by rw [Finset.sum_add_distrib, mul_add]
    _ ≤ _ := add_le_add hboundary (positive_severity_average_le X f hK hcap hn hsmall)

/-- A single size cutoff controls the geometric ratio and the deterministic exceptional contribution. -/
theorem outside_interiorZero_eventually_small (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ (n : ℝ) ^ (d₂ - 13 / 100) ≤ 1 / 2 ∧
      K * (n : ℝ) ^ (d₂ - 1 / 20) + 2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100) ≤ 1 := by
  have hlim (e : ℝ) (he : e < 0) :
      Tendsto (fun n : ℕ => (n : ℝ) ^ e) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hratio := (hlim (d₂ - 13 / 100) (by norm_num [d₂])).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hsum := ((hlim (d₂ - 1 / 20) (by norm_num [d₂])).const_mul K).add
    ((hlim (2 * d₂ - 13 / 100) (by norm_num [d₂])).const_mul (2 * K))
  have hsum0 : Tendsto (fun n : ℕ =>
      K * (n : ℝ) ^ (d₂ - 1 / 20) + 2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100)) atTop (nhds 0) := by
    simpa using hsum
  have hbound : ∀ᶠ n : ℕ in atTop,
      K * (n : ℝ) ^ (d₂ - 1 / 20) + 2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100) < 1 := by
    exact hsum0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 1, hratio, hbound] with n hn hr hb
  exact ⟨hn, hr.le, hb.le⟩

/-- The hidden raw mean, written here without importing the load declarations. -/
def evenMean (b : X.Base) (x : CubeVertex n) (a : Fin N) : ℝ :=
  (X.hidLaw b).expect fun z => Lane_sol_s06_loadA.gatedTagMixture X (b, z) (X.evenType x) a

def evenLoad (b : X.Base) (x : CubeVertex n) (a : Fin N) : ℝ :=
  if IsEvenRole x then evenMean X b x a else 0

theorem baseSupp_keysSupp (b : X.Base) (hb : X.BaseSupp b) (S : Finset X.Key) : X.KeysSupp b S := by
  refine ⟨hb.1, ?_, ?_⟩
  · intro u _
    apply hb.2.1 u
    exact Finset.mem_image.mpr ⟨(u, .interior), Finset.mem_univ _, rfl⟩
  · intro s _
    exact hb.2.2 s (Finset.mem_univ _)

theorem evenLoad_cap (hDom : X.Step2Dom) (b : X.Base) (hb : X.BaseSupp b)
    (hn : 1 ≤ n) (x : CubeVertex n) (a : Fin N) :
    evenLoad X b x a ≤ (n : ℝ) ^ (d₂ * (X.g.L.severity x + 1)) * K := by
  have hK : 0 ≤ K := (mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (M.Λ_nonneg i) ((M.μ i).nonneg a))).trans (X.hBal.1 a)
  by_cases hx : IsEvenRole x
  · rw [evenLoad, if_pos hx]
    have hcap := Lane_sol_s06_loadA.gatedTagMixture_hiddenMean_cap X hDom b (X.evenType x)
      (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩)
      (baseSupp_keysSupp X b hb _) a
    refine hcap.trans (mul_le_mul_of_nonneg_right ?_ hK)
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast evenType_u_le X x) (by norm_num [d₂])
  · simp only [evenLoad, hx, ite_false]
    positivity

theorem outside_evenLoad_average_le (hDom : X.Step2Dom) (b : X.Base) (hb : X.BaseSupp b)
    (hn : 1 ≤ n) (hsmall : (n : ℝ) ^ (d₂ - 13 / 100) ≤ 1 / 2) (a : Fin N) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
      (if InteriorZero X x then 0 else evenLoad X b x a) ≤
        K * (n : ℝ) ^ (d₂ - 1 / 20) + 2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100) := by
  apply outside_interiorZero_average_le X _ _ (fun x => evenLoad_cap X hDom b hb hn x a) hn hsmall
  exact (mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (M.Λ_nonneg i) ((M.μ i).nonneg a))).trans (X.hBal.1 a)

theorem outside_evenMean_average_eq (b : X.Base) (a : Fin N) (hn : 1 ≤ n) :
    ((evenRoleSet n).card : ℝ)⁻¹ * ∑ x ∈ evenRoleSet n,
      (if InteriorZero X x then 0 else evenMean X b x a) =
        2 * (((2 : ℝ) ^ n)⁻¹ * ∑ x : CubeVertex n,
          if InteriorZero X x then 0 else evenLoad X b x a) := by
  have hsum : (∑ x ∈ evenRoleSet n, if InteriorZero X x then 0 else evenMean X b x a) =
      ∑ x : CubeVertex n, if InteriorZero X x then 0 else evenLoad X b x a := by
    rw [evenRoleSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : IsEvenRole x <;> by_cases hi : InteriorZero X x <;> simp [evenLoad, hx, hi]
  have hcard : (evenRoleSet n).card = 2 ^ (n - 1) := (parity_class_card (by omega : 0 < n)).1
  have hcardR : ((evenRoleSet n).card : ℝ) = (2 : ℝ) ^ (n - 1) := by exact_mod_cast hcard
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega]
    rw [pow_succ]
    ring
  rw [hsum, hcardR, hpow]
  field_simp

theorem outside_evenMean_average_le_two (hDom : X.Step2Dom) (b : X.Base) (hb : X.BaseSupp b)
    (hn : 1 ≤ n) (hsmall : (n : ℝ) ^ (d₂ - 13 / 100) ≤ 1 / 2)
    (hbound : K * (n : ℝ) ^ (d₂ - 1 / 20) + 2 * K * (n : ℝ) ^ (2 * d₂ - 13 / 100) ≤ 1)
    (a : Fin N) :
    ((evenRoleSet n).card : ℝ)⁻¹ * ∑ x ∈ evenRoleSet n,
      (if InteriorZero X x then 0 else evenMean X b x a) ≤ 2 := by
  rw [outside_evenMean_average_eq X b a hn]
  have h := (outside_evenLoad_average_le X hDom b hb hn hsmall a).trans hbound
  linarith

end
end HypercubeRamsey.Lane_sol_s06_loadD
