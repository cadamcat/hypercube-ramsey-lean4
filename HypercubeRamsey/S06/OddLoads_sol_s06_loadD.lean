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

/-- Agreement of the base variables at a finite list of keys. -/
def BaseAgree (S : Finset X.Key) (b b' : X.Base) : Prop :=
  b.1 = b'.1 ∧ (∀ u ∈ X.binsOf S, b.2.1 u = b'.2.1 u) ∧
    ∀ k ∈ S, b.2.2 k = b'.2.2 k

theorem baseAgree_mono {S T : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (hTS : T ⊆ S) : BaseAgree X T b b' := by
  refine ⟨h.1, ?_, fun k hk => h.2.2 k (hTS hk)⟩
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
  exact h.2.1 k.1 (Finset.mem_image.mpr ⟨k, hTS hk, rfl⟩)

theorem baseAgree_withTag {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (s : X.Key) (i : X.ι) :
    BaseAgree X S (X.withTag b s i) (X.withTag b' s i) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro k hk
  change Function.update b.2.2 s i k = Function.update b'.2.2 s i k
  by_cases hks : k = s
  · subst k
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hks]
    exact h.2.2 k hk

theorem hidPost_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (k : X.Key) (hC : X.C k ⊆ S) :
    X.hidPost b k = X.hidPost b' k := by
  unfold Ctx6.hidPost
  congr 1
  funext y
  exact S06.Lane_sol_s06_steps1.hidWeight_local X k _ (fun _ hk => hk) b b'
    (fun _ => h.1) (fun _ u hu => h.2.1 u (Finset.image_subset_image hC hu))
    (fun s hs => h.2.2 s (hC hs)) y

theorem hidPostDel_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (k s : X.Key) (hC : X.C k ⊆ S) :
    X.hidPostDel b k s = X.hidPostDel b' k s := by
  unfold Ctx6.hidPostDel
  congr 1
  funext y
  exact S06.Lane_sol_s06_steps1.hidWeight_local X k _ (Finset.erase_subset _ _) b b'
    (fun _ => h.1) (fun _ u hu => h.2.1 u (Finset.image_subset_image hC hu))
    (fun t ht => h.2.2 t (hC (Finset.mem_erase.mp ht).2)) y

theorem typeKeys_obs (β : X.Ty) (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
    X.C ℓ.1 ⊆ X.typeKeys β := by
  intro k hk
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hk⟩)

theorem tagGate_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (i : X.ι) :
    X.tagGate b β i ↔ X.tagGate b' β i := by
  have hrep (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
      X.hidPostRep b ℓ.1 β.key i = X.hidPostRep b' ℓ.1 β.key i :=
    hidPost_eq_of_baseAgree X (baseAgree_withTag X h β.key i) ℓ.1 (typeKeys_obs X β ℓ hℓ)
  have hdel (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
      X.hidPostDel b ℓ.1 β.key = X.hidPostDel b' ℓ.1 β.key :=
    hidPostDel_eq_of_baseAgree X h ℓ.1 β.key (typeKeys_obs X β ℓ hℓ)
  unfold Ctx6.tagGate
  constructor <;> intro hg ℓ hℓ y
  · rw [← hrep ℓ hℓ, ← hdel ℓ hℓ]
    exact hg ℓ hℓ y
  · rw [hrep ℓ hℓ, hdel ℓ hℓ]
    exact hg ℓ hℓ y

theorem tagLawAt_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (k : X.Key) (hk : k ∈ S) :
    X.tagLawAt (X.parOf b) k = X.tagLawAt (X.parOf b') k := by
  have hA := h.2.1 k.1 (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  change X.tagLawAt (b.1, b.2.1) k = X.tagLawAt (b'.1, b'.2.1) k
  rw [← h.1]
  exact Lane_sol_s06_loadA.tagLawAt_bin_local X b.1 b.2.1 b'.2.1 k hA

theorem tagWeight_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) (S : Finset X.HKey)
    (hS : S ⊆ β.obs) (i : X.ι) :
    X.tagWeight (b, z) β S i = X.tagWeight (b', z) β S i := by
  have htag := tagLawAt_eq_of_baseAgree X h β.key (Finset.mem_insert_self _ _)
  have hgate := tagGate_eq_of_baseAgree X β h i
  unfold Ctx6.tagWeight
  simp only [htag, hgate]
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  have hC := typeKeys_obs X β ℓ (hS hℓ)
  have hrep := hidPost_eq_of_baseAgree X (baseAgree_withTag X h β.key i) ℓ.1 hC
  have hdel := hidPostDel_eq_of_baseAgree X h ℓ.1 β.key hC
  change safeRatio6 ((X.hidPost (X.withTag b β.key i) ℓ.1).w (z ℓ))
      ((X.hidPostDel b ℓ.1 β.key).w (z ℓ)) = _
  rw [hrep, hdel]
  rfl

theorem tagPost_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) (S : Finset X.HKey)
    (hS : S ⊆ β.obs) : X.tagPost (b, z) β S = X.tagPost (b', z) β S := by
  unfold Ctx6.tagPost
  congr 1
  funext i
  exact tagWeight_eq_of_baseAgree X β h z S hS i

theorem step2Tests_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) :
    X.Step2Tests (b, z) β ↔ X.Step2Tests (b', z) β := by
  have hmass (S : Finset X.HKey) (hS : S ⊆ β.obs) :
      X.tagMass (b, z) β S = X.tagMass (b', z) β S := by
    unfold Ctx6.tagMass
    exact Finset.sum_congr rfl fun i _ => tagWeight_eq_of_baseAgree X β h z S hS i
  have hfull := hmass β.obs (fun _ hℓ => hℓ)
  have hdel (ℓ : X.HKey) := hmass (β.obs.erase ℓ) (Finset.erase_subset _ _)
  simp only [Ctx6.Step2Tests, hfull, hdel]

theorem gatedTagMixture_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) (a : Fin N) :
    Lane_sol_s06_loadA.gatedTagMixture X (b, z) β a =
      Lane_sol_s06_loadA.gatedTagMixture X (b', z) β a := by
  have hI := h.2.2 β.key (Finset.mem_insert_self _ _)
  have hgate := tagGate_eq_of_baseAgree X β h (b'.2.2 β.key)
  have htests := step2Tests_eq_of_baseAgree X β h z
  have hpost := tagPost_eq_of_baseAgree X β h z β.obs (fun _ hℓ => hℓ)
  simp only [Lane_sol_s06_loadA.gatedTagMixture, hI, hgate, htests, Ctx6.Tβ, hpost]

/-- A hidden raw mean reads the candidates and tags in the type's finite key window. -/
theorem evenMean_eq_of_baseAgree (x : CubeVertex n) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys (X.evenType x)) b b') (a : Fin N) :
    evenMean X b x a = evenMean X b' x a := by
  let β := X.evenType x
  let f (z : X.Hid) := Lane_sol_s06_loadA.gatedTagMixture X (b', z) β a
  have hdep : FinProb.DependsOn f β.obs := by
    intro z z' hz
    have htests := Lane_q_s06_loads.step2Tests_congr_hid X b' z z' β hz
    have hpost := _root_.Lane_q_s06_loads.Tβ_congr_hid X b' z z' β hz
    simp only [f, Lane_sol_s06_loadA.gatedTagMixture, htests, hpost]
  have hkernel (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
      X.hidPost b ℓ.1 = X.hidPost b' ℓ.1 :=
    hidPost_eq_of_baseAgree X h ℓ.1 (typeKeys_obs X β ℓ hℓ)
  unfold evenMean
  have hfun : (fun z => Lane_sol_s06_loadA.gatedTagMixture X (b, z) β a) = f := by
    funext z
    exact gatedTagMixture_eq_of_baseAgree X β h z a
  change (FinProb.pi (fun ℓ : X.HKey => X.hidPost b ℓ.1)).expect _ =
    (FinProb.pi (fun ℓ : X.HKey => X.hidPost b' ℓ.1)).expect f
  rw [hfun]
  exact S06.Lane_sol_s06_steps1.pi_expect_congr_on _ _ β.obs f (fun _ => X.y₀) hdep hkernel

def evenBinScope (x : CubeVertex n) : Finset X.Bin := X.binsOf (X.typeKeys (X.evenType x))

theorem evenMean_depends_on_bins (v : Fin N) (x : CubeVertex n) (a : Fin N) :
    FinProb.DependsOn (fun z : X.Bin → Lane_sol_s06_loadA.BinData X =>
      evenMean X (v, (Lane_sol_s06_loadA.coarseBinEquiv X).symm z) x a) (evenBinScope X x) := by
  intro z z' hz
  apply evenMean_eq_of_baseAgree X x (a := a)
  refine ⟨rfl, ?_, ?_⟩
  · intro u hu
    exact congrArg Prod.fst (hz u hu)
  · intro k hk
    exact congrArg (fun p : Lane_sol_s06_loadA.BinData X => p.2 k.2)
      (hz k.1 (Finset.mem_image.mpr ⟨k, hk, rfl⟩))

theorem evenMean_nonneg (b : X.Base) (x : CubeVertex n) (a : Fin N) : 0 ≤ evenMean X b x a := by
  unfold evenMean FinProb.expect
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg ((X.hidLaw b).nonneg z) (Lane_sol_s06_loadA.gatedTagMixture_nonneg X (b, z) _ a)

theorem evenMean_product_raw_le (v : Fin N) (hv : 0 < X.initLaw.w v)
    (U : Finset (CubeVertex n)) (hInterior : ∀ x ∈ U, (X.evenType x).key.2 = .interior)
    (hdis : ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → Disjoint (evenBinScope X x) (evenBinScope X x'))
    (a : Fin N) :
    (X.coarseLaw v).expect (fun c => ∏ x ∈ U, evenMean X (v, c) x a) ≤ (20 * K / c₁) ^ U.card := by
  let F (x : CubeVertex n) (z : X.Bin → Lane_sol_s06_loadA.BinData X) :=
    evenMean X (v, (Lane_sol_s06_loadA.coarseBinEquiv X).symm z) x a
  have hfactor := _root_.Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint
    (Lane_sol_s06_loadA.binLaw X v) U (evenBinScope X) F
    (fun x => evenMean_depends_on_bins X v x a) hdis
  have hmean (x : CubeVertex n) (hx : x ∈ U) :
      (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).expect (F x) ≤ 20 * K / c₁ := by
    rw [← Lane_sol_s06_loadA.coarseLaw_expect X v (fun c => evenMean X (v, c) x a)]
    exact Lane_sol_s06_loadA.interior_gatedTagMixture_mean_le X v (X.evenType x) (hInterior x hx) hv a
  have hnonneg (x : CubeVertex n) :
      0 ≤ (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).expect (F x) := by
    unfold FinProb.expect
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg ((FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).nonneg z) (evenMean_nonneg X _ x a)
  rw [Lane_sol_s06_loadA.coarseLaw_expect X v]
  change (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).expect (fun z => ∏ x ∈ U, F x z) ≤ _
  rw [hfactor]
  calc
    _ ≤ ∏ _x ∈ U, 20 * K / c₁ :=
      Finset.prod_le_prod₀ (fun x _ => hnonneg x) (fun x hx => hmean x hx)
    _ = _ := by simp only [Finset.prod_const]

theorem baseAgree_withPar {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (nm : ParentName6 X.Bin) (ξ : Fin N) :
    BaseAgree X S (X.withPar b nm ξ) (X.withPar b' nm ξ) := by
  cases nm with
  | initial => exact ⟨rfl, h.2.1, h.2.2⟩
  | candidate w =>
    refine ⟨h.1, ?_, h.2.2⟩
    intro u hu
    change Function.update b.2.1 w ξ u = Function.update b'.2.1 w ξ u
    by_cases huw : u = w
    · subst u
      simp only [Function.update_self]
    · simp only [Function.update_of_ne huw]
      exact h.2.1 u hu

theorem step1OK_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (k : X.Key) (hC : X.C k ⊆ S) :
    X.Step1OK b k ↔ X.Step1OK b' k := by
  have hpost := hidPost_eq_of_baseAgree X h k hC
  have hdel (s : X.Key) := hidPostDel_eq_of_baseAgree X h k s hC
  simp only [Ctx6.Step1OK, Ctx6.Step1Cap, Ctx6.Step1Del, hpost, hdel]

theorem parentValues_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (k : X.Key) (hk : k ∈ S) :
    (X.parOf b).val (primaryName6 k) = (X.parOf b').val (primaryName6 k) ∧
      (X.parOf b).val (otherPrimaryName6 k) = (X.parOf b').val (otherPrimaryName6 k) := by
  have hA := h.2.1 k.1 (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  cases hf : k.2 <;> simp [Ctx6.parOf, Par6.val, primaryName6, otherPrimaryName6, hf, h.1, hA]

theorem reqNameValues_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (β : X.Ty) (hk : β.key ∈ S) (z : X.Hid) :
    ∀ nm ∈ reqNames6 β, X.varVal (b, z) nm = X.varVal (b', z) nm := by
  intro nm hnm
  cases nm with
  | hid ℓ => rfl
  | par p =>
    have hp : p = primaryName6 β.key ∨ p = otherPrimaryName6 β.key := by
      by_cases hm : β.mode = .high
      · simpa [reqNames6, hm] using hnm
      · exact Or.inl (by simpa [reqNames6, hm] using hnm)
    have hv := parentValues_eq_of_baseAgree X h β.key hk
    rcases hp with hp | hp
    · subst p
      exact hv.1
    · subst p
      exact hv.2

theorem labelLaw_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (β : X.Ty) (hk : β.key ∈ S) (z : X.Hid)
    (A : Finset X.Name) (hA : A ⊆ reqNames6 β) (i : X.ι) :
    X.labelLaw (b, z) A i = X.labelLaw (b', z) A i := by
  exact _root_.Lane_q_s06_loads.labelLaw_congr_varVal X (b, z) (b', z) A i
    (fun nm hnm => reqNameValues_eq_of_baseAgree X h β hk z nm (hA hnm))

theorem tupleLaw_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) :
    X.tupleLaw (b, z) β = X.tupleLaw (b', z) β := by
  have htag := tagPost_eq_of_baseAgree X β h z β.obs (fun _ hℓ => hℓ)
  unfold Ctx6.tupleLaw Ctx6.Tβ
  rw [htag]
  exact _root_.Lane_q_s06_loads.tupleLawOn_congr_varVal X (b, z) (b', z)
    (reqNames6 β) _
    (reqNameValues_eq_of_baseAgree X h β (Finset.mem_insert_self _ _) z)

variable {Id : Type} [Fintype Id] [DecidableEq Id]

def s3BaseKeys (b : X.State) (D : Finset (Id × X.Ty)) : Finset X.Key :=
  X.C (X.tgt b).1 ∪ X.locKeys D

theorem locHid_C_subset_locKeys (D : Finset (Id × X.Ty)) (ℓ : X.HKey)
    (hℓ : ℓ ∈ X.locHid D) : X.C ℓ.1 ⊆ X.locKeys D := by
  intro k hk
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hk⟩)

theorem typeKeys_subset_locKeys (D : Finset (Id × X.Ty)) (e : Id × X.Ty)
    (he : e ∈ D) : X.typeKeys e.2 ⊆ X.locKeys D := by
  intro k hk
  rcases Finset.mem_insert.mp hk with hkey | hobs
  · subst k
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  · rcases Finset.mem_biUnion.mp hobs with ⟨ℓ, hℓ, hk⟩
    exact locHid_C_subset_locKeys X D ℓ (Finset.mem_biUnion.mpr ⟨e, he, hℓ⟩) hk

theorem typeKeys_subset_s3BaseKeys (b : X.State) (D : Finset (Id × X.Ty))
    (e : Id × X.Ty) (he : e ∈ D) : X.typeKeys e.2 ⊆ s3BaseKeys X b D :=
  (typeKeys_subset_locKeys X D e he).trans Finset.subset_union_right

theorem tupleRatio_eq_of_baseAgree (β : X.Ty) {bξ bξ' b b' : X.Base}
    (hξ : BaseAgree X (X.typeKeys β) bξ bξ') (h : BaseAgree X (X.typeKeys β) b b')
    (zξ z : X.Hid) (T T' : FinProb X.ι) (hT : T = T') (drop : X.Name) (o : X.Tuple) :
    X.tupleRatio (bξ, zξ) (b, z) β T drop o =
      X.tupleRatio (bξ', zξ) (b', z) β T' drop o := by
  have htag := tagPost_eq_of_baseAgree X β hξ zξ β.obs (fun _ hℓ => hℓ)
  have hnum (i : X.ι) := labelLaw_eq_of_baseAgree X hξ β
    (Finset.mem_insert_self _ _) zξ (reqNames6 β) (fun _ hnm => hnm) i
  have hden (i : X.ι) := labelLaw_eq_of_baseAgree X h β
    (Finset.mem_insert_self _ _) z ((reqNames6 β).erase drop) (Finset.erase_subset _ _) i
  simp only [Ctx6.tupleRatio, Ctx6.Tβ, htag, hnum, hden, hT]

theorem lowLik_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) (s : X.State) (ξ : Fin N) (o : X.Tuple) :
    X.lowLik (b, z) s ξ β o = X.lowLik (b', z) s ξ β o := by
  have htag := tagPost_eq_of_baseAgree X β h z (β.obs.erase (X.tgt s)) (Finset.erase_subset _ _)
  exact tupleRatio_eq_of_baseAgree X β h h (Function.update z (X.tgt s) ξ) z
    _ _ htag (.hid (X.tgt s)) o

theorem highLik_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') (z : X.Hid) (s : X.State) (ξ : Fin N) (o : X.Tuple) :
    X.highLik (b, z) s ξ β o = X.highLik (b', z) s ξ β o := by
  exact tupleRatio_eq_of_baseAgree X β (baseAgree_withPar X h (X.tgtName s) ξ) h
    z z _ _ rfl (.par (X.tgtName s)) o

theorem priorOf_eq_of_baseAgree {S : Finset X.Key} {b b' : X.Base}
    (h : BaseAgree X S b b') (z : X.Hid) (nm : ParentName6 X.Bin) :
    X.priorOf (b, z) nm = X.priorOf (b', z) nm := by
  cases nm <;> simp [Ctx6.priorOf, h.1]

theorem lowGate_eq_of_baseAgree (s : X.State) (D : Finset (Id × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid) (ξ : Fin N) :
    X.LowGate (b, z) s D ξ ↔ X.LowGate (b', z) s D ξ := by
  have hpost := hidPost_eq_of_baseAgree X h (X.tgt s).1 Finset.subset_union_left
  have htest (e : Id × X.Ty) (he : e ∈ D) :
      X.Step2Tests (X.withHid (b, z) (X.tgt s) ξ) e.2 ↔
        X.Step2Tests (X.withHid (b', z) (X.tgt s) ξ) e.2 :=
    step2Tests_eq_of_baseAgree X e.2
      (baseAgree_mono X h (typeKeys_subset_s3BaseKeys X s D e he)) _
  simp only [Ctx6.LowGate, Ctx6.Step1Cap, hpost]
  constructor <;> rintro ⟨hp, hc, ht⟩ <;> refine ⟨hp, hc, ?_⟩
  · intro e he
    exact (htest e he).mp (ht e he)
  · intro e he
    exact (htest e he).mpr (ht e he)

theorem locDensity_eq_of_baseAgree (s : X.State) (D : Finset (Id × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid)
    (nm : ParentName6 X.Bin) (ξ : Fin N) :
    X.locDensity (b, z) nm D ξ = X.locDensity (b', z) nm D ξ := by
  have hξ := baseAgree_withPar X h nm ξ
  have hA (u : X.Bin) (hu : u ∈ X.locBins D nm) : b.2.1 u = b'.2.1 u := by
    exact h.2.1 u (Finset.image_subset_image Finset.subset_union_right (Finset.mem_filter.mp hu).1)
  have hI (k : X.Key) (hk : k ∈ X.locKeys D) : b.2.2 k = b'.2.2 k :=
    h.2.2 k (Finset.mem_union_right _ hk)
  have htag (k : X.Key) (hk : k ∈ X.locKeys D) :
      X.tagLawAt (X.parOf (X.withPar b nm ξ)) k =
        X.tagLawAt (X.parOf (X.withPar b' nm ξ)) k :=
    tagLawAt_eq_of_baseAgree X hξ k (Finset.mem_union_right _ hk)
  have hpost (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D) :
      X.hidPost (X.withPar b nm ξ) ℓ.1 = X.hidPost (X.withPar b' nm ξ) ℓ.1 :=
    hidPost_eq_of_baseAgree X hξ ℓ.1
      ((locHid_C_subset_locKeys X D ℓ hℓ).trans Finset.subset_union_right)
  have hcand : (∏ u ∈ X.locBins D nm, (N : ℝ) *
      (X.candLaw (X.withPar b nm ξ).1).w (b.2.1 u)) =
        ∏ u ∈ X.locBins D nm, (N : ℝ) *
          (X.candLaw (X.withPar b' nm ξ).1).w (b'.2.1 u) := by
    apply Finset.prod_congr rfl
    intro u hu
    rw [hξ.1, hA u hu]
  have htags : (∏ k ∈ X.locKeys D,
      safeRatio6 ((X.tagLawAt (X.parOf (X.withPar b nm ξ)) k).w (b.2.2 k)) (M.Λ (b.2.2 k))) =
        ∏ k ∈ X.locKeys D,
          safeRatio6 ((X.tagLawAt (X.parOf (X.withPar b' nm ξ)) k).w (b'.2.2 k)) (M.Λ (b'.2.2 k)) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [htag k hk, hI k hk]
  have hhids : (∏ ℓ ∈ X.locHid D, (N : ℝ) *
      (X.hidPost (X.withPar b nm ξ) ℓ.1).w (z ℓ)) =
        ∏ ℓ ∈ X.locHid D, (N : ℝ) * (X.hidPost (X.withPar b' nm ξ) ℓ.1).w (z ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hpost ℓ hℓ]
  dsimp only [Ctx6.locDensity]
  rw [hcand, htags, hhids]

theorem highGate_eq_of_baseAgree (s : X.State) (D : Finset (Id × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid) (ξ : Fin N) :
    X.HighGate (b, z) s D ξ ↔ X.HighGate (b', z) s D ξ := by
  have hξ := baseAgree_withPar X h (X.tgtName s) ξ
  have hprior := priorOf_eq_of_baseAgree X h z (X.tgtName s)
  have hstep1 (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D) :
      X.Step1OK (X.withPar b (X.tgtName s) ξ) ℓ.1 ↔
        X.Step1OK (X.withPar b' (X.tgtName s) ξ) ℓ.1 :=
    step1OK_eq_of_baseAgree X hξ ℓ.1
      ((locHid_C_subset_locKeys X D ℓ hℓ).trans Finset.subset_union_right)
  have hstep2 (e : Id × X.Ty) (he : e ∈ D) :
      X.Step2Tests (X.withParH (b, z) (X.tgtName s) ξ) e.2 ↔
        X.Step2Tests (X.withParH (b', z) (X.tgtName s) ξ) e.2 :=
    step2Tests_eq_of_baseAgree X e.2
      (baseAgree_mono X hξ (typeKeys_subset_s3BaseKeys X s D e he)) z
  unfold Ctx6.HighGate
  rw [hprior]
  constructor <;> rintro ⟨hp, h1, h2⟩ <;> refine ⟨hp, ?_, ?_⟩
  · intro ℓ hℓ
    exact (hstep1 ℓ hℓ).mp (h1 ℓ hℓ)
  · intro e he
    exact (hstep2 e he).mp (h2 e he)
  · intro ℓ hℓ
    exact (hstep1 ℓ hℓ).mpr (h1 ℓ hℓ)
  · intro e he
    exact (hstep2 e he).mpr (h2 e he)

theorem s3Weight_eq_of_baseAgree (s : X.State) (D : Finset (Id × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid) (o : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.s3Weight (b, z) s D o drop ξ = X.s3Weight (b', z) s D o drop ξ := by
  have htype (e : Id × X.Ty) (he : e ∈ D) :=
    baseAgree_mono X h (typeKeys_subset_s3BaseKeys X s D e he)
  have hlowprod : (∏ e ∈ D, if drop = some e then 1 else X.lowLik (b, z) s ξ e.2 (o e)) =
      ∏ e ∈ D, if drop = some e then 1 else X.lowLik (b', z) s ξ e.2 (o e) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [lowLik_eq_of_baseAgree X e.2 (htype e he) z s ξ (o e)]
  have hhighprod : (∏ e ∈ D, if drop = some e then 1 else X.highLik (b, z) s ξ e.2 (o e)) =
      ∏ e ∈ D, if drop = some e then 1 else X.highLik (b', z) s ξ e.2 (o e) := by
    apply Finset.prod_congr rfl
    intro e he
    rw [highLik_eq_of_baseAgree X e.2 (htype e he) z s ξ (o e)]
  have hpost := hidPost_eq_of_baseAgree X h (X.tgt s).1 Finset.subset_union_left
  have hlowgate := lowGate_eq_of_baseAgree X s D h z ξ
  have hhighgate := highGate_eq_of_baseAgree X s D h z ξ
  have hprior := priorOf_eq_of_baseAgree X h z (X.tgtName s)
  have hdensity := locDensity_eq_of_baseAgree X s D h z (X.tgtName s) ξ
  cases hm : X.stMode s <;>
    simp only [Ctx6.s3Weight, hm, Ctx6.lowWeight, Ctx6.highWeight,
      hpost, hlowgate, hhighgate, hprior, hdensity, hlowprod, hhighprod]

theorem trueTarget_eq_of_baseAgree (s : X.State) (D : Finset (Id × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid) :
    X.trueTarget (b, z) s = X.trueTarget (b', z) s := by
  have hself : (X.tgt s).1 ∈ X.C (X.tgt s).1 := by
    simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
  have hval := (parentValues_eq_of_baseAgree X h (X.tgt s).1
    (Finset.mem_union_left _ hself)).1
  cases hm : X.stMode s
  · simp only [Ctx6.trueTarget, hm]
  · simpa only [Ctx6.trueTarget, hm, Ctx6.tgtName, Ctx6.tgt, ChunkLayout6.stTarget] using hval

theorem s3Fail_eq_of_baseAgree (s : X.State) (D : Finset (Id × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid) (o : X.Data Id) :
    X.S3Fail (b, z) s D o ↔ X.S3Fail (b', z) s D o := by
  have hmass (drop : Option (Id × X.Ty)) :
      X.s3Mass (b, z) s D o drop = X.s3Mass (b', z) s D o drop := by
    unfold Ctx6.s3Mass
    exact Finset.sum_congr rfl fun ξ _ => s3Weight_eq_of_baseAgree X s D h z o drop ξ
  have htrue := trueTarget_eq_of_baseAgree X s D h z
  have hlow := lowGate_eq_of_baseAgree X s D h z (X.trueTarget (b', z) s)
  have hhigh := highGate_eq_of_baseAgree X s D h z (X.trueTarget (b', z) s)
  cases hm : X.stMode s <;>
    simp only [Ctx6.S3Fail, Ctx6.S3TrueGate, hm, htrue, hlow, hhigh, Ctx6.S3Tests, hmass]

theorem rate3_eq_of_baseAgree (s : X.State) (D : Finset (Fin X.T × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') (z : X.Hid) :
    X.rate3 (b, z) s D = X.rate3 (b', z) s D := by
  let P (e : Fin X.T × X.Ty) := X.tupleLaw (b, z) e.2
  let Q (e : Fin X.T × X.Ty) := X.tupleLaw (b', z) e.2
  have hPQ (e : Fin X.T × X.Ty) (he : e ∈ D) : P e = Q e :=
    tupleLaw_eq_of_baseAgree X e.2
      (baseAgree_mono X h (typeKeys_subset_s3BaseKeys X s D e he)) z
  have hdep := Lane_q_s06_stages.s3Fail_dependsOn_data X (b', z) s D
  have hpr := Lane_q_s06_stages.pi_pr_eq_of_kernel_eq_on_depends P Q D
    (fun o => X.S3Fail (b', z) s D o) hdep hPQ
  change (FinProb.pi P).pr (fun o => X.S3Fail (b, z) s D o) =
    (FinProb.pi Q).pr (fun o => X.S3Fail (b', z) s D o)
  calc
    _ = (FinProb.pi P).pr (fun o => X.S3Fail (b', z) s D o) :=
      Lane_q_s06_stages.pr_congr _ (fun o => s3Fail_eq_of_baseAgree X s D h z o)
    _ = _ := hpr

theorem rate3Base_eq_of_baseAgree (s : X.State) (D : Finset (Fin X.T × X.Ty)) {b b' : X.Base}
    (h : BaseAgree X (s3BaseKeys X s D) b b') :
    X.rate3Base b s D = X.rate3Base b' s D := by
  let S := Lane_q_s06_stages.rate3HiddenScope X s D
  let f (z : X.Hid) := X.rate3 (b', z) s D
  have hdep : FinProb.DependsOn f S := by
    intro z z' hz
    exact Lane_q_s06_stages.s3FailPr_eq_of_agree X b' s D z z' hz
  have hkernel (ℓ : X.HKey) (hℓ : ℓ ∈ S) : X.hidPost b ℓ.1 = X.hidPost b' ℓ.1 := by
    apply hidPost_eq_of_baseAgree X h ℓ.1
    rcases Finset.mem_union.mp hℓ with hloc | htgt
    · exact (locHid_C_subset_locKeys X D ℓ hloc).trans Finset.subset_union_right
    · by_cases hm : X.stMode s = .low
      · have heq : ℓ = X.tgt s := by simpa [hm] using htgt
        subst ℓ
        exact Finset.subset_union_left
      · simp [hm] at htgt
  have hfun : (fun z => X.rate3 (b, z) s D) = f := by
    funext z
    exact rate3_eq_of_baseAgree X s D h z
  unfold Ctx6.rate3Base
  change (FinProb.pi (fun ℓ : X.HKey => X.hidPost b ℓ.1)).expect _ =
    (FinProb.pi (fun ℓ : X.HKey => X.hidPost b' ℓ.1)).expect f
  rw [hfun]
  exact S06.Lane_sol_s06_steps1.pi_expect_congr_on _ _ S f (fun _ => X.y₀) hdep hkernel

theorem rate2Base_eq_of_baseAgree (β : X.Ty) {b b' : X.Base}
    (h : BaseAgree X (X.typeKeys β) b b') : X.rate2Base b β = X.rate2Base b' β := by
  let f (z : X.Hid) : ℝ := if X.Step2Fail (b', z) β then 1 else 0
  have hI := h.2.2 β.key (Finset.mem_insert_self _ _)
  have hgate := tagGate_eq_of_baseAgree X β h (b'.2.2 β.key)
  have htests (z : X.Hid) := step2Tests_eq_of_baseAgree X β h z
  have hfail (z : X.Hid) : X.Step2Fail (b, z) β ↔ X.Step2Fail (b', z) β := by
    simp only [Ctx6.Step2Fail, hI, hgate, htests]
  have hdep : FinProb.DependsOn f β.obs := by
    intro z z' hz
    have htests := Lane_q_s06_loads.step2Tests_congr_hid X b' z z' β hz
    have hff : X.Step2Fail (b', z) β ↔ X.Step2Fail (b', z') β := by
      simp only [Ctx6.Step2Fail, htests]
    by_cases hf : X.Step2Fail (b', z) β
    · have hf' := hff.mp hf
      simp [f, hf, hf']
    · have hf' : ¬ X.Step2Fail (b', z') β := fun ht => hf (hff.mpr ht)
      simp [f, hf, hf']
  have hkernel (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
      X.hidPost b ℓ.1 = X.hidPost b' ℓ.1 :=
    hidPost_eq_of_baseAgree X h ℓ.1 (typeKeys_obs X β ℓ hℓ)
  unfold Ctx6.rate2Base
  rw [Lane_q_s06_stages.finprob_pr_eq_expect_indicator,
    Lane_q_s06_stages.finprob_pr_eq_expect_indicator]
  have hfun : (fun z => if X.Step2Fail (b, z) β then (1 : ℝ) else 0) = f := by
    funext z
    simp only [f, hfail]
  rw [hfun]
  exact S06.Lane_sol_s06_steps1.pi_expect_congr_on _ _ β.obs f (fun _ => X.y₀) hdep hkernel

theorem makeType_key (h : X.Key) (t : CubeVertex X.g.L.m) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    (makeType6 binAdjacent6 h t F j X.J).key = h := by
  unfold makeType6
  split_ifs <;> rfl

theorem makeType_typeKeys_subset_keyBall (h : X.Key) (t : CubeVertex X.g.L.m)
    (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    X.typeKeys (makeType6 binAdjacent6 h t F j X.J) ⊆ Lane_q_s06_loads.keyBall6 X h 2 := by
  let β := makeType6 binAdjacent6 h t F j X.J
  have hself : h ∈ X.C h := by simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
  have hroot0 : h ∈ Lane_q_s06_loads.keyBall6 X h 0 := by simp [Lane_q_s06_loads.keyBall6]
  have hroot1 := _root_.Lane_q_s06_loads.keyBall6_pad_self X h h 0 hroot0
  have hroot2 := _root_.Lane_q_s06_loads.keyBall6_pad_self X h h 1 hroot1
  intro k hk
  rcases Finset.mem_insert.mp hk with heq | hobs
  · rw [heq, makeType_key X h t F j]
    exact hroot2
  · rcases Finset.mem_biUnion.mp hobs with ⟨ℓ, hℓ, hk⟩
    have hgeom := _root_.Lane_q_s06_loads.makeType6_obs_scope binAdjacent6 h t F j X.J ℓ hℓ
    have hC : ℓ.1 ∈ X.C h := by
      rcases hgeom.1 with heq | hC
      · rw [heq]
        exact hself
      · exact hC
    have hℓball := _root_.Lane_q_s06_loads.keyBall6_extend_C X h h ℓ.1 0 hroot0 hC
    exact _root_.Lane_q_s06_loads.keyBall6_extend_C X h ℓ.1 k 1 hℓball hk

theorem evenType_typeKeys_subset_keyBall (x : CubeVertex n) :
    X.typeKeys (X.evenType x) ⊆ Lane_q_s06_loads.keyBall6 X (X.g.L.key x) 2 :=
  makeType_typeKeys_subset_keyBall X _ _ _ _

theorem stType_typeKeys_subset_keyBall (s : X.State) :
    X.typeKeys (X.stType s) ⊆ Lane_q_s06_loads.keyBall6 X (X.g.L.stKey s) 2 :=
  makeType_typeKeys_subset_keyBall X _ _ _ _

def coarseKeyWindow (w : X.Bin) : Finset X.Key :=
  Lane_q_s06_loads.keyBall6 X (w, .interior) 4

def bad2BinScope (w : X.Bin) : Finset X.Bin := X.binsOf (coarseKeyWindow X w)

theorem sameBin_keyBall_one (w : X.Bin) (k : X.Key) (hk : k.1 = w) :
    k ∈ Lane_q_s06_loads.keyBall6 X (w, .interior) 1 := by
  have hroot : (w, KeyFlag6.interior) ∈ Lane_q_s06_loads.keyBall6 X (w, .interior) 0 := by
    simp [Lane_q_s06_loads.keyBall6]
  apply _root_.Lane_q_s06_loads.keyBall6_extend_C X (w, .interior) (w, .interior) k 0 hroot
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inl hk.symm)⟩

theorem C_C_subset_coarseKeyWindow (w : X.Bin) (k k' : X.Key)
    (hk : k.1 = w) (hk' : k' ∈ X.C k) : X.C k' ⊆ coarseKeyWindow X w := by
  have h1 := sameBin_keyBall_one X w k hk
  have h2 := _root_.Lane_q_s06_loads.keyBall6_extend_C X (w, .interior) k k' 1 h1 hk'
  intro k'' hk''
  have h3 := _root_.Lane_q_s06_loads.keyBall6_extend_C X (w, .interior) k' k'' 2 h2 hk''
  exact _root_.Lane_q_s06_loads.keyBall6_pad_self X (w, .interior) k'' 3 h3

theorem evenType_typeKeys_subset_coarseKeyWindow (w : X.Bin) (x : CubeVertex n)
    (hx : (X.g.L.key x).1 = w) : X.typeKeys (X.evenType x) ⊆ coarseKeyWindow X w := by
  intro k hk
  have h1 := sameBin_keyBall_one X w (X.g.L.key x) hx
  have h2 := evenType_typeKeys_subset_keyBall X x hk
  have h3 := _root_.Lane_q_s06_loads.keyBall6_concat X 1 2 (w, .interior)
    (X.g.L.key x) k h1 h2
  exact _root_.Lane_q_s06_loads.keyBall6_pad_self X (w, .interior) k 3 h3

theorem locKeys_subset_of_types (D : Finset (Id × X.Ty)) (S : Finset X.Key)
    (h : ∀ e ∈ D, X.typeKeys e.2 ⊆ S) : X.locKeys D ⊆ S := by
  intro k hk
  rcases Finset.mem_union.mp hk with hobs | hkey
  · rcases Finset.mem_biUnion.mp hobs with ⟨ℓ, hℓ, hk⟩
    rcases Finset.mem_biUnion.mp hℓ with ⟨e, he, hℓ⟩
    exact h e he (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hk⟩))
  · rcases Finset.mem_image.mp hkey with ⟨e, he, rfl⟩
    exact h e he (Finset.mem_insert_self _ _)

theorem s3BaseKeys_subset_coarseKeyWindow (w : X.Bin) (s : X.State)
    (hs : (X.g.L.stKey s).1 = w) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs s) :
    s3BaseKeys X s D ⊆ coarseKeyWindow X w := by
  have h1 := sameBin_keyBall_one X w (X.g.L.stKey s) hs
  have htarget : X.C (X.tgt s).1 ⊆ coarseKeyWindow X w := by
    intro k hk
    have h2 := _root_.Lane_q_s06_loads.keyBall6_extend_C X (w, .interior)
      (X.g.L.stKey s) k 1 h1 hk
    have h3 := _root_.Lane_q_s06_loads.keyBall6_pad_self X (w, .interior) k 2 h2
    exact _root_.Lane_q_s06_loads.keyBall6_pad_self X (w, .interior) k 3 h3
  have htypes (e : Fin X.T × X.Ty) (he : e ∈ D) : X.typeKeys e.2 ⊆ coarseKeyWindow X w := by
    obtain ⟨a, ha, heq⟩ := _root_.Lane_q_s06_loads.absDesc_type_mem_stNbr X s D hD e he
    have hadj := _root_.Lane_q_s06_loads.ctx6_stNbr_key_adjacent X s a ha
    have haC : X.g.L.stKey a ∈ X.C (X.g.L.stKey s) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
    have h2 := _root_.Lane_q_s06_loads.keyBall6_extend_C X (w, .interior)
      (X.g.L.stKey s) (X.g.L.stKey a) 1 h1 haC
    intro k hk
    rw [heq] at hk
    have hk2 := stType_typeKeys_subset_keyBall X a hk
    exact _root_.Lane_q_s06_loads.keyBall6_concat X 2 2 (w, .interior)
      (X.g.L.stKey a) k h2 hk2
  exact Finset.union_subset htarget (locKeys_subset_of_types X D _ htypes)

theorem bad2_eq_of_baseAgree (v : Fin N) (w : X.Bin) (c c' : X.Coarse)
    (h : BaseAgree X (coarseKeyWindow X w) (v, c) (v, c')) :
    X.Bad2 v w c ↔ X.Bad2 v w c' := by
  have hstep1 (x : CubeVertex n) (hx : (X.g.L.key x).1 = w) (k : X.Key) (hk : k ∈ X.C (X.g.L.key x)) :
      X.Step1OK (v, c) k ↔ X.Step1OK (v, c') k :=
    step1OK_eq_of_baseAgree X h k (C_C_subset_coarseKeyWindow X w (X.g.L.key x) k hx hk)
  have hrate2 (x : CubeVertex n) (hx : (X.g.L.key x).1 = w) :
      X.rate2Base (v, c) (X.evenType x) = X.rate2Base (v, c') (X.evenType x) :=
    rate2Base_eq_of_baseAgree X (X.evenType x)
      (baseAgree_mono X h (evenType_typeKeys_subset_coarseKeyWindow X w x hx))
  have hrate3 (s : X.State) (hs : (X.g.L.stKey s).1 = w)
      (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs s) :
      X.rate3Base (v, c) s D = X.rate3Base (v, c') s D :=
    rate3Base_eq_of_baseAgree X s D
      (baseAgree_mono X h (s3BaseKeys_subset_coarseKeyWindow X w s hs D hD))
  unfold Ctx6.Bad2
  constructor
  · rintro (⟨x, hx, k, hk, hbad⟩ | ⟨x, heven, hx, hbad⟩ | ⟨s, hsOdd, hs, D, hD, hbad⟩)
    · exact Or.inl ⟨x, hx, k, hk, fun hok => hbad ((hstep1 x hx k hk).mpr hok)⟩
    · exact Or.inr (Or.inl ⟨x, heven, hx, by rwa [← hrate2 x hx]⟩)
    · exact Or.inr (Or.inr ⟨s, hsOdd, hs, D, hD, by rwa [← hrate3 s hs D hD]⟩)
  · rintro (⟨x, hx, k, hk, hbad⟩ | ⟨x, heven, hx, hbad⟩ | ⟨s, hsOdd, hs, D, hD, hbad⟩)
    · exact Or.inl ⟨x, hx, k, hk, fun hok => hbad ((hstep1 x hx k hk).mp hok)⟩
    · exact Or.inr (Or.inl ⟨x, heven, hx, by rwa [hrate2 x hx]⟩)
    · exact Or.inr (Or.inr ⟨s, hsOdd, hs, D, hD, by rwa [hrate3 s hs D hD]⟩)

theorem bad2_depends_on_bins (v : Fin N) (w : X.Bin) :
    FinProb.DependsOn (fun z : X.Bin → Lane_sol_s06_loadA.BinData X =>
      X.Bad2 v w ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) (bad2BinScope X w) := by
  intro z z' hz
  apply propext
  apply bad2_eq_of_baseAgree X v w
  refine ⟨rfl, ?_, ?_⟩
  · intro u hu
    exact congrArg Prod.fst (hz u hu)
  · intro k hk
    exact congrArg (fun p : Lane_sol_s06_loadA.BinData X => p.2 k.2)
      (hz k.1 (Finset.mem_image.mpr ⟨k, hk, rfl⟩))

def coarseTouch (x : CubeVertex n) : Finset X.Bin :=
  Finset.univ.filter fun w => ¬ Disjoint (evenBinScope X x) (bad2BinScope X w)

theorem coarseTouch_subset_keyBall (x : CubeVertex n) (w : X.Bin) (hw : w ∈ coarseTouch X x) :
    w ∈ X.binsOf (Lane_q_s06_loads.keyBall6 X (X.g.L.key x) 7) := by
  obtain ⟨u, hrow, hbad⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hw).2
  obtain ⟨k, hk, hku⟩ := Finset.mem_image.mp hrow
  obtain ⟨k', hk', hk'u⟩ := Finset.mem_image.mp hbad
  have hk2 := evenType_typeKeys_subset_keyBall X x hk
  have hsame : k.1 = k'.1 := hku.trans hk'u.symm
  have hk'C : k' ∈ X.C k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inl hsame)⟩
  have hk3 := _root_.Lane_q_s06_loads.keyBall6_extend_C X (X.g.L.key x) k k' 2 hk2 hk'C
  have hrev := _root_.Lane_q_s06_loads.keyBall6_symm X 4 (w, .interior) k' hk'
  have hw7 := _root_.Lane_q_s06_loads.keyBall6_concat X 3 4 (X.g.L.key x) k' (w, .interior) hk3 hrev
  exact Finset.mem_image.mpr ⟨(w, .interior), hw7, rfl⟩

theorem coarseTouch_card_le (x : CubeVertex n) : (coarseTouch X x).card ≤ 602 ^ 7 := by
  have hsub : coarseTouch X x ⊆ X.binsOf (Lane_q_s06_loads.keyBall6 X (X.g.L.key x) 7) :=
    fun w hw => coarseTouch_subset_keyBall X x w hw
  calc
    _ ≤ (X.binsOf (Lane_q_s06_loads.keyBall6 X (X.g.L.key x) 7)).card := Finset.card_le_card hsub
    _ ≤ (Lane_q_s06_loads.keyBall6 X (X.g.L.key x) 7).card := Finset.card_image_le
    _ ≤ _ := Lane_q_s06_loads.keyBall6_card_le X _ 7

def coarseTouchUnion (U : Finset (CubeVertex n)) : Finset X.Bin :=
  Finset.univ.filter fun w => ¬ Disjoint (U.biUnion (evenBinScope X)) (bad2BinScope X w)

theorem coarseTouchUnion_card_le (U : Finset (CubeVertex n)) :
    (coarseTouchUnion X U).card ≤ U.card * 602 ^ 7 := by
  have hsub : coarseTouchUnion X U ⊆ U.biUnion (coarseTouch X) := by
    intro w hw
    obtain ⟨u, hrows, hbad⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hw).2
    obtain ⟨x, hx, hrow⟩ := Finset.mem_biUnion.mp hrows
    refine Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact Finset.not_disjoint_iff.mpr ⟨u, hrow, hbad⟩
  calc
    _ ≤ (U.biUnion (coarseTouch X)).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ U, (coarseTouch X x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ U, 602 ^ 7 := Finset.sum_le_sum fun x _ => coarseTouch_card_le X x
    _ = _ := by simp

theorem coarse_touch_charge_eventually_small :
    ∀ᶠ n : ℕ in atTop, 2 * (n : ℝ) ^ (-(δ₁ / 8)) * (602 ^ 7 : ℝ) ≤ Real.log 2 := by
  have he : 0 < δ₁ / 8 := by norm_num [δ₁]
  have hlim := ((tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop).const_mul
    (2 * (602 ^ 7 : ℝ))
  have hsmall : ∀ᶠ n : ℕ in atTop, (2 * (602 ^ 7 : ℝ)) * (n : ℝ) ^ (-(δ₁ / 8)) < Real.log 2 := by
    have hlim0 : Tendsto (fun n : ℕ => (2 * (602 ^ 7 : ℝ)) * (n : ℝ) ^ (-(δ₁ / 8)))
        atTop (nhds 0) := by simpa [Function.comp_def] using hlim
    exact hlim0.eventually (eventually_lt_nhds (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  filter_upwards [hsmall] with n hn
  nlinarith

def bad2BinEvent (v : Fin N) (w : X.Bin) : Finset (X.Bin → Lane_sol_s06_loadA.BinData X) :=
  Finset.univ.filter fun z => X.Bad2 v w ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)

theorem mem_coarseAvoid_bin_equiv (v : Fin N) (S : Finset X.Bin) (c : X.Coarse) :
    Lane_sol_s06_loadA.coarseBinEquiv X c ∈ LocalLemma.avoid (bad2BinEvent X v) S ↔
      c ∈ LocalLemma.avoid (X.bad2Set v) S := by
  simp [LocalLemma.avoid, bad2BinEvent, Ctx6.bad2Set]

theorem coarseAvoid_sum_equiv (v : Fin N) (S : Finset X.Bin) (F : X.Coarse → ℝ) :
    (∑ z ∈ LocalLemma.avoid (bad2BinEvent X v) S,
      (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).w z *
        F ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) =
      ∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, (X.coarseLaw v).w c * F c := by
  conv_lhs => rw [← Finset.sum_ite_mem_eq]
  conv_rhs => rw [← Finset.sum_ite_mem_eq]
  rw [← Equiv.sum_comp (Lane_sol_s06_loadA.coarseBinEquiv X)]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mem_coarseAvoid_bin_equiv, Lane_sol_s06_loadA.coarseLaw_weight, Equiv.symm_apply_apply]

theorem coarseAvoid_mass_equiv (v : Fin N) (S : Finset X.Bin) :
    LocalLemma.mass (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).w
      (LocalLemma.avoid (bad2BinEvent X v) S) =
        LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) S) := by
  simpa only [LocalLemma.mass, mul_one] using coarseAvoid_sum_equiv X v S (fun _ => 1)

theorem coarseAvoid_factor (v : Fin N) (U : Finset X.Bin) (W : X.Coarse → ℝ)
    (hW : FinProb.DependsOn (fun z : X.Bin → Lane_sol_s06_loadA.BinData X =>
      W ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) U)
    (S : Finset X.Bin) (hS : ∀ w ∈ S, Disjoint U (bad2BinScope X w)) :
    (∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, (X.coarseLaw v).w c * W c) =
      (X.coarseLaw v).expect W *
        LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) S) := by
  let q (w : X.Bin) := (Lane_sol_s06_loadA.binLaw X v w).w
  have hq0 : ∀ w a, 0 ≤ q w a := fun w a => (Lane_sol_s06_loadA.binLaw X v w).nonneg a
  have hq1 : ∀ w, ∑ a, q w a = 1 := fun w => (Lane_sol_s06_loadA.binLaw X v w).sum_eq_one
  have hscope : ∀ w (z z' : X.Bin → Lane_sol_s06_loadA.BinData X),
      (∀ u ∈ bad2BinScope X w, z u = z' u) →
        (z ∈ bad2BinEvent X v w ↔ z' ∈ bad2BinEvent X v w) := by
    intro w z z' hz
    have heq := bad2_depends_on_bins X v w z z' hz
    simp only [bad2BinEvent, Finset.mem_filter, Finset.mem_univ, true_and, heq]
  have hfactor := _root_.Lane_q_s06_loads.product_weight_avoid_factor
    q hq0 hq1 (bad2BinEvent X v) (bad2BinScope X) hscope U
    (fun z => W ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) hW S hS
  change (∑ z ∈ LocalLemma.avoid (bad2BinEvent X v) S,
      (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).w z *
        W ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) =
      (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).expect
        (fun z => W ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) *
          LocalLemma.mass (FinProb.pi (Lane_sol_s06_loadA.binLaw X v)).w
            (LocalLemma.avoid (bad2BinEvent X v) S) at hfactor
  rw [coarseAvoid_sum_equiv X v S W, coarseAvoid_mass_equiv X v S,
    ← Lane_sol_s06_loadA.coarseLaw_expect X v W] at hfactor
  exact hfactor

/-- Conditional avoidance on the actual coarse stage costs only constraints touching the function's bins. -/
theorem stage2_compare_local (v : Fin N) (xmax : ℝ)
    (cert : AvoidCert6 (X.coarseLaw v).w (X.bad2Set v) xmax) (hx : xmax < 1)
    (U : Finset X.Bin) (W : X.Coarse → ℝ)
    (hW : FinProb.DependsOn (fun z : X.Bin → Lane_sol_s06_loadA.BinData X =>
      W ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) U)
    (hW0 : ∀ c, 0 ≤ W c) (S T : Finset X.Bin) (hST : Disjoint S T)
    (hUnion : S ∪ T = Finset.univ)
    (hS : ∀ w ∈ S, Disjoint U (bad2BinScope X w)) :
    (X.stage2Law v).expect W ≤
      (∏ w ∈ T, (1 - cert.x w)⁻¹) * (X.coarseLaw v).expect W := by
  classical
  have hpos := Lane_q_s06_loads.S06.AvoidCert6.mass_avoid_pos cert
    (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one hx
  have hposS := _root_.Lane_q_s06_loads.avoid_mass_positive_subset cert
    (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one hx S
  have hfactor := coarseAvoid_factor X v U W hW S hS
  have hratio : (∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, (X.coarseLaw v).w c * W c) /
      LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) S) =
        (X.coarseLaw v).expect W := by
    rw [hfactor]
    exact mul_div_cancel_right₀ _ hposS.ne'
  let p (w : X.Bin) := cert.x w * ∏ w' ∈ Finset.univ.filter (cert.adj w), (1 - cert.x w')
  have havoid := LocalLemma.conditional_avoidance (X.coarseLaw v).w
    (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one (X.bad2Set v) cert.adj
    cert.adj_symm cert.adj_irrefl p cert.x cert.local_bound cert.x_nonneg
    (fun w => (cert.x_le w).trans_lt hx) (fun _ => le_rfl)
  have hcompare := havoid.2.2.1 S T hST W hW0
  rw [hUnion, hratio, ← Finset.prod_inv_distrib] at hcompare
  have hmem (c : X.Coarse) :
      c ∈ LocalLemma.avoid (X.bad2Set v) Finset.univ ↔ ∀ w, ¬ X.Bad2 v w c := by
    simp [LocalLemma.avoid, Ctx6.bad2Set]
  have hmass : LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) Finset.univ) =
      (X.coarseLaw v).pr (fun c => ∀ w, ¬ X.Bad2 v w c) := by
    unfold LocalLemma.mass FinProb.pr
    rw [← Finset.sum_ite_mem_eq]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hg : ∀ w, ¬ X.Bad2 v w c <;> simp [hmem, hg]
  have hnum : (∑ c ∈ LocalLemma.avoid (X.bad2Set v) Finset.univ, (X.coarseLaw v).w c * W c) =
      ∑ c, if (∀ w, ¬ X.Bad2 v w c) then (X.coarseLaw v).w c * W c else 0 := by
    rw [← Finset.sum_ite_mem_eq]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hg : ∀ w, ¬ X.Bad2 v w c <;> simp [hmem, hg]
  have hformula := Lane_q_s06_loads.restrictOr6_expect_formula (X.coarseLaw v)
    (fun c => ∀ w, ¬ X.Bad2 v w c) X.fallbackCoarse (by rwa [← hmass]) W
  have hstage : (X.stage2Law v).expect W =
    (∑ c, if (∀ w, ¬ X.Bad2 v w c) then (X.coarseLaw v).w c * W c else 0) /
      (X.coarseLaw v).pr (fun c => ∀ w, ¬ X.Bad2 v w c) := by
    convert hformula using 1 <;> try rfl
    apply congrArg (fun t : ℝ => t / (X.coarseLaw v).pr (fun c => ∀ w, ¬ X.Bad2 v w c))
    apply Finset.sum_congr rfl
    intro c _
    by_cases hg : ∀ w, ¬ X.Bad2 v w c <;> simp [hg]
  rw [hstage]
  rw [← hnum, ← hmass]
  exact hcompare

/-- Separated interior even means under stage 2 have a constant product-moment bound. -/
theorem stage2_evenMean_product_le (v : Fin N) (hv : 0 < X.initLaw.w v)
    (cert : AvoidCert6 (X.coarseLaw v).w (X.bad2Set v) ((n : ℝ) ^ (-(δ₁ / 8))))
    (hsmall : 2 * (n : ℝ) ^ (-(δ₁ / 8)) * (602 ^ 7 : ℝ) ≤ Real.log 2)
    (U : Finset (CubeVertex n)) (hInterior : ∀ x ∈ U, (X.evenType x).key.2 = .interior)
    (hdis : ∀ x ∈ U, ∀ x' ∈ U, x ≠ x' → Disjoint (evenBinScope X x) (evenBinScope X x'))
    (a : Fin N) :
    (X.stage2Law v).expect (fun c => ∏ x ∈ U, evenMean X (v, c) x a) ≤
      (2 : ℝ) ^ U.card * (20 * K / c₁) ^ U.card := by
  let xmax : ℝ := (n : ℝ) ^ (-(δ₁ / 8))
  let B : ℕ := 602 ^ 7
  have hBcast : (B : ℝ) = (602 ^ 7 : ℝ) := by norm_num [B]
  have hsmall' : 2 * xmax * (B : ℝ) ≤ Real.log 2 := by
    simpa only [xmax, hBcast] using hsmall
  have hx0 : 0 ≤ xmax := by dsimp [xmax]; positivity
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by norm_num [B]
  have hxhalf : xmax ≤ 1 / 2 := by
    have hm : 2 * xmax ≤ 2 * xmax * (B : ℝ) :=
      le_mul_of_one_le_right (by positivity) hB1
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  let Uscope := U.biUnion (evenBinScope X)
  let W (c : X.Coarse) := ∏ x ∈ U, evenMean X (v, c) x a
  have hW : FinProb.DependsOn (fun z : X.Bin → Lane_sol_s06_loadA.BinData X =>
      W ((Lane_sol_s06_loadA.coarseBinEquiv X).symm z)) Uscope := by
    intro z z' hz
    apply Finset.prod_congr rfl
    intro x hx
    apply evenMean_depends_on_bins X v x a
    intro u hu
    exact hz u (Finset.mem_biUnion.mpr ⟨x, hx, hu⟩)
  have hW0 (c : X.Coarse) : 0 ≤ W c := Finset.prod_nonneg fun x _ => evenMean_nonneg X _ x a
  let T := coarseTouchUnion X U
  let S := Finset.univ \ T
  have hST : Disjoint S T := Finset.sdiff_disjoint
  have hUnion : S ∪ T = Finset.univ := by ext w; simp [S]
  have hS (w : X.Bin) (hw : w ∈ S) : Disjoint Uscope (bad2BinScope X w) := by
    have hnot := (Finset.mem_sdiff.mp hw).2
    by_contra hd
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  have hcompare := stage2_compare_local X v xmax cert (by linarith) Uscope W hW hW0 S T hST hUnion hS
  have hcharge : (∏ w ∈ T, (1 - cert.x w)⁻¹) ≤ (2 : ℝ) ^ U.card := by
    apply _root_.Lane_q_s06_loads.avoidance_charge_product_le_two_pow T cert.x xmax U.card B hx0 hxhalf
    · intro w
      exact ⟨cert.x_nonneg w, cert.x_le w⟩
    · exact coarseTouchUnion_card_le X U
    · exact hsmall'
  have hraw0 : 0 ≤ (X.coarseLaw v).expect W := by
    unfold FinProb.expect
    exact Finset.sum_nonneg fun c _ => mul_nonneg ((X.coarseLaw v).nonneg c) (hW0 c)
  have hraw := evenMean_product_raw_le X v hv U hInterior hdis a
  calc
    _ ≤ (∏ w ∈ T, (1 - cert.x w)⁻¹) * (X.coarseLaw v).expect W := hcompare
    _ ≤ (2 : ℝ) ^ U.card * (X.coarseLaw v).expect W := mul_le_mul_of_nonneg_right hcharge hraw0
    _ ≤ _ := mul_le_mul_of_nonneg_left hraw (by positivity)

end
end HypercubeRamsey.Lane_sol_s06_loadD
