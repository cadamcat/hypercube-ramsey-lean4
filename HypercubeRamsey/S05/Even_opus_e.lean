import HypercubeRamsey.S05.History

/-!
# Lane opus-s05-e: the deterministic average of the even comparison means (05:806–816)

`even_mean_average` (Even.lean) bounds the average over even roles of
`d_v = C B_{K(v)} exp(C k_* 1_{j(v) > J})`, `B_K = A_K^{K_B}`, `A_K = exp(K''(1 + Σ_{ℓ ∈ S} s_ℓ))`.
The key list of a role of severity `j < J` has at most `1201 + j + 2` keys, all low (column length one); at
`j = J` one more key is the high key (column length `s`); at high severity there are at most `1201` high keys.
Severities `1 ≤ h < J` cost `e^{K'' K_B h}` against `Pr(j ≥ h) ≤ n^{-.13h}` (a geometric series once
`n^{.13} ≥ 2 e^{K'' K_B}`), and the bucket `j ≥ J` costs `exp(K'' K_B (1204 + J + 1201 s) + C k_*)` against
`n^{-.13 J}`, where `s ≤ K_s J (α log n + log 2) + 1` and `k_* ≤ J + 1 + 20 η J + q₀`; this is at most one
once `1201 K'' K_B K_s α ≤ .03` (`α` is chosen after `K_B`) and `n` is large.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_e

open Classical OAI.HypercubeRamsey

noncomputable section

variable {γ K' χ : ℝ}

/-! ### Key lists and their column lengths -/

theorem keyAt5_low {n m : ℕ} (J : ℕ) (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ) (hj : j ≤ J) :
    ∃ k, keyAt5 J i t j = Sum.inl k := by
  unfold keyAt5
  exact ⟨_, dif_pos hj⟩

theorem keyAt5_shape {n m : ℕ} (J : ℕ) (i : CoarseKey5 n) (t : CubeVertex m) (j : ℕ) :
    (∃ k, keyAt5 J i t j = Sum.inl k) ∨ (J < j ∧ keyAt5 J i t j = Sum.inr i) := by
  by_cases h : j ≤ J
  · exact Or.inl (keyAt5_low J i t j h)
  · right
    refine ⟨lt_of_not_ge h, ?_⟩
    unfold keyAt5
    exact dif_neg h

/-- At low severity every listed key is low, except the high key `(i(v), *)` when `j = J`. -/
theorem low_key_shape {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ) (x : CubeVertex n)
    (hx : g.severity x ≤ J) {ℓ : HiddenKey5 n m J} (hℓ : ℓ ∈ g.typeKeys J x) :
    (∃ k, ℓ = Sum.inl k) ∨ (g.severity x = J ∧ ℓ = Sum.inr (g.key x)) := by
  unfold ChunkGeometry5.typeKeys at hℓ
  rw [if_pos hx] at hℓ
  rcases Finset.mem_union.mp hℓ with hℓ | hℓ
  · rcases Finset.mem_union.mp hℓ with hℓ | hℓ
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hℓ
      obtain ⟨k, hk⟩ := keyAt5_low J i (g.sign x) (g.severity x) hx
      exact Or.inl ⟨k, hk⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hℓ
      obtain ⟨k, hk⟩ := keyAt5_low J (g.key x) (Function.update (g.sign x) i (!g.sign x i))
        (g.severity x) hx
      exact Or.inl ⟨k, hk⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hℓ
    have hj' : j = g.severity x + 1 ∨ j + 1 ≤ g.severity x := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact Or.inl (Finset.mem_singleton.mp hj)
      · split_ifs at hj with h0
        · have := Finset.mem_singleton.mp hj
          omega
        · simp at hj
    rcases keyAt5_shape J (g.key x) (g.sign x) j with h | h
    · exact Or.inl h
    · right
      exact ⟨by omega, h.2⟩

/-- Column lengths of a low key list: at most `1201 + j + 2` keys of length one, plus `s` at `j = J`. -/
theorem low_colLen_sum {n m : ℕ} (g : ChunkGeometry5 n m) (J s : ℕ) (x : CubeVertex n)
    (hx : g.severity x ≤ J) :
    ∑ ℓ ∈ g.typeKeys J x, colLen5 s ℓ ≤
      coarseChunkCount5 * 4 + 1 + g.severity x + 2 + (if g.severity x = J then s else 0) := by
  have hcard := Lane_sol_s05_h5l.low_type_card g J x hx
  let t : ℕ := if g.severity x = J then s else 0
  have hle : ∀ ℓ ∈ g.typeKeys J x,
      colLen5 s ℓ ≤ 1 + (if ℓ = Sum.inr (g.key x) then t else 0) := by
    intro ℓ hℓ
    rcases low_key_shape g J x hx hℓ with ⟨k, rfl⟩ | ⟨hJ, rfl⟩
    · simp [colLen5]
    · simp [colLen5, t, hJ]
  calc ∑ ℓ ∈ g.typeKeys J x, colLen5 s ℓ
      ≤ ∑ ℓ ∈ g.typeKeys J x, (1 + if ℓ = Sum.inr (g.key x) then t else 0) := Finset.sum_le_sum hle
    _ = (g.typeKeys J x).card + (if Sum.inr (g.key x) ∈ g.typeKeys J x then t else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    _ ≤ _ := by
      have : (if Sum.inr (g.key x) ∈ g.typeKeys J x then t else 0) ≤ t := by
        split_ifs <;> omega
      omega

/-- Column lengths of a high key list: at most `1201` high keys of length `s`. -/
theorem high_colLen_sum {n m : ℕ} (g : ChunkGeometry5 n m) (J s : ℕ) (x : CubeVertex n)
    (hx : ¬ g.severity x ≤ J) :
    ∑ ℓ ∈ g.typeKeys J x, colLen5 s ℓ ≤ (coarseChunkCount5 * 4 + 1) * s := by
  unfold ChunkGeometry5.typeKeys
  rw [if_neg hx]
  calc ∑ ℓ ∈ (g.coarseRange x).image (fun i => (Sum.inr i : HiddenKey5 n m J)), colLen5 s ℓ
      ≤ ((g.coarseRange x).image (fun i => (Sum.inr i : HiddenKey5 n m J))).card • s := by
        apply Finset.sum_le_card_nsmul
        intro ℓ hℓ
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hℓ
        simp [colLen5]
    _ ≤ (coarseChunkCount5 * 4 + 1) * s := by
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_image_le.trans (g.coarseRange_card_le x))

/-! ### Counting even roles -/

theorem even_total {n : ℕ} (hn : 0 < n) : (2 : ℝ) ^ n = 2 * Fintype.card (EvenRole5 n) := by
  have hEv : Fintype.card (EvenRole5 n) = 2 ^ (n - 1) := by
    rw [Fintype.card_subtype]
    have he : evenRoleSet n = Finset.univ.filter (fun x : CubeVertex n => IsEvenRole x) := by
      ext x; simp [evenRoleSet]
    rw [← he]
    exact (parity_class_card hn).1
  rw [hEv]
  have he : n = (n - 1) + 1 := by omega
  nth_rw 1 [he]
  rw [pow_succ]
  push_cast
  ring

theorem even_event_card {n : ℕ} (hn : 0 < n) (P : CubeVertex n → Prop) [DecidablePred P] (a : ℝ)
    (ha : ((Finset.univ.filter P).card : ℝ) / (2 : ℝ) ^ n ≤ a) :
    ((Finset.univ.filter fun v : EvenRole5 n => P v.1).card : ℝ) ≤
      2 * a * Fintype.card (EvenRole5 n) := by
  have hi : (Finset.univ.filter fun v : EvenRole5 n => P v.1).image Subtype.val ⊆
      Finset.univ.filter P := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
  have hc : ((Finset.univ.filter fun v : EvenRole5 n => P v.1).card : ℝ) ≤
      (Finset.univ.filter P).card := by
    exact_mod_cast (by
      rw [← Finset.card_image_of_injective _ Subtype.val_injective]
      exact Finset.card_le_card hi)
  have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp ha
  rw [even_total hn] at hh
  nlinarith

/-! ### The numerical inequality of the bucket `j ≥ J` -/

theorem big_bucket_small {C κ Ks α η q L Jr lm s k : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hKs : 0 ≤ Ks)
    (hq : 0 ≤ q) (hJ : 1 ≤ Jr) (hL : 0 ≤ L) (hα : 1201 * κ * Ks * α ≤ 3 / 100)
    (hs : s ≤ Ks * Jr * lm + 1) (hlm : lm ≤ Real.log 2 + α * L)
    (hk : k ≤ Jr + 1 + 20 * η * Jr + q)
    (hLbig : 10 * ((2 * C + 2405 * κ + C + C * q) + (κ + 1201 * κ * Ks * Real.log 2 + C + 20 * C * η)) ≤ L) :
    2 * (C * Real.exp (κ * (1204 + Jr + 1201 * s)) * Real.exp (C * k)) *
      Real.exp (L * (-(13 / 100) * Jr)) ≤ 1 := by
  have h2C : 2 * C ≤ Real.exp (2 * C) := by
    have := Real.add_one_le_exp (2 * C)
    linarith
  have hprod : 0 ≤ Real.exp (κ * (1204 + Jr + 1201 * s)) * Real.exp (C * k) *
      Real.exp (L * (-(13 / 100) * Jr)) := by positivity
  have hle : 2 * (C * Real.exp (κ * (1204 + Jr + 1201 * s)) * Real.exp (C * k)) *
      Real.exp (L * (-(13 / 100) * Jr)) ≤
      Real.exp (2 * C + κ * (1204 + Jr + 1201 * s) + C * k + L * (-(13 / 100) * Jr)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    have := mul_le_mul_of_nonneg_right h2C hprod
    calc 2 * (C * Real.exp (κ * (1204 + Jr + 1201 * s)) * Real.exp (C * k)) *
          Real.exp (L * (-(13 / 100) * Jr))
        = 2 * C * (Real.exp (κ * (1204 + Jr + 1201 * s)) * Real.exp (C * k) *
          Real.exp (L * (-(13 / 100) * Jr))) := by ring
      _ ≤ Real.exp (2 * C) * (Real.exp (κ * (1204 + Jr + 1201 * s)) * Real.exp (C * k) *
          Real.exp (L * (-(13 / 100) * Jr))) := this
      _ = _ := by ring
  refine hle.trans (Real.exp_le_one_iff.mpr ?_)
  have h1 : κ * s ≤ κ * (Ks * Jr * lm + 1) := mul_le_mul_of_nonneg_left hs hκ
  have hKJ : 0 ≤ κ * Ks * Jr := by positivity
  have h2 : κ * Ks * Jr * lm ≤ κ * Ks * Jr * (Real.log 2 + α * L) := mul_le_mul_of_nonneg_left hlm hKJ
  have hJL : 0 ≤ Jr * L := by positivity
  have h3 : (1201 * κ * Ks * α) * (Jr * L) ≤ 3 / 100 * (Jr * L) := mul_le_mul_of_nonneg_right hα hJL
  have h4 : C * k ≤ C * (Jr + 1 + 20 * η * Jr + q) := mul_le_mul_of_nonneg_left hk hC
  set A0 : ℝ := 2 * C + 2405 * κ + C + C * q
  set A1 : ℝ := κ + 1201 * κ * Ks * Real.log 2 + C + 20 * C * η
  have hA0 : 0 ≤ A0 := by positivity
  have h5 : (Jr - 1) * (A1 - L / 10) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
    linarith
  linarith [h1, h2, h3, h4, h5]

/-! ### Comparison means of single roles -/

section Roles

variable {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} (X : Setup5 γ K' χ n N E G)

theorem blockConst_rpow (K : X.Ty) :
    X.blockConst K ^ X.p.KB =
      Real.exp (X.p.Kpp * X.p.KB * (1 + ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))) := by
  unfold Setup5.blockConst
  rw [← Real.exp_mul]
  ring_nf

/-- The comparison mean of one role, split into the severity buckets `j < J` and `j ≥ J`. -/
theorem role_bound (Cd C : ℝ) (hC : 0 ≤ C) (hCd : Cd ≤ C) (x : CubeVertex n) :
    Cd * X.blockConst (X.g.evenType (X.p.J n) x) ^ X.p.KB *
        (if X.g.low (X.p.J n) x then 1 else
          Real.exp (Cd * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ))) ≤
      (if X.g.severity x < X.p.J n then
          C * Real.exp (X.p.Kpp * X.p.KB * 1204) * Real.exp (X.p.Kpp * X.p.KB) ^ X.g.severity x
        else 0) +
        (if X.p.J n ≤ X.g.severity x then
          C * Real.exp (X.p.Kpp * X.p.KB * (1204 + (X.p.J n : ℝ) + 1201 * (X.p.s n : ℝ))) *
            Real.exp (C * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ))
        else 0) := by
  have hκ : 0 ≤ X.p.Kpp * X.p.KB := (mul_pos X.p.hKpp X.p.hKB).le
  rw [blockConst_rpow]
  have hT : (X.g.evenType (X.p.J n) x).2.1 = X.g.typeKeys (X.p.J n) x := rfl
  rw [hT, ← Nat.cast_sum]
  set κ := X.p.Kpp * X.p.KB with hκdef
  set k : ℝ := ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ) with hkdef
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set S : ℕ := ∑ ℓ ∈ X.g.typeKeys (X.p.J n) x, colLen5 (X.p.s n) ℓ with hS
  have hY0 : 0 ≤ Real.exp (κ * (1 + (S : ℝ))) := (Real.exp_pos _).le
  by_cases hj : X.g.severity x < X.p.J n
  · rw [if_pos hj, if_neg (not_le.mpr hj), add_zero]
    have hlow : X.g.low (X.p.J n) x := le_of_lt hj
    rw [if_pos hlow, mul_one]
    have hSle : S ≤ 1203 + X.g.severity x := by
      have h := low_colLen_sum X.g (X.p.J n) (X.p.s n) x (le_of_lt hj)
      rw [if_neg (ne_of_lt hj)] at h
      simp only [coarseChunkCount5] at h
      omega
    have hSle' : (S : ℝ) ≤ 1203 + X.g.severity x := by exact_mod_cast hSle
    have hY : Real.exp (κ * (1 + (S : ℝ))) ≤
        Real.exp (κ * 1204) * Real.exp κ ^ X.g.severity x := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc Cd * Real.exp (κ * (1 + (S : ℝ))) ≤ C * Real.exp (κ * (1 + (S : ℝ))) :=
          mul_le_mul_of_nonneg_right hCd hY0
      _ ≤ C * (Real.exp (κ * 1204) * Real.exp κ ^ X.g.severity x) := mul_le_mul_of_nonneg_left hY hC
      _ = _ := by ring
  · have hj' : X.p.J n ≤ X.g.severity x := le_of_not_gt hj
    rw [if_neg hj, if_pos hj', zero_add]
    have hSle : S ≤ 1203 + X.p.J n + 1201 * X.p.s n := by
      by_cases hlow : X.g.severity x ≤ X.p.J n
      · have h := low_colLen_sum X.g (X.p.J n) (X.p.s n) x hlow
        have he : X.g.severity x = X.p.J n := le_antisymm hlow hj'
        rw [if_pos he] at h
        simp only [coarseChunkCount5] at h
        omega
      · have h := high_colLen_sum X.g (X.p.J n) (X.p.s n) x hlow
        simp only [coarseChunkCount5] at h
        omega
    have hSle' : (S : ℝ) ≤ 1203 + (X.p.J n : ℝ) + 1201 * (X.p.s n : ℝ) := by exact_mod_cast hSle
    have hY : Real.exp (κ * (1 + (S : ℝ))) ≤
        Real.exp (κ * (1204 + (X.p.J n : ℝ) + 1201 * (X.p.s n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hF0 : 0 ≤ (if X.g.low (X.p.J n) x then (1 : ℝ) else Real.exp (Cd * k)) := by
      split_ifs <;> positivity
    have hF : (if X.g.low (X.p.J n) x then (1 : ℝ) else Real.exp (Cd * k)) ≤ Real.exp (C * k) := by
      split_ifs
      · exact Real.one_le_exp (mul_nonneg hC hk0)
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCd hk0)
    calc Cd * Real.exp (κ * (1 + (S : ℝ))) *
          (if X.g.low (X.p.J n) x then (1 : ℝ) else Real.exp (Cd * k))
        ≤ C * Real.exp (κ * (1 + (S : ℝ))) *
          (if X.g.low (X.p.J n) x then (1 : ℝ) else Real.exp (Cd * k)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCd hY0) hF0
      _ ≤ C * Real.exp (κ * (1204 + (X.p.J n : ℝ) + 1201 * (X.p.s n : ℝ))) * Real.exp (C * k) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hY hC) hF hF0 (by positivity)

/-- The average over even roles of the comparison means (05:806–816), at one dimension. -/
theorem average_core (hG : ChunkEstimates5 X.g) (Cd C : ℝ) (hC : 0 ≤ C) (hCd : Cd ≤ C) (hn : 1 ≤ n)
    (hα : 1201 * (X.p.Kpp * X.p.KB) * X.p.Ks * X.p.alpha ≤ 3 / 100)
    (hL1 : Real.log 2 + X.p.Kpp * X.p.KB ≤ 13 / 100 * Real.log n)
    (hL2 : 10 * ((2 * C + 2405 * (X.p.Kpp * X.p.KB) + C + C * X.p.q0) +
      (X.p.Kpp * X.p.KB + 1201 * (X.p.Kpp * X.p.KB) * X.p.Ks * Real.log 2 + C + 20 * C * X.p.eta)) ≤
        Real.log n) :
    (Fintype.card (EvenRole5 n) : ℝ)⁻¹ * ∑ v : EvenRole5 n,
      (Cd * X.blockConst (X.g.evenType (X.p.J n) v.1) ^ X.p.KB *
        (if X.g.low (X.p.J n) v.1 then 1 else
          Real.exp (Cd * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ)))) ≤
      4 * C * Real.exp (X.p.Kpp * X.p.KB * 1204) + 1 := by
  have hn0 : 0 < n := hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hκ : 0 ≤ X.p.Kpp * X.p.KB := (mul_pos X.p.hKpp X.p.hKB).le
  set κ := X.p.Kpp * X.p.KB with hκdef
  set k : ℝ := ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ) with hkdef
  set L := Real.log n with hLdef
  have hL : 0 ≤ L := Real.log_nonneg hnR
  -- the scales `m`, `J`, `s`, `k_*`
  have hnα : 1 ≤ (n : ℝ) ^ X.p.alpha := Real.one_le_rpow hnR X.p.halpha.1.le
  have hm1 : 1 ≤ X.p.m n := by
    have h : (1 : ℝ) ≤ X.p.m n := hnα.trans (Nat.le_ceil _)
    exact_mod_cast h
  have hmR : (1 : ℝ) ≤ X.p.m n := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < X.p.m n := by linarith
  have hJm : X.p.J n ≤ X.p.m n := Lane_sol_s05_h1.J_le_m X.p n hm1
  have hm20 : 1 ≤ (X.p.m n : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow hmR (by norm_num)
  have hJ1 : 1 ≤ X.p.J n := Nat.le_floor (by simpa using hm20)
  have hJlt : (X.p.m n : ℝ) ^ (1 / 20 : ℝ) < X.p.J n + 1 := Nat.lt_floor_add_one _
  have hJR : (1 : ℝ) ≤ X.p.J n := by exact_mod_cast hJ1
  have hlogm0 : 0 ≤ Real.log (X.p.m n) := Real.log_nonneg hmR
  have hlogm20 : Real.log (X.p.m n) ≤ 20 * X.p.J n := by
    have h1 : Real.log ((X.p.m n : ℝ) ^ (1 / 20 : ℝ)) = 1 / 20 * Real.log (X.p.m n) :=
      Real.log_rpow hmpos _
    have h2 : Real.log ((X.p.m n : ℝ) ^ (1 / 20 : ℝ)) ≤ (X.p.m n : ℝ) ^ (1 / 20 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hlogm : Real.log (X.p.m n) ≤ Real.log 2 + X.p.alpha * L := by
    have hm2 : (X.p.m n : ℝ) ≤ 2 * (n : ℝ) ^ X.p.alpha := by
      have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le X.p.alpha)
      change (⌈(n : ℝ) ^ X.p.alpha⌉₊ : ℝ) ≤ _
      linarith
    calc Real.log (X.p.m n) ≤ Real.log (2 * (n : ℝ) ^ X.p.alpha) := Real.log_le_log hmpos hm2
      _ = Real.log 2 + X.p.alpha * L := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hnpos]
  have hs : (X.p.s n : ℝ) ≤ X.p.Ks * X.p.J n * Real.log (X.p.m n) + 1 := by
    have h0 : 0 ≤ X.p.Ks * (X.p.J n : ℝ) * Real.log (X.p.m n) := by
      have := X.p.hKs
      positivity
    have h := Nat.ceil_lt_add_one h0
    change (⌈X.p.Ks * (X.p.J n : ℝ) * Real.log (X.p.m n : ℝ)⌉₊ : ℝ) ≤ _
    linarith
  have hq0 : (0 : ℝ) < X.p.q0 := by exact_mod_cast X.p.hq0.1
  have hη : 0 < X.p.eta := X.p.heta.1
  have hk' : k ≤ (X.p.m n : ℝ) ^ (1 / 200 : ℝ) + X.p.eta * Real.log (X.p.m n) + X.p.q0 := by
    have hu : ((X.p.uStarSeg n : ℕ) : ℝ) < X.p.eta * Real.log (X.p.m n) / X.p.q0 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hur : (X.p.q0 : ℝ) * X.p.uStarSeg n ≤ X.p.eta * Real.log (X.p.m n) + X.p.q0 := by
      have h := mul_lt_mul_of_pos_left hu hq0
      have e : (X.p.q0 : ℝ) * (X.p.eta * Real.log (X.p.m n) / X.p.q0) =
          X.p.eta * Real.log (X.p.m n) := by field_simp
      rw [mul_add, e, mul_one] at h
      linarith
    rw [hkdef]
    push_cast
    rcases eq_or_lt_of_le (Nat.cast_nonneg (X.p.uStarSeg n) : (0 : ℝ) ≤ X.p.uStarSeg n) with h0 | hpos
    · rw [← h0]
      simp only [mul_zero, zero_mul]
      positivity
    · have hupos : (0 : ℝ) < X.p.q0 * X.p.uStarSeg n := mul_pos hq0 hpos
      have hb : ((X.p.usedBlocks n : ℕ) : ℝ) <
          (X.p.m n : ℝ) ^ (1 / 200 : ℝ) / (X.p.q0 * X.p.uStarSeg n) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have h := mul_lt_mul_of_pos_left hb hupos
      have e : ((X.p.q0 : ℝ) * X.p.uStarSeg n) *
          ((X.p.m n : ℝ) ^ (1 / 200 : ℝ) / (X.p.q0 * X.p.uStarSeg n)) =
          (X.p.m n : ℝ) ^ (1 / 200 : ℝ) := by field_simp
      rw [mul_add, e, mul_one] at h
      linarith
  have hk : k ≤ X.p.J n + 1 + 20 * X.p.eta * X.p.J n + X.p.q0 := by
    have h1 : (X.p.m n : ℝ) ^ (1 / 200 : ℝ) ≤ (X.p.m n : ℝ) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
    have h2 : X.p.eta * Real.log (X.p.m n) ≤ X.p.eta * (20 * X.p.J n) :=
      mul_le_mul_of_nonneg_left hlogm20 hη.le
    linarith
  -- the bucket `j ≥ J`
  set W : ℝ := C * Real.exp (κ * (1204 + (X.p.J n : ℝ) + 1201 * (X.p.s n : ℝ))) * Real.exp (C * k)
    with hWdef
  have hW0 : 0 ≤ W := by positivity
  have hbig : 2 * W * Real.exp (L * (-(13 / 100) * X.p.J n)) ≤ 1 :=
    big_bucket_small hC hκ X.p.hKs.le hq0.le hJR hL hα hs hlogm hk hL2
  -- counting
  have hEv : (0 : ℝ) < Fintype.card (EvenRole5 n) := by
    have h := even_total hn0
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
  have hEv0 := hEv.le
  have hfilt (P : EvenRole5 n → Prop) [DecidablePred P] :
      ((Finset.univ.filter P).card : ℝ) ≤ Fintype.card (EvenRole5 n) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hratio : Real.exp κ * (n : ℝ) ^ (-(13 / 100 : ℝ)) ≤ 1 / 2 := by
    have h13 : 2 * Real.exp κ ≤ (n : ℝ) ^ (13 / 100 : ℝ) := by
      rw [Real.rpow_def_of_pos hnpos]
      calc 2 * Real.exp κ = Real.exp (Real.log 2 + κ) := by
            rw [Real.exp_add, Real.exp_log (by norm_num)]
        _ ≤ Real.exp (Real.log n * (13 / 100)) := Real.exp_le_exp.mpr (by linarith)
    have hpos : 0 < (n : ℝ) ^ (13 / 100 : ℝ) := by positivity
    rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  have hlevel (h : ℕ) (hh : h < X.p.J n) :
      Real.exp κ ^ h * ((Finset.univ.filter fun v : EvenRole5 n => X.g.severity v.1 = h).card : ℝ) ≤
        2 * (1 / 2 : ℝ) ^ h * Fintype.card (EvenRole5 n) := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · have := hfilt (fun v : EvenRole5 n => X.g.severity v.1 = 0)
      simp only [pow_zero, one_mul, mul_one]
      linarith
    · have hcnt := even_event_card hn0 (fun x => h ≤ X.g.severity x) _
        (hG.severity_tail h hpos (by omega))
      have hsub2 : ((Finset.univ.filter fun v : EvenRole5 n => X.g.severity v.1 = h).card : ℝ) ≤
          ((Finset.univ.filter fun v : EvenRole5 n => h ≤ X.g.severity v.1).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (fun v hv => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          omega)
      have hpow : (n : ℝ) ^ (-(13 / 100 : ℝ) * (h : ℝ)) = ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ h := by
        rw [Real.rpow_mul hnpos.le, Real.rpow_natCast]
      have hgeo : Real.exp κ ^ h * ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ h ≤ (1 / 2 : ℝ) ^ h := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hratio h
      calc Real.exp κ ^ h * ((Finset.univ.filter fun v : EvenRole5 n => X.g.severity v.1 = h).card : ℝ)
          ≤ Real.exp κ ^ h * (2 * (n : ℝ) ^ (-(13 / 100 : ℝ) * (h : ℝ)) * Fintype.card (EvenRole5 n)) :=
            mul_le_mul_of_nonneg_left (hsub2.trans hcnt) (by positivity)
        _ = 2 * (Real.exp κ ^ h * ((n : ℝ) ^ (-(13 / 100 : ℝ))) ^ h) * Fintype.card (EvenRole5 n) := by
            rw [hpow]; ring
        _ ≤ 2 * (1 / 2 : ℝ) ^ h * Fintype.card (EvenRole5 n) := by gcongr
  -- the bucket `j < J`
  have hA : ∑ v : EvenRole5 n, (if X.g.severity v.1 < X.p.J n then
        C * Real.exp (κ * 1204) * Real.exp κ ^ X.g.severity v.1 else 0) ≤
      4 * C * Real.exp (κ * 1204) * Fintype.card (EvenRole5 n) := by
    have e : ∑ v : EvenRole5 n, (if X.g.severity v.1 < X.p.J n then
          C * Real.exp (κ * 1204) * Real.exp κ ^ X.g.severity v.1 else 0) =
        ∑ h ∈ Finset.range (X.p.J n), ∑ v : EvenRole5 n,
          (if X.g.severity v.1 = h then C * Real.exp (κ * 1204) * Real.exp κ ^ h else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_range]
    rw [e]
    calc ∑ h ∈ Finset.range (X.p.J n), ∑ v : EvenRole5 n,
          (if X.g.severity v.1 = h then C * Real.exp (κ * 1204) * Real.exp κ ^ h else 0)
        ≤ ∑ h ∈ Finset.range (X.p.J n),
            C * Real.exp (κ * 1204) * (2 * (1 / 2 : ℝ) ^ h * Fintype.card (EvenRole5 n)) := by
          refine Finset.sum_le_sum fun h hh => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have := hlevel h (Finset.mem_range.mp hh)
          have hc : 0 ≤ C * Real.exp (κ * 1204) := by positivity
          calc ((Finset.univ.filter fun v : EvenRole5 n => X.g.severity v.1 = h).card : ℝ) *
                (C * Real.exp (κ * 1204) * Real.exp κ ^ h)
              = C * Real.exp (κ * 1204) * (Real.exp κ ^ h *
                ((Finset.univ.filter fun v : EvenRole5 n => X.g.severity v.1 = h).card : ℝ)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left this hc
      _ = 2 * C * Real.exp (κ * 1204) * Fintype.card (EvenRole5 n) *
            ∑ h ∈ Finset.range (X.p.J n), (1 / 2 : ℝ) ^ h := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          ring
      _ ≤ 2 * C * Real.exp (κ * 1204) * Fintype.card (EvenRole5 n) * 2 := by
          have hgeo := sum_geometric_two_le (X.p.J n)
          have hc : 0 ≤ 2 * C * Real.exp (κ * 1204) * Fintype.card (EvenRole5 n) := by positivity
          exact mul_le_mul_of_nonneg_left (by simpa using hgeo) hc
      _ = 4 * C * Real.exp (κ * 1204) * Fintype.card (EvenRole5 n) := by ring
  -- the bucket `j ≥ J`
  have hB : ∑ v : EvenRole5 n, (if X.p.J n ≤ X.g.severity v.1 then W else 0) ≤
      Fintype.card (EvenRole5 n) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcnt := even_event_card hn0 (fun x => X.p.J n ≤ X.g.severity x) _
      (hG.severity_tail (X.p.J n) hJ1 hJm)
    have hrp : (n : ℝ) ^ (-(13 / 100 : ℝ) * (X.p.J n : ℝ)) =
        Real.exp (L * (-(13 / 100) * X.p.J n)) := Real.rpow_def_of_pos hnpos _
    rw [hrp] at hcnt
    calc ((Finset.univ.filter fun v : EvenRole5 n => X.p.J n ≤ X.g.severity v.1).card : ℝ) * W
        ≤ (2 * Real.exp (L * (-(13 / 100) * X.p.J n)) * Fintype.card (EvenRole5 n)) * W :=
          mul_le_mul_of_nonneg_right hcnt hW0
      _ = (2 * W * Real.exp (L * (-(13 / 100) * X.p.J n))) * Fintype.card (EvenRole5 n) := by ring
      _ ≤ 1 * Fintype.card (EvenRole5 n) := mul_le_mul_of_nonneg_right hbig hEv0
      _ = Fintype.card (EvenRole5 n) := one_mul _
  apply (inv_mul_le_iff₀ hEv).mpr
  calc ∑ v : EvenRole5 n, (Cd * X.blockConst (X.g.evenType (X.p.J n) v.1) ^ X.p.KB *
        (if X.g.low (X.p.J n) v.1 then 1 else Real.exp (Cd * k)))
      ≤ ∑ v : EvenRole5 n, ((if X.g.severity v.1 < X.p.J n then
          C * Real.exp (κ * 1204) * Real.exp κ ^ X.g.severity v.1 else 0) +
          (if X.p.J n ≤ X.g.severity v.1 then W else 0)) :=
        Finset.sum_le_sum fun v _ => role_bound X Cd C hC hCd v.1
    _ = ∑ v : EvenRole5 n, (if X.g.severity v.1 < X.p.J n then
          C * Real.exp (κ * 1204) * Real.exp κ ^ X.g.severity v.1 else 0) +
        ∑ v : EvenRole5 n, (if X.p.J n ≤ X.g.severity v.1 then W else 0) := Finset.sum_add_distrib
    _ ≤ 4 * C * Real.exp (κ * 1204) * Fintype.card (EvenRole5 n) + Fintype.card (EvenRole5 n) :=
        add_le_add hA hB
    _ = Fintype.card (EvenRole5 n) * (4 * C * Real.exp (κ * 1204) + 1) := by ring

end Roles

/-! ### The average with the parameter order (α after `K_B`) -/

/-- Lower bound on `log n` for the average. -/
def logBound (p : Params5 γ K' χ) (C : ℝ) : ℝ :=
  max (10 * ((2 * C + 2405 * (p.Kpp * p.KB) + C + C * p.q0) +
      (p.Kpp * p.KB + 1201 * (p.Kpp * p.KB) * p.Ks * Real.log 2 + C + 20 * C * p.eta)))
    ((Real.log 2 + p.Kpp * p.KB) / (13 / 100))

/-- SUB-LEMMA E with `evenD` and `kStarLen` unfolded (05:806–816). -/
theorem mean_average_explicit (Cd : Pre65 → ℝ) : ∃ R : ParamReq5, ∀ p : Params5 γ K' χ, R.Holds p →
    ∃ D₀ : ℝ, 0 ≤ D₀ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ChunkEstimates5 X.g →
        (Fintype.card (EvenRole5 n) : ℝ)⁻¹ * ∑ v : EvenRole5 n,
          (Cd p.pre6 * X.blockConst (X.g.evenType (X.p.J n) v.1) ^ X.p.KB *
            (if X.g.low (X.p.J n) v.1 then 1 else
              Real.exp (Cd p.pre6 * ((X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) : ℝ)))) ≤ D₀ := by
  let R : ParamReq5 :=
    { Kcap := fun _ => 0, Kpp := fun _ => 0, Kh := fun _ => 0, K1 := fun _ => 0, K2 := fun _ => 0,
      KD := fun _ => 0, Ks := fun _ => 0, KB := fun _ => 0,
      alpha := fun x => 3 / (100 * (1201 * |x.1.1.1.1.1.2.2.1 * x.2 * x.1.2| + 1)),
      alpha_pos := fun x => by positivity }
  refine ⟨R, fun p hp => ?_⟩
  have hα : p.alpha ≤ 3 / (100 * (1201 * |p.Kpp * p.KB * p.Ks| + 1)) := hp.2.2.2.2.2.2.2.2
  have hP : 0 < p.Kpp * p.KB * p.Ks := mul_pos (mul_pos p.hKpp p.hKB) p.hKs
  have hα' : 1201 * (p.Kpp * p.KB) * p.Ks * p.alpha ≤ 3 / 100 := by
    rw [abs_of_pos hP] at hα
    have hden : 0 < 100 * (1201 * (p.Kpp * p.KB * p.Ks) + 1) := by positivity
    rw [le_div_iff₀ hden] at hα
    have h0 : 0 ≤ p.alpha := p.halpha.1.le
    nlinarith
  have hC0 : 0 ≤ max (Cd p.pre6) 0 := le_max_right _ _
  refine ⟨4 * max (Cd p.pre6) 0 * Real.exp (p.Kpp * p.KB * 1204) + 1, by positivity,
    ⌈Real.exp (logBound p (max (Cd p.pre6) 0))⌉₊ + 1, ?_⟩
  intro n hn N E G X hXp hG
  subst hXp
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlog : logBound X.p (max (Cd X.p.pre6) 0) ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]
    have h1 := Nat.le_ceil (Real.exp (logBound X.p (max (Cd X.p.pre6) 0)))
    have h2 : ((⌈Real.exp (logBound X.p (max (Cd X.p.pre6) 0))⌉₊ + 1 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hn
    push_cast at h2
    linarith
  have hL1 : Real.log 2 + X.p.Kpp * X.p.KB ≤ 13 / 100 * Real.log n := by
    have h := (le_max_right _ _).trans hlog
    rw [div_le_iff₀ (by norm_num)] at h
    linarith
  have hL2 := (le_max_left _ _).trans hlog
  exact average_core X hG (Cd X.p.pre6) (max (Cd X.p.pre6) 0) hC0 (le_max_left _ _) hn1 hα' hL1 hL2

end

end HypercubeRamsey.Setup5.Lane_opus_s05_e
