import HypercubeRamsey.S05.History_sol_s05_hist1f_apply
import HypercubeRamsey.S05.History_sol_s05_hist1e_apply
import HypercubeRamsey.S05.History_sol_s05_hist1c_apply

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

private theorem card_fin_prefix {k t : ℕ} (h : k ≤ t) :
    (Finset.univ.filter (fun s : Fin t => (s : ℕ) < k)).card = k := by
  let S := Finset.univ.filter (fun s : Fin t => (s : ℕ) < k)
  let e : Fin k ≃ S := {
    toFun := fun s => ⟨Fin.castLE h s, by simp [S, s.isLt]⟩
    invFun := fun s => ⟨s.1.val, (Finset.mem_filter.mp s.2).2⟩
    left_inv := by intro s; rfl
    right_inv := by intro s; rfl }
  simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr e).symm

theorem typeBlocks_le_blockBound (K : X.Ty) : X.p.typeBlocks n K ≤ X.blockBound := by
  cases he : K.2.2 with
  | none => simpa [Params5.typeBlocks, he, Setup5.blockBound] using Nat.le_max_left _ _
  | some j =>
    have hj : X.p.lowBlocks n j ≤ Finset.univ.sup (fun j : Fin (X.p.J n + 1) => X.p.lowBlocks n j) :=
      Finset.le_sup (f := fun j : Fin (X.p.J n + 1) => X.p.lowBlocks n j) (Finset.mem_univ j)
    simpa only [Params5.typeBlocks, he, Setup5.blockBound] using
      hj.trans (Nat.le_max_right (X.p.poolBlocks n) _)

/-- The low reference list has at most one designation per cube neighbor. -/
theorem lowRefs_card_le_dimension (r : X.AbsRecord) (hr : X.RecOccurs r) :
    (lowRefs X r).card ≤ n := by
  have hfirst : (lowRefs X r).card ≤ r.2.2.1.card := Finset.card_image_le
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  obtain ⟨y, μ, hrecord⟩ := hr
  calc
    _ ≤ r.2.2.1.card := hfirst
    _ = (((Setup5.evenNbrs y).filter fun a =>
        r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          r.1.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome).image
        (fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
          X.g.optionalKey (X.p.J n) a.1))).card := congrArg Finset.card hrecord.2.2.1
    _ ≤ ((Setup5.evenNbrs y).filter fun a =>
        r.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          r.1.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome).card := Finset.card_image_le
    _ ≤ (Setup5.evenNbrs y).card := Finset.card_filter_le _ _
    _ ≤ n := evenNbrs_card_le y

private theorem roleKey_level_of_low {n m J : ℕ} (g : ChunkGeometry5 n m)
    (x : CubeVertex n) (h : (g.roleKey J x).isLeft) : (g.roleKey J x).level = g.severity x := by
  by_cases hx : g.severity x ≤ J
  · simp [ChunkGeometry5.roleKey, hx, HiddenKey5.level]
  · simp [ChunkGeometry5.roleKey, hx] at h

private theorem type_severity_of_some {n m J : ℕ} (g : ChunkGeometry5 n m)
    (x : CubeVertex n) (j : Fin (J + 1)) (h : (g.evenType J x).2.2 = some j) : g.severity x = j.val := by
  by_cases hx : g.severity x ≤ J
  · simp only [ChunkGeometry5.evenType, hx, dite_true, Option.some.injEq] at h
    exact congrArg Fin.val h
  · simp [ChunkGeometry5.evenType, hx] at h

/-- Every same-mode low reference has length at least the neighboring minimum `k'_j`. -/
theorem lowRefs_length_lower (r : X.AbsRecord) (hr : X.RecOccurs r) (hl : r.1.isLeft)
    (c : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound)) (hc : c ∈ lowRefs X r) :
    X.p.kPrime n r.1.level ≤ X.refLen c.2.1 c.2.2 := by
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hc
  have hm := low_record_ref_mode X r hr hl d hd
  cases htype : d.2.1.2.2 with
  | none => simp [htype] at hm
  | some j =>
    obtain ⟨y, μ, hrecord⟩ := hr
    have hly : (X.g.roleKey (X.p.J n) y.1).isLeft := by simpa only [hrecord.1] using hl
    have hlevel : r.1.level = X.g.severity y.1 := by
      rw [← hrecord.1]
      exact roleKey_level_of_low X.g y.1 hly
    rw [hrecord.2.2.1] at hd
    letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hd
    have htya : (X.g.evenType (X.p.J n) a.1).2.2 = some j :=
      (congrArg (fun d => d.2.1.2.2) hea).trans htype
    have hsev := type_severity_of_some X.g a.1 j htya
    have hadj := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    obtain ⟨b, hb⟩ := cube_adj_eq_flip hadj
    have hbounds : X.g.severity a.1 ≤ X.g.severity y.1 + 1 ∧
        X.g.severity y.1 ≤ X.g.severity a.1 + 1 := by
      rw [hb]
      exact severity_flip_bounds X.g y.1 b
    have hj : j.val = r.1.level ∨ j.val = r.1.level + 1 ∨ j.val = r.1.level - 1 := by omega
    have hmin : X.p.kPrime n r.1.level ≤ X.p.q0 * X.p.uSeg n j.val * X.p.lowBlocks n j.val := by
      unfold Params5.kPrime
      rcases hj with hj | hj | hj
      · rw [hj]
        exact (Nat.min_le_left _ _).trans (Nat.min_le_left _ _)
      · rw [hj]
        exact (Nat.min_le_left _ _).trans (Nat.min_le_right _ _)
      · rw [hj]
        exact Nat.min_le_right _ _
    have hlen : X.refLen c.2.1 c.2.2 = X.p.q0 * X.p.uSeg n j.val * X.p.lowBlocks n j.val := by
      have hty := congrArg (fun d : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound) => d.2.1) he
      have hmask := congrArg (fun d : Fin (X.p.T n) × X.Ty × Finset (Fin X.blockBound) => d.2.2) he
      unfold Setup5.refLen
      rw [← hmask, ← hty, card_fin_prefix (typeBlocks_le_blockBound X d.2.1)]
      simp [Params5.typeBlocks, Params5.typeSegs, htype, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    exact hmin.trans_eq hlen.symm

/-- All low targets satisfy the full Step 3 bound once the polynomial union is
absorbed by `k'_j`; this includes the interface mask gate. -/
theorem step3_low_dimension_bound (H : X.KeyHist) (r : X.AbsRecord) (hr : X.RecOccurs r)
    (hl : r.1.isLeft) :
    (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
      (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r) ≤
      ((n : ℝ) + 1) * Real.exp (-(X.p.delta * X.p.kPrime n r.1.level)) := by
  let ε := Real.exp (-(X.p.delta * X.p.kPrime n r.1.level))
  have hlo : (match r.1 with
      | .inl k => Real.exp (-(X.p.delta * X.p.kPrime n k.2.2.val))
      | .inr _ => Real.exp (-(X.p.delta * X.p.s n))) ≤ ε := by
    cases he : r.1 with
    | inl k => simp [he, ε, HiddenKey5.level]
    | inr i => simp [he] at hl
  have hrat (c) (hc : c ∈ lowRefs X r) :
      Real.exp (-(X.p.delta * X.refLen c.2.1 c.2.2 * colLen5 (X.p.s n) r.1)) ≤ ε := by
    have hlen := lowRefs_length_lower X r hr hl c hc
    have hcol : colLen5 (X.p.s n) r.1 = 1 := by
      cases he : r.1 with
      | inl k => simp [he, colLen5]
      | inr i => simp [he] at hl
    rw [hcol, Nat.cast_one, mul_one]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (show (X.p.kPrime n r.1.level : ℝ) ≤ X.refLen c.2.1 c.2.2 by
      exact_mod_cast hlen) X.p.hdelta.1.le
    exact neg_le_neg hh
  have hh := step3_low_finite_bound X H r hr hl ε (Real.exp_pos _).le hlo hrat
  exact hh.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.add_le_add_right (lowRefs_card_le_dimension X r hr) 1) (Real.exp_pos _).le)

/-- Every low tuple has at least the dimension-power length, uniformly in severity. -/
theorem low_length_power_lower (p : Params5 γ K' χ) (n j : ℕ)
    (hm : 1 ≤ (p.m n : ℝ)) (hu : 0 < (p.q0 : ℝ) * p.uSeg n j) :
    p.K2 * (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ (p.q0 * p.uSeg n j * p.lowBlocks n j : ℕ) := by
  have hc : p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) + (p.m n : ℝ) ^ (1 / 50 : ℝ)) /
      ((p.q0 : ℝ) * p.uSeg n j) ≤ (p.lowBlocks n j : ℝ) := Nat.le_ceil _
  have hh := (div_le_iff₀ hu).mp hc
  have hl := Real.log_nonneg hm
  have hj : 0 ≤ (j : ℝ) + 4 := by positivity
  have he : 0 ≤ p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) :=
    mul_nonneg p.hK2.le (mul_nonneg hj hl)
  push_cast
  nlinarith

theorem kPrime_power_lower (p : Params5 γ K' χ) (n j : ℕ)
    (hm : 1 ≤ (p.m n : ℝ)) (hu : ∀ j, 0 < (p.q0 : ℝ) * p.uSeg n j) :
    p.K2 * (p.m n : ℝ) ^ (1 / 50 : ℝ) ≤ (p.kPrime n j : ℝ) := by
  simp only [Params5.kPrime, Nat.cast_min]
  exact le_min (le_min (low_length_power_lower p n j hm (hu j))
    (low_length_power_lower p n (j + 1) hm (hu _)))
    (low_length_power_lower p n (j - 1) hm (hu _))

/-- The neighboring length absorbs the entire dimension-size reference union. -/
theorem eventually_low_union_absorbed (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ j : ℕ,
      ((n : ℝ) + 1) * Real.exp (-(p.delta * p.kPrime n j)) ≤
        Real.exp (-((p.delta / 2) * p.kPrime n j)) := by
  have hc : 0 < p.delta * p.K2 / 4 := div_pos (mul_pos p.hdelta.1 p.hK2) (by norm_num)
  have hr : 0 < p.alpha / 50 := div_pos p.halpha.1 (by norm_num)
  have hsmall := ((isLittleO_log_rpow_atTop hr).comp_tendsto
    tendsto_natCast_atTop_atTop).bound hc
  obtain ⟨n₁, hn₁⟩ := eventually_prefix_scale_one p
  have hM := (Lane_sol_s05_h1.tendsto_m p).eventually (eventually_ge_atTop (1 : ℝ))
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      ((n : ℝ) + 1) * Real.exp (-(p.delta * p.kPrime n j)) ≤
        Real.exp (-((p.delta / 2) * p.kPrime n j)) := by
    filter_upwards [hsmall, hM, eventually_ge_atTop n₁, eventually_ge_atTop (2 : ℕ)] with n hsmall hm hn hn2
    intro j
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hs : Real.log (n : ℝ) ≤ p.delta * p.K2 / 4 * (n : ℝ) ^ (p.alpha / 50) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hlog,
        abs_of_nonneg (Real.rpow_nonneg hn0 _), Function.comp_apply] using hsmall
    have hmceil : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := Nat.le_ceil _
    have hpow : (n : ℝ) ^ (p.alpha / 50) ≤ (p.m n : ℝ) ^ (1 / 50 : ℝ) := by
      calc
        _ = ((n : ℝ) ^ p.alpha) ^ (1 / 50 : ℝ) := by
          rw [← Real.rpow_mul hn0]
          congr 1
          ring
        _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hn0 _) hmceil (by norm_num)
    have hk := kPrime_power_lower p n j hm (fun j => lt_of_lt_of_le (by norm_num) (hn₁ n hn j))
    have hlog2 : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
      have hp : 0 < (n : ℝ) + 1 := by positivity
      have hh := Real.log_le_log hp (show (n : ℝ) + 1 ≤ (n : ℝ) ^ 2 by nlinarith)
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
    have hbound : Real.log ((n : ℝ) + 1) ≤ (p.delta / 2) * p.kPrime n j := by
      have hh := mul_le_mul_of_nonneg_left hpow hc.le
      have hhk := mul_le_mul_of_nonneg_left hk p.hdelta.1.le
      nlinarith
    rw [← Real.exp_log (by positivity : 0 < (n : ℝ) + 1), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  exact eventually_atTop.1 hall

/-- The complete low half of the frozen Step 3 raw estimate, with rate `δ/2`.
It is uniform in the other hidden columns and requires no conditioning assumptions. -/
theorem step3_low_eventual_bound (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
      (X : Setup5 γ K' χ n N E G), X.p = p → ∀ (H : X.KeyHist) (r : X.AbsRecord),
      X.RecOccurs r → r.1.isLeft →
      (∑ θ : Fin (colLen5 (X.p.s n) r.1) → Fin N,
        (∏ h, (X.prior H.1 r.1).w (θ h)) * X.step3Rate (X.withCol H r.1 θ) r) ≤
        Real.exp (-((p.delta / 2) * X.p.kPrime n r.1.level)) := by
  obtain ⟨n₀, hn₀⟩ := eventually_low_union_absorbed p
  refine ⟨n₀, ?_⟩
  intro n hn N E G X hXp H r hr hl
  apply (step3_low_dimension_bound X H r hr hl).trans
  simpa only [hXp] using hn₀ n hn r.1.level

end
end HypercubeRamsey.Lane_sol_s05_hist1b
