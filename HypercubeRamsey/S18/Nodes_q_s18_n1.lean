import HypercubeRamsey.S18.Defs
import HypercubeRamsey.Framework.Minimax

namespace HypercubeRamsey.Lane_q_s18_n1

open scoped BigOperators
open HypercubeRamsey.S18

private theorem law_eq_of_weights {N : ℕ} {μ ν : Law N}
    (h : ∀ x, μ.w x = ν.w x) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

private theorem normalize_indicator_eq_cond {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : HypercubeRamsey.S18.LateData hPT)
    (μ : Law (T.S.N k)) (A : Finset (Fin (T.S.N k)))
    (hA : 0 < ∑ x ∈ A, μ.w x) :
    D.normalize (fun x => μ.w x * (if x ∈ A then (1 : ℝ) else 0)) = μ.cond A hA := by
  classical
  have hmass : (∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0)) =
      ∑ x ∈ A, μ.w x := by
    simp [Finset.sum_ite_mem]
  have hnonneg : ∀ x, 0 ≤ μ.w x * (if x ∈ A then (1 : ℝ) else 0) := by
    intro x
    split_ifs with hx
    · exact mul_nonneg (μ.nonneg x) (by norm_num)
    · simp
  have hpos : 0 < ∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0) := by
    rw [hmass]
    exact hA
  have hbranch :
      (∀ x, 0 ≤ μ.w x * (if x ∈ A then (1 : ℝ) else 0)) ∧
        0 < ∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0) := ⟨hnonneg, hpos⟩
  apply law_eq_of_weights
  intro x
  simp only [HypercubeRamsey.S18.LateData.normalize, dif_pos hbranch]
  simp only [Law.cond, Law.restrict]
  by_cases hx : x ∈ A <;> simp [hx]

private theorem uniformWeight_total {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) :
    (∑ y, if y ∈ S then (1 / (S.card : ℝ)) else 0) = 1 := by
  classical
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  field_simp

private theorem weighted_sub_sum {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : (∑ a, w a) = 1) (g : A → ℝ) (c : ℝ) :
    (∑ a, w a * (g a - c)) = (∑ a, w a * g a) - c := by
  calc
    (∑ a, w a * (g a - c)) = ∑ a, (w a * g a - w a * c) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a, w a * g a) - (∑ a, w a * c) := by rw [Finset.sum_sub_distrib]
    _ = (∑ a, w a * g a) - c := by rw [← Finset.sum_mul, hw]; ring

private theorem exists_balanced_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (v : A → B → ℝ) (cap : ℝ)
    (hprice : ∀ q : FinLaw B, ∃ a,
      (∑ b, q.w b * v a b) ≤ cap) :
    ∃ p : FinLaw A, ∀ b, (∑ a, p.w a * v a b) ≤ cap := by
  have hpriceProb : ∀ q : FinProb B, ∃ a,
      (∑ b, q.w b * (v a b - cap)) ≤ 0 := by
    intro q
    let qLaw : FinLaw B := ⟨q.w, q.nonneg, q.sum_eq_one⟩
    obtain ⟨a, ha⟩ := hprice qLaw
    refine ⟨a, ?_⟩
    rw [weighted_sub_sum q.w q.sum_eq_one (fun b => v a b) cap]
    linarith
  obtain ⟨p, hp⟩ := finite_minimax (fun a b => v a b - cap) hpriceProb
  let pLaw : FinLaw A := ⟨p.w, p.nonneg, p.sum_eq_one⟩
  refine ⟨pLaw, ?_⟩
  intro b
  have hb : (∑ a, pLaw.w a * (v a b - cap)) ≤ 0 := by
    simpa [pLaw] using hp b
  have heq := weighted_sub_sum pLaw.w pLaw.sum_one (fun a => v a b) cap
  rw [heq] at hb
  linarith

private theorem labelWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
    0 ≤ D.labelWeight j side tests y := by
  unfold LateData.labelWeight
  split_ifs with hmass hpass
  · apply div_nonneg
    · unfold LateData.maskWeight
      split_ifs <;> positivity
    · exact (Real.exp_pos _).le.trans hmass
  · simp
  · unfold LateData.maskWeight
    split_ifs <;> positivity

private theorem labelWeight_total {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmask : side.1.1.Nonempty) :
    (∑ y, D.labelWeight j side tests y) = 1 := by
  classical
  unfold LateData.labelWeight
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side tests
  · simp_rw [if_pos hmass]
    have hden : 0 < D.retainedMass j side tests :=
      (Real.exp_pos _).trans_le hmass
    calc
      (∑ y, if D.passes j side tests y then
          D.maskWeight side y / D.retainedMass j side tests else 0) =
          (∑ y, if D.passes j side tests y then D.maskWeight side y else 0) /
            D.retainedMass j side tests := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro y hy
              split_ifs <;> simp
      _ = D.retainedMass j side tests / D.retainedMass j side tests := by
        simp [LateData.retainedMass]
      _ = 1 := div_self (ne_of_gt hden)
  · simp_rw [if_neg hmass]
    have hmasktotal := uniformWeight_total side.1.1 hmask
    simpa [LateData.maskWeight] using hmasktotal

private theorem lateError_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m) (remaining : ℕ) :
    0 < lateError κ T k PT i remaining := by
  have hd : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold lateError
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hd _) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)

private theorem error_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (j : Fin D.geom.r) : 0 ≤ D.error v j := by
  unfold LateData.error
  exact (lateError_pos (κ := κ) (T := T) (k := k) (PT := PT) (D.geom.patchOf v)
    (D.geom.r - j.val)).le

private theorem smallErrors_sum_control {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (v : Pos T k) :
    (∑ j : Fin D.geom.r, D.error v j) ≤ Real.log 2 / 1000 := by
  let i := D.geom.patchOf v
  have hmax : 1 ≤ (max 1 (PT.tiling.P i).h : ℝ) := le_max_left _ _
  have hsum_nonneg : 0 ≤ ∑ j : Fin D.geom.r,
      lateError κ T k PT i (D.geom.r - j.val) :=
    Finset.sum_nonneg fun j hj => by
      exact (lateError_pos (κ := κ) (T := T) (k := k) (PT := PT) i
        (D.geom.r - j.val)).le
  have hbound := hsmall i
  calc
    (∑ j : Fin D.geom.r, D.error v j) =
        ∑ j : Fin D.geom.r, lateError κ T k PT i (D.geom.r - j.val) := by
          simp [LateData.error, i]
    _ ≤ (max 1 (PT.tiling.P i).h : ℝ) *
          (∑ j : Fin D.geom.r, lateError κ T k PT i (D.geom.r - j.val)) := by
      calc
        _ = 1 * (∑ j : Fin D.geom.r,
            lateError κ T k PT i (D.geom.r - j.val)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmax hsum_nonneg
    _ ≤ Real.log 2 / 1000 := hbound

/-- The finite reverse geometric sum is bounded by the infinite geometric sum. -/
theorem finite_reverse_geometric_sum_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (r : ℕ) :
    (∑ j : Fin r, q ^ (r - j.val)) ≤ 1 / (1 - q) := by
  let S : ℕ → ℝ := fun r => ∑ j : Fin r, q ^ (r - j.val)
  have hform : ∀ r, S r * (1 - q) = q - q ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [S]
    | succ r ih =>
      have hrec : S (r + 1) = q ^ (r + 1) + S r := by
        dsimp [S]
        rw [Fin.sum_univ_succ]
        simp
      rw [hrec]
      calc
        (q ^ (r + 1) + S r) * (1 - q) =
            q ^ (r + 1) * (1 - q) + (q - q ^ (r + 1)) := by rw [add_mul, ih]
        _ = q - q ^ (r + 1) * q := by ring
        _ = q - q ^ (r + 2) := by
          congr 2
  have hden : 0 < 1 - q := by linarith
  have hnum : q - q ^ (r + 1) ≤ 1 := by
    have hp : 0 ≤ q ^ (r + 1) := pow_nonneg hq0.le _
    linarith
  apply (le_div_iff₀ hden).2
  change S r * (1 - q) ≤ 1
  rw [hform r]
  exact hnum

/-- The losses from successive hit conditioning are bounded by twice the
corresponding power of two when their total error is at most `log 2 / 12`. -/
theorem reciprocal_survival_product_le {r : ℕ} (e : Fin r → ℝ)
    (he0 : ∀ i, 0 ≤ e i) (he12 : ∀ i, e i ≤ 1 / 12)
    (hsum : (∑ i, e i) ≤ Real.log 2 / 12) :
    (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤ 2 * (2 : ℝ) ^ r := by
  have hfactor (i : Fin r) : (1 / 2 - 3 * e i)⁻¹ ≤ 2 * Real.exp (12 * e i) := by
    let x : ℝ := 6 * e i
    have hx0 : 0 ≤ x := by dsimp [x]; exact mul_nonneg (by norm_num) (he0 i)
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      nlinarith [he12 i]
    have hden : 0 < 1 - x := by linarith
    have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      apply (inv_le_iff_one_le_mul₀ hden).2
      nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)]
    have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
      have := Real.add_one_le_exp (2 * x)
      linarith
    have hrewrite : 1 / 2 - 3 * e i = (1 - x) / 2 := by
      dsimp [x]
      ring
    rw [hrewrite]
    have hInv : ((1 - x) / 2)⁻¹ = 2 * (1 - x)⁻¹ := by
      field_simp [hden.ne']
    rw [hInv]
    have htwox : 2 * x = 12 * e i := by dsimp [x]; ring
    rw [← htwox]
    exact mul_le_mul_of_nonneg_left (le_trans hinv hexp) (by norm_num)
  have hprod : (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤
      ∏ i : Fin r, (2 * Real.exp (12 * e i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have hi' := he12 i
      have hpos : 0 < 1 / 2 - 3 * e i := by nlinarith [hi']
      exact inv_nonneg.mpr hpos.le
    · intro i hi
      exact hfactor i
  have hprodEq : (∏ i : Fin r, (2 * Real.exp (12 * e i))) =
      (2 : ℝ) ^ r * Real.exp (12 * ∑ i, e i) := by
    rw [Finset.prod_mul_distrib]
    have hconst : (∏ i : Fin r, (2 : ℝ)) = (2 : ℝ) ^ r := by simp
    rw [hconst]
    congr 1
    have hExp : ∀ s : Finset (Fin r),
        (∏ i ∈ s, Real.exp (12 * e i)) = Real.exp (12 * ∑ i ∈ s, e i) := by
      intro s
      classical
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← Real.exp_add]
          congr 1
          ring
    simpa using hExp Finset.univ
  have hexpsum : Real.exp (12 * ∑ i, e i) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
    calc
      12 * ∑ i, e i ≤ 12 * (Real.log 2 / 12) := by nlinarith
      _ = Real.log 2 := by field_simp
  rw [hprodEq] at hprod
  have hpow : 0 ≤ (2 : ℝ) ^ r := pow_nonneg (by norm_num) _
  calc
    (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤ (2 : ℝ) ^ r * Real.exp (12 * ∑ i, e i) := hprod
    _ ≤ (2 : ℝ) ^ r * 2 := mul_le_mul_of_nonneg_left hexpsum hpow
    _ = 2 * (2 : ℝ) ^ r := by ring

private theorem smallErrors_survival_product_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (v : Pos T k) :
    (∏ j : Fin D.geom.r, (1 / 2 - 3 * D.error v j)⁻¹) ≤
      2 * (2 : ℝ) ^ D.geom.r := by
  have hsum := smallErrors_sum_control D hsmall v
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have he12 (j : Fin D.geom.r) : D.error v j ≤ 1 / 12 := by
    have hterm := Finset.single_le_sum
      (fun i hi => error_nonneg D v i) (Finset.mem_univ j)
    calc
      D.error v j ≤ ∑ i : Fin D.geom.r, D.error v i := hterm
      _ ≤ Real.log 2 / 1000 := hsum
      _ ≤ 1 / 12 := by nlinarith [hlog1]
  have hsum' : (∑ j : Fin D.geom.r, D.error v j) ≤ Real.log 2 / 12 := by
    calc
      (∑ j : Fin D.geom.r, D.error v j) ≤ Real.log 2 / 1000 := hsum
      _ ≤ Real.log 2 / 12 := by nlinarith [hlog0]
  exact reciprocal_survival_product_le (e := D.error v)
    (fun j => error_nonneg D v j) he12 hsum'

end HypercubeRamsey.Lane_q_s18_n1
