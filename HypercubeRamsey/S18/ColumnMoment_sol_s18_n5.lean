import HypercubeRamsey.S18.Near_sol_s18_n5
import HypercubeRamsey.S18.SeparatedProducts_sol_s18_n5
import HypercubeRamsey.S03.ScatteredMoments

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- Scattered moments use the reached subprobability measure, normalized
by the single backward/terminal/pool comparison cost. -/
theorem actual_column_moment (D : LateData hPT) (hT : TransitionData D)
    {δ ε : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (hn : 6 ≤ T.S.n k) (j : Fin D.geom.r) (y : Fin (T.S.N k))
    (hnear : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      ((consultationNear D j b).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 5))
    (hsmall : (T.S.n k : ℝ) * nearFraction D j *
      (2 * Real.exp ((κ.α / 100) * (T.S.n k : ℝ))) ≤ 1)
    (hjoint : ∀ m ≤ T.S.n k,
      ∀ s : Fin m → {b : Pos T k // b ∈ D.encoding.base.classes j},
      (∀ i i' : Fin m, i' < i → s i ∉ consultationNear D j (s i')) →
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
        (fun z => if reached D δ j z.2 then rowMassProduct D j m s y
          (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) else 0) ≤
      4 * (2 : ℝ) ^ D.geom.r * (2 / ((D.encoding.base.latePool j).card : ℝ)) ^ m) :
    (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
      (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
      (fun z => if reached D δ j z.2 then
        D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ^ T.S.n k else 0) ≤
    (2 : ℝ) ^ D.geom.r *
      (12 * (D.encoding.base.classes j).card / (D.encoding.base.latePool j).card) ^ T.S.n k := by
  classical
  let U := {b : Pos T k // b ∈ D.encoding.base.classes j}
  let P := FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
    (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))
  let L : ℝ := (D.encoding.base.classes j).card
  let M : ℝ := (D.encoding.base.latePool j).card
  let c : ℝ := 4 * (2 : ℝ) ^ D.geom.r
  let q := fun b : U => fun z : D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r) =>
    (D.encoding.kernels.refK j b (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt))).pr
      (fun out => D.encoding.base.rowLabel out = y)
  let succ := Finset.univ.filter fun z : D.encoding.InitInput × D.encoding.base.History (Fin.last D.geom.r) =>
    reached D δ j z.2
  let cap : ℝ := 2 / M * Real.exp ((κ.α / 100) * (T.S.n k : ℝ))
  let w := fun z => P.w z / c
  let d := fun _b : U => 2 / M
  have hL : 0 < L := Nat.cast_pos.mpr (class_card_pos D hn j)
  have hM : 0 < M := Nat.cast_pos.mpr (D.late_pool_pos j)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcard : (Fintype.card U : ℝ) = L := by
    dsimp [U, L]
    rw [Fintype.card_coe]
  have hnonempty := Finset.card_pos.mp (class_card_pos D hn j)
  letI : Nonempty U := ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
  have hq : ∀ b z, 0 ≤ q b z := fun b z => HypercubeRamsey.Lane_q_s17_res1.finLaw_pr_nonneg _ _
  have hcap : ∀ b z, z ∈ succ → q b z ≤ cap := by
    intro b z _
    exact referenceRow_label_cap D hT j b _ y
  have hnear' : ∀ b : U, ((consultationNear D j b).card : ℝ) ≤ nearFraction D j * Fintype.card U := by
    intro b
    have he : nearFraction D j * Fintype.card U = Real.exp (Real.log (T.S.n k) ^ 5) := by
      dsimp [nearFraction, U]
      rw [Fintype.card_coe, div_mul_cancel₀ _ hL.ne']
    rw [he]
    exact hnear b
  have hjoint' : ∀ m ≤ T.S.n k, ∀ s : Fin m → U,
      (∀ i i', i' < i → s i ∉ consultationNear D j (s i')) →
      (∑ z ∈ succ, w z * ∏ i, q (s i) z) ≤ (1 : ℝ) ^ m * ∏ i, d (s i) := by
    intro m hm s hsep
    have he : (∑ z ∈ succ, w z * ∏ i, q (s i) z) =
        P.E (fun z => if reached D δ j z.2 then rowMassProduct D j m s y
          (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) else 0) / c := by
      rw [Finset.sum_filter]
      unfold FinLaw.E
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : reached D δ j z.2 <;> simp only [hz, if_true, if_false, mul_zero, zero_div]
      dsimp [w, q, rowMassProduct]
      ring
    rw [he]
    have hb := div_le_div_of_nonneg_right (hjoint m hm s hsep) hc.le
    have he' : (c * (2 / M) ^ m) / c = (2 / M) ^ m := mul_div_cancel_left₀ _ hc.ne'
    change _ ≤ (c * (2 / M) ^ m) / c at hb
    rw [he'] at hb
    simpa only [one_pow, one_mul, d, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hb
  have hmom := scattered_moments w (fun z => div_nonneg (P.nonneg z) hc.le) succ q hq cap
    (by dsimp [cap]; positivity) hcap (consultationNear D j) (consultationNear_self D j)
    (nearFraction D j) hnear' (T.S.n k) 1 le_rfl d (fun _ => by dsimp [d]; positivity) hjoint'
  let avg := fun z => (Fintype.card U : ℝ)⁻¹ * ∑ b : U, q b z
  have hmean : (Fintype.card U : ℝ)⁻¹ * ∑ b : U, d b = 2 / M := by
    simp only [d, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    rw [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  have hsmall' : (T.S.n k : ℝ) * nearFraction D j * cap ≤ 1 / M := by
    have hh := mul_le_mul_of_nonneg_right hsmall (inv_nonneg.mpr hM.le)
    calc
      _ = ((T.S.n k : ℝ) * nearFraction D j *
          (2 * Real.exp ((κ.α / 100) * (T.S.n k : ℝ)))) * M⁻¹ := by dsimp [cap]; ring
      _ ≤ 1 * M⁻¹ := hh
      _ = _ := by ring
  have hbase0 : 0 ≤ 2 / M + (T.S.n k : ℝ) * nearFraction D j * cap := by
    dsimp [nearFraction, cap, M]
    positivity
  have hmoment : (∑ z ∈ succ, w z * avg z ^ T.S.n k) ≤ (3 / M) ^ T.S.n k := by
    simp only [one_pow, one_mul, hmean] at hmom
    have hbound : 2 / M + (T.S.n k : ℝ) * nearFraction D j * cap ≤ 3 / M := by
      calc
        _ ≤ 2 / M + 1 / M := by linarith [hsmall']
        _ = _ := by ring
    exact hmom.trans (pow_le_pow_left₀ hbase0 hbound _)
  have havg : ∀ z, avg z = L⁻¹ *
      D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y := by
    intro z
    simp only [avg, hcard]
    rfl
  have hscale : P.E (fun z => if reached D δ j z.2 then
      D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ^ T.S.n k else 0) =
      c * L ^ T.S.n k * (∑ z ∈ succ, w z * avg z ^ T.S.n k) := by
    unfold FinLaw.E
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : reached D δ j z.2
    · simp only [hz, if_true, havg, w, mul_pow, inv_pow]
      field_simp [hc.ne', hL.ne']
    · simp [hz]
  rw [hscale]
  calc
    _ ≤ c * L ^ T.S.n k * (3 / M) ^ T.S.n k :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = 4 * (2 : ℝ) ^ D.geom.r * (3 * L / M) ^ T.S.n k := by
      dsimp [c]
      rw [show 3 * L / M = L * (3 / M) by ring, mul_pow]
      ring
    _ ≤ (2 : ℝ) ^ D.geom.r * (12 * L / M) ^ T.S.n k := by
      have h4 : (4 : ℝ) ≤ 4 ^ T.S.n k := by
        exact_mod_cast Nat.le_self_pow (by omega : T.S.n k ≠ 0) 4
      rw [show 12 * L / M = 4 * (3 * L / M) by ring, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_right h4
        (by positivity : 0 ≤ (2 : ℝ) ^ D.geom.r * (3 * L / M) ^ T.S.n k)]

theorem actual_column_moment_eventually (hκ : κ.Admissible) (T : Stage)
    (εterm : ℕ → ℝ) (hterm : Tendsto εterm atTop (nhds 0)) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), D.Spec → TransitionData D → MaskBalance D → ∀ δ : ℝ,
      ∀ C : TerminalCertificate D δ (εterm k), ∀ A : ClassSamplerData D δ,
      ∀ j : Fin D.geom.r, ∀ y : Fin (T.S.N k),
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
        (fun z => if reached D δ j z.2 then
          D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ^ T.S.n k else 0) ≤
      (2 : ℝ) ^ D.geom.r *
        (12 * (D.encoding.base.classes j).card / (D.encoding.base.latePool j).card) ^ T.S.n k := by
  filter_upwards [reached_column_baseline_eventually hκ T, consultationNear_card_eventually κ T,
    nearFraction_small_eventually hκ T, (tendsto_order.1 hterm).2 1 (by norm_num),
    T.S.n_tendsto.eventually_ge_atTop 6] with k hcomp hnear hsmall he hn
  intro PT hPT D hD hT hBalance δ C A j y
  apply actual_column_moment D hT C A hn j y (hnear D hD j) (hsmall D j)
  intro m hm s hsep
  have hdisj : ∀ i i', i ≠ i' → Disjoint (consultationRows D (s i).1) (consultationRows D (s i').1) ∧
      Disjoint (consultationCells D (s i).1) (consultationCells D (s i').1) := by
    intro i i' hii'
    rcases lt_or_gt_of_ne hii' with hi | hi
    · exact consultationNear_disjoint D j (s i) (s i') (hsep i' i hi)
    · have hh := consultationNear_disjoint D j (s i') (s i) (hsep i i' hi)
      exact ⟨hh.1.symm, hh.2.symm⟩
  have hbase := baseline_row_product_le D hD hT hBalance j m s y
    (fun i i' hii' => (hdisj i i' hii').1) (fun i i' hii' => (hdisj i i' hii').2)
  exact (hcomp D hD hT δ (εterm k) he.le C A j m hm s y).trans
    (mul_le_mul_of_nonneg_left hbase (by positivity))

end HypercubeRamsey.S18.Lane_sol_s18_n5
