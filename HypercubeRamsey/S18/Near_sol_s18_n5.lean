import HypercubeRamsey.S18.Incidence_sol_s18_n5
import HypercubeRamsey.S18.Geometry_sol_s18_n5
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

noncomputable def consultationRows (D : LateData hPT) (b : Pos T k) := ancestors {b} (D.geom.r + 1)
noncomputable def consultationCells (D : LateData hPT) (b : Pos T k) :=
  D.expandCells (rowCells D (consultationRows D b))
noncomputable def consultationNear (D : LateData hPT) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) :=
  Finset.univ.filter fun b' : {b : Pos T k // b ∈ D.encoding.base.classes j} =>
    ¬ Disjoint (consultationRows D b.1) (consultationRows D b'.1) ∨
    ¬ Disjoint (consultationCells D b.1) (consultationCells D b'.1)

theorem consultationRows_self (D : LateData hPT) (b : Pos T k) : b ∈ consultationRows D b := by
  have h : ∀ m, b ∈ ancestors {b} m := by
    intro m
    induction m with
    | zero => exact Finset.mem_singleton_self _
    | succ m ih => exact Finset.mem_union.mpr (Or.inl ih)
  exact h _

theorem consultationNear_self (D : LateData hPT) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) : b ∈ consultationNear D j b := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, Or.inl ?_⟩
  exact Finset.not_disjoint_iff.mpr ⟨b.1, consultationRows_self D b.1, consultationRows_self D b.1⟩

theorem consultationNear_disjoint (D : LateData hPT) (j : Fin D.geom.r)
    (b b' : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : b' ∉ consultationNear D j b) :
    Disjoint (consultationRows D b.1) (consultationRows D b'.1) ∧
    Disjoint (consultationCells D b.1) (consultationCells D b'.1) := by
  simpa only [consultationNear, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or, not_not] using h

private theorem elementary_growth {n a t : ℕ} (hn : 2 ≤ n) :
    1 + (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1) ≤
      n ^ ((a + 5) * (2 * t + 4) + 3) := by
  have hp : 0 < n ^ (a + 4) := pow_pos (by omega) _
  have hd : n ^ (a + 4) + 1 ≤ n ^ (a + 5) := by
    calc
      _ ≤ n ^ (a + 4) * n := by nlinarith
      _ = _ := (pow_succ n (a + 4)).symm
  have hnplus : n + 1 ≤ n ^ 2 := by nlinarith
  let z := (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1)
  have hz : 1 ≤ z := by
    dsimp [z]
    have hp := pow_pos (by omega : 0 < n ^ (a + 4) + 1) (2 * t + 4)
    nlinarith
  calc
    1 + z ≤ n * z := by nlinarith
    _ ≤ n * ((n ^ (a + 5)) ^ (2 * t + 4) * n ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hnplus)
    _ = _ := by rw [← pow_mul]; ring

theorem consultation_scope_power (D : LateData hPT) (hD : D.Spec) (hn : 2 ≤ T.S.n k)
    (hr : D.geom.r ≤ D.encoding.Ts) :
    let p := 100 * (κ.Ac + 6) * (D.encoding.Ts + 1)
    (∀ b, (consultationRows D b).card ≤ T.S.n k ^ p) ∧
    (∀ b, (inverseScope (consultationRows D) b).card ≤ T.S.n k ^ p) ∧
    (∀ b, (consultationCells D b).card ≤ T.S.n k ^ p) ∧
    (∀ C, (inverseScope (consultationCells D) C).card ≤ T.S.n k ^ p) := by
  intro p
  let m := D.geom.r + 1
  let g := (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3
  have hd : 1 + T.S.n k ^ 2 ≤ T.S.n k ^ 3 := by nlinarith
  have hm : m ≤ D.encoding.Ts + 1 := by dsimp [m]; omega
  have hbudget : g + (κ.Ac + 3) + 3 * m + 4 ≤ p := by
    dsimp [g, p]
    nlinarith
  have hanc : ∀ b : Pos T k, (ancestors {b} m).card ≤ T.S.n k ^ (3 * m) := by
    intro b
    calc
      _ ≤ (1 + T.S.n k ^ 2) ^ m := by simpa only [Finset.card_singleton, one_mul] using ancestors_card {b} m
      _ ≤ (T.S.n k ^ 3) ^ m := Nat.pow_le_pow_left hd _
      _ = _ := (pow_mul _ _ _).symm
  have hpow : ∀ q, q ≤ p → T.S.n k ^ q ≤ T.S.n k ^ p :=
    fun q hq => Nat.pow_le_pow_right (by omega) hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    exact (hanc b).trans (hpow _ (by omega))
  · intro b
    apply (ancestors_incidence m b).trans
    apply le_trans (Nat.pow_le_pow_left hd _)
    rw [← pow_mul]
    exact hpow _ (by omega)
  · intro b
    have hseed : (rowCells D (ancestors {b} m)).card ≤ T.S.n k ^ (3 * m + 3) := by
      have hnp : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
      calc
        _ ≤ (ancestors {b} m).card * (T.S.n k * (T.S.n k + 1)) := rowCells_card D _
        _ ≤ T.S.n k ^ (3 * m) * (T.S.n k * T.S.n k ^ 2) :=
          Nat.mul_le_mul (hanc b) (Nat.mul_le_mul_left _ hnp)
        _ = _ := by ring
    calc
      _ ≤ (rowCells D (ancestors {b} m)).card *
          (1 + (T.S.n k ^ (κ.Ac + 4) + 1) ^ (2 * D.encoding.Ts + 4) * (T.S.n k + 1)) :=
        HypercubeRamsey.Lane_sol_s18_3f.expandCells_card D hD hn _
      _ ≤ T.S.n k ^ (3 * m + 3) * T.S.n k ^ g :=
        Nat.mul_le_mul hseed (elementary_growth hn)
      _ = T.S.n k ^ (3 * m + 3 + g) := (pow_add _ _ _).symm
      _ ≤ _ := hpow _ (by omega)
  · intro C
    exact (horizon_incidence_power D hD hn m C).trans (hpow _ (by dsimp [g] at hbudget; omega))

theorem consultationNear_card_power (D : LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (hr : D.geom.r ≤ D.encoding.Ts) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) :
    (consultationNear D j b).card ≤
      2 * (T.S.n k ^ (100 * (κ.Ac + 6) * (D.encoding.Ts + 1))) ^ 2 := by
  let M := T.S.n k ^ (100 * (κ.Ac + 6) * (D.encoding.Ts + 1))
  obtain ⟨hrows, hrowinc, hcells, hcellinc⟩ := consultation_scope_power D hD hn hr
  let R := Finset.univ.filter fun b' : Pos T k =>
    ¬ Disjoint (consultationRows D b.1) (consultationRows D b')
  let C := Finset.univ.filter fun b' : Pos T k =>
    ¬ Disjoint (consultationCells D b.1) (consultationCells D b')
  have hsub : (consultationNear D j b).image Subtype.val ⊆ R ∪ C := by
    intro b' hb'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb'
    rcases (Finset.mem_filter.mp hc).2 with hr | hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
  have hR : R.card ≤ M * M := overlap_card _ M M hrows hrowinc b.1
  have hC : C.card ≤ M * M := overlap_card _ M M hcells hcellinc b.1
  calc
    _ = ((consultationNear D j b).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (R ∪ C).card := Finset.card_le_card hsub
    _ ≤ R.card + C.card := Finset.card_union_le _ _
    _ ≤ M * M + M * M := Nat.add_le_add hR hC
    _ = _ := by dsimp [M]; ring

theorem consultationNear_card_eventually (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), D.Spec → ∀ j : Fin D.geom.r,
      ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j},
      ((consultationNear D j b).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 5) := by
  let a := 100 * (κ.Ac + 6)
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  filter_upwards [HypercubeRamsey.Lane_sol_s18_n4.terminalScaleEventually κ T,
    (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop (max 3 (3 * (a : ℝ)))] with k hs hl
  intro PT hPT D hD j b
  obtain ⟨hn, _, hr⟩ := hs D
  have hrN : D.geom.r ≤ D.encoding.Ts := by exact_mod_cast hr
  let y := Real.log (T.S.n k : ℝ)
  have hy : 3 ≤ y := (le_max_left _ _).trans hl
  have hya : 3 * (a : ℝ) ≤ y := (le_max_right _ _).trans hl
  have hTs : (D.encoding.Ts : ℝ) ≤ y ^ 2 + 1 := by
    rw [D.encoding.Ts_eq]
    exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
  have hp : ((a * (D.encoding.Ts + 1) : ℕ) : ℝ) ≤ y ^ 3 := by
    push_cast
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hTs ha
    have hlim := mul_le_mul_of_nonneg_right hya (sq_nonneg y)
    nlinarith
  have hM : (T.S.n k : ℝ) ^ (a * (D.encoding.Ts + 1)) ≤ Real.exp (y ^ 4) := by
    have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
    rw [← Real.exp_log hnpos, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ y)
    nlinarith
  have h2 : (2 : ℝ) ≤ Real.exp (y ^ 4) := by
    have h := Real.add_one_le_exp (y ^ 4)
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hy 4
    norm_num at hp
    linarith
  have h5 : 3 * y ^ 4 ≤ y ^ 5 := by
    have h := mul_le_mul_of_nonneg_right hy (pow_nonneg (by linarith : 0 ≤ y) 4)
    nlinarith
  have hc : ((consultationNear D j b).card : ℝ) ≤
      2 * ((T.S.n k : ℝ) ^ (a * (D.encoding.Ts + 1))) ^ 2 := by
    exact_mod_cast consultationNear_card_power D hD (by omega) hrN j b
  calc
    _ ≤ 2 * ((T.S.n k : ℝ) ^ (a * (D.encoding.Ts + 1))) ^ 2 := hc
    _ ≤ 2 * Real.exp (y ^ 4) ^ 2 := by gcongr
    _ ≤ Real.exp (y ^ 4) * Real.exp (y ^ 4) ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = Real.exp (y ^ 4) ^ 3 := by ring
    _ = Real.exp (3 * y ^ 4) := (Real.exp_nat_mul _ 3).symm
    _ ≤ _ := Real.exp_le_exp.mpr h5

noncomputable def nearFraction (D : LateData hPT) (j : Fin D.geom.r) : ℝ :=
  Real.exp (Real.log (T.S.n k) ^ 5) / (D.encoding.base.classes j).card

/-- The exponentially large physical class absorbs all consultation
incidences and the deterministic row cap. -/
theorem nearFraction_small_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : LateData hPT), ∀ j : Fin D.geom.r,
      (T.S.n k : ℝ) * nearFraction D j *
        (2 * Real.exp ((κ.α / 100) * (T.S.n k : ℝ))) ≤ 1 := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hlogpos : 0 < Real.log 2 := by linarith
  have hg : κ.α / 100 ≤ Real.log 2 / 4 := by linarith [hκ.α_rng.2]
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  have hpoly := (Real.isLittleO_pow_log_id_atTop (n := 5)).bound
    (by positivity : 0 < Real.log 2 / 4)
  have hdecay : Tendsto (fun k => 16 * (T.S.n k : ℝ) ^ 2 *
      Real.exp (-(Real.log 2 / 2) * (T.S.n k : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (Real.log 2 / 2)
      (by positivity)).comp hnR
    simpa only [Function.comp_apply, Real.rpow_eq_pow, Real.rpow_two, mul_assoc, mul_zero] using h.const_mul 16
  filter_upwards [hnR.eventually hpoly, (tendsto_order.1 hdecay).2 1 (by norm_num),
    T.S.n_tendsto.eventually_ge_atTop 6,
    (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop 0] with k hp hd hn hl
  intro PT hPT D j
  have hn0 : 0 ≤ (T.S.n k : ℝ) := Nat.cast_nonneg _
  have hL : 0 < ((D.encoding.base.classes j).card : ℝ) := Nat.cast_pos.mpr (class_card_pos D hn j)
  have hc : (2 : ℝ) ^ T.S.n k ≤ 8 * (T.S.n k : ℝ) * (D.encoding.base.classes j).card := by
    exact_mod_cast cube_size_le_class_card D hn j
  have hp' : Real.log (T.S.n k : ℝ) ^ 5 ≤ (Real.log 2 / 4) * (T.S.n k : ℝ) := by
    have hpabs : |Real.log (T.S.n k : ℝ) ^ 5| ≤ (Real.log 2 / 4) * (T.S.n k : ℝ) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hn0, id_eq] using hp
    exact (le_abs_self _).trans hpabs
  have hexp : Real.exp (Real.log (T.S.n k : ℝ) ^ 5 + (κ.α / 100) * (T.S.n k : ℝ)) /
      (2 : ℝ) ^ T.S.n k ≤ Real.exp (-(Real.log 2 / 2) * (T.S.n k : ℝ)) := by
    rw [show (2 : ℝ) ^ T.S.n k = Real.exp ((T.S.n k : ℝ) * Real.log 2) by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)], ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hg hn0
    linarith
  calc
    _ = 2 * (T.S.n k : ℝ) *
        Real.exp (Real.log (T.S.n k : ℝ) ^ 5 + (κ.α / 100) * (T.S.n k : ℝ)) /
        (D.encoding.base.classes j).card := by dsimp [nearFraction]; rw [Real.exp_add]; ring
    _ ≤ 16 * (T.S.n k : ℝ) ^ 2 *
        (Real.exp (Real.log (T.S.n k : ℝ) ^ 5 + (κ.α / 100) * (T.S.n k : ℝ)) /
          (2 : ℝ) ^ T.S.n k) := by
      apply (div_le_iff₀ hL).mpr
      have hm := mul_le_mul_of_nonneg_left hc
        (by positivity : 0 ≤ 2 * (T.S.n k : ℝ) *
          Real.exp (Real.log (T.S.n k : ℝ) ^ 5 + (κ.α / 100) * (T.S.n k : ℝ)))
      rw [show 16 * (T.S.n k : ℝ) ^ 2 *
          (Real.exp (Real.log (T.S.n k : ℝ) ^ 5 + (κ.α / 100) * (T.S.n k : ℝ)) /
            (2 : ℝ) ^ T.S.n k) * (D.encoding.base.classes j).card =
          (16 * (T.S.n k : ℝ) ^ 2 *
            Real.exp (Real.log (T.S.n k : ℝ) ^ 5 + (κ.α / 100) * (T.S.n k : ℝ)) *
            (D.encoding.base.classes j).card) / (2 : ℝ) ^ T.S.n k by ring]
      apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ T.S.n k)).mpr
      nlinarith
    _ ≤ 16 * (T.S.n k : ℝ) ^ 2 * Real.exp (-(Real.log 2 / 2) * (T.S.n k : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 1 := hd.le

end HypercubeRamsey.S18.Lane_sol_s18_n5
