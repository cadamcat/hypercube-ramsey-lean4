import HypercubeRamsey.S18.Incoming_sol_s18_n5
import HypercubeRamsey.S18.Locality_sol_s18_n5
import Mathlib.Analysis.SpecificLimits.Normed

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

theorem class_count_le (D : LateData hPT) : D.geom.r ≤ 2 * T.S.n k + 1 := by
  let v : Pos T k := fun _ => false
  have hv : IsEvenRole v := by simp [IsEvenRole, v]
  have hc := D.l16_valid.remaining_count v hv ⟨0, D.l16_valid.r_pos⟩
  have hn := Finset.card_le_card (Finset.filter_subset
    (fun a : Fin (T.S.n k) => ∃ s : Fin D.geom.r,
      0 ≤ s.val ∧ D.geom.classOf (flipPos v a) = some s) Finset.univ)
  simp only [Nat.sub_zero, Finset.card_univ, Fintype.card_fin] at hc hn
  omega

/-- Positive late pools make the floor lose at most a factor two. -/
theorem latePool_size_lower (D : LateData hPT) (j : Fin D.geom.r) :
    T.S.N k ≤ 6 * D.geom.r * (D.encoding.base.latePool j).card := by
  let M := (D.encoding.base.latePool j).card
  have hM : 1 ≤ M := D.late_pool_pos j
  have hfloor : T.S.N k / (3 * D.geom.r) = M := by
    rw [← Nat.div_div_eq_div_mul, ← D.encoding.base.latePool_card j]
  have hdiv : T.S.N k / (3 * D.geom.r) < M + 1 := by omega
  have hlt : T.S.N k < (M + 1) * (3 * D.geom.r) :=
    (Nat.div_lt_iff_lt_mul (by have := D.l16_valid.r_pos; omega)).mp hdiv
  have hb : M + 1 ≤ 2 * M := by omega
  have hmul := Nat.mul_le_mul_right (3 * D.geom.r) hb
  nlinarith

theorem class_pool_ratio_le (D : LateData hPT) (j : Fin D.geom.r)
    (hn : 1 ≤ T.S.n k) :
    ((D.encoding.base.classes j).card : ℝ) /
      (D.encoding.base.latePool j).card ≤ 18 / densityScale T k := by
  have hnR : 0 < (T.S.n k : ℝ) := by exact_mod_cast hn
  have hMR : 0 < ((D.encoding.base.latePool j).card : ℝ) := by
    exact_mod_cast D.late_pool_pos j
  have hNR : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hpow : 0 < (2 : ℝ) ^ T.S.n k := by positivity
  have hL : ((D.encoding.base.classes j).card : ℝ) * T.S.n k ≤ (2 : ℝ) ^ T.S.n k := by
    exact_mod_cast class_card_times_dimension D j
  have hM : (T.S.N k : ℝ) ≤ 6 * D.geom.r * (D.encoding.base.latePool j).card := by
    exact_mod_cast latePool_size_lower D j
  have hr : (D.geom.r : ℝ) ≤ 3 * T.S.n k := by
    exact_mod_cast (show D.geom.r ≤ 3 * T.S.n k from by
      have := class_count_le D; omega)
  have hscale : 0 < densityScale T k := div_pos hNR hpow
  apply (div_le_iff₀ hMR).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hscale).mpr
  dsimp [densityScale]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hpow).mpr
  have hLM := mul_le_mul_of_nonneg_left hM
    (Nat.cast_nonneg (D.encoding.base.classes j).card : (0 : ℝ) ≤ _)
  have hnr := mul_le_mul_of_nonneg_right hr
    (Nat.cast_nonneg (D.encoding.base.classes j).card : (0 : ℝ) ≤ _)
  have hL' : ((D.encoding.base.classes j).card : ℝ) * D.geom.r ≤
      3 * (2 : ℝ) ^ T.S.n k := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hL' hMR.le
  nlinarith

noncomputable def runError (T : Stage) (k : ℕ) : ℝ :=
  6 * (T.S.n k : ℝ) ^ 2 * (1 / 4 : ℝ) ^ T.S.n k

theorem runError_nonneg (T : Stage) (k : ℕ) : 0 ≤ runError T k := by
  unfold runError
  positivity

theorem runError_tendsto (T : Stage) : Tendsto (runError T) atTop (nhds 0) := by
  have h := (tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)).comp T.S.n_tendsto
  change Tendsto (fun k => 6 * (T.S.n k : ℝ) ^ 2 * (1 / 4 : ℝ) ^ T.S.n k) atTop (nhds 0)
  simpa only [Function.comp_def, mul_assoc, mul_zero] using h.const_mul 6

theorem fullRunProbability_mono (D : LateData hPT) {δ ε ε₁ ε₂ : ℝ}
    (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (h : FullRunProbability D C A ε₁) (he : ε₁ ≤ ε₂) :
    FullRunProbability D C A ε₂ := by
  unfold FullRunProbability at h ⊢
  linarith

/-- A constant-base reached column moment gives an explicit uniform run
error. The class-to-pool ratio uses only one_per_class and positive pools. -/
theorem fullRunProbability_of_column_moments (D : LateData hPT) (hD : D.Spec)
    {δ ε K27 K : ℝ} (C : TerminalCertificate D δ ε) (A : ClassSamplerData D δ)
    (hBroad : BroadDeletionFacts D K27) (hθ : 0 < κ.θ0) (hK : 0 ≤ K)
    (hn : 1 ≤ T.S.n k) (hscale : 576 * K / κ.θ0 ≤ densityScale T k)
    (hmoments : ∀ j y,
      (FinLaw.bind (D.encoding.terminalLaw (terminalSet D δ) C.positive)
        (fun x => D.encoding.base.runFull A.act (D.encoding.initialState x))).E
        (fun z => if reached D δ j z.2 then
          D.columnSum j (D.beforeHistory z.2 j.castSucc (Nat.le_of_lt j.isLt)) y ^ T.S.n k else 0) ≤
            (2 : ℝ) ^ D.geom.r *
              (K * (D.encoding.base.classes j).card / (D.encoding.base.latePool j).card) ^ T.S.n k) :
    FullRunProbability D C A (runError T k) := by
  let M : Fin D.geom.r → ℝ := fun j => (2 : ℝ) ^ D.geom.r *
    (K * (D.encoding.base.classes j).card / (D.encoding.base.latePool j).card) ^ T.S.n k
  have hfull := fullRunProbability_of_reached_moments D hD C A hBroad hθ (T.S.n k) M
    (reached_incoming D C A) hmoments
  apply fullRunProbability_mono D C A hfull
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hNR : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hpow : 0 < (2 : ℝ) ^ T.S.n k := by positivity
  have hscalePos : 0 < densityScale T k := div_pos hNR hpow
  have hbase : ∀ j,
      (K * (D.encoding.base.classes j).card / (D.encoding.base.latePool j).card) / κ.θ0 ≤ 1 / 32 := by
    intro j
    have hratio := mul_le_mul_of_nonneg_left (class_pool_ratio_le D j hn) hK
    have hscale' : 576 * K ≤ densityScale T k * κ.θ0 := (div_le_iff₀ hθ).mp hscale
    have hbound : K * (18 / densityScale T k) ≤ κ.θ0 / 32 := by
      have hstep : 576 * K / densityScale T k ≤ κ.θ0 :=
        (div_le_iff₀ hscalePos).mpr (by nlinarith)
      calc
        _ = (576 * K / densityScale T k) / 32 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hstep (by norm_num)
    apply (div_le_iff₀ hθ).mpr
    convert hratio.trans hbound using 1 <;> ring
  have hterm : ∀ j, M j / κ.θ0 ^ T.S.n k ≤ (2 : ℝ) ^ D.geom.r * (1 / 32 : ℝ) ^ T.S.n k := by
    intro j
    have hnn : 0 ≤ (K * (D.encoding.base.classes j).card /
        (D.encoding.base.latePool j).card) / κ.θ0 := by positivity
    have hp := pow_le_pow_left₀ hnn (hbase j) (T.S.n k)
    dsimp [M]
    rw [mul_div_assoc, ← div_pow]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hr : (D.geom.r : ℝ) ≤ 3 * T.S.n k := by
    exact_mod_cast (show D.geom.r ≤ 3 * T.S.n k from by
      have := class_count_le D; omega)
  have hrpow : (2 : ℝ) ^ D.geom.r ≤ 2 * (4 : ℝ) ^ T.S.n k := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * T.S.n k + 1) :=
        pow_le_pow_right₀ (by norm_num) (class_count_le D)
      _ = _ := by rw [pow_add, pow_mul]; norm_num; ring
  have hN : (T.S.N k : ℝ) ≤ T.S.n k * (2 : ℝ) ^ T.S.n k := by
    exact_mod_cast T.S.N_le k
  calc
    (T.S.N k : ℝ) * ∑ j, M j / κ.θ0 ^ T.S.n k ≤
        (T.S.N k : ℝ) * (D.geom.r * ((2 : ℝ) ^ D.geom.r * (1 / 32 : ℝ) ^ T.S.n k)) := by
      gcongr
      simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
    _ ≤ (T.S.n k * (2 : ℝ) ^ T.S.n k) *
        ((3 * T.S.n k) * ((2 * (4 : ℝ) ^ T.S.n k) * (1 / 32 : ℝ) ^ T.S.n k)) := by
      gcongr
    _ = runError T k := by
      unfold runError
      have hp : (2 : ℝ) ^ T.S.n k * (4 : ℝ) ^ T.S.n k * (1 / 32 : ℝ) ^ T.S.n k =
          (1 / 4 : ℝ) ^ T.S.n k := by
        rw [← mul_pow, ← mul_pow]
        norm_num
      calc
        _ = 6 * (T.S.n k : ℝ) ^ 2 *
          ((2 : ℝ) ^ T.S.n k * (4 : ℝ) ^ T.S.n k * (1 / 32 : ℝ) ^ T.S.n k) := by ring
        _ = _ := by rw [hp]

end HypercubeRamsey.S18.Lane_sol_s18_n5
