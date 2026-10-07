import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k
import HypercubeRamsey.Tools.HeavyTrunc

/-!
# q-s10-d7 finite posterior utilities

The even-row proof uses the generic heavy-coordinate truncation estimate for the
posterior law on candidate tuples.
-/

namespace HypercubeRamsey.Lane_q_s10_d7

open Classical
open Filter
open scoped BigOperators

private theorem eventually_power_gap {a b c : ℝ} (hab : a < b) (_hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    Filter.eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hnlarge, htend.eventually_gt_atTop c] with n hn hlarge
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnpos]; congr 1 <;> ring

theorem evenRow_scales_eventually (δ : ℝ) (hδ : 0 < δ)
    (hδsmall : δ < (1 : ℝ) / 2000) :
    ∀ᶠ n : ℕ in atTop,
      1000000000000000 ≤ n ∧
      200 * (n : ℝ) ^ δ < (n : ℝ) ^ (-δ) * n ∧
      200 * Real.log 2 < (n : ℝ) ^ (-δ) * n ∧
      200 < (n : ℝ) ^ (-δ) * (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) := by
  have hδhalf : δ < (1 : ℝ) / 2 := by linarith
  have hδgap : δ < 1 - δ := by linarith
  have hgap1 := eventually_power_gap hδgap (by norm_num : (0 : ℝ) < 200)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap2 := eventually_power_gap (by linarith : (0 : ℝ) < 1 - δ)
    (mul_pos (by norm_num : (0 : ℝ) < 200) hlog2)
  have hgap3 := eventually_power_gap (by positivity : (0 : ℝ) < 299 * δ)
    (by norm_num : (0 : ℝ) < 200)
  have hlarge : ∀ᶠ n : ℕ in atTop, 1000000000000000 ≤ n :=
    Filter.eventually_atTop.mpr ⟨1000000000000000,
      fun _ hn => hn⟩
  filter_upwards [hlarge, hgap1, hgap2, hgap3] with n hlarge hgap1 hgap2 hgap3
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have haId : (n : ℝ) ^ (-δ) * (n : ℝ) = (n : ℝ) ^ (1 - δ) := by
    calc
      (n : ℝ) ^ (-δ) * (n : ℝ) = (n : ℝ) ^ (-δ) * (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (-δ + 1) := by rw [← Real.rpow_add hnpos]
      _ = (n : ℝ) ^ (1 - δ) := by congr 1 <;> ring
  have hkLower : (n : ℝ) ^ (300 * δ) ≤
      (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) := by
    dsimp [HypercubeRamsey.S10.p10_1kTupleListLength]
    exact_mod_cast (Nat.le_ceil ((n : ℝ) ^ (300 * δ)))
  have hakLower : (n : ℝ) ^ (299 * δ) ≤
      (n : ℝ) ^ (-δ) *
        (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) := by
    have hpow : (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) =
        (n : ℝ) ^ (299 * δ) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    calc
      (n : ℝ) ^ (299 * δ) =
          (n : ℝ) ^ (-δ) * (n : ℝ) ^ (300 * δ) := hpow.symm
      _ ≤ (n : ℝ) ^ (-δ) *
          (HypercubeRamsey.S10.p10_1kTupleListLength n δ : ℝ) :=
        mul_le_mul_of_nonneg_left hkLower (Real.rpow_nonneg hnpos.le _)
  refine ⟨hlarge, ?_, ?_, ?_⟩
  · rw [haId]
    exact hgap1
  · rw [haId]
    simpa [Real.rpow_zero] using hgap2
  · exact lt_of_lt_of_le (by simpa [Real.rpow_zero] using hgap3) hakLower

theorem exp_quartic_lower {x : ℝ} (hx : 0 ≤ x) :
    x ^ 4 / 256 ≤ Real.exp x := by
  have hlin : 1 + x / 4 ≤ Real.exp (x / 4) := by
    have := Real.add_one_le_exp (x / 4)
    linarith
  have hpow₁ : (1 + x / 4) ^ 4 ≤ (Real.exp (x / 4)) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) hlin 4
  have hpow₂ : (x / 4) ^ 4 ≤ (1 + x / 4) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hexp : (Real.exp (x / 4)) ^ 4 = Real.exp x := by
    calc
      (Real.exp (x / 4)) ^ 4 = Real.exp (4 * (x / 4)) := by
        rw [← Real.exp_nat_mul]
        congr 1
      _ = Real.exp x := by congr 1 <;> ring
  calc
    x ^ 4 / 256 = (x / 4) ^ 4 := by ring
    _ ≤ (1 + x / 4) ^ 4 := hpow₂
    _ ≤ (Real.exp (x / 4)) ^ 4 := hpow₁
    _ = Real.exp x := hexp

theorem averageCoordinateMarginal_sum_one {N k : ℕ}
    (P : HypercubeRamsey.FinProb (Fin k → Fin N)) (hk : 0 < k) :
    ∑ x : Fin N, HypercubeRamsey.averageCoordinateMarginal P x = 1 := by
  classical
  have hcoord (i : Fin k) :
      ∑ x : Fin N, P.pr (fun ω => ω i = x) = 1 := by
    unfold HypercubeRamsey.FinProb.pr
    rw [Finset.sum_comm]
    have hrow (ω : Fin k → Fin N) :
        ∑ x : Fin N, @ite ℝ (ω i = x) (Classical.propDecidable _) (P.w ω) 0 = P.w ω := by
      rw [Finset.sum_eq_single (ω i)]
      · simp
      · intro x hx hne
        have hneq : ¬ ω i = x := fun he => hne he.symm
        simp [hneq]
      · intro hnot
        exact (hnot (Finset.mem_univ _)).elim
    calc
      ∑ ω : (Fin k → Fin N), ∑ x : Fin N,
          @ite ℝ (ω i = x) (Classical.propDecidable _) (P.w ω) 0 = ∑ ω, P.w ω := by
        apply Finset.sum_congr rfl
        intro ω hω
        exact hrow ω
      _ = 1 := P.sum_eq_one
  unfold HypercubeRamsey.averageCoordinateMarginal
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    (k : ℝ)⁻¹ * ∑ i : Fin k, ∑ x : Fin N, P.pr (fun ω => ω i = x) =
        (k : ℝ)⁻¹ * ∑ i : Fin k, 1 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact hcoord i
    _ = 1 := by simp [Nat.cast_ne_zero.mpr hk.ne']

theorem averageCoordinateMarginal_nonneg {N k : ℕ}
    (P : HypercubeRamsey.FinProb (Fin k → Fin N)) (x : Fin N) :
    0 ≤ HypercubeRamsey.averageCoordinateMarginal P x := by
  classical
  unfold HypercubeRamsey.averageCoordinateMarginal
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))
  apply Finset.sum_nonneg
  intro i hi
  unfold HypercubeRamsey.FinProb.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact P.nonneg ω
  · exact le_rfl

theorem finprob_expect_nonneg {α : Type*} [Fintype α]
    (P : HypercubeRamsey.FinProb α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f := by
  unfold HypercubeRamsey.FinProb.expect
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (P.nonneg x) (hf x)

end HypercubeRamsey.Lane_q_s10_d7
