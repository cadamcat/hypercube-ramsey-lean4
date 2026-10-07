import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.Framework.LawLemmas

namespace HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer

open Filter

theorem eventually_pow_gap (a b c : ℝ) (hab : a < b) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ a < (n : ℝ) ^ b := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  filter_upwards [hnlarge, htend.eventually_gt_atTop c] with n hn hlarge
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  calc
    c * (n : ℝ) ^ a < (n : ℝ) ^ (b - a) * (n : ℝ) ^ a :=
      mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnpos]; congr 1 <;> ring

theorem innerCoord_card_le (n : ℕ) : Fintype.card (InnerCoord n) ≤ hIn n := by
  simpa using Fintype.card_le_of_injective
    (fun j : InnerCoord n => (⟨j.1.val, j.2⟩ : Fin (hIn n)))
    (by
      intro j j' hj
      have hv : j.1.val = j'.1.val := congrArg (fun z : Fin (hIn n) => z.val) hj
      exact Subtype.ext (Fin.ext hv))

theorem hIn_real_le_pow (n : ℕ) :
    (hIn n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
  unfold hIn
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
