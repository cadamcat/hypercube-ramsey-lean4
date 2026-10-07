import Mathlib
import HypercubeRamsey.Tools.Binomial

/-!
Shared Section 6 tool interfaces not yet present in this worktree.  These are
requests for the shared tools lane; the Section 6 geometry node currently
records the resulting bounds directly.
-/

namespace HypercubeRamsey.S06.Needs

open scoped BigOperators

/-- SHARED: X-Bins (L6.1b). Consecutive bins for `Bin(ell, 1/2)` with small mass. -/
theorem shared_consecutive_bin_map6 (ell n : ℕ) (hn : 0 < n)
    (hEll : ell = Nat.floor ((n : ℝ) ^ (1 / 5 : ℝ))) :
    ∃ bin : ℕ → Fin (ell + 1),
      (∀ a b, a ≤ b → (bin a).val ≤ (bin b).val) ∧
      (∀ a b c, a ≤ b → b ≤ c → bin a = bin c → bin a = bin b) ∧
      (∀ j, (∑ q ∈ Finset.range (ell + 1),
        if bin q = j then (Nat.choose ell q : ℝ) else 0) ≤
          2 * (n : ℝ) ^ (-0.04 : ℝ) * (2 : ℝ) ^ ell) := by
  classical
  let bin : ℕ → Fin (ell + 1) := fun q =>
    ⟨min q ell, Nat.lt_succ_of_le (Nat.min_le_right q ell)⟩
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hellPos : 0 < ell := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hn1
        (by norm_num : 0 ≤ (1 / 5 : ℝ))
      simpa using h
    have hfloor : 1 ≤ Nat.floor ((n : ℝ) ^ (1 / 5 : ℝ)) :=
      (Nat.le_floor_iff (by positivity)).2 (by exact_mod_cast hx)
    omega
  have hmono : ∀ a b, a ≤ b → (bin a).val ≤ (bin b).val := by
    intro a b hab
    exact min_le_min hab le_rfl
  have hinterval : ∀ a b c, a ≤ b → b ≤ c → bin a = bin c → bin a = bin b := by
    intro a b c hab hbc hac
    have h₁ := hmono a b hab
    have h₂ := hmono b c hbc
    have heq : (bin a).val = (bin c).val := congrArg Fin.val hac
    apply Fin.ext
    omega
  have hj : ∀ j : Fin (ell + 1), j.val ≤ ell := by
    intro j
    omega
  have hsum : ∀ j : Fin (ell + 1),
      (∑ q ∈ Finset.range (ell + 1),
        if bin q = j then (Nat.choose ell q : ℝ) else 0) =
        (Nat.choose ell j.val : ℝ) := by
    intro j
    have hjmem : j.val ∈ Finset.range (ell + 1) := Finset.mem_range.mpr (by omega)
    have hbinj : bin j.val = j := by
      apply Fin.ext
      simp [bin, Nat.min_eq_left (hj j)]
    rw [Finset.sum_eq_single j.val]
    · simp [hbinj]
    · intro q hq hqne
      have hqle : q ≤ ell := by
        have := Finset.mem_range.mp hq
        omega
      have hneq : bin q ≠ j := by
        intro h
        apply hqne
        have hv : q = j.val := by
          have hv := congrArg Fin.val h
          simpa [bin, Nat.min_eq_left hqle] using hv
        exact hv
      simp [hneq]
    · intro hnot
      exact False.elim (hnot hjmem)
  refine ⟨bin, ?_, ?_, ?_⟩
  · exact hmono
  · exact hinterval
  · intro j
    rw [hsum j]
    by_cases ht : (n : ℝ) ^ (1 / 25 : ℝ) ≤ 2
    · have hchoose : (Nat.choose ell j.val : ℝ) ≤ (2 : ℝ) ^ ell := by
        exact_mod_cast Nat.choose_le_two_pow ell j.val
      have hfactor : 1 ≤ 2 * (n : ℝ) ^ (-0.04 : ℝ) := by
        have hneg : (n : ℝ) ^ (-0.04 : ℝ) =
            ((n : ℝ) ^ (1 / 25 : ℝ))⁻¹ := by
          rw [show (-0.04 : ℝ) = -(1 / 25 : ℝ) by norm_num, Real.rpow_neg hnR.le]
        rw [hneg, ← div_eq_mul_inv]
        exact (le_div_iff₀ (Real.rpow_pos_of_pos hnR _)).2 (by nlinarith)
      calc
        (Nat.choose ell j.val : ℝ) ≤ (2 : ℝ) ^ ell := hchoose
        _ ≤ (2 * (n : ℝ) ^ (-0.04 : ℝ)) * (2 : ℝ) ^ ell :=
          by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right hfactor
                (by positivity : 0 ≤ (2 : ℝ) ^ ell))
    · have hneg : (n : ℝ) ^ (-0.04 : ℝ) =
        ((n : ℝ) ^ (1 / 25 : ℝ))⁻¹ := by
        rw [show (-0.04 : ℝ) = -(1 / 25 : ℝ) by norm_num, Real.rpow_neg hnR.le]
      have hsqrt : 2 / Real.sqrt ell ≤ 2 * (n : ℝ) ^ (-0.04 : ℝ) := by
        let t : ℝ := (n : ℝ) ^ (1 / 25 : ℝ)
        let x : ℝ := (n : ℝ) ^ (1 / 5 : ℝ)
        have hx : x = t ^ 5 := by
          dsimp [x, t]
          rw [show (1 / 5 : ℝ) = (1 / 25 : ℝ) * (5 : ℕ) by norm_num,
            Real.rpow_mul_natCast hnR.le (1 / 25 : ℝ) 5]
        have ht : 2 < t := lt_of_not_ge ht
        have ht5 : (2 : ℝ) ^ 5 ≤ t ^ 5 := by gcongr
        have hx2 : 2 ≤ x := by
          rw [hx]
          exact le_trans (by norm_num) ht5
        have hfloor : x < (ell : ℝ) + 1 := by
          simpa [x, hEll] using (Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 5 : ℝ)))
        have hfloorLower : x / 2 ≤ (ell : ℝ) := by nlinarith
        have ht3 : (2 : ℝ) ≤ t ^ 3 := by
          have hpow : (2 : ℝ) ^ 3 ≤ t ^ 3 := by gcongr
          exact (by norm_num : (2 : ℝ) ≤ 2 ^ 3).trans hpow
        have hprod : 0 ≤ t ^ 2 * (t ^ 3 - 2) :=
          mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht3)
        have hquad : t ^ 2 ≤ x / 2 := by
          rw [hx]
          nlinarith [hprod]
        have hsqrt : t ≤ Real.sqrt ell := Real.le_sqrt_of_sq_le (hquad.trans hfloorLower)
        have hinv : (Real.sqrt ell)⁻¹ ≤ t⁻¹ :=
          (inv_le_inv₀ (Real.sqrt_pos.2 (by exact_mod_cast hellPos))
            (Real.rpow_pos_of_pos hnR _)).2 hsqrt
        calc
          2 / Real.sqrt ell = 2 * (Real.sqrt ell)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ 2 * t⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
          _ = 2 * (n : ℝ) ^ (-0.04 : ℝ) := by rw [hneg]
      have hnorm := (centralBinomialUpper ell hellPos j.val (hj j)).trans hsqrt
      exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ ell)).1 hnorm

def nearMidCount6 (ell q : ℕ) : Bool := decide (Nat.dist (2 * q) ell ≤ 11)

/--
SHARED: X-BinomTail (L6.1b).  Joint near-mid tail for `m` independent odd
chunks, with the `5.5` cutoff and Section 6's `J=floor(m^.04)` regime.
-/
theorem shared_fine_severity_tail6 (n m ell : ℕ) (hn : 0 < n)
    (hellOdd : Odd ell)
    (hellLower : (n : ℝ) ^ (3 / 10 : ℝ) ≤ ell)
    (hellUpper : (ell : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 10 : ℝ))
    (hm : (m : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ)) :
    ∀ q, 1 ≤ q → q ≤ m →
      (∑ s : (Fin m → Fin (ell + 1)),
        if q ≤ (Finset.univ.filter fun i => nearMidCount6 ell (s i).val = true).card then
          ∏ i, (Nat.choose ell (s i) : ℝ) / (2 : ℝ) ^ ell else 0) ≤
        (2 : ℝ) ^ m * (n : ℝ) ^ (-(0.13 : ℝ) * q) := by
  sorry

end HypercubeRamsey.S06.Needs
