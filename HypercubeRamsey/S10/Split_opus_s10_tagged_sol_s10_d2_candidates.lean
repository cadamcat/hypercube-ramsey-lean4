import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_numeric

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

theorem envelope_card_polynomial {n m : ℕ} (hm : m ≤ n) (hn : 2 ≤ n)
    (q : P10_1kProjectedSite n m) : (p10_1kProjectedNeighborEnvelope q).card ≤ 9 * n ^ 3 := by
  have henv := p10_1kProjectedNeighborEnvelope_card_le q
  have hp : (n - m + 1) ^ 3 ≤ (2 * n) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hn3 : n ≤ n ^ 3 := by
    have hh := Nat.mul_le_mul_left n hn2
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh
  calc
    (p10_1kProjectedNeighborEnvelope q).card ≤ m + (n - m + 1) ^ 3 := henv
    _ ≤ n + (2 * n) ^ 3 := Nat.add_le_add hm hp
    _ ≤ 9 * n ^ 3 := by nlinarith

/-- The larger envelope candidate set has the polynomial bound needed for list enumeration. -/
theorem candidate_polynomial_bound {n m : ℕ} (δ : ℝ) (hm : m ≤ n) (hn : 2 ≤ n)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (q : P10_1kProjectedSite n m)
    (P : P10_1kProspectiveId n m δ → Bool)
    (hcounts : ∀ s ∈ p10_1kProjectedNeighborEnvelope q,
      ∀ j : Fin ((p10_1kHeightParams n m δ).H + 1),
      (p10_1kHeightPositionCount (p10_1kHeightParams n m δ)
        (fun loc => P (s.1, loc)) s.2 j : ℝ) ≤ 2 * (p10_1kHeightParams n m δ).lam) :
    ((p10_1kGroupPositionCandidates δ q P).card : ℝ) ≤ 36 * (n : ℝ) ^ 16 := by
  have hb := p10_1kGroupPositionCandidates_card_bound δ q P hcounts
  have he : ((p10_1kProjectedNeighborEnvelope q).card : ℝ) ≤ 9 * (n : ℝ) ^ 3 := by
    exact_mod_cast envelope_card_polynomial hm hn q
  have hH : ((p10_1kHeightParams n m δ).H : ℝ) ≤ (n : ℝ) ^ 3 := by
    exact_mod_cast height_scale_le_cube n δ hn hδ1 hδ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
  have hH' : (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 3 := by
    push_cast
    linarith
  calc
    ((p10_1kGroupPositionCandidates δ q P).card : ℝ) ≤
        (p10_1kProjectedNeighborEnvelope q).card *
          (((p10_1kHeightParams n m δ).H + 1 : ℕ) : ℝ) *
          (2 * (p10_1kHeightParams n m δ).lam) := hb
    _ ≤ (9 * (n : ℝ) ^ 3) * (2 * (n : ℝ) ^ 3) * (2 * (n : ℝ) ^ 10) := by
      change _ * _ * (2 * (n : ℝ) ^ 10) ≤ _
      gcongr
    _ = 36 * (n : ℝ) ^ 16 := by ring

end HypercubeRamsey.Lane_sol_s10_d2
