import HypercubeRamsey.S10.Transfer_sol_s10_1k

namespace HypercubeRamsey.Lane_q_s10_b

open OAI.HypercubeRamsey
open scoped BigOperators

/-- Scattered moments bound a retained odd-column failure after normalizing
the column sum by the number of labels. -/
theorem scattered_scaled_column_tail
    {Ω U Y : Type*} [Fintype Ω] [Fintype U] [DecidableEq U] [Nonempty U]
    (P : FinProb Ω) (good : Finset Ω) (row : U → Y → Ω → ℝ)
    (hrow_nonneg : ∀ u y ω, 0 ≤ row u y ω)
    (N : ℕ) (hN : 0 < N) (L : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ u y ω, ω ∈ good → (N : ℝ) * row u y ω ≤ L)
    (near : U → Finset U) (hself : ∀ u, u ∈ near u)
    (f : ℝ) (hnear : ∀ u, ((near u).card : ℝ) ≤ f * Fintype.card U)
    (n : ℕ) (d : Y → U → ℝ) (hd : ∀ y u, 0 ≤ d y u)
    (hjoint : ∀ y m, m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ good, P.w ω * ∏ i, (N : ℝ) * row (s i) y ω ≤ ∏ i, d y (s i))
    (avg : ℝ) (havg : ∀ y,
      (Fintype.card U : ℝ)⁻¹ * ∑ u, d y u ≤ avg)
    (thr : ℝ) (hthr : 0 < thr) :
    ∀ y, P.pr (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) ≤
      ((Fintype.card U : ℝ) * (avg + n * f * L) / ((N : ℝ) * thr)) ^ n := by
  classical
  intro y
  let c : ℝ := Fintype.card U
  let t : ℝ := (N : ℝ) * thr / c
  let b : ℝ := c⁻¹ * ∑ u, d y u + n * f * L
  let q : ℝ := avg + n * f * L
  let Z : U → Ω → ℝ := fun u ω => (N : ℝ) * row u y ω
  have hcNat : 0 < Fintype.card U := Fintype.card_pos_iff.mpr ‹Nonempty U›
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast hcNat
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht : 0 < t := by positivity
  have hf : 0 ≤ f := by
    obtain ⟨u₀⟩ := ‹Nonempty U›
    have hcard : (1 : ℝ) ≤ ((near u₀).card : ℝ) := by
      have hmem : u₀ ∈ near u₀ := hself u₀
      exact_mod_cast (Finset.card_pos.mpr ⟨u₀, hmem⟩)
    have hprod : (1 : ℝ) ≤ f * c := by
      exact hcard.trans (hnear u₀)
    nlinarith
  have hdsum : 0 ≤ ∑ u, d y u := Finset.sum_nonneg fun u _ => hd y u
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact add_nonneg (mul_nonneg (by positivity) hdsum)
      (mul_nonneg (mul_nonneg (by positivity) hf) hL)
  have hble : b ≤ q := by
    dsimp [b, q]
    exact add_le_add (havg y) le_rfl
  have hq0 : 0 ≤ q := hb0.trans hble
  have hratio : b / t ≤ (c * q) / ((N : ℝ) * thr) := by
    calc
      b / t ≤ q / t := div_le_div_of_nonneg_right hble ht.le
      _ = (c * q) / ((N : ℝ) * thr) := by
        dsimp [t]
        field_simp
        <;> ring
  have hZ : ∀ u ω, 0 ≤ Z u ω := by
    intro u ω
    dsimp [Z]
    exact mul_nonneg (by positivity) (hrow_nonneg u y ω)
  have hcapZ : ∀ u ω, ω ∈ good → Z u ω ≤ L := by
    intro u ω hω
    exact hcap u y ω hω
  have hjointZ : ∀ m, m ≤ n → ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ good, P.w ω * ∏ i, Z (s i) ω ≤
          (1 : ℝ) ^ m * ∏ i, d y (s i) := by
    intro m hm s hs
    simpa [Z, one_pow] using hjoint y m hm s hs
  have htail := Lane_sol_s10_1k.scattered_retained_tail P good Z hZ L hL
    hcapZ near hself f hnear n 1 (by norm_num) (d y) (hd y)
    (by
      intro m hm s hs
      simpa [one_pow] using hjointZ m hm s hs)
    t ht
  have hsumZ (ω : Ω) :
      c⁻¹ * ∑ u, Z u ω = ((N : ℝ) * ∑ u, row u y ω) / c := by
    calc
      c⁻¹ * ∑ u, Z u ω = c⁻¹ * ((N : ℝ) * ∑ u, row u y ω) := by
        congr 1
        simp [Z, Finset.mul_sum]
      _ = ((N : ℝ) * ∑ u, row u y ω) / c := by
        rw [div_eq_mul_inv]
        ring
  have hscaled (ω : Ω) :
      thr < ∑ u, row u y ω ↔ t < c⁻¹ * ∑ u, Z u ω := by
    rw [hsumZ]
    dsimp [t]
    rw [div_lt_div_iff_of_pos_right hc]
    constructor
    · intro hlt
      exact mul_lt_mul_of_pos_left hlt hNreal
    · intro hmul
      have hdiv :
          ((N : ℝ) * thr) / (N : ℝ) < ((N : ℝ) * (∑ u, row u y ω)) / (N : ℝ) :=
        (div_lt_div_iff_of_pos_right hNreal).2 hmul
      simpa [mul_div_cancel_left₀, hNreal.ne'] using hdiv
  have hevent :
      (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) =
      (fun ω => ω ∈ good ∧ t < c⁻¹ * ∑ u, Z u ω) := by
    funext ω
    exact propext (and_congr_right fun _ => hscaled ω)
  have htail' :
      P.pr (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) ≤ (b / t) ^ n := by
    rw [hevent]
    calc
      P.pr (fun ω => ω ∈ good ∧ t < c⁻¹ * ∑ u, Z u ω) ≤
          (1 ^ n * (c⁻¹ * ∑ u, d y u + n * f * L) ^ n) / t ^ n := htail
      _ = (b / t) ^ n := by
        dsimp [b]
        calc
          1 ^ n * (c⁻¹ * ∑ u, d y u + n * f * L) ^ n / t ^ n =
              (c⁻¹ * ∑ u, d y u + n * f * L) ^ n / t ^ n := by simp
          _ = ((c⁻¹ * ∑ u, d y u + n * f * L) / t) ^ n := by rw [← div_pow]
  have hfinal : (b / t) ^ n ≤ (c * q / ((N : ℝ) * thr)) ^ n :=
    pow_le_pow_left₀ (div_nonneg hb0 ht.le) hratio n
  calc
    P.pr (fun ω => ω ∈ good ∧ thr < ∑ u, row u y ω) ≤ (b / t) ^ n := htail'
    _ ≤ (c * q / ((N : ℝ) * thr)) ^ n := hfinal

end HypercubeRamsey.Lane_q_s10_b
