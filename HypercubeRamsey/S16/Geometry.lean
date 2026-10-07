import HypercubeRamsey.PartC.Resampling
import HypercubeRamsey.S16.Geometry_q_s16_geom

/-!
# Section 16 low-mode geometry and shared quantitative assumptions

The geometry certificates attach the combinatorial data from L16.1 to the
audited `LowGeom` interface. `LowModeQuantFacts` is the common quantitative
predicate used by later low-mode sections; it contains scale and conflict
bounds, but no syndrome, cell, pool, or sampler conclusion.
-/

namespace HypercubeRamsey.S16

open Classical
open scoped BigOperators

/-- L16.0: quantitative hypotheses shared with Sections 17 and 18. The fixed
exponent `1/2` is the precise reading of the paper's little-oh bounds.
`hκ` supplies the `c14_pos`, `h0_pos`, and `cChernoff_pos` contracts from
`CConsts.Admissible`; `ProfiledTiling.Valid` carries the Section 14 solver
contracts using `c14`. -/
structure LowModeQuantFacts {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} (K16 : ℝ) : Prop where
  profiled_valid : PT.Valid
  mode_low : PT.tiling.mode.isLow
  n_large : 2 ≤ T.S.n k
  K16_pos : 0 < K16
  height_bound : ∀ i : Fin PT.tiling.m,
    ((PT.tiling.P i).h : ℝ) ≤ Real.rpow (Real.log (T.S.n k : ℝ)) (1 / 10 : ℝ)
  prefix_bound : ∀ i : Fin PT.tiling.m,
    ((PT.tiling.P i).ℓ : ℝ) ≤ Real.sqrt (Real.log (T.S.n k : ℝ))
  patch_mass_bound : ∀ i : Fin PT.tiling.m,
    Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
      Real.sqrt (Real.log (T.S.n k : ℝ))
  bin_count_bound : ∀ i : Fin PT.tiling.m,
    ((PT.tiling.P i).d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (T.S.n k : ℝ)))
  interaction_scale_bound : ∀ i : Fin PT.tiling.m,
    Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ κ.KB * Real.log (T.S.n k : ℝ)
  degree_bound : ∀ i : Fin PT.tiling.m, ∀ x ∈ PT.envelope i,
    (T.S.n k : ℝ) * |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
      K16 * Real.log (T.S.n k : ℝ)
  conflict_bound : ∀ i : Fin PT.tiling.m, ∀ v ∈ PT.activeVertices,
    ∀ x : Fin (T.S.N k),
      (((PT.mesh.corner v i).filter fun z =>
        κ.ξ < |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|).card ≤
        K16 * Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)))

/-- Numerical feasibility for L16.1. These are scale inequalities, not
syndrome/cell existence assumptions. The uniform cutoff node produces them. -/
structure LowModeScaleFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16) : Prop where
  n_four : 4 ≤ T.S.n k
  class_scale : 2 ≤ κ.A0 * Real.log (T.S.n k : ℝ)
  coset_room :
    4 * κ.A0 * Real.log (T.S.n k : ℝ) *
      max 1 ((Finset.univ.biUnion fun i : Fin PT.tiling.m =>
        PT.tiling.Icoord i).card : ℝ) ≤ T.S.n k
  slice_room : ∀ i : Fin PT.tiling.m,
    2 * (2 ^ (PT.tiling.P i).h : ℕ) ≤
      ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊
  coloring_room :
    1 + (∑ j ∈ Finset.range (⌈Real.rpow (Real.log (T.S.n k : ℝ)) 3⌉₊ + 1),
      (Nat.choose (T.S.n k) j : ℝ)) ≤
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)
  patch_capacity : ∀ i : Fin PT.tiling.m,
    (3 * Real.rpow 2 ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
      Real.rpow (T.S.n k : ℝ) κ.Ac +
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)) *
      (⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
        (PT.tiling.P i).d⌉₊ : ℝ) ≤ Fintype.card (Bin PT.tiling i)
  cell_scope_bound : ∀ i : Fin PT.tiling.m,
    (⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / (PT.tiling.P i).d⌉₊ : ℝ) ≤
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10)
  comparison_room : ∀ i : Fin PT.tiling.m,
    2 * (Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10) + 1) ^ 2 ≤
      Fintype.card (Bin PT.tiling i)

set_option maxHeartbeats 400000
/-- Fixed constants precede every dimension, host size, and tiling.
The dyadic mass allocation in `Tiling.Valid` supplies the host capacity;
its lower bound on `S` is essential here (16:106–107). -/
theorem low_geometry_thresholds {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16),
        n₀ ≤ T.S.n k → C₀ * (2 : ℝ) ^ T.S.n k ≤ T.S.N k →
        LowModeScaleFacts hκ Q := by
  classical
  have hPpos : 0 < κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hRpos : 0 < κ.R := by
    rw [hκ.R_eq]
    exact pow_pos hPpos _
  have hA0pos : 0 < κ.A0 := by
    exact lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 10 ^ 6)
      (by exact_mod_cast hRpos)) hκ.A0_big
  have hKpos : 0 < κ.Kcell := by
    rcases hκ.bucket with ⟨_, _, _, _, hθ⟩
    exact lt_of_lt_of_le (by positivity) hκ.Kcell_big
  let C0 : ℝ := 800 * (6 * κ.Kcell + 2)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hC0large : 800 ≤ C0 := by dsimp [C0]; nlinarith [hKpos]
  let L : ℕ → ℝ := fun m => Real.log (m : ℝ)
  let Good : ℕ → Prop := fun m =>
    4 ≤ m ∧
    2 ≤ κ.A0 * L m ∧
    4 * κ.A0 * L m * (L m + 1) ≤ (m : ℝ) ∧
    2 * m ≤ ⌊Real.rpow (m : ℝ) κ.Ac⌋₊ ∧
    (1 + ∑ j ∈ Finset.range (⌈Real.rpow (L m) 3⌉₊ + 1),
      (Nat.choose m j : ℝ)) ≤ Real.exp (Real.rpow (L m) 5) ∧
    κ.Kcell * (m : ℝ) ^ 200 + 1 ≤ Real.exp (Real.rpow (L m) 10) ∧
    2 * (Real.exp (Real.rpow (L m) 10) + 1) ^ 2 * (m : ℝ) ^ 2 ≤ (2 : ℝ) ^ m ∧
    2 * (κ.Kcell + 1) * (m : ℝ) ^ 201 * Real.exp (Real.rpow (L m) 5) ≤
      (2 : ℝ) ^ m
  have hLog1 : ∀ᶠ m : ℕ in Filter.atTop, L m ≤ (m : ℝ) / 1000 := by
    filter_upwards [Lane_q_s16_geom.eventually_log_rpow_le_linear
      (s := 1) (ε := 1 / 1000) (by norm_num) (by norm_num)] with m hm
    simpa [L, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm
  have hLog2 : ∀ᶠ m : ℕ in Filter.atTop,
      Real.rpow (L m) 2 ≤ (m : ℝ) / (8 * κ.A0) := by
    filter_upwards [Lane_q_s16_geom.eventually_log_rpow_le_linear
      (s := 2) (ε := 1 / (8 * κ.A0)) (by norm_num)
      (div_pos (by norm_num) (mul_pos (by norm_num) hA0pos))] with m hm
    simpa [L, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm
  have hLog5 : ∀ᶠ m : ℕ in Filter.atTop,
      Real.rpow (L m) 5 ≤ (m : ℝ) / 1000 := by
    filter_upwards [Lane_q_s16_geom.eventually_log_rpow_le_linear
      (s := 5) (ε := 1 / 1000) (by norm_num) (by norm_num)] with m hm
    simpa [L, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm
  have hLog10 : ∀ᶠ m : ℕ in Filter.atTop,
      Real.rpow (L m) 10 ≤ (m : ℝ) / 1000 := by
    filter_upwards [Lane_q_s16_geom.eventually_log_rpow_le_linear
      (s := 10) (ε := 1 / 1000) (by norm_num) (by norm_num)] with m hm
    simpa [L, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm
  let Bcut : ℝ := max (4 : ℝ)
    (max (2 / κ.A0) (Real.log (κ.Kcell + 1) + 1))
  have hLogLarge : ∀ᶠ m : ℕ in Filter.atTop, Bcut ≤ L m := by
    have hlog :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop Bcut
    simpa [L] using hlog
  have hNatLarge : ∀ᶠ m : ℕ in Filter.atTop, 100 ≤ m :=
    Filter.eventually_ge_atTop 100
  have hGood : ∀ᶠ m : ℕ in Filter.atTop, Good m := by
    filter_upwards [hLog1, hLog2, hLog5, hLog10, hLogLarge, hNatLarge]
      with m hlog1 hlog2 hlog5 hlog10 hlogLarge hm
    let l := L m
    have hl4 : 4 ≤ l := by
      exact (le_max_left (4 : ℝ) _).trans hlogLarge
    have hlA0 : 2 / κ.A0 ≤ l := by
      exact (le_max_left _ _).trans ((le_max_right (4 : ℝ) _).trans hlogLarge)
    have hlK : Real.log (κ.Kcell + 1) + 1 ≤ l := by
      exact (le_max_right _ _).trans ((le_max_right (4 : ℝ) _).trans hlogLarge)
    have hlpos : 0 < l := by linarith
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmreal : (100 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hlog1' : l ≤ (m : ℝ) / 1000 := by simpa [l] using hlog1
    have hlog2' : l ^ 2 ≤ (m : ℝ) / (8 * κ.A0) := by
      simpa [l, Real.rpow_natCast] using hlog2
    have hlog5' : l ^ 5 ≤ (m : ℝ) / 1000 := by
      simpa [l, Real.rpow_natCast] using hlog5
    have hlog10' : l ^ 10 ≤ (m : ℝ) / 1000 := by
      simpa [l, Real.rpow_natCast] using hlog10
    unfold Good
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hA : 0 < κ.A0 := hA0pos
      have hmul := mul_le_mul_of_nonneg_left hlA0 hA.le
      have hcancel : κ.A0 * (2 / κ.A0) = 2 := by field_simp [ne_of_gt hA]
      nlinarith [hmul, hcancel]
    · have hLplus : l + 1 ≤ 2 * l := by linarith
      have hcoef : 0 ≤ 4 * κ.A0 * l := by positivity
      have hstep := mul_le_mul_of_nonneg_left hLplus hcoef
      have hsq : 8 * κ.A0 * l ^ 2 ≤ (m : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hlog2' (show 0 ≤ 8 * κ.A0 by positivity)
        have hcancel : 8 * κ.A0 * ((m : ℝ) / (8 * κ.A0)) = (m : ℝ) := by
          field_simp [ne_of_gt hA0pos]
        exact hmul.trans_eq hcancel
      nlinarith [hstep, hsq]
    · have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have hpow200 : (m : ℝ) ^ 2 ≤ Real.rpow (m : ℝ) κ.Ac := by
        rw [hκ.Ac_eq]
        simpa [Real.rpow_natCast] using
          (Real.rpow_le_rpow_of_exponent_le hmOne (by norm_num : (2 : ℝ) ≤ 200))
      have hpow200' : (m : ℝ) ^ 2 ≤ Real.rpow (m : ℝ) 200 := by
        simpa [hκ.Ac_eq] using hpow200
      have hfloor : m ^ 2 ≤ ⌊Real.rpow (m : ℝ) κ.Ac⌋₊ := by
        rw [hκ.Ac_eq]
        apply (Nat.le_floor_iff' (Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < m)))).2
        exact_mod_cast hpow200'
      have htwo : 2 * m ≤ m ^ 2 := by nlinarith
      exact htwo.trans hfloor
    · let r := ⌈Real.rpow l 3⌉₊
      have hrCast : (r : ℝ) ≤ l ^ 3 + 1 := by
        have hceil : r ≤ ⌊Real.rpow l 3⌋₊ + 1 := Nat.ceil_le_floor_add_one _
        have hceilR : (r : ℝ) ≤ (⌊Real.rpow l 3⌋₊ : ℝ) + 1 := by exact_mod_cast hceil
        have hfloor : (⌊Real.rpow l 3⌋₊ : ℝ) ≤ Real.rpow l 3 := by
          have hfloor' : (⌊l ^ 3⌋₊ : ℝ) ≤ l ^ 3 := Nat.floor_le (by positivity)
          simpa [Real.rpow_natCast] using hfloor'
        have hceilR' : (r : ℝ) ≤ Real.rpow l 3 + 1 := by
          linarith [hceilR, hfloor]
        simpa [Real.rpow_natCast] using hceilR'
      have hsumNat :
          (∑ j ∈ Finset.range (r + 1), Nat.choose m j) ≤ (r + 1) * m ^ r := by
        calc
          (∑ j ∈ Finset.range (r + 1), Nat.choose m j) ≤
              ∑ j ∈ Finset.range (r + 1), m ^ r := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
                exact (Nat.choose_le_pow m j).trans
                  (Nat.pow_le_pow_right (by omega : 1 ≤ m) hjle)
          _ = (r + 1) * m ^ r := by simp
      have hsumReal :
          (∑ j ∈ Finset.range (r + 1), (Nat.choose m j : ℝ)) ≤
            ((r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r := by exact_mod_cast hsumNat
      have hL3 : (1 : ℝ) ≤ l ^ 3 := by nlinarith [hl4]
      have hLminus : (3 : ℝ) ≤ l - 1 := by linarith
      have hLgap : (3 : ℝ) ≤ l ^ 3 * (l - 1) := by
        calc
          3 = 1 * 3 := by norm_num
          _ ≤ l ^ 3 * (l - 1) := mul_le_mul hL3 hLminus (by norm_num) (by positivity)
      have hL4id : l ^ 4 = l ^ 3 + l ^ 3 * (l - 1) := by ring
      have hRplus : (r : ℝ) + 2 ≤ l ^ 4 := by
        have := hL4id
        linarith [hrCast, hLgap]
      have hLogR : Real.log ((r : ℝ) + 2) ≤ l ^ 4 := by
        have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (r : ℝ) + 2)
        linarith [h, hRplus]
      have hRL : (r : ℝ) * l ≤ l ^ 4 + l := by
        exact (mul_le_mul_of_nonneg_right hrCast (by positivity)).trans_eq (by ring)
      have hL5 : 4 * l ^ 4 ≤ l ^ 5 := by
        have hprod : 0 ≤ l ^ 4 * (l - 4) :=
          mul_nonneg (by positivity) (by linarith [hl4])
        nlinarith [hprod]
      have hExpArg : Real.log ((r : ℝ) + 2) + (r : ℝ) * l ≤ l ^ 5 := by
        have hle : l ^ 4 + (l ^ 4 + l) ≤ 3 * l ^ 4 := by nlinarith [hl4]
        linarith [hLogR, hRL, hL5, hle]
      have hexpNatPow (p : ℕ) : Real.exp ((p : ℝ) * l) = (m : ℝ) ^ p := by
        have hlogpow : Real.log ((m : ℝ) ^ p) = (p : ℝ) * l := by
          simpa [l, L, mul_comm] using (Real.log_pow (m : ℝ) p)
        calc
          Real.exp ((p : ℝ) * l) = Real.exp (Real.log ((m : ℝ) ^ p)) :=
            congrArg Real.exp hlogpow.symm
          _ = (m : ℝ) ^ p := Real.exp_log (pow_pos hmpos _)
      have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      have hmPowOne : (1 : ℝ) ≤ (m : ℝ) ^ r := one_le_pow₀ hmOne
      have hCountCoarse :
          1 + ((r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r ≤
            ((r : ℝ) + 2) * (m : ℝ) ^ r := by
        calc
          1 + ((r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r ≤
              (m : ℝ) ^ r + ((r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r := by nlinarith [hmPowOne]
          _ = ((r : ℝ) + 2) * (m : ℝ) ^ r := by push_cast; ring
      have hExpEq : Real.exp (Real.log ((r : ℝ) + 2) + (r : ℝ) * l) =
          ((r : ℝ) + 2) * (m : ℝ) ^ r := by
        calc
          Real.exp (Real.log ((r : ℝ) + 2) + (r : ℝ) * l) =
              Real.exp (Real.log ((r : ℝ) + 2)) * Real.exp ((r : ℝ) * l) := by
                rw [Real.exp_add]
          _ = ((r : ℝ) + 2) * (m : ℝ) ^ r := by
                rw [Real.exp_log (by positivity), hexpNatPow r]
      calc
        1 + ∑ j ∈ Finset.range (r + 1), (Nat.choose m j : ℝ) ≤
            1 + ((r + 1 : ℕ) : ℝ) * (m : ℝ) ^ r := by
              simpa [add_comm] using add_le_add_left hsumReal (1 : ℝ)
        _ ≤ ((r : ℝ) + 2) * (m : ℝ) ^ r := hCountCoarse
        _ = Real.exp (Real.log ((r : ℝ) + 2) + (r : ℝ) * l) := hExpEq.symm
        _ ≤ Real.exp (Real.rpow l 5) := by
          apply Real.exp_le_exp.mpr
          simpa [Real.rpow_natCast] using hExpArg
    · have hL9 : (202 : ℝ) ≤ l ^ 9 := by
        calc
          202 ≤ 4 ^ 9 := by norm_num
          _ ≤ l ^ 9 := by gcongr
      have hL10large : (202 : ℝ) * l ≤ Real.rpow l 10 := by
        calc
          202 * l ≤ l ^ 9 * l := mul_le_mul_of_nonneg_right hL9 (by positivity)
          _ = l ^ 10 := by ring
          _ = Real.rpow l 10 := (Real.rpow_natCast l 10).symm
      have hLogK : Real.log (κ.Kcell + 1) ≤ l - 1 := by linarith [hlK]
      have hLogScope : Real.log (κ.Kcell + 1) + 200 * l ≤ Real.rpow l 10 := by
        have h201 : Real.log (κ.Kcell + 1) + 200 * l ≤ 201 * l := by linarith [hLogK]
        have h202 : 201 * l ≤ 202 * l := by nlinarith [hlpos]
        exact h201.trans (h202.trans hL10large)
      have hexpNatPow (p : ℕ) : Real.exp ((p : ℝ) * l) = (m : ℝ) ^ p := by
        have hlogpow : Real.log ((m : ℝ) ^ p) = (p : ℝ) * l := by
          simpa [l, L, mul_comm] using (Real.log_pow (m : ℝ) p)
        calc
          Real.exp ((p : ℝ) * l) = Real.exp (Real.log ((m : ℝ) ^ p)) :=
            congrArg Real.exp hlogpow.symm
          _ = (m : ℝ) ^ p := Real.exp_log (pow_pos hmpos _)
      have hscopeExp : (κ.Kcell + 1) * (m : ℝ) ^ 200 ≤ Real.exp (Real.rpow l 10) := by
        calc
          (κ.Kcell + 1) * (m : ℝ) ^ 200 =
              Real.exp (Real.log (κ.Kcell + 1) + (200 : ℝ) * l) := by
                calc
                  (κ.Kcell + 1) * (m : ℝ) ^ 200 =
                      (κ.Kcell + 1) * Real.exp (200 * l) := by
                        rw [(hexpNatPow 200).symm]
                        change (κ.Kcell + 1) * Real.exp ((200 : ℝ) * l) =
                          (κ.Kcell + 1) * Real.exp ((200 : ℝ) * l)
                        norm_num
                  _ = Real.exp (Real.log (κ.Kcell + 1)) * Real.exp (200 * l) := by
                        rw [Real.exp_log (by positivity)]
                  _ = Real.exp (Real.log (κ.Kcell + 1) + 200 * l) := by rw [← Real.exp_add]
          _ ≤ Real.exp (Real.rpow l 10) := Real.exp_le_exp.mpr hLogScope
      have hpoly : κ.Kcell * (m : ℝ) ^ 200 + 1 ≤
          (κ.Kcell + 1) * (m : ℝ) ^ 200 := by
        have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        have hmPowOne : (1 : ℝ) ≤ (m : ℝ) ^ 200 := one_le_pow₀ hmOne
        calc
          κ.Kcell * (m : ℝ) ^ 200 + 1 ≤
              κ.Kcell * (m : ℝ) ^ 200 + (m : ℝ) ^ 200 := by gcongr
          _ = (κ.Kcell + 1) * (m : ℝ) ^ 200 := by ring
      exact hpoly.trans hscopeExp
    · have hCompArg : Real.log 8 + 2 * Real.rpow l 10 + 2 * l ≤
          (m : ℝ) * Real.log 2 := by
        have hpow : Real.rpow l 10 ≤ (m : ℝ) / 1000 := by
          simpa [Real.rpow_natCast] using hlog10'
        exact Lane_q_s16_geom.comparison_exp_argument hmreal hpow hlog1'
      have hexpSquare : (Real.exp (Real.rpow l 10)) ^ 2 =
          Real.exp (2 * Real.rpow l 10) := by
        rw [← Real.exp_nat_mul]
        change Real.exp ((2 : ℝ) * Real.rpow l 10) =
          Real.exp (2 * Real.rpow l 10)
        rfl
      have hTwoPow : Real.exp ((m : ℝ) * Real.log 2) = (2 : ℝ) ^ m := by
        have hlogPow : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by
          simpa [mul_comm] using (Real.log_pow (2 : ℝ) m)
        calc
          Real.exp ((m : ℝ) * Real.log 2) = Real.exp (Real.log ((2 : ℝ) ^ m)) :=
            congrArg Real.exp hlogPow.symm
          _ = (2 : ℝ) ^ m := Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      have hexpNatPow (p : ℕ) : Real.exp ((p : ℝ) * l) = (m : ℝ) ^ p := by
        have hlogpow : Real.log ((m : ℝ) ^ p) = (p : ℝ) * l := by
          simpa [l, L, mul_comm] using (Real.log_pow (m : ℝ) p)
        calc
          Real.exp ((p : ℝ) * l) = Real.exp (Real.log ((m : ℝ) ^ p)) :=
            congrArg Real.exp hlogpow.symm
          _ = (m : ℝ) ^ p := Real.exp_log (pow_pos hmpos _)
      have hCompEq : 8 * Real.exp (2 * Real.rpow l 10) * (m : ℝ) ^ 2 =
          Real.exp (Real.log 8 + 2 * Real.rpow l 10 + 2 * l) := by
        have h8mul : 8 * Real.exp (2 * Real.rpow l 10) =
            Real.exp (Real.log 8) * Real.exp (2 * Real.rpow l 10) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 8)]
        have hpow2 : (m : ℝ) ^ 2 = Real.exp (2 * l) := (hexpNatPow 2).symm
        calc
          8 * Real.exp (2 * Real.rpow l 10) * (m : ℝ) ^ 2 =
              (Real.exp (Real.log 8) * Real.exp (2 * Real.rpow l 10)) * Real.exp (2 * l) := by
                calc
                  8 * Real.exp (2 * Real.rpow l 10) * (m : ℝ) ^ 2 =
                      (8 * Real.exp (2 * Real.rpow l 10)) * (m : ℝ) ^ 2 := by ring
                  _ = (Real.exp (Real.log 8) * Real.exp (2 * Real.rpow l 10)) * (m : ℝ) ^ 2 :=
                        congrArg (fun x : ℝ => x * (m : ℝ) ^ 2) h8mul
                  _ = _ := by rw [hpow2]
          _ = Real.exp (Real.log 8 + 2 * Real.rpow l 10 + 2 * l) := by
                rw [← Real.exp_add, ← Real.exp_add]
      have hExpGe : (1 : ℝ) ≤ Real.exp (Real.rpow l 10) := by
        apply Real.one_le_exp_iff.mpr
        exact Real.rpow_nonneg (le_of_lt hlpos) 10
      have hCompCore : 2 * (Real.exp (Real.rpow l 10) + 1) ^ 2 * (m : ℝ) ^ 2 ≤ (2 : ℝ) ^ m := by
        calc
          2 * (Real.exp (Real.rpow l 10) + 1) ^ 2 * (m : ℝ) ^ 2 ≤
              8 * Real.exp (2 * Real.rpow l 10) * (m : ℝ) ^ 2 := by
                have hsq : (Real.exp (Real.rpow l 10) + 1) ^ 2 ≤
                    4 * (Real.exp (Real.rpow l 10)) ^ 2 :=
                  Lane_q_s16_geom.square_add_one_le_four_mul_sq hExpGe
                calc
                  2 * (Real.exp (Real.rpow l 10) + 1) ^ 2 * (m : ℝ) ^ 2 ≤
                      2 * (4 * (Real.exp (Real.rpow l 10)) ^ 2) * (m : ℝ) ^ 2 := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hsq (by norm_num)) (sq_nonneg (m : ℝ))
                  _ = 8 * Real.exp (2 * Real.rpow l 10) * (m : ℝ) ^ 2 := by
                    rw [hexpSquare]
                    ring
          _ = Real.exp (Real.log 8 + 2 * Real.rpow l 10 + 2 * l) := hCompEq
          _ ≤ Real.exp ((m : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hCompArg
          _ = (2 : ℝ) ^ m := hTwoPow
      exact hCompCore
    · have hLogC : Real.log (2 * (κ.Kcell + 1)) ≤ l := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : κ.Kcell + 1 ≠ 0)]
        have hlog2 : Real.log 2 ≤ 1 :=
          (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq (by norm_num)
        linarith [hlK]
      have hCapArg : Real.log (2 * (κ.Kcell + 1)) + 201 * l + Real.rpow l 5 ≤
          (m : ℝ) * Real.log 2 := by
        have hLog1' : l ≤ (m : ℝ) / 1000 := by simpa [l] using hlog1
        have hLog5' : Real.rpow l 5 ≤ (m : ℝ) / 1000 := by simpa [l] using hlog5
        exact Lane_q_s16_geom.capacity_exp_argument hmreal hLogC hLog1' hLog5'
      have hexpNatPow (p : ℕ) : Real.exp ((p : ℝ) * l) = (m : ℝ) ^ p := by
        have hlogpow : Real.log ((m : ℝ) ^ p) = (p : ℝ) * l := by
          simpa [l, L, mul_comm] using (Real.log_pow (m : ℝ) p)
        calc
          Real.exp ((p : ℝ) * l) = Real.exp (Real.log ((m : ℝ) ^ p)) :=
            congrArg Real.exp hlogpow.symm
          _ = (m : ℝ) ^ p := Real.exp_log (pow_pos hmpos _)
      have hTwoPow : Real.exp ((m : ℝ) * Real.log 2) = (2 : ℝ) ^ m := by
        have hlogPow : Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by
          simpa [mul_comm] using (Real.log_pow (2 : ℝ) m)
        calc
          Real.exp ((m : ℝ) * Real.log 2) = Real.exp (Real.log ((2 : ℝ) ^ m)) :=
            congrArg Real.exp hlogPow.symm
          _ = (2 : ℝ) ^ m := Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) _)
      have hCapEq :
          2 * (κ.Kcell + 1) * (m : ℝ) ^ 201 * Real.exp (Real.rpow l 5) =
            Real.exp (Real.log (2 * (κ.Kcell + 1)) + 201 * l + Real.rpow l 5) := by
        have hCoeff : 2 * (κ.Kcell + 1) =
            Real.exp (Real.log (2 * (κ.Kcell + 1))) :=
          (Real.exp_log (by positivity)).symm
        have hpow201 : (m : ℝ) ^ 201 = Real.exp (201 * l) :=
          (hexpNatPow 201).symm
        calc
          2 * (κ.Kcell + 1) * (m : ℝ) ^ 201 * Real.exp (Real.rpow l 5) =
              (2 * (κ.Kcell + 1)) * Real.exp (201 * l) * Real.exp (Real.rpow l 5) := by
                rw [hpow201]
          _ = Real.exp (Real.log (2 * (κ.Kcell + 1))) * Real.exp (201 * l) *
                Real.exp (Real.rpow l 5) := by
                  exact congrArg (fun x : ℝ => x * Real.exp (201 * l) * Real.exp (Real.rpow l 5)) hCoeff
          _ = Real.exp (Real.log (2 * (κ.Kcell + 1)) + 201 * l + Real.rpow l 5) := by
                rw [← Real.exp_add, ← Real.exp_add]
      calc
        2 * (κ.Kcell + 1) * (m : ℝ) ^ 201 * Real.exp (Real.rpow l 5) =
            Real.exp (Real.log (2 * (κ.Kcell + 1)) + 201 * l + Real.rpow l 5) := hCapEq
        _ ≤ Real.exp ((m : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hCapArg
        _ = (2 : ℝ) ^ m := hTwoPow
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hGood
  refine ⟨n₀, C0, hC0, ?_⟩
  intro T k PT K16 Q hn hhost
  let n := T.S.n k
  have hGoodN : Good n := by
    apply hn₀
    simpa [n] using hn
  obtain ⟨hn4, hclass, hcoset, hsliceBase, hcoloring, hscope, hcomparison, hcapacity⟩ := hGoodN
  let topH : ℕ := ⌈Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ)⌉₊
  let inner : Finset (Fin n) := Finset.univ.biUnion fun i => PT.tiling.Icoord i
  have hlogn : 1 ≤ Real.log (n : ℝ) := by
    have hlog4 : 1 ≤ Real.log (4 : ℝ) := by
      have hlog4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [hlog4eq]
      nlinarith [Lane_q_s16_geom.log_two_ge_half]
    have hnreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    exact hlog4.trans (Real.log_le_log (by norm_num) hnreal)
  have hpowlog : Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ) ≤ Real.log (n : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hlogn (by norm_num : (1 / 10 : ℝ) ≤ 1)
    simpa using h
  have htopbound : (topH : ℝ) ≤ Real.log (n : ℝ) + 1 := by
    have hceilNat : topH ≤ ⌊Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ)⌋₊ + 1 := by
      simpa [topH] using Nat.ceil_le_floor_add_one
        (Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ))
    have hrpow_nonneg : 0 ≤ Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ) :=
      Real.rpow_nonneg (by linarith [hlogn]) _
    have hfloor : (⌊Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ)⌋₊ : ℝ) ≤
        Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ) :=
      Nat.floor_le hrpow_nonneg
    calc
      (topH : ℝ) ≤ (⌊Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ)⌋₊ : ℝ) + 1 := by
        exact_mod_cast hceilNat
      _ ≤ Real.log (n : ℝ) + 1 := by linarith [hfloor, hpowlog]
  have hlogUpper : Real.log (n : ℝ) ≤ (n : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by exact_mod_cast (by omega : 0 < n))
  have htop_le_n : topH ≤ n := by
    have ht : (topH : ℝ) ≤ (n : ℝ) := by linarith [htopbound, hlogUpper]
    exact_mod_cast ht
  have htop_le (i : Fin PT.tiling.m) : (PT.tiling.P i).h ≤ topH := by
    exact Nat.cast_le.mp ((Q.height_bound i).trans (by simpa [topH] using
      (Nat.le_ceil (Real.rpow (Real.log (n : ℝ)) (1 / 10 : ℝ)))) )
  have hinner_sub : inner ⊆ topCoordinates n topH := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨i, hi, hji⟩
    have hjtop : n - (PT.tiling.P i).h ≤ j.val := by
      simpa [Tiling.Icoord, topCoordinates] using hji
    have hhi := htop_le i
    have hsub : n - topH ≤ n - (PT.tiling.P i).h := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub.trans hjtop⟩
  have hinner_card : inner.card ≤ topH := by
    let f : {j : Fin n // j ∈ inner} → Fin topH := fun j =>
      ⟨j.val.val - (n - topH), by
        have hj := (Finset.mem_filter.mp (hinner_sub j.property)).2
        omega⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      have h := congrArg Fin.val hxy
      have hxlo := (Finset.mem_filter.mp (hinner_sub x.property)).2
      have hylo := (Finset.mem_filter.mp (hinner_sub y.property)).2
      dsimp [f] at h
      omega
    have hcardEq : inner.card = Fintype.card {j : Fin n // j ∈ inner} := by
      rw [Fintype.card_subtype]
      simp
    rw [hcardEq]
    calc
      Fintype.card {j : Fin n // j ∈ inner} ≤ Fintype.card (Fin topH) :=
        Fintype.card_le_of_injective f hf
      _ = topH := by simp
  have hinner_card_real : (inner.card : ℝ) ≤ (topH : ℝ) := by exact_mod_cast hinner_card
  have hcosetMax : max 1 (inner.card : ℝ) ≤ Real.log (n : ℝ) + 1 := by
    apply max_le
    · linarith
    · exact hinner_card_real.trans htopbound
  refine ⟨hn4, hclass, ?_, ?_, hcoloring, ?_, ?_, ?_⟩
  · have hcoef : 0 ≤ 4 * κ.A0 * Real.log (n : ℝ) := by positivity
    calc
      4 * κ.A0 * Real.log (n : ℝ) * max 1 (inner.card : ℝ) ≤
          4 * κ.A0 * Real.log (n : ℝ) * (Real.log (n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hcosetMax hcoef
      _ ≤ (n : ℝ) := by simpa [L] using hcoset
  · intro i
    have hhlog : ((PT.tiling.P i).h : ℝ) ≤ Real.log (n : ℝ) :=
      (Q.height_bound i).trans hpowlog
    have hpow := Lane_q_s16_geom.two_pow_le_of_log (by omega) hhlog
    have hpowNat : 2 ^ (PT.tiling.P i).h ≤ n := by exact_mod_cast hpow
    calc
      2 * 2 ^ (PT.tiling.P i).h ≤ 2 * n := Nat.mul_le_mul_left 2 hpowNat
      _ ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := hsliceBase
  · intro i
    let p := PT.tiling.P i
    let ell := p.ℓ
    let d := p.d
    let E : ℝ := Real.exp (Real.rpow (Real.log (n : ℝ)) 5)
    let A : ℝ :=
      3 * Real.rpow (2 : ℝ) ((n - ell : ℕ) : ℝ) /
        Real.rpow (n : ℝ) κ.Ac + E
    let x : ℝ := κ.Kcell * Real.rpow (n : ℝ) κ.Ac / d
    let q : ℕ := ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac / d⌉₊
    have hEllH : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ n := by
      have hlen := Q.profiled_valid.tiling_valid.prefix_internal_length
      have hell := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
        (Finset.mem_univ i)
      have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
        (Finset.mem_univ i)
      omega
    have hEllN : ell ≤ n := by
      dsimp [ell, p]
      exact (Nat.le_add_right _ _).trans hEllH
    have hprefixLog : (ell : ℝ) ≤ Real.log (n : ℝ) := by
      have hp := Q.prefix_bound i
      have hsqrt : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
        have hsqrtOne : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
          simpa using Real.sqrt_le_sqrt hlogn
        have hsqrtSq : (Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) :=
          Real.sq_sqrt (by linarith [hlogn])
        nlinarith [hsqrtSq, hsqrtOne]
      exact hp.trans hsqrt
    have hpowEll := Lane_q_s16_geom.two_pow_le_of_log (by omega) hprefixLog
    have hpowEllNat : 2 ^ ell ≤ n := by exact_mod_cast hpowEll
    have hpowEllReal : (2 : ℝ) ^ ell ≤ (n : ℝ) := by exact_mod_cast hpowEllNat
    have hdleExp : (d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (n : ℝ))) := by
      exact Q.bin_count_bound i
    have hdleNReal : (d : ℝ) ≤ (n : ℝ) := by
      calc
        (d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (n : ℝ))) := hdleExp
        _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by
          have hsqrtOne : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
            simpa using Real.sqrt_le_sqrt hlogn
          have hsqrtSq : (Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) :=
            Real.sq_sqrt (by linarith [hlogn])
          nlinarith [hsqrtSq, hsqrtOne])
        _ = (n : ℝ) := Real.exp_log (by positivity)
    have hMlower : (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) ≤ (p.M : ℝ) :=
      Lane_q_s16_geom.patch_mass_lower_bound PT Q.profiled_valid n (by rfl) C0 (by rfl)
        hC0 (by simpa [n] using hhost) i hEllN
    have hdPos : 0 < d := Lane_q_s16_geom.bin_size_pos PT Q.profiled_valid i
    have hdPosReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdPos
    have hBinMulNat := Lane_q_s16_geom.bin_card_mul_bin_size PT Q.profiled_valid i
    have hBinEq : (Fintype.card (Bin PT.tiling i) : ℝ) = (p.M : ℝ) / d := by
      have hBinMul : (Fintype.card (Bin PT.tiling i) : ℝ) * (d : ℝ) = (p.M : ℝ) :=
        by exact_mod_cast hBinMulNat
      calc
        (Fintype.card (Bin PT.tiling i) : ℝ) =
            (Fintype.card (Bin PT.tiling i) : ℝ) * (d : ℝ) / d :=
          (mul_div_cancel_right₀ _ hdPosReal.ne').symm
        _ = (p.M : ℝ) / d := congrArg (fun z : ℝ => z / d) hBinMul
    have hpowNonneg : 0 ≤ Real.rpow (n : ℝ) κ.Ac :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (mul_nonneg hKpos.le hpowNonneg) (Nat.cast_nonneg _)
    have hxNorm : x = κ.Kcell * (n : ℝ) ^ 200 / d := by
      dsimp [x]
      rw [hκ.Ac_eq]
      simp [Real.rpow_natCast]
    have hceilNat : q ≤ ⌊x⌋₊ + 1 := by
      dsimp [q]
      exact Nat.ceil_le_floor_add_one x
    have hceilReal : (q : ℝ) ≤ x + 1 := by
      calc
        (q : ℝ) ≤ (⌊x⌋₊ + 1 : ℕ) := by exact_mod_cast hceilNat
        _ = (⌊x⌋₊ : ℝ) + 1 := by simp
        _ ≤ x + 1 := by linarith [Nat.floor_le hxnonneg]
    have hqMul : (q : ℝ) * (d : ℝ) ≤ κ.Kcell * (n : ℝ) ^ 200 + d := by
      calc
        (q : ℝ) * (d : ℝ) ≤ (x + 1) * (d : ℝ) :=
          mul_le_mul_of_nonneg_right hceilReal hdPosReal.le
        _ = κ.Kcell * (n : ℝ) ^ 200 + d := by
          rw [hxNorm]
          field_simp [ne_of_gt hdPosReal]
          <;> ring
    have hAeq : A =
        3 * (2 : ℝ) ^ (n - ell) / (n : ℝ) ^ 200 + E := by
      dsimp [A]
      rw [hκ.Ac_eq]
      simp [Real.rpow_natCast]
    have hCapProduct := Lane_q_s16_geom.capacity_product_bound
      (n := n) (ell := ell) (K := κ.Kcell) (E := E) (d := d)
      (by omega) hEllN hpowEllReal hdleNReal hKpos (by positivity)
      (by simpa [E, L] using hcapacity)
    have hApos : 0 ≤ A := by dsimp [A]; positivity
    have hTargetMul : A * (q : ℝ) * (d : ℝ) ≤ (p.M : ℝ) := by
      calc
        A * (q : ℝ) * (d : ℝ) = A * ((q : ℝ) * (d : ℝ)) := by ring
        _ ≤ A * (κ.Kcell * (n : ℝ) ^ 200 + d) :=
          mul_le_mul_of_nonneg_left hqMul hApos
        _ ≤ (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) := by rw [hAeq]; exact hCapProduct
        _ ≤ (p.M : ℝ) := hMlower
    change A * (q : ℝ) ≤ Fintype.card (Bin PT.tiling i)
    calc
      A * (q : ℝ) ≤ (p.M : ℝ) / d :=
        (le_div_iff₀ hdPosReal).2 (by simpa [mul_assoc] using hTargetMul)
      _ = Fintype.card (Bin PT.tiling i) := hBinEq.symm
  · intro i
    have hparts : (PT.tiling.P i).bins.parts.Nonempty := by
      by_contra hparts
      have hpartsEmpty : (PT.tiling.P i).bins.parts = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hparts
      have hYempty : (PT.tiling.P i).Y = ∅ := by
        rw [← (PT.tiling.P i).bins.sup_parts]
        simp [hpartsEmpty]
      exact (Q.profiled_valid.tiling_valid.patch_nonempty i).2.ne_empty hYempty
    have hdpos : 0 < (PT.tiling.P i).d := by
      by_contra h
      have hdzero : (PT.tiling.P i).d = 0 := by omega
      obtain ⟨B, hB⟩ := hparts
      have hcard := Q.profiled_valid.tiling_valid.bins_card i B hB
      have hBzero : B.card = 0 := by simpa [hdzero] using hcard
      have hBempty : B = ∅ := Finset.card_eq_zero.mp hBzero
      have hBot : (∅ : Finset (Fin (T.S.N k))) ∈ (PT.tiling.P i).bins.parts := by
        simpa [hBempty] using hB
      exact (PT.tiling.P i).bins.bot_notMem hBot
    let x : ℝ := κ.Kcell * Real.rpow (n : ℝ) κ.Ac / (PT.tiling.P i).d
    have hpowNonneg : 0 ≤ Real.rpow (n : ℝ) κ.Ac := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hxnonneg : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (mul_nonneg hKpos.le hpowNonneg) (Nat.cast_nonneg _)
    have hdNat : 1 ≤ (PT.tiling.P i).d := Nat.one_le_iff_ne_zero.mpr hdpos.ne'
    have hdge : (1 : ℝ) ≤ (PT.tiling.P i).d := by exact_mod_cast hdNat
    have hnum_nonneg : 0 ≤ κ.Kcell * (n : ℝ) ^ 200 :=
      mul_nonneg hKpos.le (pow_nonneg (Nat.cast_nonneg n) 200)
    have hxle_norm : κ.Kcell * Real.rpow (n : ℝ) κ.Ac /
        ((PT.tiling.P i).d : ℝ) ≤ κ.Kcell * (n : ℝ) ^ 200 := by
      rw [Lane_q_s16_geom.rpow_ac_eq_pow_200 hκ n]
      exact div_le_self hnum_nonneg hdge
    have hxle : x ≤ κ.Kcell * (n : ℝ) ^ 200 := by simpa [x] using hxle_norm
    have hceilNat : ⌈x⌉₊ ≤ ⌊x⌋₊ + 1 := Nat.ceil_le_floor_add_one x
    have hceilReal : (⌈x⌉₊ : ℝ) ≤ x + 1 := by
      calc
        (⌈x⌉₊ : ℝ) ≤ (⌊x⌋₊ + 1 : ℕ) := by exact_mod_cast hceilNat
        _ = (⌊x⌋₊ : ℝ) + 1 := by simp
        _ ≤ x + 1 := by linarith [Nat.floor_le hxnonneg]
    calc
      (⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac / (PT.tiling.P i).d⌉₊ : ℝ) ≤
          x + 1 := by simpa [x] using hceilReal
      _ ≤ κ.Kcell * (n : ℝ) ^ 200 + 1 := by linarith [hxle]
      _ ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 10) := by simpa [L] using hscope
  · intro i
    let p := PT.tiling.P i
    let ell := p.ℓ
    let d := p.d
    have hEllH : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ n := by
      have hlen := Q.profiled_valid.tiling_valid.prefix_internal_length
      have hell := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
        (Finset.mem_univ i)
      have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
        (Finset.mem_univ i)
      omega
    have hEllN : ell ≤ n := by
      dsimp [ell, p]
      exact (Nat.le_add_right _ _).trans hEllH
    have hprefixLog : (ell : ℝ) ≤ Real.log (n : ℝ) := by
      have hp := Q.prefix_bound i
      have hsqrt : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) := by
        have hsqrtOne : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
          simpa using Real.sqrt_le_sqrt hlogn
        have hsqrtSq : (Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) :=
          Real.sq_sqrt (by linarith [hlogn])
        nlinarith [hsqrtSq, hsqrtOne]
      exact hp.trans hsqrt
    have hpowEll := Lane_q_s16_geom.two_pow_le_of_log (by omega) hprefixLog
    have hpowEllNat : 2 ^ ell ≤ n := by exact_mod_cast hpowEll
    have hpowEllReal : (2 : ℝ) ^ ell ≤ (n : ℝ) := by exact_mod_cast hpowEllNat
    have hdleExp : (d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (n : ℝ))) := by
      exact Q.bin_count_bound i
    have hdleNReal : (d : ℝ) ≤ (n : ℝ) := by
      calc
        (d : ℝ) ≤ Real.exp (Real.sqrt (Real.log (n : ℝ))) := hdleExp
        _ ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr (by
          have hsqrtOne : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
            simpa using Real.sqrt_le_sqrt hlogn
          have hsqrtSq : (Real.sqrt (Real.log (n : ℝ))) ^ 2 = Real.log (n : ℝ) :=
            Real.sq_sqrt (by linarith [hlogn])
          nlinarith [hsqrtSq, hsqrtOne])
        _ = (n : ℝ) := Real.exp_log (by positivity)
    have hdleN : d ≤ n := by exact_mod_cast hdleNReal
    have hMlower : (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) ≤ (p.M : ℝ) :=
      Lane_q_s16_geom.patch_mass_lower_bound PT Q.profiled_valid n (by rfl) C0 (by rfl)
        hC0 (by simpa [n] using hhost) i hEllN
    have hparts : p.bins.parts.Nonempty := by
      by_contra hparts
      have hpartsEmpty : p.bins.parts = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hparts
      have hYempty : p.Y = ∅ := by
        rw [← p.bins.sup_parts]
        simp [hpartsEmpty]
      exact (Q.profiled_valid.tiling_valid.patch_nonempty i).2.ne_empty hYempty
    have hdPos : 0 < d := by
      by_contra hd
      have hdzero : d = 0 := by omega
      obtain ⟨B, hB⟩ := hparts
      have hcard := Q.profiled_valid.tiling_valid.bins_card i B hB
      have hdVal : (PT.tiling.P i).d = 0 := by simpa [d, p] using hdzero
      have hBzero : B.card = 0 := hcard.trans hdVal
      have hBempty : B = ∅ := Finset.card_eq_zero.mp hBzero
      have hBot : (∅ : Finset (Fin (T.S.N k))) ∈ p.bins.parts := by simpa [hBempty] using hB
      exact p.bins.bot_notMem hBot
    have hBinMulNat := Lane_q_s16_geom.bin_card_mul_bin_size PT Q.profiled_valid i
    have hBinMul : (Fintype.card (Bin PT.tiling i) : ℝ) * (d : ℝ) = (p.M : ℝ) := by
      exact_mod_cast hBinMulNat
    have hdPosReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdPos
    have hBinEq : (Fintype.card (Bin PT.tiling i) : ℝ) = (p.M : ℝ) / d := by
      calc
        (Fintype.card (Bin PT.tiling i) : ℝ) =
            (Fintype.card (Bin PT.tiling i) : ℝ) * (d : ℝ) / d :=
          (mul_div_cancel_right₀ _ hdPosReal.ne').symm
        _ = (p.M : ℝ) / d := congrArg (fun x : ℝ => x / d) hBinMul
    have hpowSplit : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - ell) * (2 : ℝ) ^ ell := by
      have hs : n - ell + ell = n := Nat.sub_add_cancel hEllN
      calc
        (2 : ℝ) ^ n = (2 : ℝ) ^ (n - ell + ell) :=
          congrArg (fun m : ℕ => (2 : ℝ) ^ m) hs.symm
        _ = (2 : ℝ) ^ (n - ell) * (2 : ℝ) ^ ell := by rw [pow_add]
    have hprod : (2 : ℝ) ^ ell * (d : ℝ) ≤ (n : ℝ) ^ 2 := by
      calc
        (2 : ℝ) ^ ell * (d : ℝ) ≤ (2 : ℝ) ^ ell * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hdleNReal (by positivity)
        _ ≤ (n : ℝ) ^ 2 := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_right hpowEllReal (Nat.cast_nonneg n)
    have hcoeff : (1 : ℝ) ≤ 6 * κ.Kcell + 2 :=
      Lane_q_s16_geom.one_le_six_mul_add_two hKpos
    have hCross : (2 : ℝ) ^ n * (d : ℝ) ≤
        (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2 := by
      rw [hpowSplit]
      calc
        (2 : ℝ) ^ (n - ell) * (2 : ℝ) ^ ell * (d : ℝ) =
            (2 : ℝ) ^ (n - ell) * ((2 : ℝ) ^ ell * (d : ℝ)) := by ring
        _ ≤
            (2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        _ ≤ (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2 := by
          calc
            (2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2 =
                1 * ((2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2) := by ring
            _ ≤ (6 * κ.Kcell + 2) * ((2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hcoeff
                (mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg (n : ℝ)))
            _ = (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) * (n : ℝ) ^ 2 := by ring
    have hratio : (2 : ℝ) ^ n / (n : ℝ) ^ 2 ≤
        (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) / d := by
      rw [div_le_div_iff₀ (by positivity) hdPosReal]
      exact hCross
    have hcomp : 2 * (Real.exp (Real.rpow (Real.log (n : ℝ)) 10) + 1) ^ 2 ≤
        (2 : ℝ) ^ n / (n : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      simpa [n] using hcomparison
    have hcoeff : 2 ≤ 6 * κ.Kcell + 2 := by
      have hnonneg : 0 ≤ 6 * κ.Kcell := mul_nonneg (by norm_num) hKpos.le
      linarith
    have hMdiv : (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) / d ≤ (p.M : ℝ) / d :=
      div_le_div_of_nonneg_right hMlower hdPosReal.le
    calc
      2 * (Real.exp (Real.rpow (Real.log (n : ℝ)) 10) + 1) ^ 2 ≤
          (2 : ℝ) ^ n / (n : ℝ) ^ 2 := hcomp
      _ ≤ (6 * κ.Kcell + 2) * (2 : ℝ) ^ (n - ell) / d := hratio
      _ ≤ (p.M : ℝ) / d := hMdiv
      _ = Fintype.card (Bin PT.tiling i) := hBinEq.symm

/-- L16.1a data: coordinate IDs, the hyperplane, and ordered syndrome classes. -/
structure SyndromeData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  Hdim : ℕ
  ids : Fin (T.S.n k) → (Fin Hdim → ZMod 2)
  H0 : Submodule (ZMod 2) (Fin Hdim → ZMod 2)
  Lsub : Submodule (ZMod 2) (Fin Hdim → ZMod 2)
  r : ℕ
  classEnum : Fin r ≃ Lsub

namespace SyndromeData

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

def syndrome (S : SyndromeData PT) (z : Pos T k) : Fin S.Hdim → ZMod 2 :=
  ∑ j, if z j = true then S.ids j else 0

noncomputable def classOf (S : SyndromeData PT) (z : Pos T k) : Option (Fin S.r) :=
  if h : ¬ IsEvenRole z ∧ S.syndrome z ∈ S.Lsub then
    some (S.classEnum.symm ⟨S.syndrome z, h.2⟩)
  else none

def internalAxes (_S : SyndromeData PT) : Finset (Fin (T.S.n k)) :=
  Finset.univ.biUnion fun i : Fin PT.tiling.m => PT.tiling.Icoord i

def suffix (S : SyndromeData PT) (j : ℕ) : Finset (Fin S.r) :=
  Finset.univ.filter fun t => S.r - j ≤ t.val

noncomputable def suffixNeighbours (S : SyndromeData PT) (v : Pos T k) (j : ℕ) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun i => ∃ t ∈ S.suffix j,
    S.classOf (flipPos v i) = some t

noncomputable def lateNeighbours (S : SyndromeData PT) (v : Pos T k) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun i => (S.classOf (flipPos v i)).isSome

end SyndromeData

/-- L16.1a (16:49–77): one consistent ID assignment and balanced class order. -/
structure SyndromeFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (S : SyndromeData PT) : Prop where
  group_size : T.S.n k ≤ 2 ^ S.Hdim ∧ 2 ^ S.Hdim < 2 * T.S.n k
  hyperplane_card : Fintype.card S.H0 = 2 ^ (S.Hdim - 1)
  ids_injective : Function.Injective S.ids
  hyperplane_in_ids : ∀ a : S.H0, ∃ i, S.ids i = a.1
  subspace_size :
    (κ.A0 * Real.log (T.S.n k : ℝ) ≤ (S.r : ℝ)) ∧
      (S.r : ℝ) < 2 * κ.A0 * Real.log (T.S.n k : ℝ)
  class_enum_card : Fintype.card S.Lsub = S.r
  late_subspace_not_hyperplane : ¬ S.Lsub ≤ S.H0
  internal_cosets_distinct : ∀ i ∈ S.internalAxes, ∀ j ∈ S.internalAxes,
    i ≠ j → S.ids i - S.ids j ∉ S.Lsub
  class_size : ∀ t : Fin S.r,
    Fintype.card {z : Pos T k // ¬ IsEvenRole z ∧
      S.syndrome z = S.classEnum t} = 2 ^ (T.S.n k - 1) / 2 ^ S.Hdim
  one_neighbour_per_class : ∀ v : Pos T k, IsEvenRole v → ∀ t : Fin S.r,
    ((Finset.univ.filter fun i : Fin (T.S.n k) =>
      S.classOf (flipPos v i) = some t).card : ℕ) ≤ 1
  suffix_neighbour_bounds : ∀ v : Pos T k, IsEvenRole v → ∀ j ≤ S.r,
    j / 2 ≤ (S.suffixNeighbours v j).card ∧
      (S.suffixNeighbours v j).card ≤ j
  total_late_neighbour_bounds : ∀ v : Pos T k, IsEvenRole v →
    S.r / 2 ≤ (S.lateNeighbours v).card ∧ (S.lateNeighbours v).card ≤ S.r
  at_most_one_internal_late_neighbour : ∀ v : Pos T k, IsEvenRole v →
    ((S.internalAxes.filter fun i => (S.classOf (flipPos v i)).isSome).card : ℕ) ≤ 1
  coset_criterion : ∀ v : Pos T k, IsEvenRole v → ∀ i : Fin (T.S.n k),
    (S.classOf (flipPos v i)).isSome ↔ S.ids i + S.syndrome v ∈ S.Lsub

/-- L16.1b data: cell maps are independent of the syndrome allocation. -/
structure CellData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  Cell : Type
  [cellFin : Fintype Cell]
  [cellDec : DecidableEq Cell]
  cellOf : Pos T k → Cell
  patchOf : Pos T k → Fin PT.tiling.m
  patchOf_leaf : ∀ b, b ∈ PT.tiling.leaf (patchOf b)
  cellPatch : Cell → Fin PT.tiling.m
  cellOf_patch : ∀ b, cellPatch (cellOf b) = patchOf b
  nslot : Cell → ℕ

instance instCellDataFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (C : CellData PT) : Fintype C.Cell := C.cellFin

instance instCellDataDecidableEq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (C : CellData PT) : DecidableEq C.Cell := C.cellDec

namespace CellData

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k}

def positions (C : CellData PT) (c : C.Cell) : Finset (Pos T k) :=
  Finset.univ.filter fun b => C.cellOf b = c

def cellsInPatch (C : CellData PT) (i : Fin PT.tiling.m) : Finset C.Cell :=
  Finset.univ.filter fun c => C.cellPatch c = i

def sameSlice (i : Fin PT.tiling.m) (b b' : Pos T k) : Prop :=
  ∀ j, j ∉ PT.tiling.Icoord i → b j = b' j

end CellData

/-- L16.1b (16:90–96): whole-slice cells and the batching count bound. -/
structure CellPartitionFacts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (C : CellData PT) : Prop where
  cells_nonempty : ∀ c, (C.positions c).Nonempty
  cell_size : ∀ c, (C.positions c).card ≤
    ⌊Real.rpow (T.S.n k : ℝ) κ.Ac⌋₊
  /-- Complete batches have at least n^Ac/3 positions; one short batch
  per color is allowed. This is the counting input, not just an upper size. -/
  short_batches : ∀ i : Fin PT.tiling.m,
    (((C.cellsInPatch i).filter fun c =>
      ((C.positions c).card : ℝ) < Real.rpow (T.S.n k : ℝ) κ.Ac / 3).card : ℝ) ≤
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)
  whole_slices : ∀ c b, C.cellOf b = c → ∀ b',
    CellData.sameSlice (C.cellPatch c) b b' → C.cellOf b' = c
  slice_separation : ∀ c b b', C.cellOf b = c → C.cellOf b' = c →
    ¬ CellData.sameSlice (C.cellPatch c) b b' →
    Real.rpow (Real.log (T.S.n k : ℝ)) 3 < (hammingDist b b' : ℝ)
  cell_count : ∀ i : Fin PT.tiling.m,
    ((C.cellsInPatch i).card : ℝ) ≤
      3 * Real.rpow (2 : ℝ) ((T.S.n k - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
        Real.rpow (T.S.n k : ℝ) κ.Ac +
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 5)
  slot_count : ∀ c,
    C.nslot c = ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac /
      (PT.tiling.P (C.cellPatch c)).d⌉₊
  slots_fit : ∀ i : Fin PT.tiling.m,
    (∑ c ∈ C.cellsInPatch i, C.nslot c) ≤ Fintype.card (Bin PT.tiling i)

/-- L16.1 assembly data: independent syndrome and cell allocations. -/
structure LowGeometryData {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) where
  syndrome : SyndromeData PT
  cells : CellData PT

def LowGeometryData.toLowGeom {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : LowGeometryData PT) : LowGeom PT :=
  { Hdim := D.syndrome.Hdim
    ids := D.syndrome.ids
    Lsub := D.syndrome.Lsub
    r := D.syndrome.r
    classEnum := D.syndrome.classEnum
    Cell := D.cells.Cell
    cellFin := D.cells.cellFin
    cellDec := D.cells.cellDec
    cellOf := D.cells.cellOf
    patchOf := D.cells.patchOf
    patchOf_leaf := D.cells.patchOf_leaf
    cellPatch := D.cells.cellPatch
    cellOf_patch := D.cells.cellOf_patch
    nslot := D.cells.nslot }

/-- L16.1c (16:98–121): patchwise permutation pools dominate iid slots on
small scopes, including after a single global slot pin. -/
abbrev CellSlot {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) :=
  Σ c : G.Cell, Fin (G.nslot c)

abbrev PoolAssignment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) := ∀ c, CellPool G c

def DependsOnCellSlots {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (S : Finset (CellSlot G)) (F : PoolAssignment G → ℝ) : Prop :=
  ∀ P Q, (∀ s ∈ S, P s.1 s.2 = Q s.1 s.2) → F P = F Q

noncomputable def poolPinEvent {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT}
    (s : CellSlot G) (D : Bin PT.tiling (G.cellPatch s.1)) :
    Finset (PoolAssignment G) :=
  Finset.univ.filter fun P => P s.1 s.2 = D

noncomputable def PoolComparison {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) : Prop :=
  ∀ (i : Fin PT.tiling.m) (hperm : (permPools G).Nonempty)
    (S : Finset (CellSlot G)),
    (∀ s ∈ S, G.cellPatch s.1 = i) →
    (S.card : ℝ) ≤ Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10) →
    2 * ((S.card : ℝ) + 1) ^ 2 ≤ Fintype.card (Bin PT.tiling i) →
    ∀ F : PoolAssignment G → ℝ, (∀ P, 0 ≤ F P) → DependsOnCellSlots S F →
      (permPoolLaw G hperm).E F ≤
        (1 + (S.card : ℝ) ^ 2 / Fintype.card (Bin PT.tiling i)) *
          (iidPoolLaw G hperm).E F ∧
      ∀ (s : CellSlot G) (D : Bin PT.tiling (G.cellPatch s.1)),
        (G.cellPatch s.1 = i) →
        (hpermPin : 0 < ∑ P ∈ poolPinEvent s D, (permPoolLaw G hperm).w P) →
        (hiidPin : 0 < ∑ P ∈ poolPinEvent s D, (iidPoolLaw G hperm).w P) →
        (FinLaw.cond (permPoolLaw G hperm) (poolPinEvent s D) hpermPin).E F ≤
          (1 + ((insert s S).card : ℝ) ^ 2 / Fintype.card (Bin PT.tiling i)) *
            (FinLaw.cond (iidPoolLaw G hperm) (poolPinEvent s D) hiidPin).E F

/-- Shared validity of the actual `LowGeom` consumed in Sections 17–18.
The witness ties all syndrome and cell facts to this exact geometry. -/
def LowGeomValid {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (G : LowGeom PT) : Prop :=
  ∃ D : LowGeometryData PT, D.toLowGeom = G ∧
    SyndromeFacts D.syndrome ∧ CellPartitionFacts hκ Q D.cells ∧
    (permPools G).Nonempty ∧ PoolComparison G

/-- L16.1: existence assembled from the syndrome, cell, and pool subnodes. -/
structure LowGeometryCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16) where
  data : LowGeometryData PT
  scale : LowModeScaleFacts hκ Q
  late_classes : SyndromeFacts data.syndrome
  cell_partition : CellPartitionFacts hκ Q data.cells
  perm_pool_nonempty : (permPools data.toLowGeom).Nonempty
  pool_comparison : PoolComparison data.toLowGeom

namespace LowGeometryCertificate

variable {κ : CConsts} {T : Stage} {k : ℕ}
variable {PT : ProfiledTiling κ T k} {hκ : κ.Admissible}
variable {K16 : ℝ} {Q : LowModeQuantFacts hκ (PT := PT) K16}

def geom (G : LowGeometryCertificate hκ Q) : LowGeom PT := G.data.toLowGeom

theorem geom_valid (G : LowGeometryCertificate hκ Q) : LowGeomValid hκ Q G.geom :=
  ⟨G.data, rfl, G.late_classes, G.cell_partition, G.perm_pool_nonempty, G.pool_comparison⟩

end LowGeometryCertificate

/-- L16.1a (16:49–77): syndrome IDs and the balanced class order. -/
theorem syndrome_data_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) :
    ∃ S : SyndromeData PT, SyndromeFacts S := by
  classical
  let n := T.S.n k
  obtain ⟨Hdim, hGroupLower, hGroupUpper⟩ :=
    Lane_q_s16_geom.exists_paired_group_dimension hScale.n_four
  have hGroupCard : Fintype.card (Fin Hdim → ZMod 2) = 2 ^ Hdim := by
    simp [Fintype.card_fun]
  have hEmbedCard : Fintype.card (Fin n) ≤ Fintype.card (Fin Hdim → ZMod 2) := by
    simpa [hGroupCard] using hGroupLower
  let idsBase : Fin n ↪ (Fin Hdim → ZMod 2) :=
    Lane_q_s16_geom.finiteEmbeddingOfCardLE hEmbedCard
  have hidsBase : Function.Injective idsBase := idsBase.injective
  sorry

/-- L16.1b (16:90–96): separated cells made from whole slices. -/
theorem cell_data_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) :
    ∃ C : CellData PT, CellPartitionFacts hκ Q C := by
  classical
  let n := T.S.n k
  let hPT := Q.profiled_valid
  let R : ℕ := ⌈Real.rpow (Real.log (n : ℝ)) 3⌉₊
  let D : ℕ := ∑ j ∈ Finset.range (R + 1), Nat.choose n j
  have hEllH (i : Fin PT.tiling.m) :
      (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ n := by
    have hlen := hPT.tiling_valid.prefix_internal_length
    have hell := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ)
      (Finset.mem_univ i)
    have hh := Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h)
      (Finset.mem_univ i)
    omega
  let SliceValid (i : Fin PT.tiling.m) (s : CubePos n) : Prop :=
    (∀ j : Fin (PT.tiling.P i).ℓ,
      s ⟨j.val, by have := j.isLt; have := hEllH i; omega⟩ =
        (PT.tiling.w i) ⟨j.val, by have := j.isLt; have := hEllH i; omega⟩) ∧
    (∀ j, j ∈ PT.tiling.Icoord i → s j = false)
  have hD : (∑ j ∈ Finset.range (R + 1), Nat.choose n j) ≤ D := by
    dsimp [D]
    exact le_rfl
  have sliceColoring := Lane_q_s16_geom.cube_hamming_coloring
    (m := n) (r := R) (d := D) hD
  let colors : CubePos n → Fin (D + 1) := Classical.choose sliceColoring
  have colorsProper {s t : CubePos n}
      (hst : s ≠ t) (hdist : hammingDist s t ≤ R) : colors s ≠ colors t :=
    (Classical.choose_spec sliceColoring) hst hdist
  let batchSize (i : Fin PT.tiling.m) : ℕ :=
    ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ / 2 ^ (PT.tiling.P i).h
  have batchSize_pos (i : Fin PT.tiling.m) : 0 < batchSize i := by
    have hs : 2 * 2 ^ (PT.tiling.P i).h ≤
        ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := by
      simpa [n] using hScale.slice_room i
    have hden : 0 < 2 ^ (PT.tiling.P i).h := Nat.pow_pos (by decide)
    have hdenle : 2 ^ (PT.tiling.P i).h ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := by
      calc
        2 ^ (PT.tiling.P i).h ≤ 2 * 2 ^ (PT.tiling.P i).h := by omega
        _ ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := hs
    dsimp [batchSize]
    exact Nat.div_pos hdenle hden
  let SliceClass (i : Fin PT.tiling.m) (c : Fin (D + 1)) : Finset (CubePos n) :=
    Finset.univ.filter fun s => SliceValid i s ∧ colors s = c
  let Key : Type := Σ i : Fin PT.tiling.m, Fin (D + 1) × ℕ
  letI : DecidableEq Key := Classical.decEq Key
  let patchOf : Pos T k → Fin PT.tiling.m := fun b =>
    Classical.choose (hPT.tiling_valid.prefix_complete b)
  have patchOf_leaf (b : Pos T k) : b ∈ PT.tiling.leaf (patchOf b) :=
    (Classical.choose_spec (hPT.tiling_valid.prefix_complete b)).1
  let sliceAt (i : Fin PT.tiling.m) (b : Pos T k)
      (_hb : b ∈ PT.tiling.leaf i) : CubePos n :=
    fun j => if j ∈ PT.tiling.Icoord i then false else b j
  have sliceAt_valid (i : Fin PT.tiling.m) (b : Pos T k)
      (hb : b ∈ PT.tiling.leaf i) : SliceValid i (sliceAt i b hb) := by
    constructor
    · intro j
      have hj : (⟨j.val, by have := j.isLt; have := hEllH i; omega⟩ : Fin n) ∉
          PT.tiling.Icoord i := by
        simp [Tiling.Icoord, topCoordinates]
        have hlen := hEllH i
        omega
      simp [sliceAt, hj]
      exact hb ⟨j.val, by have := j.isLt; have := hEllH i; omega⟩ j.isLt
    · intro j hj
      simp [sliceAt, hj]
  let keyOfAt (i : Fin PT.tiling.m) (s : CubePos n) : Key := by
    classical
    let c := colors s
    if h : s ∈ SliceClass i c then
      let r := (SliceClass i c).equivFin ⟨s, h⟩
      exact ⟨i, (c, Lane_q_s16_geom.batchStart r.1 (batchSize i))⟩
    else
      exact ⟨i, (c, 0)⟩
  let sliceOf (b : Pos T k) : CubePos n :=
    sliceAt (patchOf b) b (patchOf_leaf b)
  let keyOf (b : Pos T k) : Key := keyOfAt (patchOf b) (sliceOf b)
  let keys : Finset Key := Finset.univ.image keyOf
  let Cell : Type := {key : Key // key ∈ keys}
  letI : Fintype Cell := by classical infer_instance
  letI : DecidableEq Cell := Classical.decEq Cell
  let cellPatch : Cell → Fin PT.tiling.m := fun c => c.1.1
  let cellOf (b : Pos T k) : Cell :=
    ⟨keyOf b, Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩⟩
  let nslot (c : Cell) : ℕ :=
    ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac /
      (PT.tiling.P (cellPatch c)).d⌉₊
  have cellOf_patch (b : Pos T k) : cellPatch (cellOf b) = patchOf b := by
    dsimp [cellPatch, cellOf, keyOf, keyOfAt]
    split_ifs <;> rfl
  let C : CellData PT := @CellData.mk κ T k PT Cell
    (inferInstance : Fintype Cell) (Classical.decEq Cell)
    cellOf patchOf patchOf_leaf cellPatch cellOf_patch nslot
  have hCells_nonempty : ∀ c : Cell, (CellData.positions C c).Nonempty := by
    intro c₀
    rcases Finset.mem_image.mp c₀.2 with ⟨b, hb, hkey⟩
    refine ⟨b, ?_⟩
    have hEq : C.cellOf b = c₀ := by
      change cellOf b = c₀
      apply Subtype.ext
      exact hkey
    simpa [CellData.positions] using hEq
  have hSlotCount (c : Cell) :
      C.nslot c = ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac /
        (PT.tiling.P (C.cellPatch c)).d⌉₊ := rfl

  have hWholeSlices : ∀ c b, C.cellOf b = c → ∀ b',
      CellData.sameSlice (C.cellPatch c) b b' → C.cellOf b' = c := by
    intro c b hbc b' hsame
    let i := patchOf b
    have hpc : C.cellPatch c = i := by
      calc
        C.cellPatch c = C.cellPatch (C.cellOf b) := by rw [hbc]
        _ = patchOf b := C.cellOf_patch b
    have hsame' : CellData.sameSlice i b b' := by
      simpa [i, hpc] using hsame
    have hb'leaf : b' ∈ PT.tiling.leaf i := by
      intro j hj
      have hnot : j ∉ PT.tiling.Icoord i := by
        simp [Tiling.Icoord, topCoordinates]
        have hlen := hEllH i
        omega
      have hbits := hsame' j hnot
      rw [← hbits]
      exact patchOf_leaf b j hj
    have hpatch' : patchOf b' = i := by
      rcases hPT.tiling_valid.prefix_complete b' with ⟨j, hj, hjuniq⟩
      exact (hjuniq (patchOf b') (patchOf_leaf b')).trans
        (hjuniq i hb'leaf).symm
    have hpc' : patchOf b' = patchOf b := by
      simpa [i] using hpatch'
    have hslice : sliceOf b = sliceOf b' := by
      funext j
      dsimp [sliceOf, sliceAt]
      rw [hpc']
      by_cases hj : j ∈ PT.tiling.Icoord i
      · have hj' : j ∈ PT.tiling.Icoord (patchOf b) := by simpa [i] using hj
        simp [hj']
      · have hj' : j ∉ PT.tiling.Icoord (patchOf b) := by simpa [i] using hj
        simp [hj', hsame' j hj]
    have hkey : keyOf b = keyOf b' := by
      dsimp [keyOf]
      rw [hpc', hslice]
    have hcell : cellOf b' = cellOf b := by
      apply Subtype.ext
      exact hkey.symm
    exact hcell.trans hbc

  have hSliceSeparation : ∀ c b b', C.cellOf b = c → C.cellOf b' = c →
      ¬ CellData.sameSlice (C.cellPatch c) b b' →
      Real.rpow (Real.log (n : ℝ)) 3 < (hammingDist b b' : ℝ) := by
    intro c b b' hbc hbc' hnot
    let i := C.cellPatch c
    have hp1 : patchOf b = i := by
      dsimp [i]
      calc
        patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
        _ = C.cellPatch c := congrArg C.cellPatch hbc
    have hp2 : patchOf b' = i := by
      dsimp [i]
      calc
        patchOf b' = C.cellPatch (C.cellOf b') := (C.cellOf_patch b').symm
        _ = C.cellPatch c := congrArg C.cellPatch hbc'
    have hslices_ne : sliceOf b ≠ sliceOf b' := by
      intro hslice
      apply hnot
      intro j hj
      have h1 : sliceOf b j = b j := by
        simp [sliceOf, sliceAt, hp1, i, hj]
      have h2 : sliceOf b' j = b' j := by
        simp [sliceOf, sliceAt, hp2, i, hj]
      rw [← h1, hslice, h2]
    have hkey : keyOf b = keyOf b' := by
      have hcell : C.cellOf b = C.cellOf b' := hbc.trans hbc'.symm
      exact congrArg Subtype.val hcell
    have hk1 : (keyOf b).2.1 = colors (sliceOf b) := by
      dsimp [keyOf, keyOfAt]
      split_ifs <;> rfl
    have hk2 : (keyOf b').2.1 = colors (sliceOf b') := by
      dsimp [keyOf, keyOfAt]
      split_ifs <;> rfl
    have hcolors : colors (sliceOf b) = colors (sliceOf b') := by
      have hckey := congrArg (fun q : Key => q.2.1) hkey
      exact hk1.symm.trans (hckey.trans hk2)
    have hdistSlice : R < hammingDist (sliceOf b) (sliceOf b') := by
      by_contra hle
      have hle' : hammingDist (sliceOf b) (sliceOf b') ≤ R := Nat.le_of_not_gt hle
      exact (colorsProper hslices_ne hle') hcolors
    have hdistSub : hammingDist (sliceOf b) (sliceOf b') ≤ hammingDist b b' := by
      classical
      change (Finset.univ.filter (fun j : Fin n => sliceOf b j ≠ sliceOf b' j)).card ≤ _
      apply Finset.card_le_card
      intro j hj
      have hdiff := (Finset.mem_filter.mp hj).2
      have hjnot : j ∉ PT.tiling.Icoord i := by
        intro hjmem
        have h1 : sliceOf b j = false := by
          simp [sliceOf, sliceAt, hp1, i, hjmem]
        have h2 : sliceOf b' j = false := by
          simp [sliceOf, sliceAt, hp2, i, hjmem]
        rw [h1, h2] at hdiff
        exact hdiff rfl
      have h1 : sliceOf b j = b j := by
        simp [sliceOf, sliceAt, hp1, i, hjnot]
      have h2 : sliceOf b' j = b' j := by
        simp [sliceOf, sliceAt, hp2, i, hjnot]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [h1, h2] using hdiff⟩
    have hRle : Real.rpow (Real.log (n : ℝ)) 3 ≤ (R : ℝ) := by
      dsimp [R]
      exact Nat.le_ceil _
    have hdistReal : (R : ℝ) < (hammingDist (sliceOf b) (sliceOf b') : ℝ) := by
      exact_mod_cast hdistSlice
    have hsubReal : (hammingDist (sliceOf b) (sliceOf b') : ℝ) ≤
        (hammingDist b b' : ℝ) := by
      exact_mod_cast hdistSub
    calc
      Real.rpow (Real.log (n : ℝ)) 3 ≤ (R : ℝ) := hRle
      _ < (hammingDist (sliceOf b) (sliceOf b') : ℝ) := hdistReal
      _ ≤ (hammingDist b b' : ℝ) := hsubReal

  let innerAt (i : Fin PT.tiling.m) (b : Pos T k) :
      CubePos (PT.tiling.P i).h := fun j =>
    b ⟨n - (PT.tiling.P i).h + j.val, by
      have hj := j.isLt
      have hlen := hEllH i
      omega⟩
  let rankAt (i : Fin PT.tiling.m) (col : Fin (D + 1))
      (b : Pos T k) : ℕ := by
    classical
    if h : SliceValid i (sliceOf b) ∧ colors (sliceOf b) = col then
      have hmem : sliceOf b ∈ SliceClass i col := by
        simp [SliceClass, h]
      exact ((SliceClass i col).equivFin ⟨sliceOf b, hmem⟩).val
    else
      exact 0
  have hCellSize : ∀ c : Cell,
      (C.positions c).card ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := by
    intro c
    let i := C.cellPatch c
    let q := batchSize i
    have hpatchOfCell (b : Pos T k) (hb : b ∈ C.positions c) : patchOf b = i := by
      have hcell : C.cellOf b = c := (Finset.mem_filter.mp hb).2
      dsimp [i]
      calc
        patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
        _ = C.cellPatch c := congrArg C.cellPatch hcell
    have hRankBatch (b : Pos T k) (hb : b ∈ C.positions c) :
        Lane_q_s16_geom.batchStart (rankAt i (colors (sliceOf b)) b) q = c.1.2.2 := by
      let hp := hpatchOfCell b hb
      let col := colors (sliceOf b)
      have hvalid : SliceValid i (sliceOf b) := by
        simpa [sliceOf, hp] using sliceAt_valid (patchOf b) b (patchOf_leaf b)
      have hmem : sliceOf b ∈ SliceClass i col := by
        simp [SliceClass, col, hvalid]
      let r := (SliceClass i col).equivFin ⟨sliceOf b, hmem⟩
      have hrank : rankAt i col b = r.val := by
        simp [rankAt, col, hvalid, hmem, r]
      have hkey : keyOf b = c.1 := by
        have hcell : cellOf b = c := (Finset.mem_filter.mp hb).2
        simpa [cellOf] using congrArg Subtype.val hcell
      have hstart : (keyOf b).2.2 = c.1.2.2 := congrArg (fun z : Key => z.2.2) hkey
      calc
        Lane_q_s16_geom.batchStart (rankAt i col b) q =
            Lane_q_s16_geom.batchStart r.val (batchSize i) := by
              simp [hrank, q]
        _ = (keyOf b).2.2 := by
          dsimp [keyOf, keyOfAt]
          rw [hp]
          simp [col, hmem, r]
        _ = c.1.2.2 := hstart
    let f : {b : Pos T k // b ∈ C.positions c} → Fin q × CubePos (PT.tiling.P i).h :=
      fun x => ⟨⟨rankAt i (colors (sliceOf x.1)) x.1 % q,
        Nat.mod_lt _ (batchSize_pos i)⟩, innerAt i x.1⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply funext
      intro j
      let b := x.1
      let b' := y.1
      have hp1 := hpatchOfCell b x.2
      have hp2 := hpatchOfCell b' y.2
      have hmod : rankAt i (colors (sliceOf b)) b % q =
          rankAt i (colors (sliceOf b')) b' % q :=
        congrArg (fun z : Fin q × CubePos (PT.tiling.P i).h => z.1.val) hxy
      have hinner : innerAt i b = innerAt i b' := congrArg Prod.snd hxy
      have hstart : Lane_q_s16_geom.batchStart
          (rankAt i (colors (sliceOf b)) b) q =
          Lane_q_s16_geom.batchStart (rankAt i (colors (sliceOf b')) b') q := by
        rw [hRankBatch b x.2, hRankBatch b' y.2]
      have hmul : rankAt i (colors (sliceOf b)) b / q * q =
          rankAt i (colors (sliceOf b')) b' / q * q := by
        simpa [Lane_q_s16_geom.batchStart] using hstart
      have hqpos : 0 < q := by dsimp [q]; exact batchSize_pos i
      have hdiv : rankAt i (colors (sliceOf b)) b / q =
          rankAt i (colors (sliceOf b')) b' / q :=
        Nat.mul_right_cancel hqpos hmul
      have hrank := Lane_q_s16_geom.rank_eq_of_same_batch hdiv hmod
      have hkey : keyOf b = keyOf b' := by
        have hcell₁ : cellOf b = c := (Finset.mem_filter.mp x.2).2
        have hcell₂ : cellOf b' = c := (Finset.mem_filter.mp y.2).2
        have hcell : cellOf b = cellOf b' := hcell₁.trans hcell₂.symm
        simpa [cellOf] using congrArg Subtype.val hcell
      have hk1 : (keyOf b).2.1 = colors (sliceOf b) := by
        dsimp [keyOf, keyOfAt]
        split_ifs <;> rfl
      have hk2 : (keyOf b').2.1 = colors (sliceOf b') := by
        dsimp [keyOf, keyOfAt]
        split_ifs <;> rfl
      have hcolors : colors (sliceOf b) = colors (sliceOf b') := by
        exact hk1.symm.trans
          ((congrArg (fun z : Key => z.2.1) hkey).trans hk2)
      have hv1 : SliceValid i (sliceOf b) := by
        simpa [sliceOf, hp1] using sliceAt_valid (patchOf b) b (patchOf_leaf b)
      have hv2 : SliceValid i (sliceOf b') := by
        simpa [sliceOf, hp2] using sliceAt_valid (patchOf b') b' (patchOf_leaf b')
      have hm1 : sliceOf b ∈ SliceClass i (colors (sliceOf b)) := by
        simp [SliceClass, hv1]
      have hm2 : sliceOf b' ∈ SliceClass i (colors (sliceOf b)) := by
        simp [SliceClass, hv2, hcolors]
      have hslice : sliceOf b = sliceOf b' := by
        let col := colors (sliceOf b)
        have hrank' : rankAt i col b = rankAt i col b' := by
          simpa [col, hcolors] using hrank
        have hval1 : rankAt i col b =
            ((SliceClass i (colors (sliceOf b))).equivFin ⟨sliceOf b, hm1⟩).val := by
          simp [rankAt, col, hv1, hm1]
        have hval2 : rankAt i col b' =
            ((SliceClass i col).equivFin ⟨sliceOf b', hm2⟩).val := by
          simp [rankAt, col, hv2, hcolors.symm, hm2]
        have hfin : (SliceClass i (colors (sliceOf b))).equivFin
              ⟨sliceOf b, hm1⟩ =
            (SliceClass i (colors (sliceOf b))).equivFin ⟨sliceOf b', hm2⟩ := by
          apply Fin.ext
          rw [← hval1, ← hval2]
          exact hrank'
        exact congrArg Subtype.val
          ((SliceClass i (colors (sliceOf b))).equivFin.injective hfin)
      change b j = b' j
      by_cases hj : j ∈ PT.tiling.Icoord i
      · have htop : n - (PT.tiling.P i).h ≤ j.val := by
          simpa [Tiling.Icoord, topCoordinates] using hj
        let t : Fin (PT.tiling.P i).h :=
          ⟨j.val - (n - (PT.tiling.P i).h), by
            have hjlt := j.isLt
            omega⟩
        have hcoord : (⟨n - (PT.tiling.P i).h + t.val,
            by have ht := t.isLt; have hlen := hEllH i; omega⟩ : Fin n) = j := by
          apply Fin.ext
          dsimp [t]
          omega
        have hbit := congrFun hinner t
        change b ⟨n - (PT.tiling.P i).h + t.val, by
          have ht := t.isLt; have hlen := hEllH i; omega⟩ =
          b' ⟨n - (PT.tiling.P i).h + t.val, by
            have ht := t.isLt; have hlen := hEllH i; omega⟩ at hbit
        rw [← hcoord]
        exact hbit
      · have h1 : sliceOf b j = b j := by simp [sliceOf, sliceAt, hp1, i, hj]
        have h2 : sliceOf b' j = b' j := by simp [sliceOf, sliceAt, hp2, i, hj]
        rw [← h1, hslice, h2]
    have hcard : (C.positions c).card ≤ Fintype.card (Fin q × CubePos (PT.tiling.P i).h) := by
      have hsubtype : Fintype.card {b : Pos T k // b ∈ C.positions c} =
          (C.positions c).card := by
        rw [Fintype.card_subtype]
        simp
      rw [← hsubtype]
      exact Fintype.card_le_of_injective f hf
    calc
      (C.positions c).card ≤ Fintype.card (Fin q × CubePos (PT.tiling.P i).h) := hcard
      _ = q * 2 ^ (PT.tiling.P i).h := by simp
      _ = (⌊Real.rpow (n : ℝ) κ.Ac⌋₊ / 2 ^ (PT.tiling.P i).h) *
          2 ^ (PT.tiling.P i).h := by rfl
      _ ≤ ⌊Real.rpow (n : ℝ) κ.Ac⌋₊ := Nat.div_mul_le_self _ _

  have hCellCount : ∀ i : Fin PT.tiling.m,
      ((C.cellsInPatch i).card : ℝ) ≤
        3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
          Real.rpow (n : ℝ) κ.Ac + Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
    intro i
    classical
    let cells := C.cellsInPatch i
    let q := batchSize i
    have hq : 0 < q := batchSize_pos i
    let validSlices : Finset (CubePos n) := Finset.univ.filter (SliceValid i)
    have hClassEq (col : Fin (D + 1)) :
        SliceClass i col = validSlices.filter (fun s => colors s = col) := by
      ext s
      simp [SliceClass, validSlices, and_assoc]
    have hsumClasses :
        (∑ col : Fin (D + 1), (SliceClass i col).card) = validSlices.card := by
      simpa [hClassEq] using
        (Finset.sum_card_fiberwise_eq_card_filter
          (s := validSlices) (t := (Finset.univ : Finset (Fin (D + 1))))
          (g := colors))
    have hEllH' : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ n := hEllH i
    have hValidCard : validSlices.card ≤
        2 ^ (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) := by
      let freeAt : Fin (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) → Fin n :=
        fun j => ⟨(PT.tiling.P i).ℓ + j.val, by
          have hj := j.isLt
          omega⟩
      let encode : {s : CubePos n // SliceValid i s} →
          CubePos (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) :=
        fun s j => s.1 (freeAt j)
      have hEncode : Function.Injective encode := by
        intro x y hxy
        apply Subtype.ext
        funext a
        by_cases hprefix : a.val < (PT.tiling.P i).ℓ
        · let p : Fin (PT.tiling.P i).ℓ := ⟨a.val, hprefix⟩
          have hidx :
              (⟨p.val, by have hp := p.isLt; omega⟩ : Fin n) = a := by
            apply Fin.ext
            rfl
          rw [← hidx]
          rw [x.2.1 p, y.2.1 p]
        · by_cases htop : n - (PT.tiling.P i).h ≤ a.val
          · have hmem : a ∈ PT.tiling.Icoord i := by
              simpa [Tiling.Icoord, topCoordinates] using htop
            rw [x.2.2 a hmem, y.2.2 a hmem]
          · let j : Fin (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) :=
              ⟨a.val - (PT.tiling.P i).ℓ, by omega⟩
            have hfree : freeAt j = a := by
              apply Fin.ext
              simp [freeAt, j]
              omega
            have h := congrFun hxy j
            change x.1 (freeAt j) = y.1 (freeAt j) at h
            simpa [hfree] using h
      have hsub : Fintype.card {s : CubePos n // SliceValid i s} ≤
          Fintype.card (CubePos (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h)) :=
        Fintype.card_le_of_injective encode hEncode
      have hcard : validSlices.card =
          Fintype.card {s : CubePos n // SliceValid i s} := by
        rw [Fintype.card_subtype]
      rw [hcard]
      calc
        Fintype.card {s : CubePos n // SliceValid i s} ≤
            Fintype.card (CubePos (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h)) := hsub
        _ = 2 ^ (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) := by
          simp [CubePos, Fintype.card_fun]
    let Starts : Fin (D + 1) → Type := fun col =>
      {r : Fin (SliceClass i col).card // r.val % q = 0}
    have hstartBound (col : Fin (D + 1)) :
        Fintype.card (Starts col) ≤ (SliceClass i col).card / q + 1 := by
      exact Lane_q_s16_geom.card_rank_starts_le (SliceClass i col).card q
    let toStarts : {c : Cell // c ∈ cells} → Σ col, Starts col := fun x => by
      let c := x.1
      let b : Pos T k := Classical.choose (hCells_nonempty c)
      have hb : b ∈ C.positions c := Classical.choose_spec (hCells_nonempty c)
      have hcell : C.cellOf b = c := (Finset.mem_filter.mp hb).2
      have hkey : keyOf b = c.1 := by
        change cellOf b = c at hcell
        exact congrArg Subtype.val hcell
      have hpatchC : c.1.1 = i := by
        change C.cellPatch c = i
        exact (Finset.mem_filter.mp x.2).2
      have hpatch : patchOf b = i := by
        calc
          patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
          _ = C.cellPatch c := congrArg C.cellPatch hcell
          _ = i := hpatchC
      have hvalid : SliceValid i (sliceOf b) := by
        simpa [sliceOf, hpatch] using
          sliceAt_valid (patchOf b) b (patchOf_leaf b)
      have hkcolor : (keyOf b).2.1 = colors (sliceOf b) := by
        dsimp [keyOf, keyOfAt]
        split_ifs <;> rfl
      have hcolor : colors (sliceOf b) = c.1.2.1 := by
        exact hkcolor.symm.trans (congrArg (fun z : Key => z.2.1) hkey)
      have hmem : sliceOf b ∈ SliceClass i c.1.2.1 := by
        simp [SliceClass, hvalid, hcolor]
      let r := (SliceClass i c.1.2.1).equivFin ⟨sliceOf b, hmem⟩
      have hstart : c.1.2.2 = Lane_q_s16_geom.batchStart r.val q := by
        calc
          c.1.2.2 = (keyOf b).2.2 := (congrArg (fun z : Key => z.2.2) hkey).symm
          _ = Lane_q_s16_geom.batchStart r.val q := by
            dsimp [keyOf, keyOfAt]
            rw [hpatch]
            rw [hcolor]
            simp [r, hmem, q]
      have hlt : c.1.2.2 < (SliceClass i c.1.2.1).card := by
        rw [hstart]
        exact (Lane_q_s16_geom.batchStart_le_rank r.val q).trans_lt r.isLt
      have hmod : c.1.2.2 % q = 0 := by
        rw [hstart]
        exact Lane_q_s16_geom.batchStart_mod r.val q
      exact ⟨c.1.2.1, ⟨⟨c.1.2.2, hlt⟩, hmod⟩⟩
    have hInjective : Function.Injective toStarts := by
      intro x y hxy
      have hpatchX : x.1.1.1 = i := by
        change C.cellPatch x.1 = i
        exact (Finset.mem_filter.mp x.2).2
      have hpatchY : y.1.1.1 = i := by
        change C.cellPatch y.1 = i
        exact (Finset.mem_filter.mp y.2).2
      have hcolor : x.1.1.2.1 = y.1.1.2.1 := congrArg Sigma.fst hxy
      have hstart : x.1.1.2.2 = y.1.1.2.2 :=
        congrArg (fun z : Σ col, Starts col => z.2.1.val) hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Sigma.ext
      · exact hpatchX.trans hpatchY.symm
      · exact heq_of_eq (Prod.ext hcolor hstart)
    have hcardCells : cells.card ≤
        ∑ col : Fin (D + 1), Fintype.card (Starts col) := by
      have hsubcard : Fintype.card {c : Cell // c ∈ cells} = cells.card := by
        rw [Fintype.card_subtype]
        simp
      calc
        cells.card = Fintype.card {c : Cell // c ∈ cells} := hsubcard.symm
        _ ≤ Fintype.card (Σ col, Starts col) := Fintype.card_le_of_injective toStarts hInjective
        _ = ∑ col : Fin (D + 1), Fintype.card (Starts col) := by
          simp [Fintype.card_sigma]
    have hcountNat : cells.card ≤
        ∑ col : Fin (D + 1), ((SliceClass i col).card / q + 1) := by
      calc
        cells.card ≤ ∑ col : Fin (D + 1), Fintype.card (Starts col) := hcardCells
        _ ≤ ∑ col : Fin (D + 1), ((SliceClass i col).card / q + 1) := by
          apply Finset.sum_le_sum
          intro col hcol
          exact hstartBound col
    have hsumDiv :
        (∑ col : Fin (D + 1), (((SliceClass i col).card / q : ℕ) : ℝ)) ≤
          (validSlices.card : ℝ) / (q : ℝ) := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      calc
        (∑ col : Fin (D + 1), (((SliceClass i col).card / q : ℕ) : ℝ)) ≤
            ∑ col : Fin (D + 1),
              ((SliceClass i col).card : ℝ) / (q : ℝ) := by
          apply Finset.sum_le_sum
          intro col hcol
          apply (le_div_iff₀ hqR).2
          exact_mod_cast (Nat.div_mul_le_self (SliceClass i col).card q)
        _ = (∑ col : Fin (D + 1), (SliceClass i col).card : ℝ) / (q : ℝ) := by
          rw [Finset.sum_div]
        _ = ((∑ col : Fin (D + 1), (SliceClass i col).card : ℕ) : ℝ) / (q : ℝ) := by
          rw [Nat.cast_sum]
        _ = (validSlices.card : ℝ) / (q : ℝ) := by rw [hsumClasses]
    have hcountReal : (cells.card : ℝ) ≤
        (validSlices.card : ℝ) / (q : ℝ) + (D + 1 : ℝ) := by
      have hcast : (cells.card : ℝ) ≤
          ((∑ col : Fin (D + 1), ((SliceClass i col).card / q + 1 : ℕ)) : ℝ) := by
        exact_mod_cast hcountNat
      simp only [Nat.cast_add, Nat.cast_one] at hcast
      calc
        (cells.card : ℝ) ≤
            ∑ col : Fin (D + 1),
              (((SliceClass i col).card / q : ℕ) : ℝ) + (D + 1 : ℝ) := by
                simpa [Finset.sum_add_distrib] using hcast
        _ ≤ (validSlices.card : ℝ) / (q : ℝ) + (D + 1 : ℝ) := by
          gcongr
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by
        dsimp [n]
        exact lt_of_lt_of_le (by norm_num) hScale.n_four
      exact_mod_cast this
    have hpow : 0 < Real.rpow (n : ℝ) κ.Ac := Real.rpow_pos_of_pos hn _
    let F : ℕ := ⌊Real.rpow (n : ℝ) κ.Ac⌋₊
    let d : ℕ := 2 ^ (PT.tiling.P i).h
    have hd : 0 < d := by dsimp [d]; exact Nat.pow_pos (by decide)
    have hF : 2 * d ≤ F := by
      dsimp [F, d, n]
      simpa using hScale.slice_room i
    have hqEq : q = F / d := by rfl
    have hqTwo : 2 ≤ q := by
      rw [hqEq]
      exact (Nat.le_div_iff_mul_le hd).2 (by nlinarith)
    have hrem : F % d < d := Nat.mod_lt _ hd
    have hdecomp : F = F % d + d * (F / d) := (Nat.mod_add_div F d).symm
    have hFlt : F < 2 * (q * d) := by
      rw [hqEq]
      nlinarith [hdecomp, hrem, hqTwo]
    have hRealX : Real.rpow (n : ℝ) κ.Ac ≤ 3 * (q : ℝ) * (d : ℝ) := by
      have hfloor : Real.rpow (n : ℝ) κ.Ac < (F : ℝ) + 1 := by
        dsimp [F]
        exact Nat.lt_floor_add_one (Real.rpow (n : ℝ) κ.Ac)
      have hFcast : (F : ℝ) < 2 * (q : ℝ) * (d : ℝ) := by
        have hFltCast : (F : ℝ) < 2 * ((q : ℝ) * (d : ℝ)) := by
          exact_mod_cast hFlt
        simpa [mul_assoc] using hFltCast
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqTwo
      have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
      have hqd : (1 : ℝ) ≤ (q : ℝ) * (d : ℝ) := by nlinarith
      nlinarith
    have hDivBound :
        (validSlices.card : ℝ) / (q : ℝ) ≤
          3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
            Real.rpow (n : ℝ) κ.Ac := by
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hvalidR : (validSlices.card : ℝ) ≤
          Real.rpow (2 : ℝ)
            ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) := by
        have hpowNat (m : ℕ) : Real.rpow (2 : ℝ) (m : ℝ) = (2 : ℝ) ^ m :=
          Real.rpow_natCast (2 : ℝ) m
        rw [hpowNat]
        exact_mod_cast hValidCard
      have hexp : (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) +
          (PT.tiling.P i).h = n - (PT.tiling.P i).ℓ := by omega
      have hpow2 :
          Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) *
              (2 : ℝ) ^ (PT.tiling.P i).h =
            Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) := by
        have hpowNat (m : ℕ) : Real.rpow (2 : ℝ) (m : ℝ) = (2 : ℝ) ^ m :=
          Real.rpow_natCast (2 : ℝ) m
        rw [hpowNat, hpowNat]
        calc
          (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) *
              (2 : ℝ) ^ (PT.tiling.P i).h =
              (2 : ℝ) ^ ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h) +
                (PT.tiling.P i).h) := by rw [← pow_add]
          _ = (2 : ℝ) ^ (n - (PT.tiling.P i).ℓ) := by rw [hexp]
      have hrecip : (1 : ℝ) / (q : ℝ) ≤
          3 * (2 : ℝ) ^ (PT.tiling.P i).h / Real.rpow (n : ℝ) κ.Ac := by
        have hmul : Real.rpow (n : ℝ) κ.Ac ≤
            3 * (q : ℝ) * (2 : ℝ) ^ (PT.tiling.P i).h := by
          simpa [d] using hRealX
        rw [div_le_div_iff₀ hqR hpow]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
      calc
        (validSlices.card : ℝ) / (q : ℝ) ≤
            Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) / (q : ℝ) :=
                (div_le_div_of_nonneg_right hvalidR hqR.le)
        _ = Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) * (1 / (q : ℝ)) := by ring
        _ ≤ Real.rpow (2 : ℝ)
              ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) *
              (3 * (2 : ℝ) ^ (PT.tiling.P i).h / Real.rpow (n : ℝ) κ.Ac) := by
                exact mul_le_mul_of_nonneg_left hrecip
                  (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        _ = 3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
              Real.rpow (n : ℝ) κ.Ac := by
                calc
                  _ = 3 *
                      (Real.rpow (2 : ℝ)
                        ((n - (PT.tiling.P i).ℓ - (PT.tiling.P i).h : ℕ) : ℝ) *
                        (2 : ℝ) ^ (PT.tiling.P i).h) /
                        Real.rpow (n : ℝ) κ.Ac := by ring
                  _ = _ := by rw [hpow2]
    have hColorCast : (D + 1 : ℝ) ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
      calc
        (D + 1 : ℝ) = 1 +
            ∑ j ∈ Finset.range (R + 1), (Nat.choose n j : ℝ) := by
              simp [D, Nat.cast_sum, add_comm]
        _ ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
              simpa [R, n] using hScale.coloring_room
    calc
      ((C.cellsInPatch i).card : ℝ) = (cells.card : ℝ) := rfl
      _ ≤ (validSlices.card : ℝ) / (q : ℝ) + (D + 1 : ℝ) := hcountReal
      _ ≤ 3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
            Real.rpow (n : ℝ) κ.Ac + Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
              exact add_le_add hDivBound hColorCast

  have hBatchRoom (i : Fin PT.tiling.m) :
      Real.rpow (n : ℝ) κ.Ac ≤
        3 * (batchSize i : ℝ) * (2 : ℝ) ^ (PT.tiling.P i).h := by
    have hn : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by
        dsimp [n]
        exact lt_of_lt_of_le (by norm_num) hScale.n_four
      exact_mod_cast this
    let F : ℕ := ⌊Real.rpow (n : ℝ) κ.Ac⌋₊
    let d : ℕ := 2 ^ (PT.tiling.P i).h
    have hd : 0 < d := by dsimp [d]; exact Nat.pow_pos (by decide)
    have hF : 2 * d ≤ F := by
      dsimp [F, d, n]
      simpa using hScale.slice_room i
    have hq : batchSize i = F / d := by rfl
    have hqTwo : 2 ≤ batchSize i := by
      rw [hq]
      exact (Nat.le_div_iff_mul_le hd).2 (by nlinarith)
    have hrem : F % d < d := Nat.mod_lt _ hd
    have hdecomp : F = F % d + d * (F / d) := (Nat.mod_add_div F d).symm
    have hFlt : F < 2 * (batchSize i * d) := by
      rw [hq]
      nlinarith [hdecomp, hrem, hqTwo]
    have hfloor : Real.rpow (n : ℝ) κ.Ac < (F : ℝ) + 1 := by
      dsimp [F]
      exact Nat.lt_floor_add_one (Real.rpow (n : ℝ) κ.Ac)
    have hFcast : (F : ℝ) < 2 * (batchSize i : ℝ) * (d : ℝ) := by
      have hFltCast : (F : ℝ) < 2 * ((batchSize i : ℝ) * (d : ℝ)) := by
        exact_mod_cast hFlt
      simpa [mul_assoc] using hFltCast
    have hqR : (0 : ℝ) < (batchSize i : ℝ) := by
      exact_mod_cast (batchSize_pos i)
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hqR2 : (2 : ℝ) ≤ (batchSize i : ℝ) := by exact_mod_cast hqTwo
    have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))
    have hqd : (1 : ℝ) ≤ (batchSize i : ℝ) * (d : ℝ) := by nlinarith
    have hReal : Real.rpow (n : ℝ) κ.Ac ≤
        3 * (batchSize i : ℝ) * (d : ℝ) := by nlinarith
    simpa [d] using hReal

  have hCellRank (i : Fin PT.tiling.m) (c : Cell)
      (hc : C.cellPatch c = i) :
      ∃ s : CubePos n, ∃ hs : s ∈ SliceClass i c.1.2.1,
        c.1.2.2 = Lane_q_s16_geom.batchStart
          ((SliceClass i c.1.2.1).equivFin ⟨s, hs⟩).val (batchSize i) := by
    obtain ⟨b, hb⟩ := hCells_nonempty c
    have hcell : C.cellOf b = c := (Finset.mem_filter.mp hb).2
    have hkey : keyOf b = c.1 := by
      change cellOf b = c at hcell
      exact congrArg Subtype.val hcell
    have hpatch : patchOf b = i := by
      calc
        patchOf b = C.cellPatch (C.cellOf b) := (C.cellOf_patch b).symm
        _ = C.cellPatch c := congrArg C.cellPatch hcell
        _ = i := hc
    have hvalid : SliceValid i (sliceOf b) := by
      simpa [sliceOf, hpatch] using
        sliceAt_valid (patchOf b) b (patchOf_leaf b)
    have hkcolor : (keyOf b).2.1 = colors (sliceOf b) := by
      dsimp [keyOf, keyOfAt]
      split_ifs <;> rfl
    have hcolor : colors (sliceOf b) = c.1.2.1 := by
      exact hkcolor.symm.trans (congrArg (fun z : Key => z.2.1) hkey)
    have hmem : sliceOf b ∈ SliceClass i c.1.2.1 := by
      simp [SliceClass, hvalid, hcolor]
    let r := (SliceClass i c.1.2.1).equivFin ⟨sliceOf b, hmem⟩
    have hstart : c.1.2.2 = Lane_q_s16_geom.batchStart r.val (batchSize i) := by
      calc
        c.1.2.2 = (keyOf b).2.2 := (congrArg (fun z : Key => z.2.2) hkey).symm
        _ = Lane_q_s16_geom.batchStart r.val (batchSize i) := by
          dsimp [keyOf, keyOfAt]
          rw [hpatch]
          rw [hcolor]
          simp [r, hmem]
    exact ⟨sliceOf b, hmem, hstart⟩

  have hSlotsFit : ∀ i : Fin PT.tiling.m,
      (∑ c ∈ C.cellsInPatch i, C.nslot c) ≤ Fintype.card (Bin PT.tiling i) := by
    intro i
    let cells := C.cellsInPatch i
    let q : ℕ := ⌈κ.Kcell * Real.rpow (n : ℝ) κ.Ac / (PT.tiling.P i).d⌉₊
    have hslots : ∀ c ∈ cells, C.nslot c = q := by
      intro c hc
      have hpatch : C.cellPatch c = i := (Finset.mem_filter.mp hc).2
      rw [hSlotCount c]
      simp [q, hpatch]
    have hsum : (∑ c ∈ cells, C.nslot c) = cells.card * q := by
      calc
        (∑ c ∈ cells, C.nslot c) = ∑ c ∈ cells, q := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hslots c hc
        _ = cells.card * q := by simp
    have hcount := hCellCount i
    have hprod : (cells.card : ℝ) * (q : ℝ) ≤
        (3 * Real.rpow (2 : ℝ) ((n - (PT.tiling.P i).ℓ : ℕ) : ℝ) /
          Real.rpow (n : ℝ) κ.Ac + Real.exp (Real.rpow (Real.log (n : ℝ)) 5)) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg q)
    have hcap := hScale.patch_capacity i
    have htotal : ((cells.card * q : ℕ) : ℝ) ≤ Fintype.card (Bin PT.tiling i) := by
      rw [Nat.cast_mul]
      dsimp [q] at hprod hcap ⊢
      exact hprod.trans hcap
    rw [hsum]
    exact_mod_cast htotal

  refine ⟨C, ?_⟩
  refine ⟨hCells_nonempty, hCellSize, ?_, hWholeSlices, ?_, hCellCount, hSlotCount, hSlotsFit⟩
  · intro i
    classical
    let cells := C.cellsInPatch i
    let q := batchSize i
    let small := cells.filter fun c =>
      ((C.positions c).card : ℝ) < Real.rpow (n : ℝ) κ.Ac / 3
    have hq : 0 < q := batchSize_pos i
    let extendAt (s : CubePos n) (u : CubePos (PT.tiling.P i).h) : Pos T k :=
      fun j => if hj : j ∈ PT.tiling.Icoord i then
        u ⟨j.val - (n - (PT.tiling.P i).h), by
          have hj' : n - (PT.tiling.P i).h ≤ j.val := by
            simpa [Tiling.Icoord, topCoordinates] using hj
          have hjlt := j.isLt
          omega⟩
        else s j
    have hExtendLeaf (s : CubePos n) (u : CubePos (PT.tiling.P i).h)
        (hs : SliceValid i s) : extendAt s u ∈ PT.tiling.leaf i := by
      change ∀ j : Fin n, j.val < (PT.tiling.P i).ℓ →
        extendAt s u j = PT.tiling.w i ⟨j.val, by omega⟩
      intro j hj
      have hnot : j ∉ PT.tiling.Icoord i := by
        intro hmem
        have htop : n - (PT.tiling.P i).h ≤ j.val := by
          simpa [Tiling.Icoord, topCoordinates] using hmem
        have hlen := hEllH i
        omega
      let p : Fin (PT.tiling.P i).ℓ := ⟨j.val, hj⟩
      let pN : Fin n := ⟨p.val, by
        have hp := p.isLt
        have hlen := hEllH i
        dsimp [n] at hlen
        omega⟩
      have hpN : pN = j := by apply Fin.ext; rfl
      have hnotP : pN ∉ PT.tiling.Icoord i := by simpa [hpN] using hnot
      have hbit : extendAt s u j = s pN := by
        rw [← hpN]
        simp [extendAt, hnotP]
      calc
        extendAt s u j = s pN := hbit
        _ = PT.tiling.w i pN := by simpa [pN] using hs.1 p
    have hExtendPatch (s : CubePos n) (u : CubePos (PT.tiling.P i).h)
        (hs : SliceValid i s) : patchOf (extendAt s u) = i := by
      have hleaf := hExtendLeaf s u hs
      rcases hPT.tiling_valid.prefix_complete (extendAt s u) with ⟨j, hj, hjuniq⟩
      exact (hjuniq (patchOf (extendAt s u)) (patchOf_leaf (extendAt s u))).trans
        (hjuniq i hleaf).symm
    have hExtendSlice (s : CubePos n) (u : CubePos (PT.tiling.P i).h)
        (hs : SliceValid i s) : sliceOf (extendAt s u) = s := by
      have hp := hExtendPatch s u hs
      funext j
      dsimp [sliceOf, sliceAt]
      rw [hp]
      by_cases hj : j ∈ PT.tiling.Icoord i
      · simp [hj, hs.2 j hj]
      · simp [hj, extendAt]
    have hExtendInner (s : CubePos n) (u : CubePos (PT.tiling.P i).h)
        (hs : SliceValid i s) : innerAt i (extendAt s u) = u := by
      funext j
      have hjmem :
          (⟨n - (PT.tiling.P i).h + j.val,
            by have hj := j.isLt; have hlen := hEllH i; omega⟩ : Fin n) ∈
              PT.tiling.Icoord i := by
        simp [Tiling.Icoord, topCoordinates]
        have hj := j.isLt
        omega
      have hidx :
          (⟨n - (PT.tiling.P i).h + j.val - (n - (PT.tiling.P i).h),
            by have hj := j.isLt; omega⟩ : Fin (PT.tiling.P i).h) = j := by
        apply Fin.ext
        exact Nat.add_sub_cancel_left _ _
      simpa [innerAt, extendAt, hjmem] using congrArg u hidx
    have hKeyShape (col : Fin (D + 1)) (start : ℕ) (s : CubePos n)
        (r : Fin (SliceClass i col).card) (hs : s ∈ SliceClass i col)
        (hc : colors s = col)
        (hr : (SliceClass i col).equivFin ⟨s, hs⟩ = r)
        (hstart : Lane_q_s16_geom.batchStart r.val q = start) :
        keyOfAt i s = ⟨i, (col, start)⟩ := by
      dsimp [keyOfAt]
      rw [hc]
      simp [hs, hr, hstart, q]
    have hBatchComplete (c : Cell) (hc : C.cellPatch c = i)
        (hfull : c.1.2.2 + q ≤ (SliceClass i c.1.2.1).card) :
        Real.rpow (n : ℝ) κ.Ac / 3 ≤ (C.positions c).card := by
      obtain ⟨s₀, hs₀, hstart₀⟩ := hCellRank i c hc
      let col := c.1.2.1
      let start := c.1.2.2
      have hmod : start % q = 0 := by
        dsimp [start, q]
        rw [hstart₀]
        exact Lane_q_s16_geom.batchStart_mod _ _
      have hqPos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      let f : Fin q × CubePos (PT.tiling.P i).h →
          {b : Pos T k // b ∈ C.positions c} := fun z => by
        let r : Fin (SliceClass i col).card :=
          ⟨start + z.1.val, by have hz := z.1.isLt; dsimp [start, col] at *; omega⟩
        let point := (SliceClass i col).equivFin.symm r
        let s := point.1
        have hmem : s ∈ SliceClass i col := point.2
        have hvalid : SliceValid i s := (Finset.mem_filter.mp hmem).2.1
        have hcolor : colors s = col := (Finset.mem_filter.mp hmem).2.2
        have hrank : (SliceClass i col).equivFin ⟨s, hmem⟩ = r := by
          exact Equiv.apply_symm_apply _ _
        have hstart : Lane_q_s16_geom.batchStart r.val q = start := by
          dsimp [r, start]
          exact Lane_q_s16_geom.batchStart_add_of_mod_eq_zero hq hmod z.1.isLt
        let b := extendAt s z.2
        have hleaf := hExtendLeaf s z.2 hvalid
        have hpatch : patchOf b = i := by
          simpa [b] using hExtendPatch s z.2 hvalid
        have hslice : sliceOf b = s := by
          simpa [b] using hExtendSlice s z.2 hvalid
        have hkeyB : keyOf b = ⟨i, (col, start)⟩ := by
          calc
            keyOf b = keyOfAt i s := by simp [keyOf, hpatch, hslice]
            _ = ⟨i, (col, start)⟩ := hKeyShape col start s r hmem hcolor hrank hstart
        have hkeyC : c.1 = ⟨i, (col, start)⟩ := by
          apply Sigma.ext
          · exact hc
          · exact heq_of_eq (Prod.ext rfl rfl)
        have hcell : C.cellOf b = c := by
          apply Subtype.ext
          exact hkeyB.trans hkeyC.symm
        refine ⟨b, ?_⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
      have hf : Function.Injective f := by
        intro z z' hzz'
        have hb :
            extendAt
              ((SliceClass i col).equivFin.symm
                ⟨start + z.1.val, by have hz := z.1.isLt; dsimp [start, col] at *; omega⟩).1 z.2 =
            extendAt
              ((SliceClass i col).equivFin.symm
                ⟨start + z'.1.val, by have hz := z'.1.isLt; dsimp [start, col] at *; omega⟩).1 z'.2 :=
          congrArg Subtype.val hzz'
        let r : Fin (SliceClass i col).card :=
          ⟨start + z.1.val, by have hz := z.1.isLt; dsimp [start, col] at *; omega⟩
        let r' : Fin (SliceClass i col).card :=
          ⟨start + z'.1.val, by have hz := z'.1.isLt; dsimp [start, col] at *; omega⟩
        have hslice : ((SliceClass i col).equivFin.symm r).1 =
            ((SliceClass i col).equivFin.symm r').1 := by
          calc
            ((SliceClass i col).equivFin.symm r).1 =
                sliceOf (extendAt ((SliceClass i col).equivFin.symm r).1 z.2) :=
                  (hExtendSlice ((SliceClass i col).equivFin.symm r).1 z.2
                    ((Finset.mem_filter.mp ((SliceClass i col).equivFin.symm r).2).2.1)).symm
            _ = sliceOf (extendAt ((SliceClass i col).equivFin.symm r').1 z'.2) :=
                  congrArg sliceOf hb
            _ = ((SliceClass i col).equivFin.symm r').1 :=
                  hExtendSlice ((SliceClass i col).equivFin.symm r').1 z'.2
                    ((Finset.mem_filter.mp ((SliceClass i col).equivFin.symm r').2).2.1)
        have hr : r = r' := (SliceClass i col).equivFin.symm.injective (Subtype.ext hslice)
        have hzval : z.1.val = z'.1.val := by
          have hv := congrArg Fin.val hr
          dsimp [r, r'] at hv
          omega
        have hinner : z.2 = z'.2 := by
          have hv := congrArg (innerAt i) hb
          rw [hExtendInner _ _ ((Finset.mem_filter.mp ((SliceClass i col).equivFin.symm r).2).2.1),
            hExtendInner _ _ ((Finset.mem_filter.mp ((SliceClass i col).equivFin.symm r').2).2.1)] at hv
          exact hv
        exact Prod.ext (Fin.ext hzval) hinner
      have hsubcard : Fintype.card {b : Pos T k // b ∈ C.positions c} =
          (C.positions c).card := by
        rw [Fintype.card_subtype]
        simp
      have hcard : q * 2 ^ (PT.tiling.P i).h ≤ (C.positions c).card := by
        have hcard' := Fintype.card_le_of_injective f hf
        simpa [CubePos, hsubcard] using hcard'
      have hcardR : (q : ℝ) * (2 : ℝ) ^ (PT.tiling.P i).h ≤
          ((C.positions c).card : ℝ) := by
        have hcardCast : ((q * 2 ^ (PT.tiling.P i).h : ℕ) : ℝ) ≤
            ((C.positions c).card : ℝ) := by exact_mod_cast hcard
        simpa using hcardCast
      have hroom : Real.rpow (n : ℝ) κ.Ac / 3 ≤
          (q : ℝ) * (2 : ℝ) ^ (PT.tiling.P i).h := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hBatchRoom i
      exact hroom.trans hcardR
    have hFinal (c : Cell) (hc : c ∈ small) :
        (SliceClass i c.1.2.1).card < c.1.2.2 + q := by
      by_contra hnot
      have hfull : c.1.2.2 + q ≤ (SliceClass i c.1.2.1).card := Nat.le_of_not_gt hnot
      have hcin : c ∈ cells := (Finset.mem_filter.mp hc).1
      have hpatch : C.cellPatch c = i := (Finset.mem_filter.mp hcin).2
      have hlarge := hBatchComplete c hpatch hfull
      exact (not_lt_of_ge hlarge) (Finset.mem_filter.mp hc).2
    let colorOf : {c : Cell // c ∈ small} → Fin (D + 1) := fun x => x.1.1.2.1
    have hColorInj : Function.Injective colorOf := by
      intro x y hxy
      let c₁ := x.1
      let c₂ := y.1
      have hcin₁ : c₁ ∈ cells := (Finset.mem_filter.mp x.2).1
      have hcin₂ : c₂ ∈ cells := (Finset.mem_filter.mp y.2).1
      have hp₁ : C.cellPatch c₁ = i := (Finset.mem_filter.mp hcin₁).2
      have hp₂ : C.cellPatch c₂ = i := (Finset.mem_filter.mp hcin₂).2
      obtain ⟨s₁, hsMem₁, hsStart₁⟩ := hCellRank i c₁ hp₁
      obtain ⟨s₂, hsMem₂, hsStart₂⟩ := hCellRank i c₂ hp₂
      have hcolors : c₁.1.2.1 = c₂.1.2.1 := by
        change colorOf x = colorOf y at hxy
        exact hxy
      have hmod₁ : c₁.1.2.2 % q = 0 := by
        rw [hsStart₁]
        exact Lane_q_s16_geom.batchStart_mod _ _
      have hmod₂ : c₂.1.2.2 % q = 0 := by
        rw [hsStart₂]
        exact Lane_q_s16_geom.batchStart_mod _ _
      have hmul₁ : q * (c₁.1.2.2 / q) = c₁.1.2.2 := by
        simpa [hmod₁] using Nat.mod_add_div c₁.1.2.2 q
      have hmul₂ : q * (c₂.1.2.2 / q) = c₂.1.2.2 := by
        simpa [hmod₂] using Nat.mod_add_div c₂.1.2.2 q
      have hkeyOfStarts (heq : c₁.1.2.2 = c₂.1.2.2) : c₁.1 = c₂.1 := by
        apply Sigma.ext
        · exact hp₁.trans hp₂.symm
        · exact heq_of_eq (Prod.ext hcolors heq)
      by_cases hstartEq : c₁.1.2.2 = c₂.1.2.2
      · apply Subtype.ext
        simpa [c₁, c₂] using hkeyOfStarts hstartEq
      · rcases lt_or_gt_of_ne hstartEq with hlt | hgt
        · have hdivlt : c₁.1.2.2 / q < c₂.1.2.2 / q := by
            apply lt_of_mul_lt_mul_left _ (Nat.zero_le q)
            simpa [hmul₁, hmul₂] using hlt
          have hgap : c₁.1.2.2 + q ≤ c₂.1.2.2 := by
            calc
              c₁.1.2.2 + q = q * (c₁.1.2.2 / q + 1) := by
                rw [Nat.mul_add, Nat.mul_one, hmul₁]
              _ ≤ q * (c₂.1.2.2 / q) := Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr hdivlt)
              _ = c₂.1.2.2 := hmul₂
          let r₂ := (SliceClass i c₂.1.2.1).equivFin ⟨s₂, hsMem₂⟩
          have hstart₂lt : c₂.1.2.2 < (SliceClass i c₂.1.2.1).card := by
            rw [hsStart₂]
            exact (Lane_q_s16_geom.batchStart_le_rank r₂.val q).trans_lt r₂.isLt
          have hcardEq : (SliceClass i c₂.1.2.1).card =
              (SliceClass i c₁.1.2.1).card := by rw [← hcolors]
          have hFinal₁ := hFinal c₁ x.2
          omega
        · have hdivlt : c₂.1.2.2 / q < c₁.1.2.2 / q := by
            apply lt_of_mul_lt_mul_left _ (Nat.zero_le q)
            simpa [hmul₁, hmul₂] using hgt
          have hgap : c₂.1.2.2 + q ≤ c₁.1.2.2 := by
            calc
              c₂.1.2.2 + q = q * (c₂.1.2.2 / q + 1) := by
                rw [Nat.mul_add, Nat.mul_one, hmul₂]
              _ ≤ q * (c₁.1.2.2 / q) := Nat.mul_le_mul_left q (Nat.succ_le_iff.mpr hdivlt)
              _ = c₁.1.2.2 := hmul₁
          let r₁ := (SliceClass i c₁.1.2.1).equivFin ⟨s₁, hsMem₁⟩
          have hstart₁lt : c₁.1.2.2 < (SliceClass i c₁.1.2.1).card := by
            rw [hsStart₁]
            exact (Lane_q_s16_geom.batchStart_le_rank r₁.val q).trans_lt r₁.isLt
          have hcardEq : (SliceClass i c₁.1.2.1).card =
              (SliceClass i c₂.1.2.1).card := by rw [hcolors]
          have hFinal₂ := hFinal c₂ y.2
          omega
    have hsmallNat : small.card ≤ D + 1 := by
      have hsubcard : Fintype.card {c : Cell // c ∈ small} = small.card := by
        rw [Fintype.card_subtype]
        simp
      calc
        small.card = Fintype.card {c : Cell // c ∈ small} := hsubcard.symm
        _ ≤ Fintype.card (Fin (D + 1)) := Fintype.card_le_of_injective colorOf hColorInj
        _ = D + 1 := by simp
    have hsmallReal : (small.card : ℝ) ≤ (D + 1 : ℝ) := by exact_mod_cast hsmallNat
    have hColorBound : (D + 1 : ℝ) ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
      calc
        (D + 1 : ℝ) = 1 +
            ∑ j ∈ Finset.range (R + 1), (Nat.choose n j : ℝ) := by
              simp [D, Nat.cast_sum, add_comm]
        _ ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := by
              simpa [R, n] using hScale.coloring_room
    calc
      (small.card : ℝ) ≤ (D + 1 : ℝ) := hsmallReal
      _ ≤ Real.exp (Real.rpow (Real.log (n : ℝ)) 5) := hColorBound
  · intro c b b' hbc hbc' hnot
    simpa [n] using hSliceSeparation c b b' hbc hbc' hnot

/-- L16.1c (16:98–121): the pool comparison; the finite tape law is already
defined as `PartC.tapeLaw` from L16.1c's indexed lookup representation. -/
theorem pool_comparison_exists {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) (D : LowGeometryData PT)
    (hC : CellPartitionFacts hκ Q D.cells) :
    (permPools D.toLowGeom).Nonempty ∧ PoolComparison D.toLowGeom := by
  classical
  let G := D.toLowGeom
  let SlotDomain (i : Fin PT.tiling.m) :=
    Σ c : {c : G.Cell // G.cellPatch c = i}, Fin (G.nslot c.1)
  have hSlotCard (i : Fin PT.tiling.m) :
      Fintype.card (SlotDomain i) = ∑ c ∈ D.cells.cellsInPatch i, D.cells.nslot c := by
    classical
    change Fintype.card
        (Σ c : {c : D.cells.Cell // D.cells.cellPatch c = i}, Fin (D.cells.nslot c.1)) =
      ∑ c ∈ D.cells.cellsInPatch i, D.cells.nslot c
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    change (∑ c ∈ (Finset.univ : Finset {c : D.cells.Cell // D.cells.cellPatch c = i}),
        D.cells.nslot c.1) = ∑ c ∈ D.cells.cellsInPatch i, D.cells.nslot c
    rw [show D.cells.cellsInPatch i =
      Finset.univ.filter (fun c : D.cells.Cell => D.cells.cellPatch c = i) by rfl]
    apply Finset.sum_bij (fun c _ => c.1)
    · intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c.2⟩
    · intro c₁ hc₁ c₂ hc₂ heq
      exact Subtype.ext heq
    · intro c hc
      have hc' := (Finset.mem_filter.mp hc).2
      exact ⟨⟨c, hc'⟩, Finset.mem_univ _, rfl⟩
    · intro c hc
      rfl
  have hEmbed (i : Fin PT.tiling.m) :
      ∃ e : SlotDomain i ↪ Bin PT.tiling i, True := by
    refine ⟨Lane_q_s16_geom.finiteEmbeddingOfCardLE ?_, trivial⟩
    rw [hSlotCard]
    exact hC.slots_fit i
  let embed (i : Fin PT.tiling.m) : SlotDomain i ↪ Bin PT.tiling i :=
    Classical.choose (hEmbed i)
  have hEmbedInjective {i j : Fin PT.tiling.m} (hij : i = j)
      (x : SlotDomain i) (y : SlotDomain j)
      (hbin : (embed i x).1 = (embed j y).1) :
      x.1.1 = y.1.1 ∧ x.2.val = y.2.val := by
    cases hij
    rcases x with ⟨⟨C, hC⟩, s⟩
    rcases y with ⟨⟨C', hC'⟩, s'⟩
    have hEq : embed i ⟨⟨C, hC⟩, s⟩ = embed i ⟨⟨C', hC'⟩, s'⟩ := by
      apply Subtype.ext
      exact hbin
    have hSigma := (embed i).injective hEq
    rcases Sigma.mk.inj_iff.mp hSigma with ⟨hcell, hslot⟩
    have hcell' : C = C' := congrArg Subtype.val hcell
    subst C'
    exact ⟨rfl, congrArg Fin.val (eq_of_heq hslot)⟩
  let P : PoolAssignment G := fun c s =>
    embed (G.cellPatch c) ⟨⟨c, rfl⟩, s⟩
  have hP : P ∈ permPools G := by
    simp only [permPools, Finset.mem_filter, Finset.mem_univ, true_and]
    intro C C' s s' hpatch hbin
    have hbin' : (embed (G.cellPatch C) ⟨⟨C, rfl⟩, s⟩).1 =
        (embed (G.cellPatch C') ⟨⟨C', rfl⟩, s'⟩).1 := by
      simpa [P] using hbin
    exact hEmbedInjective hpatch ⟨⟨C, rfl⟩, s⟩ ⟨⟨C', rfl⟩, s'⟩ hbin'
  have hNonempty : (permPools G).Nonempty := ⟨P, hP⟩
  have hComparison : PoolComparison G := by
    intro i hperm S hpatch hSsize hBinGuard F hF hDepends
    by_cases hSempty : S = ∅
    · subst S
      let P0 := hperm.choose
      let c : ℝ := F P0
      have hFconstant : ∀ P, F P = c := by
        intro P'
        dsimp [c]
        apply hDepends P' P0
        intro s hs
        simp at hs
      have hFeq : F = fun _ => c := by
        funext P'
        exact hFconstant P'
      have hcNonneg : 0 ≤ c := by simpa [c] using hF P0
      have hpermE : (permPoolLaw G hperm).E F = c := by
        rw [hFeq]
        exact Lane_q_s16_geom.finLaw_expectation_const (permPoolLaw G hperm) c
      have hiidE : (iidPoolLaw G hperm).E F = c := by
        rw [hFeq]
        exact Lane_q_s16_geom.finLaw_expectation_const (iidPoolLaw G hperm) c
      constructor
      · rw [hpermE, hiidE]
        simp
      · intro s D hpinPatch hpermPin hiidPin
        have hpermPinE :
            (FinLaw.cond (permPoolLaw G hperm) (poolPinEvent s D) hpermPin).E F = c := by
          rw [hFeq]
          exact Lane_q_s16_geom.finLaw_expectation_const _ c
        have hiidPinE :
            (FinLaw.cond (iidPoolLaw G hperm) (poolPinEvent s D) hiidPin).E F = c := by
          rw [hFeq]
          exact Lane_q_s16_geom.finLaw_expectation_const _ c
        rw [hpermPinE, hiidPinE]
        have hcoefTerm : 0 ≤ ((insert s (∅ : Finset (CellSlot G))).card : ℝ) ^ 2 /
            Fintype.card (Bin PT.tiling i) :=
          div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
        have hcoef : 1 ≤ 1 + ((insert s (∅ : Finset (CellSlot G))).card : ℝ) ^ 2 /
            Fintype.card (Bin PT.tiling i) := by linarith
        calc
          c = 1 * c := by ring
          _ ≤ (1 + ((insert s (∅ : Finset (CellSlot G))).card : ℝ) ^ 2 /
              Fintype.card (Bin PT.tiling i)) * c :=
            mul_le_mul_of_nonneg_right hcoef hcNonneg
    · let B := Fintype.card (Bin PT.tiling i)
      have hBguardNat : 2 * (S.card + 1) ^ 2 ≤ B := by exact_mod_cast hBinGuard
      have hscopeSquare : S.card ^ 2 ≤ (S.card + 1) ^ 2 :=
        Nat.pow_le_pow_left (Nat.le_add_right _ _) 2
      have hscopeGuard : 2 * S.card ^ 2 ≤ B :=
        (Nat.mul_le_mul_left 2 hscopeSquare).trans hBguardNat
      have hscopeRatio : (B : ℝ) ^ S.card / (B.descFactorial S.card : ℝ) ≤
          1 + (S.card : ℝ) ^ 2 / B :=
        Lane_q_s16_geom.descFactorial_ratio_bound hscopeGuard
      constructor
      · sorry
      · intro s D hpinPatch hpermPin hiidPin
        have hpinCard : (insert s S).card ≤ S.card + 1 := by
          by_cases hs : s ∈ S <;> simp [hs]
        have hpinSquare : (insert s S).card ^ 2 ≤ (S.card + 1) ^ 2 :=
          Nat.pow_le_pow_left hpinCard 2
        have hpinGuard : 2 * (insert s S).card ^ 2 ≤ B :=
          (Nat.mul_le_mul_left 2 hpinSquare).trans hBguardNat
        have hpinRatio : (B : ℝ) ^ (insert s S).card /
            (B.descFactorial (insert s S).card : ℝ) ≤
              1 + ((insert s S).card : ℝ) ^ 2 / B :=
          Lane_q_s16_geom.descFactorial_ratio_bound hpinGuard
        sorry
  exact ⟨hNonempty, hComparison⟩

/-- L16.1: late classes, separated cells, persistent slot pools, and tapes. -/
theorem low_geometry_at_scale {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible)
    {K16 : ℝ} (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (hScale : LowModeScaleFacts hκ Q) :
    Nonempty (LowGeometryCertificate hκ Q) := by
  obtain ⟨S, hS⟩ := syndrome_data_exists hκ Q hScale
  obtain ⟨C, hC⟩ := cell_data_exists hκ Q hScale
  let D : LowGeometryData PT := ⟨S, C⟩
  obtain ⟨hNonempty, hPool⟩ := pool_comparison_exists hκ Q hScale D hC
  exact ⟨⟨D, hScale, hS, hC, hNonempty, hPool⟩⟩

/-- L16.1 in its eventual form. Neither cutoff may depend on the index,
the dimension, the host size, or the chosen profiled tiling. -/
theorem late_classes_and_cell_inputs {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
        (Q : LowModeQuantFacts hκ (PT := PT) K16),
        n₀ ≤ T.S.n k → C₀ * (2 : ℝ) ^ T.S.n k ≤ T.S.N k →
        Nonempty (LowGeometryCertificate hκ Q) := by
  obtain ⟨n₀, C₀, hC₀, hScale⟩ := low_geometry_thresholds hκ
  exact ⟨n₀, C₀, hC₀, fun Q hn hN =>
    low_geometry_at_scale hκ Q (hScale Q hn hN)⟩

end HypercubeRamsey.S16
