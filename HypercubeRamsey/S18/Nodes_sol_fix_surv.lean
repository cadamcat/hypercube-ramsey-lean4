import HypercubeRamsey.S18.Nodes_q_s18_n3
import HypercubeRamsey.S18.Nodes_sol_s18_2i

namespace HypercubeRamsey.S18.Lane_sol_fix_surv
open Classical Filter
open scoped BigOperators

set_option maxHeartbeats 500000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

theorem KB_ge_ten (hκ : κ.Admissible) : 10 ≤ κ.KB := by
  have hP : 1 ≤ κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hR : 1 ≤ κ.R := by
    rw [hκ.R_eq]
    exact Nat.one_le_pow _ _ hP
  have hRreal : (1 : ℝ) ≤ κ.R := by exact_mod_cast hR
  nlinarith [hκ.KB_big]

/-- The low cluster exponent is smaller than one, uniformly in the stage. -/
theorem cluster_exponent_le_one (hκ : κ.Admissible) :
    0 ≤ κ.Cb ∧ κ.cq * κ.Cb ≤ 1 := by
  have hfrac : 0 < 100 * κ.aC / κ.aB := by
    positivity [hκ.aC_rng.1, hκ.aB_rng.1]
  have hCb : 0 < κ.Cb := by linarith [hκ.Cb_big]
  have hM : 0 < (κ.Mlo : ℝ) := by linarith [hκ.Mlo_big]
  have hprod : κ.cq * (20 * (κ.Mlo : ℝ)) < 1 :=
    (lt_div_iff₀ (by positivity)).mp hκ.cq_rng.2
  have hcompare := mul_le_mul_of_nonneg_left
    (show κ.Cb ≤ 20 * (κ.Mlo : ℝ) by linarith [hκ.Mlo_big]) hκ.cq_rng.1.le
  exact ⟨hCb.le, by linarith⟩

/-- All three low-mode windows give the same drift bound once log n is large. -/
theorem low_degree_upper (hκ : κ.Admissible) (hPT : PT.Valid) (hLow : PT.tiling.mode.isLow)
    (hn : 0 < (T.S.n k : ℝ)) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (hbd : κ.Kbd ≤ Real.log (T.S.n k : ℝ))
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope i) :
    deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
      1 / 2 + 4 * κ.KB * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) := by
  have hKB := KB_ge_ten hκ
  have hown := hPT.envelope_degree i x hx
  have hlog0 : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  cases hm : PT.tiling.mode with
  | bounded =>
      have h := (abs_le.mp (by simpa [OwnDegOK, hm] using hown)).2
      have hnum : κ.Kbd ≤ 4 * κ.KB * Real.log (T.S.n k : ℝ) := by
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 4 * κ.KB by linarith) hlog0
        nlinarith
      have := div_le_div_of_nonneg_right hnum hn.le
      linarith
  | lowDirect =>
      have hup := (by simpa [OwnDegOK, hm] using hown :
        1 / 2 + (PT.tiling.P i).g / (4 * T.S.n k) ≤
          deg (T.S.E k) PT.tiling.c (PT.π i).w x ∧
        deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤
          1 / 2 + 4 * (PT.tiling.P i).g / T.S.n k).2
      have hg : (PT.tiling.P i).g ≤ κ.KB * Real.log (T.S.n k : ℝ) := by
        have hh := (hPT.tiling_valid.direct_data (Or.inl hm) i).2.2.2.2.2.2
        apply le_of_not_gt
        intro hgt
        have : PT.tiling.mode = .highDirect := hh.mpr hgt
        simp [hm] at this
      have hnum := mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 4)
      have hdiv : 4 * (PT.tiling.P i).g / (T.S.n k : ℝ) ≤
          4 * κ.KB * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) := by
        simpa only [mul_assoc] using div_le_div_of_nonneg_right hnum hn.le
      exact hup.trans (by simpa only [add_comm] using add_le_add_left hdiv (1 / 2))
  | lowCluster =>
      have hup := (abs_le.mp (by simpa [OwnDegOK, hm] using hown)).2
      have hqiff := (hPT.tiling_valid.cluster_data (Or.inl hm) i).2.2.2.2.2.2.2.2.2.1
      have hq : ((PT.tiling.P i).q : ℝ) ≤
          Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq := hqiff.mp hm
      obtain ⟨hCb, hexp⟩ := cluster_exponent_le_one hκ
      have hqpow : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤
          Real.log (T.S.n k : ℝ) := by
        calc
          _ ≤ Real.rpow (Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq) κ.Cb :=
            Real.rpow_le_rpow (by positivity) hq hCb
          _ = Real.rpow (Real.log (T.S.n k : ℝ)) (κ.cq * κ.Cb) :=
            (Real.rpow_mul hlog0 _ _).symm
          _ ≤ Real.rpow (Real.log (T.S.n k : ℝ)) 1 :=
            Real.rpow_le_rpow_of_exponent_le hlog hexp
          _ = _ := Real.rpow_one _
      have hnum : 10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤
          4 * κ.KB * Real.log (T.S.n k : ℝ) := by
        have hh := mul_le_mul_of_nonneg_right (show (10 : ℝ) ≤ 4 * κ.KB by linarith) hlog0
        linarith
      have hdec : deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2 ≤
          4 * κ.KB * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) := by
        simpa only [one_div] using hup.trans (div_le_div_of_nonneg_right hnum hn.le)
      linarith only [hdec]
  | highDirect => simp [Mode.isLow, hm] at hLow
  | highSmall => simp [Mode.isLow, hm] at hLow
  | highLarge => simp [Mode.isLow, hm] at hLow

/-- An exponential bound for a normalized power, keeping the relative
marginal error separate from the degree/correlation drift. -/
theorem normalized_moment_le {p q e B a : ℝ} (d : ℕ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (he : 0 ≤ e) (ha : 0 ≤ a)
    (hpq : p ≤ ((1 + e) * q) ^ d) (hqB : a * q ≤ 1 + B) :
    (a ^ d * p) ^ 2 ≤ Real.exp (2 * (d : ℝ) * (e + B)) := by
  have hbase : a * ((1 + e) * q) ≤ Real.exp (e + B) := by
    calc
      _ = (1 + e) * (a * q) := by ring
      _ ≤ Real.exp e * Real.exp B :=
        mul_le_mul (by simpa only [add_comm] using Real.add_one_le_exp e)
          (hqB.trans (by simpa only [add_comm] using Real.add_one_le_exp B)) (by positivity) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hupper : a ^ d * p ≤ Real.exp ((d : ℝ) * (e + B)) := by
    calc
      _ ≤ a ^ d * (((1 + e) * q) ^ d) :=
        mul_le_mul_of_nonneg_left hpq (by positivity)
      _ = (a * ((1 + e) * q)) ^ d := (mul_pow _ _ _).symm
      _ ≤ (Real.exp (e + B)) ^ d := pow_le_pow_left₀ (by positivity) hbase d
      _ = _ := (Real.exp_nat_mul _ _).symm
  calc
    _ ≤ (Real.exp ((d : ℝ) * (e + B))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hupper 2
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; norm_num; ring

theorem probability_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A : Ω → Prop) : 0 ≤ P.pr A := by
  classical
  unfold FinLaw.pr
  exact Finset.sum_nonneg fun s _ => by split_ifs <;> simp [P.nonneg]

theorem degree_nonneg (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) :
    0 ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
  unfold deg hit
  exact Finset.sum_nonneg fun y _ => mul_nonneg ((PT.π i).nonneg y)
    (by split_ifs <;> norm_num)

theorem marginal_error_bound (hn : 1 ≤ (T.S.n k : ℝ))
    (hKB : 0 ≤ κ.KB) :
    (T.S.n k : ℝ) * (κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ≤ κ.KB := by
  have hnpos : 0 < (T.S.n k : ℝ) := by linarith
  have heq : (T.S.n k : ℝ) * Real.rpow (T.S.n k : ℝ) (-3) =
      Real.rpow (T.S.n k : ℝ) (-2) := by
    calc
      _ = Real.rpow (T.S.n k : ℝ) (1 : ℝ) * Real.rpow (T.S.n k : ℝ) (-3) :=
        congrArg (fun t : ℝ => t * Real.rpow (T.S.n k : ℝ) (-3))
          (Real.rpow_one (T.S.n k : ℝ)).symm
      _ = Real.rpow (T.S.n k : ℝ) ((1 : ℝ) + (-3)) :=
        (Real.rpow_add hnpos (1 : ℝ) (-3)).symm
      _ = _ := by norm_num
  calc
    _ = κ.KB * Real.rpow (T.S.n k : ℝ) (-2) := by rw [← heq]; ring
    _ ≤ κ.KB * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)) hKB
    _ = _ := mul_one _

theorem corr_false_eq_true {N : ℕ} (E : Fin N → Fin N → Prop)
    (μ : Fin N → ℝ) (x z : Fin N) : corr E false μ x z = corr E true μ x z := by
  classical
  unfold corr
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : E x y <;> by_cases h' : E z y <;>
    simp [fv, hit, Hits, h, h'] <;> ring

theorem pairHitMass_identity {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (μ : Law N) (x z : Fin N) :
    (∑ y, μ.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) =
      (deg E c μ.w x + deg E c μ.w z) / 2 - 1 / 4 +
        corr E c μ.w x z / 4 := by
  classical
  have hfx (v : Fin N) :
      (∑ y, μ.w y * fv E c v y) = 2 * deg E c μ.w v - 1 := by
    calc
      (∑ y, μ.w y * fv E c v y) =
          ∑ y, (2 * (μ.w y * hit E c v y) - μ.w y) := by
            apply Finset.sum_congr rfl
            intro y _
            simp [fv]
            ring
      _ = 2 * (∑ y, μ.w y * hit E c v y) - ∑ y, μ.w y := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * deg E c μ.w v - 1 := by simp [deg, μ.sum_eq_one]
  have hpoint (y : Fin N) :
      (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0) =
        (1 + fv E c x y + fv E c z y + fv E c x y * fv E c z y) / 4 := by
    by_cases hx : Hits E c x y <;> by_cases hz : Hits E c z y <;>
      simp [fv, hit, hx, hz] <;> ring
  calc
    (∑ y, μ.w y * (if Hits E c x y ∧ Hits E c z y then (1 : ℝ) else 0)) =
        (∑ y, μ.w y *
          (1 + fv E c x y + fv E c z y + fv E c x y * fv E c z y)) / 4 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro y _
            rw [hpoint]
            ring
    _ = (∑ y, μ.w y + ∑ y, μ.w y * fv E c x y +
          ∑ y, μ.w y * fv E c z y +
          ∑ y, μ.w y * fv E c x y * fv E c z y) / 4 := by
            congr 1
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
            simp [mul_one, mul_assoc]
    _ = (deg E c μ.w x + deg E c μ.w z) / 2 - 1 / 4 +
          corr E c μ.w x z / 4 := by
            rw [μ.sum_eq_one, hfx x, hfx z]
            unfold corr
            ring

/-- Integrate the independent-cell upper bounds over the full patch.
The pair contribution uses the weighted relaxed tail inside the cutoff. -/
theorem survival_moments (hκ : κ.Admissible) (hD : D.Spec)
    (hgeom : TransferGeometry X) (hn : 1 ≤ (T.S.n k : ℝ))
    (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (hbd : κ.Kbd ≤ Real.log (T.S.n k : ℝ)) :
    ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      if X.allowed x none then ((2 : ℝ) ^ X.criticalCoords.card *
        X.rawLaw.pr (fun s => X.survives s x none)) ^ 2 else 0) /
        (PT.tiling.P (D.geom.patchOf X.target)).M ≤
          Real.exp ((64 * κ.KB) * Real.log (T.S.n k))) ∧
    ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      ∑ z ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
      if X.allowed x (some z) then ((4 : ℝ) ^ X.criticalCoords.card *
        X.rawLaw.pr (fun s => X.survives s x (some z))) ^ 2 else 0) /
        (PT.tiling.P (D.geom.patchOf X.target)).M ^ 2 ≤
          Real.exp ((64 * κ.KB) * Real.log (T.S.n k))) := by
  let n : ℝ := T.S.n k
  let L := Real.log n
  let i := D.geom.patchOf X.target
  let A := (PT.tiling.P i).X
  let M : ℝ := (PT.tiling.P i).M
  let d := X.criticalCoords.card
  let b := 4 * κ.KB * L / n
  let e := κ.KB * Real.rpow n (-3)
  have hnpos : 0 < n := by dsimp [n]; linarith
  have hKB := KB_ge_ten hκ
  have hKB0 : 0 ≤ κ.KB := by linarith
  have hL : 1 ≤ L := hlog
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hdnat : d ≤ T.S.n k := by
    simpa [d] using Finset.card_le_univ X.criticalCoords
  have hd : (d : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hdnat
  have hM : 0 < M := by
    dsimp [M]
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hcard : (A.card : ℝ) = M := by dsimp [A, M]; rw [(PT.tiling.P i).cardX]
  have hnb : n * b = 4 * κ.KB * L := by dsimp [b]; field_simp [hnpos.ne']
  have hne : n * e ≤ κ.KB := marginal_error_bound hn hKB0
  have hdeg (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope i) :
      deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤ 1 / 2 + b :=
    low_degree_upper hκ hPT D.low_mode hnpos hlog hbd i x hx
  have hcoeffSingle : 4 * n * b + 2 * n * e ≤ 64 * κ.KB * L := by
    have hKL : κ.KB ≤ κ.KB * L := by nlinarith
    nlinarith [hnb, hne]
  have hsingle (x : Fin (T.S.N k)) (hx : X.allowed x none) :
      ((2 : ℝ) ^ d * X.rawLaw.pr (fun s => X.survives s x none)) ^ 2 ≤
        Real.exp (64 * κ.KB * L) := by
    have hu := Lane_q_s18_n3.critical_raw_single_survival_upper hD hgeom x
    have hxenv := hx.1
    have hbase : 2 * deg (T.S.E k) PT.tiling.c (PT.π i).w x ≤ 1 + 2 * b := by
      linarith [hdeg x hxenv]
    have hh := normalized_moment_le d
      (probability_nonneg X.rawLaw _) (degree_nonneg i x) he (by norm_num : (0 : ℝ) ≤ 2)
      hu hbase
    have hexp : 2 * (d : ℝ) * (e + 2 * b) ≤ 4 * n * b + 2 * n * e := by
      have := mul_le_mul_of_nonneg_right hd (show 0 ≤ e + 2 * b by positivity)
      nlinarith
    exact hh.trans (Real.exp_le_exp.mpr (hexp.trans hcoeffSingle))
  constructor
  · change (∑ x ∈ A, if X.allowed x none then
        ((2 : ℝ) ^ d * X.rawLaw.pr (fun s => X.survives s x none)) ^ 2 else 0) / M ≤
          Real.exp (64 * κ.KB * L)
    apply (div_le_iff₀ hM).mpr
    calc
      _ ≤ ∑ x ∈ A, Real.exp (64 * κ.KB * L) := by
        apply Finset.sum_le_sum
        intro x _
        split_ifs with hx
        · exact hsingle x hx
        · positivity
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]
  · let C := Real.exp (8 * n * b + 2 * n * e)
    have hpair (x z : Fin (T.S.N k)) (hxz : X.allowed x (some z)) :
        ((4 : ℝ) ^ d * X.rawLaw.pr (fun s => X.survives s x (some z))) ^ 2 ≤
          C * Real.exp (2 * n * |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) := by
      let q := (deg (T.S.E k) PT.tiling.c (PT.π i).w x +
          deg (T.S.E k) PT.tiling.c (PT.π i).w z) / 2 - 1 / 4 +
            corr (T.S.E k) PT.tiling.c (PT.π i).w x z / 4
      let r := |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|
      have hq : 0 ≤ q := by
        dsimp [q]
        rw [← pairHitMass_identity]
        exact Finset.sum_nonneg fun y _ => mul_nonneg ((PT.π i).nonneg y)
          (by split_ifs <;> norm_num)
      have hz := (hxz.2 z rfl).1
      have hbase : 4 * q ≤ 1 + (4 * b + r) := by
        dsimp [q, r]
        have hc := le_abs_self (corr (T.S.E k) PT.tiling.c (PT.π i).w x z)
        linarith [hdeg x hxz.1, hdeg z hz]
      have hu := Lane_q_s18_n3.critical_raw_pair_survival_upper hD hgeom x z
      have hh := normalized_moment_le d (probability_nonneg X.rawLaw _)
        hq he (by norm_num : (0 : ℝ) ≤ 4) hu hbase
      have hexp : 2 * (d : ℝ) * (e + (4 * b + r)) ≤
          (8 * n * b + 2 * n * e) + 2 * n * r := by
        have := mul_le_mul_of_nonneg_right hd
          (show 0 ≤ e + (4 * b + r) by dsimp [r]; positivity)
        nlinarith
      calc
        _ ≤ Real.exp (2 * (d : ℝ) * (e + (4 * b + r))) := hh
        _ ≤ Real.exp ((8 * n * b + 2 * n * e) + 2 * n * r) := Real.exp_le_exp.mpr hexp
        _ = _ := by rw [Real.exp_add]
    have hξ : 0 ≤ κ.ξ := hκ.ξ_rng.1.le
    have hcorr (x z : Fin (T.S.N k)) (hxz : X.allowed x (some z)) :
        |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ := by
      have hc := (hxz.2 z rfl).2
      change |pairCorr (T.S.E k) true (PT.π i) x z| ≤ κ.ξ at hc
      cases hm : PT.tiling.c with
      | false => simpa [pairCorr, hm, corr_false_eq_true] using hc
      | true => simpa [pairCorr, hm] using hc
    have hrow (x : Fin (T.S.N k)) :
        (∑ z ∈ A, if X.allowed x (some z) then
          ((4 : ℝ) ^ d * X.rawLaw.pr (fun s => X.survives s x (some z))) ^ 2 else 0) ≤
            C * (Real.exp (2 * n * Real.rpow n (-1.02)) +
              Real.exp (-Real.rpow n 0.19)) * M := by
      by_cases hx : x ∈ PT.envelope i
      · have hr := Lane_sol_s18_2i.row_tail_exponential_sum hnpos.le hξ
          (hPT.envelope_row_tail i i x hx)
        calc
          _ ≤ ∑ z ∈ A, C * (if |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ then
                Real.exp (2 * n * |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0) := by
            apply Finset.sum_le_sum
            intro z _
            by_cases hxz : X.allowed x (some z)
            · rw [if_pos hxz, if_pos (hcorr x z hxz)]
              exact hpair x z hxz
            · rw [if_neg hxz]; dsimp [C]; split_ifs <;> positivity
          _ = C * (∑ z ∈ A, if |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ κ.ξ then
                Real.exp (2 * n * |corr (T.S.E k) PT.tiling.c (PT.π i).w x z|) else 0) :=
            (Finset.mul_sum _ _ _).symm
          _ ≤ C * ((Real.exp (2 * n * Real.rpow n (-1.02)) +
                Real.exp (-Real.rpow n 0.19)) * A.card) :=
            mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
          _ = _ := by rw [hcard]; ring
      · have hnot (z : Fin (T.S.N k)) : ¬ X.allowed x (some z) := fun hz => hx hz.1
        simp only [if_neg (hnot _), Finset.sum_const_zero]
        dsimp [C]; positivity
    have hτ : n * Real.rpow n (-1.02) ≤ 1 := by
      have heq : n * Real.rpow n (-1.02) = Real.rpow n (-0.02) := by
        calc
          _ = Real.rpow n (1 : ℝ) * Real.rpow n (-1.02) :=
            congrArg (fun t : ℝ => t * Real.rpow n (-1.02)) (Real.rpow_one n).symm
          _ = Real.rpow n ((1 : ℝ) + (-1.02)) :=
            (Real.rpow_add hnpos (1 : ℝ) (-1.02)).symm
          _ = _ := by norm_num
      rw [heq]
      exact Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num)
    have htail : Real.exp (-Real.rpow n 0.19) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg hnpos.le _))
    have hfactor : Real.exp (2 * n * Real.rpow n (-1.02)) +
        Real.exp (-Real.rpow n 0.19) ≤ Real.exp 3 := by
      have hh : Real.exp (2 * n * Real.rpow n (-1.02)) ≤ Real.exp 2 :=
        Real.exp_le_exp.mpr (by nlinarith [hτ])
      have h1 : 1 ≤ Real.exp (2 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
      have h2 : 2 ≤ Real.exp (1 : ℝ) := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h3 : 2 * Real.exp (2 : ℝ) ≤ Real.exp (1 : ℝ) * Real.exp 2 :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      rw [← Real.exp_add] at h3
      norm_num at h3
      linarith
    have hcoeffPair : (8 * n * b + 2 * n * e) + 3 ≤ 64 * κ.KB * L := by
      have hKL : κ.KB ≤ κ.KB * L := by nlinarith
      nlinarith [hnb, hne]
    have hC : C * (Real.exp (2 * n * Real.rpow n (-1.02)) +
        Real.exp (-Real.rpow n 0.19)) ≤ Real.exp (64 * κ.KB * L) := by
      calc
        _ ≤ C * Real.exp 3 := mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg _)
        _ = Real.exp ((8 * n * b + 2 * n * e) + 3) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr hcoeffPair
    change (∑ x ∈ A, ∑ z ∈ A, if X.allowed x (some z) then
        ((4 : ℝ) ^ d * X.rawLaw.pr (fun s => X.survives s x (some z))) ^ 2 else 0) / M ^ 2 ≤
          Real.exp (64 * κ.KB * L)
    apply (div_le_iff₀ (by positivity : 0 < M ^ 2)).mpr
    calc
      _ ≤ ∑ x ∈ A, C * (Real.exp (2 * n * Real.rpow n (-1.02)) +
          Real.exp (-Real.rpow n 0.19)) * M := Finset.sum_le_sum fun x _ => hrow x
      _ = (C * (Real.exp (2 * n * Real.rpow n (-1.02)) +
          Real.exp (-Real.rpow n 0.19))) * M ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC (sq_nonneg M)

/-- The coefficient depends only on the global constants, before k. -/
theorem survival_moments_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → ∀ X : CriticalTransferData D,
        TransferGeometry X →
        ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
          if X.allowed x none then ((2 : ℝ) ^ X.criticalCoords.card *
            X.rawLaw.pr (fun s => X.survives s x none)) ^ 2 else 0) /
              (PT.tiling.P (D.geom.patchOf X.target)).M ≤
                Real.exp ((64 * κ.KB) * Real.log (T.S.n k))) ∧
        ((∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
          ∑ z ∈ (PT.tiling.P (D.geom.patchOf X.target)).X,
          if X.allowed x (some z) then ((4 : ℝ) ^ X.criticalCoords.card *
            X.rawLaw.pr (fun s => X.survives s x (some z))) ^ 2 else 0) /
              (PT.tiling.P (D.geom.patchOf X.target)).M ^ 2 ≤
                Real.exp ((64 * κ.KB) * Real.log (T.S.n k))) := by
  have hnR : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlog := (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop (max 1 κ.Kbd)
  filter_upwards [hnR.eventually_ge_atTop 1, hlog] with k hn hl
  intro PT hPT D hD X hgeom
  exact survival_moments hκ hD hgeom hn ((le_max_left _ _).trans hl)
    ((le_max_right _ _).trans hl)

end HypercubeRamsey.S18.Lane_sol_fix_surv
