import HypercubeRamsey.S18.Nodes_sol_s18_n1_caps
import HypercubeRamsey.S18.Nodes_sol_s18_n5
import HypercubeRamsey.S18.Nodes_q_s18_n1

namespace HypercubeRamsey.Lane_sol_s18_n1_sketch
open Classical Filter
open scoped BigOperators
open S18 Lane_sol_s18_n1
set_option backward.isDefEq.respectTransparency false
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem corr_colour {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ : Law N) (x z : Fin N) : corr E c μ.w x z = pairCorr E true μ x z := by
  unfold pairCorr
  simp only [ite_true]
  cases c
  · unfold corr
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : E x y <;> by_cases hz : E z y <;> simp [fv,hit,Hits,hx,hz] <;> ring
  · rfl

/-- The gated posterior retains the active single-corner support of its initial prior. -/
theorem current_corner_support (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hg : D.gate j b h) (hb : b ∈ D.encoding.base.classes j) (a : Fin (T.S.n k)) :
    ∃ q ∈ PT.activeVertices, ∀ x,
      (D.currentPrior j (flipPos b a) h).w x ≠ 0 →
        x ∈ PT.mesh.corner q (D.geom.patchOf (flipPos b a)) := by
  let v := flipPos b a
  obtain ⟨hv,hmass⟩ := Lane_sol_s18_n1_caps.gated_current_mass D hsmall j b h hg hb a
  obtain ⟨q,hq,hsupp⟩ := hv.1.2.2.2.1
  refine ⟨q,hq,?_⟩
  intro x hx
  have hraw : Lane_sol_s18_n1_caps.rawWeight D h v x ≠ 0 := by
    intro hz
    apply hx
    rw [LateData.currentPrior,Lane_sol_s18_n1_caps.priorAt_weight D h v hv hmass,hz,zero_div]
  have hinit : (D.initialPrior v h.1).w x ≠ 0 := by
    intro hz
    apply hraw
    simp [Lane_sol_s18_n1_caps.rawWeight,hz]
  have hweight := (S18.Lane_sol_s18_n5.initialPrior_support D v h.1 hv x hinit).2
  by_contra hnot
  have hzero := hsupp x hnot
  change D.sigma v h.1 x = 0 at hzero
  apply hweight
  simp only [LateData.initialWeight,hzero,zero_mul,zero_div]

/-- Conflict mass is bounded by the conflict count on that single corner times the atom cap. -/
theorem current_conflict_mass (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (hC : CurrentListCapFacts D) (j : Fin D.geom.r)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hg : D.gate j b.1 h)
    {K16 : ℝ} (Q : S16.LowModeQuantFacts D.constants (PT := PT) K16)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) :
    (∑ z, (D.currentPrior j (flipPos b.1 a) h).w z *
      (if ¬ D.nonconflict (flipPos b.1 a) x z then (1:ℝ) else 0)) ≤
      K16 * Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q (D.geom.patchOf (flipPos b.1 a)) : ℝ)) *
        (8 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf (flipPos b.1 a))) *
          Real.rpow 2 (-(D.remainingNeighbors (flipPos b.1 a) j : ℝ))) := by
  let v := flipPos b.1 a
  let μ := D.currentPrior j v h
  let cap := 8 * κ.KB / densityScale T k * Real.exp (-199 * PT.tiling.gain (D.geom.patchOf v)) *
    Real.rpow 2 (-(D.remainingNeighbors v j : ℝ))
  obtain ⟨q,hq,hsupp⟩ := current_corner_support D hsmall j b.1 h hg b.2 a
  let C := (PT.mesh.corner q (D.geom.patchOf v)).filter fun z =>
    κ.ξ < |corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z|
  have hcount := Q.conflict_bound (D.geom.patchOf v) q hq x
  have hcap : ∀ z, μ.w z ≤ cap := hC j b.1 h hg b.2 a
  have hcap0 : 0 ≤ cap := (μ.nonneg x).trans (hcap x)
  have hzero (z : Fin (T.S.N k)) (hz : z ∉ C) :
      μ.w z * (if ¬ D.nonconflict v x z then (1:ℝ) else 0) = 0 := by
    by_cases hm : μ.w z = 0
    · simp [hm]
    · have hs := hsupp z hm
      have hcorr : |corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z| ≤ κ.ξ := by
        have hh : ¬ κ.ξ < |corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z| := by
          intro hh
          exact hz (Finset.mem_filter.mpr ⟨hs,hh⟩)
        exact le_of_not_gt hh
      have hn : D.nonconflict v x z := by
        rw [corr_colour] at hcorr
        exact hcorr
      simp [hn]
  calc
    _ = ∑ z ∈ C, μ.w z * (if ¬ D.nonconflict v x z then (1:ℝ) else 0) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro z _ hz
      exact hzero z hz
    _ ≤ ∑ z ∈ C, cap := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hn : D.nonconflict v x z
      · simpa [hn] using hcap0
      · simpa [hn] using hcap z
    _ = (C.card : ℝ) * cap := by simp
    _ ≤ K16 * Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q (D.geom.patchOf v) : ℝ)) * cap :=
      mul_le_mul_of_nonneg_right hcount hcap0


/-- The conflict-count exponential is absorbed by one gain exponential in each low mode. -/
theorem conflict_scale (hκ : κ.Admissible) (D : LateData hPT) (i : Fin PT.tiling.m) :
    Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) ≤
      max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)) * Real.exp (PT.tiling.gain i) := by
  have hc : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
  have ha : 0 ≤ κ.a := by rw [hκ.a_eq]; exact div_nonneg hκ.θ_rng.1.le (by norm_num)
  have hmax : (1:ℝ) ≤ max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)) := le_max_left _ _
  have hgain0 : 0 ≤ PT.tiling.gain i := by
    cases hm : PT.tiling.mode <;> simp_all [Tiling.gain,Mode.isLow] <;> positivity
  by_cases hb : PT.tiling.mode = .bounded
  · have hQ := (hPT.tiling_valid.bounded_data hb).2 i |>.2.2.2.2
    have hg : PT.tiling.gain i = 0 := by simp [Tiling.gain,hb]
    simp only [hQ,hg,Real.exp_zero,mul_one]
    exact le_max_right _ _
  · have hscale : Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ PT.tiling.gain i := by
      cases hm : PT.tiling.mode with
      | bounded => exact (hb hm).elim
      | lowDirect =>
        have hQ := ((hPT.tiling_valid.clique_scales i).2 (Or.inl hm)).2.2.1
        have hsq : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.mpr (by linarith [hκ.M1_big.1])
        have hg0 : (0:ℝ) ≤ (PT.tiling.P i).g := by positivity
        calc
          Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).g / Real.sqrt κ.M1) :=
            mul_le_mul_of_nonneg_left hQ hc
          _ = (2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1) * (PT.tiling.P i).g := by ring
          _ ≤ 0.0001 * (PT.tiling.P i).g := mul_le_mul_of_nonneg_right hκ.M1_big.2 hg0
          _ ≤ PT.tiling.gain i := by simp only [Tiling.gain,hm]; nlinarith
      | lowCluster =>
        rcases hPT.tiling_valid.cluster_data (Or.inl hm) i with
          ⟨hthreshold,hgq,hmass,hsmall,hbin,hcodeg,hdyadic,hhl,hhu,hrest⟩
        have hq : κ.Q0 ≤ ((PT.tiling.P i).q : ℝ) := by
          have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
          have hmaxq : max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) ≤
              κ.M1 * (PT.tiling.P i).q := by
            apply max_le hgq
            nlinarith [(show (0:ℝ) ≤ (PT.tiling.P i).q by positivity),hκ.M1_big.1]
          have hth : κ.M1 * κ.Q0 ≤ max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) := by
            simpa only [Nat.cast_max] using hthreshold
          nlinarith [hth.trans hmaxq]
        have hQ := ((hPT.tiling_valid.clique_scales i).1 (Or.inl hm)).2.2.1
        have hroom := (hκ.Q0_large _ hq).2.2.2.2.2.2.1
        have hheight : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mlo ≤ (PT.tiling.P i).h := by simpa [hm] using hhl
        have hh := mul_le_mul_of_nonneg_left hheight (show 0 ≤ κ.a / 10^6 by positivity)
        have hbound := mul_le_mul_of_nonneg_left hQ hc
        have hq0 : 0 ≤ ((PT.tiling.P i).q : ℝ)^2 := sq_nonneg _
        simp only [Tiling.gain,hm]
        nlinarith [mul_nonneg hc hq0]
      | highSmall => have hlow := D.low_mode; simp [Mode.isLow,hm] at hlow
      | highLarge => have hlow := D.low_mode; simp [Mode.isLow,hm] at hlow
      | highDirect => have hlow := D.low_mode; simp [Mode.isLow,hm] at hlow
    calc
      _ ≤ Real.exp (PT.tiling.gain i) := Real.exp_le_exp.mpr hscale
      _ ≤ max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)) * Real.exp (PT.tiling.gain i) := by
        simpa using mul_le_mul_of_nonneg_right hmax (Real.exp_nonneg _)


private theorem gain_nonneg (hκ : κ.Admissible) (i : Fin PT.tiling.m) : 0 ≤ PT.tiling.gain i := by
  have ha : 0 ≤ κ.a := by rw [hκ.a_eq]; exact div_nonneg hκ.θ_rng.1.le (by norm_num)
  cases hm : PT.tiling.mode <;> simp [Tiling.gain,hm] <;> positivity

private theorem beta_small (hκ : κ.Admissible) : κ.β ≤ 1/8 := by
  have hKB : 0 ≤ κ.KB := by nlinarith [hκ.KB_big]
  have hA : 0 ≤ κ.A0 := by nlinarith [hκ.A0_big]
  have hd : 0 < 1+κ.KB+2*κ.A0 := by positivity
  have hh := (le_div_iff₀ hd).mp hκ.β_rng.2.1
  have hb := mul_nonneg hκ.β_rng.1.le (show 0 ≤ κ.KB+2*κ.A0 by positivity)
  nlinarith

private theorem error_four (D : LateData hPT) (v : Pos T k) (j : Fin D.geom.r) :
    D.error v j ^ 4 = Real.exp (-4*κ.β*Real.log (densityScale T k)) *
      Real.exp (-4*κ.β*PT.tiling.gain (D.geom.patchOf v)) *
      Real.exp (-4*κ.β*(D.geom.r-j.val : ℕ)*Real.log 2) := by
  have hc : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold LateData.error lateError
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos hc,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_nat_mul]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  ring

/-- A density cutoff uniform over gains and the number of remaining classes. -/
theorem conflict_mass_half (hκ : κ.Admissible) (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000)) (hC : CurrentListCapFacts D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hg : D.gate j b.1 h)
    {K16 : ℝ} (Q : S16.LowModeQuantFacts D.constants (PT := PT) K16)
    (hsize : 32 * κ.KB * K16 * max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)) ≤
      Real.rpow (densityScale T k) (1-4*κ.β)) (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) :
    (∑ z, (D.currentPrior j (flipPos b.1 a) h).w z *
      (if ¬ D.nonconflict (flipPos b.1 a) x z then (1:ℝ) else 0)) ≤
        D.error (flipPos b.1 a) j ^ 4 / 2 := by
  let v := flipPos b.1 a
  let g := PT.tiling.gain (D.geom.patchOf v)
  let r := D.geom.r-j.val
  let p := D.remainingNeighbors v j
  let C := densityScale T k
  let A := max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd))
  let M := 8 * κ.KB * K16 * A
  have hCpos : 0 < C := by
    unfold C densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  have hKB : 0 ≤ κ.KB := by nlinarith [hκ.KB_big]
  have hM0 : 0 ≤ M := by
    have hK := Q.K16_pos
    dsimp [M,A]
    positivity
  have hg0 : 0 ≤ g := gain_nonneg hκ _
  have heven : IsEvenRole v := by
    obtain ⟨hv,hmass⟩ := Lane_sol_s18_n1_caps.gated_current_mass D hsmall j b.1 h hg b.2 a
    have hc := (D.encoding.base.class_of_spec b.1 j).mp b.2
    have hodd : ¬ IsEvenRole b.1 := by
      unfold LowGeom.classOf at hc
      split_ifs at hc with hh
      exact hh.1
    exact (cubeFlip_parity b.1 a).mpr hodd
  have hremain : r/2 ≤ p := D.l16_valid.remaining_count v heven j
  have hpr : (r:ℝ) ≤ 2*(p:ℝ)+1 := by
    have hh : r ≤ 2*p+1 := by omega
    exact_mod_cast hh
  have hβ := beta_small hκ
  have hexpg : Real.exp (-198*g) ≤ Real.exp (-4*κ.β*g) := by
    have hh := mul_le_mul_of_nonneg_right hβ hg0
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hpowp : Real.rpow 2 (-(p:ℝ)) ≤ 2 * Real.exp (-4*κ.β*(r:ℝ)*Real.log 2) := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    have hp : -(p:ℝ) ≤ 1-4*κ.β*(r:ℝ) := by
      have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
      have hh := mul_le_mul_of_nonneg_right hβ (show (0:ℝ) ≤ r by positivity)
      nlinarith
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc
      _ ≤ Real.exp (Real.log 2 * (1-4*κ.β*(r:ℝ))) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hlog)
      _ = 2 * Real.exp (-4*κ.β*(r:ℝ)*Real.log 2) := by
        rw [show Real.log 2 * (1-4*κ.β*(r:ℝ)) = Real.log 2 + (-4*κ.β*(r:ℝ)*Real.log 2) by ring]
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ) < 2)]
  have hbase : M/C ≤ Real.exp (-4*κ.β*Real.log C)/4 := by
    apply (div_le_iff₀ hCpos).mpr
    have hh : 4*M ≤ Real.rpow C (1-4*κ.β) := by
      convert hsize using 1 <;> dsimp [M,C,A] <;> ring
    have heq : Real.rpow C (1-4*κ.β) = C * Real.exp (-4*κ.β*Real.log C) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_def_of_pos hCpos]
      calc
        _ = Real.exp (Real.log C + (-4*κ.β*Real.log C)) := by congr 1; ring
        _ = _ := by rw [Real.exp_add,Real.exp_log hCpos]
    rw [heq] at hh
    nlinarith
  have hconf := current_conflict_mass D hsmall hC j b h hg Q a x
  have hscale := conflict_scale hκ D (D.geom.patchOf v)
  have hcap0 : 0 ≤ 8 * κ.KB / C * Real.exp (-199*g) * Real.rpow 2 (-(p:ℝ)) := by
    apply mul_nonneg
    · positivity
    · exact Real.rpow_nonneg (by norm_num) _
  have hdegree := mul_le_mul_of_nonneg_left hscale Q.K16_pos.le
  calc
    _ ≤ K16 * Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q (D.geom.patchOf v) : ℝ)) *
        (8 * κ.KB / C * Real.exp (-199*g) * Real.rpow 2 (-(p:ℝ))) := hconf
    _ ≤ (K16 * (A * Real.exp g)) *
        (8 * κ.KB / C * Real.exp (-199*g) * Real.rpow 2 (-(p:ℝ))) :=
      mul_le_mul_of_nonneg_right hdegree hcap0
    _ = M/C * Real.exp (-198*g) * Real.rpow 2 (-(p:ℝ)) := by
      dsimp [M]
      rw [show -198*g = g+(-199*g) by ring,Real.exp_add]
      ring
    _ ≤ (Real.exp (-4*κ.β*Real.log C)/4) * Real.exp (-4*κ.β*g) *
        (2 * Real.exp (-4*κ.β*(r:ℝ)*Real.log 2)) := by
      apply mul_le_mul
      · exact mul_le_mul hbase hexpg (Real.exp_nonneg _) (by positivity)
      · exact hpowp
      · exact Real.rpow_nonneg (by norm_num) _
      · positivity
    _ = D.error v j ^ 4 / 2 := by rw [error_four]; dsimp [C,g,r]; ring


/-- All analytic inputs to the exact row estimate, with uniform scalar cutoffs explicit. -/
theorem row_estimate (hκ : κ.Admissible) (D : LateData hPT) (hT : TransitionData D)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000)) (hC : CurrentListCapFacts D)
    {K16 : ℝ} (Q : S16.LowModeQuantFacts D.constants (PT := PT) K16)
    (hsize : 32 * κ.KB * K16 * max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)) ≤
      Real.rpow (densityScale T k) (1-4*κ.β))
    (hdiag : 2 ≤ Real.rpow (T.S.n k : ℝ) 0.17)
    (hunion : 2 * (T.S.n k : ℝ) * Real.exp (-Real.rpow (T.S.n k : ℝ) 0.09 / 2) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04))
    (hlower : ∀ i (j : Fin D.geom.r), Real.rpow (T.S.n k : ℝ) (-0.02) ≤
      lateError κ T k PT i (D.geom.r-j.val))
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hg : D.gate j b.1 h) :
    (D.encoding.kernels.refK j b h).pr (fun out => ¬ D.R1 j out) ≤
      Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  classical
  let n : ℝ := T.S.n k
  let m := sketchLength T k
  have hn : 0 < n := by dsimp [n]; exact_mod_cast (show 0 < T.S.n k by have hn := Q.n_large; omega)
  have hmc : Real.rpow n 0.25 ≤ (m:ℝ) := Nat.le_ceil _
  have hm' : 0 < (m:ℝ) := (Real.rpow_pos_of_pos hn _).trans_le hmc
  have hm : 0 < m := by exact_mod_cast hm'
  have hpowid (s : ℕ) : Real.rpow n 0.25 * (Real.rpow n (-0.02)) ^ s =
      Real.rpow n (0.25 + (-0.02)*(s:ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hn.le,← Real.rpow_add hn]
  have he (a : Fin (T.S.n k)) : Real.rpow n (-0.02) ≤ D.error (flipPos b.1 a) j := hlower _ j
  have he0 (a : Fin (T.S.n k)) : 0 < D.error (flipPos b.1 a) j := (Real.rpow_pos_of_pos hn _).trans_le (he a)
  have hprod (a : Fin (T.S.n k)) (s : ℕ) :
      Real.rpow n (0.25 + (-0.02)*(s:ℝ)) ≤ (m:ℝ)*D.error (flipPos b.1 a) j ^ s := by
    rw [← hpowid]
    exact mul_le_mul hmc (pow_le_pow_left₀ (Real.rpow_nonneg hn.le _) (he a) s)
      (pow_nonneg (Real.rpow_nonneg hn.le _) _) hm'.le
  have hmean (a : Fin (T.S.n k)) :
      (FinLaw.pi fun _ : Fin m => (⟨(D.currentPrior j (flipPos b.1 a) h).w,
        (D.currentPrior j (flipPos b.1 a) h).nonneg,
        (D.currentPrior j (flipPos b.1 a) h).sum_eq_one⟩ : FinLaw (Fin (T.S.N k)))).E
        (conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z)) ≤ D.error (flipPos b.1 a) j ^ 4 := by
    let P : FinLaw (Fin (T.S.N k)) := ⟨(D.currentPrior j (flipPos b.1 a) h).w,
      (D.currentPrior j (flipPos b.1 a) h).nonneg,(D.currentPrior j (flipPos b.1 a) h).sum_eq_one⟩
    have hbound : (FinLaw.pi fun _ : Fin m => P).E
        (conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z)) ≤
        1/(m:ℝ) + D.error (flipPos b.1 a) j ^ 4 / 2 := by
      apply conflictFraction_mean P _ m hm (D.error (flipPos b.1 a) j ^ 4 / 2) (by positivity)
      intro x
      convert conflict_mass_half hκ D hsmall hC j b h hg Q hsize a x using 1
      apply Finset.sum_congr rfl
      intro z _
      by_cases hh : D.nonconflict (flipPos b.1 a) x z <;> simp [P,hh]
    have hprod4 := hprod a 4
    rw [show (0.25:ℝ)+(-0.02)*((4:ℕ):ℝ) = 0.17 by norm_num] at hprod4
    have htw : 2 ≤ (m:ℝ)*D.error (flipPos b.1 a) j ^ 4 := hdiag.trans hprod4
    have hfrac : 1/(m:ℝ) ≤ D.error (flipPos b.1 a) j ^ 4 / 2 := by
      apply (div_le_iff₀ hm').mpr
      nlinarith
    exact hbound.trans (by linarith)
  have htail := R1_tail_from_means D hT j b h hm hmean
  calc
    _ ≤ ∑ a : Fin (T.S.n k), 2 * Real.exp (-(m:ℝ) * D.error (flipPos b.1 a) j ^ 8 / 2) := htail
    _ ≤ ∑ a : Fin (T.S.n k), 2 * Real.exp (-Real.rpow n 0.09 / 2) := by
      apply Finset.sum_le_sum
      intro a _
      have hprod8 := hprod a 8
      norm_num only [Nat.cast_ofNat,show (0.25:ℝ)+(-0.02)*8 = 0.09 by norm_num] at hprod8
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ = 2*n * Real.exp (-Real.rpow n 0.09 / 2) := by simp [n]; ring
    _ ≤ _ := hunion

/-- The slow .04 exponent is uniform after the .09 bounded-difference estimate. -/
theorem numerical_cutoffs (hκ : κ.Admissible) (T : Stage) (K16 : ℝ) :
    ∀ᶠ k in atTop,
      32 * κ.KB * K16 * max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)) ≤
        Real.rpow (densityScale T k) (1-4*κ.β) ∧
      2 ≤ Real.rpow (T.S.n k : ℝ) 0.17 ∧
      2 * (T.S.n k : ℝ) * Real.exp (-Real.rpow (T.S.n k : ℝ) 0.09 / 2) ≤
        Real.exp (-Real.rpow (T.S.n k : ℝ) 0.04) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hC : Tendsto (densityScale T) atTop atTop := by
    change Tendsto (fun k => (T.S.N k : ℝ) / (2:ℝ)^T.S.n k) atTop atTop
    exact T.S.ratio_tendsto
  have hp : 0 < 1-4*κ.β := by have hh := beta_small hκ; linarith
  have hsize := ((tendsto_rpow_atTop hp).comp hC).eventually_ge_atTop
    (32 * κ.KB * K16 * max 1 (Real.exp (Cstar κ.u κ.ξ * κ.Qbd)))
  have hdiag := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 0.17)).comp hn).eventually_ge_atTop 2
  have hslow := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 0.05)).comp hn).eventually
    (Iio_mem_nhds (show (0:ℝ) < 1/4 by norm_num))
  have hx : Tendsto (fun k => (T.S.n k : ℝ) ^ (0.09:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hn
  have hfast0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/0.09:ℝ) (1/4:ℝ) (by norm_num)).comp hx
  have hfast : Tendsto (fun k => 2*(T.S.n k : ℝ) * Real.exp (-Real.rpow (T.S.n k : ℝ) 0.09 / 4)) atTop (nhds 0) := by
    have hh : Tendsto (fun k => 2 * (((T.S.n k : ℝ) ^ (0.09:ℝ)) ^ (1/0.09:ℝ) *
        Real.exp (-(1/4:ℝ) * (T.S.n k : ℝ) ^ (0.09:ℝ)))) atTop (nhds 0) := by
      simpa only [Function.comp_apply,mul_zero] using hfast0.const_mul 2
    apply hh.congr'
    filter_upwards [hn.eventually_gt_atTop 0] with k hk
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hk.le]
    norm_num
    rw [show -((1/4:ℝ) * (T.S.n k : ℝ) ^ (9/100:ℝ)) = -((T.S.n k : ℝ) ^ (9/100:ℝ))/4 by ring]
    ring
  have hfastEvent := hfast.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [hsize,hdiag,hslow,hfastEvent,hn.eventually_gt_atTop 0] with k hs hd hl hf hpos
  refine ⟨hs,hd,?_⟩
  let n : ℝ := T.S.n k
  change Real.rpow n (-0.05) < 1/4 at hl
  have hsmallpow : Real.rpow n 0.04 ≤ Real.rpow n 0.09 / 4 := by
    have hprod : Real.rpow n 0.04 = Real.rpow n (-0.05) * Real.rpow n 0.09 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hpos]
      norm_num
      rfl
    rw [hprod]
    have hpowpos : 0 < Real.rpow n 0.09 := Real.rpow_pos_of_pos hpos _
    have hh := mul_le_mul_of_nonneg_right hl.le hpowpos.le
    nlinarith
  calc
    _ = (2*n*Real.exp (-Real.rpow n 0.09/4)) * Real.exp (-Real.rpow n 0.09/4) := by
      change 2*n*Real.exp (-Real.rpow n 0.09/2) = _
      have he : Real.exp (-Real.rpow n 0.09/2) =
          Real.exp (-Real.rpow n 0.09/4) * Real.exp (-Real.rpow n 0.09/4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ Real.exp (-Real.rpow n 0.09/4) := by
      have he := mul_le_mul_of_nonneg_right hf.le (Real.exp_nonneg (-Real.rpow n 0.09/4))
      simpa only [one_mul] using he
    _ ≤ Real.exp (-Real.rpow n 0.04) := Real.exp_le_exp.mpr (by linarith)

end HypercubeRamsey.Lane_sol_s18_n1_sketch
