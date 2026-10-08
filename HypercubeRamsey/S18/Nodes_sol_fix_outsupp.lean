import HypercubeRamsey.S18.Nodes_sol_s18_2lm
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.S18.Lane_sol_fix_outsupp

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

private theorem degree_bounds {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (U : Law N) (x : Fin N) :
    0 ≤ deg E c U.w x ∧ deg E c U.w x ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun y _ => mul_nonneg (U.nonneg y)
      (by unfold hit; split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ y, U.w y := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_of_le_one_right (U.nonneg y)
          (by unfold hit; split_ifs <;> norm_num)
      _ = 1 := U.sum_eq_one

private noncomputable def joint {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (U : Law N) (x y : Fin N) : ℝ :=
  ∑ u, U.w u * (if Hits E c x u ∧ Hits E c y u then 1 else 0)

private theorem joint_centered {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (U : Law N) (x y : Fin N) :
    (∑ u, U.w u * hit E c x u * (hit E c y u - deg E c U.w y)) =
      joint E c U x y - deg E c U.w x * deg E c U.w y := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hprod : (∑ u, U.w u * hit E c x u * hit E c y u) = joint E c U x y := by
    apply Finset.sum_congr rfl
    intro u _
    by_cases hx : Hits E c x u <;> by_cases hy : Hits E c y u <;>
      simp [hit, joint, hx, hy]
  rw [hprod]
  rfl

private theorem pair_good {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (U : Law N) (x y : Fin N) {e : ℝ} (he : 0 ≤ e)
    (hx : |deg E c U.w x - 1 / 2| ≤ e)
    (hy : |deg E c U.w y - 1 / 2| ≤ e)
    (hcov : |∑ u, U.w u * hit E c x u * (hit E c y u - deg E c U.w y)| ≤ 6 * e) :
    |joint E c U x y - 1 / 4| ≤ 10 * e := by
  have hxb := degree_bounds E c U x
  have habsx : |deg E c U.w x| ≤ 1 := by simpa [abs_of_nonneg hxb.1] using hxb.2
  have hp : |deg E c U.w x * deg E c U.w y - 1 / 4| ≤ e + e / 2 := by
    calc
      _ = |deg E c U.w x * (deg E c U.w y - 1 / 2) +
          (deg E c U.w x - 1 / 2) / 2| := by congr 1; ring
      _ ≤ |deg E c U.w x| * |deg E c U.w y - 1 / 2| +
          |deg E c U.w x - 1 / 2| / 2 := by
        simpa [abs_mul, abs_div] using abs_add_le
          (deg E c U.w x * (deg E c U.w y - 1 / 2)) ((deg E c U.w x - 1 / 2) / 2)
      _ ≤ 1 * e + e / 2 := by gcongr
      _ = e + e / 2 := by ring
  rw [joint_centered] at hcov
  calc
    _ = |(joint E c U x y - deg E c U.w x * deg E c U.w y) +
        (deg E c U.w x * deg E c U.w y - 1 / 4)| := by congr 1; ring
    _ ≤ |joint E c U x y - deg E c U.w x * deg E c U.w y| +
        |deg E c U.w x * deg E c U.w y - 1 / 4| := abs_add_le _ _
    _ ≤ 6 * e + (e + e / 2) := add_le_add hcov hp
    _ ≤ 10 * e := by linarith

/-- Discrepancy for a supported broad output, averaged against any independent
first-side law. The signed test controls the pair covariance. -/
theorem fixed_output_bound
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (U τ : Law (T.S.N k)) (hU : U.SupportedIn (T.Y k))
    (hwidth : U.WidthLE (κ.α * T.S.n k / 2))
    (hmargin : Real.log 3 ≤ κ.α * T.S.n k / 2)
    (hτ : τ.SupportedIn (T.X k)) {w : ℝ} (hτwidth : τ.WidthLE w) :
    (τ.expect (fun x => if 10 * bstar T k <
      |deg (T.S.E k) PT.tiling.c U.w x - 1 / 2| then 1 else 0) ≤
        8 * Real.exp (w - Real.rpow (T.S.n k : ℝ) κ.xs)) ∧
    (τ.expect (fun x => τ.expect (fun y => if 10 * bstar T k <
      |joint (T.S.E k) PT.tiling.c U x y - 1 / 4| then 1 else 0)) ≤
        8 * Real.exp (w - Real.rpow (T.S.n k : ℝ) κ.xs)) := by
  let q := fun x => deg (T.S.E k) PT.tiling.c U.w x
  let cov := fun x y => ∑ u, U.w u * hit (T.S.E k) PT.tiling.c x u *
    (hit (T.S.E k) PT.tiling.c y u - q y)
  let B := fun x => bstar T k < |q x - 1 / 2|
  let C := fun x y => 6 * bstar T k < |cov x y|
  let A := Real.exp (w - Real.rpow (T.S.n k : ℝ) κ.xs)
  have he : 0 ≤ bstar T k := by unfold bstar; positivity
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hwide := hwidth.mono (show κ.α * T.S.n k / 2 ≤ κ.α * T.S.n k by linarith)
  have hsigned := hwidth.mono (show κ.α * T.S.n k / 2 ≤
      κ.α * T.S.n k - Real.log 3 by linarith)
  have hdeg : τ.expect (fun x => if B x then 1 else 0) ≤ 2 * A := by
    have hh := S15.Needs.exceptional_first hdisc PT.tiling.c
      (Or.inr ⟨le_rfl, le_rfl⟩) U τ hU hwide hτ hτwidth
    simpa only [FinProb.expect, B, q, Finset.sum_filter, mul_ite, mul_one, mul_zero] using hh
  have hc (x) : τ.expect (fun y => if C x y then 1 else 0) ≤ 4 * A := by
    have hh := S15.Needs.exceptional_signed hdisc PT.tiling.c
      (Or.inr ⟨le_rfl, le_rfl⟩) U hU hsigned
      (fun u => hit (T.S.E k) PT.tiling.c x u)
      (by intro u; unfold hit; split_ifs <;> norm_num) τ hτ hτwidth
    simpa only [FinProb.expect, C, cov, q, Finset.sum_filter, mul_ite, mul_one, mul_zero] using hh
  constructor
  · have hm : τ.expect (fun x => if 10 * bstar T k < |q x - 1 / 2| then 1 else 0) ≤
        τ.expect (fun x => if B x then 1 else 0) := by
      apply FinProb.expect_mono
      intro x
      by_cases hx : 10 * bstar T k < |q x - 1 / 2|
      · have hb : B x := by dsimp [B]; linarith
        rw [if_pos hx, if_pos hb]
      · rw [if_neg hx]; split_ifs <;> norm_num
    exact hm.trans (hdeg.trans (by
      have hA : 0 ≤ A := (Real.exp_pos _).le
      nlinarith))
  · have hpoint (x y) :
        (if 10 * bstar T k < |joint (T.S.E k) PT.tiling.c U x y - 1 / 4| then (1 : ℝ) else 0) ≤
          (if B x then 1 else 0) + (if B y then 1 else 0) + (if C x y then 1 else 0) := by
      by_cases hx : B x <;> by_cases hy : B y <;> by_cases hc : C x y
      all_goals try { simp [hx, hy, hc]; split_ifs <;> norm_num }
      have hg := pair_good (T.S.E k) PT.tiling.c U x y he
        (le_of_not_gt hx) (le_of_not_gt hy) (le_of_not_gt hc)
      simp only [not_lt_of_ge hg, ↓reduceIte, hx, hy, hc]
      norm_num
    have hm := FinProb.expect_mono τ (fun x => FinProb.expect_mono τ (hpoint x))
    have hcov : τ.expect (fun x => τ.expect (fun y => if C x y then 1 else 0)) ≤ 4 * A := by
      calc
        _ ≤ τ.expect (fun _ => 4 * A) := FinProb.expect_mono τ hc
        _ = 4 * A := FinProb.expect_const _ _
    simp_rw [FinProb.expect_add, FinProb.expect_const] at hm
    have hnum : τ.expect (fun x => if B x then 1 else 0) +
        τ.expect (fun x => if B x then 1 else 0) +
        τ.expect (fun x => τ.expect (fun y => if C x y then 1 else 0)) ≤ 8 * A := by
      linarith
    exact hm.trans hnum

/-- A uniform patch witness has sub-discrepancy width. The bounded-mode
mass lower bound supplies the constant term. -/
theorem patch_log_width (hκ : κ.Admissible) (hPT : PT.Valid) (hn : 1 ≤ (T.S.n k : ℝ))
    (i : Fin PT.tiling.m) :
    Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
      Real.log 400 + (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι := by
  have hM : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1
  have hN : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
  have hp : 0 ≤ Real.rpow (T.S.n k : ℝ) κ.ι := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlog : 0 ≤ Real.log 400 := Real.log_nonneg (by norm_num)
  by_cases hb : PT.tiling.mode = .bounded
  · have hmass := ((hPT.tiling_valid.bounded_data hb).2 i).2.2.2.1
    have hratio : (T.S.N k : ℝ) / (PT.tiling.P i).M ≤ 400 := by
      apply (div_le_iff₀ hM).2
      linarith
    have hnonneg : 0 ≤ (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι :=
      mul_nonneg (by positivity) hp
    exact (Real.log_le_log (div_pos hN hM) hratio).trans (by linarith)
  · have hd (hm : PT.tiling.mode = .lowDirect ∨ PT.tiling.mode = .highDirect) :
        PT.tiling.gain i ≤ Real.rpow (T.S.n k : ℝ) κ.ι := by
      have hg := hPT.tiling_valid.direct_scale_bound hm i
      have hpow := Real.rpow_le_rpow_of_exponent_le hn
        (show κ.ι / 2 ≤ κ.ι by linarith [hκ.ι_rng.1])
      have heq : PT.tiling.gain i = (PT.tiling.P i).g / 1000 := by
        rcases hm with hm | hm <;> simp [Tiling.gain, hm]
      rw [heq]
      calc
        _ ≤ ((PT.tiling.P i).g : ℝ) := div_le_self (by positivity) (by norm_num)
        _ ≤ _ := hg.trans hpow
    have hc (hm : PT.tiling.mode = .lowCluster ∨ PT.tiling.mode = .highSmall ∨
        PT.tiling.mode = .highLarge) :
        PT.tiling.gain i ≤ |κ.a| * Real.rpow (T.S.n k : ℝ) κ.ι := by
      have hh : ((PT.tiling.P i).h : ℝ) ≤ Real.rpow (T.S.n k : ℝ) κ.ι :=
        (show ((PT.tiling.P i).h : ℝ) ≤ (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ)
          by exact_mod_cast le_max_left (PT.tiling.P i).h (PT.tiling.P i).ℓ).trans
            (hPT.tiling_valid.allocation_bounds i).1.le
      have heq : PT.tiling.gain i = κ.a * (PT.tiling.P i).h / 10 ^ 6 := by
        rcases hm with hm | hm | hm <;> simp [Tiling.gain, hm]
      rw [heq]
      have ha := mul_le_mul_of_nonneg_right (le_abs_self κ.a)
        (show (0 : ℝ) ≤ (PT.tiling.P i).h by positivity)
      have hh' := mul_le_mul_of_nonneg_left hh (abs_nonneg κ.a)
      have hprod := mul_nonneg (abs_nonneg κ.a)
        (show (0 : ℝ) ≤ (PT.tiling.P i).h by positivity)
      nlinarith
    have hgain : PT.tiling.gain i ≤ (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι := by
      cases hm : PT.tiling.mode with
      | bounded => exact (hb hm).elim
      | lowDirect => have hh := hd (Or.inl hm); nlinarith [mul_nonneg (abs_nonneg κ.a) hp]
      | highDirect => have hh := hd (Or.inr hm); nlinarith [mul_nonneg (abs_nonneg κ.a) hp]
      | lowCluster => have hh := hc (Or.inl hm); nlinarith
      | highSmall => have hh := hc (Or.inr (Or.inl hm)); nlinarith
      | highLarge => have hh := hc (Or.inr (Or.inr hm)); nlinarith
    obtain ⟨hmode, halloc⟩ := hPT.tiling_valid.allocation_bounds i
    rcases halloc with hbad | ⟨_, halloc⟩
    · exact (hb hbad).elim
    have hu : (1 : ℝ) ≤ κ.u := by
      exact_mod_cast (show 1 ≤ κ.u by have := hκ.u_rng.2; omega)
    have hdiv : PT.tiling.gain i / (1000 * (κ.u : ℝ)) ≤
        (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (κ.u : ℝ))).2
      have hm := mul_le_mul_of_nonneg_left
        (show (1 : ℝ) ≤ 1000 * (κ.u : ℝ) by linarith)
        (mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + |κ.a|) hp)
      exact hgain.trans (by simpa only [mul_one] using hm)
    exact halloc.trans (hdiv.trans (by linarith))

private theorem uniform_expect {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty)
    (f : Fin N → ℝ) :
    (Law.unif A hA).expect f = (∑ x ∈ A, f x) / A.card := by
  simp only [FinProb.expect, Law.unif, FinProb.uniform, ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

/-- The fixed-output estimate with uniform witnesses on the target patch.
The allowed-witness restriction only decreases this mean. -/
theorem supported_output_witness_bound (hκ : κ.Admissible)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hn : 1 ≤ (T.S.n k : ℝ)) (hmargin : Real.log 3 ≤ κ.α * T.S.n k / 2)
    (U : Law (T.S.N k)) (hU : U.SupportedIn (T.Y k))
    (hwidth : U.WidthLE (κ.α * T.S.n k / 2)) (pair : Bool) :
    witnessMean X pair (fun x z => if X.allowed x z ∧ X.deviates U x z then 1 else 0) ≤
      8 * Real.exp (Real.log 400 + (1 + |κ.a|) *
        Real.rpow (T.S.n k : ℝ) κ.ι - Real.rpow (T.S.n k : ℝ) κ.xs) := by
  let i := D.geom.patchOf X.target
  let τ := Law.unif (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
  let W := Real.log 400 + (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι
  have hτ : τ.SupportedIn (T.X k) := by
    intro x hx
    have hx' : x ∉ (PT.tiling.P i).X := by
      intro hh
      exact hx (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1
        ((hPT.tiling_valid.patch_supports i).1 hh))).1
    simp [τ, Law.unif, FinProb.uniform, hx']
  have hτwidth : τ.WidthLE W := by
    have hh := Law.uniform_width (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
    change (Law.unif (PT.tiling.P i).X _).WidthLE _ at hh
    rw [(PT.tiling.P i).cardX] at hh
    exact hh.mono (patch_log_width hκ hPT hn i)
  obtain ⟨hs, hp⟩ := fixed_output_bound (PT := PT) hdisc U τ hU hwidth hmargin hτ hτwidth
  have hmean := Lane_sol_s18_2lm.witnessMean_mono (X := X) pair
    (fun x z => if X.allowed x z ∧ X.deviates U x z then 1 else 0)
    (fun x z => if X.deviates U x z then 1 else 0) (by
      intro x z
      by_cases ha : X.allowed x z <;> by_cases hd : X.deviates U x z <;> simp [ha, hd])
  apply hmean.trans
  simp only [τ, uniform_expect, (PT.tiling.P i).cardX] at hs hp
  simp only [← Finset.sum_div, div_div, ← pow_two] at hp
  cases pair with
  | false => simpa only [witnessMean, Bool.false_eq_true, ↓reduceIte,
      CriticalTransferData.deviates, rowDeg, deg, hit, i, W] using hs
  | true => simpa only [witnessMean, ↓reduceIte, CriticalTransferData.deviates, joint, i, W] using hp

private theorem witnessMean_expect {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (pair : Bool) (f : Fin (T.S.N k) → Option (Fin (T.S.N k)) → Ω → ℝ) :
    witnessMean X pair (fun x z => Q.E (f x z)) =
      Q.E (fun s => witnessMean X pair (fun x z => f x z s)) := by
  cases pair <;> simp only [witnessMean, Bool.false_eq_true, ↓reduceIte, FinLaw.E]
  all_goals simp_rw [Finset.sum_comm
    (s := (PT.tiling.P (D.geom.patchOf X.target)).X) (t := (Finset.univ : Finset Ω))]
  all_goals simp_rw [← Finset.mul_sum]
  all_goals rw [Finset.sum_div]
  all_goals simpa only [mul_div_assoc]

/-- Output can depend on the raw state, while witnesses are averaged
independently. Exchange these two finite averages before applying discrepancy. -/
theorem raw_output_bound (hκ : κ.Admissible)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs)
      (κ.α * T.S.n k) (bstar T k))
    (hn : 1 ≤ (T.S.n k : ℝ)) (hmargin : Real.log 3 ≤ κ.α * T.S.n k / 2)
    (P : TransferProtocol X) (seed : P.Seed) (pair : Bool) :
    witnessMean X pair (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) ≤
      8 * Real.exp (Real.log 400 + (1 + |κ.a|) *
        Real.rpow (T.S.n k : ℝ) κ.ι - Real.rpow (T.S.n k : ℝ) κ.xs) := by
  let f := fun x z s => if X.allowed x z ∧
    X.deviates (P.output seed (P.replies seed s P.steps)) x z then (1 : ℝ) else 0
  have heq : (fun x z => if X.allowed x z then X.rawLaw.pr (fun s =>
      X.deviates (P.output seed (P.replies seed s P.steps)) x z) else 0) =
      (fun x z => X.rawLaw.E (f x z)) := by
    funext x z
    by_cases ha : X.allowed x z <;>
      simp [f, ha, FinLaw.E, FinLaw.pr, mul_ite]
  rw [heq, witnessMean_expect]
  let B := 8 * Real.exp (Real.log 400 + (1 + |κ.a|) *
    Real.rpow (T.S.n k : ℝ) κ.ι - Real.rpow (T.S.n k : ℝ) κ.xs)
  calc
    _ ≤ X.rawLaw.E (fun _ => B) := by
      unfold FinLaw.E
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (X.rawLaw.nonneg s)
      exact supported_output_witness_bound hκ hdisc hn hmargin
        (P.output seed (P.replies seed s P.steps)) (P.output_supported seed s) (P.broad seed s) pair
    _ = B := by simp [FinLaw.E, ← Finset.sum_mul, X.rawLaw.sum_one]

/-- The patch width and the tilt amplification have lower powers than the
small discrepancy budget. All constants and the tilt exponent precede k. -/
theorem parameters_eventually (hκ : κ.Admissible) (T : Stage) (c : ℝ)
    (hcx : c < κ.xs / 4) :
    ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) ∧
      Real.log 3 ≤ κ.α * T.S.n k / 2 ∧
      8 * Real.exp (Real.log 400 + (1 + |κ.a|) *
        Real.rpow (T.S.n k : ℝ) κ.ι - Real.rpow (T.S.n k : ℝ) κ.xs) ≤
        Real.exp (-2 * Real.rpow (T.S.n k : ℝ) c) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hιxs : κ.ι < κ.xs := by
    have hi := hκ.ι_rng.2
    have hm := min_le_left κ.xs (min κ.η0 (0.01 : ℝ))
    linarith [hκ.xs_rng.1]
  have hcxs : c < κ.xs := by linarith [hκ.xs_rng.1]
  have hnum := hn.eventually (Lane_sol_consts_adm.eventually_power_sum
    κ.ι c κ.xs (1 + |κ.a|) 2 (Real.log 400 + Real.log 8) 1
    hιxs hcxs hκ.xs_rng.1 (by norm_num))
  filter_upwards [hn.eventually_ge_atTop 1,
    hn.eventually_ge_atTop (2 * Real.log 3 / κ.α), hnum] with k hn1 hα hnum
  refine ⟨hn1, ?_, ?_⟩
  · have hh := (div_le_iff₀ hκ.α_rng.1).mp hα
    linarith
  · calc
      _ = Real.exp (Real.log 8 + (Real.log 400 + (1 + |κ.a|) *
          Real.rpow (T.S.n k : ℝ) κ.ι - Real.rpow (T.S.n k : ℝ) κ.xs)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        simp only [Real.rpow_eq_pow] at hnum ⊢
        linarith only [hnum])

end HypercubeRamsey.S18.Lane_sol_fix_outsupp
