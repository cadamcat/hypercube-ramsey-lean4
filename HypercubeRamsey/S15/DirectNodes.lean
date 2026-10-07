import HypercubeRamsey.S15.Defs
import HypercubeRamsey.S15.DirectNodes_q_s15_direct
import HypercubeRamsey.S15.DirectNodes_sol_s15_bulk
import HypercubeRamsey.S15.DirectNodes_sol_s15_cross

set_option maxHeartbeats 1000000

/-! L15.1: direct assignment, its mass gates, and its column estimate. -/

namespace HypercubeRamsey.S15

open HypercubeRamsey Filter
open scoped BigOperators

/-- L15.1a (15:21–22): crossing filters preserve the direct row mass. -/
def DirectCrossingClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hmode : PT.tiling.mode = .highDirect, ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys =>
        |directCrossingMass PT hPT ys a - 1| >
          Real.exp (20 * (PT.tiling.P (patchAt PT hPT a.1)).ℓ * bstar T k) - 1) ≤
          (T.S.n k : ℝ) ^ (-(κ.R : ℝ))

/-- L15.1b (15:23–31): the post-crossing bulk law has a lower-tail bound. -/
def DirectBulkClaim (κ : CConsts) (T : Stage) : Prop :=
  ∃ Cbulk : ℝ, 0 < Cbulk ∧
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hmode : PT.tiling.mode = .highDirect, ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys =>
        9 / 10 ≤ directCrossingMass PT hPT ys a ∧
          directBulkMass PT hPT ys a < 3 / 4) ≤
            4 ^ κ.u * ((T.S.n k : ℝ) ^ (-((3 * κ.R : ℕ) : ℝ)) +
              Cbulk * Real.exp (-200 * PT.tiling.gain (patchAt PT hPT a.1)))

/-- L15.1c (15:19, 31): full independent row mass is at least one half except with probability `n^-R`. -/
def DirectMassClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hmode : PT.tiling.mode = .highDirect, ∀ a : EvenPosition T k,
      (directRawLaw PT hPT).pr (fun ys => directRowMass PT hPT ys a < 1 / 2) ≤
        (T.S.n k : ℝ) ^ (-(κ.R : ℝ))

/-- L15.1f output: the direct row formula normalizes to a fractional Hall system. -/
structure DirectCertificate {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) where
  sampler : DirectSampler PT hPT
  labels : OddAssignment T k
  positive : sampler.law.w labels ≠ 0
  rows : DirectHallRows (T := T) (k := k) PT.tiling.c
  labels_eq : rows.oddLabel = labels
  row_eq : rows.row = fun a x => directNormalizedRow PT hPT labels a x

/-- L15.1d (15:33–34): the clock sampler avoids every direct row mass failure and is injective. -/
def DirectSamplerClaim (κ : CConsts) (T : Stage) (hDeep : DeepDisc T κ.xs κ.α 0.04) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ (hmode : PT.tiling.mode = .highDirect), Nonempty (DirectSampler PT hPT)

/-- L15.1e (15:36): the `n`th patch-column moment under the clock law is uniformly bounded. -/
def DirectMomentClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ (hmode : PT.tiling.mode = .highDirect), ∀ J : DirectSampler PT hPT,
      ∀ i x, x ∈ PT.envelope i →
        J.law.E (fun ys =>
          patchColumnAverage PT i (directRowWeight PT hPT) ys x ^ (T.S.n k)) ≤
            κ.A0 ^ (T.S.n k)

/-- L15.1f (15:38–40): one clock outcome has all mass gates and all column loads. -/
def DirectCertificateClaim (κ : CConsts) (T : Stage) : Prop :=
  ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ (hmode : PT.tiling.mode = .highDirect), Nonempty (DirectCertificate PT hPT)

/-- L15.1a: the deep-discrepancy crossing-filter estimate. -/
theorem high_direct_crossing_filters (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    DirectCrossingClaim κ T ∧ ClusterCrossingClaim κ T := by
  constructor
  · exact Lane_sol_s15_cross.direct_crossing_bound κ hκ T hDeep
  · sorry

/-- L15.1b: bulk lower-tail estimate, using the crossing-filter stage. -/
theorem high_direct_bulk_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : DirectCrossingClaim κ T) :
    DirectBulkClaim κ T := by
  exact Lane_sol_s15_bulk.bulk_lower_tail κ hκ T hDeep

/-- L15.1c: assemble the crossing and bulk estimates into the independent row-mass bound. -/
theorem high_direct_mass_estimate (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : DirectCrossingClaim κ T)
    (hBulk : DirectBulkClaim κ T) : DirectMassClaim κ T := by
  rcases hBulk with ⟨Cbulk, hCbulk, hBulk⟩
  filter_upwards [hBulk, Lane_sol_s15_bulk.bulk_error_half κ hκ T Cbulk hCbulk,
    Lane_sol_s15_bulk.sharp_direct_crossing_bound κ hκ T hDeep,
    Lane_q_s15_direct.highDirect_cross_threshold_small hκ T] with k hkBulk hkSlack hkCross hkThreshold
  intro PT hPT hmode a
  let i := patchAt PT hPT a.1
  let err : ℝ := (T.S.n k : ℝ) ^ (-(κ.R : ℝ)) / 2
  have hcross := hkCross PT hPT hmode a
  have hbulk : (directRawLaw PT hPT).pr (fun ys =>
      9 / 10 ≤ directCrossingMass PT hPT ys a ∧ directBulkMass PT hPT ys a < 3 / 4) ≤ err :=
    (hkBulk PT hPT hmode a).trans (hkSlack PT hPT hmode i)
  have hmass := Lane_q_s15_direct.row_failure_probability_le (directRawLaw PT hPT)
    (fun ys => directCrossingMass PT hPT ys a)
    (fun ys => directBulkMass PT hPT ys a)
    (fun ys => directRowMass PT hPT ys a)
    (fun _ => Real.exp (20 * (PT.tiling.P i).ℓ * bstar T k) - 1) err err
    (fun _ => rfl) (fun _ => hkThreshold PT hPT hmode i) hcross hbulk
  simpa [err, add_halves] using hmass

/-- L15.1d: apply the clock sampler to the row-failure predicates. -/
theorem high_direct_clock_injection (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hMass : DirectMassClaim κ T) :
    DirectSamplerClaim κ T hDeep := by
  classical
  rcases hκ.clock with ⟨_, hθ0, A', P', n₀, ε, hA, hP, hA_le, hP_le, hn₀, hε, hClock⟩
  let Ccol : ℝ := 8800 / κ.θ0 + 1
  have hHost : ∀ᶠ k in atTop,
      max n₀ 2 ≤ T.S.n k ∧ LargeHost 1 (T.S.n k) (T.S.N k) := by
    exact T.S.eventually_large 1 (max n₀ 2)
  have hRatio : ∀ᶠ k in atTop, Ccol ≤ (T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) := by
    exact T.S.ratio_tendsto.eventually_ge_atTop Ccol
  have hEps : ∀ᶠ k in atTop, ε (T.S.n k) ≤ 1 := by
    have hεcomp : Filter.Tendsto (fun k => ε (T.S.n k)) atTop (nhds 0) :=
      hε.comp T.S.n_tendsto
    exact hεcomp.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hTail : ∀ᶠ k in atTop,
      8800 * Real.exp (-(Real.log 2 / 2) * (T.S.n k : ℝ)) ≤
        (T.S.n k : ℝ) ^ (-A') :=
    T.S.n_tendsto.eventually (HypercubeRamsey.Lane_q_s15_direct.eventually_two_pow_tail A' hA)
  have hPnat : 1 ≤ κ.P := by
    have hp := hκ.P_big.2
    rw [hκ.Ac_eq] at hp
    norm_num at hp
    omega
  have hPtoR : (κ.P : ℝ) ≤ κ.R := by
    have hnat : κ.P ≤ κ.P ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_self κ.P
    rw [hκ.R_eq]
    exact_mod_cast hnat
  have hPstar : (κ.Pstar : ℝ) ≤ κ.P := by exact_mod_cast hκ.P_big.1
  have hPexp : P' ≤ (κ.R : ℝ) := by
    exact le_trans hP_le (le_trans hPstar hPtoR)
  have htheta_pos : 0 < κ.θ0 := by rw [hθ0]; norm_num
  filter_upwards [hMass, hHost, hRatio, hEps, hTail] with k hmass hhost hratio hεsmall htail
  intro PT hPT hmode
  let n := T.S.n k
  let N := T.S.N k
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hhost.1
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hhost.1
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast T.S.N_pos k
  have hnRpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hNpow : (2 : ℝ) ^ n ≤ (N : ℝ) := by
    have h := hhost.2.1
    change (1 : ℝ) * (2 : ℝ) ^ n ≤ (N : ℝ) at h
    nlinarith
  have hnPow5 : (n : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
    calc
      (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1 : ℝ) ≤ (5 : ℝ))
  have honePow5 : (1 : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
    calc
      (1 : ℝ) = (n : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (n : ℝ) ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (0 : ℝ) ≤ (5 : ℝ))
  have honePow5Nat : (1 : ℝ) ≤ (n : ℝ) ^ (5 : ℕ) := by
    simpa [Real.rpow_natCast] using honePow5
  have hNupper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by
    exact_mod_cast hhost.2.2
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hnRpos.le
  have hlogN : Real.log (N : ℝ) ≤ 2 * (n : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ Real.log ((n : ℝ) * (2 : ℝ) ^ n) :=
        Real.log_le_log hNpos hNupper
      _ = Real.log (n : ℝ) + (n : ℝ) * Real.log (2 : ℝ) := by
        rw [Real.log_mul hnRpos.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
      _ ≤ (n : ℝ) + (n : ℝ) := by
        apply add_le_add hlogn
        calc
          (n : ℝ) * Real.log (2 : ℝ) ≤ (n : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hlog2 hnRpos.le
          _ = (n : ℝ) := by ring
      _ = 2 * (n : ℝ) := by ring
  let Ω : OddPosition T k → Type := fun _ => Fin N
  have hNnat : 0 < N := T.S.N_pos k
  have hΩnonempty : ∀ b : OddPosition T k, Nonempty (Ω b) := fun _ => ⟨⟨0, hNnat⟩⟩
  letI : ∀ b : OddPosition T k, Nonempty (Ω b) := hΩnonempty
  let laws : ∀ b : OddPosition T k, FinProb (Ω b) := fun b => lawAtOdd PT hPT b
  let lab : ∀ b : OddPosition T k, Ω b → Fin N := fun _ y => y
  let Bad : EvenPosition T k → (∀ b : OddPosition T k, Ω b) → Prop := fun a ys =>
    directRowMass PT hPT ys a < 1 / 2
  let scope : EvenPosition T k → Finset (OddPosition T k) :=
    fun a => Lane_q_s15_direct.star a
  have hMarg (b : OddPosition T k) (y : Fin N) :
      labMarg (laws b) (lab b) y = (laws b).w y := by
    classical
    unfold labMarg
    simp only [lab]
    rw [Finset.sum_ite_eq']
    simp
  have hcol : ∀ y, ∑ b, labMarg (laws b) (lab b) y ≤ κ.θ0 := by
    intro y
    calc
      ∑ b, labMarg (laws b) (lab b) y = ∑ b, (laws b).w y := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hMarg b y
      _ ≤ 8800 * (2 : ℝ) ^ n / N :=
        Lane_q_s15_direct.direct_marginal_column_bound PT hPT y
      _ ≤ κ.θ0 := by
        have hratio0 : 8800 / κ.θ0 ≤ (N : ℝ) / (2 : ℝ) ^ n := by
          dsimp [Ccol] at hratio
          linarith
        have h1 : 8800 ≤ κ.θ0 * ((N : ℝ) / (2 : ℝ) ^ n) := by
          calc
            8800 = κ.θ0 * (8800 / κ.θ0) := by field_simp [ne_of_gt htheta_pos]
            _ ≤ κ.θ0 * ((N : ℝ) / (2 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left hratio0 (le_of_lt htheta_pos)
        have h2 : 8800 * (2 : ℝ) ^ n ≤ κ.θ0 * N := by
          calc
            8800 * (2 : ℝ) ^ n ≤
                (κ.θ0 * ((N : ℝ) / (2 : ℝ) ^ n)) * (2 : ℝ) ^ n :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = κ.θ0 * N := by field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
        exact (div_le_iff₀ hNpos).2 h2
  have hAtoms : ∀ b y, labMarg (laws b) (lab b) y ≤ (n : ℝ) ^ (-A') := by
    intro b y
    have hlabel := hMarg b y
    rw [hlabel]
    have hprefix := Lane_q_s15_direct.highDirect_prefix_le_half PT hPT hκ hmode
      (by omega : 1 ≤ n) (patchAt PT hPT b.1)
    have hprefixRatio := Lane_q_s15_direct.prefix_ratio_le_exp hprefix hNpow
    calc
      (laws b).w y ≤ 8800 * (2 : ℝ) ^
          ((PT.tiling.P (patchAt PT hPT b.1)).ℓ) / N :=
        Lane_q_s15_direct.direct_atom_bound PT hPT b y
      _ ≤ 8800 * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) := by
        calc
          _ = 8800 * ((2 : ℝ) ^
              ((PT.tiling.P (patchAt PT hPT b.1)).ℓ) / N) := by ring
          _ ≤ 8800 * Real.exp (-(Real.log 2 / 2) * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (by simpa [n] using hprefixRatio)
              (by norm_num : (0 : ℝ) ≤ 8800)
      _ ≤ (n : ℝ) ^ (-A') := htail
  have hfail : ∀ a, (FinProb.pi laws).pr (Bad a) ≤ (n : ℝ) ^ (-P') := by
    intro a
    have hweight (ys : OddAssignment T k) :
        (FinProb.pi laws).w ys = (directRawLaw PT hPT).w ys := by
      simp [FinProb.pi, directRawLaw, FinLaw.pi, lawToFinLaw, laws]
    have hprEq : (FinProb.pi laws).pr (Bad a) =
        (directRawLaw PT hPT).pr (fun ys => directRowMass PT hPT ys a < 1 / 2) := by
      unfold FinProb.pr FinLaw.pr
      apply Finset.sum_congr rfl
      intro ys hys
      by_cases hbad : directRowMass PT hPT ys a < 1 / 2 <;>
        simp [Bad, hbad, hweight]
    have hm := hmass PT hPT hmode a
    calc
      (FinProb.pi laws).pr (Bad a) =
          (directRawLaw PT hPT).pr (fun ys => directRowMass PT hPT ys a < 1 / 2) := hprEq
      _ ≤ (n : ℝ) ^ (-(κ.R : ℝ)) := hm
      _ ≤ (n : ℝ) ^ (-P') :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hdep : ∀ a, FinProb.DependsOn (Bad a) (scope a) := by
    intro a ys ys' hsame
    change (directRowMass PT hPT ys a < 1 / 2) =
      (directRowMass PT hPT ys' a < 1 / 2)
    apply congrArg (fun z : ℝ => z < 1 / 2)
    exact Lane_q_s15_direct.directRowMass_dependsOn PT hPT a ys ys' hsame
  have hscope : ∀ a, ((scope a).card : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
    intro a
    have hcard : ((scope a).card : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Lane_q_s15_direct.star_card_le a
    exact hcard.trans hnPow5
  have hinc : ∀ b, ((Finset.univ.filter fun a : EvenPosition T k => b ∈ scope a).card : ℝ) ≤
      (n : ℝ) ^ (5 : ℝ) := by
    intro b
    have hcard : ((Finset.univ.filter fun a : EvenPosition T k => b ∈ scope a).card : ℝ) ≤
        (n : ℝ) := by
      change ((Lane_q_s15_direct.starIncidence b).card : ℝ) ≤ (n : ℝ)
      exact_mod_cast Lane_q_s15_direct.star_incidence_card_le b
    exact hcard.trans hnPow5
  have hRnonempty : Nonempty (OddPosition T k) := by
    let v : Position T k := fun _ => false
    have hv : IsEvenRole v := by simp [IsEvenRole, v]
    let j : Fin n := ⟨0, by omega⟩
    let w := cubeFlip v j
    have hw : ¬ IsEvenRole w := by
      intro hw
      have hnot := (cubeFlip_parity v j).mp hw
      exact hnot hv
    exact ⟨⟨w, hw⟩⟩
  letI : Nonempty (OddPosition T k) := hRnonempty
  have hclockOut := hClock n hn0 N hlogN lab laws Bad scope hcol hAtoms hdep hscope hinc hfail
  obtain ⟨J, hGood, hComp⟩ := hclockOut
  have hrawWeight (ys : OddAssignment T k) :
      (FinProb.pi laws).w ys = (directRawLaw PT hPT).w ys := by
    simp [FinProb.pi, directRawLaw, FinLaw.pi, lawToFinLaw, laws]
  have hrawExp (F : OddAssignment T k → ℝ) :
      (FinProb.pi laws).expect F = (directRawLaw PT hPT).E F := by
    unfold FinProb.expect FinLaw.E
    apply Finset.sum_congr rfl
    intro ys hys
    rw [hrawWeight]
  have hsampler : DirectSampler PT hPT := by
    refine {
      rawLaw := directRawLaw PT hPT
      rawLaw_eq := rfl
      law := ⟨J.w, J.nonneg, J.sum_eq_one⟩
      local_upper_comparison := ?_
      label_supported := ?_
      injective_on_support := ?_
      row_mass_gate := ?_ }
    · intro F hF S hdepF hS
      have hlocal := Lane_q_s15_direct.expect_le_of_cylinder hΩnonempty J laws S F (1 + ε n)
        hF hdepF (fun o => hComp S o (by simpa [Real.rpow_natCast] using hS))
      have hrawNonneg : 0 ≤ (directRawLaw PT hPT).E F := by
        unfold FinLaw.E
        apply Finset.sum_nonneg
        intro ys hys
        exact mul_nonneg ((directRawLaw PT hPT).nonneg ys) (hF ys)
      calc
        (⟨J.w, J.nonneg, J.sum_eq_one⟩ : FinLaw (OddAssignment T k)).E F = J.expect F := rfl
        _ ≤ (1 + ε n) * (FinProb.pi laws).expect F := hlocal
        _ = (1 + ε n) * (directRawLaw PT hPT).E F := by rw [hrawExp]
        _ ≤ 2 * (directRawLaw PT hPT).E F :=
          mul_le_mul_of_nonneg_right (by linarith [hεsmall]) hrawNonneg
    · intro ys hys b
      by_contra hnot
      have hscard : (({b} : Finset (OddPosition T k)).card : ℝ) ≤ (n : ℝ) ^ (5 : ℝ) := by
        simpa [Real.rpow_natCast] using honePow5Nat
      have hupper := hComp {b} ys hscard
      have hzero : (laws b).w (ys b) = 0 := by
        apply hPT.law_supported (patchAt PT hPT b.1)
        exact hnot
      have hprob : J.pr (fun z => ∀ c ∈ ({b} : Finset (OddPosition T k)), z c = ys c) ≤ 0 := by
        calc
          _ ≤ (1 + ε n) * ∏ c ∈ ({b} : Finset (OddPosition T k)), (laws c).w (ys c) := hupper
          _ = 0 := by simp [hzero]
      have hpoint : J.w ys ≤
          J.pr (fun z => ∀ c ∈ ({b} : Finset (OddPosition T k)), z c = ys c) :=
        Lane_q_s15_direct.weight_le_pr J
          (fun z => ∀ c ∈ ({b} : Finset (OddPosition T k)), z c = ys c) ys (by simp)
      exact (not_le_of_gt (lt_of_le_of_ne (J.nonneg ys) (Ne.symm hys)))
        (le_trans hpoint hprob)
    · intro ys hys
      obtain ⟨hinj, _⟩ := hGood ys hys
      intro b' b'' hEq
      have hlabels : lab b' (ys b') = lab b'' (ys b'') := by simpa [lab] using hEq
      exact hinj hlabels
    · intro ys hys a
      have hgood := hGood ys hys
      exact le_of_not_gt (hgood.2 a)
  exact ⟨hsampler⟩

/-- L15.1e: scattered-moment estimate under any clock sampler from L15.1d. -/
theorem high_direct_column_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hSampler : DirectSamplerClaim κ T hDeep) :
    DirectMomentClaim κ T := by
  classical
  have hPpos : 0 < κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    omega
  have hRpos : 0 < κ.R := by
    rw [hκ.R_eq]
    exact Nat.pow_pos hPpos
  have hA0 : 12 ≤ κ.A0 := by
    have h := hκ.A0_big
    have hR : 1 ≤ (κ.R : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hRpos.ne')
    nlinarith
  have hcapClaim := Lane_q_s15_direct.highDirect_row_weight_cap_claim κ hκ T
  have hslackClaim := Lane_q_s15_direct.highDirect_scattered_slack (κ := κ) hκ T
  have hNlarge : ∀ᶠ k : ℕ in atTop, 3 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (eventually_ge_atTop 3)
  have hbstarSmall : ∀ᶠ k : ℕ in atTop, 3 * bstar T k ≤ 1 / 4 := by
    have hlim : Filter.Tendsto (fun k : ℕ =>
        (T.S.n k : ℝ) ^ (-(0.96 : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp
        (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
    have hsmall := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12))
    filter_upwards [hsmall] with k hk
    have hk' : (T.S.n k : ℝ) ^ (-1 + (0.04 : ℝ)) < 1 / 12 := by
      convert hk using 1 <;> norm_num
    have hb : bstar T k < 1 / 12 := by simpa [bstar] using hk'
    nlinarith
  filter_upwards [hcapClaim, hslackClaim, hNlarge, hbstarSmall]
    with k hcap hslack hn hbstar
  intro PT hPT hmode J i x hx
  let E := evenPatchPositions PT.tiling i
  let U := {a : EvenPosition T k // a ∈ E}
  let n := T.S.n k
  let nR : ℝ := n
  let M := (PT.tiling.P i).M
  let succ : Finset (OddAssignment T k) :=
    Finset.univ.filter fun ys => J.law.w ys ≠ 0
  let stats : U → OddAssignment T k → ℝ := fun a ys =>
    (M : ℝ) * directRowWeight PT hPT ys a.1 x
  let d : U → ℝ := fun _ => 1
  let near : U → Finset U := fun a => Lane_q_s15_direct.starNearWithin E a
  let f : ℝ := nR ^ 2 / (Fintype.card U : ℝ)
  let L : ℝ := (2 : ℝ) ^ n * Real.exp (-200 * PT.tiling.gain i)
  have hn : 0 < n := by omega
  have hleHalf := Lane_q_s15_direct.highDirect_prefix_le_half PT hPT hκ hmode
    (by omega) i
  have hEllLt : (PT.tiling.P i).ℓ < n := by omega
  have hEcard := Lane_q_s15_direct.evenPatchPositions_card_eq PT i hEllLt
  have hEpos : 0 < E.card := by rw [hEcard]; positivity
  have hUcard : Fintype.card U = E.card := by
    dsimp [U]
    exact Fintype.card_coe E
  have hUpos : 0 < (Fintype.card U : ℝ) := by
    rw [hUcard]
    exact_mod_cast hEpos
  have hUnonempty : Nonempty U := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hEpos
    exact ⟨⟨a, ha⟩⟩
  letI : Nonempty U := hUnonempty
  have hself : ∀ a : U, a ∈ near a := by
    intro a
    exact Lane_q_s15_direct.self_mem_starNearWithin E a (by omega)
  have hnearCard : ∀ a : U, ((near a).card : ℝ) ≤ nR ^ 2 := by
    intro a
    have hcard := Lane_q_s15_direct.starNearWithin_card_le_sq E a
    have hcard' : ((near a).card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard
    simpa [nR, n] using hcard'
  have hf : 0 ≤ f := by positivity [f]
  have hnear : ∀ a : U, ((near a).card : ℝ) ≤ f * Fintype.card U := by
    intro a
    have hratio : f * (Fintype.card U : ℝ) = nR ^ 2 := by
      dsimp [f]
      field_simp [ne_of_gt hUpos]
    exact le_trans (hnearCard a) hratio.symm.le
  have hL : 0 ≤ L := by positivity [L]
  have hZ0 : ∀ a ys, 0 ≤ stats a ys := by
    intro a ys
    exact mul_nonneg (by positivity)
      (Lane_q_s15_direct.directRowWeight_nonneg PT hPT ys a.1 x)
  have hsupport : ∀ ys, ys ∉ succ → J.law.w ys = 0 := by
    intro ys hys
    by_contra hne
    exact hys (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  have hZL : ∀ a ys, ys ∈ succ → stats a ys ≤ L := by
    intro a ys hys
    have hleaf : a.1.1 ∈ PT.tiling.leaf i := (Finset.mem_filter.mp a.2).2
    have hpatch : S15.patchAt PT hPT a.1.1 = i :=
      Lane_q_s15_direct.patchAt_eq_of_leaf PT hPT i a.1.1 hleaf
    have h := hcap PT hPT hmode i a.1 hpatch x hx ys
    simpa [stats, L, M, n] using h
  have hd : ∀ a : U, 0 ≤ d a := by
    intro a
    simp [d]
  have hmean : (Fintype.card U : ℝ)⁻¹ * ∑ a : U, d a ≤ 1 := by
    simp [d]
  have hsmall : (n : ℝ) * f * L ≤ 1 := by
    have h := hslack PT hPT hmode i
    simpa [f, L, nR, n, U, hUcard] using h
  have hjoint : ∀ m ≤ n, ∀ s : Fin m → U,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
      (∑ ys ∈ succ, J.law.w ys * ∏ j, stats (s j) ys) ≤
        (4 : ℝ) ^ m * ∏ j, d (s j) := by
    intro m hm s hsep
    by_cases hm0 : m = 0
    · subst m
      have hsum := Lane_q_s15_direct.finLaw_sum_support_eq_one J.law
      have hsum' : ∑ ys ∈ succ, J.law.w ys = 1 := by simpa [succ] using hsum
      have hle : (∑ ys ∈ succ, J.law.w ys) ≤ 1 := le_of_eq hsum'
      simpa [succ, stats, d] using hle
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      let rows : Fin m → EvenPosition T k := fun j => (s j).1
      let scope : Finset (OddPosition T k) :=
        Finset.univ.biUnion fun j : Fin m => Lane_q_s15_direct.star (rows j)
      have hdisj : ∀ i j : Fin m, i ≠ j →
          Disjoint (Lane_q_s15_direct.star (rows i)) (Lane_q_s15_direct.star (rows j)) := by
        intro i j hij
        rcases lt_trichotomy i j with hlt | heq | hgt
        · have hnot := hsep j i hlt
          have hnot' : (s j).1 ∉ Lane_q_s15_direct.starNear (rows i) := by
            intro hmem
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
          exact Lane_q_s15_direct.stars_disjoint_of_not_mem_starNear (rows i) (rows j) hnot'
        · exact (hij heq).elim
        · have hnot := hsep i j hgt
          have hnot' : (s i).1 ∉ Lane_q_s15_direct.starNear (rows j) := by
            intro hmem
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
          exact (Lane_q_s15_direct.stars_disjoint_of_not_mem_starNear (rows j) (rows i) hnot').symm
      have hscope : ∀ j, Lane_q_s15_direct.star (rows j) ⊆ scope := by
        intro j b hb
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hb⟩
      have hscopeNat : scope.card ≤ n ^ 2 := by
        calc
          scope.card ≤ ∑ j : Fin m, (Lane_q_s15_direct.star (rows j)).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _j : Fin m, n :=
            Finset.sum_le_sum fun j _ => Lane_q_s15_direct.star_card_le (rows j)
          _ = m * n := by simp
          _ ≤ n * n := Nat.mul_le_mul_right n hm
          _ = n ^ 2 := by rw [pow_two]
      have hn1 : 1 ≤ n := by omega
      have hnPow : n ^ 2 ≤ n ^ 5 := by
        calc
          n ^ 2 = n ^ 2 * 1 := by simp
          _ ≤ n ^ 2 * n ^ 3 := Nat.mul_le_mul_left _ (one_le_pow₀ hn1)
          _ = n ^ 5 := by rw [← pow_add]
      have hscopeCard : (scope.card : ℝ) ≤ (n : ℝ) ^ 5 := by
        exact_mod_cast le_trans hscopeNat hnPow
      have hdegree : ∀ j b, b ∈ Lane_q_s15_direct.star (rows j) →
          0 < deg (T.S.E k) PT.tiling.c (S15.lawAtOdd PT hPT b).w x := by
        intro j b hb
        have hleaf : (rows j).1 ∈ PT.tiling.leaf i :=
          (Finset.mem_filter.mp (s j).2).2
        have hpatch : S15.patchAt PT hPT (rows j).1 = i :=
          Lane_q_s15_direct.patchAt_eq_of_leaf PT hPT i (rows j).1 hleaf
        exact Lane_q_s15_direct.highDirect_star_degrees_positive PT hPT hmode i
          (rows j) hpatch x hx (by omega) hbstar b hb
      have hrowBase : ∀ j, (M : ℝ) *
          S15.directBaseWeight PT hPT (rows j) x ≤ 2 := by
        intro j
        have hleaf : (rows j).1 ∈ PT.tiling.leaf i :=
          (Finset.mem_filter.mp (s j).2).2
        have hpatch : S15.patchAt PT hPT (rows j).1 = i :=
          Lane_q_s15_direct.patchAt_eq_of_leaf PT hPT i (rows j).1 hleaf
        simpa [M] using Lane_q_s15_direct.highDirect_scaled_baseweight_le_two
          PT hPT hmode i (rows j) hpatch x
      have hMpos : 0 < M := by
        have hcard : 0 < ((PT.tiling.P i).X.card : ℝ) :=
          Nat.cast_pos.mpr (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1)
        rw [(PT.tiling.P i).cardX] at hcard
        exact_mod_cast hcard
      have hj := Lane_q_s15_direct.direct_sampler_separated_product_bound
        PT hPT J rows x M scope hMpos hdegree hdisj hscope hscopeCard hrowBase hmpos
      simpa [d] using hj
  have hscattered := Lane_q_s15_direct.scattered_moment_sampler_bound
    J.law succ hsupport stats hZ0 L hL hZL near
    (fun a => Lane_q_s15_direct.self_mem_starNearWithin E a (by omega))
    f (by positivity) hnear n 4 1 (by norm_num) (by norm_num) d hd hmean hsmall hjoint
  have haverage : ∀ ys, (Fintype.card U : ℝ)⁻¹ * ∑ a : U, stats a ys =
      patchColumnAverage PT i (directRowWeight PT hPT) ys x := by
    intro ys
    have hsum : ∑ a : U, stats a ys =
        ∑ a ∈ E, (PT.tiling.P i).M * directRowWeight PT hPT ys a x := by
      dsimp [stats, M, U]
      change (∑ a ∈ (Finset.univ : Finset {a : EvenPosition T k // a ∈ E}),
        (PT.tiling.P i).M * directRowWeight PT hPT ys a.1 x) = _
      have hattach : (Finset.univ : Finset {a : EvenPosition T k // a ∈ E}) = E.attach :=
        Finset.univ_eq_attach E
      rw [hattach]
      exact Finset.sum_attach E
        (fun a : EvenPosition T k => (PT.tiling.P i).M * directRowWeight PT hPT ys a x)
    unfold patchColumnAverage
    rw [hUcard, hsum]
  have hMoment : (J.law).E
      (fun ys => patchColumnAverage PT i (directRowWeight PT hPT) ys x ^ n) ≤
        (12 : ℝ) ^ n := by
    have hEq : (fun ys => patchColumnAverage PT i (directRowWeight PT hPT) ys x ^ n) =
        fun ys => ((Fintype.card U : ℝ)⁻¹ * ∑ a : U, stats a ys) ^ n := by
      funext ys
      rw [(haverage ys).symm]
    rw [hEq]
    calc
      _ ≤ (4 : ℝ) ^ n * (1 + 1) ^ n := by simpa [d] using hscattered
      _ = (8 : ℝ) ^ n := by
        rw [show (1 + 1 : ℝ) = 2 by norm_num, ← mul_pow]
        norm_num
      _ ≤ (12 : ℝ) ^ n :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) (by norm_num : (8 : ℝ) ≤ 12) n
  have hA0pow : (12 : ℝ) ^ n ≤ κ.A0 ^ n :=
    pow_le_pow_left₀ (by norm_num) hA0 n
  exact le_trans hMoment hA0pow

/-- L15.1f: Markov, the union bound, and the mass gates yield a direct Hall certificate. -/
theorem high_direct_load_existence (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hSampler : DirectSamplerClaim κ T hDeep)
    (hMoment : DirectMomentClaim κ T) : DirectCertificateClaim κ T := by
  classical
  have hPpos : 0 < κ.P := by
    have h := hκ.P_big.2
    rw [hκ.Ac_eq] at h
    norm_num at h
    omega
  have hRpos : 0 < κ.R := by
    rw [hκ.R_eq]
    exact Nat.pow_pos hPpos
  have hA0 : 0 < κ.A0 :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 10 ^ 6) (by exact_mod_cast hRpos))
      hκ.A0_big
  let Clarge : ℝ := 51200 * κ.A0
  have hHost : ∀ᶠ k in atTop,
      max 4 2 ≤ T.S.n k ∧ LargeHost Clarge (T.S.n k) (T.S.N k) :=
    T.S.eventually_large Clarge (max 4 2)
  have hRatio : ∀ᶠ k in atTop,
      Clarge ≤ (T.S.N k : ℝ) / (2 : ℝ) ^ (T.S.n k) :=
    T.S.ratio_tendsto.eventually_ge_atTop Clarge
  have hNsmall : ∀ᶠ k in atTop,
      (T.S.n k : ℝ) ^ 2 / (2 : ℝ) ^ (T.S.n k) < 1 :=
    T.S.n_tendsto.eventually
      Lane_q_s15_direct.eventually_nat_sq_over_two_pow_lt_one
  filter_upwards [hSampler, hMoment, hHost, hRatio, hNsmall]
    with k hsampler hmoment hhost hratio hnsq
  intro PT hPT hmode
  obtain ⟨J⟩ := hsampler PT hPT hmode
  let n := T.S.n k
  let N := T.S.N k
  have hn : 0 < n := by dsimp [n]; have := hhost.1; omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast T.S.N_pos k
  have hnPowPos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hnsq' : (n : ℝ) ^ 2 < (2 : ℝ) ^ n := by
    have h := (div_lt_iff₀ hnPowPos).mp (by simpa [n] using hnsq)
    simpa [n] using h
  have hNupper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by
    exact_mod_cast hhost.2.2
  have hNpowSq : (N : ℝ) ^ 2 < (8 : ℝ) ^ n := by
    have hpow2 : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
      calc
        ((2 : ℝ) ^ n) ^ 2 = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by rw [pow_two]
        _ = ((2 : ℝ) * 2) ^ n := by rw [← mul_pow]
        _ = (4 : ℝ) ^ n := by norm_num
    calc
      (N : ℝ) ^ 2 ≤ ((n : ℝ) * (2 : ℝ) ^ n) ^ 2 := by nlinarith
      _ = (n : ℝ) ^ 2 * ((2 : ℝ) ^ n) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 * (4 : ℝ) ^ n := by rw [hpow2]
      _ < (2 : ℝ) ^ n * (4 : ℝ) ^ n :=
        mul_lt_mul_of_pos_right hnsq' (by positivity)
      _ = (8 : ℝ) ^ n := by rw [← mul_pow]; norm_num
  let t : ℝ := (N : ℝ) / (2 : ℝ) ^ n / 1600
  have ht : 0 < t := by dsimp [t]; positivity
  have hratio32 : 32 * κ.A0 ≤ t := by
    have hscaled : (51200 * κ.A0) / 1600 ≤
        ((N : ℝ) / (2 : ℝ) ^ n) / 1600 :=
      div_le_div_of_nonneg_right (by simpa [Clarge] using hratio) (by norm_num)
    have hconst : (51200 * κ.A0) / 1600 = 32 * κ.A0 := by ring
    rw [hconst] at hscaled
    simpa [t] using hscaled
  let P : FinProb (OddAssignment T k) :=
    ⟨J.law.w, J.law.nonneg, J.law.sum_one⟩
  let stats : (Fin PT.tiling.m × Fin N) → OddAssignment T k → ℝ := fun ix ys =>
    if ix.2 ∈ PT.envelope ix.1 then
      patchColumnAverage PT ix.1 (directRowWeight PT hPT) ys ix.2 else 0
  have hstats : ∀ ix ys, 0 ≤ stats ix ys := by
    intro ix ys
    by_cases hx : ix.2 ∈ PT.envelope ix.1
    · simpa [stats, hx] using
        Lane_q_s15_direct.patchColumnAverage_directRowWeight_nonneg
          PT hPT ix.1 ys ix.2
    · simp [stats, hx]
  have hindexMoment (ix : Fin PT.tiling.m × Fin N) :
      P.expect (fun ys => (stats ix ys) ^ n) ≤ κ.A0 ^ n := by
    by_cases hx : ix.2 ∈ PT.envelope ix.1
    · simpa [P, stats, hx, FinProb.expect, FinLaw.E, n] using
        hmoment PT hPT hmode J ix.1 ix.2 hx
    · simp [P, stats, hx, FinProb.expect, hn.ne', n]
      exact pow_nonneg hA0.le n
  have hsumMoment :
      P.expect (fun ys => ∑ ix : Fin PT.tiling.m × Fin N, (stats ix ys) ^ n) ≤
        (N : ℝ) ^ 2 * κ.A0 ^ n := by
    rw [Lane_q_s15_direct.finProb_expect_sum]
    calc
      (∑ ix : Fin PT.tiling.m × Fin N, P.expect (fun ys => (stats ix ys) ^ n)) ≤
          ∑ ix : Fin PT.tiling.m × Fin N, κ.A0 ^ n :=
        Finset.sum_le_sum fun ix _ => hindexMoment ix
      _ = ((PT.tiling.m * N : ℕ) : ℝ) * κ.A0 ^ n := by
        simp [Fintype.card_prod, Fintype.card_fin]
      _ ≤ (N : ℝ) ^ 2 * κ.A0 ^ n := by
        have hcount : PT.tiling.m * N ≤ N * N :=
          Nat.mul_le_mul_right N
            (Lane_q_s15_direct.tiling_patch_count_le PT hPT)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hA0.le n)
        rw [pow_two]
        exact_mod_cast hcount
  have hlargeMoment : (N : ℝ) ^ 2 * κ.A0 ^ n < t ^ n := by
    have hpowBase : 8 * κ.A0 < 32 * κ.A0 := by nlinarith [hA0]
    calc
      (N : ℝ) ^ 2 * κ.A0 ^ n ≤ (8 : ℝ) ^ n * κ.A0 ^ n :=
        mul_le_mul_of_nonneg_right hNpowSq.le (pow_nonneg hA0.le n)
      _ = (8 * κ.A0) ^ n := by rw [← mul_pow]
      _ < (32 * κ.A0) ^ n := pow_lt_pow_left₀ hpowBase (by positivity) hn.ne'
      _ ≤ t ^ n := pow_le_pow_left₀ (by positivity) hratio32 n
  have htotalMoment :
      P.expect (fun ys => ∑ ix : Fin PT.tiling.m × Fin N, (stats ix ys) ^ n) < t ^ n :=
    lt_of_le_of_lt hsumMoment hlargeMoment
  obtain ⟨ys, hys, hbelow⟩ :=
    Lane_q_s15_direct.exists_support_all_below_of_sum_moment
      P stats n t hn ht hstats htotalMoment
  have havg : ∀ i x, patchColumnAverage PT i (directRowWeight PT hPT) ys x ≤ t := by
    intro i x
    by_cases hx : x ∈ PT.envelope i
    · have hlt := hbelow ⟨i, x⟩
      simpa [stats, hx] using le_of_lt hlt
    · rw [Lane_q_s15_direct.patchColumnAverage_directRowWeight_zero PT hPT i ys x hx]
      exact le_of_lt ht
  have hcol :=
    Lane_q_s15_direct.direct_column_le_of_patch_averages PT hPT J ys hys havg
  let rows := Lane_q_s15_direct.directHallRows_of_sampler PT hPT J ys hys hcol
  exact ⟨⟨J, ys, hys, rows, rfl, rfl⟩⟩

/-- Hall assembly retains the sampler support and normalized-row identity. -/
theorem direct_certificate_to_cube {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (C : DirectCertificate PT hPT) :
    ∃ P : FinLaw (OddAssignment T k), P = directRawLaw PT hPT ∧
      CubeIn T k PT.tiling.c ∧ C.sampler.rawLaw = directRawLaw PT hPT ∧
      C.sampler.law.w C.labels ≠ 0 ∧ C.rows.oddLabel = C.labels ∧
      C.rows.row = fun a x => directNormalizedRow PT hPT C.labels a x := by
  have hRows := rows_to_cube PT.tiling.c C.rows
  exact ⟨directRawLaw PT hPT, rfl, hRows.1, C.sampler.rawLaw_eq,
    C.positive, C.labels_eq, C.row_eq⟩

/-- L15.1 (`lem:high-direct-assignment`, 15:8–41): every valid high-direct profiled tiling gives a cube. -/
theorem high_direct (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      PT.tiling.mode = .highDirect → CubeIn T k PT.tiling.c := by
  have hCross := high_direct_crossing_filters κ hκ T hDeep
  have hBulk := high_direct_bulk_lower_tail κ hκ T hDeep hCross.1
  have hMass := high_direct_mass_estimate κ hκ T hDeep hCross.1 hBulk
  have hSampler := high_direct_clock_injection κ hκ T hDeep hMass
  have hMoment := high_direct_column_moment κ hκ T hDeep hSampler
  have hFinal := high_direct_load_existence κ hκ T hDeep hSampler hMoment
  filter_upwards [hFinal] with k hk
  intro PT hPT hmode
  obtain ⟨C⟩ := hk PT hPT hmode
  obtain ⟨_, _, hCube, _, _, _, _⟩ := direct_certificate_to_cube C
  exact hCube

end HypercubeRamsey.S15
