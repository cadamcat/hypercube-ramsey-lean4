import HypercubeRamsey.S15.Defs
import HypercubeRamsey.S15.DirectNodes_q_s15_direct

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
  sorry

/-- L15.1b: bulk lower-tail estimate, using the crossing-filter stage. -/
theorem high_direct_bulk_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : DirectCrossingClaim κ T) :
    DirectBulkClaim κ T := by
  sorry

/-- L15.1c: assemble the crossing and bulk estimates into the independent row-mass bound. -/
theorem high_direct_mass_estimate (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hCross : DirectCrossingClaim κ T)
    (hBulk : DirectBulkClaim κ T) : DirectMassClaim κ T := by
  sorry

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
  sorry

/-- L15.1f: Markov, the union bound, and the mass gates yield a direct Hall certificate. -/
theorem high_direct_load_existence (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (hSampler : DirectSamplerClaim κ T hDeep)
    (hMoment : DirectMomentClaim κ T) : DirectCertificateClaim κ T := by
  sorry

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
