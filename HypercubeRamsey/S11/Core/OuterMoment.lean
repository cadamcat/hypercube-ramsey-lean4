import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
import HypercubeRamsey.Tools.SignedTest
import HypercubeRamsey.Tools.Ramsey

/-!
# Lemma 11.3: the outer mass lower tail

Source: `sections/11-…tex`, lines 164–331 (L11.3, L11.3a–g in `research/blueprint/PART-B.md` §3.11).  The
interaction estimates are stated for tuples whose fixed coordinates lie in the compatible support `S` (all tuple
coordinates are drawn from `σ`, supported in `S`); every constant may depend on the tuple length `u` and is chosen
before the dimension.
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open Filter
open scoped BigOperators

/-- The hypotheses of Lemma 11.3 at one dimension (11:168–171): (11.1), a second law `π` on `Y` with `N π ≤ K`, a
compatible support `S ⊆ X` (degree condition and no correlation clique), and a probability `σ` on `S` with
`N σ ≤ exp((log 2 - g/2) h)`. -/
structure OuterHyp (δ x₀ K : ℝ) (n N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
    (π σ : Fin N → ℝ) (S : Finset (Fin N)) : Prop where
  host : 2 ^ n ≤ N
  disc : DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - δ / 16)) ((n : ℝ) ^ x₀) ((n : ℝ) ^ (-(19 : ℝ) / 20))
  pi_nonneg : ∀ y, 0 ≤ π y
  pi_sum : ∑ y, π y = 1
  pi_supp : ∀ y, π y ≠ 0 → y ∈ Y
  pi_cap : ∀ y, (N : ℝ) * π y ≤ K
  S_sub : S ⊆ X
  degree : ∀ x ∈ S, |sMean E G π x| ≤ 4 * bS n
  noClique : NoClique E G π n δ S
  sigma_nonneg : ∀ x, 0 ≤ σ x
  sigma_sum : ∑ x, σ x = 1
  sigma_supp : ∀ x, σ x ≠ 0 → x ∈ S
  sigma_cap : ∀ x, (N : ℝ) * σ x ≤ Real.exp ((Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n))

/-- Lemma 11.3's conclusion at one dimension, for every setup (11:177–182). -/
def OuterTailAt (δ x₀ K P : ℝ) (n : ℕ) : Prop :=
  ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour) (π σ : Fin N → ℝ)
    (S : Finset (Fin N)), OuterHyp δ x₀ K n N E X Y G π σ S → outerFail E G π σ (OuterCoord n) ≤ (n : ℝ) ^ (-P)

section Facts

variable {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N))

/-- One free label (11:196–198): `|M_J| ≤ C b_*` except with `σ`-probability `2e^{-n^{1-υ/4}/2}`, `υ = δ/4`. -/
def OneFree (n : ℕ) (δ C : ℝ) (u : ℕ) : Prop :=
  ∀ (J : Finset (Fin u)) (j : Fin u), j ∈ J → ∀ base : Fin u → Fin N, (∀ l, base l ∈ S) →
    (∑ x, σ x * (if C * bS n < |inter E G π J (Function.update base j x)| then 1 else 0)) ≤
      2 * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16)) / 2)

/-- Two free labels (11:207–211): `Pr{|M_J| > n^{-1.03}} ≤ e^{-n^.4}`. -/
def TwoFree (n u : ℕ) : Prop :=
  ∀ (J : Finset (Fin u)) (j j' : Fin u), j ∈ J → j' ∈ J → j ≠ j' → ∀ base : Fin u → Fin N,
    (∀ l, base l ∈ S) →
    (∑ x, ∑ z, σ x * σ z *
      (if (n : ℝ) ^ (-(103 : ℝ) / 100) <
          |inter E G π J (Function.update (Function.update base j x) j' z)| then 1 else 0)) ≤
      Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))

/-- Mean interaction size (11:254–255): `E|M_J| ≤ n^{-.4|J|}` for `|J| ≥ 2`. -/
def MeanInter (n u : ℕ) : Prop :=
  ∀ J : Finset (Fin u), 2 ≤ J.card →
    (∑ x : Fin u → Fin N, tupWt σ x * |inter E G π J x|) ≤ (n : ℝ) ^ (-(2 / 5 : ℝ) * J.card)

/-- Counting large extensions (11:270–272): at most `e^{n^.03}` labels of `S` extend fixed coordinates to
`|M_J| > n^{-υ}`. -/
def CountExt (n : ℕ) (δ : ℝ) (u : ℕ) : Prop :=
  ∀ (J : Finset (Fin u)) (j : Fin u), j ∈ J → ∀ base : Fin u → Fin N, (∀ l, base l ∈ S) →
    ((S.filter fun x => (n : ℝ) ^ (-(δ / 4)) < |inter E G π J (Function.update base j x)|).card : ℝ) ≤
      Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100))

/-- Exponential weights, bounded part (11:283–284). -/
def ModBounded (n : ℕ) (δ : ℝ) (u : ℕ) : Prop :=
  (∑ x : Fin u → Fin N, tupWt σ x *
    (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4)) then Real.exp ((2 : ℝ) ^ u * n * env E G π x) else 0)) ≤
    Real.exp ((2 : ℝ) ^ u) + 1

/-- Exponential weights, the part above `n^{-1.03}` (11:284–292). -/
def ModTail (n : ℕ) (δ P' : ℝ) (u : ℕ) : Prop :=
  (∑ x : Fin u → Fin N, tupWt σ x *
    (if (n : ℝ) ^ (-(103 : ℝ) / 100) < env E G π x ∧ env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
     then Real.exp ((2 : ℝ) ^ u * n * env E G π x) else 0)) ≤ (n : ℝ) ^ (-P')

/-- The contribution of tuples with `w ≤ n^{-υ}` to `∫ |Φ_u| dσ^{⊗u}` (11:294–309). -/
def SmallRange (d n : ℕ) (δ P : ℝ) (u : ℕ) : Prop :=
  (∑ x : Fin u → Fin N, tupWt σ x *
    (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4)) then |phiU E G π d u x| else 0)) ≤
    (2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P)

/-- The contribution of tuples with `w > n^{-υ}` (11:311–327). -/
def LargeRange (d n : ℕ) (δ P : ℝ) (u : ℕ) : Prop :=
  (∑ x : Fin u → Fin N, tupWt σ x *
    (if (n : ℝ) ^ (-(δ / 4)) < env E G π x then |phiU E G π d u x| else 0)) ≤
    (2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P)

/-- The moment identity `E(Z - 1)^u = ∫ Φ_u dσ^{⊗u}` (11:295–300). -/
def MomentIdentity (D : Type) [Fintype D] [DecidableEq D] (u : ℕ) : Prop :=
  (∑ Yv : D → Fin N, outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) =
    ∑ x : Fin u → Fin N, tupWt σ x * phiU E G π (Fintype.card D) u x

end Facts

/-- L11.3a's conclusion, uniformly in the setup. -/
def OneFreeEv (δ x₀ K : ℝ) : Prop :=
  ∀ u : ℕ, ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N)),
    OuterHyp δ x₀ K n N E X Y G π σ S → OneFree E G π σ S n δ C u

/-- L11.3b's conclusion. -/
def TwoFreeEv (δ x₀ K : ℝ) : Prop :=
  ∀ u : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N)),
    OuterHyp δ x₀ K n N E X Y G π σ S → TwoFree E G π σ S n u

/-- L11.3c's conclusion. -/
def MeanInterEv (δ x₀ K : ℝ) : Prop :=
  ∀ u : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N)),
    OuterHyp δ x₀ K n N E X Y G π σ S → MeanInter E G π σ n u

/-- L11.3d's conclusion. -/
def CountExtEv (δ x₀ K : ℝ) : Prop :=
  ∀ u : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N)),
    OuterHyp δ x₀ K n N E X Y G π σ S → CountExt E G π S n δ u

/-- L11.3e's conclusion, for all tuple lengths up to `U` (the subtuples of L11.3g). -/
def ModerateEv (δ x₀ K : ℝ) : Prop :=
  ∀ (U : ℕ) (P' : ℝ), ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N)),
    OuterHyp δ x₀ K n N E X Y G π σ S →
    ∀ u ≤ U, ModBounded E G π σ n δ u ∧ ModTail E G π σ n δ P' u

/-- L11.3a (11:196–205).  `M_J = ⟨f_x, H₀ - E_π H₀⟩_π / (1 + m_x)` with `|H₀| ≤ C_u` (fixed coordinates in `S`,
`D_x ≥ 1/2 - 2b_*`).  A signed exceptional set of `σ`-mass `≥ e^{-n^{1-υ/4}/2}` gives a first law of width
`≤ h log 2 + n^{1-υ/4}/2 < n^{1-υ/4}`; reweight by `(1 + m_x)^{-1}` and apply F-SignedTest (width
`log K + O_u(1) ≤ n^{x₀}`) with (11.1). -/
theorem one_free (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : OneFreeEv δ x₀ K := by
  classical
  unfold OneFreeEv
  intro u
  let a : ℝ := 1 - δ / 16
  let Hbound : ℝ := (5 : ℝ) ^ u
  let B : ℝ := 2 * Hbound
  let C : ℝ := 8 * (B + 1) + 1
  let tσ : ℕ → ℝ := fun n => (Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n)
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hgap := OuterMoment_q_s11_outer.eventually_pow_gap
    ((1 : ℝ) / 10) a 6 (by
      dsimp [a]
      have hδsmall : δ / 16 < (1 : ℝ) / 320000 := by linarith
      nlinarith) (by norm_num)
  have hbT : Tendsto (fun n : ℕ => bS n) atTop (nhds (0 : ℝ)) := by
    simpa [bS, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (19 : ℝ) / 20)).comp
        tendsto_natCast_atTop_atTop
  have hbSmall : ∀ᶠ n : ℕ in atTop, bS n ≤ 1 / 8 := by
    have h := hbT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [h] with n hn
    exact hn.le
  have hnLarge : ∀ᶠ n : ℕ in atTop, 64 ≤ n :=
    eventually_atTop.mpr ⟨64, fun _ hn => hn⟩
  have hPiTend : Tendsto (fun n : ℕ => (n : ℝ) ^ x₀) atTop atTop :=
    (tendsto_rpow_atTop hx₀).comp tendsto_natCast_atTop_atTop
  have hPiWidth : ∀ᶠ n : ℕ in atTop,
      Real.log K + Real.log (2 * B + 2) ≤ (n : ℝ) ^ x₀ := by
    filter_upwards [hPiTend.eventually_gt_atTop (Real.log K + Real.log (2 * B + 2))]
      with n hn
    exact hn.le
  have hScale : ∀ᶠ n : ℕ in atTop,
      64 ≤ n ∧ bS n ≤ 1 / 8 ∧ tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 ∧
        Real.log K + Real.log (2 * B + 2) ≤ (n : ℝ) ^ x₀ := by
    filter_upwards [hnLarge, hbSmall, hgap, hPiWidth] with n hn hb hg hp
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
      have h := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (0 : ℝ) ≤ 1 / 10)
      simpa using h
    have hcard : (Fintype.card (InnerCoord n) : ℝ) ≤ (hIn n : ℝ) := by
      exact_mod_cast OuterMoment_q_s11_outer.innerCoord_card_le n
    have hfloor := OuterMoment_q_s11_outer.hIn_real_le_pow n
    have hgNonneg : 0 ≤ gS n := by
      unfold gS
      exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have htσ : tσ n ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
      dsimp [tσ]
      calc
        (Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n) ≤
            1 * Fintype.card (InnerCoord n) := by
              exact mul_le_mul_of_nonneg_right (by linarith) (by exact_mod_cast Nat.cast_nonneg _)
        _ ≤ (hIn n : ℝ) := by simpa using hcard
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := hfloor
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hwidth : tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 := by
      have hpowgap := hg
      nlinarith [htσ, hlog3, hpow1]
    exact ⟨hn, hb, hwidth, hp⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hScale
  refine ⟨C, n₀, ?_⟩
  intro n hn N E X Y G π σ S hO
  intro J j hj base hbase
  have hpars := hn₀ n hn
  rcases hpars with ⟨hn64, hbSmallN, hwidthN, hpiWidthN⟩
  have hNpos : 0 < (N : ℝ) := by
    have hNnat : 0 < N := lt_of_lt_of_le (by positivity) hO.host
    exact_mod_cast hNnat
  let πlaw : Law N := ⟨π, hO.pi_nonneg, hO.pi_sum⟩
  let σlaw : Law N := ⟨σ, hO.sigma_nonneg, hO.sigma_sum⟩
  have hπWidth : πlaw.WidthLE (Real.log K) := by
    intro y
    apply (le_div_iff₀ hNpos).2
    rw [Real.exp_log hK]
    nlinarith [hO.pi_cap y]
  have hσWidth : σlaw.WidthLE (tσ n) := by
    intro x
    apply (le_div_iff₀ hNpos).2
    change σ x * (N : ℝ) ≤ Real.exp ((Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n))
    nlinarith [hO.sigma_cap x]
  have hπSupport : πlaw.SupportedIn Y := by
    intro y hy
    by_contra hne
    exact hy (hO.pi_supp y hne)
  have hσSupport : σlaw.SupportedIn S := by
    intro x hx
    by_contra hne
    exact hx (hO.sigma_supp x hne)
  let bad : Finset (Fin N) := Finset.univ.filter fun x =>
    C * bS n < |inter E G π J (Function.update base j x)|
  let pos : Finset (Fin N) := S.filter fun x =>
    C * bS n < inter E G π J (Function.update base j x)
  let neg : Finset (Fin N) := S.filter fun x =>
    C * bS n < -inter E G π J (Function.update base j x)
  let badMass : ℝ := ∑ x, σ x * (if x ∈ bad then 1 else 0)
  let posMass : ℝ := ∑ x, σ x * (if x ∈ pos then 1 else 0)
  let negMass : ℝ := ∑ x, σ x * (if x ∈ neg then 1 else 0)
  have hbadDecomp : badMass ≤ posMass + negMass := by
    dsimp [badMass, posMass, negMass]
    calc
      (∑ x, σ x * (if x ∈ bad then 1 else 0)) ≤
          ∑ x, (σ x * (if x ∈ pos then 1 else 0) +
            σ x * (if x ∈ neg then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hxS : x ∈ S
        · by_cases hbad : C * bS n < |inter E G π J (Function.update base j x)|
          · by_cases hp : C * bS n < inter E G π J (Function.update base j x)
            · have hσnonneg : 0 ≤ σ x := hO.sigma_nonneg x
              simp [bad, pos, neg, hxS, hbad, hp]
              split_ifs <;> linarith [hσnonneg]
            · by_cases hn : C * bS n < -inter E G π J (Function.update base j x)
              · simp [bad, pos, neg, hxS, hbad, hp, hn]
              · have hlow : -(C * bS n) ≤ inter E G π J (Function.update base j x) := by
                  by_contra hlow
                  exact hn (by linarith)
                have hup : inter E G π J (Function.update base j x) ≤ C * bS n := le_of_not_gt hp
                have habs : |inter E G π J (Function.update base j x)| ≤ C * bS n :=
                  abs_le.mpr ⟨hlow, hup⟩
                exact False.elim ((not_lt_of_ge habs) hbad)
          · simp [bad, hbad]
            have hσnonneg : 0 ≤ σ x := hO.sigma_nonneg x
            split_ifs <;> positivity
        · have hσ0 : σ x = 0 := by
            by_contra hne
            exact hxS (hO.sigma_supp x hne)
          simp [hσ0, pos, neg, hxS]
      _ = posMass + negMass := by rw [Finset.sum_add_distrib]
  have hindicator (A : Finset (Fin N)) :
      (∑ x, σ x * (if x ∈ A then 1 else 0)) = ∑ x ∈ A, σ x := by
    calc
      (∑ x, σ x * (if x ∈ A then 1 else 0)) =
          ∑ x, (if x ∈ A then σ x else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : x ∈ A <;> simp [h] <;> ring
      _ = ∑ x ∈ A, σ x := Finset.sum_ite_mem_eq A σ
  let ε : ℝ := Real.exp (-((n : ℝ) ^ a) / 2)
  have hεpos : 0 < ε := by dsimp [ε]; exact Real.exp_pos _
  have hsideImpossible (A : Finset (Fin N)) (hAsub : A ⊆ S) (sgn : ℝ)
      (hsign : |sgn| = 1) (hmass : ε < ∑ x ∈ A, σ x)
      (hEvent : ∀ x ∈ A, C * bS n < sgn * inter E G π J (Function.update base j x)) : False := by
    let mass : ℝ := ∑ x ∈ A, σ x
    have hmasspos : 0 < mass := by
      dsimp [mass]
      exact lt_trans hεpos hmass
    let q : Law N := Law.restrict σlaw A hmasspos
    have hqSupport : q.SupportedIn A := by
      intro x hx
      simp [q, Law.restrict, hx]
    have hqWidth0 : q.WidthLE (tσ n - Real.log mass) := by
      simpa [q, mass] using Law.WidthLE.restrict hσWidth hmasspos
    have hmass' : ε < mass := by simpa [mass] using hmass
    have hlogmass : -((n : ℝ) ^ a) / 2 < Real.log mass := by
      have h := Real.log_lt_log (Real.exp_pos _) hmass'
      simpa [ε, Real.log_exp] using h
    have hqWidth : q.WidthLE (tσ n + (n : ℝ) ^ a / 2) :=
      Law.WidthLE.mono hqWidth0 (by linarith)
    have hMeanRel (x : Fin N) : sMean E G π x = 2 * deg E G π x - 1 := by
      unfold sMean deg fv
      calc
        (∑ y, π y * (2 * hit E G x y - 1)) =
            ∑ y, (2 * (π y * hit E G x y) - π y) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y, 2 * (π y * hit E G x y)) - ∑ y, π y := by
          rw [Finset.sum_sub_distrib]
        _ = 2 * (∑ y, π y * hit E G x y) - 1 := by
          rw [← Finset.mul_sum, hO.pi_sum]
    have hMeanDen (x : Fin N) : 1 + sMean E G π x = 2 * deg E G π x := by
      rw [hMeanRel x]
      ring
    have hMeanAbs (x : Fin N) (hx : x ∈ A) : |sMean E G π x| ≤ 1 / 2 := by
      calc
        |sMean E G π x| ≤ 4 * bS n := hO.degree x (hAsub hx)
        _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hbSmallN (by norm_num)
        _ = 1 / 2 := by norm_num
    have hDenBounds (x : Fin N) (hx : x ∈ A) :
        1 / 2 ≤ 1 + sMean E G π x ∧ 1 + sMean E G π x ≤ 3 / 2 := by
      have h := abs_le.mp (hMeanAbs x hx)
      constructor <;> linarith
    have hDegLower (x : Fin N) (hx : x ∈ A) : 1 / 4 ≤ deg E G π x := by
      have h := hMeanDen x
      have h' := (hDenBounds x hx).1
      nlinarith
    have hDegPos (x : Fin N) (hx : x ∈ A) : 0 < deg E G π x :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (hDegLower x hx)
    have haFid (x : Fin N) (hx : x ∈ A) (y : Fin N) :
        aF E G π x y =
          (fv E G x y - sMean E G π x) / (1 + sMean E G π x) := by
      unfold aF
      rw [hMeanDen x]
      unfold fv
      field_simp [ne_of_gt (hDegPos x hx)]
      <;> nlinarith [hMeanDen x]
    let H : Fin N → ℝ := fun y =>
      ∏ l ∈ J.erase j, aF E G π (base l) y
    have haBound (x : Fin N) (hx : x ∈ S) (y : Fin N) :
        |aF E G π x y| ≤ 5 := by
      have hmean : |sMean E G π x| ≤ 1 / 2 := by
        calc
          |sMean E G π x| ≤ 4 * bS n := hO.degree x hx
          _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hbSmallN (by norm_num)
          _ = 1 / 2 := by norm_num
      have hden : 1 / 4 ≤ deg E G π x := by
        have h := hMeanDen x
        have h' := (abs_le.mp hmean).1
        nlinarith
      have hdenpos : 0 < deg E G π x :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hden
      have hhit : |hit E G x y| ≤ 1 := by
        unfold hit
        split_ifs <;> norm_num
      have hfrac : |hit E G x y / deg E G π x| ≤ 4 := by
        rw [abs_div, abs_of_pos hdenpos]
        apply (div_le_iff₀ hdenpos).2
        nlinarith
      unfold aF
      calc
        |hit E G x y / deg E G π x - 1| ≤
            |hit E G x y / deg E G π x| + 1 := by
              simpa using abs_sub (hit E G x y / deg E G π x) 1
        _ ≤ 5 := by linarith
    have hHbound (y : Fin N) : |H y| ≤ Hbound := by
      dsimp [H]
      calc
        |∏ l ∈ J.erase j, aF E G π (base l) y| =
            ∏ l ∈ J.erase j, |aF E G π (base l) y| := by
          rw [Finset.abs_prod]
        _ ≤ ∏ l ∈ J.erase j, (5 : ℝ) :=
          Finset.prod_le_prod₀ (fun l hl => abs_nonneg _) (fun l hl => haBound (base l) (hbase l) y)
        _ = (5 : ℝ) ^ (J.erase j).card := by simp
        _ ≤ (5 : ℝ) ^ u := by
          apply pow_le_pow_right₀ (by norm_num)
          simpa using Finset.card_le_univ (J.erase j)
    let avgH : ℝ := ∑ y, π y * H y
    have havgUpper : avgH ≤ Hbound := by
      dsimp [avgH]
      calc
        (∑ y, π y * H y) ≤ ∑ y, π y * Hbound := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (le_of_abs_le (hHbound y)) (hO.pi_nonneg y)
        _ = Hbound := by rw [← Finset.sum_mul, hO.pi_sum]; ring
    have havgLower : -Hbound ≤ avgH := by
      dsimp [avgH]
      calc
        -Hbound = ∑ y, π y * (-Hbound) := by rw [← Finset.sum_mul, hO.pi_sum]; ring
        _ ≤ ∑ y, π y * H y := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hHbound y)) (hO.pi_nonneg y)
    have havgAbs : |avgH| ≤ Hbound := abs_le.mpr ⟨havgLower, havgUpper⟩
    let T : Fin N → ℝ := fun y => H y - avgH
    have hTbound (y : Fin N) : |T y| ≤ B := by
      dsimp [T, B]
      calc
        |H y - avgH| ≤ |H y| + |avgH| := abs_sub _ _
        _ ≤ Hbound + Hbound := add_le_add (hHbound y) havgAbs
        _ = 2 * Hbound := by ring
    let P : Fin N → ℝ := fun x => ∑ y, π y * fv E G x y * T y
    have hMeanF (x : Fin N) : (∑ y, π y * fv E G x y) = sMean E G π x := rfl
    have hcenter (x : Fin N) :
        (∑ y, π y * (fv E G x y - sMean E G π x) * H y) = P x := by
      have hleft :
          (∑ y, π y * (fv E G x y - sMean E G π x) * H y) =
            (∑ y, π y * fv E G x y * H y) - sMean E G π x * avgH := by
        calc
          (∑ y, π y * (fv E G x y - sMean E G π x) * H y) =
              ∑ y, (π y * fv E G x y * H y - π y * sMean E G π x * H y) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
          _ = (∑ y, π y * fv E G x y * H y) -
                ∑ y, π y * sMean E G π x * H y := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ y, π y * fv E G x y * H y) - sMean E G π x * avgH := by
            congr 1
            calc
              (∑ y, π y * sMean E G π x * H y) =
                  ∑ y, sMean E G π x * (π y * H y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = sMean E G π x * avgH := by
                dsimp [avgH]
                rw [Finset.mul_sum]
      have hright : P x =
          (∑ y, π y * fv E G x y * H y) - avgH * sMean E G π x := by
        dsimp [P, T]
        calc
          (∑ y, π y * fv E G x y * (H y - avgH)) =
              ∑ y, (π y * fv E G x y * H y - π y * fv E G x y * avgH) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
          _ = (∑ y, π y * fv E G x y * H y) -
                ∑ y, π y * fv E G x y * avgH := by
            rw [Finset.sum_sub_distrib]
          _ = (∑ y, π y * fv E G x y * H y) - avgH * sMean E G π x := by
            congr 1
            calc
              (∑ y, π y * fv E G x y * avgH) =
                  ∑ y, avgH * (π y * fv E G x y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = avgH * (∑ y, π y * fv E G x y) := by rw [Finset.mul_sum]
              _ = avgH * sMean E G π x := by rw [hMeanF]
      rw [hleft, hright]
      ring
    have hprodUpdate (x : Fin N) (hx : x ∈ A) (y : Fin N) :
        (∏ l ∈ J, aF E G π (Function.update base j x l) y) =
          aF E G π x y * H y := by
      have herase :
          (∏ l ∈ J.erase j, aF E G π (Function.update base j x l) y) = H y := by
        dsimp [H]
        apply Finset.prod_congr rfl
        intro l hl
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hl) x base]
      calc
        (∏ l ∈ J, aF E G π (Function.update base j x l) y) =
            (∏ l ∈ J.erase j, aF E G π (Function.update base j x l) y) *
              aF E G π (Function.update base j x j) y :=
          (Finset.prod_erase_mul J (fun l => aF E G π (Function.update base j x l) y) hj).symm
        _ = H y * aF E G π x y := by rw [herase, Function.update_self]
        _ = aF E G π x y * H y := by ring
    have hproj (x : Fin N) (hx : x ∈ A) :
        inter E G π J (Function.update base j x) =
          (1 + sMean E G π x)⁻¹ * P x := by
      unfold inter
      calc
        (∑ y, π y * ∏ l ∈ J, aF E G π (Function.update base j x l) y) =
            ∑ y, π y * (aF E G π x y * H y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hprodUpdate x hx y]
        _ = ∑ y, (1 + sMean E G π x)⁻¹ *
            (π y * (fv E G x y - sMean E G π x) * H y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [haFid x hx y]
          ring
        _ = (1 + sMean E G π x)⁻¹ *
            (∑ y, π y * (fv E G x y - sMean E G π x) * H y) := by
          rw [Finset.mul_sum]
        _ = (1 + sMean E G π x)⁻¹ * P x := by rw [hcenter x]
    have hQbound : tσ n + (n : ℝ) ^ a / 2 + Real.log 3 ≤ (n : ℝ) ^ a := by
      linarith [hwidthN]
    let r : Fin N → ℝ := fun x =>
      if x ∈ A then (1 + sMean E G π x)⁻¹ else 0
    have hrBounds (x : Fin N) (hx : x ∈ A) :
        2 / 3 ≤ r x ∧ r x ≤ 2 := by
      have hdenpos : 0 < 1 + sMean E G π x :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hDenBounds x hx).1
      dsimp [r]
      rw [if_pos hx]
      rw [inv_eq_one_div]
      constructor
      · apply (le_div_iff₀ hdenpos).2
        nlinarith [(hDenBounds x hx).2]
      · apply (div_le_iff₀ hdenpos).2
        nlinarith [(hDenBounds x hx).1]
    have hrNonneg (x : Fin N) : 0 ≤ r x := by
      by_cases hx : x ∈ A
      · exact (le_trans (by norm_num : (0 : ℝ) ≤ 2 / 3) (hrBounds x hx).1)
      · simp [r, hx]
    let c : ℝ := ∑ x, q.w x * r x
    have hcLower : 2 / 3 ≤ c := by
      dsimp [c]
      calc
        (2 / 3 : ℝ) = (∑ x, q.w x) * (2 / 3) := by rw [q.sum_eq_one]; ring
        _ = ∑ x, q.w x * (2 / 3) := by rw [Finset.sum_mul]
        _ ≤ ∑ x, q.w x * r x := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hxA : x ∈ A
          · exact mul_le_mul_of_nonneg_left (hrBounds x hxA).1 (q.nonneg x)
          · simp [hqSupport x hxA]
    have hcUpper : c ≤ 2 := by
      dsimp [c]
      calc
        (∑ x, q.w x * r x) ≤ ∑ x, q.w x * 2 := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hxA : x ∈ A
          · exact mul_le_mul_of_nonneg_left (hrBounds x hxA).2 (q.nonneg x)
          · simp [hqSupport x hxA]
        _ = (∑ x, q.w x) * 2 := by rw [Finset.sum_mul]
        _ = 2 := by rw [q.sum_eq_one]; ring
    have hcPos : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hcLower
    let ρ : Law N := {
      w := fun x => q.w x * r x / c
      nonneg := fun x => div_nonneg (mul_nonneg (q.nonneg x) (hrNonneg x)) hcPos.le
      sum_eq_one := by
        calc
          (∑ x, q.w x * r x / c) = (∑ x, q.w x * r x) / c := by rw [Finset.sum_div]
          _ = c / c := rfl
          _ = 1 := div_self hcPos.ne'
    }
    have hρSupport : ρ.SupportedIn X := by
      intro x hx
      have hxA : x ∉ A := fun hA => hx (hO.S_sub (hAsub hA))
      have hq0 : q.w x = 0 := hqSupport x hxA
      simp [ρ, hq0]
    have hρWidth : ρ.WidthLE ((n : ℝ) ^ a) := by
      intro x
      change q.w x * r x / c ≤ Real.exp ((n : ℝ) ^ a) / N
      have hratio : r x / c ≤ 3 := by
        by_cases hxA : x ∈ A
        · have hr := (hrBounds x hxA).2
          apply (div_le_iff₀ hcPos).2
          nlinarith [hr, hcLower]
        · simp [r, hxA]
      calc
        q.w x * r x / c = q.w x * (r x / c) := by ring
        _ ≤ q.w x * 3 := mul_le_mul_of_nonneg_left hratio (q.nonneg x)
        _ ≤ (Real.exp (tσ n + (n : ℝ) ^ a / 2) / N) * 3 :=
          mul_le_mul_of_nonneg_right (hqWidth x) (by positivity)
        _ = Real.exp (tσ n + (n : ℝ) ^ a / 2 + Real.log 3) / N := by
          calc
            (Real.exp (tσ n + (n : ℝ) ^ a / 2) / N) * 3 =
                (Real.exp (tσ n) * Real.exp ((n : ℝ) ^ a / 2) / N) * 3 := by
              rw [Real.exp_add]
            _ =
                (Real.exp (tσ n) * Real.exp ((n : ℝ) ^ a / 2) * 3) / N := by ring
            _ = (Real.exp (tσ n + (n : ℝ) ^ a / 2) * 3) / N := by
              rw [← Real.exp_add]
            _ = (Real.exp (tσ n + (n : ℝ) ^ a / 2) * Real.exp (Real.log 3)) / N := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
            _ = Real.exp (tσ n + (n : ℝ) ^ a / 2 + Real.log 3) / N := by
              rw [← Real.exp_add]
        _ ≤ Real.exp ((n : ℝ) ^ a) / N := by
          exact div_le_div_of_nonneg_right
            (Real.exp_le_exp.mpr hQbound) (by positivity)
    let πwide : ℝ := (n : ℝ) ^ x₀ - Real.log (2 * B + 2)
    have hπWidth' : πlaw.WidthLE πwide := by
      apply Law.WidthLE.mono hπWidth
      dsimp [πwide]
      linarith [hpiWidthN]
    have hSigned :
        |signedHitExpectation E G ρ πlaw T| ≤ 2 * (B + 1) * bS n := by
      have h := signedTest_of_discrepancy (show 0 ≤ B by positivity) hO.disc
        ρ πlaw hρSupport hπSupport hρWidth hπWidth' T hTbound G
      simpa [bS, neg_div] using h
    have hkernel (x y : Fin N) :
        (if Hits E G x y then (1 : ℝ) else 0) - 1 / 2 = fv E G x y / 2 := by
      unfold fv hit
      split_ifs <;> norm_num
    have hSignedId : signedHitExpectation E G ρ πlaw T =
        (1 / 2 : ℝ) * (∑ x, ρ.w x * P x) := by
      unfold signedHitExpectation
      calc
        (∑ x, ρ.w x * ∑ y, πlaw.w y *
            ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * T y) =
          ∑ x, ρ.w x * ((1 / 2 : ℝ) * P x) := by
            apply Finset.sum_congr rfl
            intro x hx
            congr 1
            calc
              (∑ y, πlaw.w y *
                  ((if Hits E G x y then (1 : ℝ) else 0) - 1 / 2) * T y) =
                ∑ y, (1 / 2 : ℝ) * (πlaw.w y * fv E G x y * T y) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  rw [hkernel x y]
                  ring
              _ = (1 / 2 : ℝ) * P x := by
                dsimp [P, πlaw]
                rw [Finset.mul_sum]
        _ = (1 / 2 : ℝ) * (∑ x, ρ.w x * P x) := by
          calc
            (∑ x, ρ.w x * ((1 / 2 : ℝ) * P x)) =
                ∑ x, (1 / 2 : ℝ) * (ρ.w x * P x) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = (1 / 2 : ℝ) * (∑ x, ρ.w x * P x) := by rw [Finset.mul_sum]
    have hPsum : (∑ x, ρ.w x * P x) = 2 * signedHitExpectation E G ρ πlaw T := by
      rw [hSignedId]
      ring
    have hPsign : (∑ x, ρ.w x * (sgn * P x)) =
        sgn * (∑ x, ρ.w x * P x) := by
      calc
        (∑ x, ρ.w x * (sgn * P x)) = ∑ x, sgn * (ρ.w x * P x) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = sgn * (∑ x, ρ.w x * P x) := by rw [Finset.mul_sum]
    have hPabs : |∑ x, ρ.w x * (sgn * P x)| ≤ 4 * (B + 1) * bS n := by
      calc
        |∑ x, ρ.w x * (sgn * P x)| =
            2 * |signedHitExpectation E G ρ πlaw T| := by
          rw [hPsign, hPsum, abs_mul, abs_mul, hsign, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring
        _ ≤ 2 * (2 * (B + 1) * bS n) :=
          mul_le_mul_of_nonneg_left hSigned (by norm_num)
        _ = 4 * (B + 1) * bS n := by ring
    have hAvgEq :
        (∑ x, q.w x * (sgn * inter E G π J (Function.update base j x))) =
          c * (∑ x, ρ.w x * (sgn * P x)) := by
      calc
        (∑ x, q.w x * (sgn * inter E G π J (Function.update base j x))) =
            ∑ x, c * (ρ.w x * (sgn * P x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxA : x ∈ A
          · have hdenpos : 0 < 1 + sMean E G π x :=
              lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hDenBounds x hxA).1
            rw [hproj x hxA]
            dsimp [ρ, r]
            simp only [if_pos hxA]
            field_simp [hcPos.ne', hdenpos.ne']
            <;> ring
          · have hq0 : q.w x = 0 := hqSupport x hxA
            have hr0 : r x = 0 := by simp [r, hxA]
            simp [hq0, hr0, ρ]
        _ = c * (∑ x, ρ.w x * (sgn * P x)) := by
          rw [Finset.mul_sum]
    have hbpos : 0 < bS n := by
      unfold bS
      exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
    have hAvgAbs :
        |∑ x, q.w x * (sgn * inter E G π J (Function.update base j x))| ≤
          8 * (B + 1) * bS n := by
      rw [hAvgEq]
      calc
        |c * (∑ x, ρ.w x * (sgn * P x))| =
            c * |∑ x, ρ.w x * (sgn * P x)| := by
          rw [abs_mul, abs_of_pos hcPos]
        _ ≤ c * (4 * (B + 1) * bS n) :=
          mul_le_mul_of_nonneg_left hPabs hcPos.le
        _ ≤ 2 * (4 * (B + 1) * bS n) :=
          mul_le_mul_of_nonneg_right hcUpper (by positivity)
        _ = 8 * (B + 1) * bS n := by ring
    have hAvgLower :
        C * bS n ≤ ∑ x, q.w x * (sgn * inter E G π J (Function.update base j x)) := by
      calc
        C * bS n = (∑ x, q.w x) * (C * bS n) := by rw [q.sum_eq_one]; ring
        _ = ∑ x, q.w x * (C * bS n) := by rw [Finset.sum_mul]
        _ ≤ ∑ x, q.w x * (sgn * inter E G π J (Function.update base j x)) := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hxA : x ∈ A
          · exact mul_le_mul_of_nonneg_left (le_of_lt (hEvent x hxA)) (q.nonneg x)
          · simp [hqSupport x hxA]
    have hC : C = 8 * (B + 1) + 1 := rfl
    have hle := hAvgLower.trans (le_trans (le_abs_self _) hAvgAbs)
    linarith [hle, hbpos, hC]
  by_contra hgoal
  have hbadLarge : 2 * ε < badMass := by
    apply lt_of_not_ge
    simpa [OneFree, badMass, bad, ε] using hgoal
  have hside : ε < posMass ∨ ε < negMass := by
    by_cases hp : ε < posMass
    · exact Or.inl hp
    · have hp' : posMass ≤ ε := le_of_not_gt hp
      by_cases hn : ε < negMass
      · exact Or.inr hn
      · have hn' : negMass ≤ ε := le_of_not_gt hn
        linarith
  rcases hside with hp | hn
  · have hmass : ε < ∑ x ∈ pos, σ x := by simpa [posMass] using hp
    exact hsideImpossible pos (by intro x hx; exact (Finset.mem_filter.mp hx).1)
      1 (by norm_num) hmass (by
        intro x hx
        simpa using (Finset.mem_filter.mp hx).2)
  · have hmass : ε < ∑ x ∈ neg, σ x := by simpa [negMass] using hn
    exact hsideImpossible neg (by intro x hx; exact (Finset.mem_filter.mp hx).1)
      (-1) (by norm_num) hmass (by
        intro x hx
        have h := (Finset.mem_filter.mp hx).2
        simpa using h)

/-- L11.3b (11:207–252).  `t = ⌈n^.25⌉` conditioned samples from `σ|_{E_x}`, `‖E_{ρ_x} a_z‖_{L²(π)} = O(b_*)` by
(11.1), `E‖S‖² = O_u(t)`, Fubini to a fixed norm-good tuple whose simultaneous violation set has `x`-mass
`e^{-O(t n^.4)}` (width `O(n^.65)`), the projection identity and the equal-normalizer pair `π_±`
(F-SignedTest): `O_u(b_* √t) = O_u(n^{-.825})` against `t n^{-1.03} = n^{-.78+o(1)}`.  Diagonal pairs have
probability `≤ max σ ≤ e^{h}/N`. -/
theorem two_free (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : TwoFreeEv δ x₀ K := by
  sorry

/-- L11.3c (11:254–268).  `E M_J² = E_{y,y'∼π} (∫ a_x(y) a_x(y') dσ)^{|J|}`; the kernel is `O(b_*)` off a
`π`-set of mass `e^{-Ω(n^{x₀})}` by (11.1), so `E M_J² ≤ (C_u b_*)^{|J|} + C_u e^{-Ω(n^{x₀})}`; Cauchy–Schwarz
with `.95/2 > .4`.  Coinciding coordinates have probability `O_u(e^h/N)`. -/
theorem mean_inter (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : MeanInterEv δ x₀ K := by
  sorry

/-- L11.3d (11:270–280).  An extension with `|M_J| > n^{-υ}` has projection `≥ c_u n^{-υ}` of `f_x` on a fixed
bounded direction; `t₀` candidates of one sign with mutual `K_π ≤ 8n^{-δ}` force `t₀ = O_u(n^{2υ})`; no
`s_c`-clique in `S` (compatibility) and X-RamseyBinom bound the candidates by `binom(s_c + t₀, t₀)`, of logarithm
`O_u(n^{ζ + 2υ}) < n^{.03}`. -/
theorem count_ext (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : CountExtEv δ x₀ K := by
  classical
  unfold CountExtEv
  intro u
  let θ : ℝ := δ / 2
  let Hbound : ℝ := (5 : ℝ) ^ u
  let B : ℝ := 2 * Hbound
  let t₀ : ℕ → ℕ := fun n => Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 1000))
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hθsmall : θ < (1 : ℝ) / 1000 := by dsimp [θ]; linarith
  have hgap₁ := OuterMoment_q_s11_outer.eventually_pow_gap
    (-(1 : ℝ) / 1000) (-θ) (8 * B ^ 2) (by linarith) (by positivity)
  have hgap₂ := OuterMoment_q_s11_outer.eventually_pow_gap
    (-δ) (-θ) (64 * B ^ 2) (by dsimp [θ]; linarith) (by positivity)
  have hgap₃ := OuterMoment_q_s11_outer.eventually_pow_gap
    ((1 : ℝ) / 1000) ((1 : ℝ) / 100) 2 (by norm_num) (by norm_num)
  have hgap₄ := OuterMoment_q_s11_outer.eventually_pow_gap
    ((11 : ℝ) / 1000) ((1 : ℝ) / 50) 4 (by norm_num) (by norm_num)
  have hgap₅ := OuterMoment_q_s11_outer.eventually_pow_gap
    ((1 : ℝ) / 50) ((3 : ℝ) / 100) 2 (by norm_num) (by norm_num)
  have hbT : Tendsto (fun n : ℕ => bS n) atTop (nhds (0 : ℝ)) := by
    simpa [bS, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (19 : ℝ) / 20)).comp
        tendsto_natCast_atTop_atTop
  have hbSmall : ∀ᶠ n : ℕ in atTop, bS n ≤ 1 / 8 := by
    have h := hbT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [h] with n hn
    exact hn.le
  have hθTend : Tendsto (fun n : ℕ => (n : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθpos).comp tendsto_natCast_atTop_atTop
  have hRamseyScale : ∀ᶠ n : ℕ in atTop,
      64 ≤ n ∧ bS n ≤ 1 / 8 ∧
      8 * B ^ 2 * (n : ℝ) ^ (-(1 : ℝ) / 1000) < (n : ℝ) ^ (-θ) ∧
      64 * B ^ 2 * (n : ℝ) ^ (-δ) < (n : ℝ) ^ (-θ) ∧
      2 * (n : ℝ) ^ ((1 : ℝ) / 1000) < (n : ℝ) ^ ((1 : ℝ) / 100) ∧
      4 * (n : ℝ) ^ ((11 : ℝ) / 1000) < (n : ℝ) ^ ((1 : ℝ) / 50) ∧
      2 * (n : ℝ) ^ ((1 : ℝ) / 50) < (n : ℝ) ^ ((3 : ℝ) / 100) ∧
      Real.log 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) ∧
      64 * B ^ 2 < (n : ℝ) ^ θ := by
    have hnLarge : ∀ᶠ n : ℕ in atTop, 64 ≤ n :=
      eventually_atTop.mpr ⟨64, fun _ hn => hn⟩
    have hθLarge := hθTend.eventually_gt_atTop (64 * B ^ 2)
    have hlogLarge : ∀ᶠ n : ℕ in atTop, Real.log 3 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := by
      have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 100)).comp
        tendsto_natCast_atTop_atTop
      filter_upwards [h.eventually_gt_atTop (Real.log 3)] with n hn
      exact hn.le
    filter_upwards [hnLarge, hbSmall, hgap₁, hgap₂, hgap₃, hgap₄, hgap₅,
      hlogLarge, hθLarge] with n hn hb h₁ h₂ h₃ h₄ h₅ hlog hθn
    exact ⟨hn, hb, h₁, h₂, h₃, h₄, h₅, hlog, hθn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hRamseyScale
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G π σ S hO
  intro J j hj base hbase
  have hpar := hn₀ n hn
  rcases hpar with ⟨hn64, hbSmallN, hgram₁, hgram₂, hpow₁, hpow₂, hpow₃, hlog, hθn⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let cut : ℝ := (n : ℝ) ^ (-(δ / 4))
  let s₀ : ℕ := sC n
  let t : ℕ := t₀ n
  have hcut : 0 < cut := by dsimp [cut]; exact Real.rpow_pos_of_pos hnreal _
  have hs₀ : 1 ≤ s₀ := by
    dsimp [s₀, sC]
    apply Nat.ceil_pos.2
    exact Real.exp_pos _
  have ht : 1 ≤ t := by
    dsimp [t, t₀]
    apply Nat.ceil_pos.2
    exact Real.rpow_pos_of_pos hnreal _
  have htReal : (t : ℝ) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 1000) := by
    dsimp [t, t₀]
    have hpow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 1000) := by
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      exact Real.one_le_rpow hn1 (by norm_num)
    have hceil : (Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 1000)) : ℝ) ≤
        (n : ℝ) ^ ((1 : ℝ) / 1000) + 1 :=
      (Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) _)).le
    calc
      (Nat.ceil ((n : ℝ) ^ ((1 : ℝ) / 1000)) : ℝ) ≤
          (n : ℝ) ^ ((1 : ℝ) / 1000) + 1 := hceil
      _ ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 1000) := by nlinarith only [hpow]
  have hsReal : (s₀ : ℝ) ≤ 2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) := by
    dsimp [s₀, sC]
    have hexp : 1 ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) :=
      Real.one_le_exp_iff.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hceil : (Nat.ceil (Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100))) : ℝ) ≤
        Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    calc
      (Nat.ceil (Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100))) : ℝ) ≤
          Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) + 1 := hceil
      _ ≤ 2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) := by nlinarith only [hexp]
  have hchoose :
      ((Nat.choose (s₀ + t - 2) (s₀ - 1) : ℕ) : ℝ) <
        Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) := by
    have hchooseNat : Nat.choose (s₀ + t - 2) (s₀ - 1) ≤ s₀ ^ t := by
      have hdecomp : s₀ + t - 2 = (s₀ - 1) + (t - 1) := by omega
      calc
        Nat.choose (s₀ + t - 2) (s₀ - 1) =
            Nat.choose ((s₀ - 1) + (t - 1)) (s₀ - 1) := by rw [hdecomp]
        _ = Nat.choose ((s₀ - 1) + (t - 1)) (t - 1) := by
          have hh := Nat.choose_symm (n := (s₀ - 1) + (t - 1))
            (k := s₀ - 1) (by omega)
          have hsub : ((s₀ - 1) + (t - 1)) - (s₀ - 1) = t - 1 := by omega
          simpa [hsub] using hh.symm
        _ ≤
            ((s₀ - 1) + 1) ^ (t - 1) := Nat.choose_add_le_add_one_pow _ _
        _ ≤ s₀ ^ t := by
          rw [Nat.sub_add_cancel hs₀]
          exact Nat.pow_le_pow_right (by omega) (by omega)
    have hchooseR :
        ((Nat.choose (s₀ + t - 2) (s₀ - 1) : ℕ) : ℝ) ≤ (s₀ : ℝ) ^ t := by
      exact_mod_cast hchooseNat
    have hExpPow (z : ℝ) (m : ℕ) : Real.exp z ^ m = Real.exp ((m : ℝ) * z) := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, ih, Nat.cast_succ, ← Real.exp_add]
        congr 1
        ring
    have h2exp : (2 : ℝ) * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) =
        Real.exp (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have hpowBound : (s₀ : ℝ) ^ t ≤
        Real.exp ((t : ℝ) * (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100))) := by
      have h2pow : (2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100))) ^ t =
          Real.exp ((t : ℝ) * (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100))) := by
        rw [h2exp, hExpPow]
      calc
        (s₀ : ℝ) ^ t ≤ (2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100))) ^ t :=
          pow_le_pow_left₀ (by positivity) hsReal t
        _ = Real.exp ((t : ℝ) * (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100))) := h2pow
    have hlog23 : Real.log 2 ≤ Real.log 3 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog2 : Real.log 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := hlog23.trans hlog
    have hexponent :
        (t : ℝ) * (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100)) ≤
          4 * (n : ℝ) ^ ((11 : ℝ) / 1000) := by
      have hnα : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 100) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hnβ : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 1000) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hsumPow :
          (n : ℝ) ^ ((1 : ℝ) / 1000) * (n : ℝ) ^ ((1 : ℝ) / 100) =
            (n : ℝ) ^ ((11 : ℝ) / 1000) := by
        rw [← Real.rpow_add hnreal]
        congr 1 <;> norm_num
      calc
        (t : ℝ) * (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100)) ≤
            (2 * (n : ℝ) ^ ((1 : ℝ) / 1000)) *
              (2 * (n : ℝ) ^ ((1 : ℝ) / 100)) := by
                exact mul_le_mul htReal (by nlinarith [hlog2]) (by positivity) (by positivity)
        _ = 4 * (n : ℝ) ^ ((11 : ℝ) / 1000) := by
          calc
            (2 * (n : ℝ) ^ ((1 : ℝ) / 1000)) *
                (2 * (n : ℝ) ^ ((1 : ℝ) / 100)) =
                4 * ((n : ℝ) ^ ((1 : ℝ) / 1000) *
                  (n : ℝ) ^ ((1 : ℝ) / 100)) := by ring
            _ = 4 * (n : ℝ) ^ ((11 : ℝ) / 1000) := by rw [hsumPow]
    have hpowSmall : 4 * (n : ℝ) ^ ((11 : ℝ) / 1000) <
        (n : ℝ) ^ ((1 : ℝ) / 50) := hpow₂
    exact lt_of_le_of_lt hchooseR (lt_of_le_of_lt hpowBound <| by
      calc
        Real.exp ((t : ℝ) * (Real.log 2 + (n : ℝ) ^ ((1 : ℝ) / 100))) ≤
            Real.exp (4 * (n : ℝ) ^ ((11 : ℝ) / 1000)) := Real.exp_le_exp.mpr hexponent
        _ < Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) := Real.exp_lt_exp.mpr hpowSmall)
  let cand : Finset (Fin N) := S.filter fun x =>
    cut < |inter E G π J (Function.update base j x)|
  let pos : Finset (Fin N) := S.filter fun x =>
    cut < inter E G π J (Function.update base j x)
  let neg : Finset (Fin N) := S.filter fun x =>
    cut < -inter E G π J (Function.update base j x)
  change (cand.card : ℝ) ≤ Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100))
  have hsplit (x : Fin N) (hx : x ∈ cand) : x ∈ pos ∪ neg := by
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hbad : cut < |inter E G π J (Function.update base j x)| :=
      (Finset.mem_filter.mp hx).2
    by_cases hpos : 0 < inter E G π J (Function.update base j x)
    · apply Finset.mem_union_left
      simp [pos, hxS, abs_of_pos hpos] at *
      exact hbad
    · have hneg : inter E G π J (Function.update base j x) < 0 := by
        by_contra hn
        have hz : inter E G π J (Function.update base j x) = 0 :=
          le_antisymm (le_of_not_gt hpos) (le_of_not_gt hn)
        simp [hz] at hbad
        linarith [hcut]
      apply Finset.mem_union_right
      simp [neg, hxS, abs_of_neg hneg] at *
      exact hbad
  have hcardCand : (cand.card : ℝ) ≤ (pos.card : ℝ) + (neg.card : ℝ) := by
    calc
      (cand.card : ℝ) ≤ ((pos ∪ neg).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (by
          intro x hx
          exact hsplit x hx)
      _ ≤ (pos.card : ℝ) + (neg.card : ℝ) := by
        exact_mod_cast Finset.card_union_le pos neg
  by_contra hCount
  have hlargeCand : Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100)) < (cand.card : ℝ) := by
    exact lt_of_not_ge hCount
  have hlog2small : Real.log 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 50) := by
    have hlog21 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 50) :=
      Real.one_le_rpow hn1 (by norm_num)
    exact hlog21.trans hpow
  have hhalf : Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) ≤
      Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100)) / 2 := by
    have hgap : (n : ℝ) ^ ((1 : ℝ) / 50) + Real.log 2 ≤
        (n : ℝ) ^ ((3 : ℝ) / 100) := by linarith [hpow₃]
    have hexp := Real.exp_le_exp.mpr hgap
    have hfactor : (2 : ℝ) * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) =
        Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50) + Real.log 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    have htwice : 2 * Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) ≤
        Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100)) := by
      rw [hfactor]
      exact hexp
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith [htwice])
  have hside : Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) < (pos.card : ℝ) ∨
      Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) < (neg.card : ℝ) := by
    by_contra h
    push_neg at h
    have hsum : (cand.card : ℝ) ≤ 2 * (Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100)) / 2) := by
      calc
        (cand.card : ℝ) ≤ (pos.card : ℝ) + (neg.card : ℝ) := hcardCand
        _ ≤ Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100)) / 2 +
              Real.exp ((n : ℝ) ^ ((3 : ℝ) / 100)) / 2 := by
          exact add_le_add (le_trans h.1 hhalf) (le_trans h.2 hhalf)
        _ = _ := by ring
    linarith
  let Hbound : ℝ := (5 : ℝ) ^ u
  let B : ℝ := 2 * Hbound
  have hBpos : 0 < B := by dsimp [B, Hbound]; positivity
  have hMeanRel (x : Fin N) : sMean E G π x = 2 * deg E G π x - 1 := by
    unfold sMean deg fv
    calc
      (∑ y, π y * (2 * hit E G x y - 1)) =
          ∑ y, (2 * (π y * hit E G x y) - π y) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ y, 2 * (π y * hit E G x y)) - ∑ y, π y := by
        rw [Finset.sum_sub_distrib]
      _ = 2 * (∑ y, π y * hit E G x y) - 1 := by
        rw [← Finset.mul_sum, hO.pi_sum]
  have hMeanDen (x : Fin N) : 1 + sMean E G π x = 2 * deg E G π x := by
    rw [hMeanRel x]
    ring
  have hMeanAbs (x : Fin N) (hx : x ∈ S) : |sMean E G π x| ≤ 1 / 2 := by
    calc
      |sMean E G π x| ≤ 4 * bS n := hO.degree x hx
      _ ≤ 4 * (1 / 8) := mul_le_mul_of_nonneg_left hbSmallN (by norm_num)
      _ = 1 / 2 := by norm_num
  have hDenBounds (x : Fin N) (hx : x ∈ S) :
      1 / 2 ≤ 1 + sMean E G π x ∧ 1 + sMean E G π x ≤ 3 / 2 := by
    have h := abs_le.mp (hMeanAbs x hx)
    constructor <;> linarith only [h.1, h.2]
  have hDegLower (x : Fin N) (hx : x ∈ S) : 1 / 4 ≤ deg E G π x := by
    have h := hMeanDen x
    have h' := (hDenBounds x hx).1
    nlinarith only [h, h']
  have haFid (x : Fin N) (hx : x ∈ S) (y : Fin N) :
      aF E G π x y = (fv E G x y - sMean E G π x) / (1 + sMean E G π x) := by
    unfold aF
    rw [hMeanRel x]
    unfold fv
    field_simp [ne_of_gt (by
      have : (0 : ℝ) < 1 / 4 := by norm_num
      exact lt_of_lt_of_le this (hDegLower x hx))]
    ring
  let H : Fin N → ℝ := fun y => ∏ l ∈ J.erase j, aF E G π (base l) y
  have haBound (x : Fin N) (hx : x ∈ S) (y : Fin N) : |aF E G π x y| ≤ 5 := by
    have hden : 1 / 4 ≤ deg E G π x := hDegLower x hx
    have hdenpos : 0 < deg E G π x := lt_of_lt_of_le (by norm_num) hden
    have hhit : |hit E G x y| ≤ 1 := by
      unfold hit
      split_ifs <;> norm_num
    have hfrac : |hit E G x y / deg E G π x| ≤ 4 := by
      rw [abs_div, abs_of_pos hdenpos]
      apply (div_le_iff₀ hdenpos).2
      nlinarith
    unfold aF
    calc
      |hit E G x y / deg E G π x - 1| ≤
          |hit E G x y / deg E G π x| + 1 := by
            simpa using abs_sub (hit E G x y / deg E G π x) 1
      _ ≤ 5 := by linarith
  have hHbound (y : Fin N) : |H y| ≤ Hbound := by
    dsimp [H]
    calc
      |∏ l ∈ J.erase j, aF E G π (base l) y| =
          ∏ l ∈ J.erase j, |aF E G π (base l) y| := by rw [Finset.abs_prod]
      _ ≤ ∏ l ∈ J.erase j, (5 : ℝ) :=
        Finset.prod_le_prod₀ (fun l hl => abs_nonneg _) (fun l hl => haBound (base l) (hbase l) y)
      _ = (5 : ℝ) ^ (J.erase j).card := by simp
      _ ≤ (5 : ℝ) ^ u := by
        apply pow_le_pow_right₀ (by norm_num)
        simpa using Finset.card_le_univ (J.erase j)
  let avgH : ℝ := ∑ y, π y * H y
  have havgAbs : |avgH| ≤ Hbound := by
    have hup : avgH ≤ Hbound := by
      dsimp [avgH]
      calc
        (∑ y, π y * H y) ≤ ∑ y, π y * Hbound := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (le_of_abs_le (hHbound y)) (hO.pi_nonneg y)
        _ = Hbound := by rw [← Finset.sum_mul, hO.pi_sum]; ring
    have hlo : -Hbound ≤ avgH := by
      dsimp [avgH]
      calc
        -Hbound = ∑ y, π y * (-Hbound) := by rw [← Finset.sum_mul, hO.pi_sum]; ring
        _ ≤ ∑ y, π y * H y := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hHbound y)) (hO.pi_nonneg y)
    exact abs_le.mpr ⟨hlo, hup⟩
  let T : Fin N → ℝ := fun y => H y - avgH
  have hTbound (y : Fin N) : |T y| ≤ B := by
    dsimp [T, B]
    calc
      |H y - avgH| ≤ |H y| + |avgH| := abs_sub _ _
      _ ≤ Hbound + Hbound := add_le_add (hHbound y) havgAbs
      _ = 2 * Hbound := by ring
  let P : Fin N → ℝ := fun x => ∑ y, π y * fv E G x y * T y
  have hcenter (x : Fin N) :
      (∑ y, π y * (fv E G x y - sMean E G π x) * H y) = P x := by
    have hleft :
        (∑ y, π y * (fv E G x y - sMean E G π x) * H y) =
          (∑ y, π y * fv E G x y * H y) - sMean E G π x * avgH := by
      calc
        (∑ y, π y * (fv E G x y - sMean E G π x) * H y) =
            ∑ y, (π y * fv E G x y * H y - π y * sMean E G π x * H y) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y, π y * fv E G x y * H y) -
              ∑ y, π y * sMean E G π x * H y := by rw [Finset.sum_sub_distrib]
        _ = (∑ y, π y * fv E G x y * H y) - sMean E G π x * avgH := by
          congr 1
          calc
            (∑ y, π y * sMean E G π x * H y) =
                ∑ y, sMean E G π x * (π y * H y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
            _ = sMean E G π x * avgH := by dsimp [avgH]; rw [Finset.mul_sum]
    have hright : P x =
        (∑ y, π y * fv E G x y * H y) - avgH * sMean E G π x := by
      dsimp [P, T]
      calc
        (∑ y, π y * fv E G x y * (H y - avgH)) =
            ∑ y, (π y * fv E G x y * H y - π y * fv E G x y * avgH) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y, π y * fv E G x y * H y) -
              ∑ y, π y * fv E G x y * avgH := by rw [Finset.sum_sub_distrib]
        _ = (∑ y, π y * fv E G x y * H y) - avgH * sMean E G π x := by
          congr 1
          calc
            (∑ y, π y * fv E G x y * avgH) =
                ∑ y, avgH * (π y * fv E G x y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
            _ = avgH * (∑ y, π y * fv E G x y) := by rw [Finset.mul_sum]
            _ = avgH * sMean E G π x := by rfl
    rw [hleft, hright]
    ring
  have hprodUpdate (x : Fin N) (y : Fin N) :
      (∏ l ∈ J, aF E G π (Function.update base j x l) y) = aF E G π x y * H y := by
    have herase :
        (∏ l ∈ J.erase j, aF E G π (Function.update base j x l) y) = H y := by
      dsimp [H]
      apply Finset.prod_congr rfl
      intro l hl
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hl) x base]
    calc
      (∏ l ∈ J, aF E G π (Function.update base j x l) y) =
          (∏ l ∈ J.erase j, aF E G π (Function.update base j x l) y) *
            aF E G π (Function.update base j x j) y :=
        (Finset.prod_erase_mul J (fun l => aF E G π (Function.update base j x l) y) hj).symm
      _ = H y * aF E G π x y := by rw [herase, Function.update_self]
      _ = aF E G π x y * H y := by ring
  have hinter (x : Fin N) (hx : x ∈ S) :
      inter E G π J (Function.update base j x) =
        (1 + sMean E G π x)⁻¹ * P x := by
    unfold inter
    calc
      (∑ y, π y * ∏ l ∈ J, aF E G π (Function.update base j x l) y) =
          ∑ y, π y * (aF E G π x y * H y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [hprodUpdate x y]
      _ = ∑ y, (1 + sMean E G π x)⁻¹ *
          (π y * (fv E G x y - sMean E G π x) * H y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [haFid x hx y]
        ring
      _ = (1 + sMean E G π x)⁻¹ *
          (∑ y, π y * (fv E G x y - sMean E G π x) * H y) := by
        rw [Finset.mul_sum]
      _ = (1 + sMean E G π x)⁻¹ * P x := by rw [hcenter x]
  have hsideRun (R : Finset (Fin N)) (sgn : ℝ)
      (hRsub : R ⊆ S)
      (hRlarge : Real.exp ((n : ℝ) ^ ((1 : ℝ) / 50)) < (R.card : ℝ))
      (hsgn : sgn = 1 ∨ sgn = -1)
      (hRbad : ∀ x ∈ R, cut < sgn * inter E G π J (Function.update base j x)) : False := by
    classical
    let V := {x : Fin N // x ∈ R}
    let eps : ℝ := 8 * (n : ℝ) ^ (-δ)
    let τ : ℝ := cut / (2 * B)
    let f : V → Fin N → ℝ := fun v y => sgn * fv E G v.1 y
    let g : Fin N → ℝ := fun y => (T y) / B
    let gr : SimpleGraph V := {
      Adj := fun v w => v ≠ w ∧ eps < corr E G π v.1 w.1
      symm := by
        refine ⟨?_⟩
        intro v w hvw
        rcases hvw with ⟨hne, hcorr⟩
        refine ⟨hne.symm, ?_⟩
        have hsym : corr E G π v.1 w.1 = corr E G π w.1 v.1 := by
          unfold corr
          apply Finset.sum_congr rfl
          intro y hy
          ring
        simpa [hsym] using hcorr
      loopless := by
        refine ⟨?_⟩
        intro v hv
        exact hv.1 rfl
    }
    have hsgnSq : sgn ^ 2 = 1 := by rcases hsgn with h | h <;> simp [h]
    have hfvSq (x y : Fin N) : (fv E G x y) ^ 2 = 1 := by
      unfold fv hit
      split_ifs <;> norm_num
    have hfnorm (v : V) : (∑ y, π y * (f v y) ^ 2) ≤ 1 := by
      have hunit (y : Fin N) : (f v y) ^ 2 = 1 := by
        dsimp [f]
        rw [mul_pow, hsgnSq, hfvSq]
        norm_num
      calc
        (∑ y, π y * (f v y) ^ 2) = ∑ y, π y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hunit y]
          ring
        _ = 1 := hO.pi_sum
        _ ≤ 1 := le_rfl
    have hT2 (y : Fin N) : (T y) ^ 2 ≤ B ^ 2 := by
      have habs := abs_le.mp (hTbound y)
      nlinarith only [habs.1, habs.2]
    have hgnorm : (∑ y, π y * (g y) ^ 2) ≤ 1 := by
      calc
        (∑ y, π y * (g y) ^ 2) ≤ ∑ y, π y * 1 := by
          apply Finset.sum_le_sum
          intro y hy
          have hdiv : (T y / B) ^ 2 ≤ 1 := by
            rw [div_pow]
            exact (div_le_one₀ (by positivity : 0 < B ^ 2)).2 (hT2 y)
          exact mul_le_mul_of_nonneg_left hdiv (hO.pi_nonneg y)
        _ = 1 := by simp [hO.pi_sum]
    have hproj (v : V) (hv : v ∈ (Finset.univ : Finset V)) :
        τ ≤ ∑ y, π y * f v y * g y := by
      have hvS : v.1 ∈ S := hRsub v.2
      have hden : 1 / 2 ≤ 1 + sMean E G π v.1 := (hDenBounds v.1 hvS).1
      have hsgnInter := hRbad v.1 v.2
      have hprojP : cut / 2 < sgn * P v.1 := by
        have hmul : cut / 2 < (1 + sMean E G π v.1) *
            (sgn * inter E G π J (Function.update base j v.1)) := by
          have hpositive : 0 < sgn * inter E G π J (Function.update base j v.1) :=
            lt_trans hcut hsgnInter
          calc
            cut / 2 = (1 / 2) * cut := by ring
            _ < (1 / 2) * (sgn * inter E G π J (Function.update base j v.1)) :=
              mul_lt_mul_of_pos_left hsgnInter (by norm_num)
            _ ≤ (1 + sMean E G π v.1) *
                (sgn * inter E G π J (Function.update base j v.1)) :=
              mul_le_mul_of_nonneg_right hden (le_of_lt hpositive)
        have hiden : (1 + sMean E G π v.1) *
            (sgn * inter E G π J (Function.update base j v.1)) = sgn * P v.1 := by
          rw [hinter v.1 hvS]
          have hdenpos : 0 < 1 + sMean E G π v.1 :=
            lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden
          field_simp [ne_of_gt hdenpos]
        rw [← hiden]
        exact hmul
      have hprojId : (∑ y, π y * f v y * g y) = (sgn * P v.1) / B := by
        calc
          (∑ y, π y * (sgn * fv E G v.1 y) * (T y / B)) =
              (∑ y, π y * (sgn * fv E G v.1 y) * T y) / B := by
                rw [Finset.sum_div]
                apply Finset.sum_congr rfl
                intro y hy
                ring
          _ = (sgn * P v.1) / B := by
            congr 1
            dsimp [P]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            ring
      dsimp [τ]
      rw [hprojId]
      apply le_of_lt
      have hτrewrite : cut / (2 * B) = (cut / 2) / B := by
        field_simp [ne_of_gt hBpos]
      rw [hτrewrite]
      apply (div_lt_div_iff₀ hBpos hBpos).2
      exact mul_lt_mul_of_pos_right hprojP hBpos
    have hfcorr (v w : V) :
        (∑ y, π y * f v y * f w y) = corr E G π v.1 w.1 := by
      calc
        (∑ y, π y * (sgn * fv E G v.1 y) * (sgn * fv E G w.1 y)) =
            sgn ^ 2 * (∑ y, π y * fv E G v.1 y * fv E G w.1 y) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = corr E G π v.1 w.1 := by
          rw [hsgnSq]
          simp [HypercubeRamsey.corr]
    have hclique (C : Finset V) (hCcard : C.card = s₀)
        (hC : ∀ v ∈ C, ∀ w ∈ C, v ≠ w → gr.Adj v w) : False := by
      let emb : V ↪ Fin N := ⟨Subtype.val, fun a b h => Subtype.ext h⟩
      let C' := C.map emb
      have hC'card : C'.card = s₀ := by simpa [C'] using hCcard
      have hC'sub : C' ⊆ S := by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
        exact hRsub v.2
      obtain ⟨x, hx, z, hz, hxz, hlow⟩ := hO.noClique C' hC'sub hC'card
      rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
      rcases Finset.mem_map.mp hz with ⟨w, hw, rfl⟩
      have hne : v ≠ w := by
        intro h
        apply hxz
        exact congrArg Subtype.val h
      have hhigh := (hC v hv w hw hne).2
      exact (not_lt_of_ge hlow) hhigh
    have hindependent (I : Finset V) (hIcard : I.card = t)
        (hI : ∀ v ∈ I, ∀ w ∈ I, v ≠ w → ¬ gr.Adj v w) : False := by
      have hlowcorr (v : V) (hv : v ∈ I) (w : V) (hw : w ∈ I) (hne : v ≠ w) :
          (∑ y, π y * f v y * f w y) ≤ eps := by
        apply le_of_not_gt
        intro hlt
        apply hI v hv w hw hne
        refine ⟨hne, ?_⟩
        simpa [gr, eps, hfcorr] using hlt
      have hcutSq : cut ^ 2 = (n : ℝ) ^ (-θ) := by
        dsimp [cut, θ]
        calc
          ((n : ℝ) ^ (-(δ / 4))) ^ 2 =
              (n : ℝ) ^ ((-(δ / 4)) * 2) :=
                (Real.rpow_mul_natCast hnreal.le (-(δ / 4)) 2).symm
          _ = (n : ℝ) ^ (-(δ / 2)) := by congr 1 <;> ring
      have htBase : (n : ℝ) ^ ((1 : ℝ) / 1000) ≤ (t : ℝ) := by
        dsimp [t, t₀]
        exact Nat.le_ceil _
      have hinvT : 1 / (t : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 1000) := by
          have hpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 1000) :=
            Real.rpow_pos_of_pos hnreal _
          have hrecip : 1 / (t : ℝ) ≤ 1 / ((n : ℝ) ^ ((1 : ℝ) / 1000)) :=
            one_div_le_one_div_of_le hpos htBase
          calc
            1 / (t : ℝ) ≤ 1 / ((n : ℝ) ^ ((1 : ℝ) / 1000)) := hrecip
            _ = ((n : ℝ) ^ ((1 : ℝ) / 1000))⁻¹ := by rw [one_div]
            _ = (n : ℝ) ^ (-((1 : ℝ) / 1000)) := by rw [Real.rpow_neg hnreal.le]
            _ = (n : ℝ) ^ (-(1 : ℝ) / 1000) := by congr 1 <;> ring
      have hfirst : 1 / (t : ℝ) < (n : ℝ) ^ (-θ) / (8 * B ^ 2) := by
        have h' : (n : ℝ) ^ (-(1 : ℝ) / 1000) <
            (n : ℝ) ^ (-θ) / (8 * B ^ 2) := by
          apply (lt_div_iff₀ (by positivity : 0 < 8 * B ^ 2)).2
          simpa [mul_assoc, mul_left_comm, mul_comm] using hgram₁
        exact lt_of_le_of_lt hinvT h'
      have hsecond : eps < (n : ℝ) ^ (-θ) / (8 * B ^ 2) := by
        dsimp [eps]
        apply (lt_div_iff₀ (by positivity : 0 < 8 * B ^ 2)).2
        convert hgram₂ using 1 <;> ring
      have hτsq : τ ^ 2 = (n : ℝ) ^ (-θ) / (4 * B ^ 2) := by
        dsimp [τ]
        calc
          (cut / (2 * B)) ^ 2 = cut ^ 2 / (4 * B ^ 2) := by
            field_simp [ne_of_gt hBpos]
            ring
          _ = (n : ℝ) ^ (-θ) / (4 * B ^ 2) := by rw [hcutSq]
      have hgap : 1 / (t : ℝ) + eps < τ ^ 2 := by
        rw [hτsq]
        have hsum : 1 / (t : ℝ) + eps <
            (n : ℝ) ^ (-θ) / (8 * B ^ 2) + (n : ℝ) ^ (-θ) / (8 * B ^ 2) :=
          add_lt_add hfirst hsecond
        have hEq : (n : ℝ) ^ (-θ) / (8 * B ^ 2) +
            (n : ℝ) ^ (-θ) / (8 * B ^ 2) = (n : ℝ) ^ (-θ) / (4 * B ^ 2) := by
          field_simp [ne_of_gt hBpos]
          ring
        exact lt_of_lt_of_eq hsum hEq
      exact OuterMoment_q_s11_outer.weighted_gram_clique_impossible I t
        (by exact_mod_cast ht) hIcard π hO.pi_nonneg f hfnorm g hgnorm τ eps
        (by positivity) (by positivity) hgap hlowcorr
        (by intro v hv; exact hproj v (Finset.mem_univ v))
    have hcardV : Fintype.card V < Nat.choose (s₀ + t - 2) (s₀ - 1) := by
      apply OuterMoment_q_s11_outer.card_lt_ramsey_of_forbidden gr s₀ t hs₀
      · exact_mod_cast ht
      · intro C hCcard hC
        exact hclique C hCcard hC
      · intro I hIcard hI
        exact hindependent I hIcard hI
    have hVcard : Fintype.card V = R.card := by simp [V]
    have hRchoose : (R.card : ℝ) <
        ((Nat.choose (s₀ + t - 2) (s₀ - 1) : ℕ) : ℝ) := by
      exact_mod_cast (hVcard ▸ hcardV)
    linarith [hRlarge, hchoose]
  rcases hside with hpos | hneg
  · exact hsideRun pos 1 (by
      intro x hx
      exact (Finset.mem_filter.mp hx).1) hpos (Or.inl rfl) (by
      intro x hx
      simpa using (Finset.mem_filter.mp hx).2)
  · exact hsideRun neg (-1) (by
      intro x hx
      exact (Finset.mem_filter.mp hx).1) hneg (Or.inr rfl) (by
      intro x hx
      simpa using (Finset.mem_filter.mp hx).2)

/-- L11.3e (11:282–292).  On `w ≤ n^{-1.03}` the weight is at most `e^{2^u n^{-.03}}`; on
`n^{-1.03} < w ≤ n^{-1+.06}` use the two-free estimate (`C_u e^{2^u n^{.06} - n^{.4}}`), on
`n^{-1+.06} < w ≤ n^{-υ}` the one-free estimate (`C_u e^{2^u n^{1-υ} - n^{1-υ/4}/2}`); finitely many `u ≤ U`. -/
theorem moderate (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hA : OneFreeEv δ x₀ K) (hB : TwoFreeEv δ x₀ K) : ModerateEv δ x₀ K := by
  sorry

/-- The moment identity (11:295–300): expand `(Z - 1)^u` binomially over subsets `I ⊆ [u]`, write `Z^{|I|}` as an
integral over `|I|` independent `σ`-labels, integrate the independent outer labels (each factor gives
`∫ ∏_{j ∈ I} (1 + a_{x_j}) dπ`), and extend to `u` coordinates (`σ` has mass one). -/
theorem moment_identity {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (π σ : Fin N → ℝ) (D : Type)
    [Fintype D] [DecidableEq D] (u : ℕ) (hσ : ∑ x, σ x = 1) : MomentIdentity E G π σ D u := by
  classical
  unfold MomentIdentity
  have hZ (Yv : D → Fin N) :
      outerZ E G π σ Yv - 1 =
        ∑ x, σ x * ((∏ l, (1 + aF E G π x (Yv l))) - 1) := by
    unfold outerZ
    calc
      (∑ x, σ x * ∏ l, (1 + aF E G π x (Yv l))) - 1 =
          (∑ x, σ x * ∏ l, (1 + aF E G π x (Yv l))) - ∑ x, σ x := by rw [hσ]
      _ = ∑ x, (σ x * ∏ l, (1 + aF E G π x (Yv l)) - σ x) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ x, σ x * ((∏ l, (1 + aF E G π x (Yv l))) - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hprod (x : Fin u → Fin N) (Yv : D → Fin N) :
      (∏ j : Fin u, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) =
        ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)) := by
    calc
      (∏ j : Fin u, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) =
          ∏ j : Fin u, ((∏ l, (1 + aF E G π (x j) (Yv l))) + (-1 : ℝ)) := by
        apply Finset.prod_congr rfl
        intro j hj
        ring
      _ = ∑ I : Finset (Fin u),
          (∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l))) *
            ∏ j ∈ Iᶜ, (-1 : ℝ) := by
        exact Fintype.prod_add (fun j : Fin u => ∏ l, (1 + aF E G π (x j) (Yv l)))
          (fun _ => (-1 : ℝ))
      _ = ∑ I : Finset (Fin u),
          (∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l))) *
            (-1 : ℝ) ^ (u - I.card) := by
        apply Finset.sum_congr rfl
        intro I hI
        simp [Finset.prod_const, Finset.card_compl, Fintype.card_fin]
      _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)) := by
        apply Finset.sum_congr rfl
        intro I hI
        ring
  have hI (x : Fin u → Fin N) (I : Finset (Fin u)) :
      (∑ Yv : D → Fin N, outWt π Yv *
        (∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)))) =
      (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ Fintype.card D := by
    calc
      (∑ Yv : D → Fin N, outWt π Yv *
          (∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)))) =
        ∑ Yv : D → Fin N, ∏ l, (π (Yv l) *
          (∏ j ∈ I, (1 + aF E G π (x j) (Yv l)))) := by
        apply Finset.sum_congr rfl
        intro Yv hYv
        simp only [outWt]
        calc
          (∏ l, π (Yv l)) * ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)) =
              (∏ l, π (Yv l)) * ∏ l, ∏ j ∈ I, (1 + aF E G π (x j) (Yv l)) := by
            congr 1
            exact Finset.prod_comm (s := I) (t := Finset.univ)
          _ = ∏ l, π (Yv l) * ∏ j ∈ I, (1 + aF E G π (x j) (Yv l)) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ l : D, ∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y) := by
        symm
        exact Fintype.prod_sum (fun (_ : D) (y : Fin N) =>
          π y * ∏ j ∈ I, (1 + aF E G π (x j) y))
      _ = (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ Fintype.card D := by
        simp
  have hkernel (x : Fin u → Fin N) :
      (∑ Yv : D → Fin N, outWt π Yv *
        ∏ j : Fin u, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) =
      ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
        (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ Fintype.card D := by
    calc
      (∑ Yv : D → Fin N, outWt π Yv *
          ∏ j : Fin u, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) =
        ∑ Yv : D → Fin N, ∑ I : Finset (Fin u),
          (outWt π Yv * (-1 : ℝ) ^ (u - I.card)) *
            ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)) := by
        apply Finset.sum_congr rfl
        intro Yv hYv
        rw [hprod x Yv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I hI'
        ring
      _ = ∑ I : Finset (Fin u), ∑ Yv : D → Fin N,
          (outWt π Yv * (-1 : ℝ) ^ (u - I.card)) *
            ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)) := by
        rw [Finset.sum_comm]
      _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          (∑ Yv : D → Fin N, outWt π Yv *
            ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l))) := by
        apply Finset.sum_congr rfl
        intro I hI'
        calc
          (∑ Yv : D → Fin N,
              (outWt π Yv * (-1 : ℝ) ^ (u - I.card)) *
                ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l))) =
              ∑ Yv : D → Fin N, (-1 : ℝ) ^ (u - I.card) *
                (outWt π Yv * ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l))) := by
            apply Finset.sum_congr rfl
            intro Yv hYv
            ring
          _ = (-1 : ℝ) ^ (u - I.card) *
              ∑ Yv : D → Fin N, outWt π Yv *
                ∏ j ∈ I, ∏ l, (1 + aF E G π (x j) (Yv l)) := by
            rw [← Finset.mul_sum]
      _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ Fintype.card D := by
        apply Finset.sum_congr rfl
        intro I hI'
        rw [hI x I]
  calc
    (∑ Yv : D → Fin N, outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) =
        ∑ Yv : D → Fin N, outWt π Yv *
          (∑ x, σ x * ((∏ l, (1 + aF E G π x (Yv l))) - 1)) ^ u := by
      apply Finset.sum_congr rfl
      intro Yv hYv
      rw [hZ Yv]
    _ = ∑ Yv : D → Fin N, outWt π Yv *
        ∑ x : Fin u → Fin N, ∏ j, σ (x j) *
          ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1) := by
      apply Finset.sum_congr rfl
      intro Yv hYv
      rw [Fintype.sum_pow]
    _ = ∑ Yv : D → Fin N, ∑ x : Fin u → Fin N, outWt π Yv *
        ∏ j, σ (x j) * ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1) := by
      apply Finset.sum_congr rfl
      intro Yv hYv
      rw [Finset.mul_sum]
    _ = ∑ x : Fin u → Fin N, ∑ Yv : D → Fin N, outWt π Yv *
        ∏ j, σ (x j) * ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1) := by
      rw [Finset.sum_comm]
    _ = ∑ x : Fin u → Fin N, tupWt σ x *
        (∑ Yv : D → Fin N, outWt π Yv *
          ∏ j, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [tupWt]
      calc
        (∑ Yv : D → Fin N, outWt π Yv *
            ∏ j, σ (x j) * ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) =
          ∑ Yv : D → Fin N, (∏ j, σ (x j)) *
            (outWt π Yv * ∏ j, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1)) := by
          apply Finset.sum_congr rfl
          intro Yv hYv
          rw [Finset.prod_mul_distrib]
          ring
        _ = (∏ j, σ (x j)) *
            ∑ Yv : D → Fin N, outWt π Yv *
              ∏ j, ((∏ l, (1 + aF E G π (x j) (Yv l))) - 1) := by
          rw [Finset.mul_sum]
    _ = ∑ x : Fin u → Fin N, tupWt σ x *
        (∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          (∑ y, π y * ∏ j ∈ I, (1 + aF E G π (x j) y)) ^ Fintype.card D) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hkernel x]
    _ = ∑ x : Fin u → Fin N, tupWt σ x * phiU E G π (Fintype.card D) u x := by
      simp [phiU]

/-- L11.3f (11:294–309).  Choose `L = L(P)` and then an even `u` with `.4u/L > L + P + O(1)`.  On
`w ≤ n^{-1.03}` expand each of the `d` factors into its interactions: only lists covering `[u]` survive the
alternating sum; lists of more than `L` interactions give the geometric tail in `2^u n^{-.03}`, lists of at most
`L` interactions contain one of size `≥ u/L` and give `O_u(n^{L - .4u/L})` (mean interaction size).  On
`n^{-1.03} < w ≤ n^{-υ}` each positive product is at most `e^{2^u n w}` (exponential weights). -/
theorem small_range (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hC : MeanInterEv δ x₀ K) (hE : ModerateEv δ x₀ K) (P : ℝ) (hP : 0 < P) :
    ∃ u : ℕ, Even u ∧ 0 < u ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop}
      {X Y : Finset (Fin N)} (G : Colour) (π σ : Fin N → ℝ) (S : Finset (Fin N)),
      OuterHyp δ x₀ K n N E X Y G π σ S → SmallRange E G π σ (Fintype.card (OuterCoord n)) n δ P u := by
  sorry

/-- L11.3g (11:311–327).  For a tuple with `w > n^{-υ}` fix a maximal retained set `R` (all interactions within `R`
at most `n^{-υ}`); each omitted coordinate lies in `B_R`, `|B_R| ≤ 2^u e^{n^.03}` (counting large extensions),
and costs `|B_R| max σ max_x D_x^{-d} ≤ (2^n/N) exp(-.5gh + O(n^.05) + n^.03 + O_u(1)) = n^{-ω(1)}`; the retained
positive product has bounded integral (exponential weights at length `|R| < u`). -/
theorem large_range (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hD : CountExtEv δ x₀ K) (hE : ModerateEv δ x₀ K) (u : ℕ) (P : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
      (π σ : Fin N → ℝ) (S : Finset (Fin N)),
      OuterHyp δ x₀ K n N E X Y G π σ S → LargeRange E G π σ (Fintype.card (OuterCoord n)) n δ P u := by
  sorry

/-- Markov's inequality on the even moment (11:329): `Z < 1/2` forces `(Z - 1)^u ≥ 2^{-u}`, and
`E(Z - 1)^u = ∫ Φ_u ≤ ∫ |Φ_u| ≤ 2 · 2^{-(u+2)} n^{-P}`. -/
theorem tail_of_ranges {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
    {π σ : Fin N → ℝ} {S : Finset (Fin N)} {δ x₀ K P : ℝ} {n : ℕ} (u : ℕ) (hu : Even u)
    (hO : OuterHyp δ x₀ K n N E X Y G π σ S) (hid : MomentIdentity E G π σ (OuterCoord n) u)
    (hs : SmallRange E G π σ (Fintype.card (OuterCoord n)) n δ P u)
    (hl : LargeRange E G π σ (Fintype.card (OuterCoord n)) n δ P u) :
    outerFail E G π σ (OuterCoord n) ≤ (n : ℝ) ^ (-P) := by
  classical
  have hsplit (x : Fin u → Fin N) :
      (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
        then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0) +
      (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
        then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0) =
      |phiU E G π (Fintype.card (OuterCoord n)) u x| := by
    by_cases h : env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
    · simp [h, not_lt_of_ge h]
    · have h' : (n : ℝ) ^ (-(δ / 4)) < env E G π x := lt_of_not_ge h
      simp [h, h']
  have habs :
      (∑ x : Fin u → Fin N, tupWt σ x *
        |phiU E G π (Fintype.card (OuterCoord n)) u x|) ≤
      2 * ((2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P)) := by
    change (∑ x : Fin u → Fin N, tupWt σ x *
        (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
          then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) ≤
      (2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P) at hs
    change (∑ x : Fin u → Fin N, tupWt σ x *
        (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
          then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) ≤
      (2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P) at hl
    calc
      (∑ x : Fin u → Fin N, tupWt σ x *
          |phiU E G π (Fintype.card (OuterCoord n)) u x|) =
        ∑ x : Fin u → Fin N, tupWt σ x *
          ((if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
              then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0) +
            (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
              then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hsplit x]
      _ = (∑ x : Fin u → Fin N, tupWt σ x *
            (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
              then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) +
          (∑ x : Fin u → Fin N, tupWt σ x *
            (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
              then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) := by
        calc
          (∑ x : Fin u → Fin N, tupWt σ x *
              ((if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
                  then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0) +
                (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
                  then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0))) =
            ∑ x : Fin u → Fin N, (tupWt σ x *
              (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
                then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0) +
              tupWt σ x *
                (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
                  then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = (∑ x : Fin u → Fin N, tupWt σ x *
                (if env E G π x ≤ (n : ℝ) ^ (-(δ / 4))
                  then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) +
              (∑ x : Fin u → Fin N, tupWt σ x *
                (if (n : ℝ) ^ (-(δ / 4)) < env E G π x
                  then |phiU E G π (Fintype.card (OuterCoord n)) u x| else 0)) := by
            rw [Finset.sum_add_distrib]
      _ ≤ (2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P) +
          (2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P) := add_le_add hs hl
      _ = 2 * ((2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P)) := by ring
  have htup_nonneg (x : Fin u → Fin N) : 0 ≤ tupWt σ x := by
    unfold tupWt
    exact Finset.prod_nonneg (fun j hj => hO.sigma_nonneg (x j))
  have hmomentId :
      (∑ Yv : OuterCoord n → Fin N, outWt π Yv *
        (outerZ E G π σ Yv - 1) ^ u) =
      ∑ x : Fin u → Fin N,
        tupWt σ x * phiU E G π (Fintype.card (OuterCoord n)) u x := by
    simpa [MomentIdentity] using hid
  have hmoment :
      (∑ Yv : OuterCoord n → Fin N, outWt π Yv *
        (outerZ E G π σ Yv - 1) ^ u) ≤
      2 * ((2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P)) := by
    calc
      (∑ Yv : OuterCoord n → Fin N, outWt π Yv *
          (outerZ E G π σ Yv - 1) ^ u) =
        ∑ x : Fin u → Fin N,
          tupWt σ x * phiU E G π (Fintype.card (OuterCoord n)) u x := hmomentId
      _ ≤ ∑ x : Fin u → Fin N, tupWt σ x *
          |phiU E G π (Fintype.card (OuterCoord n)) u x| := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (htup_nonneg x)
      _ ≤ 2 * ((2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P)) := habs
  have hscale :
      (2 : ℝ) ^ u * (2 * (2 : ℝ) ^ (-((u : ℝ) + 2))) = 1 / 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) u]
    rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)) ((u : ℝ) + 2)]
    have hplus : (2 : ℝ) ^ ((u : ℝ) + 2) = (2 : ℝ) ^ u * 4 := by
      rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ)) (u : ℝ) 2]
      norm_num [Real.rpow_natCast]
    rw [hplus]
    have huPow : (2 : ℝ) ^ u ≠ 0 := pow_ne_zero u (by norm_num)
    field_simp [huPow]
    rw [Real.rpow_natCast]
    norm_num
  have houtWt_nonneg (Yv : OuterCoord n → Fin N) : 0 ≤ outWt π Yv := by
    unfold outWt
    exact Finset.prod_nonneg (fun l hl => hO.pi_nonneg (Yv l))
  have hpoint (Yv : OuterCoord n → Fin N) :
      outWt π Yv * (if outerZ E G π σ Yv < 1 / 2 then 1 else 0) ≤
        (2 : ℝ) ^ u * (outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) := by
    by_cases hz : outerZ E G π σ Yv < 1 / 2
    · have hgap : (1 / 2 : ℝ) ≤ 1 - outerZ E G π σ Yv := by linarith
      have hpow : (1 / 2 : ℝ) ^ u ≤ (1 - outerZ E G π σ Yv) ^ u :=
        pow_le_pow_left₀ (by norm_num) hgap u
      have hneg : (1 - outerZ E G π σ Yv) ^ u =
          (outerZ E G π σ Yv - 1) ^ u := by
        calc
          (1 - outerZ E G π σ Yv) ^ u =
              (-(outerZ E G π σ Yv - 1)) ^ u := by congr 1 <;> ring
          _ = (outerZ E G π σ Yv - 1) ^ u := hu.neg_pow _
      have hmarkov : 1 ≤
          (2 : ℝ) ^ u * (outerZ E G π σ Yv - 1) ^ u := by
        calc
          1 = ((2 : ℝ) * (1 / 2)) ^ u := by norm_num
          _ = (2 : ℝ) ^ u * (1 / 2 : ℝ) ^ u := by rw [mul_pow]
          _ ≤ (2 : ℝ) ^ u * (1 - outerZ E G π σ Yv) ^ u :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = (2 : ℝ) ^ u * (outerZ E G π σ Yv - 1) ^ u := by rw [hneg]
      rw [if_pos hz]
      calc
        outWt π Yv * 1 = outWt π Yv := by ring
        _ ≤ outWt π Yv *
            ((2 : ℝ) ^ u * (outerZ E G π σ Yv - 1) ^ u) :=
          by simpa using mul_le_mul_of_nonneg_left hmarkov (houtWt_nonneg Yv)
        _ = (2 : ℝ) ^ u *
            (outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) := by ring
    · rw [if_neg hz]
      simpa using mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) u)
        (mul_nonneg (houtWt_nonneg Yv) (hu.pow_nonneg _))
  have hfail :
      outerFail E G π σ (OuterCoord n) ≤
        (2 : ℝ) ^ u *
          (∑ Yv : OuterCoord n → Fin N,
            outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) := by
    unfold outerFail
    calc
      (∑ Yv : OuterCoord n → Fin N,
          outWt π Yv * (if outerZ E G π σ Yv < 1 / 2 then 1 else 0)) ≤
        ∑ Yv : OuterCoord n → Fin N,
          (2 : ℝ) ^ u * (outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) := by
        apply Finset.sum_le_sum
        intro Yv hYv
        exact hpoint Yv
      _ = (2 : ℝ) ^ u *
          (∑ Yv : OuterCoord n → Fin N,
            outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) := by
        rw [Finset.mul_sum]
  calc
    outerFail E G π σ (OuterCoord n) ≤
        (2 : ℝ) ^ u *
          (∑ Yv : OuterCoord n → Fin N,
            outWt π Yv * (outerZ E G π σ Yv - 1) ^ u) := hfail
    _ ≤ (2 : ℝ) ^ u *
        (2 * ((2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P))) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = (1 / 2 : ℝ) * (n : ℝ) ^ (-P) := by
      calc
        (2 : ℝ) ^ u *
            (2 * ((2 : ℝ) ^ (-((u : ℝ) + 2)) * (n : ℝ) ^ (-P))) =
          ((2 : ℝ) ^ u * (2 * (2 : ℝ) ^ (-((u : ℝ) + 2)))) *
            (n : ℝ) ^ (-P) := by ring
        _ = (1 / 2 : ℝ) * (n : ℝ) ^ (-P) := by rw [hscale]
    _ ≤ (n : ℝ) ^ (-P) := by
      simpa using mul_le_mul_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-P))

/-- Lemma 11.3 (11:167–331) assembled. -/
theorem outer_mass_tail (δ x₀ K P : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀)
    (hx₀' : x₀ < 1) (hK : 0 < K) (hP : 0 < P) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, OuterTailAt δ x₀ K P n := by
  have hA := one_free δ x₀ K hδ hδ' hx₀ hx₀' hK
  have hB := two_free δ x₀ K hδ hδ' hx₀ hx₀' hK
  have hC := mean_inter δ x₀ K hδ hδ' hx₀ hx₀' hK
  have hD := count_ext δ x₀ K hδ hδ' hx₀ hx₀' hK
  have hE := moderate δ x₀ K hδ hδ' hx₀ hx₀' hK hA hB
  obtain ⟨u, hu, _hu0, n₁, hsmall⟩ := small_range δ x₀ K hδ hδ' hx₀ hx₀' hK hC hE P hP
  obtain ⟨n₂, hlarge⟩ := large_range δ x₀ K hδ hδ' hx₀ hx₀' hK hD hE u P
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn N E X Y G π σ S hO
  exact tail_of_ranges u hu hO (moment_identity E G π σ (OuterCoord n) u hO.sigma_sum)
    (hsmall n (le_trans (le_max_left _ _) hn) G π σ S hO)
    (hlarge n (le_trans (le_max_right _ _) hn) G π σ S hO)

end HypercubeRamsey.S11.Core
