import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S11.Core.OuterMoment_q_s11_outer
import HypercubeRamsey.S11.Core.OuterMoment_sol_s11_range
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

set_option maxHeartbeats 800000 in
/-- L11.3b (11:207–252).  `t = ⌈n^.25⌉` conditioned samples from `σ|_{E_x}`, `‖E_{ρ_x} a_z‖_{L²(π)} = O(b_*)` by
(11.1), `E‖S‖² = O_u(t)`, Fubini to a fixed norm-good tuple whose simultaneous violation set has `x`-mass
`e^{-O(t n^.4)}` (width `O(n^.65)`), the projection identity and the equal-normalizer pair `π_±`
(F-SignedTest): `O_u(b_* √t) = O_u(n^{-.825})` against `t n^{-1.03} = n^{-.78+o(1)}`.  Diagonal pairs have
probability `≤ max σ ≤ e^{h}/N`. -/
theorem two_free (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : TwoFreeEv δ x₀ K := by
  classical
  unfold TwoFreeEv
  intro u
  let a : ℝ := 1 - δ / 16
  let Hbound : ℝ := (5 : ℝ) ^ u
  let B : ℝ := 2 * Hbound
  let tσ : ℕ → ℝ := fun n => (Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n)
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hgap := OuterMoment_q_s11_outer.eventually_pow_gap
    ((1 : ℝ) / 10) a (8 : ℝ) (by dsimp [a]; nlinarith) (by norm_num)
  have hgapFiber := OuterMoment_q_s11_outer.eventually_pow_gap
    ((2 : ℝ) / 5) a (8 : ℝ) (by dsimp [a]; nlinarith) (by norm_num)
  have hgapTuple := OuterMoment_q_s11_outer.eventually_pow_gap
    ((13 : ℝ) / 20) a (16 : ℝ) (by dsimp [a]; nlinarith) (by norm_num)
  have hgapTail := OuterMoment_q_s11_outer.eventually_pow_gap
    (x₀ / 4) x₀ (32 / x₀) (by nlinarith [hx₀]) (by positivity)
  have hbT : Tendsto (fun n : ℕ => bS n) atTop (nhds (0 : ℝ)) := by
    simpa [bS, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (19 : ℝ) / 20)).comp
        tendsto_natCast_atTop_atTop
  have hbSmall : ∀ᶠ n : ℕ in atTop, bS n ≤ 1 / 8 := by
    have h := hbT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [h] with n hn
    exact hn.le
  have hPiTend : Tendsto (fun n : ℕ => (n : ℝ) ^ x₀) atTop atTop :=
    (tendsto_rpow_atTop hx₀).comp tendsto_natCast_atTop_atTop
  have hPiWidth : ∀ᶠ n : ℕ in atTop,
      Real.log K + Real.log (2 * B + 2) ≤ (n : ℝ) ^ x₀ := by
    filter_upwards [hPiTend.eventually_gt_atTop (Real.log K + Real.log (2 * B + 2))]
      with n hn
    exact hn.le
  have hnLarge : ∀ᶠ n : ℕ in atTop, 64 ≤ n :=
    eventually_atTop.mpr ⟨64, fun _ hn => hn⟩
  have hKHalf : ∀ᶠ n : ℕ in atTop, Real.log K ≤ (n : ℝ) ^ x₀ / 2 := by
    filter_upwards [hPiTend.eventually_gt_atTop (2 * Real.log K)] with n hn
    linarith
  have hScale : ∀ᶠ n : ℕ in atTop,
      64 ≤ n ∧ bS n ≤ 1 / 8 ∧ tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 ∧
        Real.log K + Real.log (2 * B + 2) ≤ (n : ℝ) ^ x₀ ∧
        8 * (n : ℝ) ^ ((2 : ℝ) / 5) < (n : ℝ) ^ a ∧
        16 * (n : ℝ) ^ ((13 : ℝ) / 20) < (n : ℝ) ^ a ∧
        Real.log K ≤ (n : ℝ) ^ x₀ / 2 ∧
        (32 / x₀) * (n : ℝ) ^ (x₀ / 4) < (n : ℝ) ^ x₀ := by
    filter_upwards [hnLarge, hbSmall, hgap, hPiWidth, hgapFiber, hgapTuple, hKHalf, hgapTail]
      with n hn hb hg hp hgf hgt hk ht
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
      exact Real.one_le_rpow hn1 (by norm_num)
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
              exact mul_le_mul_of_nonneg_right (by linarith)
                (by exact_mod_cast Nat.cast_nonneg (Fintype.card (InnerCoord n)))
        _ ≤ (hIn n : ℝ) := by simpa using hcard
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := hfloor
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hwidth : tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 := by
      nlinarith [htσ, hlog3, hpow, hg]
    exact ⟨hn, hb, hwidth, hp, hgf, hgt, hk, ht⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hScale
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G π σ S hO
  intro J j j' hj hj' hjj base hbase
  have hpars := hn₀ n hn
  rcases hpars with ⟨hn64, hbSmallN, hwidthN, hpiWidthN, hfiberGap, htupleGap,
    hKHalfN, htailGap⟩
  have hNpos : 0 < (N : ℝ) := by
    have hNnat : 0 < N := lt_of_lt_of_le (by positivity) hO.host
    exact_mod_cast hNnat
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
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
    constructor <;> linarith
  have hDegLower (x : Fin N) (hx : x ∈ S) : 1 / 4 ≤ deg E G π x := by
    have h := hMeanDen x
    have h' := (hDenBounds x hx).1
    nlinarith
  have haFid (x : Fin N) (hx : x ∈ S) (y : Fin N) :
      aF E G π x y = (fv E G x y - sMean E G π x) / (1 + sMean E G π x) := by
    unfold aF
    rw [hMeanDen x]
    unfold fv
    have hdeg : 0 < deg E G π x := lt_of_lt_of_le (by norm_num) (hDegLower x hx)
    field_simp [ne_of_gt hdeg]
    <;> nlinarith [hMeanDen x]
  have haBound (x : Fin N) (hx : x ∈ S) (y : Fin N) : |aF E G π x y| ≤ 5 := by
    have hmean : |sMean E G π x| ≤ 1 / 2 := hMeanAbs x hx
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
      |hit E G x y / deg E G π x - 1| ≤ |hit E G x y / deg E G π x| + 1 := by
        simpa using abs_sub (hit E G x y / deg E G π x) 1
      _ ≤ 5 := by linarith
  let threshold : ℝ := (n : ℝ) ^ (-(103 : ℝ) / 100)
  let ε : ℝ := Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))
  let ρ : ℝ := ε / 4
  have hthreshold_pos : 0 < threshold := by dsimp [threshold]; positivity
  have hεpos : 0 < ε := by dsimp [ε]; exact Real.exp_pos _
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  let τ : ℝ := Real.exp (-((n : ℝ) ^ x₀ / 4))
  have hτpos : 0 < τ := by dsimp [τ]; exact Real.exp_pos _
  have hn1R : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogPower : Real.log (n : ℝ) ≤
      (n : ℝ) ^ (x₀ / 4) / (x₀ / 4) :=
    Real.log_natCast_le_rpow_div n (by positivity)
  have hLogTail : 8 * Real.log (n : ℝ) < (n : ℝ) ^ x₀ := by
    calc
      8 * Real.log (n : ℝ) ≤ 8 * ((n : ℝ) ^ (x₀ / 4) / (x₀ / 4)) :=
        mul_le_mul_of_nonneg_left hlogPower (by norm_num)
      _ = (32 / x₀) * (n : ℝ) ^ (x₀ / 4) := by field_simp [ne_of_gt hx₀]; ring
      _ < (n : ℝ) ^ x₀ := htailGap
  have hτExp : τ ≤ (n : ℝ) ^ (-(2 : ℝ)) := by
    have harg : -((n : ℝ) ^ x₀ / 4) ≤ -2 * Real.log (n : ℝ) := by
      nlinarith [hLogTail]
    calc
      τ = Real.exp (-((n : ℝ) ^ x₀ / 4)) := rfl
      _ ≤ Real.exp (-2 * Real.log (n : ℝ)) := Real.exp_le_exp.mpr harg
      _ = (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hnreal]
        congr 1
        ring
  have hBsq : bS n ^ 2 = (n : ℝ) ^ (-(19 : ℝ) / 10) := by
    dsimp [bS]
    calc
      ((n : ℝ) ^ (-(19 : ℝ) / 20)) ^ 2 =
          (n : ℝ) ^ ((-(19 : ℝ) / 20) * 2) :=
            (Real.rpow_mul_natCast (Nat.cast_nonneg n) (-(19 : ℝ) / 20) 2).symm
      _ = (n : ℝ) ^ (-(19 : ℝ) / 10) := by congr 1 <;> ring
  have hτLeBsq : τ ≤ bS n ^ 2 := by
    calc
      τ ≤ (n : ℝ) ^ (-(2 : ℝ)) := hτExp
      _ ≤ (n : ℝ) ^ (-(19 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
      _ = bS n ^ 2 := hBsq.symm
  let pairMass (sgn : ℝ) : ℝ :=
    ∑ x : Fin N, ∑ z : Fin N, σ x * σ z *
      (if threshold < sgn * inter E G π J
          (Function.update (Function.update base j x) j' z) then 1 else 0)
  let badMass : ℝ :=
    ∑ x : Fin N, ∑ z : Fin N, σ x * σ z *
      (if threshold < |inter E G π J
          (Function.update (Function.update base j x) j' z)| then 1 else 0)
  have hbadSplit : badMass ≤ pairMass 1 + pairMass (-1) := by
    dsimp [badMass, pairMass]
    simp only [one_mul, neg_one_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x hx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z hz
    have hweight : 0 ≤ σ x * σ z := mul_nonneg (hO.sigma_nonneg x) (hO.sigma_nonneg z)
    have hcoeff :
        (if threshold < |inter E G π J (Function.update (Function.update base j x) j' z)|
          then (1 : ℝ) else 0) ≤
        (if threshold < inter E G π J (Function.update (Function.update base j x) j' z)
          then (1 : ℝ) else 0) +
        (if threshold < -inter E G π J (Function.update (Function.update base j x) j' z)
          then (1 : ℝ) else 0) := by
      by_cases hp : threshold < inter E G π J (Function.update (Function.update base j x) j' z)
      · have hbad :
            (if threshold < |inter E G π J (Function.update (Function.update base j x) j' z)|
              then (1 : ℝ) else 0) ≤ 1 := by
            split_ifs <;> norm_num
        have hpos : (if threshold < inter E G π J
            (Function.update (Function.update base j x) j' z) then (1 : ℝ) else 0) = 1 := by
          simp [hp]
        have hneg : 0 ≤ (if threshold < -inter E G π J
            (Function.update (Function.update base j x) j' z) then (1 : ℝ) else 0) := by
          split_ifs <;> positivity
        calc
          (if threshold < |inter E G π J
              (Function.update (Function.update base j x) j' z)| then (1 : ℝ) else 0) ≤ 1 := hbad
          _ ≤ (if threshold < inter E G π J
              (Function.update (Function.update base j x) j' z) then (1 : ℝ) else 0) +
            (if threshold < -inter E G π J
              (Function.update (Function.update base j x) j' z) then (1 : ℝ) else 0) := by
                rw [hpos]
                exact le_add_of_nonneg_right hneg
      · by_cases hm : threshold < -inter E G π J (Function.update (Function.update base j x) j' z)
        · simp [hp, hm]
          split_ifs <;> norm_num
        · have habs : |inter E G π J (Function.update (Function.update base j x) j' z)| ≤ threshold := by
            apply abs_le.mpr
            constructor <;> linarith
          simp only [if_neg (not_lt_of_ge habs)]
          have hpos : 0 ≤ (if threshold < inter E G π J
              (Function.update (Function.update base j x) j' z) then (1 : ℝ) else 0) := by
            split_ifs <;> positivity
          have hneg : 0 ≤ (if threshold < -inter E G π J
              (Function.update (Function.update base j x) j' z) then (1 : ℝ) else 0) := by
            split_ifs <;> positivity
          linarith
    calc
      σ x * σ z *
          (if threshold < |inter E G π J (Function.update (Function.update base j x) j' z)|
            then 1 else 0) ≤
          σ x * σ z *
            ((if threshold < inter E G π J (Function.update (Function.update base j x) j' z)
                then 1 else 0) +
              (if threshold < -inter E G π J (Function.update (Function.update base j x) j' z)
                then 1 else 0)) := mul_le_mul_of_nonneg_left hcoeff hweight
      _ = σ x * σ z *
            (if threshold < inter E G π J (Function.update (Function.update base j x) j' z)
              then 1 else 0) +
          σ x * σ z *
            (if threshold < -inter E G π J (Function.update (Function.update base j x) j' z)
              then 1 else 0) := by ring
  have hσS : (∑ x ∈ S, σ x) = 1 := by
    calc
      (∑ x ∈ S, σ x) = ∑ x, (if x ∈ S then σ x else 0) := by
        symm
        exact Finset.sum_ite_mem_eq S σ
      _ = ∑ x, σ x := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxS : x ∈ S
        · simp [hxS]
        · have hσ0 : σ x = 0 := by
            by_contra hne
            exact hxS (hO.sigma_supp x hne)
          simp [hxS, hσ0]
      _ = 1 := hO.sigma_sum
  have hσMass : ∀ T : Finset (Fin N), (∑ z ∈ T, σ z) ≤ 1 := by
    intro T
    calc
      (∑ z ∈ T, σ z) ≤ ∑ z, σ z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.subset_univ T
        · intro z hz hnot
          exact hO.sigma_nonneg z
      _ = 1 := hO.sigma_sum
  by_contra hgoal
  have hbadLarge : ε < badMass := by
    apply lt_of_not_ge
    simpa [TwoFree, badMass, threshold, ε] using hgoal
  have hside : ε / 2 < pairMass 1 ∨ ε / 2 < pairMass (-1) := by
    by_contra h
    have hp : pairMass 1 ≤ ε / 2 := le_of_not_gt (fun hp => h (Or.inl hp))
    have hm : pairMass (-1) ≤ ε / 2 := le_of_not_gt (fun hm => h (Or.inr hm))
    linarith [hbadSplit]
  let sgn : ℝ := if pairMass 1 > ε / 2 then 1 else -1
  have hsgn : |sgn| = 1 := by
    dsimp [sgn]
    split_ifs <;> norm_num
  have hchosen : ε / 2 < pairMass sgn := by
    rcases hside with hpos | hneg
    · have htest : ε / 2 < pairMass 1 := hpos
      simp [sgn, htest]
    · by_cases htest : ε / 2 < pairMass 1
      · simp [sgn, htest]
      · simp [sgn, htest]
        exact hneg
  let event (x z : Fin N) : Prop :=
    threshold < sgn * inter E G π J
      (Function.update (Function.update base j x) j' z)
  let fiber (x : Fin N) : Finset (Fin N) := Finset.univ.filter (event x)
  let fiberMass (x : Fin N) : ℝ :=
    ∑ z, σ z * (if z ∈ fiber x then (1 : ℝ) else 0)
  let A : Finset (Fin N) := Finset.univ.filter (fun x => ρ < fiberMass x)
  have hindicator (T : Finset (Fin N)) :
      (∑ z, σ z * (if z ∈ T then (1 : ℝ) else 0)) = ∑ z ∈ T, σ z := by
    calc
      (∑ z, σ z * (if z ∈ T then (1 : ℝ) else 0)) =
          ∑ z, (if z ∈ T then σ z else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases h : z ∈ T <;> simp [h] <;> ring
      _ = ∑ z ∈ T, σ z := Finset.sum_ite_mem_eq T σ
  have hFiberMassNonneg (x : Fin N) : 0 ≤ fiberMass x := by
    dsimp [fiberMass]
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg (hO.sigma_nonneg z) (by split_ifs <;> positivity)
  have hFiberMassLeOne (x : Fin N) : fiberMass x ≤ 1 := by
    dsimp [fiberMass]
    rw [hindicator]
    exact hσMass (fiber x)
  have hpairMassFiber : pairMass sgn = ∑ x, σ x * fiberMass x := by
    dsimp [pairMass, fiberMass]
    calc
      (∑ x, ∑ z, σ x * σ z *
          (if threshold < sgn * inter E G π J
            (Function.update (Function.update base j x) j' z) then 1 else 0)) =
        ∑ x, σ x * ∑ z, σ z *
          (if threshold < sgn * inter E G π J
            (Function.update (Function.update base j x) j' z) then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro x hx
              calc
                (∑ z, σ x * σ z *
                    (if threshold < sgn * inter E G π J
                      (Function.update (Function.update base j x) j' z) then 1 else 0)) =
                  ∑ z, σ x * (σ z *
                    (if threshold < sgn * inter E G π J
                      (Function.update (Function.update base j x) j' z) then 1 else 0)) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    ring
                _ = σ x * ∑ z, σ z *
                    (if threshold < sgn * inter E G π J
                      (Function.update (Function.update base j x) j' z) then 1 else 0) := by
                    rw [Finset.mul_sum]
      _ = ∑ x, σ x * ∑ z, σ z *
          (if z ∈ fiber x then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply congrArg (fun q : ℝ => σ x * q)
        apply Finset.sum_congr rfl
        intro z hz
        simp [fiber, event]
      _ = ∑ x, σ x * fiberMass x := by rfl
  have hpairMassUpper : pairMass sgn ≤ (∑ x ∈ A, σ x) + ρ := by
    rw [hpairMassFiber]
    calc
      (∑ x, σ x * fiberMass x) ≤
          ∑ x, ((if x ∈ A then σ x else 0) + ρ * σ x) := by
            apply Finset.sum_le_sum
            intro x hx
            by_cases hxA : x ∈ A
            · have hfm : fiberMass x ≤ 1 := hFiberMassLeOne x
              have hσ : 0 ≤ σ x := hO.sigma_nonneg x
              have hmul : σ x * fiberMass x ≤ σ x * 1 :=
                mul_le_mul_of_nonneg_left hfm hσ
              simp [A, hxA]
              nlinarith [hmul, mul_nonneg hσ hρpos.le]
            · have hfm : fiberMass x ≤ ρ := by
                have hnot : ¬ ρ < fiberMass x := by
                  intro hlt
                  exact hxA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
                exact le_of_not_gt hnot
              have hσ : 0 ≤ σ x := hO.sigma_nonneg x
              have hmul : σ x * fiberMass x ≤ σ x * ρ :=
                mul_le_mul_of_nonneg_left hfm hσ
              simp [A, hxA]
              nlinarith [hmul]
      _ = (∑ x ∈ A, σ x) + ρ := by
            rw [Finset.sum_add_distrib]
            have hfirst : (∑ x, if x ∈ A then σ x else 0) = ∑ x ∈ A, σ x :=
              Finset.sum_ite_mem_eq A σ
            rw [hfirst, ← Finset.mul_sum, hO.sigma_sum]
            ring
  have hAmass : ρ < ∑ x ∈ A, σ x := by
    have hρeq : ε / 2 = 2 * ρ := by dsimp [ρ]; ring
    linarith [hchosen, hpairMassUpper, hρeq]
  have hApos : 0 < ∑ x ∈ A, σ x := lt_trans hρpos hAmass
  have hApositive (x : Fin N) (hx : x ∈ A) : ρ < fiberMass x :=
    (Finset.mem_filter.mp hx).2
  have hFiberMassAsSum (x : Fin N) : fiberMass x = ∑ z ∈ fiber x, σ z := by
    dsimp [fiberMass]
    exact hindicator (fiber x)
  have hFiberSetMassPos (x : Fin N) (hx : x ∈ A) :
      0 < ∑ z ∈ fiber x, σ z := by
    rw [← hFiberMassAsSum x]
    exact lt_trans hρpos (hApositive x hx)
  let q (x : Fin N) (hx : x ∈ A) : Law N :=
    Law.restrict σlaw (fiber x) (hFiberSetMassPos x hx)
  have hqSupport (x : Fin N) (hx : x ∈ A) : (q x hx).SupportedIn (fiber x) := by
    intro z hz
    simp [q, Law.restrict, hz]
  have hqWidth (x : Fin N) (hx : x ∈ A) :
      (q x hx).WidthLE (tσ n - Real.log (∑ z ∈ fiber x, σ z)) := by
    simpa [q] using Law.WidthLE.restrict hσWidth (hFiberSetMassPos x hx)
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hnPowFiber : 1 ≤ (n : ℝ) ^ ((2 : ℝ) / 5) := by
    exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  have hqWidthPlusLog3 (x : Fin N) (hx : x ∈ A) :
      tσ n - Real.log (∑ z ∈ fiber x, σ z) + Real.log 3 ≤ (n : ℝ) ^ a := by
    have hmasslog : -((n : ℝ) ^ ((2 : ℝ) / 5)) - Real.log 4 <
        Real.log (∑ z ∈ fiber x, σ z) := by
      have hmass : ρ < ∑ z ∈ fiber x, σ z := by
        rw [← hFiberMassAsSum x]
        exact hApositive x hx
      have h := Real.log_lt_log hρpos hmass
      have hρlog : Real.log ρ = -((n : ℝ) ^ ((2 : ℝ) / 5)) - Real.log 4 := by
        dsimp [ρ, ε]
        rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num : (4 : ℝ) ≠ 0)]
        rw [Real.log_exp]
      rw [hρlog] at h
      exact h
    have hpenalty : (n : ℝ) ^ ((2 : ℝ) / 5) + Real.log 4 ≤ (n : ℝ) ^ a / 2 := by
      nlinarith [hfiberGap, hnPowFiber]
    have htσ : tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 := hwidthN
    linarith
  have hqWidthForDisc (x : Fin N) (hx : x ∈ A) :
      (q x hx).WidthLE ((n : ℝ) ^ a - Real.log 3) := by
    exact Law.WidthLE.mono (hqWidth x hx) (by linarith [hqWidthPlusLog3 x hx])
  have hqSupportedInS (x : Fin N) (hx : x ∈ A) : (q x hx).SupportedIn S := by
    intro z hzS
    have hσzero : σ z = 0 := by
      by_contra hσne
      exact hzS (hO.sigma_supp z hσne)
    simp [q, Law.restrict, σlaw, hσzero]
  let r (z : Fin N) : ℝ := if z ∈ S then (1 + sMean E G π z)⁻¹ else 0
  have hrBounds (z : Fin N) (hz : z ∈ S) : 2 / 3 ≤ r z ∧ r z ≤ 2 := by
    have hdenpos : 0 < 1 + sMean E G π z :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hDenBounds z hz).1
    have hr : r z = (1 + sMean E G π z)⁻¹ := by simp [r, hz]
    rw [hr, inv_eq_one_div]
    constructor
    · apply (le_div_iff₀ hdenpos).2
      linarith [(hDenBounds z hz).2]
    · apply (div_le_iff₀ hdenpos).2
      linarith [(hDenBounds z hz).1]
  have hrNonneg (z : Fin N) : 0 ≤ r z := by
    by_cases hz : z ∈ S
    · linarith [(hrBounds z hz).1]
    · simp [r, hz]
  let c (x : Fin N) (hx : x ∈ A) : ℝ := ∑ z, (q x hx).w z * r z
  have hcLower (x : Fin N) (hx : x ∈ A) : 2 / 3 ≤ c x hx := by
    dsimp [c]
    calc
      (2 / 3 : ℝ) = (∑ z, (q x hx).w z) * (2 / 3) := by rw [(q x hx).sum_eq_one]; ring
      _ = ∑ z, (q x hx).w z * (2 / 3) := by rw [Finset.sum_mul]
      _ ≤ ∑ z, (q x hx).w z * r z := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzS : z ∈ S
        · exact mul_le_mul_of_nonneg_left (hrBounds z hzS).1 ((q x hx).nonneg z)
        · have hq0 : (q x hx).w z = 0 := hqSupportedInS x hx z hzS
          simp [hq0]
  have hcUpper (x : Fin N) (hx : x ∈ A) : c x hx ≤ 2 := by
    dsimp [c]
    calc
      (∑ z, (q x hx).w z * r z) ≤ ∑ z, (q x hx).w z * 2 := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzS : z ∈ S
        · exact mul_le_mul_of_nonneg_left (hrBounds z hzS).2 ((q x hx).nonneg z)
        · have hq0 : (q x hx).w z = 0 := hqSupportedInS x hx z hzS
          simp [hq0]
      _ = 2 := by rw [← Finset.sum_mul, (q x hx).sum_eq_one]; ring
  have hcPos (x : Fin N) (hx : x ∈ A) : 0 < c x hx :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) (hcLower x hx)
  let qtilde (x : Fin N) (hx : x ∈ A) : Law N := {
    w := fun z => (q x hx).w z * r z / c x hx
    nonneg := fun z => div_nonneg (mul_nonneg ((q x hx).nonneg z) (hrNonneg z))
      (hcPos x hx).le
    sum_eq_one := by
      calc
        (∑ z, (q x hx).w z * r z / c x hx) =
            (∑ z, (q x hx).w z * r z) / c x hx := by rw [Finset.sum_div]
        _ = c x hx / c x hx := rfl
        _ = 1 := div_self (hcPos x hx).ne'
  }
  have hqtildeSupport (x : Fin N) (hx : x ∈ A) : (qtilde x hx).SupportedIn S := by
    intro z hzS
    have hq0 : (q x hx).w z = 0 := hqSupportedInS x hx z hzS
    simp [qtilde, hq0]
  have hqtildeWidth (x : Fin N) (hx : x ∈ A) :
      (qtilde x hx).WidthLE ((n : ℝ) ^ a) := by
    intro z
    change (q x hx).w z * r z / c x hx ≤ Real.exp ((n : ℝ) ^ a) / N
    have hratio : r z / c x hx ≤ 3 := by
      by_cases hzS : z ∈ S
      · apply (div_le_iff₀ (hcPos x hx)).2
        calc
          r z ≤ 2 := (hrBounds z hzS).2
          _ = 3 * (2 / 3 : ℝ) := by norm_num
          _ ≤ 3 * c x hx := mul_le_mul_of_nonneg_left (hcLower x hx) (by norm_num)
      · simp [r, hzS]
    calc
      (q x hx).w z * r z / c x hx = (q x hx).w z * (r z / c x hx) := by ring
      _ ≤ (q x hx).w z * 3 :=
        mul_le_mul_of_nonneg_left hratio ((q x hx).nonneg z)
      _ ≤ (Real.exp ((n : ℝ) ^ a - Real.log 3) / N) * 3 :=
        mul_le_mul_of_nonneg_right (hqWidthForDisc x hx z) (by norm_num)
      _ = Real.exp ((n : ℝ) ^ a) / N := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        field_simp [ne_of_gt hNpos]
        <;> ring
  have hqtildeWeight (x : Fin N) (hx : x ∈ A) (z : Fin N) :
      c x hx * (qtilde x hx).w z = (q x hx).w z * r z := by
    change c x hx * ((q x hx).w z * r z / c x hx) = _
    field_simp [ne_of_gt (hcPos x hx)]
  let dir (x : Fin N) (hx : x ∈ A) (y : Fin N) : ℝ :=
    ∑ z, (q x hx).w z * aF E G π z y
  let dirF (x : Fin N) (hx : x ∈ A) (y : Fin N) : ℝ :=
    ∑ z, (qtilde x hx).w z * fv E G z y
  let dirMean (x : Fin N) (hx : x ∈ A) : ℝ :=
    ∑ z, (qtilde x hx).w z * sMean E G π z
  have hdirTerm (x : Fin N) (hx : x ∈ A) (y z : Fin N) :
      (q x hx).w z * aF E G π z y =
        c x hx * ((qtilde x hx).w z * (fv E G z y - sMean E G π z)) := by
    by_cases hzS : z ∈ S
    · have hrf : r z = (1 + sMean E G π z)⁻¹ := by simp [r, hzS]
      calc
        (q x hx).w z * aF E G π z y =
            ((q x hx).w z * r z) * (fv E G z y - sMean E G π z) := by
              rw [haFid z hzS y, div_eq_mul_inv, ← hrf]
              ring
        _ = c x hx * ((qtilde x hx).w z * (fv E G z y - sMean E G π z)) := by
              rw [← hqtildeWeight x hx z]
              ring
    · have hq0 : (q x hx).w z = 0 := hqSupportedInS x hx z hzS
      have hqt0 : (qtilde x hx).w z = 0 := hqtildeSupport x hx z hzS
      simp [hq0, hqt0]
  have hdirIdentity (x : Fin N) (hx : x ∈ A) (y : Fin N) :
      dir x hx y = c x hx * (dirF x hx y - dirMean x hx) := by
    dsimp [dir, dirF, dirMean]
    calc
      (∑ z, (q x hx).w z * aF E G π z y) =
          ∑ z, c x hx * ((qtilde x hx).w z *
            (fv E G z y - sMean E G π z)) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hdirTerm x hx y z
      _ = c x hx *
          ((∑ z, (qtilde x hx).w z * fv E G z y) -
            ∑ z, (qtilde x hx).w z * sMean E G π z) := by
              calc
                (∑ z, c x hx * ((qtilde x hx).w z *
                    (fv E G z y - sMean E G π z))) =
                  c x hx * ∑ z, (qtilde x hx).w z *
                    (fv E G z y - sMean E G π z) := by rw [← Finset.mul_sum]
                _ = c x hx *
                    ((∑ z, (qtilde x hx).w z * fv E G z y) -
                      ∑ z, (qtilde x hx).w z * sMean E G π z) := by
                    congr 1
                    calc
                      (∑ z, (qtilde x hx).w z * (fv E G z y - sMean E G π z)) =
                          ∑ z, ((qtilde x hx).w z * fv E G z y -
                            (qtilde x hx).w z * sMean E G π z) := by
                              apply Finset.sum_congr rfl
                              intro z hz
                              ring
                      _ = _ := by rw [Finset.sum_sub_distrib]
      _ = c x hx * (dirF x hx y - dirMean x hx) := by rfl
  have hdirFExpectation (x : Fin N) (hx : x ∈ A) (ν : Law N) :
      (∑ y, ν.w y * dirF x hx y) = 2 * dens E G (qtilde x hx) ν - 1 := by
    classical
    unfold dirF dens
    calc
      (∑ y, ν.w y * ∑ z, (qtilde x hx).w z * fv E G z y) =
          ∑ z, ∑ y, (qtilde x hx).w z * ν.w y * fv E G z y := by
            calc
              (∑ y, ν.w y * ∑ z, (qtilde x hx).w z * fv E G z y) =
                  ∑ y, ∑ z, ν.w y * ((qtilde x hx).w z * fv E G z y) := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    rw [Finset.mul_sum]
              _ = ∑ z, ∑ y, (qtilde x hx).w z * ν.w y * fv E G z y := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro z hz
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
      _ = 2 * (∑ z, ∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) - 1 := by
            have hByZ (z : Fin N) :
                (∑ y, (qtilde x hx).w z * ν.w y * fv E G z y) =
                  2 * (∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) -
                    (qtilde x hx).w z := by
              calc
                (∑ y, (qtilde x hx).w z * ν.w y * fv E G z y) =
                    ∑ y, (2 * ((qtilde x hx).w z * ν.w y * hit E G z y) -
                      (qtilde x hx).w z * ν.w y) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        unfold fv
                        ring
                _ = (∑ y, 2 * ((qtilde x hx).w z * ν.w y * hit E G z y)) -
                    ∑ y, (qtilde x hx).w z * ν.w y := by
                      rw [Finset.sum_sub_distrib]
                _ = 2 * (∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) -
                    (qtilde x hx).w z * ∑ y, ν.w y := by
                      rw [← Finset.mul_sum, ← Finset.mul_sum]
                _ = 2 * (∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) -
                    (qtilde x hx).w z := by rw [ν.sum_eq_one]; ring
            calc
              (∑ z, ∑ y, (qtilde x hx).w z * ν.w y * fv E G z y) =
                  ∑ z, (2 * (∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) -
                    (qtilde x hx).w z) := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      exact hByZ z
              _ = 2 * (∑ z, ∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) -
                    ∑ z, (qtilde x hx).w z := by
                      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              _ = 2 * (∑ z, ∑ y, (qtilde x hx).w z * ν.w y * hit E G z y) - 1 := by
                    rw [(qtilde x hx).sum_eq_one]
      _ = 2 * dens E G (qtilde x hx) ν - 1 := by rfl
  have hdirMeanEq (x : Fin N) (hx : x ∈ A) :
      dirMean x hx = ∑ y, π y * dirF x hx y := by
    dsimp [dirMean, dirF]
    calc
      (∑ z, (qtilde x hx).w z * sMean E G π z) =
          ∑ z, (qtilde x hx).w z * ∑ y, π y * fv E G z y := by
            apply Finset.sum_congr rfl
            intro z hz
            rfl
      _ = ∑ z, ∑ y, (qtilde x hx).w z * (π y * fv E G z y) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.mul_sum]
      _ = ∑ y, ∑ z, (qtilde x hx).w z * (π y * fv E G z y) := by
            exact Finset.sum_comm
      _ = ∑ y, π y * ∑ z, (qtilde x hx).w z * fv E G z y := by
            apply Finset.sum_congr rfl
            intro y hy
            calc
              (∑ z, (qtilde x hx).w z * (π y * fv E G z y)) =
                  ∑ z, π y * ((qtilde x hx).w z * fv E G z y) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    ring
              _ = π y * ∑ z, (qtilde x hx).w z * fv E G z y := by
                    rw [Finset.mul_sum]
      _ = ∑ y, π y * dirF x hx y := by rfl
  have hdirAverageIdentity (x : Fin N) (hx : x ∈ A) (ν : Law N) :
      (∑ y, ν.w y * dir x hx y) =
        2 * c x hx * (dens E G (qtilde x hx) ν - dens E G (qtilde x hx) πlaw) := by
    have hcenter (ν' : Law N) :
        (∑ y, ν'.w y * (dirF x hx y - dirMean x hx)) =
          (∑ y, ν'.w y * dirF x hx y) - dirMean x hx := by
      calc
        (∑ y, ν'.w y * (dirF x hx y - dirMean x hx)) =
            ∑ y, (ν'.w y * dirF x hx y - ν'.w y * dirMean x hx) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = (∑ y, ν'.w y * dirF x hx y) -
            ∑ y, ν'.w y * dirMean x hx := by rw [Finset.sum_sub_distrib]
        _ = (∑ y, ν'.w y * dirF x hx y) - dirMean x hx := by
              have hconst : (∑ y, ν'.w y * dirMean x hx) = dirMean x hx := by
                calc
                  (∑ y, ν'.w y * dirMean x hx) =
                      (∑ y, ν'.w y) * dirMean x hx := by rw [← Finset.sum_mul]
                  _ = dirMean x hx := by rw [ν'.sum_eq_one]; ring
              rw [hconst]
    have hfactor :
        (∑ y, ν.w y * dir x hx y) =
          c x hx * (∑ y, ν.w y * (dirF x hx y - dirMean x hx)) := by
      calc
        (∑ y, ν.w y * dir x hx y) =
            ∑ y, ν.w y * (c x hx * (dirF x hx y - dirMean x hx)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [hdirIdentity x hx y]
        _ = ∑ y, c x hx * (ν.w y * (dirF x hx y - dirMean x hx)) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = c x hx * ∑ y, ν.w y * (dirF x hx y - dirMean x hx) := by
              rw [Finset.mul_sum]
    calc
      (∑ y, ν.w y * dir x hx y) =
          c x hx * ((∑ y, ν.w y * dirF x hx y) - dirMean x hx) := by
            rw [hfactor, hcenter]
      _ = 2 * c x hx *
          (dens E G (qtilde x hx) ν - dens E G (qtilde x hx) πlaw) := by
            rw [hdirFExpectation x hx ν, hdirMeanEq x hx,
              hdirFExpectation x hx πlaw]
            ring
  have hqtildeSupportX (x : Fin N) (hx : x ∈ A) : (qtilde x hx).SupportedIn X := by
    intro z hzX
    have hzS : z ∉ S := by
      intro hz
      exact hzX (hO.S_sub hz)
    exact hqtildeSupport x hx z hzS
  let posDir (x : Fin N) (hx : x ∈ A) : Finset (Fin N) :=
    Finset.univ.filter (fun y => 16 * bS n < dir x hx y)
  let negDir (x : Fin N) (hx : x ∈ A) : Finset (Fin N) :=
    Finset.univ.filter (fun y => 16 * bS n < -dir x hx y)
  have hbpos : 0 < bS n := by
    unfold bS
    exact Real.rpow_pos_of_pos hnreal _
  have hNoSide (x : Fin N) (hx : x ∈ A) (Bset : Finset (Fin N))
      (sgn : ℝ) (hsign : |sgn| = 1)
      (hEvent : ∀ y ∈ Bset, 16 * bS n < sgn * dir x hx y) :
      (∑ y ∈ Bset, π y) ≤ τ := by
    by_contra hmassNot
    have hmass : τ < ∑ y ∈ Bset, π y := lt_of_not_ge hmassNot
    have hmassPos : 0 < ∑ y ∈ Bset, π y := lt_trans hτpos hmass
    let ν : Law N := Law.restrict πlaw Bset hmassPos
    have hνSupportB : ν.SupportedIn Bset := by
      intro y hy
      simp [ν, Law.restrict, hy]
    have hνSupportY : ν.SupportedIn Y := by
      intro y hy
      have hπzero : πlaw.w y = 0 := hπSupport y hy
      simp [ν, Law.restrict, hπzero]
    have hmassLog : -((n : ℝ) ^ x₀ / 4) < Real.log (∑ y ∈ Bset, π y) := by
      have hlog := Real.log_lt_log hτpos hmass
      simpa [τ, Real.log_exp] using hlog
    have hνWidth0 : ν.WidthLE (Real.log K - Real.log (∑ y ∈ Bset, π y)) := by
      simpa [ν] using Law.WidthLE.restrict hπWidth hmassPos
    have hνWidth : ν.WidthLE ((n : ℝ) ^ x₀) := by
      have hneglog : -Real.log (∑ y ∈ Bset, π y) < (n : ℝ) ^ x₀ / 4 := by
        linarith [hmassLog]
      have hpowNonneg : 0 ≤ (n : ℝ) ^ x₀ := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hExponent : Real.log K - Real.log (∑ y ∈ Bset, π y) ≤ (n : ℝ) ^ x₀ := by
        calc
          Real.log K - Real.log (∑ y ∈ Bset, π y) ≤
              Real.log K + (n : ℝ) ^ x₀ / 4 := by linarith [hneglog]
          _ ≤ (n : ℝ) ^ x₀ / 2 + (n : ℝ) ^ x₀ / 4 :=
                add_le_add hKHalfN le_rfl
          _ = (3 / 4 : ℝ) * (n : ℝ) ^ x₀ := by ring
          _ ≤ (1 : ℝ) * (n : ℝ) ^ x₀ :=
                mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ 1) hpowNonneg
          _ = (n : ℝ) ^ x₀ := by ring
      intro y
      change ν.w y ≤ Real.exp ((n : ℝ) ^ x₀) / N
      calc
        ν.w y ≤ Real.exp (Real.log K - Real.log (∑ y ∈ Bset, π y)) / N := hνWidth0 y
        _ ≤ Real.exp ((n : ℝ) ^ x₀) / N := by
              exact div_le_div_of_nonneg_right
                (Real.exp_le_exp.mpr hExponent) (by positivity)
    have hDiscν : |dens E G (qtilde x hx) ν - 1 / 2| ≤ bS n := by
      have hd := hO.disc (qtilde x hx) ν (hqtildeSupportX x hx) hνSupportY
        (hqtildeWidth x hx) hνWidth G
      simpa [bS, neg_div] using hd
    have hDiscπ : |dens E G (qtilde x hx) πlaw - 1 / 2| ≤ bS n := by
      have hpowNonneg : 0 ≤ (n : ℝ) ^ x₀ := Real.rpow_nonneg (Nat.cast_nonneg n) _
      have hπWidth' : πlaw.WidthLE ((n : ℝ) ^ x₀) := by
        apply Law.WidthLE.mono hπWidth
        exact hKHalfN.trans (div_le_self hpowNonneg (by norm_num))
      have hd := hO.disc (qtilde x hx) πlaw (hqtildeSupportX x hx) hπSupport
        (hqtildeWidth x hx) hπWidth' G
      simpa [bS, neg_div] using hd
    have hDensityDiff :
        |dens E G (qtilde x hx) ν - dens E G (qtilde x hx) πlaw| ≤ 2 * bS n := by
      calc
        |dens E G (qtilde x hx) ν - dens E G (qtilde x hx) πlaw| ≤
            |dens E G (qtilde x hx) ν - 1 / 2| +
              |dens E G (qtilde x hx) πlaw - 1 / 2| := by
                calc
                  _ = |(dens E G (qtilde x hx) ν - 1 / 2) -
                        (dens E G (qtilde x hx) πlaw - 1 / 2)| := by congr 1 <;> ring
                  _ ≤ _ := abs_sub _ _
        _ ≤ bS n + bS n := add_le_add hDiscν hDiscπ
        _ = 2 * bS n := by ring
    have hDirMeanAbs : |∑ y, ν.w y * dir x hx y| ≤ 8 * bS n := by
      have h2c : 0 ≤ 2 * c x hx := mul_nonneg (by norm_num) (hcPos x hx).le
      rw [hdirAverageIdentity x hx ν, abs_mul, abs_of_nonneg h2c]
      calc
        2 * c x hx * |dens E G (qtilde x hx) ν - dens E G (qtilde x hx) πlaw| ≤
            2 * c x hx * (2 * bS n) :=
              mul_le_mul_of_nonneg_left hDensityDiff h2c
        _ ≤ 8 * bS n := by
              have h2cUpper : 2 * c x hx ≤ 4 :=
                calc
                  2 * c x hx ≤ 2 * 2 :=
                    mul_le_mul_of_nonneg_left (hcUpper x hx) (by norm_num : (0 : ℝ) ≤ 2)
                  _ = 4 := by norm_num
              have h2bpos : 0 ≤ 2 * bS n := mul_nonneg (by norm_num) hbpos.le
              calc
                2 * c x hx * (2 * bS n) ≤ 4 * (2 * bS n) :=
                  mul_le_mul_of_nonneg_right h2cUpper h2bpos
                _ = 8 * bS n := by ring
    have hDirLower : 16 * bS n ≤ sgn * (∑ y, ν.w y * dir x hx y) := by
      calc
        16 * bS n = (∑ y, ν.w y) * (16 * bS n) := by rw [ν.sum_eq_one]; ring
        _ = ∑ y, ν.w y * (16 * bS n) := by rw [Finset.sum_mul]
        _ ≤ ∑ y, ν.w y * (sgn * dir x hx y) := by
          apply Finset.sum_le_sum
          intro y hy
          by_cases hyB : y ∈ Bset
          · exact mul_le_mul_of_nonneg_left (le_of_lt (hEvent y hyB)) (ν.nonneg y)
          · have hνzero : ν.w y = 0 := hνSupportB y hyB
            simp [hνzero]
        _ = sgn * (∑ y, ν.w y * dir x hx y) := by
          calc
            (∑ y, ν.w y * (sgn * dir x hx y)) =
                ∑ y, sgn * (ν.w y * dir x hx y) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  ring
            _ = _ := by rw [Finset.mul_sum]
    have hSignedAbs : sgn * (∑ y, ν.w y * dir x hx y) ≤
        |∑ y, ν.w y * dir x hx y| := by
      calc
        sgn * (∑ y, ν.w y * dir x hx y) ≤
            |sgn * (∑ y, ν.w y * dir x hx y)| := le_abs_self _
        _ = |∑ y, ν.w y * dir x hx y| := by rw [abs_mul, hsign, one_mul]
    have hbad : 16 * bS n ≤ 8 * bS n := hDirLower.trans (hSignedAbs.trans hDirMeanAbs)
    nlinarith only [hbad, hbpos]
  have hposMassSmall (x : Fin N) (hx : x ∈ A) :
      (∑ y ∈ posDir x hx, π y) ≤ τ := by
    apply hNoSide x hx (posDir x hx) 1 (by norm_num)
    intro y hy
    calc
      16 * bS n < dir x hx y := (Finset.mem_filter.mp hy).2
      _ = 1 * dir x hx y := by ring
  have hnegMassSmall (x : Fin N) (hx : x ∈ A) :
      (∑ y ∈ negDir x hx, π y) ≤ τ := by
    apply hNoSide x hx (negDir x hx) (-1) (by norm_num)
    intro y hy
    calc
      16 * bS n < -dir x hx y := (Finset.mem_filter.mp hy).2
      _ = (-1) * dir x hx y := by ring
  have hπIndicator (T : Finset (Fin N)) :
      (∑ y, π y * (if y ∈ T then (1 : ℝ) else 0)) = ∑ y ∈ T, π y := by
    calc
      (∑ y, π y * (if y ∈ T then (1 : ℝ) else 0)) =
          ∑ y, (if y ∈ T then π y else 0) := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases h : y ∈ T <;> simp [h] <;> ring
      _ = ∑ y ∈ T, π y := Finset.sum_ite_mem_eq T π
  have hdirAbsBound (x : Fin N) (hx : x ∈ A) (y : Fin N) :
      |dir x hx y| ≤ 5 := by
    dsimp [dir]
    calc
      |∑ z, (q x hx).w z * aF E G π z y| ≤
          ∑ z, |(q x hx).w z * aF E G π z y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ z, (q x hx).w z * |aF E G π z y| := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [abs_mul, abs_of_nonneg ((q x hx).nonneg z)]
      _ ≤ ∑ z, (q x hx).w z * 5 := by
            apply Finset.sum_le_sum
            intro z hz
            by_cases hzS : z ∈ S
            · exact mul_le_mul_of_nonneg_left (haBound z hzS y) ((q x hx).nonneg z)
            · have hqzero : (q x hx).w z = 0 := hqSupportedInS x hx z hzS
              simp [hqzero]
      _ = 5 := by rw [← Finset.sum_mul, (q x hx).sum_eq_one]; ring
  have hdirPoint (x : Fin N) (hx : x ∈ A) (y : Fin N) :
      (dir x hx y) ^ 2 ≤ (16 * bS n) ^ 2 +
        25 * (if y ∈ posDir x hx then (1 : ℝ) else 0) +
        25 * (if y ∈ negDir x hx then (1 : ℝ) else 0) := by
    by_cases hp : y ∈ posDir x hx
    · have hpos : 16 * bS n < dir x hx y := (Finset.mem_filter.mp hp).2
      have hsq : (dir x hx y) ^ 2 ≤ 25 := by
        have habs : |dir x hx y| ≤ |(5 : ℝ)| := by
          simpa using hdirAbsBound x hx y
        calc
          (dir x hx y) ^ 2 ≤ (5 : ℝ) ^ 2 := (sq_le_sq).2 habs
          _ = 25 := by norm_num
      have hsqNonneg : 0 ≤ (16 * bS n) ^ 2 := sq_nonneg _
      have hnegInd : 0 ≤ (if y ∈ negDir x hx then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      have hPosCase : (dir x hx y) ^ 2 ≤
          (16 * bS n) ^ 2 + 25 +
            25 * (if y ∈ negDir x hx then (1 : ℝ) else 0) := by
        calc
          (dir x hx y) ^ 2 ≤ 25 := hsq
          _ ≤ 25 + ((16 * bS n) ^ 2 +
              25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) :=
                le_add_of_nonneg_right
                  (add_nonneg hsqNonneg (mul_nonneg (by norm_num) hnegInd))
          _ = (16 * bS n) ^ 2 + 25 +
              25 * (if y ∈ negDir x hx then (1 : ℝ) else 0) := by ring
      simpa [hp, mul_one] using hPosCase
    · by_cases hn : y ∈ negDir x hx
      · have hneg : 16 * bS n < -dir x hx y := (Finset.mem_filter.mp hn).2
        have hsq : (dir x hx y) ^ 2 ≤ 25 := by
          have habs : |dir x hx y| ≤ |(5 : ℝ)| := by
            simpa using hdirAbsBound x hx y
          calc
            (dir x hx y) ^ 2 ≤ (5 : ℝ) ^ 2 := (sq_le_sq).2 habs
            _ = 25 := by norm_num
        have hsqNonneg : 0 ≤ (16 * bS n) ^ 2 := sq_nonneg _
        have hNegCase : (dir x hx y) ^ 2 ≤ (16 * bS n) ^ 2 + 25 := by
          calc
            (dir x hx y) ^ 2 ≤ 25 := hsq
            _ ≤ (16 * bS n) ^ 2 + 25 := le_add_of_nonneg_left hsqNonneg
        simpa [hp, hn, mul_one] using hNegCase
      · have hupper : dir x hx y ≤ 16 * bS n := by
          exact le_of_not_gt (by intro h; exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
        have hlower : -(16 * bS n) ≤ dir x hx y := by
          have hnot : ¬ 16 * bS n < -dir x hx y := by
            intro h
            exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          linarith
        have hsq : (dir x hx y) ^ 2 ≤ (16 * bS n) ^ 2 := sq_le_sq' hlower hupper
        simpa [hp, hn, mul_one] using hsq
  have hdirL2 (x : Fin N) (hx : x ∈ A) :
      (∑ y, π y * (dir x hx y) ^ 2) ≤ 306 * (bS n) ^ 2 := by
    calc
      (∑ y, π y * (dir x hx y) ^ 2) ≤
          ∑ y, π y * ((16 * bS n) ^ 2 +
            25 * (if y ∈ posDir x hx then (1 : ℝ) else 0) +
            25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
              apply Finset.sum_le_sum
              intro y hy
              exact mul_le_mul_of_nonneg_left (hdirPoint x hx y) (hO.pi_nonneg y)
      _ = (16 * bS n) ^ 2 + 25 * (∑ y, π y * (if y ∈ posDir x hx then (1 : ℝ) else 0)) +
            25 * (∑ y, π y * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
              have hbase : (∑ y, π y * (16 * bS n) ^ 2) = (16 * bS n) ^ 2 := by
                rw [← Finset.sum_mul, hO.pi_sum]
                ring
              have hposTerm :
                  (∑ y, π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0))) =
                    25 * (∑ y, π y * (if y ∈ posDir x hx then (1 : ℝ) else 0)) := by
                calc
                  (∑ y, π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0))) =
                      ∑ y, 25 * (π y * (if y ∈ posDir x hx then (1 : ℝ) else 0)) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        ring
                  _ = _ := by rw [Finset.mul_sum]
              have hnegTerm :
                  (∑ y, π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0))) =
                    25 * (∑ y, π y * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
                calc
                  (∑ y, π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0))) =
                      ∑ y, 25 * (π y * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        ring
                  _ = _ := by rw [Finset.mul_sum]
              calc
                (∑ y, π y * ((16 * bS n) ^ 2 +
                    25 * (if y ∈ posDir x hx then (1 : ℝ) else 0) +
                    25 * (if y ∈ negDir x hx then (1 : ℝ) else 0))) =
                    ∑ y, (π y * (16 * bS n) ^ 2 +
                      π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0)) +
                      π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0))) := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        calc
                          π y * ((16 * bS n) ^ 2 +
                              25 * (if y ∈ posDir x hx then (1 : ℝ) else 0) +
                              25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) =
                              π y * ((16 * bS n) ^ 2 +
                                25 * (if y ∈ posDir x hx then (1 : ℝ) else 0)) +
                                π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
                                  rw [mul_add]
                          _ = π y * (16 * bS n) ^ 2 +
                                π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0)) +
                                π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
                                  rw [mul_add]
                _ = (∑ y, π y * (16 * bS n) ^ 2) +
                      (∑ y, π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0))) +
                      ∑ y, π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) := by
                        calc
                          (∑ y : Fin N, ((π y * (16 * bS n) ^ 2 +
                              π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0))) +
                              π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)))) =
                              (∑ y : Fin N, (π y * (16 * bS n) ^ 2 +
                                π y * (25 * (if y ∈ posDir x hx then (1 : ℝ) else 0)))) +
                                ∑ y : Fin N, π y * (25 * (if y ∈ negDir x hx then (1 : ℝ) else 0)) :=
                                  Finset.sum_add_distrib
                          _ = _ := by rw [Finset.sum_add_distrib]
                _ = _ := by rw [hbase, hposTerm, hnegTerm]
      _ ≤ 256 * (bS n) ^ 2 + 25 * τ + 25 * τ := by
            have hposIndicator :
                (∑ y, π y * (if y ∈ posDir x hx then (1 : ℝ) else 0)) =
                  ∑ y ∈ posDir x hx, π y := by
                exact hπIndicator (posDir x hx)
            have hnegIndicator :
                (∑ y, π y * (if y ∈ negDir x hx then (1 : ℝ) else 0)) =
                  ∑ y ∈ negDir x hx, π y := by
                exact hπIndicator (negDir x hx)
            rw [hposIndicator, hnegIndicator]
            have hpos := hposMassSmall x hx
            have hneg := hnegMassSmall x hx
            have hposTerm : 25 * (∑ y ∈ posDir x hx, π y) ≤ 25 * τ :=
              mul_le_mul_of_nonneg_left hpos (by norm_num)
            have hnegTerm : 25 * (∑ y ∈ negDir x hx, π y) ≤ 25 * τ :=
              mul_le_mul_of_nonneg_left hneg (by norm_num)
            have h16 : (16 * bS n) ^ 2 = 256 * (bS n) ^ 2 := by ring
            rw [h16]
            have htailSum :
                25 * (∑ y ∈ posDir x hx, π y) + 25 * (∑ y ∈ negDir x hx, π y) ≤
                  25 * τ + 25 * τ := add_le_add hposTerm hnegTerm
            calc
              256 * (bS n) ^ 2 + 25 * (∑ y ∈ posDir x hx, π y) +
                  25 * (∑ y ∈ negDir x hx, π y) =
                  256 * (bS n) ^ 2 +
                    (25 * (∑ y ∈ posDir x hx, π y) + 25 * (∑ y ∈ negDir x hx, π y)) := by ring
              _ ≤ 256 * (bS n) ^ 2 + (25 * τ + 25 * τ) :=
                    add_le_add (le_refl (256 * (bS n) ^ 2)) htailSum
              _ = 256 * (bS n) ^ 2 + 25 * τ + 25 * τ := by ring
      _ ≤ 306 * (bS n) ^ 2 := by
            calc
              256 * (bS n) ^ 2 + 25 * τ + 25 * τ =
                  256 * (bS n) ^ 2 + 50 * τ := by ring
              _ ≤ 256 * (bS n) ^ 2 + 50 * (bS n) ^ 2 := by
                    have h50 : 50 * τ ≤ 50 * (bS n) ^ 2 :=
                      mul_le_mul_of_nonneg_left hτLeBsq (by norm_num : (0 : ℝ) ≤ 50)
                    exact add_le_add (le_refl (256 * (bS n) ^ 2)) h50
              _ = 306 * (bS n) ^ 2 := by ring
  -- The conditioned fibers have mass above `ρ`; the remaining proof bounds their
  -- centered direction in L², samples a norm-good tuple, and applies the equal-normalizer signed test.
  sorry

/-- L11.3c (11:254–268).  `E M_J² = E_{y,y'∼π} (∫ a_x(y) a_x(y') dσ)^{|J|}`; the kernel is `O(b_*)` off a
`π`-set of mass `e^{-Ω(n^{x₀})}` by (11.1), so `E M_J² ≤ (C_u b_*)^{|J|} + C_u e^{-Ω(n^{x₀})}`; Cauchy–Schwarz
with `.95/2 > .4`.  Coinciding coordinates have probability `O_u(e^h/N)`. -/
theorem mean_inter (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : MeanInterEv δ x₀ K := by
  classical
  unfold MeanInterEv
  intro u
  let a : ℝ := 1 - δ / 16
  let tσ : ℕ → ℝ := fun n => (Real.log 2 - gS n / 2) * Fintype.card (InnerCoord n)
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hgap := OuterMoment_q_s11_outer.eventually_pow_gap
    ((1 : ℝ) / 10) a 8 (by dsimp [a]; nlinarith) (by norm_num)
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
  have hScale : ∀ᶠ n : ℕ in atTop, 64 ≤ n ∧ bS n ≤ 1 / 8 ∧
      tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 := by
    filter_upwards [hnLarge, hbSmall, hgap] with n hn hb hg
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hpow : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) :=
      Real.one_le_rpow hn1 (by norm_num)
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
              exact mul_le_mul_of_nonneg_right (by linarith)
                (by exact_mod_cast Nat.cast_nonneg (Fintype.card (InnerCoord n)))
        _ ≤ (hIn n : ℝ) := by simpa using hcard
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := hfloor
    have hlog3 : Real.log 3 ≤ 2 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hwidth : tσ n + Real.log 3 ≤ (n : ℝ) ^ a / 2 := by
      nlinarith [htσ, hlog3, hpow, hg]
    exact ⟨hn, hb, hwidth⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hScale
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G π σ S hO
  have ⟨hn64, hbSmallN, hwidthN⟩ := hn₀ n hn
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
  have hσSupport : σlaw.SupportedIn S := by
    intro x hx
    by_contra hne
    exact hx (hO.sigma_supp x hne)
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
  have hDenLower (x : Fin N) (hx : x ∈ S) : 1 / 2 ≤ 1 + sMean E G π x := by
    have h := abs_le.mp (hMeanAbs x hx)
    linarith
  have hDegLower (x : Fin N) (hx : x ∈ S) : 1 / 4 ≤ deg E G π x := by
    have h := hMeanDen x
    nlinarith [hDenLower x hx]
  have haFid (x : Fin N) (hx : x ∈ S) (y : Fin N) :
      aF E G π x y = (fv E G x y - sMean E G π x) / (1 + sMean E G π x) := by
    unfold aF
    rw [hMeanDen x]
    unfold fv
    have hdeg : 0 < deg E G π x := lt_of_lt_of_le (by norm_num) (hDegLower x hx)
    field_simp [ne_of_gt hdeg]
    <;> nlinarith [hMeanDen x]
  have haBound (x : Fin N) (hx : x ∈ S) (y : Fin N) : |aF E G π x y| ≤ 5 := by
    have hmean : |sMean E G π x| ≤ 1 / 2 := hMeanAbs x hx
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
      |hit E G x y / deg E G π x - 1| ≤ |hit E G x y / deg E G π x| + 1 := by
        simpa using abs_sub (hit E G x y / deg E G π x) 1
      _ ≤ 5 := by linarith
  intro J hJ
  -- The second-moment expansion reduces the target to a kernel estimate under π⊗π;
  -- discrepancy controls that kernel outside an exponentially small set, then Cauchy--Schwarz applies.
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

set_option maxHeartbeats 400000 in
/-- L11.3e (11:282–292).  On `w ≤ n^{-1.03}` the weight is at most `e^{2^u n^{-.03}}`; on
`n^{-1.03} < w ≤ n^{-1+.06}` use the two-free estimate (`C_u e^{2^u n^{.06} - n^{.4}}`), on
`n^{-1+.06} < w ≤ n^{-υ}` the one-free estimate (`C_u e^{2^u n^{1-υ} - n^{1-υ/4}/2}`); finitely many `u ≤ U`. -/
theorem moderate (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hA : OneFreeEv δ x₀ K) (hB : TwoFreeEv δ x₀ K) : ModerateEv δ x₀ K := by
  classical
  unfold ModerateEv
  intro U P'
  let cA : ℕ → ℝ := fun v => Classical.choose (hA v)
  have hArest (v : ℕ) := Classical.choose_spec (hA v)
  let nA : ℕ → ℕ := fun v => Classical.choose (hArest v)
  have hAvalid (v : ℕ) := Classical.choose_spec (hArest v)
  have hBrest (v : ℕ) := hB v
  let nB : ℕ → ℕ := fun v => Classical.choose (hBrest v)
  have hBvalid (v : ℕ) := Classical.choose_spec (hBrest v)
  let idxs : Finset ℕ := Finset.range (U + 1)
  let cmax : ℝ := (∑ v ∈ idxs, max (cA v) 0) + 1
  let nAmax : ℕ := ∑ v ∈ idxs, nA v
  let nBmax : ℕ := ∑ v ∈ idxs, nB v
  let nStart : ℕ := max 64 (nAmax + nBmax + 2)
  have huMem (u : ℕ) (hu : u ≤ U) : u ∈ idxs := by
    dsimp [idxs]
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hu)
  have hcmax_nonneg : 0 ≤ cmax := by
    dsimp [cmax]
    positivity
  have hcmax (u : ℕ) (hu : u ≤ U) : cA u ≤ cmax := by
    dsimp [cmax]
    calc
      cA u ≤ max (cA u) 0 := le_max_left _ _
      _ ≤ ∑ v ∈ idxs, max (cA v) 0 :=
        Finset.single_le_sum (fun v hv => le_max_right _ _) (huMem u hu)
      _ ≤ (∑ v ∈ idxs, max (cA v) 0) + 1 := by linarith
  have hnAmax (u : ℕ) (hu : u ≤ U) : nA u ≤ nAmax := by
    dsimp [nAmax]
    exact Finset.single_le_sum (fun v hv => Nat.zero_le _) (huMem u hu)
  have hnBmax (u : ℕ) (hu : u ≤ U) : nB u ≤ nBmax := by
    dsimp [nBmax]
    exact Finset.single_le_sum (fun v hv => Nat.zero_le _) (huMem u hu)
  let a : ℝ := 1 - δ / 16
  let ell : ℝ := 1 - δ / 4
  let Amax : ℝ := (2 : ℝ) ^ U
  let Mmax : ℝ := (2 : ℝ) ^ U
  let Pstar : ℝ := max P' 0 + 1
  have ha_pos : 0 < a := by dsimp [a]; nlinarith
  have hell_pos : 0 < ell := by dsimp [ell]; nlinarith
  have hell_lt_a : ell < a := by dsimp [ell, a]; linarith
  have hCgap := OuterMoment_q_s11_outer.eventually_pow_gap
    (-(19 : ℝ) / 20) (-(94 : ℝ) / 100) (cmax + 1) (by norm_num) (by positivity)
  have hGapOne := OuterMoment_q_s11_outer.eventually_pow_gap
    ((1 : ℝ) / 10) ((2 : ℝ) / 5)
    (2 * (Amax + Mmax + 10 * Pstar + 3)) (by norm_num) (by positivity)
  have hGapTwo := OuterMoment_q_s11_outer.eventually_pow_gap
    ell a (2 * (Amax + 2 * Mmax + 10 * Pstar + 3)) hell_lt_a (by positivity)
  have hnLarge : ∀ᶠ n : ℕ in atTop, 2 ≤ n :=
    eventually_atTop.mpr ⟨2, fun _ hn => hn⟩
  have hScale : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ (cmax + 1) * (n : ℝ) ^ (-(19 : ℝ) / 20) <
          (n : ℝ) ^ (-(94 : ℝ) / 100) ∧
        2 * (Amax + Mmax + 10 * Pstar + 3) * (n : ℝ) ^ ((1 : ℝ) / 10) <
          (n : ℝ) ^ ((2 : ℝ) / 5) ∧
        2 * (Amax + 2 * Mmax + 10 * Pstar + 3) * (n : ℝ) ^ ell < (n : ℝ) ^ a := by
    filter_upwards [hnLarge, hCgap, hGapOne, hGapTwo] with n hn hc h1 h2
    exact ⟨hn, hc, h1, h2⟩
  obtain ⟨nScale, hnScale⟩ := Filter.eventually_atTop.1 hScale
  let n₀ := max nStart nScale
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G π σ S hO u hu
  have hnStart : n ≥ nStart := le_trans (le_max_left _ _) hn
  have hnScale' : n ≥ nScale := le_trans (le_max_right _ _) hn
  have hnA : n ≥ nA u := by
    have hsum : nA u ≤ nAmax := hnAmax u hu
    dsimp [nStart] at hnStart
    dsimp [nAmax] at hsum
    omega
  have hnB : n ≥ nB u := by
    have hsum : nB u ≤ nBmax := hnBmax u hu
    dsimp [nStart] at hnStart
    dsimp [nBmax] at hsum
    omega
  have hpars := hnScale n hnScale'
  rcases hpars with ⟨hn2, hCpow, hGapOneN, hGapTwoN⟩
  have hn1R : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hσpos : ∃ x, 0 < σ x := by
    by_contra h
    have hnonpos : ∀ x, σ x ≤ 0 := by
      intro x
      by_contra hx
      exact h ⟨x, lt_of_not_ge hx⟩
    have hzero : ∀ x, σ x = 0 := by
      intro x
      exact le_antisymm (hnonpos x) (hO.sigma_nonneg x)
    have hsum0 : (∑ x, σ x) = 0 := Finset.sum_eq_zero fun x hx => hzero x
    have hsum := hO.sigma_sum
    rw [hsum0] at hsum
    norm_num at hsum
  obtain ⟨x₀, hx₀pos⟩ := hσpos
  have hx₀S : x₀ ∈ S := hO.sigma_supp x₀ (ne_of_gt hx₀pos)
  have hwt_nonneg (f : Fin u → Fin N) : 0 ≤ tupWt σ f := by
    unfold tupWt
    exact Finset.prod_nonneg fun i hi => hO.sigma_nonneg (f i)
  have hwt_sum : (∑ f : Fin u → Fin N, tupWt σ f) = 1 := by
    unfold tupWt
    calc
      (∑ f : Fin u → Fin N, ∏ i, σ (f i)) = ∏ i : Fin u, ∑ x, σ x := by
        symm
        exact Fintype.prod_sum (fun (_ : Fin u) (x : Fin N) => σ x)
      _ = 1 := by simp [hO.sigma_sum]
  have hOne := hAvalid u n hnA (N := N) (E := E) (X := X) (Y := Y) G π σ S hO
  have hTwo := hBvalid u n hnB (N := N) (E := E) (X := X) (Y := Y) G π σ S hO
  have hUnion (v b : ℝ) (hv : 0 < v) (hb : 0 ≤ b)
      (hper : ∀ J : Finset (Fin u), 2 ≤ J.card →
        (∑ f : Fin u → Fin N, tupWt σ f *
          (if v < |inter E G π J f| then 1 else 0)) ≤ b) :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if v < env E G π f then 1 else 0)) ≤ (Fintype.card (Finset (Fin u) : Type) : ℝ) * b := by
    have hpoint (f : Fin u → Fin N) :
        (if v < env E G π f then (1 : ℝ) else 0) ≤
          ∑ J : Finset (Fin u), if 2 ≤ J.card ∧ v < |inter E G π J f| then (1 : ℝ) else 0 := by
      by_cases henv : v < env E G π f
      · have hsome : ∃ J : Finset (Fin u), 2 ≤ J.card ∧ v < |inter E G π J f| := by
          have hmax' : v < (Finset.univ : Finset (Finset (Fin u))).sup'
              (⟨∅, Finset.mem_univ _⟩) (fun J : Finset (Fin u) =>
                if 2 ≤ J.card then |inter E G π J f| else 0) := by
            simpa [env] using henv
          have hmax := (Finset.lt_sup'_iff
            (show (Finset.univ : Finset (Finset (Fin u))).Nonempty from ⟨∅, Finset.mem_univ _⟩)).mp hmax'
          rcases hmax with ⟨J, hJ, hJlt⟩
          by_cases hJcard : 2 ≤ J.card
          · exact ⟨J, hJcard, by simpa [hJcard] using hJlt⟩
          · have hJzero : (if 2 ≤ J.card then |inter E G π J f| else 0) = 0 := by simp [hJcard]
            rw [hJzero] at hJlt
            exact False.elim (not_lt_of_ge hv.le hJlt)
        rcases hsome with ⟨J, hJcard, hJevent⟩
        have hsum : (1 : ℝ) ≤
            ∑ J' : Finset (Fin u), if 2 ≤ J'.card ∧ v < |inter E G π J' f| then (1 : ℝ) else 0 := by
          calc
            (1 : ℝ) = (if 2 ≤ J.card ∧ v < |inter E G π J f| then (1 : ℝ) else 0) := by simp [hJcard, hJevent]
            _ ≤ ∑ J' : Finset (Fin u), if 2 ≤ J'.card ∧ v < |inter E G π J' f| then (1 : ℝ) else 0 := by
              exact Finset.single_le_sum
                (f := fun J' : Finset (Fin u) =>
                  if 2 ≤ J'.card ∧ v < |inter E G π J' f| then (1 : ℝ) else 0)
                (fun J' hJ' => by split_ifs <;> norm_num)
                (Finset.mem_univ J)
        simpa [henv] using hsum
      · simp only [if_neg henv]
        exact Finset.sum_nonneg fun J hJ => by split_ifs <;> positivity
    calc
      (∑ f : Fin u → Fin N, tupWt σ f * (if v < env E G π f then 1 else 0)) ≤
          ∑ f : Fin u → Fin N, tupWt σ f *
            (∑ J : Finset (Fin u), if 2 ≤ J.card ∧ v < |inter E G π J f| then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro f hf
        exact mul_le_mul_of_nonneg_left (hpoint f) (hwt_nonneg f)
      _ = ∑ J : Finset (Fin u), ∑ f : Fin u → Fin N, tupWt σ f *
            (if 2 ≤ J.card ∧ v < |inter E G π J f| then 1 else 0) := by
        calc
          (∑ f : Fin u → Fin N, tupWt σ f *
              (∑ J : Finset (Fin u), if 2 ≤ J.card ∧ v < |inter E G π J f| then (1 : ℝ) else 0)) =
              ∑ f : Fin u → Fin N, ∑ J : Finset (Fin u), tupWt σ f *
                (if 2 ≤ J.card ∧ v < |inter E G π J f| then (1 : ℝ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro f hf
                  rw [Finset.mul_sum]
          _ = ∑ J : Finset (Fin u), ∑ f : Fin u → Fin N, tupWt σ f *
                (if 2 ≤ J.card ∧ v < |inter E G π J f| then (1 : ℝ) else 0) := by rw [Finset.sum_comm]
      _ ≤ ∑ J : Finset (Fin u), b := by
        apply Finset.sum_le_sum
        intro J hJ
        by_cases hJcard : 2 ≤ J.card
        · simpa [hJcard] using hper J hJcard
        · simpa [hJcard] using hb
      _ = (Fintype.card (Finset (Fin u) : Type) : ℝ) * b := by simp
  have hTwoPer (J : Finset (Fin u)) (hJ : 2 ≤ J.card) :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if (n : ℝ) ^ (-(103 : ℝ) / 100) < |inter E G π J f| then 1 else 0)) ≤
        Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5))) := by
    obtain ⟨j, hj, j', hj', hjj⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
    apply OuterMoment_q_s11_outer.tuple_event_mass_le_of_two_free
      σ S hO.sigma_nonneg hO.sigma_sum hO.sigma_supp j j' hjj x₀ hx₀S
      (fun f => (n : ℝ) ^ (-(103 : ℝ) / 100) < |inter E G π J f|)
      (Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))) (by positivity)
    intro base hbase
    exact hTwo J j j' hj hj' hjj base hbase
  have hOneThreshold : cA u * bS n ≤ (n : ℝ) ^ (-(94 : ℝ) / 100) := by
    have hcA : cA u ≤ cmax := hcmax u hu
    have hbS : 0 ≤ bS n := by unfold bS; positivity
    have hcA' : cA u * bS n ≤ cmax * bS n := mul_le_mul_of_nonneg_right hcA hbS
    have hcgap : (cmax + 1) * bS n < (n : ℝ) ^ (-(94 : ℝ) / 100) := by
      simpa [bS, neg_div] using hCpow
    have hcoeff : cmax * bS n ≤ (cmax + 1) * bS n := by
      nlinarith [mul_nonneg hbS (by norm_num : (0 : ℝ) ≤ 1)]
    exact hcA'.trans (le_of_lt (hcoeff.trans_lt hcgap))
  have hOnePer (J : Finset (Fin u)) (hJ : 2 ≤ J.card) :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if (n : ℝ) ^ (-(94 : ℝ) / 100) < |inter E G π J f| then 1 else 0)) ≤
        2 * Real.exp (-((n : ℝ) ^ a / 2)) := by
    obtain ⟨j, hj, j', hj', hjj⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
    apply OuterMoment_q_s11_outer.tuple_event_mass_le_of_one_free
      σ S hO.sigma_nonneg hO.sigma_sum hO.sigma_supp j j' hjj x₀ hx₀S
      (fun f => (n : ℝ) ^ (-(94 : ℝ) / 100) < |inter E G π J f|)
      (2 * Real.exp (-((n : ℝ) ^ a / 2))) (by positivity)
    intro base hbase
    calc
      (∑ x, σ x *
        (if (n : ℝ) ^ (-(94 : ℝ) / 100) < |inter E G π J (Function.update base j x)| then 1 else 0)) ≤
        ∑ x, σ x *
          (if cA u * bS n < |inter E G π J (Function.update base j x)| then 1 else 0) := by
            apply Finset.sum_le_sum
            intro x hx
            have hInd :
                (if (n : ℝ) ^ (-(94 : ℝ) / 100) <
                    |inter E G π J (Function.update base j x)| then (1 : ℝ) else 0) ≤
                  (if cA u * bS n < |inter E G π J (Function.update base j x)| then 1 else 0) := by
              by_cases hlarge : (n : ℝ) ^ (-(94 : ℝ) / 100) <
                  |inter E G π J (Function.update base j x)|
              · have hlarge' : cA u * bS n <
                  |inter E G π J (Function.update base j x)| := lt_of_le_of_lt hOneThreshold hlarge
                simp [hlarge, hlarge']
              · simp only [if_neg hlarge]
                split_ifs <;> norm_num
            exact mul_le_mul_of_nonneg_left hInd (hO.sigma_nonneg x)
      _ ≤ 2 * Real.exp (((-1 : ℝ) * (n : ℝ) ^ a) / 2) := by
        simpa [cA, a] using hOne J j hj base hbase
      _ = 2 * Real.exp (-((n : ℝ) ^ a / 2)) := by congr 1; congr 1; ring
  let t0 : ℝ := (n : ℝ) ^ (-(103 : ℝ) / 100)
  let t1 : ℝ := (n : ℝ) ^ (-(94 : ℝ) / 100)
  let cap : ℝ := (n : ℝ) ^ (-(δ / 4))
  let A : ℝ := (2 : ℝ) ^ u
  let M : ℝ := (Fintype.card (Finset (Fin u)) : ℝ)
  have hA_bound : A ≤ Amax := by
    dsimp [A, Amax]
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hu)
  have hcardFinset : Fintype.card (Finset (Fin u)) = 2 ^ u := by
    simp [Fintype.card_finset]
  have hM_bound : M ≤ Mmax := by
    have hMA : M = A := by
      dsimp [M, A]
      exact_mod_cast hcardFinset
    rw [hMA]
    simpa [Amax, Mmax] using hA_bound
  have hnpos : 0 < (n : ℝ) := by positivity
  have hmulRpow (q : ℝ) : (n : ℝ) * (n : ℝ) ^ q = (n : ℝ) ^ (1 + q) := by
    calc
      (n : ℝ) * (n : ℝ) ^ q = (n : ℝ) ^ 1 * (n : ℝ) ^ q :=
        congrArg (fun z : ℝ => z * (n : ℝ) ^ q) (Real.rpow_one (n : ℝ)).symm
      _ = (n : ℝ) ^ (1 + q) := by rw [Real.rpow_add hnpos]
  have hnt0 : (n : ℝ) * t0 ≤ 1 := by
    dsimp [t0]
    calc
      (n : ℝ) * (n : ℝ) ^ (-(103 : ℝ) / 100) =
          (n : ℝ) ^ (-(3 : ℝ) / 100) := by rw [hmulRpow]; congr 1; norm_num
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1R (by norm_num)
  have hnt1 : (n : ℝ) * t1 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
    dsimp [t1]
    calc
      (n : ℝ) * (n : ℝ) ^ (-(94 : ℝ) / 100) =
          (n : ℝ) ^ ((6 : ℝ) / 100) := by rw [hmulRpow]; congr 1; norm_num
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
  have hncap : (n : ℝ) * cap = (n : ℝ) ^ ell := by
    dsimp [cap, ell]
    calc
      (n : ℝ) * (n : ℝ) ^ (-(δ / 4)) = (n : ℝ) ^ (1 + (-(δ / 4))) := hmulRpow _
      _ = (n : ℝ) ^ (1 - δ / 4) := by congr 1
  have hlogn : Real.log (n : ℝ) ≤ 10 * (n : ℝ) ^ ((1 : ℝ) / 10) := by
    calc
      Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 10) / ((1 : ℝ) / 10) :=
        Real.log_natCast_le_rpow_div n (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)
      _ = 10 * (n : ℝ) ^ ((1 : ℝ) / 10) := by ring
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hPstar_nonneg : 0 ≤ Pstar := by dsimp [Pstar]; positivity
  have hPstar_ge1 : 1 ≤ Pstar := by dsimp [Pstar]; linarith [le_max_right P' 0]
  have hPstar_geP : P' + 1 ≤ Pstar := by dsimp [Pstar]; linarith [le_max_left P' 0]
  have hAmax_nonneg : 0 ≤ Amax := by dsimp [Amax]; positivity
  have hMmax_nonneg : 0 ≤ Mmax := by dsimp [Mmax]; positivity
  have hMexp : Mmax ≤ Real.exp Mmax := by
    have h := Real.add_one_le_exp Mmax
    nlinarith [h, hMmax_nonneg]
  have h2Mexp : 2 * Mmax ≤ Real.exp (2 * Mmax) := by
    have h := Real.add_one_le_exp (2 * Mmax)
    nlinarith [h, hMmax_nonneg]
  have hprob0 :
      (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) ≤
        Mmax * Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5))) := by
    have h := hUnion t0 (Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))) (by positivity)
      (by positivity) hTwoPer
    have hraw :
        (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) ≤
          A * Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5))) := by simpa [t0, A, hcardFinset] using h
    exact hraw.trans (mul_le_mul_of_nonneg_right hA_bound (Real.exp_nonneg _))
  have hprob1 :
      (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤
        2 * Mmax * Real.exp (-((n : ℝ) ^ a / 2)) := by
    have h := hUnion t1 (2 * Real.exp (-((n : ℝ) ^ a / 2))) (by positivity)
      (by positivity) hOnePer
    have hraw :
        (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤
          A * (2 * Real.exp (-((n : ℝ) ^ a / 2))) := by simpa [t1, A, hcardFinset] using h
    calc
      (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤
          A * (2 * Real.exp (-((n : ℝ) ^ a / 2))) := hraw
      _ = 2 * (A * Real.exp (-((n : ℝ) ^ a / 2))) := by ring
      _ ≤ 2 * (Mmax * Real.exp (-((n : ℝ) ^ a / 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hA_bound (Real.exp_nonneg _)) (by norm_num)
      _ = 2 * Mmax * Real.exp (-((n : ℝ) ^ a / 2)) := by ring
  have hnPow01 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1R
      (y := 0) (z := (1 : ℝ) / 10) (by norm_num)
  have hell_ge_tenth : (1 : ℝ) / 10 ≤ ell := by dsimp [ell]; linarith [hδ']
  have hnPowEll : 1 ≤ (n : ℝ) ^ ell := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1R (y := 0) (z := ell) hell_pos.le
  have hnPowTenthLeEll : (n : ℝ) ^ ((1 : ℝ) / 10) ≤ (n : ℝ) ^ ell :=
    Real.rpow_le_rpow_of_exponent_le hn1R hell_ge_tenth
  have hMterm : Mmax ≤ Mmax * (n : ℝ) ^ ((1 : ℝ) / 10) := by
    calc
      Mmax = Mmax * 1 := by ring
      _ ≤ Mmax * (n : ℝ) ^ ((1 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_left hnPow01 hMmax_nonneg
  have hAterm : A * ((n : ℝ) * t1) ≤ Amax * (n : ℝ) ^ ((1 : ℝ) / 10) := by
    calc
      A * ((n : ℝ) * t1) ≤ Amax * ((n : ℝ) * t1) :=
        mul_le_mul_of_nonneg_right hA_bound (by positivity)
      _ ≤ Amax * (n : ℝ) ^ ((1 : ℝ) / 10) :=
        mul_le_mul_of_nonneg_left hnt1 hAmax_nonneg
  have hPterm : Pstar * Real.log (n : ℝ) ≤ 10 * Pstar * (n : ℝ) ^ ((1 : ℝ) / 10) := by
    calc
      Pstar * Real.log (n : ℝ) ≤ Pstar * (10 * (n : ℝ) ^ ((1 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_left hlogn hPstar_nonneg
      _ = 10 * Pstar * (n : ℝ) ^ ((1 : ℝ) / 10) := by ring
  have hlog2term : Real.log 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
    exact hlog2.trans hnPow01
  have hAddOne : Mmax + A * ((n : ℝ) * t1) + Pstar * Real.log (n : ℝ) + Real.log 2 ≤
      (Amax + Mmax + 10 * Pstar + 1) * (n : ℝ) ^ ((1 : ℝ) / 10) := by
    have hsum := add_le_add (add_le_add hMterm hAterm) (add_le_add hPterm hlog2term)
    calc
      Mmax + A * ((n : ℝ) * t1) + Pstar * Real.log (n : ℝ) + Real.log 2 ≤
          (Mmax * (n : ℝ) ^ ((1 : ℝ) / 10) + Amax * (n : ℝ) ^ ((1 : ℝ) / 10)) +
            (10 * Pstar * (n : ℝ) ^ ((1 : ℝ) / 10) + (n : ℝ) ^ ((1 : ℝ) / 10)) := by
              simpa [add_assoc] using hsum
      _ = (Amax + Mmax + 10 * Pstar + 1) * (n : ℝ) ^ ((1 : ℝ) / 10) := by ring
  have hCoeffOne : (Amax + Mmax + 10 * Pstar + 1) * (n : ℝ) ^ ((1 : ℝ) / 10) <
      (n : ℝ) ^ ((2 : ℝ) / 5) / 2 := by
    have hcoef : Amax + Mmax + 10 * Pstar + 1 ≤ Amax + Mmax + 10 * Pstar + 3 := by linarith
    have hpow_nonneg : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hprod := mul_le_mul_of_nonneg_right hcoef hpow_nonneg
    have hstrict : (Amax + Mmax + 10 * Pstar + 3) * (n : ℝ) ^ ((1 : ℝ) / 10) <
        (n : ℝ) ^ ((2 : ℝ) / 5) / 2 := by nlinarith only [hGapOneN]
    exact lt_of_le_of_lt hprod hstrict
  have hAddTwo : 2 * Mmax + A * ((n : ℝ) * cap) + Pstar * Real.log (n : ℝ) + Real.log 2 ≤
      (Amax + 2 * Mmax + 10 * Pstar + 1) * (n : ℝ) ^ ell := by
    have hMterm' : 2 * Mmax ≤ 2 * Mmax * (n : ℝ) ^ ell := by
      calc
        2 * Mmax = (2 * Mmax) * 1 := by ring
        _ ≤ (2 * Mmax) * (n : ℝ) ^ ell :=
          mul_le_mul_of_nonneg_left hnPowEll (by positivity)
    have hAterm' : A * ((n : ℝ) * cap) ≤ Amax * (n : ℝ) ^ ell := by
      rw [hncap]
      exact mul_le_mul_of_nonneg_right hA_bound (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hPterm' : Pstar * Real.log (n : ℝ) ≤ 10 * Pstar * (n : ℝ) ^ ell := by
      calc
        Pstar * Real.log (n : ℝ) ≤ 10 * Pstar * (n : ℝ) ^ ((1 : ℝ) / 10) := hPterm
        _ ≤ 10 * Pstar * (n : ℝ) ^ ell :=
          mul_le_mul_of_nonneg_left hnPowTenthLeEll (by positivity)
    have hlog2term' : Real.log 2 ≤ (n : ℝ) ^ ell := hlog2.trans hnPowEll
    have hsum := add_le_add (add_le_add hMterm' hAterm') (add_le_add hPterm' hlog2term')
    calc
      2 * Mmax + A * ((n : ℝ) * cap) + Pstar * Real.log (n : ℝ) + Real.log 2 ≤
          (2 * Mmax * (n : ℝ) ^ ell + Amax * (n : ℝ) ^ ell) +
            (10 * Pstar * (n : ℝ) ^ ell + (n : ℝ) ^ ell) := by simpa [add_assoc] using hsum
      _ = (Amax + 2 * Mmax + 10 * Pstar + 1) * (n : ℝ) ^ ell := by ring
  have hCoeffTwo : (Amax + 2 * Mmax + 10 * Pstar + 1) * (n : ℝ) ^ ell <
      (n : ℝ) ^ a / 2 := by
    have hcoef : Amax + 2 * Mmax + 10 * Pstar + 1 ≤ Amax + 2 * Mmax + 10 * Pstar + 3 := by linarith
    have hpow_nonneg : 0 ≤ (n : ℝ) ^ ell := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hprod := mul_le_mul_of_nonneg_right hcoef hpow_nonneg
    have hstrict : (Amax + 2 * Mmax + 10 * Pstar + 3) * (n : ℝ) ^ ell <
        (n : ℝ) ^ a / 2 := by nlinarith only [hGapTwoN]
    exact lt_of_le_of_lt hprod hstrict
  have hTailTwo : Real.exp (A * ((n : ℝ) * t1)) *
      (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) ≤
        (n : ℝ) ^ (-Pstar) := by
    calc
      Real.exp (A * ((n : ℝ) * t1)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) ≤
          Real.exp (A * ((n : ℝ) * t1)) * (Mmax * Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))) :=
        mul_le_mul_of_nonneg_left hprob0 (Real.exp_nonneg _)
      _ = Mmax * Real.exp (A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5)) := by
        calc
          Real.exp (A * ((n : ℝ) * t1)) * (Mmax * Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))) =
              Mmax * (Real.exp (A * ((n : ℝ) * t1)) * Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5)))) := by ring
          _ = Mmax * Real.exp (A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5)) := by
            have hExp : Real.exp (A * ((n : ℝ) * t1)) *
                Real.exp (-((n : ℝ) ^ ((2 : ℝ) / 5))) =
                Real.exp (A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5)) := by
              calc
                _ = Real.exp (A * ((n : ℝ) * t1) + (-((n : ℝ) ^ ((2 : ℝ) / 5)))) :=
                  (Real.exp_add _ _).symm
                _ = _ := by congr 1
            exact congrArg (fun z : ℝ => Mmax * z) hExp
      _ ≤ Real.exp Mmax * Real.exp (A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_right hMexp (Real.exp_nonneg _)
      _ = Real.exp (Mmax + A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5)) := by
        simpa [sub_eq_add_neg, add_assoc] using
          (Real.exp_add Mmax (A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5))).symm
      _ ≤ Real.exp (-Pstar * Real.log (n : ℝ)) := by
        have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        have hpow_nonneg : 0 ≤ (n : ℝ) ^ ((2 : ℝ) / 5) :=
          Real.rpow_nonneg (Nat.cast_nonneg n) _
        have htotal : Mmax + A * ((n : ℝ) * t1) + Pstar * Real.log (n : ℝ) + Real.log 2 <
            (n : ℝ) ^ ((2 : ℝ) / 5) / 2 := hAddOne.trans_lt hCoeffOne
        have hhalf : (n : ℝ) ^ ((2 : ℝ) / 5) / 2 ≤ (n : ℝ) ^ ((2 : ℝ) / 5) := by
          exact div_le_self hpow_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        have hbaseStrict : Mmax + A * ((n : ℝ) * t1) + Pstar * Real.log (n : ℝ) <
            (n : ℝ) ^ ((2 : ℝ) / 5) := by
          calc
            Mmax + A * ((n : ℝ) * t1) + Pstar * Real.log (n : ℝ) ≤
                Mmax + A * ((n : ℝ) * t1) + Pstar * Real.log (n : ℝ) + Real.log 2 := by
                  exact le_add_of_nonneg_right hlog2nonneg
            _ < (n : ℝ) ^ ((2 : ℝ) / 5) / 2 := htotal
            _ ≤ (n : ℝ) ^ ((2 : ℝ) / 5) := hhalf
        have hExponent := OuterMoment_q_s11_outer.sub_le_neg_of_add_le (le_of_lt hbaseStrict)
        have hExponent' : Mmax + A * ((n : ℝ) * t1) - (n : ℝ) ^ ((2 : ℝ) / 5) ≤
            -Pstar * Real.log (n : ℝ) := by simpa only [neg_mul] using hExponent
        exact Real.exp_le_exp.mpr hExponent'
      _ = (n : ℝ) ^ (-Pstar) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
  have hTailOne : Real.exp (A * ((n : ℝ) * cap)) *
      (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤
        (n : ℝ) ^ (-Pstar) := by
    calc
      Real.exp (A * ((n : ℝ) * cap)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤
          Real.exp (A * ((n : ℝ) * cap)) * (2 * Mmax * Real.exp (-((n : ℝ) ^ a / 2))) :=
        mul_le_mul_of_nonneg_left hprob1 (Real.exp_nonneg _)
      _ = 2 * Mmax * Real.exp (A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2) := by
        calc
          Real.exp (A * ((n : ℝ) * cap)) * (2 * Mmax * Real.exp (-((n : ℝ) ^ a / 2))) =
              2 * Mmax * (Real.exp (A * ((n : ℝ) * cap)) * Real.exp (-((n : ℝ) ^ a / 2))) := by ring
          _ = 2 * Mmax * Real.exp (A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2) := by
            have hExp : Real.exp (A * ((n : ℝ) * cap)) *
                Real.exp (-((n : ℝ) ^ a / 2)) =
                Real.exp (A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2) := by
              calc
                _ = Real.exp (A * ((n : ℝ) * cap) + (-((n : ℝ) ^ a / 2))) :=
                  (Real.exp_add _ _).symm
                _ = _ := by congr 1
            exact congrArg (fun z : ℝ => 2 * Mmax * z) hExp
      _ ≤ Real.exp (2 * Mmax) * Real.exp (A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2) :=
        mul_le_mul_of_nonneg_right h2Mexp (Real.exp_nonneg _)
      _ = Real.exp (2 * Mmax + A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2) := by
        have harg : 2 * Mmax + A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2 =
            2 * Mmax + (A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2) := by ring
        rw [harg]
        exact (Real.exp_add (2 * Mmax) (A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2)).symm
      _ ≤ Real.exp (-Pstar * Real.log (n : ℝ)) := by
        have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
        have htotal : 2 * Mmax + A * ((n : ℝ) * cap) + Pstar * Real.log (n : ℝ) + Real.log 2 <
            (n : ℝ) ^ a / 2 := hAddTwo.trans_lt hCoeffTwo
        have hbaseStrict : 2 * Mmax + A * ((n : ℝ) * cap) + Pstar * Real.log (n : ℝ) <
            (n : ℝ) ^ a / 2 := by
          calc
            2 * Mmax + A * ((n : ℝ) * cap) + Pstar * Real.log (n : ℝ) ≤
                2 * Mmax + A * ((n : ℝ) * cap) + Pstar * Real.log (n : ℝ) + Real.log 2 := by
                  exact le_add_of_nonneg_right hlog2nonneg
            _ < (n : ℝ) ^ a / 2 := htotal
        have hExponent := OuterMoment_q_s11_outer.sub_le_neg_of_add_le (le_of_lt hbaseStrict)
        have hExponent' : 2 * Mmax + A * ((n : ℝ) * cap) - (n : ℝ) ^ a / 2 ≤
            -Pstar * Real.log (n : ℝ) := by simpa only [neg_mul] using hExponent
        exact Real.exp_le_exp.mpr hExponent'
      _ = (n : ℝ) ^ (-Pstar) := by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring
  have hn2R : 2 ≤ (n : ℝ) := by exact_mod_cast hn2
  have hInvHalf : (n : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    have hInv : (n : ℝ) ^ (-(1 : ℝ)) = (n : ℝ)⁻¹ := by rw [Real.rpow_neg_one]
    rw [hInv]
    simpa [one_div] using (inv_le_inv₀ hnpos (by norm_num : (0 : ℝ) < 2)).2 hn2R
  have hPstarSmall : (n : ℝ) ^ (-Pstar) ≤ 1 / 2 := by
    calc
      (n : ℝ) ^ (-Pstar) ≤ (n : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by linarith [hPstar_ge1])
      _ ≤ 1 / 2 := hInvHalf
  have hPstarHalf : (n : ℝ) ^ (-Pstar) ≤ (n : ℝ) ^ (-P') / 2 := by
    have hexp : -Pstar ≤ -(P' + 1) := by linarith [hPstar_geP]
    calc
      (n : ℝ) ^ (-Pstar) ≤ (n : ℝ) ^ (-(P' + 1)) :=
        Real.rpow_le_rpow_of_exponent_le hn1R hexp
      _ = (n : ℝ) ^ (-P') * (n : ℝ) ^ (-(1 : ℝ)) := by
        rw [show -(P' + 1) = (-P') + (-(1 : ℝ)) by ring, Real.rpow_add hnpos]
      _ ≤ (n : ℝ) ^ (-P') * (1 / 2) :=
        mul_le_mul_of_nonneg_left hInvHalf (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n : ℝ) ^ (-P') / 2 := by ring
  have hBaseSum : (∑ f : Fin u → Fin N, tupWt σ f * Real.exp A) = Real.exp A := by
    calc
      (∑ f : Fin u → Fin N, tupWt σ f * Real.exp A) =
          (∑ f : Fin u → Fin N, tupWt σ f) * Real.exp A := by rw [Finset.sum_mul]
      _ = Real.exp A := by rw [hwt_sum]; ring
  have hBump0 :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0)) =
        Real.exp (A * ((n : ℝ) * t1)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) := by
    calc
      (∑ f : Fin u → Fin N, tupWt σ f *
          (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0)) =
        ∑ f : Fin u → Fin N, Real.exp (A * ((n : ℝ) * t1)) *
          (tupWt σ f * (if t0 < env E G π f then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro f hf
            by_cases hf0 : t0 < env E G π f <;> simp [hf0] <;> ring
      _ = Real.exp (A * ((n : ℝ) * t1)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) := by
            rw [Finset.mul_sum]
  have hBump1 :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0)) =
        Real.exp (A * ((n : ℝ) * cap)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
    calc
      (∑ f : Fin u → Fin N, tupWt σ f *
          (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0)) =
        ∑ f : Fin u → Fin N, Real.exp (A * ((n : ℝ) * cap)) *
          (tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro f hf
            by_cases hf1 : t1 < env E G π f <;> simp [hf1] <;> ring
      _ = Real.exp (A * ((n : ℝ) * cap)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
            rw [Finset.mul_sum]
  have hBaseNonneg (f : Fin u → Fin N) : 0 ≤ tupWt σ f * Real.exp A :=
    mul_nonneg (hwt_nonneg f) (Real.exp_nonneg _)
  have hBump0Nonneg (f : Fin u → Fin N) :
      0 ≤ tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) := by
    by_cases h : t0 < env E G π f
    · simpa only [if_pos h] using mul_nonneg (hwt_nonneg f) (Real.exp_nonneg _)
    · simp only [if_neg h, mul_zero]
      exact le_rfl
  have hBump1Nonneg (f : Fin u → Fin N) :
      0 ≤ tupWt σ f * (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0) := by
    by_cases h : t1 < env E G π f
    · simpa only [if_pos h] using mul_nonneg (hwt_nonneg f) (Real.exp_nonneg _)
    · simp only [if_neg h, mul_zero]
      exact le_rfl
  have hcoefNonneg : 0 ≤ A * (n : ℝ) := mul_nonneg (by positivity) (by positivity)
  have hExpBase (f : Fin u → Fin N) (hf : env E G π f ≤ t0) :
      Real.exp (A * ((n : ℝ) * env E G π f)) ≤ Real.exp A := by
    apply Real.exp_le_exp.mpr
    calc
      A * ((n : ℝ) * env E G π f) ≤ A * ((n : ℝ) * t0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
      _ = A * ((n : ℝ) * t0) := rfl
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hnt0 (by positivity)
      _ = A := by ring
  have hExpMid (f : Fin u → Fin N) (hf : env E G π f ≤ t1) :
      Real.exp (A * ((n : ℝ) * env E G π f)) ≤ Real.exp (A * ((n : ℝ) * t1)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
  have hExpCap (f : Fin u → Fin N) (hf : env E G π f ≤ cap) :
      Real.exp (A * ((n : ℝ) * env E G π f)) ≤ Real.exp (A * ((n : ℝ) * cap)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
  have hPointBounded (f : Fin u → Fin N) :
      tupWt σ f *
        (if env E G π f ≤ cap then Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0) ≤
      tupWt σ f * Real.exp A +
        tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) +
        tupWt σ f * (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0) := by
    have hExpIdent : ((2 : ℝ) ^ u) * n * env E G π f = A * ((n : ℝ) * env E G π f) := by
      dsimp [A]
      ring
    rw [hExpIdent]
    by_cases hcap : env E G π f ≤ cap
    · by_cases hlow : env E G π f ≤ t0
      · calc
          tupWt σ f * (if env E G π f ≤ cap then Real.exp (A * ((n : ℝ) * env E G π f)) else 0) =
              tupWt σ f * Real.exp (A * ((n : ℝ) * env E G π f)) := by simp [hcap]
          _ ≤ tupWt σ f * Real.exp A := mul_le_mul_of_nonneg_left (hExpBase f hlow) (hwt_nonneg f)
          _ ≤ tupWt σ f * Real.exp A +
                tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) :=
                  le_add_of_nonneg_right (hBump0Nonneg f)
          _ ≤ tupWt σ f * Real.exp A +
                tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) +
                tupWt σ f * (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0) :=
                  le_add_of_nonneg_right (hBump1Nonneg f)
      · by_cases hmid : env E G π f ≤ t1
        · have h0lt : t0 < env E G π f := lt_of_not_ge hlow
          have h1not : ¬ t1 < env E G π f := not_lt_of_ge hmid
          simp only [if_pos hcap, if_pos h0lt, if_neg h1not, mul_zero, add_zero]
          calc
            tupWt σ f * Real.exp (A * ((n : ℝ) * env E G π f)) ≤
                tupWt σ f * Real.exp (A * ((n : ℝ) * t1)) :=
                  mul_le_mul_of_nonneg_left (hExpMid f hmid) (hwt_nonneg f)
            _ ≤ tupWt σ f * Real.exp A + tupWt σ f * Real.exp (A * ((n : ℝ) * t1)) := by
                  simpa only [zero_add] using
                    add_le_add_left (hBaseNonneg f) (tupWt σ f * Real.exp (A * ((n : ℝ) * t1)))
        · have h1lt : t1 < env E G π f := lt_of_not_ge hmid
          have h0lt : t0 < env E G π f := lt_of_not_ge hlow
          simp only [if_pos hcap, if_pos h0lt, if_pos h1lt]
          calc
            tupWt σ f * Real.exp (A * ((n : ℝ) * env E G π f)) ≤
                tupWt σ f * Real.exp (A * ((n : ℝ) * cap)) :=
                  mul_le_mul_of_nonneg_left (hExpCap f hcap) (hwt_nonneg f)
            _ ≤ tupWt σ f * Real.exp A +
                  tupWt σ f * Real.exp (A * ((n : ℝ) * t1)) +
                  tupWt σ f * Real.exp (A * ((n : ℝ) * cap)) := by
                    have hbaseMid : 0 ≤ tupWt σ f * Real.exp A +
                        tupWt σ f * Real.exp (A * ((n : ℝ) * t1)) :=
                      add_nonneg (hBaseNonneg f)
                        (mul_nonneg (hwt_nonneg f) (Real.exp_nonneg _))
                    simpa only [zero_add] using
                      add_le_add_left hbaseMid (tupWt σ f * Real.exp (A * ((n : ℝ) * cap)))
    · simp only [if_neg hcap]
      simp only [mul_zero]
      exact add_nonneg (add_nonneg (hBaseNonneg f) (hBump0Nonneg f)) (hBump1Nonneg f)
  have hBoundedSum :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if env E G π f ≤ cap then Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0)) ≤
        Real.exp A + Real.exp (A * ((n : ℝ) * t1)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
          Real.exp (A * ((n : ℝ) * cap)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
    calc
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if env E G π f ≤ cap then Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0)) ≤
        ∑ f : Fin u → Fin N, (tupWt σ f * Real.exp A +
          tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) +
          tupWt σ f * (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0)) := by
            apply Finset.sum_le_sum
            intro f hf
            exact hPointBounded f
      _ = (∑ f : Fin u → Fin N, tupWt σ f * Real.exp A) +
            (∑ f : Fin u → Fin N, tupWt σ f *
              (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0)) +
            (∑ f : Fin u → Fin N, tupWt σ f *
              (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = Real.exp A + Real.exp (A * ((n : ℝ) * t1)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
            Real.exp (A * ((n : ℝ) * cap)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
            rw [hBaseSum, hBump0, hBump1]
  have hTail0Half : Real.exp (A * ((n : ℝ) * t1)) *
      (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) ≤ 1 / 2 :=
    (hTailTwo.trans hPstarSmall)
  have hTail1Half : Real.exp (A * ((n : ℝ) * cap)) *
      (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤ 1 / 2 :=
    (hTailOne.trans hPstarSmall)
  have hBounded : ModBounded E G π σ n δ u := by
    unfold ModBounded
    have htailSum :
        Real.exp (A * ((n : ℝ) * t1)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
          Real.exp (A * ((n : ℝ) * cap)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤ 1 := by
      calc
        _ ≤ (1 / 2 : ℝ) + 1 / 2 := add_le_add hTail0Half hTail1Half
        _ = 1 := by norm_num
    calc
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if env E G π f ≤ (n : ℝ) ^ (-(δ / 4)) then Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0)) ≤
        Real.exp A + Real.exp (A * ((n : ℝ) * t1)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
          Real.exp (A * ((n : ℝ) * cap)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
              simpa [cap] using hBoundedSum
      _ = Real.exp A +
          (Real.exp (A * ((n : ℝ) * t1)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
          Real.exp (A * ((n : ℝ) * cap)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0))) := by ring
      _ ≤ Real.exp A + 1 := add_le_add_right htailSum (Real.exp A)
      _ = Real.exp ((2 : ℝ) ^ u) + 1 := by rfl
  have hPointTail (f : Fin u → Fin N) :
      tupWt σ f *
        (if t0 < env E G π f ∧ env E G π f ≤ cap then
          Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0) ≤
      tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) +
        tupWt σ f * (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0) := by
    have hExpIdent : ((2 : ℝ) ^ u) * (n : ℝ) * env E G π f =
        A * ((n : ℝ) * env E G π f) := by dsimp [A]; ring
    rw [hExpIdent]
    by_cases hrange : t0 < env E G π f ∧ env E G π f ≤ cap
    · rcases hrange with ⟨h0, hcap⟩
      by_cases hmid : env E G π f ≤ t1
      · have h1not : ¬ t1 < env E G π f := not_lt_of_ge hmid
        simp [h0, hcap, h1not]
        exact mul_le_mul_of_nonneg_left (hExpMid f hmid) (hwt_nonneg f)
      · have h1 : t1 < env E G π f := lt_of_not_ge hmid
        simp [h0, hcap, h1]
        calc
          tupWt σ f * Real.exp (A * ((n : ℝ) * env E G π f)) ≤
              tupWt σ f * Real.exp (A * ((n : ℝ) * cap)) := by
                exact mul_le_mul_of_nonneg_left (hExpCap f hcap) (hwt_nonneg f)
          _ ≤ tupWt σ f * Real.exp (A * ((n : ℝ) * t1)) +
                tupWt σ f * Real.exp (A * ((n : ℝ) * cap)) := by
                  exact le_add_of_nonneg_left (mul_nonneg (hwt_nonneg f) (Real.exp_nonneg _))
    · simp only [if_neg hrange, mul_zero]
      exact add_nonneg (hBump0Nonneg f) (hBump1Nonneg f)
  have hTailSum :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if t0 < env E G π f ∧ env E G π f ≤ cap then
          Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0)) ≤
        Real.exp (A * ((n : ℝ) * t1)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
        Real.exp (A * ((n : ℝ) * cap)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
    calc
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if t0 < env E G π f ∧ env E G π f ≤ cap then
          Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0)) ≤
          ∑ f : Fin u → Fin N,
            (tupWt σ f * (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0) +
              tupWt σ f * (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0)) := by
                apply Finset.sum_le_sum
                intro f hf
                exact hPointTail f
      _ = (∑ f : Fin u → Fin N, tupWt σ f *
            (if t0 < env E G π f then Real.exp (A * ((n : ℝ) * t1)) else 0)) +
          (∑ f : Fin u → Fin N, tupWt σ f *
            (if t1 < env E G π f then Real.exp (A * ((n : ℝ) * cap)) else 0)) := by
              rw [Finset.sum_add_distrib]
      _ = Real.exp (A * ((n : ℝ) * t1)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
        Real.exp (A * ((n : ℝ) * cap)) *
          (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
            rw [hBump0, hBump1]
  have hTailTwoSmall : Real.exp (A * ((n : ℝ) * t1)) *
      (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) ≤
        (n : ℝ) ^ (-P') / 2 := hTailTwo.trans hPstarHalf
  have hTailOneSmall : Real.exp (A * ((n : ℝ) * cap)) *
      (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) ≤
        (n : ℝ) ^ (-P') / 2 := hTailOne.trans hPstarHalf
  have hModTail : ModTail E G π σ n δ P' u := by
    unfold ModTail
    calc
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if (n : ℝ) ^ (-(103 : ℝ) / 100) < env E G π f ∧
            env E G π f ≤ (n : ℝ) ^ (-(δ / 4)) then
          Real.exp ((2 : ℝ) ^ u * n * env E G π f) else 0)) ≤
          Real.exp (A * ((n : ℝ) * t1)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t0 < env E G π f then 1 else 0)) +
          Real.exp (A * ((n : ℝ) * cap)) *
            (∑ f : Fin u → Fin N, tupWt σ f * (if t1 < env E G π f then 1 else 0)) := by
              simpa [t0, cap] using hTailSum
      _ ≤ (n : ℝ) ^ (-P') := by
          calc
            _ ≤ (n : ℝ) ^ (-P') / 2 + (n : ℝ) ^ (-P') / 2 :=
              add_le_add hTailTwoSmall hTailOneSmall
            _ = (n : ℝ) ^ (-P') := by ring
  exact ⟨hBounded, hModTail⟩

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

set_option maxHeartbeats 600000 in
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
  classical
  let r : ℕ := Nat.ceil (5 * (P + 4)) + 2
  let u : ℕ := 2 * Nat.ceil (100 * (r : ℝ) * (P + 4))
  let A : ℝ := (2 : ℝ) ^ u
  let c : ℝ := (2 : ℝ) ^ (-((u : ℝ) + 2))
  let C : ℝ := Real.exp A + A ^ 2 * Real.exp A + A
  let a : ℝ := 3 / (200 * (r : ℝ))
  have hr : 2 ≤ r := by dsimp [r]; omega
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hrLarge : 5 * (P + 4) ≤ (r : ℝ) := by
    have hh := Nat.le_ceil (5 * (P + 4))
    dsimp [r]
    push_cast
    linarith
  have huLarge : 200 * (r : ℝ) * (P + 4) ≤ (u : ℝ) := by
    have hh := Nat.le_ceil (100 * (r : ℝ) * (P + 4))
    dsimp [u]
    push_cast
    linarith
  have hu0 : 0 < u := by
    have hh : 0 < (u : ℝ) := lt_of_lt_of_le (by positivity) huLarge
    exact_mod_cast hh
  have huEven : Even u := ⟨Nat.ceil (100 * (r : ℝ) * (P + 4)), by dsimp [u]; omega⟩
  have ha0 : 0 < a := by dsimp [a]; positivity
  have hau : P + 2 ≤ a * u := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 200 * (r : ℝ))).mpr
    nlinarith
  have har : a * r = 3 / 200 := by dsimp [a]; field_simp
  have hmeanexp : 1 - (2 / 5 : ℝ) * r ≤ -P - 2 := by linarith
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hC0 : 0 < C := by dsimp [C]; positivity
  have hgap := OuterMoment_q_s11_outer.eventually_pow_gap (-P-2) (-P) (C/c)
    (by linarith) (div_pos hC0 hc0)
  have hbT : Tendsto (fun n : ℕ => bS n) atTop (nhds (0 : ℝ)) := by
    simpa [bS, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (19 : ℝ) / 20)).comp
        tendsto_natCast_atTop_atTop
  have hbSmall : ∀ᶠ n : ℕ in atTop, bS n ≤ 1 / 8 := by
    filter_upwards [hbT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/8))] with n hn
    exact hn.le
  obtain ⟨nC, hCev⟩ := hC u
  obtain ⟨nE, hEev⟩ := hE u (P+2)
  obtain ⟨nB, hnB⟩ := eventually_atTop.mp hbSmall
  obtain ⟨nG, hnG⟩ := eventually_atTop.mp hgap
  let n₀ := max 2 (max nC (max nE (max nB nG)))
  refine ⟨u, huEven, hu0, n₀, ?_⟩
  intro n hn N E X Y G π σ S hO
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnC : nC ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnE : nE ≤ n := by dsimp [n₀] at hn; omega
  have hnB' : nB ≤ n := by dsimp [n₀] at hn; omega
  have hnG' : nG ≤ n := by dsimp [n₀] at hn; omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hMean := hCev n hnC G π σ S hO
  have hTail := (hEev n hnE G π σ S hO u le_rfl).2
  let t : ℝ := (n : ℝ) ^ (-(103 : ℝ) / 100)
  let cap : ℝ := (n : ℝ) ^ (-(δ/4))
  let lam : ℝ := (n : ℝ) ^ a
  let d : ℕ := Fintype.card (OuterCoord n)
  have hdn : d ≤ n := by
    simpa [d] using Fintype.card_le_of_injective
      (fun j : OuterCoord n => j.1) Subtype.val_injective
  have hlam : 1 ≤ lam := by
    dsimp [lam]
    exact Real.one_le_rpow hn1 ha0.le
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hlamr : lam ^ r = (n : ℝ) ^ ((3 : ℝ)/200) := by
    dsimp [lam]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, har]
  have hscale : (n : ℝ) * lam ^ r * t ≤ 1 := by
    rw [hlamr]
    dsimp [t]
    have heq : (n : ℝ) * (n : ℝ) ^ ((3 : ℝ)/200) * (n : ℝ) ^ (-(103 : ℝ)/100) =
        (n : ℝ) ^ (-(3 : ℝ)/200) := by
      calc
        _ = (n : ℝ)^((1 : ℝ)) * (n : ℝ)^((3 : ℝ)/200) * (n : ℝ)^(-(103 : ℝ)/100) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]
          congr 1
          ring
    rw [heq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hlambda_decay : Real.exp A / lam ^ u ≤ Real.exp A * (n : ℝ) ^ (-P-2) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg A)
    change (lam ^ u)⁻¹ ≤ (n : ℝ) ^ (-P-2)
    have heq : (lam ^ u)⁻¹ = (n : ℝ) ^ (-(a * u)) := by
      rw [Real.rpow_neg hnpos.le, Real.rpow_mul hnpos.le, Real.rpow_natCast]
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hwt (f : Fin u → Fin N) : 0 ≤ tupWt σ f :=
    Finset.prod_nonneg (fun j _ => hO.sigma_nonneg (f j))
  have hsupport (f : Fin u → Fin N) (hf : tupWt σ f ≠ 0) (j : Fin u) : f j ∈ S := by
    exact hO.sigma_supp (f j) ((Finset.prod_ne_zero_iff.mp hf) j (Finset.mem_univ j))
  have hdeg (f : Fin u → Fin N) (hf : tupWt σ f ≠ 0) (j : Fin u) : deg E G π (f j) ≠ 0 := by
    have hm := hO.degree (f j) (hsupport f hf j)
    have heq := OuterMoment_sol_s11_range.sMean_eq_two_deg_sub_one E G π hO.pi_sum (f j)
    have hb := hnB n hnB'
    have hl := (abs_le.mp hm).1
    have hdpos : 0 < deg E G π (f j) := by linarith
    exact hdpos.ne'
  have hpoly (f : Fin u → Fin N) :
      phiU E G π d u f = OuterMoment_sol_s11_range.polyPhi u d (fun J => inter E G π J f) := by
    unfold phiU OuterMoment_sol_s11_range.polyPhi
    apply Finset.sum_congr rfl
    intro I _
    rw [OuterMoment_sol_s11_range.kernel_expansion]
  have hLowPoint (f : Fin u → Fin N) (hf : tupWt σ f ≠ 0) (hlow : env E G π f ≤ t) :
      |phiU E G π d u f| ≤ Real.exp A * (n : ℝ) ^ (-P-2) +
        A * n * Real.exp A * ∑ J : Finset (Fin u), if r ≤ J.card then |inter E G π J f| else 0 := by
    rw [hpoly]
    apply (OuterMoment_sol_s11_range.polyPhi_low_bound u d n r (fun J => inter E G π J f)
      t lam ht hlam (by omega) hdn (by simp [inter, hO.pi_sum]) ?_ hscale).trans
    · exact add_le_add hlambda_decay (le_refl _)
    · intro J hJ
      by_cases hc : 2 ≤ J.card
      · exact (OuterMoment_sol_s11_range.inter_le_env E G π f J hc).trans hlow
      · have hc1 : J.card = 1 := by
          have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ)
          omega
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hc1
        rw [OuterMoment_sol_s11_range.inter_singleton E G π hO.pi_sum f j (hdeg f hf j), abs_zero]
        exact ht
  have hMeanSum :
      (∑ f : Fin u → Fin N, tupWt σ f *
        ∑ J : Finset (Fin u), if r ≤ J.card then |inter E G π J f| else 0) ≤
        A * (n : ℝ) ^ (-(2/5 : ℝ) * r) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _J : Finset (Fin u), (n : ℝ) ^ (-(2/5 : ℝ) * r) := by
        apply Finset.sum_le_sum
        intro J _
        by_cases hJ : r ≤ J.card
        · simp only [if_pos hJ]
          exact (hMean J (by omega)).trans
            (Real.rpow_le_rpow_of_exponent_le hn1 (by
              have hj : (r : ℝ) ≤ J.card := by exact_mod_cast hJ
              linarith))
        · simp [hJ, Real.rpow_nonneg hnpos.le]
      _ = _ := by simp [A, Fintype.card_finset]
  have hLow :
      (∑ f : Fin u → Fin N, tupWt σ f * (if env E G π f ≤ t then |phiU E G π d u f| else 0)) ≤
      (Real.exp A + A ^ 2 * Real.exp A) * (n : ℝ) ^ (-P-2) := by
    have hpt (f : Fin u → Fin N) :
        tupWt σ f * (if env E G π f ≤ t then |phiU E G π d u f| else 0) ≤
        tupWt σ f * (Real.exp A * (n : ℝ) ^ (-P-2) + A * n * Real.exp A *
          ∑ J : Finset (Fin u), if r ≤ J.card then |inter E G π J f| else 0) := by
      by_cases hf : tupWt σ f = 0
      · simp [hf]
      by_cases hl : env E G π f ≤ t
      · simp only [if_pos hl]
        exact mul_le_mul_of_nonneg_left (hLowPoint f hf hl) (hwt f)
      · simp only [if_neg hl, mul_zero]
        exact mul_nonneg (hwt f) (add_nonneg (by positivity)
          (mul_nonneg (by positivity) (Finset.sum_nonneg (fun J _ => by split_ifs <;> positivity))))
    calc
      _ ≤ ∑ f : Fin u → Fin N, tupWt σ f * (Real.exp A * (n : ℝ) ^ (-P-2) +
          A * n * Real.exp A * ∑ J : Finset (Fin u), if r ≤ J.card then |inter E G π J f| else 0) :=
        Finset.sum_le_sum (fun f _ => hpt f)
      _ = Real.exp A * (n : ℝ) ^ (-P-2) + A * n * Real.exp A *
          (∑ f : Fin u → Fin N, tupWt σ f * ∑ J : Finset (Fin u),
            if r ≤ J.card then |inter E G π J f| else 0) := by
        calc
          _ = ∑ f : Fin u → Fin N, (Real.exp A * (n : ℝ)^(-P-2) * tupWt σ f +
              (A*n*Real.exp A) * (tupWt σ f * ∑ J : Finset (Fin u), if r ≤ J.card then |inter E G π J f| else 0)) := by
            apply Finset.sum_congr rfl
            intro f _
            ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              OuterMoment_sol_s11_range.tuple_weight_sum σ hO.sigma_sum, mul_one]
      _ ≤ Real.exp A * (n : ℝ) ^ (-P-2) + A * n * Real.exp A * (A * (n : ℝ) ^ (-(2/5 : ℝ) * r)) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hMeanSum (by positivity))
      _ = Real.exp A * (n : ℝ) ^ (-P-2) + A ^ 2 * Real.exp A * (n : ℝ) ^ (1-(2/5 : ℝ)*r) := by
        have heq : (n : ℝ) * (n : ℝ)^(-(2/5 : ℝ)*r) = (n : ℝ)^(1-(2/5 : ℝ)*r) := by
          calc
            _ = (n : ℝ)^(1 : ℝ) * (n : ℝ)^(-(2/5 : ℝ)*r) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; ring
        rw [← heq]
        ring
      _ ≤ _ := by
        have hh := Real.rpow_le_rpow_of_exponent_le hn1 hmeanexp
        nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ A^2*Real.exp A)]
  have hMiddle :
      (∑ f : Fin u → Fin N, tupWt σ f *
        (if t < env E G π f ∧ env E G π f ≤ cap then |phiU E G π d u f| else 0)) ≤
        A * (n : ℝ) ^ (-P-2) := by
    calc
      _ ≤ ∑ f : Fin u → Fin N, A * (tupWt σ f *
        (if t < env E G π f ∧ env E G π f ≤ cap then Real.exp (A*n*env E G π f) else 0)) := by
          apply Finset.sum_le_sum
          intro f _
          by_cases hf : tupWt σ f = 0
          · simp [hf]
          split_ifs with he
          · have hh := OuterMoment_sol_s11_range.phi_abs_le_exp E G π hO.pi_sum f (hdeg f hf) hdn
            simpa [A, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hh (hwt f)
          · simp
      _ = A * (∑ f : Fin u → Fin N, tupWt σ f *
          (if t < env E G π f ∧ env E G π f ≤ cap then Real.exp (A*n*env E G π f) else 0)) := by rw [Finset.mul_sum]
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_left hTail hA0.le using 1 <;> congr 2 <;> ring
  have hsplit (f : Fin u → Fin N) :
      (if env E G π f ≤ cap then |phiU E G π d u f| else 0) ≤
      (if env E G π f ≤ t then |phiU E G π d u f| else 0) +
      (if t < env E G π f ∧ env E G π f ≤ cap then |phiU E G π d u f| else 0) := by
    by_cases hc : env E G π f ≤ cap
    · by_cases ht : env E G π f ≤ t
      · simp only [if_pos hc, if_pos ht, not_lt_of_ge ht, false_and, if_false, add_zero, le_refl]
      · simp only [if_pos hc, if_neg ht, lt_of_not_ge ht, true_and, if_true, zero_add, le_refl]
    · simp only [if_neg hc]
      split_ifs <;> linarith [abs_nonneg (phiU E G π d u f)]
  unfold SmallRange
  change (∑ f : Fin u → Fin N, tupWt σ f *
    (if env E G π f ≤ cap then |phiU E G π d u f| else 0)) ≤ c * (n : ℝ) ^ (-P)
  calc
    _ ≤ (∑ f : Fin u → Fin N, tupWt σ f * (if env E G π f ≤ t then |phiU E G π d u f| else 0)) +
        ∑ f : Fin u → Fin N, tupWt σ f *
          (if t < env E G π f ∧ env E G π f ≤ cap then |phiU E G π d u f| else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro f _
      simpa [mul_add] using mul_le_mul_of_nonneg_left (hsplit f) (hwt f)
    _ ≤ (Real.exp A + A^2*Real.exp A) * (n : ℝ) ^ (-P-2) + A*(n : ℝ)^(-P-2) := add_le_add hLow hMiddle
    _ = C * (n : ℝ) ^ (-P-2) := by dsimp [C]; ring
    _ ≤ c * (n : ℝ) ^ (-P) := by
      have hh := hnG n hnG'
      have hh' : C * (n : ℝ)^(-P-2) / c < (n : ℝ)^(-P) := by
        simpa [div_mul_eq_mul_div] using hh
      exact le_of_lt (by simpa only [mul_comm] using (div_lt_iff₀ hc0).mp hh')

open OuterMoment_sol_s11_range in
set_option maxHeartbeats 800000 in
/-- L11.3g (11:311–327).  For a tuple with `w > n^{-υ}` fix a maximal retained set `R` (all interactions within `R`
at most `n^{-υ}`); each omitted coordinate lies in `B_R`, `|B_R| ≤ 2^u e^{n^.03}` (counting large extensions),
and costs `|B_R| max σ max_x D_x^{-d} ≤ (2^n/N) exp(-.5gh + O(n^.05) + n^.03 + O_u(1)) = n^{-ω(1)}`; the retained
positive product has bounded integral (exponential weights at length `|R| < u`). -/
theorem large_range (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hD : CountExtEv δ x₀ K) (hE : ModerateEv δ x₀ K) (u : ℕ) (P : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
      (π σ : Fin N → ℝ) (S : Finset (Fin N)),
      OuterHyp δ x₀ K n N E X Y G π σ S → LargeRange E G π σ (Fintype.card (OuterCoord n)) n δ P u := by
  classical
  let A : ℝ := (2 : ℝ)^u
  let c : ℝ := (2 : ℝ)^(-((u : ℝ)+2))
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨nD, hDev⟩ := hD u
  obtain ⟨nE, hEev⟩ := hE u 0
  have hbT : Tendsto (fun n : ℕ => bS n) atTop (nhds (0 : ℝ)) := by
    simpa [bS, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<(19 : ℝ)/20)).comp
        tendsto_natCast_atTop_atTop
  have hbSmall : ∀ᶠ n : ℕ in atTop, bS n ≤ 1/8 := by
    filter_upwards [hbT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/8))] with n hn
    exact hn.le
  obtain ⟨nB, hnB⟩ := eventually_atTop.mp hbSmall
  obtain ⟨nQ, hnQ⟩ := eventually_atTop.mp (eventually_extension_charge A 0 hA)
  obtain ⟨nF, hnF⟩ := eventually_atTop.mp (eventually_extension_charge
    (A^3*(Real.exp A+1)/c) P (by positivity))
  let n₀ := 2+nD+nE+nB+nQ+nF
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G π σ S hO
  have hn2 : 2 ≤ n := by dsimp [n₀] at hn; omega
  have hnD : nD ≤ n := by dsimp [n₀] at hn; omega
  have hnE : nE ≤ n := by dsimp [n₀] at hn; omega
  have hnB' : nB ≤ n := by dsimp [n₀] at hn; omega
  have hnQ' : nQ ≤ n := by dsimp [n₀] at hn; omega
  have hnF' : nF ≤ n := by dsimp [n₀] at hn; omega
  have hCount := hDev n hnD G π σ S hO
  have hMod := hEev n hnE G π σ S hO
  let cap : ℝ := (n : ℝ)^(-(δ/4))
  let d : ℕ := Fintype.card (OuterCoord n)
  let echarge : ℝ := -gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n + (n : ℝ)^((3 : ℝ)/100)
  let q : ℝ := A*Real.exp echarge
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by simpa [q, echarge] using hnQ n hnQ'
  have hdn : d ≤ n := by
    simpa [d] using Fintype.card_le_of_injective (fun j : OuterCoord n => j.1) Subtype.val_injective
  have hcap0 : 0 ≤ cap := by dsimp [cap]; positivity
  have hdeg0 (y : Fin N) : 0 ≤ deg E G π y :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hO.pi_nonneg z) (by unfold hit; split_ifs <;> norm_num))
  have hwt (f : Fin u → Fin N) : 0 ≤ tupWt σ f :=
    Finset.prod_nonneg (fun j _ => hO.sigma_nonneg (f j))
  have hsupport (f : Fin u → Fin N) (hf : tupWt σ f ≠ 0) (j : Fin u) : f j ∈ S :=
    hO.sigma_supp (f j) ((Finset.prod_ne_zero_iff.mp hf) j (Finset.mem_univ j))
  have hdeg (f : Fin u → Fin N) (hf : tupWt σ f ≠ 0) (j : Fin u) : 0 < deg E G π (f j) :=
    (inverse_degree_le E G π hO.pi_sum (bS n) (by unfold bS; positivity)
      (hnB n hnB') (f j) (hO.degree (f j) (hsupport f hf j))).1
  have hs0 : ∃ x : Fin N, σ x ≠ 0 := by
    by_contra h
    push Not at h
    have hs := hO.sigma_sum
    simp [h] at hs
  obtain ⟨s0, hs0⟩ := hs0
  have hs0S : s0 ∈ S := hO.sigma_supp s0 hs0
  let base (R : Finset (Fin u)) (z : R → Fin N) : Fin u → Fin N :=
    fun j => if hj : j ∈ R then z ⟨j,hj⟩ else s0
  let BR (R : Finset (Fin u)) (z : R → Fin N) (i : Fin u) : Finset (Fin N) :=
    S.filter fun y => ∃ J ∈ R.powerset, cap < |inter E G π (insert i J) (Function.update (base R z) i y)|
  let B (R : Finset (Fin u)) (z : R → Fin N) (i : {j : Fin u // j ∉ R}) (y : Fin N) : ℝ :=
    if y ∈ BR R z i then ((deg E G π y)⁻¹)^d else 0
  let H (R : Finset (Fin u)) (z : R → Fin N) : ℝ :=
    if env E G π (retainedTuple R z) ≤ cap then
      Real.exp ((2 : ℝ)^R.card*n*env E G π (retainedTuple R z)) else 0
  have hB0 (R : Finset (Fin u)) (z : R → Fin N) (i : {j : Fin u // j ∉ R}) (y : Fin N) :
      0 ≤ B R z i y := by
    dsimp [B]
    split_ifs
    · exact pow_nonneg (inv_nonneg.mpr (hdeg0 y)) d
    · exact le_refl 0
  have hH0 (R : Finset (Fin u)) (z : R → Fin N) : 0 ≤ H R z := by dsimp [H]; split_ifs <;> positivity
  have hAtom (y : Fin N) (hy : y ∈ S) :
      σ y*((deg E G π y)⁻¹)^d ≤ Real.exp (-gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n) :=
    sigma_charged_atom E G π σ hO.pi_sum hO.sigma_nonneg hO.host (hnB n hnB')
      hO.sigma_cap y (hO.degree y hy)
  have hBSum (R : Finset (Fin u)) (z : R → Fin N) (hz : (∏ j : R, σ (z j)) ≠ 0)
      (i : {j : Fin u // j ∉ R}) : (∑ y, σ y*B R z i y) ≤ q := by
    have hzS (j : R) : z j ∈ S :=
      hO.sigma_supp (z j) ((Finset.prod_ne_zero_iff.mp hz) j (Finset.mem_univ j))
    have hbS : ∀ j, base R z j ∈ S := by
      intro j
      dsimp [base]
      split_ifs with hj
      · exact hzS ⟨j,hj⟩
      · exact hs0S
    have hcard : ((BR R z i).card : ℝ) ≤ A*Real.exp ((n : ℝ)^((3 : ℝ)/100)) :=
      extension_union_card S cap (Real.exp ((n : ℝ)^((3 : ℝ)/100)))
        (fun J f => inter E G π J f) hCount (base R z) hbS R i
    change (∑ y, σ y*(if y ∈ BR R z i then ((deg E G π y)⁻¹)^d else 0)) ≤ q
    simp_rw [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun y => y ∈ BR R z i) = BR R z i := by ext y; simp
    rw [hfilter]
    calc
      _ ≤ ∑ _y ∈ BR R z i, Real.exp (-gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n) :=
        Finset.sum_le_sum (fun y hy => hAtom y (Finset.mem_filter.mp hy).1)
      _ = ((BR R z i).card : ℝ)*Real.exp (-gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n) := by simp
      _ ≤ (A*Real.exp ((n : ℝ)^((3 : ℝ)/100)))*
          Real.exp (-gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = q := by
        dsimp [q, echarge]
        rw [Real.exp_add (-gS n*Fintype.card (InnerCoord n)/2 + 8*(n : ℝ)*bS n)
          ((n : ℝ)^((3 : ℝ)/100))]
        ring
  have hRetainedIntegral (R : Finset (Fin u)) :
      (∑ z : R → Fin N, (∏ j : R, σ (z j))*H R z) ≤ Real.exp A+1 := by
    have hRcard : R.card ≤ u := by simpa using Finset.card_le_univ R
    have hMR := (hMod R.card hRcard).1
    change (∑ z : R → Fin N, (∏ j : R, σ (z j))*
      (if env E G π (retainedTuple R z) ≤ cap then
        Real.exp ((2 : ℝ)^R.card*n*env E G π (retainedTuple R z)) else 0)) ≤ _
    rw [retained_sum_eq σ R (fun f : Fin R.card → Fin N => if env E G π f ≤ cap then
      Real.exp ((2 : ℝ)^R.card*n*env E G π f) else 0)]
    have hpower : (2 : ℝ)^R.card ≤ A := pow_le_pow_right₀ (by norm_num) hRcard
    exact hMR.trans (add_le_add (Real.exp_le_exp.mpr hpower) (le_refl 1))
  let F (R : Finset (Fin u)) (f : Fin u → Fin N) : ℝ :=
    H R (fun j => f j) * ∏ i : {j : Fin u // j ∉ R}, B R (fun j => f j) i (f i)
  have hF0 (R : Finset (Fin u)) (f : Fin u → Fin N) : 0 ≤ F R f := by
    change 0 ≤ H R (fun j => f j) *
      ∏ i : {j : Fin u // j ∉ R}, B R (fun j => f j) i (f i)
    exact mul_nonneg (hH0 R (fun j => f j))
      (Finset.prod_nonneg (fun (i : {j : Fin u // j ∉ R}) _ => hB0 R (fun j => f j) i (f i)))
  have hRIntegral (R : Finset (Fin u)) (hR : R ≠ Finset.univ) :
      (∑ f : Fin u → Fin N, tupWt σ f*F R f) ≤ (Real.exp A+1)*q := by
    have hnonempty : Nonempty {j : Fin u // j ∉ R} := by
      have hh : ¬ Finset.univ ⊆ R := fun h => hR (Finset.Subset.antisymm (Finset.subset_univ R) h)
      obtain ⟨j, _, hj⟩ := Finset.not_subset.mp hh
      exact ⟨⟨j,hj⟩⟩
    have hcardpos : 0 < Fintype.card {j : Fin u // j ∉ R} := Fintype.card_pos_iff.mpr hnonempty
    have hprod (z : R → Fin N) (hz : (∏ j : R, σ (z j)) ≠ 0) :
        (∏ i : {j : Fin u // j ∉ R}, ∑ y, σ y*B R z i y) ≤ q := by
      calc
        _ ≤ ∏ _i : {j : Fin u // j ∉ R}, q := Finset.prod_le_prod₀
          (fun i _ => Finset.sum_nonneg (fun y _ => mul_nonneg (hO.sigma_nonneg y) (hB0 R z i y)))
          (fun i _ => hBSum R z hz i)
        _ = q^Fintype.card {j : Fin u // j ∉ R} := by simp
        _ ≤ q := pow_le_of_le_one hq0 hq1 (by omega)
    change (∑ f : Fin u → Fin N, tupWt σ f * (H R (fun j => f j)*
      ∏ i : {j : Fin u // j ∉ R}, B R (fun j => f j) i (f i))) ≤ _
    simp_rw [← mul_assoc]
    rw [split_weight_integral σ R (H R) (B R)]
    calc
      _ ≤ ∑ z : R → Fin N, ((∏ j : R, σ (z j))*H R z)*q := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : (∏ j : R, σ (z j)) = 0
        · simp only [hz, zero_mul, le_refl]
        · exact mul_le_mul_of_nonneg_left (hprod z hz)
            (mul_nonneg (Finset.prod_nonneg (fun j _ => hO.sigma_nonneg (z j))) (hH0 R z))
      _ = (∑ z : R → Fin N, (∏ j : R, σ (z j))*H R z)*q := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hRetainedIntegral R) hq0
  have hPoint (f : Fin u → Fin N) :
      tupWt σ f*(if cap < env E G π f then |phiU E G π d u f| else 0) ≤
      A*tupWt σ f * ∑ R : Finset (Fin u), if R ≠ Finset.univ then F R f else 0 := by
    have hsum0 : 0 ≤ ∑ R : Finset (Fin u), if R ≠ Finset.univ then F R f else 0 :=
      Finset.sum_nonneg (fun R _ => by split_ifs; exact hF0 R f; exact le_refl 0)
    by_cases hf : tupWt σ f = 0
    · simp [hf]
    by_cases hh : cap < env E G π f
    · have hlarge : ∃ J : Finset (Fin u), 2 ≤ J.card ∧ cap < |inter E G π J f| := by
        by_contra h
        have he : env E G π f ≤ cap := by
          unfold env
          apply Finset.sup'_le
          intro J _
          split_ifs with hcJ
          · exact le_of_not_gt (fun hJ => h ⟨J,hcJ,hJ⟩)
          · exact hcap0
        exact (not_le_of_gt hh) he
      obtain ⟨R,hR,hgood,hext⟩ := maximal_retained (fun J => inter E G π J f) cap hlarge
      have henv := env_retained_le E G π R f cap hcap0 hgood
      have hBmem (i : {j : Fin u // j ∉ R}) : f i ∈ BR R (fun j => f j) i := by
        obtain ⟨J,hJ,hv⟩ := hext i i.property
        refine Finset.mem_filter.mpr ⟨hsupport f hf i, J, hJ, ?_⟩
        have heq : inter E G π (insert (i : Fin u) J)
            (Function.update (base R (fun j => f j)) i (f i)) = inter E G π (insert (i : Fin u) J) f := by
          apply inter_congr
          intro j hj
          obtain rfl | hjJ := Finset.mem_insert.mp hj
          · simp
          · have hjR := Finset.mem_powerset.mp hJ hjJ
            have hji : j ≠ (i : Fin u) := by intro he; exact i.property (he ▸ hjR)
            simp [Function.update_of_ne hji, base, hjR]
        simpa [heq] using hv
      have hFR : F R f = Real.exp ((2 : ℝ)^R.card*n*env E G π (retainedTuple R (fun j => f j))) *
          ∏ j ∈ Rᶜ, ((deg E G π (f j))⁻¹)^d := by
        dsimp [F]
        rw [show H R (fun j => f j) = Real.exp ((2 : ℝ)^R.card*n*env E G π (retainedTuple R (fun j => f j))) by
          simp [H, henv]]
        congr 1
        have hprod : (∏ i : {j : Fin u // j ∉ R}, B R (fun j => f j) i (f i)) =
            ∏ i : {j : Fin u // j ∉ R}, ((deg E G π (f i))⁻¹)^d := by
          apply Finset.prod_congr rfl
          intro i _
          simp [B, hBmem i]
        rw [hprod]
        exact (Finset.prod_subtype (p := fun j : Fin u => j ∉ R) Rᶜ (fun j => Finset.mem_compl)
          (fun j => ((deg E G π (f j))⁻¹)^d)).symm
      have hp : |phiU E G π d u f| ≤ A*F R f := by
        rw [hFR]
        simpa [A, mul_assoc] using phi_retained_le E G π hO.pi_nonneg hO.pi_sum R f (hdeg f hf) hdn
      have hsum : F R f ≤ ∑ R : Finset (Fin u), if R ≠ Finset.univ then F R f else 0 := by
        have hs : (if R ≠ Finset.univ then F R f else 0) ≤
            ∑ R : Finset (Fin u), if R ≠ Finset.univ then F R f else 0 :=
          Finset.single_le_sum (f := fun T : Finset (Fin u) => if T ≠ Finset.univ then F T f else 0)
            (fun T _ => by split_ifs; exact hF0 T f; exact le_refl 0) (Finset.mem_univ R)
        simpa only [if_pos hR] using hs
      rw [if_pos hh]
      have hpp := hp.trans (mul_le_mul_of_nonneg_left hsum hA.le)
      simpa [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left hpp (hwt f)
    · rw [if_neg hh, mul_zero]
      exact mul_nonneg (mul_nonneg hA.le (hwt f)) hsum0
  unfold LargeRange
  change (∑ f : Fin u → Fin N, tupWt σ f*(if cap < env E G π f then |phiU E G π d u f| else 0)) ≤ c*(n : ℝ)^(-P)
  calc
    _ ≤ ∑ f : Fin u → Fin N, A*tupWt σ f* ∑ R : Finset (Fin u), if R ≠ Finset.univ then F R f else 0 :=
      Finset.sum_le_sum (fun f _ => hPoint f)
    _ = A*∑ R : Finset (Fin u), ∑ f : Fin u → Fin N, tupWt σ f*(if R ≠ Finset.univ then F R f else 0) := by
      simp_rw [mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ A*∑ _R : Finset (Fin u), (Real.exp A+1)*q := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Finset.sum_le_sum
      intro R _
      by_cases hR : R ≠ Finset.univ
      · simpa only [if_pos hR] using hRIntegral R hR
      · simp only [if_neg hR, mul_zero, Finset.sum_const_zero]
        positivity
    _ = A^3*(Real.exp A+1)*Real.exp echarge := by simp [Fintype.card_finset, q, A]; ring
    _ ≤ c*(n : ℝ)^(-P) := by
      have hh := hnF n hnF'
      have hh' : (A^3*(Real.exp A+1)*Real.exp echarge)/c ≤ (n : ℝ)^(-P) := by
        simpa [echarge, div_mul_eq_mul_div] using hh
      simpa only [mul_comm] using (div_le_iff₀ hc).mp hh'

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
