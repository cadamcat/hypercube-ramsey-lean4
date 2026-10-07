import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S07.Profiles
import HypercubeRamsey.Tools.Ramsey
import HypercubeRamsey.S11.Core.Compatibility_q_s11_compat

/-!
# Lemma 11.2: a compatible balanced profile

Source: `sections/11-…tex`, lines 103–161 (L11.2, L11.2a–c in `research/blueprint/PART-B.md` §3.11).  The lemma is
stated for any menu with odd mean rows `π_i` (laws on `supp ν_i` of width `.02n`) and even mean rows `α_i`
(subprobabilities on `supp μ_i`); the proof of Proposition 11.1 applies it to the rows of the slice experiment.
The balance constant is `K = 16/κ`, fixed before the discard tolerance (thin spot TS-B6).
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

/-- L11.2a(i)'s conclusion: few signed degree outliers against a broad second law. -/
def SignedOutliersEv (δ x₀ K : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
    (π : Fin N → ℝ),
    1 ≤ N → (∀ y, 0 ≤ π y) → (∑ y, π y = 1) → (∀ y, π y ≠ 0 → y ∈ Y) → (∀ y, (N : ℝ) * π y ≤ K) →
    DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - δ / 16)) ((n : ℝ) ^ x₀) ((n : ℝ) ^ (-(19 : ℝ) / 20)) →
    ((X.filter fun x => 4 * bS n < |sMean E G π x|).card : ℝ) <
      2 * N * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16)))

/-- L11.2a(ii)'s conclusion: removing fewer than `N e^{-n^δ}` labels kills every correlation clique. -/
def CliqueRemovalEv (δ K : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
    (π : Fin N → ℝ),
    1 ≤ N → (∀ y, 0 ≤ π y) → (∑ y, π y = 1) → (∀ y, π y ≠ 0 → y ∈ Y) → (∀ y, (N : ℝ) * π y ≤ K) →
    ClusterAbsYX n N E X Y δ →
    ∀ S ⊆ X, (∀ x ∈ S, |sMean E G π x| ≤ 4 * bS n) →
      ∃ V ⊆ S, (V.card : ℝ) < N * Real.exp (-((n : ℝ) ^ δ)) ∧ NoClique E G π n δ (S \ V)

/-- L11.2b's conclusion: few good-degree labels see profile mass above `η` on high-degree tags. -/
def HighDegreeEv (δ K : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
    {ι : Type} [Fintype ι] (π : ι → Fin N → ℝ) (p : FinProb ι),
    2 ^ n ≤ N → (∀ i y, 0 ≤ π i y) → (∀ i, ∑ y, π i y = 1) → (∀ i y, π i y ≠ 0 → y ∈ Y) →
    (∀ i y, (N : ℝ) * π i y ≤ Real.exp ((n : ℝ) / 50)) → (∀ y, (N : ℝ) * mixW p π y ≤ K) →
    ClusterAbsXY n N E X Y δ →
    ((X.filter fun x => |sMean E G (mixW p π) x| ≤ 4 * bS n ∧
        etaC < ∑ i ∈ Finset.univ.filter (fun i => (4 / 5 : ℝ) < deg E G (π i) x), p.w i).card : ℝ) <
      N * Real.exp (-((n : ℝ) ^ δ))

/-- The discard step's conclusion (11:118, 161): for every balanced input profile, some set of at most `κN/4`
first-side labels is such that every tag whose first support avoids it is compatible with the input. -/
def DiscardEv (δ x₀ K κ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
    {ι : Type} [Fintype ι] (μ ν : ι → Law N) (π α : ι → Fin N → ℝ) (p : FinProb ι),
    ProfileInput n N E X Y κ μ ν π α → (∀ y, (N : ℝ) * mixW p π y ≤ K) →
    DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - δ / 16)) ((n : ℝ) ^ x₀) ((n : ℝ) ^ (-(19 : ℝ) / 20)) →
    ClusterAbsXY n N E X Y δ → ClusterAbsYX n N E X Y δ →
    ∃ D : Finset (Fin N), (D.card : ℝ) ≤ κ / 4 * N ∧
      ∀ i, (∀ x ∈ D, (μ i).w x = 0) → CompatTag E G n δ μ π p i

/-- L11.2a(i) (11:119–120).  If the labels of `X` with `m_x > 4b_*` (or `< -4b_*`) numbered at least
`N e^{-n^{1-υ/4}}`, their uniform law (width `≤ n^{1-δ/16}`) against `π` (width `log K ≤ n^{x₀}`) would have
`|d_G - 1/2| = |avg m_x|/2 > b_*`, contradicting (11.1). -/
theorem signed_outliers (δ x₀ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) : SignedOutliersEv δ x₀ K := by
  classical
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ x₀) Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hx₀).comp tendsto_natCast_atTop_atTop
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp ((n : ℝ) ^ x₀)) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hpow
  have hKevent : ∀ᶠ n : ℕ in Filter.atTop, K ≤ Real.exp ((n : ℝ) ^ x₀) :=
    hexp.eventually (Filter.eventually_ge_atTop K)
  obtain ⟨nK, hKeventN⟩ := Filter.eventually_atTop.1 hKevent
  refine ⟨max nK 1, ?_⟩
  intro n hn N E X Y G π hN hπ0 hπsum hπsupp hπcap hdisc
  have hnK' : nK ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnKexp : K ≤ Real.exp ((n : ℝ) ^ x₀) := hKeventN n hnK'
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  let πlaw : Law N := ⟨π, hπ0, hπsum⟩
  have hπwidth : πlaw.WidthLE ((n : ℝ) ^ x₀) := by
    intro y
    change π y ≤ Real.exp ((n : ℝ) ^ x₀) / N
    apply (le_div_iff₀ hNr).2
    calc
      π y * (N : ℝ) = (N : ℝ) * π y := by ring
      _ ≤ K := hπcap y
      _ ≤ Real.exp ((n : ℝ) ^ x₀) := hnKexp
  let O : Finset (Fin N) := X.filter fun x => 4 * bS n < |sMean E G π x|
  let Opos : Finset (Fin N) := X.filter fun x => 4 * bS n < sMean E G π x
  let Oneg : Finset (Fin N) := X.filter fun x => 4 * bS n < -sMean E G π x
  have hcover : O ⊆ Opos ∪ Oneg := by
    intro x hx
    simp only [O, Finset.mem_filter] at hx
    rcases hx with ⟨hxX, hout⟩
    change x ∈ Opos ∪ Oneg
    rw [Finset.mem_union]
    by_cases hsign : 0 ≤ sMean E G π x
    · left
      simp only [Opos, Finset.mem_filter]
      exact ⟨hxX, by simpa [abs_of_nonneg hsign] using hout⟩
    · right
      have hneg : sMean E G π x < 0 := lt_of_not_ge hsign
      simp only [Oneg, Finset.mem_filter]
      exact ⟨hxX, by simpa [abs_of_neg hneg] using hout⟩
  have hcardCover : (O.card : ℝ) ≤ (Opos.card : ℝ) + (Oneg.card : ℝ) := by
    calc
      (O.card : ℝ) ≤ ((Opos ∪ Oneg).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
      _ ≤ (Opos.card : ℝ) + (Oneg.card : ℝ) := by
        exact_mod_cast (Finset.card_union_le Opos Oneg)
  have hmeanIdentity (μ : Law N) :
      (∑ x, μ.w x * sMean E G π x) = 2 * dens E G μ πlaw - 1 := by
    have hrow (x : Fin N) : sMean E G π x =
        2 * (∑ y, π y * hit E G x y) - 1 := by
      unfold sMean fv
      calc
        (∑ y, π y * (2 * hit E G x y - 1)) =
            ∑ y, (2 * (π y * hit E G x y) - π y) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = 2 * (∑ y, π y * hit E G x y) - ∑ y, π y := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = 2 * (∑ y, π y * hit E G x y) - 1 := by rw [hπsum]
    have hdens (x : Fin N) :
        (∑ y, μ.w x * πlaw.w y * (if Hits E G x y then (1 : ℝ) else 0)) =
          μ.w x * (∑ y, π y * hit E G x y) := by
      calc
        (∑ y, μ.w x * πlaw.w y * (if Hits E G x y then (1 : ℝ) else 0)) =
            ∑ y, μ.w x * (π y * hit E G x y) := by
              apply Finset.sum_congr rfl
              intro y hy
              simp [πlaw, hit]
        _ = μ.w x * (∑ y, π y * hit E G x y) := by rw [Finset.mul_sum]
    have hdens' : dens E G μ πlaw =
        ∑ x, μ.w x * (∑ y, π y * hit E G x y) := by
      unfold dens
      apply Finset.sum_congr rfl
      intro x hx
      exact hdens x
    calc
      (∑ x, μ.w x * sMean E G π x) =
          ∑ x, μ.w x * (2 * (∑ y, π y * hit E G x y) - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hrow x]
      _ = 2 * (∑ x, μ.w x * (∑ y, π y * hit E G x y)) - 1 := by
            calc
              _ = ∑ x, (2 * (μ.w x * (∑ y, π y * hit E G x y)) - μ.w x) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    ring
              _ = 2 * (∑ x, μ.w x * (∑ y, π y * hit E G x y)) - ∑ x, μ.w x := by
                    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              _ = _ := by rw [μ.sum_eq_one]
      _ = 2 * dens E G μ πlaw - 1 := by rw [hdens']
  have hnoSet (positive : Bool) (U : Finset (Fin N)) (hUsub : U ⊆ X)
      (hU : ∀ x ∈ U, if positive then 4 * bS n < sMean E G π x
        else 4 * bS n < -sMean E G π x)
      (hUlarge : (N : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) ≤ U.card) : False := by
    let T : ℝ := (n : ℝ) ^ ((1 : ℝ) - δ / 16)
    have hUcardPos : 0 < (U.card : ℝ) :=
      lt_of_lt_of_le (mul_pos hNr (Real.exp_pos _)) hUlarge
    have hUne : U.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero (by
      intro hzero
      simp [hzero] at hUcardPos))
    let μ : Law N := Law.unif U hUne
    have hμX : μ.SupportedIn X := by
      intro x hx
      have hxU : x ∉ U := fun hxU => hx (hUsub hxU)
      simp [μ, Law.unif, FinProb.uniform, hxU]
    have hμwidth : μ.WidthLE T := by
      intro x
      change (if x ∈ U then (U.card : ℝ)⁻¹ else 0) ≤ Real.exp T / N
      by_cases hx : x ∈ U
      · rw [if_pos hx]
        have hcardMul : (N : ℝ) ≤ (U.card : ℝ) * Real.exp T := by
          calc
            (N : ℝ) = (N : ℝ) * 1 := by ring
            _ = (N : ℝ) * (Real.exp (-T) * Real.exp T) := by
              rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
            _ = ((N : ℝ) * Real.exp (-T)) * Real.exp T := by ring
            _ ≤ (U.card : ℝ) * Real.exp T :=
              mul_le_mul_of_nonneg_right (by simpa [T] using hUlarge) (le_of_lt (Real.exp_pos T))
        rw [show (U.card : ℝ)⁻¹ = (1 : ℝ) / (U.card : ℝ) by ring]
        rw [div_le_div_iff₀ hUcardPos hNr]
        nlinarith [hcardMul]
      · rw [if_neg hx]
        positivity
    have hμpos (x : Fin N) (hx : x ∈ U) : 0 < μ.w x := by
      simpa [μ, Law.unif, FinProb.uniform, hx] using (inv_pos.mpr hUcardPos)
    have hmeanPos : 0 < bS n := by
      dsimp [bS]
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn1) _
    have hsumConst : (∑ x, μ.w x * (4 * bS n)) = 4 * bS n := by
      rw [← Finset.sum_mul, μ.sum_eq_one]
      ring
    have hsumAbs : 4 * bS n < |∑ x, μ.w x * sMean E G π x| := by
      by_cases hp : positive
      · have hsumlt :
            (∑ x, μ.w x * (4 * bS n)) < ∑ x, μ.w x * sMean E G π x := by
          apply Finset.sum_lt_sum
          · intro x hx
            by_cases hxU : x ∈ U
            · have hpoint := hU x hxU
              simp [hp] at hpoint
              exact (mul_lt_mul_of_pos_left hpoint (hμpos x hxU)).le
            · have hμzero : μ.w x = 0 := by
                simp [μ, Law.unif, FinProb.uniform, hxU]
              simp [hμzero]
          · obtain ⟨x, hx⟩ := hUne
            refine ⟨x, Finset.mem_univ _, ?_⟩
            have hpoint := hU x hx
            simp [hp] at hpoint
            exact mul_lt_mul_of_pos_left hpoint (hμpos x hx)
        have hsumgt : 4 * bS n < ∑ x, μ.w x * sMean E G π x := by
          rw [← hsumConst]
          exact hsumlt
        rw [abs_of_pos (lt_trans (by positivity) hsumgt)]
        exact hsumgt
      · have hsumgt :
            (∑ x, μ.w x * (-4 * bS n)) > ∑ x, μ.w x * sMean E G π x := by
          apply Finset.sum_lt_sum
          · intro x hx
            by_cases hxU : x ∈ U
            · have hpoint := hU x hxU
              simp [hp] at hpoint
              have hpoint' : sMean E G π x < -4 * bS n := by linarith
              exact (mul_lt_mul_of_pos_left hpoint' (hμpos x hxU)).le
            · have hμzero : μ.w x = 0 := by
                simp [μ, Law.unif, FinProb.uniform, hxU]
              simp [hμzero]
          · obtain ⟨x, hx⟩ := hUne
            refine ⟨x, Finset.mem_univ _, ?_⟩
            have hpoint := hU x hx
            simp [hp] at hpoint
            have hpoint' : sMean E G π x < -4 * bS n := by linarith
            exact mul_lt_mul_of_pos_left hpoint' (hμpos x hx)
        have hsumConstNeg : (∑ x, μ.w x * (-4 * bS n)) = -4 * bS n := by
          rw [← Finset.sum_mul, μ.sum_eq_one]
          ring
        have hsumlt' : ∑ x, μ.w x * sMean E G π x < -4 * bS n := by
          rw [← hsumConstNeg]
          exact hsumgt
        have hsumNeg : ∑ x, μ.w x * sMean E G π x < 0 := by linarith
        rw [abs_of_neg hsumNeg]
        linarith
    have hπlawY : πlaw.SupportedIn Y := by
      intro y hy
      by_contra hne
      exact hy (hπsupp y (by simpa [πlaw] using hne))
    have hdisc' : |dens E G μ πlaw - 1 / 2| ≤ bS n := by
      simpa [bS] using hdisc μ πlaw hμX hπlawY hμwidth hπwidth G
    have hmeanBound : |∑ x, μ.w x * sMean E G π x| ≤ 2 * bS n := by
      rw [hmeanIdentity]
      have hrewrite : 2 * dens E G μ πlaw - 1 = 2 * (dens E G μ πlaw - 1 / 2) := by ring
      rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left hdisc' (by norm_num)
    nlinarith [hmeanPos, hsumAbs, hmeanBound]
  by_contra hnot
  have hlarge : 2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) ≤ O.card :=
    le_of_not_gt hnot
  let T : ℝ := (n : ℝ) ^ ((1 : ℝ) - δ / 16)
  have hq : 0 < (N : ℝ) * Real.exp (-T) := mul_pos hNr (Real.exp_pos _)
  have hsumlarge : 2 * ((N : ℝ) * Real.exp (-T)) ≤ (Opos.card : ℝ) + (Oneg.card : ℝ) := by
    dsimp [T] at hlarge ⊢
    nlinarith [hlarge, hcardCover]
  rcases le_total ((N : ℝ) * Real.exp (-T)) (Opos.card : ℝ) with hpos | hpos
  · exact hnoSet true Opos (Finset.filter_subset _ _) (by
      intro x hx
      simpa using (Finset.mem_filter.mp hx).2) (by simpa [T] using hpos)
  · have hneg : (N : ℝ) * Real.exp (-T) ≤ (Oneg.card : ℝ) := by
      by_contra hsmall
      have hsmall' : (Oneg.card : ℝ) < (N : ℝ) * Real.exp (-T) := lt_of_not_ge hsmall
      nlinarith [hsumlarge, hpos]
    exact hnoSet false Oneg (Finset.filter_subset _ _) (by
      intro x hx
      simpa using (Finset.mem_filter.mp hx).2) (by simpa [T] using hneg)

/-- L11.2a(ii) (11:120–128).  Take a maximal family of disjoint `s_c`-cliques of the graph `K_π > 8n^{-δ}` on `S`,
with union `V`; `S \ V` has no clique.  If `|V| ≥ N e^{-n^δ}`: first law `π` (width `log K ≤ n^δ`), clusters
uniform on the cliques weighted by size (aggregate uniform on `V`, width `≤ n^δ`; atoms `1/s_c ≤ e^{-n^ζ}`), and
codegree `(1 + m_x + m_{x'} + K_π)/4 ≥ 1/4 + n^{-δ}` (diagonal `(1 + m_x)/2`, as `b_* = o(n^{-δ})`): a reversed
cluster witness, excluded. -/
theorem clique_removal (δ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hK : 0 < K) :
    CliqueRemovalEv δ K := by
  classical
  have hgap : 0 < (19 : ℝ) / 20 - δ := by nlinarith [hδ']
  have hKevent : ∀ᶠ n : ℕ in Filter.atTop, K ≤ Real.exp ((n : ℝ) ^ δ) := by
    have hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ δ) Filter.atTop Filter.atTop :=
      (_root_.tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_exp_atTop.comp hp).eventually (Filter.eventually_ge_atTop K)
  have hgapEvent : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ (n : ℝ) ^ ((19 : ℝ) / 20 - δ) := by
    have hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((19 : ℝ) / 20 - δ))
        Filter.atTop Filter.atTop := (_root_.tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
    exact hp.eventually (Filter.eventually_ge_atTop 2)
  have hδsmall : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-δ) < 1 / 8 := by
    have hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) Filter.atTop (nhds 0) := by
      exact (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    exact hp.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨nK, hKeventN⟩ := Filter.eventually_atTop.1 hKevent
  obtain ⟨ngap, hngap⟩ := Filter.eventually_atTop.1 hgapEvent
  obtain ⟨nδ, hnδ⟩ := Filter.eventually_atTop.1 hδsmall
  refine ⟨max nK (max ngap (max nδ 2)), ?_⟩
  intro n hn N E X Y G π hN hπ0 hπsum hπsupp hπcap hYX S hSsub hSdegree
  have hnK : nK ≤ n := by omega
  have hngapN : ngap ≤ n := by omega
  have hnδN : nδ ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hKpow : K ≤ Real.exp ((n : ℝ) ^ δ) := hKeventN n hnK
  have hgapPow : 2 ≤ (n : ℝ) ^ ((19 : ℝ) / 20 - δ) := hngap n hngapN
  have hδpow : (n : ℝ) ^ (-δ) < 1 / 8 := hnδ n hnδN
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hNpos : 0 < N := by
    by_contra hN
    have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hX : X = ∅ := by ext x; exact Fin.elim0 x
    have hY : Y = ∅ := by ext y; exact Fin.elim0 y
    have hπsum' := hπsum
    simp [hY] at hπsum'
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hsmallb : 2 * bS n ≤ (n : ℝ) ^ (-δ) := by
    have hbase := mul_le_mul_of_nonneg_right hgapPow
      (Real.rpow_pos_of_pos hnpos (-(19 : ℝ) / 20)).le
    have hpow : (n : ℝ) ^ ((19 : ℝ) / 20 - δ) * (n : ℝ) ^ (-(19 : ℝ) / 20) =
        (n : ℝ) ^ (-δ) := by
      rw [← Real.rpow_add hnpos]
      congr 1 <;> ring
    calc
      2 * bS n = 2 * (n : ℝ) ^ (-(19 : ℝ) / 20) := by rfl
      _ ≤ (n : ℝ) ^ ((19 : ℝ) / 20 - δ) * (n : ℝ) ^ (-(19 : ℝ) / 20) := hbase
      _ = (n : ℝ) ^ (-δ) := hpow
  have hdiag : (n : ℝ) ^ (-δ) + 2 * bS n ≤ 1 / 4 := by
    have htwo : 2 * (n : ℝ) ^ (-δ) < 1 / 4 := by nlinarith [hδpow]
    nlinarith [hsmallb, htwo]
  let πlaw : Law N := ⟨π, hπ0, hπsum⟩
  have hπwidth : πlaw.WidthLE ((n : ℝ) ^ δ) := by
    intro y
    apply (le_div_iff₀ hNr).2
    calc
      π y * (N : ℝ) = (N : ℝ) * π y := by ring
      _ ≤ K := hπcap y
      _ ≤ Real.exp ((n : ℝ) ^ δ) := hKpow
  let IsClique (C : Finset (Fin N)) : Prop :=
    C ⊆ S ∧ C.card = sC n ∧
      ∀ x ∈ C, ∀ z ∈ C, x ≠ z → 8 * (n : ℝ) ^ (-δ) < corr E G π x z
  let Cliques : Finset (Finset (Fin N)) := Finset.univ.filter IsClique
  let IsPacking (P : Finset (Finset (Fin N))) : Prop :=
    (∀ C ∈ P, C ∈ Cliques) ∧
      ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D
  let Packings : Finset (Finset (Finset (Fin N))) := Finset.univ.filter IsPacking
  have hPackings : Packings.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Packings, IsPacking]
  obtain ⟨P, hPmem, hPmax⟩ := Finset.exists_max_image Packings Finset.card hPackings
  have hP : IsPacking P := (Finset.mem_filter.mp hPmem).2
  let V : Finset (Fin N) := P.biUnion (fun C => C)
  have hVsub : V ⊆ S := by
    intro x hx
    obtain ⟨C, hCP, hxC⟩ := Finset.mem_biUnion.mp hx
    have hC := hP.1 C hCP
    exact (Finset.mem_filter.mp hC).2.1 hxC
  have hsCpos : 0 < sC n := by
    dsimp [sC]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hNoClique : NoClique E G π n δ (S \ V) := by
    intro C hC hCcard
    by_contra hnoPair
    have hEdges : ∀ x ∈ C, ∀ z ∈ C, x ≠ z →
        8 * (n : ℝ) ^ (-δ) < corr E G π x z := by
      intro x hx z hz hxz
      by_contra hnot
      exact hnoPair ⟨x, hx, z, hz, hxz, le_of_not_gt hnot⟩
    have hClique : IsClique C := ⟨Finset.Subset.trans hC (Finset.sdiff_subset), hCcard, hEdges⟩
    have hCmem : C ∈ Cliques := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hClique⟩
    have hCne : C.Nonempty := Finset.card_pos.mp (by rw [hCcard]; exact hsCpos)
    have hCnotP : C ∉ P := by
      intro hCP
      obtain ⟨x, hx⟩ := hCne
      have hxV : x ∈ V := Finset.mem_biUnion.mpr ⟨C, hCP, hx⟩
      exact (Finset.mem_sdiff.mp (hC hx)).2 hxV
    have hCdisj (D : Finset (Fin N)) (hDP : D ∈ P) : Disjoint C D := by
      have hDsub : D ⊆ V := by
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨D, hDP, hx⟩
      apply Finset.disjoint_left.mpr
      intro x hxC hxD
      exact (Finset.mem_sdiff.mp (hC hxC)).2 (hDsub hxD)
    have hP' : IsPacking (insert C P) := by
      refine ⟨?_, ?_⟩
      · intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hDP
        · exact hCmem
        · exact hP.1 D hDP
      · intro D hD D' hD' hne
        rcases Finset.mem_insert.mp hD with rfl | hDP
        · rcases Finset.mem_insert.mp hD' with rfl | hD'P
          · exact (hne rfl).elim
          · exact hCdisj D' hD'P
        · rcases Finset.mem_insert.mp hD' with rfl | hD'P
          · exact (hCdisj D hDP).symm
          · exact hP.2 D hDP D' hD'P hne
    have hP'mem : insert C P ∈ Packings := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩
    have hmax := hPmax (insert C P) hP'mem
    have hcardInsert : (insert C P).card = P.card + 1 := Finset.card_insert_of_notMem hCnotP
    omega
  by_cases hVsmall : (V.card : ℝ) < (N : ℝ) * Real.exp (-((n : ℝ) ^ δ))
  · exact ⟨V, hVsub, hVsmall, hNoClique⟩
  · have hVlarge : (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) ≤ V.card := le_of_not_gt hVsmall
    have hVpos : 0 < (V.card : ℝ) :=
      lt_of_lt_of_le (mul_pos hNr (Real.exp_pos _)) hVlarge
    have hVne : V.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast hVpos
    have hPne : P.Nonempty := by
      obtain ⟨x, hxV⟩ := hVne
      obtain ⟨C, hCP, _⟩ := Finset.mem_biUnion.mp hxV
      exact ⟨C, hCP⟩
    have hPcard : 0 < P.card := Finset.card_pos.mpr hPne
    have hPcardR : 0 < (P.card : ℝ) := by exact_mod_cast hPcard
    have hVcardEq : V.card = P.card * sC n := by
      dsimp [V]
      rw [Finset.card_biUnion (fun C hC D hD hCD => hP.2 C hC D hD hCD)]
      have hsum : (∑ C ∈ P, C.card) = ∑ C ∈ P, sC n := by
        apply Finset.sum_congr rfl
        intro C hC
        exact (Finset.mem_filter.mp (hP.1 C hC)).2.2.1
      rw [hsum]
      simp
    have hVcardR : (V.card : ℝ) = (P.card : ℝ) * (sC n : ℝ) := by
      exact_mod_cast hVcardEq
    let e : {C : Finset (Fin N) // C ∈ P} ≃ Fin P.card := P.equivFin
    let block : Fin P.card → Finset (Fin N) := fun j => (e.symm j).1
    have hblockMem (j : Fin P.card) : block j ∈ P := (e.symm j).2
    have hblockClique (j : Fin P.card) : IsClique (block j) :=
      (Finset.mem_filter.mp (hP.1 (block j) (hblockMem j))).2
    have hblockCard (j : Fin P.card) : (block j).card = sC n := hblockClique j |>.2.1
    have hblockGood (j : Fin P.card) : block j ⊆ S := hblockClique j |>.1
    have hblockCorr (j : Fin P.card) : ∀ x ∈ block j, ∀ z ∈ block j, x ≠ z →
        8 * (n : ℝ) ^ (-δ) < corr E G π x z := hblockClique j |>.2.2
    have hblockDisjoint (j k : Fin P.card) (hjk : j ≠ k) : Disjoint (block j) (block k) := by
      have hblocks : block j ≠ block k := by
        intro heq
        apply hjk
        have hsub : e.symm j = e.symm k := Subtype.ext heq
        simpa using congrArg e hsub
      exact hP.2 (block j) (hblockMem j) (block k) (hblockMem k) hblocks
    have hPcardRpos : 0 < (P.card : ℝ) := hPcardR
    have hsCcastPos : 0 < (sC n : ℝ) := by exact_mod_cast hsCpos
    let lam : Fin P.card → ℝ := fun _ => (P.card : ℝ)⁻¹
    have hlamNonneg : ∀ j, 0 ≤ lam j := by intro j; exact (inv_nonneg.mpr hPcardR.le)
    have hlamSum : ∑ j : Fin P.card, lam j = 1 := by
      simp [lam, hPcardR.ne']
    have hlamPos : ∀ j, 0 < lam j := by intro j; exact inv_pos.mpr hPcardR
    let Dlaw : Fin P.card → Law N := fun j => Law.unif (block j)
      (Finset.card_pos.mp (by rw [hblockCard j]; exact hsCpos))
    have hDlawSupport : ∀ j, (Dlaw j).SupportedIn V := by
      intro j x hx
      by_contra hweight
      have hxBlock : x ∈ block j := by
        by_contra hxBlock
        have hz : (Dlaw j).w x = 0 := by
          simp [Dlaw, Law.unif, FinProb.uniform, hxBlock]
        exact hweight hz
      exact hx (Finset.mem_biUnion.mpr ⟨block j, hblockMem j, hxBlock⟩)
    let Klarge : ℝ := (n : ℝ) ^ δ
    have hKlarge : K ≤ Real.exp Klarge := hKpow
    have hπwidth' : πlaw.WidthLE Klarge := by
      intro y
      apply (le_div_iff₀ hNr).2
      calc
        πlaw.w y * (N : ℝ) = (N : ℝ) * π y := by simp [πlaw]; ring
        _ ≤ K := hπcap y
        _ ≤ Real.exp Klarge := hKlarge
    have hAgg (x : Fin N) :
        (∑ j : Fin P.card, lam j * (Dlaw j).w x) ≤ (V.card : ℝ)⁻¹ := by
      let Jx : Finset (Fin P.card) := Finset.univ.filter fun j => x ∈ block j
      have hJcard : Jx.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro j hj k hk
        by_contra hjk
        have hdisj := hblockDisjoint j k hjk
        have hnot : x ∉ block k := by
          intro hxk
          exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hj).2 hxk
        exact hnot (Finset.mem_filter.mp hk).2
      have hrecip (j : Fin P.card) :
          lam j * ((block j).card : ℝ)⁻¹ = (V.card : ℝ)⁻¹ := by
        rw [hblockCard j, hVcardR]
        dsimp [lam]
        field_simp [ne_of_gt hPcardR, ne_of_gt hsCcastPos]
      have hweight (j : Fin P.card) :
          lam j * (Dlaw j).w x = if j ∈ Jx then (V.card : ℝ)⁻¹ else 0 := by
        by_cases hj : j ∈ Jx
        · have hxj : x ∈ block j := (Finset.mem_filter.mp hj).2
          simp [Jx, Dlaw, Law.unif, FinProb.uniform, hxj, hrecip]
        · have hxj : x ∉ block j := by
            intro hxj
            exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩)
          simp [Jx, Dlaw, Law.unif, FinProb.uniform, hxj, hj]
      calc
        (∑ j : Fin P.card, lam j * (Dlaw j).w x) =
            ∑ j : Fin P.card, if j ∈ Jx then (V.card : ℝ)⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hweight j
        _ = (Jx.card : ℝ) * (V.card : ℝ)⁻¹ := by
              calc
                _ = ∑ j : Fin P.card, (if j ∈ Jx then (1 : ℝ) else 0) *
                    (V.card : ℝ)⁻¹ := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      by_cases hmem : j ∈ Jx <;> simp [hmem]
                _ = (∑ j : Fin P.card, if j ∈ Jx then (1 : ℝ) else 0) *
                    (V.card : ℝ)⁻¹ := by rw [← Finset.sum_mul]
                _ = (Jx.card : ℝ) * (V.card : ℝ)⁻¹ := by simp
        _ ≤ (V.card : ℝ)⁻¹ := by
              have hJcardR : (Jx.card : ℝ) ≤ 1 := by exact_mod_cast hJcard
              simpa using mul_le_mul_of_nonneg_right hJcardR
                (inv_nonneg.mpr (show (0 : ℝ) ≤ (V.card : ℝ) from Nat.cast_nonneg _))
    have hAtom (j : Fin P.card) (x : Fin N) : (Dlaw j).w x ≤
        Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 100))) := by
      have hceil : Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) ≤ (sC n : ℝ) := by
        dsimp [sC]
        exact Nat.le_ceil _
      have hrecip : (sC n : ℝ)⁻¹ ≤ Real.exp (-((n : ℝ) ^ ((1 : ℝ) / 100))) := by
        have h := one_div_le_one_div_of_le (Real.exp_pos ((n : ℝ) ^ ((1 : ℝ) / 100))) hceil
        simpa [Real.exp_neg] using h
      by_cases hx : x ∈ block j
      · have hcard : (block j).card = sC n := hblockCard j
        simpa [Dlaw, Law.unif, FinProb.uniform, hx, hcard] using hrecip
      · simpa [Dlaw, Law.unif, FinProb.uniform, hx] using
          ((Real.exp_pos _).le)
    have hcodegFormula (x z : Fin N) :
        4 * codeg (transposeRel E) G πlaw x z =
          1 + sMean E G π x + sMean E G π z + corr E G π x z := by
      have hcodeg : codeg (transposeRel E) G πlaw x z =
          ∑ y, π y * (if Hits E G x y ∧ Hits E G z y then (1 : ℝ) else 0) := by
        unfold codeg
        apply Finset.sum_congr rfl
        intro y hy
        simp [πlaw, hits_transpose]
      have hpoint (y : Fin N) :
          4 * (if Hits E G x y ∧ Hits E G z y then (1 : ℝ) else 0) =
            1 + fv E G x y + fv E G z y + fv E G x y * fv E G z y := by
        by_cases hxy : Hits E G x y <;> by_cases hzy : Hits E G z y <;>
          simp [fv, hit, hxy, hzy] <;> ring
      have hsumIdentity :
          (∑ y, π y *
              (1 + fv E G x y + fv E G z y + fv E G x y * fv E G z y)) =
            (∑ y, π y) + (∑ y, π y * fv E G x y) +
              (∑ y, π y * fv E G z y) + (∑ y, π y * fv E G x y * fv E G z y) := by
        calc
          _ = ∑ y, (π y + π y * fv E G x y + π y * fv E G z y +
              π y * fv E G x y * fv E G z y) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
          _ = _ := by simp only [Finset.sum_add_distrib]
      calc
        4 * codeg (transposeRel E) G πlaw x z =
            ∑ y, π y * (4 * (if Hits E G x y ∧ Hits E G z y then (1 : ℝ) else 0)) := by
              rw [hcodeg, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              ring
        _ = ∑ y, π y *
              (1 + fv E G x y + fv E G z y + fv E G x y * fv E G z y) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [hpoint y]
        _ = (∑ y, π y) + (∑ y, π y * fv E G x y) +
              (∑ y, π y * fv E G z y) + (∑ y, π y * fv E G x y * fv E G z y) := hsumIdentity
        _ = 1 + sMean E G π x + sMean E G π z + corr E G π x z := by
              simp [sMean, corr, hπsum]
    have hVwidth : (V.card : ℝ)⁻¹ ≤ Real.exp ((n : ℝ) ^ δ) / N := by
      have hmul : (N : ℝ) ≤ (V.card : ℝ) * Real.exp ((n : ℝ) ^ δ) := by
        calc
          (N : ℝ) = (N : ℝ) * 1 := by ring
          _ = (N : ℝ) *
              (Real.exp (-((n : ℝ) ^ δ)) * Real.exp ((n : ℝ) ^ δ)) := by
                rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          _ = ((N : ℝ) * Real.exp (-((n : ℝ) ^ δ))) * Real.exp ((n : ℝ) ^ δ) := by ring
          _ ≤ (V.card : ℝ) * Real.exp ((n : ℝ) ^ δ) :=
                mul_le_mul_of_nonneg_right hVlarge (Real.exp_pos _).le
      rw [show (V.card : ℝ)⁻¹ = (1 : ℝ) / V.card by ring]
      rw [div_le_div_iff₀ hVpos hNr]
      nlinarith [hmul]
    have hπsupported : πlaw.SupportedIn Y := by
      intro y hy
      by_contra hne
      exact hy (hπsupp y (by simpa [πlaw] using hne))
    have hmeanLower (x : Fin N) (hx : x ∈ S) : -4 * bS n ≤ sMean E G π x :=
      by linarith [(abs_le.mp (hSdegree x hx)).1]
    have hcorrSelf (x : Fin N) : corr E G π x x = 1 := by
      have hpoint (y : Fin N) : fv E G x y * fv E G x y = 1 := by
        by_cases hxy : Hits E G x y <;> simp [fv, hit, hxy] <;> ring
      calc
        corr E G π x x = ∑ y, π y := by
          unfold corr
          apply Finset.sum_congr rfl
          intro y hy
          calc
            π y * fv E G x y * fv E G x y = π y * (fv E G x y * fv E G x y) := by ring
            _ = π y := by rw [hpoint]; ring
        _ = 1 := hπsum
    have hcodegBound (j : Fin P.card) (y z : Fin N)
        (hy : 0 < (Dlaw j).w y) (hz : 0 < (Dlaw j).w z) :
        1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg (transposeRel E) G πlaw y z := by
      have hyBlock : y ∈ block j := by
        by_contra hnot
        have hzero : (Dlaw j).w y = 0 := by
          simp [Dlaw, Law.unif, FinProb.uniform, hnot]
        linarith
      have hzBlock : z ∈ block j := by
        by_contra hnot
        have hzero : (Dlaw j).w z = 0 := by
          simp [Dlaw, Law.unif, FinProb.uniform, hnot]
        linarith
      have hyS : y ∈ S := hblockGood j hyBlock
      have hzS : z ∈ S := hblockGood j hzBlock
      have hmy : -4 * bS n ≤ sMean E G π y := hmeanLower y hyS
      have hmz : -4 * bS n ≤ sMean E G π z := hmeanLower z hzS
      by_cases hyz : y = z
      · subst z
        have hdiag := hcodegFormula y y
        rw [hcorrSelf y] at hdiag
        have hcodegEq : codeg (transposeRel E) G πlaw y y = (1 + sMean E G π y) / 2 := by
          nlinarith [hdiag]
        rw [hcodegEq]
        nlinarith [hdiag]
      · have hcorr : 8 * (n : ℝ) ^ (-δ) < corr E G π y z :=
          hblockCorr j y hyBlock z hzBlock hyz
        have hform := hcodegFormula y z
        nlinarith [hform, hmy, hmz, hcorr, hsmallb]
    have hCluster : PCluster G ((1 / 100 : ℚ) : ℝ) δ n N (transposeRel E) (Y, V) := by
      unfold PCluster
      change ∃ μ' : Law N, ∃ K' : ℕ, ∃ lam' : Fin K' → ℝ, ∃ D' : Fin K' → Law N,
        μ'.SupportedIn Y ∧ (∀ j, (D' j).SupportedIn V) ∧
        (∀ j, 0 ≤ lam' j) ∧ ∑ j, lam' j = 1 ∧
        μ'.WidthLE ((n : ℝ) ^ δ) ∧
        (∀ y, ∑ j, lam' j * (D' j).w y ≤ Real.exp ((n : ℝ) ^ δ) / N) ∧
        (∀ j y, (D' j).w y ≤ Real.exp (-((n : ℝ) ^ ((1 / 100 : ℚ) : ℝ)))) ∧
        (∀ j, 0 < lam' j → ∀ y y', 0 < (D' j).w y → 0 < (D' j).w y' →
          1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg (transposeRel E) G μ' y y')
      have hAtom' : ∀ j x, (Dlaw j).w x ≤
          Real.exp (-((n : ℝ) ^ ((1 / 100 : ℚ) : ℝ))) := by
        intro j x
        have hzeta : ((1 / 100 : ℚ) : ℝ) = (1 : ℝ) / 100 := by norm_num
        simpa [hzeta] using hAtom j x
      refine ⟨πlaw, P.card, lam, Dlaw, hπsupported, hDlawSupport,
        hlamNonneg, hlamSum, hπwidth', ?_, hAtom', ?_⟩
      · intro x
        exact (hAgg x).trans hVwidth
      · intro j hweight y z hy hz
        exact hcodegBound j y z hy hz
    have hExcluded := hYX G Y V (by simp) (Finset.Subset.trans hVsub hSsub)
    exact False.elim (hExcluded hCluster)

set_option maxHeartbeats 12000000

/-- L11.2b (11:130–159).  Suppose the violators `U` number at least `N e^{-n^δ}`; let `μ_U` be uniform on `U`.
`E_i D_i(x) = (1 + m_x)/2` and tag mass `> η` has `D_i(x) > .8`, so `E_i D_i(x)² ≥ 1/4 + cη`.  In `L²(μ_U)` a
positive `p`-fraction of tags has `‖v_i‖ > 1/2 + c'`; each such tag gives `ρ_i ≤ Cπ_i` on labels with projection
`≥ 1/2 + c''` on `v_i/‖v_i‖`; the graph `codeg_{μ_U} ≥ 1/4 + c'''` on them has independence number below an
absolute `t₀`.  Draw `r₀ = ⌊e^{.03n}⌋` distinct labels from `ρ_i` (collisions `O(r₀² e^{.02n}/N) = o(1)`), pack
all but `binom(s_c + t₀, t₀)` of them into `s_c`-cliques (X-RamseyBinom), and average the cluster mixtures over
samples and tags (aggregate `O(1) π`): an `(X, Y)` cluster witness with first law `μ_U`, excluded. -/
theorem high_degree (δ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hK : 0 < K) :
    HighDegreeEv δ K := by
  classical
  let t₀ : ℕ := q_s11_compat_t₀
  have heta : 0 < etaC := by norm_num [etaC]
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp ((n : ℝ) ^ δ))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hpow
  have hpow01 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 100))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hexp01 : Filter.Tendsto (fun n : ℕ => Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp hpow01
  have hexpLarge : ∀ᶠ n : ℕ in Filter.atTop,
      (t₀ : ℝ) + 1 ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) :=
    hexp01.eventually (Filter.eventually_ge_atTop ((t₀ : ℝ) + 1))
  have hpowNeg99 : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ (-(99 / 100 : ℝ))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 99 / 100)).comp
      tendsto_natCast_atTop_atTop
  have hsmallRatio : ∀ᶠ n : ℕ in Filter.atTop,
      2 * (t₀ : ℝ) * (n : ℝ) ^ (-(99 / 100 : ℝ)) < 1 / 100 := by
    have hscaled : Filter.Tendsto
        (fun n : ℕ => 2 * (t₀ : ℝ) * (n : ℝ) ^ (-(99 / 100 : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hpowNeg99)
    exact hscaled.eventually (Iio_mem_nhds (by norm_num))
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-δ) < etaC / 1000 := by
    have hneg : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop
    exact hneg.eventually (Iio_mem_nhds (by norm_num [etaC]))
  have hbsmall : ∀ᶠ n : ℕ in Filter.atTop, bS n < etaC / 100 := by
    have hneg : Filter.Tendsto
        ((fun x : ℝ => x ^ (-(19 / 20 : ℝ))) ∘ (fun n : ℕ => (n : ℝ)))
        Filter.atTop (nhds 0) := by
      have hpos : 0 < (19 : ℝ) / 20 := by norm_num
      exact (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
    have hneigh : Set.Iio (etaC / 100) ∈ nhds (0 : ℝ) := Iio_mem_nhds (by positivity)
    have hevent := hneg.eventually hneigh
    have hevent' : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(19 / 20 : ℝ)) < etaC / 100 := by
      simpa only [Function.comp_apply] using hevent
    simpa only [bS, show -(19 : ℝ) / 20 = -(19 / 20 : ℝ) from by ring] using hevent'
  have hKlarge : ∀ᶠ n : ℕ in Filter.atTop, K ≤ Real.exp ((n : ℝ) ^ δ) :=
    hexp.eventually (Filter.eventually_ge_atTop K)
  obtain ⟨nsmall, hnsmall⟩ := Filter.eventually_atTop.1 hsmall
  obtain ⟨nb, hnb⟩ := Filter.eventually_atTop.1 hbsmall
  obtain ⟨nK, hnK⟩ := Filter.eventually_atTop.1 hKlarge
  obtain ⟨nExp, hnExp⟩ := Filter.eventually_atTop.1 hexpLarge
  obtain ⟨nRatio, hnRatio⟩ := Filter.eventually_atTop.1 hsmallRatio
  refine ⟨max nsmall (max nb (max nK (max nExp (max nRatio 10)))), ?_⟩
  intro n hn N E X Y G ι hι π p hN hπnonneg hπsum hπsupp hπcap hmixcap hXY
  have hnsmall' : nsmall ≤ n := by omega
  have hnb' : nb ≤ n := by omega
  have hnK' : nK ≤ n := by omega
  have hnExp' : nExp ≤ n := by omega
  have hnRatio' : nRatio ≤ n := by omega
  have hn10 : 10 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hpowSmall : (n : ℝ) ^ (-δ) < etaC / 1000 := hnsmall n hnsmall'
  have hbSmall : bS n < etaC / 100 := hnb n hnb'
  have hKexp : K ≤ Real.exp ((n : ℝ) ^ δ) := hnK n hnK'
  have hExpLarge' : (t₀ : ℝ) + 1 ≤ Real.exp ((n : ℝ) ^ ((1 : ℝ) / 100)) :=
    hnExp n hnExp'
  have hsmallRatio' :
      2 * (t₀ : ℝ) * (n : ℝ) ^ (-(99 / 100 : ℝ)) < 1 / 100 := hnRatio n hnRatio'
  let πbar : Fin N → ℝ := mixW p π
  have hbarNonneg : ∀ y, 0 ≤ πbar y := by
    intro y
    dsimp [πbar, mixW]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (hπnonneg i y)
  have hbarSum : ∑ y, πbar y = 1 := by
    simp only [πbar, mixW]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hπsum]
    simp [p.sum_eq_one]
  have hdegreeMix (x : Fin N) :
      deg E G πbar x = ∑ i, p.w i * deg E G (π i) x := by
    unfold deg
    change (∑ y, (∑ i, p.w i * π i y) * hit E G x y) = _
    calc
      (∑ y, (∑ i, p.w i * π i y) * hit E G x y) =
          ∑ y, ∑ i, p.w i * (π i y * hit E G x y) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = ∑ i, ∑ y, p.w i * (π i y * hit E G x y) := by rw [Finset.sum_comm]
      _ = ∑ i, p.w i * (∑ y, π i y * hit E G x y) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ i, p.w i * deg E G (π i) x := by rfl
  have hsMeanDegree (x : Fin N) : sMean E G πbar x = 2 * deg E G πbar x - 1 := by
    unfold sMean deg fv
    calc
      (∑ y, πbar y * (2 * hit E G x y - 1)) =
          ∑ y, (2 * (πbar y * hit E G x y) - πbar y) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
      _ = 2 * (∑ y, πbar y * hit E G x y) - ∑ y, πbar y := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * (∑ y, πbar y * hit E G x y) - 1 := by rw [hbarSum]
      _ = 2 * deg E G πbar x - 1 := by rfl
  have hdegreeBounds (i : ι) (x : Fin N) :
      0 ≤ deg E G (π i) x ∧ deg E G (π i) x ≤ 1 := by
    unfold deg
    constructor
    · exact Finset.sum_nonneg fun y _ =>
        mul_nonneg (hπnonneg i y) (by unfold hit; split_ifs <;> norm_num)
    · calc
        (∑ y, π i y * hit E G x y) ≤ ∑ y, π i y * 1 := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (by unfold hit; split_ifs <;> norm_num) (hπnonneg i y)
        _ = 1 := by simp [hπsum i]
  let U : Finset (Fin N) := X.filter fun x =>
    |sMean E G πbar x| ≤ 4 * bS n ∧
      etaC < ∑ i ∈ Finset.univ.filter (fun i => (4 / 5 : ℝ) < deg E G (π i) x), p.w i
  change (U.card : ℝ) < (N : ℝ) * Real.exp (-((n : ℝ) ^ δ))
  by_contra hsmall
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by norm_num : 0 < 2)) hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hUlarge : (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) ≤ U.card := le_of_not_gt hsmall
  have hUcardPos : 0 < (U.card : ℝ) :=
    lt_of_lt_of_le (mul_pos hNr (Real.exp_pos _)) hUlarge
  have hUne : U.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hUcardPos
  let μ : Law N := Law.unif U hUne
  have hUsub : U ⊆ X := Finset.filter_subset _ _
  have hμX : μ.SupportedIn X := by
    intro x hx
    have hxU : x ∉ U := fun hxU => hx (hUsub hxU)
    simp [μ, Law.unif, FinProb.uniform, hxU]
  have hμWidth : μ.WidthLE ((n : ℝ) ^ δ) := by
    intro x
    change (if x ∈ U then (U.card : ℝ)⁻¹ else 0) ≤ Real.exp ((n : ℝ) ^ δ) / N
    by_cases hx : x ∈ U
    · rw [if_pos hx]
      have hcardMul : (N : ℝ) ≤ (U.card : ℝ) * Real.exp ((n : ℝ) ^ δ) := by
        calc
          (N : ℝ) = (N : ℝ) * 1 := by ring
          _ = (N : ℝ) * (Real.exp (-((n : ℝ) ^ δ)) * Real.exp ((n : ℝ) ^ δ)) := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          _ = ((N : ℝ) * Real.exp (-((n : ℝ) ^ δ))) * Real.exp ((n : ℝ) ^ δ) := by ring
          _ ≤ (U.card : ℝ) * Real.exp ((n : ℝ) ^ δ) :=
            mul_le_mul_of_nonneg_right hUlarge (le_of_lt (Real.exp_pos _))
      rw [show (U.card : ℝ)⁻¹ = (1 : ℝ) / (U.card : ℝ) by ring]
      rw [div_le_div_iff₀ (by exact_mod_cast (Finset.card_pos.mpr hUne)) hNr]
      nlinarith
    · rw [if_neg hx]
      positivity
  let massHigh (x : Fin N) : ℝ :=
    ∑ i ∈ Finset.univ.filter (fun i => (4 / 5 : ℝ) < deg E G (π i) x), p.w i
  have hmassHigh (x : Fin N) (hx : x ∈ U) : etaC < massHigh x := by
    exact (Finset.mem_filter.mp hx).2.2
  have hgoodMean (x : Fin N) (hx : x ∈ U) : |sMean E G πbar x| ≤ 4 * bS n :=
    (Finset.mem_filter.mp hx).2.1
  have hdegreeBarBounds (x : Fin N) :
      0 ≤ deg E G πbar x ∧ deg E G πbar x ≤ 1 := by
    constructor
    · rw [hdegreeMix]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (hdegreeBounds i x).1
    · rw [hdegreeMix]
      calc
        (∑ i, p.w i * deg E G (π i) x) ≤ ∑ i, p.w i * 1 := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hdegreeBounds i x).2 (p.nonneg i)
        _ = 1 := by simp [p.sum_eq_one]
  have hmeanBounds (x : Fin N) (hx : x ∈ U) :
      1 / 2 - 2 * bS n ≤ deg E G πbar x ∧ deg E G πbar x ≤ 1 / 2 + 2 * bS n := by
    have h := abs_le.mp (hgoodMean x hx)
    rw [hsMeanDegree] at h
    constructor <;> linarith
  have hvariance (x : Fin N) (hx : x ∈ U) :
      etaC * (3 / 10 : ℝ) ^ 2 ≤
        ∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2 := by
    let H : Finset ι := Finset.univ.filter fun i => (4 / 5 : ℝ) < deg E G (π i) x
    have hconst (i : ι) (hi : i ∈ H) :
        (3 / 10 : ℝ) ^ 2 ≤ (deg E G (π i) x - 1 / 2) ^ 2 := by
      have hdegree : (4 / 5 : ℝ) < deg E G (π i) x := (Finset.mem_filter.mp hi).2
      nlinarith
    have hrestrict :
        (∑ i ∈ H, p.w i * (3 / 10 : ℝ) ^ 2) =
          (3 / 10 : ℝ) ^ 2 * massHigh x := by
      calc
        (∑ i ∈ H, p.w i * (3 / 10 : ℝ) ^ 2) =
            (∑ i ∈ H, p.w i) * (3 / 10 : ℝ) ^ 2 := by rw [← Finset.sum_mul]
        _ = (3 / 10 : ℝ) ^ 2 * massHigh x := by
          have hm : (∑ i ∈ H, p.w i) = massHigh x := rfl
          rw [hm]
          ring
    have hsubsum :
        (∑ i ∈ H, p.w i * (deg E G (π i) x - 1 / 2) ^ 2) ≤
          ∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro i hi hnot
        exact mul_nonneg (p.nonneg i) (sq_nonneg _))
    have hterm :
        (∑ i ∈ H, p.w i * (3 / 10 : ℝ) ^ 2) ≤
          ∑ i ∈ H, p.w i * (deg E G (π i) x - 1 / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hconst i hi) (p.nonneg i)
    have hvarlt : etaC * (3 / 10 : ℝ) ^ 2 <
        ∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2 := by
      calc
        etaC * (3 / 10 : ℝ) ^ 2 < massHigh x * (3 / 10 : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right (hmassHigh x hx) (by norm_num)
        _ = ∑ i ∈ H, p.w i * (3 / 10 : ℝ) ^ 2 := by rw [hrestrict]; ring
        _ ≤ ∑ i ∈ H, p.w i * (deg E G (π i) x - 1 / 2) ^ 2 := hterm
        _ ≤ ∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2 := hsubsum
    exact hvarlt.le
  have hsecondIdentity (x : Fin N) :
      ∑ i, p.w i * (deg E G (π i) x) ^ 2 =
        (∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2) +
          (∑ i, p.w i * deg E G (π i) x) - 1 / 4 := by
    calc
      ∑ i, p.w i * (deg E G (π i) x) ^ 2 =
          ∑ i, (p.w i * (deg E G (π i) x - 1 / 2) ^ 2 +
            p.w i * deg E G (π i) x - p.w i * (1 / 4 : ℝ)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = (∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2) +
            (∑ i, p.w i * deg E G (π i) x) - (∑ i, p.w i * (1 / 4 : ℝ)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ i, p.w i * (deg E G (π i) x - 1 / 2) ^ 2) +
            (∑ i, p.w i * deg E G (π i) x) - 1 / 4 := by
              rw [← Finset.sum_mul, p.sum_eq_one]
              ring
  have hrowSecond (x : Fin N) (hx : x ∈ U) :
      1 / 4 + etaC / 20 ≤ ∑ i, p.w i * (deg E G (π i) x) ^ 2 := by
    have hmeanSum : 1 / 2 - 2 * bS n ≤ ∑ i, p.w i * deg E G (π i) x := by
      rw [← hdegreeMix x]
      exact (hmeanBounds x hx).1
    rw [hsecondIdentity]
    nlinarith [hvariance x hx, hmeanSum, hbSmall, heta]
  let tagMoment (i : ι) : ℝ := ∑ x, μ.w x * (deg E G (π i) x) ^ 2
  have htagMomentBounds (i : ι) : 0 ≤ tagMoment i ∧ tagMoment i ≤ 1 := by
    constructor
    · dsimp [tagMoment]
      exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _)
    · dsimp [tagMoment]
      calc
        (∑ x, μ.w x * (deg E G (π i) x) ^ 2) ≤ ∑ x, μ.w x * 1 := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (by nlinarith [(hdegreeBounds i x).1, (hdegreeBounds i x).2])
            (μ.nonneg x)
        _ = 1 := by simp [μ.sum_eq_one]
  have hprofileSecond :
      (∑ i, p.w i * tagMoment i) =
        ∑ x, μ.w x * (∑ i, p.w i * (deg E G (π i) x) ^ 2) := by
    dsimp [tagMoment]
    calc
      (∑ i, p.w i * ∑ x, μ.w x * (deg E G (π i) x) ^ 2) =
          ∑ i, ∑ x, p.w i * (μ.w x * (deg E G (π i) x) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = ∑ x, ∑ i, p.w i * (μ.w x * (deg E G (π i) x) ^ 2) := by
            rw [Finset.sum_comm]
      _ = ∑ x, μ.w x * (∑ i, p.w i * (deg E G (π i) x) ^ 2) := by
            apply Finset.sum_congr rfl
            intro x hx
            calc
              (∑ i, p.w i * (μ.w x * (deg E G (π i) x) ^ 2)) =
                  ∑ i, μ.w x * (p.w i * (deg E G (π i) x) ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
              _ = μ.w x * (∑ i, p.w i * (deg E G (π i) x) ^ 2) := by
                    rw [← Finset.mul_sum]
  have hprofileSecondLower : 1 / 4 + etaC / 20 ≤ ∑ i, p.w i * tagMoment i := by
    calc
      1 / 4 + etaC / 20 = (1 / 4 + etaC / 20) * ∑ x, μ.w x := by rw [μ.sum_eq_one]; ring
      _ = ∑ x, μ.w x * (1 / 4 + etaC / 20) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ ≤ ∑ x, μ.w x * (∑ i, p.w i * (deg E G (π i) x) ^ 2) := by
        apply Finset.sum_le_sum
        intro x hx
        by_cases hxU : x ∈ U
        · exact mul_le_mul_of_nonneg_left (hrowSecond x hxU) (μ.nonneg x)
        · have hμzero : μ.w x = 0 := by simp [μ, Law.unif, FinProb.uniform, hxU]
          simp [hμzero]
      _ = ∑ i, p.w i * tagMoment i := hprofileSecond.symm
  let NormGood : Finset ι := Finset.univ.filter fun i => 1 / 4 + etaC / 40 < tagMoment i
  let normGoodMass : ℝ := ∑ i ∈ NormGood, p.w i
  have hnormGoodMass : etaC / 100 < normGoodMass := by
    by_contra hnot
    have hgoodIndicator :
        (∑ i, p.w i * (if i ∈ NormGood then (1 : ℝ) else 0)) = normGoodMass := by
      calc
        (∑ i, p.w i * (if i ∈ NormGood then (1 : ℝ) else 0)) =
            ∑ i, if i ∈ NormGood then p.w i else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases h : i ∈ NormGood <;> simp [h]
        _ = normGoodMass := by simp [normGoodMass, NormGood, Finset.sum_filter]
    have hsumUpper :
        (∑ i, p.w i * (1 / 4 + etaC / 40 + if i ∈ NormGood then 1 else 0)) =
          1 / 4 + etaC / 40 + normGoodMass := by
      calc
        _ = ∑ i, (p.w i * (1 / 4 + etaC / 40) +
            p.w i * (if i ∈ NormGood then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i, p.w i * (1 / 4 + etaC / 40)) +
            (∑ i, p.w i * (if i ∈ NormGood then 1 else 0)) := by
              rw [Finset.sum_add_distrib]
        _ = 1 / 4 + etaC / 40 + normGoodMass := by
              rw [← Finset.sum_mul, p.sum_eq_one, hgoodIndicator]
              ring
    have hnormUpper : (∑ i, p.w i * tagMoment i) ≤ 1 / 4 + etaC / 40 + normGoodMass := by
      calc
        (∑ i, p.w i * tagMoment i) ≤
            ∑ i, p.w i * (1 / 4 + etaC / 40 + if i ∈ NormGood then 1 else 0) := by
              apply Finset.sum_le_sum
              intro i hi
              apply mul_le_mul_of_nonneg_left _ (p.nonneg i)
              by_cases hiGood : i ∈ NormGood
              · have hle := (htagMomentBounds i).2
                simp [hiGood]
                linarith
              · have hsmallI : tagMoment i ≤ 1 / 4 + etaC / 40 := by
                  by_contra hn
                  exact hiGood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hn⟩)
                simp [hiGood]
                nlinarith [hsmallI]
        _ = 1 / 4 + etaC / 40 + normGoodMass := hsumUpper
    have hmassLe : normGoodMass ≤ etaC / 100 := le_of_not_gt hnot
    nlinarith [hprofileSecondLower, heta]
  have hweightedCS (f g : Fin N → ℝ) :
      (∑ x, μ.w x * f x * g x) ^ 2 ≤
        (∑ x, μ.w x * f x ^ 2) * (∑ x, μ.w x * g x ^ 2) := by
    let r : Fin N → ℝ := fun x => Real.sqrt (μ.w x)
    have hr (x : Fin N) : r x ^ 2 = μ.w x := Real.sq_sqrt (μ.nonneg x)
    have hsumSq (f : Fin N → ℝ) :
        ∑ x, (r x * f x) ^ 2 = ∑ x, μ.w x * f x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [mul_pow, hr]
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun x => r x * f x) (fun x => r x * g x)
    calc
      (∑ x, μ.w x * f x * g x) ^ 2 =
          (∑ x, (r x * f x) * (r x * g x)) ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro x hx
            rw [← hr x]
            ring
      _ ≤ (∑ x, (r x * f x) ^ 2) * (∑ x, (r x * g x) ^ 2) := h
      _ = (∑ x, μ.w x * f x ^ 2) * (∑ x, μ.w x * g x ^ 2) := by
            rw [hsumSq f, hsumSq g]
  let inner (i : ι) (y : Fin N) : ℝ :=
    ∑ x, μ.w x * hit E G x y * deg E G (π i) x
  have hinnerNonneg (i : ι) (y : Fin N) : 0 ≤ inner i y := by
    dsimp [inner]
    apply Finset.sum_nonneg
    intro x hx
    exact mul_nonneg (mul_nonneg (μ.nonneg x)
      (by unfold hit; split_ifs <;> norm_num)) (hdegreeBounds i x).1
  have hinnerUpper (i : ι) (y : Fin N) : inner i y ≤ Real.sqrt (tagMoment i) := by
    have hcs := hweightedCS (fun x => hit E G x y) (fun x => deg E G (π i) x)
    have hhit : ∑ x, μ.w x * (hit E G x y) ^ 2 ≤ 1 := by
      calc
        (∑ x, μ.w x * (hit E G x y) ^ 2) ≤ ∑ x, μ.w x * 1 := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (by unfold hit; split_ifs <;> norm_num) (μ.nonneg x)
        _ = 1 := by simp [μ.sum_eq_one]
    have hsq : inner i y ^ 2 ≤ tagMoment i := by
      dsimp [inner] at hcs ⊢
      dsimp [tagMoment]
      calc
        (∑ x, μ.w x * hit E G x y * deg E G (π i) x) ^ 2 ≤
            (∑ x, μ.w x * (hit E G x y) ^ 2) * (∑ x, μ.w x * (deg E G (π i) x) ^ 2) := by
              simpa [mul_assoc] using hcs
        _ ≤ 1 * (∑ x, μ.w x * (deg E G (π i) x) ^ 2) :=
              mul_le_mul_of_nonneg_right hhit (htagMomentBounds i).1
        _ = ∑ x, μ.w x * (deg E G (π i) x) ^ 2 := by ring
    exact Real.le_sqrt_of_sq_le hsq
  have hinnerAverage (i : ι) :
      ∑ y, π i y * inner i y = tagMoment i := by
    calc
      (∑ y, π i y * inner i y) =
          ∑ y, ∑ x, π i y * (μ.w x * hit E G x y * deg E G (π i) x) := by
            apply Finset.sum_congr rfl
            intro y hy
            dsimp [inner]
            rw [Finset.mul_sum]
      _ = ∑ x, ∑ y, π i y * (μ.w x * hit E G x y * deg E G (π i) x) := by
            rw [Finset.sum_comm]
      _ = ∑ x, μ.w x * deg E G (π i) x *
            (∑ y, π i y * hit E G x y) := by
              apply Finset.sum_congr rfl
              intro x hx
              calc
                (∑ y, π i y * (μ.w x * hit E G x y * deg E G (π i) x)) =
                    ∑ y, (μ.w x * deg E G (π i) x) * (π i y * hit E G x y) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
                _ = μ.w x * deg E G (π i) x * (∑ y, π i y * hit E G x y) := by
                      rw [Finset.mul_sum]
      _ = ∑ x, μ.w x * (deg E G (π i) x) ^ 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [← show deg E G (π i) x = ∑ y, π i y * hit E G x y from rfl]
            ring
      _ = tagMoment i := rfl
  let norm (i : ι) : ℝ := Real.sqrt (tagMoment i)
  let projection (i : ι) (y : Fin N) : ℝ := inner i y / norm i
  have hnormPos (i : ι) (hi : i ∈ NormGood) : 0 < norm i := by
    have hmoment : 0 < tagMoment i := by
      have h := (Finset.mem_filter.mp hi).2
      linarith [heta]
    dsimp [norm]
    exact Real.sqrt_pos.2 hmoment
  have hnormLower (i : ι) (hi : i ∈ NormGood) :
      1 / 2 + etaC / 100 ≤ norm i := by
    have hmoment := (Finset.mem_filter.mp hi).2
    have hbase : (1 / 2 + etaC / 100) ^ 2 ≤ 1 / 4 + etaC / 40 := by
      norm_num [etaC]
    dsimp [norm]
    exact Real.le_sqrt_of_sq_le (le_trans hbase (le_of_lt hmoment))
  have hprojectionNonneg (i : ι) (hi : i ∈ NormGood) (y : Fin N) :
      0 ≤ projection i y := by
    dsimp [projection]
    exact div_nonneg (hinnerNonneg i y) (Real.sqrt_nonneg _)
  have hprojectionLeOne (i : ι) (hi : i ∈ NormGood) (y : Fin N) :
      projection i y ≤ 1 := by
    have hnorm := hnormPos i hi
    apply (div_le_one hnorm).2
    exact (hinnerUpper i y).trans_eq (by rfl)
  have hprojectionAverage (i : ι) (hi : i ∈ NormGood) :
      ∑ y, π i y * projection i y = norm i := by
    have hnorm := hnormPos i hi
    calc
      (∑ y, π i y * projection i y) =
          (∑ y, π i y * inner i y) / norm i := by
            dsimp [projection]
            calc
              (∑ y, π i y * (inner i y / norm i)) =
                  ∑ y, (π i y * inner i y) / norm i := by
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring
              _ = (∑ y, π i y * inner i y) / norm i := by rw [Finset.sum_div]
      _ = tagMoment i / norm i := by rw [hinnerAverage]
      _ = norm i := by
            apply (div_eq_iff hnorm.ne').2
            dsimp [norm]
            calc
              tagMoment i = Real.sqrt (tagMoment i) ^ 2 :=
                (Real.sq_sqrt (htagMomentBounds i).1).symm
              _ = Real.sqrt (tagMoment i) * Real.sqrt (tagMoment i) := by ring
  let selected (i : ι) : Finset (Fin N) :=
    Finset.univ.filter fun y => (1 / 2 + etaC / 200) < projection i y
  let selectedMass (i : ι) : ℝ := ∑ y ∈ selected i, π i y
  have hselectedMass (i : ι) (hi : i ∈ NormGood) : etaC / 1000 < selectedMass i := by
    let S := selected i
    have hindicator :
        (∑ y, π i y * (if y ∈ S then (1 : ℝ) else 0)) = selectedMass i := by
      calc
        (∑ y, π i y * (if y ∈ S then (1 : ℝ) else 0)) =
            ∑ y, if y ∈ S then π i y else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases h : y ∈ S <;> simp [h]
        _ = selectedMass i := by simp [selectedMass, S]
    have hupper :
        (∑ y, π i y * projection i y) ≤ 1 / 2 + etaC / 200 + selectedMass i := by
      calc
        (∑ y, π i y * projection i y) ≤
            ∑ y, π i y * (1 / 2 + etaC / 200 + if y ∈ S then 1 else 0) := by
              apply Finset.sum_le_sum
              intro y hy
              apply mul_le_mul_of_nonneg_left _ (hπnonneg i y)
              by_cases h : y ∈ S
              · have hp := hprojectionLeOne i hi y
                simp [h]
                linarith
              · have hp : projection i y ≤ 1 / 2 + etaC / 200 := by
                  by_contra hlarge
                  exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hlarge⟩)
                simp [h]
                nlinarith [hp]
        _ = 1 / 2 + etaC / 200 + selectedMass i := by
              calc
                _ = ∑ y, (π i y * (1 / 2 + etaC / 200) +
                    π i y * (if y ∈ S then 1 else 0)) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
                _ = (∑ y, π i y * (1 / 2 + etaC / 200)) +
                    (∑ y, π i y * (if y ∈ S then 1 else 0)) := by
                      rw [Finset.sum_add_distrib]
                _ = 1 / 2 + etaC / 200 + selectedMass i := by
                      rw [← Finset.sum_mul, hπsum i, hindicator]
                      ring
    rw [hprojectionAverage i hi] at hupper
    nlinarith [hnormLower i hi, heta]
  have hHitProd (x y z : Fin N) :
      hit E G x y * hit E G x z =
        (if Hits E G x y ∧ Hits E G x z then (1 : ℝ) else 0) := by
    unfold hit
    by_cases hy : Hits E G x y <;> by_cases hz : Hits E G x z <;> simp [hy, hz]
  have hcodegGram (y z : Fin N) :
      codeg E G μ y z = ∑ x, μ.w x * hit E G x y * hit E G x z := by
    unfold codeg
    apply Finset.sum_congr rfl
    intro x hx
    rw [← hHitProd x y z]
    ring
  have hcodegDiag (y : Fin N) : codeg E G μ y y ≤ 1 := by
    rw [hcodegGram]
    calc
      (∑ x, μ.w x * hit E G x y * hit E G x y) ≤ ∑ x, μ.w x * 1 := by
        apply Finset.sum_le_sum
        intro x hx
        calc
          μ.w x * hit E G x y * hit E G x y =
              μ.w x * (hit E G x y * hit E G x y) := by ring
          _ ≤ μ.w x * 1 := by
            apply mul_le_mul_of_nonneg_left _ (μ.nonneg x)
            unfold hit
            split_ifs <;> norm_num
      _ = 1 := by simp [μ.sum_eq_one]
  have hPairExpansion (A : Finset (Fin N)) :
      (∑ x, μ.w x * (∑ y ∈ A, hit E G x y) ^ 2) =
        ∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z := by
    have hsumProd (x : Fin N) :
        (∑ y ∈ A, hit E G x y) ^ 2 =
          ∑ y ∈ A, ∑ z ∈ A, hit E G x y * hit E G x z := by
      calc
        (∑ y ∈ A, hit E G x y) ^ 2 =
            (∑ y ∈ A, hit E G x y) * (∑ z ∈ A, hit E G x z) := by ring
        _ = ∑ y ∈ A, hit E G x y * (∑ z ∈ A, hit E G x z) := by rw [Finset.sum_mul]
        _ = ∑ y ∈ A, ∑ z ∈ A, hit E G x y * hit E G x z := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Finset.mul_sum]
    calc
      (∑ x, μ.w x * (∑ y ∈ A, hit E G x y) ^ 2) =
          ∑ x, μ.w x * (∑ y ∈ A, ∑ z ∈ A, hit E G x y * hit E G x z) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hsumProd]
      _ = ∑ y ∈ A, ∑ z ∈ A, ∑ x, μ.w x * hit E G x y * hit E G x z := by
            calc
              _ = ∑ x, ∑ y ∈ A, ∑ z ∈ A,
                    μ.w x * hit E G x y * hit E G x z := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro y hy
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro z hz
                      ring
              _ = ∑ y ∈ A, ∑ x, ∑ z ∈ A,
                    μ.w x * hit E G x y * hit E G x z := by rw [Finset.sum_comm]
              _ = ∑ y ∈ A, ∑ z ∈ A, ∑ x,
                    μ.w x * hit E G x y * hit E G x z := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      rw [Finset.sum_comm]
      _ = ∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z := by
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro z hz
            rw [hcodegGram]
  have ht₀pos : 0 < t₀ := by norm_num [t₀, q_s11_compat_t₀]
  have ht₀recip : 1 / (t₀ : ℝ) < etaC / 1000 :=
    by norm_num [t₀, q_s11_compat_t₀, etaC]
  have hprojectionGap : 1 / 4 + etaC / 1000 + 1 / (t₀ : ℝ) <
      (1 / 2 + etaC / 200) ^ 2 := by norm_num [t₀, q_s11_compat_t₀, etaC]
  have hnoIndependent (i : ι) (hi : i ∈ NormGood) (A : Finset (Fin N))
      (hA : A ⊆ selected i) (hcard : A.card = t₀)
      (hpair : ∀ y ∈ A, ∀ z ∈ A, y ≠ z →
        codeg E G μ y z < 1 / 4 + (n : ℝ) ^ (-δ)) : False := by
    let m : ℝ := (A.card : ℝ)
    let C : ℝ := 1 / 4 + (n : ℝ) ^ (-δ)
    have hmEq : m = (t₀ : ℝ) := by
      dsimp [m]
      exact_mod_cast hcard
    have hmCard : m = (A.card : ℝ) := rfl
    have hmpos : 0 < m := by rw [hmEq]; exact_mod_cast ht₀pos
    have hmomentPos : 0 < tagMoment i := by
      have h := (Finset.mem_filter.mp hi).2
      linarith [heta]
    let sumHit (x : Fin N) : ℝ := ∑ y ∈ A, hit E G x y
    have hinnerSum :
        (∑ x, μ.w x * sumHit x * deg E G (π i) x) = ∑ y ∈ A, inner i y := by
      calc
        (∑ x, μ.w x * sumHit x * deg E G (π i) x) =
            ∑ x, ∑ y ∈ A, μ.w x * hit E G x y * deg E G (π i) x := by
              apply Finset.sum_congr rfl
              intro x hx
              dsimp [sumHit]
              rw [Finset.mul_sum, Finset.sum_mul]
        _ = ∑ y ∈ A, ∑ x, μ.w x * hit E G x y * deg E G (π i) x := by
              rw [Finset.sum_comm]
        _ = ∑ y ∈ A, inner i y := by
              apply Finset.sum_congr rfl
              intro y hy
              rfl
    have hinnerLower (y : Fin N) (hy : y ∈ A) :
        (1 / 2 + etaC / 200) * norm i < inner i y := by
      have hproj : 1 / 2 + etaC / 200 < projection i y :=
        (Finset.mem_filter.mp (hA hy)).2
      dsimp [projection] at hproj
      exact (lt_div_iff₀ (hnormPos i hi)).mp hproj
    have hsumInnerLower : m * (1 / 2 + etaC / 200) * norm i <
        ∑ y ∈ A, inner i y := by
      have hsum : (∑ y ∈ A, (1 / 2 + etaC / 200) * norm i) <
          ∑ y ∈ A, inner i y := by
        apply Finset.sum_lt_sum
        · intro y hy
          exact (hinnerLower y hy).le
        · obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hcard]; exact ht₀pos)
          exact ⟨y, hy, hinnerLower y hy⟩
      have hconst : (∑ y ∈ A, (1 / 2 + etaC / 200) * norm i) =
          m * ((1 / 2 + etaC / 200) * norm i) := by simp [m]
      rw [hconst] at hsum
      nlinarith [hsum]
    have hPairTotal :
        (∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z) ≤ m ^ 2 * C + m := by
      have hcodegPoint (y z : Fin N) (hy : y ∈ A) (hz : z ∈ A) :
          codeg E G μ y z ≤ C + if y = z then (1 : ℝ) else 0 := by
        by_cases hyz : y = z
        · subst z
          have hdiag := hcodegDiag y
          have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
          have hone : 1 ≤ C + 1 := by linarith [hCnonneg]
          simpa using hdiag.trans hone
        · have h := hpair y hy z hz hyz
          simp [hyz, C]
          nlinarith [h]
      have hinnerPair (y : Fin N) (hy : y ∈ A) :
          (∑ z ∈ A, (C + if y = z then (1 : ℝ) else 0)) = m * C + 1 := by
        rw [Finset.sum_add_distrib]
        have hconst : (∑ z ∈ A, C) = m * C := by simp [m]
        have hdelta : (∑ z ∈ A, if y = z then (1 : ℝ) else 0) = 1 := by
          rw [Finset.sum_ite_eq A y (fun _ => (1 : ℝ))]
          exact if_pos hy
        rw [hconst, hdelta]
      calc
        (∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z) ≤
            ∑ y ∈ A, ∑ z ∈ A, (C + if y = z then (1 : ℝ) else 0) := by
              apply Finset.sum_le_sum
              intro y hy
              apply Finset.sum_le_sum
              intro z hz
              exact hcodegPoint y z hy hz
        _ = m * (m * C + 1) := by
              calc
                (∑ y ∈ A, ∑ z ∈ A, (C + if y = z then (1 : ℝ) else 0)) =
                    ∑ y ∈ A, (m * C + 1) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      exact hinnerPair y hy
                _ = (A.card : ℝ) * (m * C + 1) := by simp; ring
                _ = m * (m * C + 1) := by rw [← hmCard]
        _ = m ^ 2 * C + m := by ring
    have hcs :
        (∑ x, μ.w x * sumHit x * deg E G (π i) x) ^ 2 ≤
          (∑ x, μ.w x * (sumHit x) ^ 2) * tagMoment i := by
      simpa [sumHit, tagMoment] using
        hweightedCS (fun x => ∑ y ∈ A, hit E G x y) (fun x => deg E G (π i) x)
    have hcsLower :
        (m * (1 / 2 + etaC / 200) * norm i) ^ 2 <
          (∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z) * tagMoment i := by
      calc
        (m * (1 / 2 + etaC / 200) * norm i) ^ 2 <
            (∑ x, μ.w x * sumHit x * deg E G (π i) x) ^ 2 := by
              rw [hinnerSum]
              have hleft : 0 ≤ m * (1 / 2 + etaC / 200) * norm i := by positivity
              have hleftPos : 0 < m * (1 / 2 + etaC / 200) * norm i := by positivity
              have hright : 0 ≤ ∑ y ∈ A, inner i y :=
                (le_of_lt (lt_trans hleftPos hsumInnerLower))
              exact (sq_lt_sq₀ hleft hright).2 hsumInnerLower
        _ ≤ (∑ x, μ.w x * (sumHit x) ^ 2) * tagMoment i := hcs
        _ = (∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z) * tagMoment i := by
              rw [hPairExpansion]
    have hmul :
        (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) * tagMoment i <
          (m ^ 2 * C + m) * tagMoment i := by
      have hroot : norm i ^ 2 = tagMoment i := by
        dsimp [norm]
        exact Real.sq_sqrt (htagMomentBounds i).1
      have hsq :
          (m * (1 / 2 + etaC / 200) * norm i) ^ 2 =
            (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) * tagMoment i := by
        calc
          (m * (1 / 2 + etaC / 200) * norm i) ^ 2 =
              (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) * norm i ^ 2 := by ring
          _ = (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) * tagMoment i := by rw [hroot]
      calc
        (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) * tagMoment i =
            (m * (1 / 2 + etaC / 200) * norm i) ^ 2 := hsq.symm
        _ < (∑ y ∈ A, ∑ z ∈ A, codeg E G μ y z) * tagMoment i := hcsLower
        _ ≤ (m ^ 2 * C + m) * tagMoment i :=
              mul_le_mul_of_nonneg_right hPairTotal (le_of_lt hmomentPos)
    have hcoeff : m ^ 2 * (1 / 2 + etaC / 200) ^ 2 < m ^ 2 * C + m :=
      (mul_lt_mul_iff_of_pos_right hmomentPos).mp hmul
    have hratio : (1 / 2 + etaC / 200) ^ 2 < C + 1 / m := by
      have hmulEq : m ^ 2 * (C + 1 / m) = m ^ 2 * C + m := by
        field_simp [ne_of_gt hmpos]
        <;> ring
      have hcoeff' : m ^ 2 * (1 / 2 + etaC / 200) ^ 2 <
          m ^ 2 * (C + 1 / m) := by rw [hmulEq]; exact hcoeff
      have hmSq : 0 < m ^ 2 := sq_pos_of_pos hmpos
      have hdiv : (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) / m ^ 2 < C + 1 / m := by
        apply (div_lt_iff₀ hmSq).2
        nlinarith [hcoeff']
      have hcancel :
          (m ^ 2 * (1 / 2 + etaC / 200) ^ 2) / m ^ 2 = (1 / 2 + etaC / 200) ^ 2 := by
        field_simp [ne_of_gt hmSq]
      rw [hcancel] at hdiv
      exact hdiv
    have hC : C < 1 / 4 + etaC / 1000 := by
      dsimp [C]
      linarith [hpowSmall]
    have hminv : 1 / m = 1 / (t₀ : ℝ) := by rw [hmEq]
    nlinarith [hratio, hprojectionGap, hC, hminv]
  let HighTags := {i : ι // i ∈ NormGood}
  have hnormGoodMassPos : 0 < normGoodMass :=
    lt_trans (by positivity : (0 : ℝ) < etaC / 100) hnormGoodMass
  let tagPrior : FinProb HighTags := {
    w := fun i => p.w i.1 / normGoodMass
    nonneg := by
      intro i
      exact div_nonneg (p.nonneg i.1) hnormGoodMassPos.le
    sum_eq_one := by
      have hUnivSubtype :
          (Finset.univ : Finset HighTags) =
            Finset.subtype (fun i : ι => i ∈ NormGood) (Finset.univ : Finset ι) := by
        ext i
        simp [HighTags]
      have hsubtype : (∑ i : HighTags, p.w i.1) = normGoodMass := by
        change (∑ i ∈ (Finset.univ : Finset HighTags), p.w i.1) = normGoodMass
        rw [hUnivSubtype, Finset.sum_subtype_eq_sum_filter]
        simp [normGoodMass, NormGood]
      calc
        (∑ i : HighTags, p.w i.1 / normGoodMass) =
            ∑ i : HighTags, p.w i.1 * normGoodMass⁻¹ := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i : HighTags, p.w i.1) * normGoodMass⁻¹ := by rw [← Finset.sum_mul]
        _ = 1 := by
              rw [hsubtype]
              field_simp [ne_of_gt hnormGoodMassPos]
  }
  let πlaw (i : ι) : Law N := ⟨π i, hπnonneg i, hπsum i⟩
  have hselectedPositive (i : HighTags) :
      0 < ∑ y ∈ selected i.1, (πlaw i.1).w y := by
    change 0 < selectedMass i.1
    exact lt_trans (by positivity : (0 : ℝ) < etaC / 1000)
      (hselectedMass i.1 i.2)
  let rho (i : HighTags) : Law N :=
    Law.restrict (πlaw i.1) (selected i.1) (hselectedPositive i)
  have hrhoSupport (i : HighTags) : (rho i).SupportedIn (selected i.1) := by
    intro y hy
    simp [rho, Law.restrict, hy]
  have hrhoY (i : HighTags) : (rho i).SupportedIn Y := by
    intro y hy
    by_contra hρzero
    have hsel : y ∈ selected i.1 := by
      by_contra hnot
      exact hρzero (hrhoSupport i y hnot)
    have hπne : (πlaw i.1).w y ≠ 0 := by
      intro hzero
      exact hρzero (by simp [rho, Law.restrict, hsel, hzero])
    exact hy (hπsupp i.1 y (by simpa [πlaw] using hπne))
  have hrhoCap (i : HighTags) (y : Fin N) :
      (N : ℝ) * (rho i).w y ≤ (1000 / etaC) * Real.exp ((n : ℝ) / 50) := by
    by_cases hy : y ∈ selected i.1
    · have hmass := hselectedMass i.1 i.2
      have hq : 0 < selectedMass i.1 := lt_trans (by positivity) hmass
      have hrecip0 : 1 / selectedMass i.1 ≤ 1 / (etaC / 1000) :=
        one_div_le_one_div_of_le (by positivity) (le_of_lt hmass)
      have hrecip : 1 / selectedMass i.1 ≤ 1000 / etaC := by
        calc
          1 / selectedMass i.1 ≤ 1 / (etaC / 1000) := hrecip0
          _ = 1000 / etaC := by field_simp [ne_of_gt heta]
      have hcap := hπcap i.1 y
      have hrhow : (rho i).w y = π i.1 y / selectedMass i.1 := by
        simp [rho, Law.restrict, πlaw, hy, selectedMass]
      rw [hrhow]
      calc
        (N : ℝ) * (π i.1 y / selectedMass i.1) =
            ((N : ℝ) * π i.1 y) / selectedMass i.1 := by ring
        _ ≤ Real.exp ((n : ℝ) / 50) / selectedMass i.1 :=
              div_le_div_of_nonneg_right hcap hq.le
        _ = Real.exp ((n : ℝ) / 50) * (1 / selectedMass i.1) := by ring
        _ ≤ Real.exp ((n : ℝ) / 50) * (1000 / etaC) :=
              mul_le_mul_of_nonneg_left hrecip (Real.exp_pos _).le
        _ = (1000 / etaC) * Real.exp ((n : ℝ) / 50) := by ring
    · have hzero : (rho i).w y = 0 := by simp [rho, Law.restrict, hy]
      rw [hzero]
      have hRpos : 0 < (1000 / etaC) * Real.exp ((n : ℝ) / 50) :=
        mul_pos (by positivity) (Real.exp_pos _)
      simpa using hRpos.le
  have hcodegSymm (y z : Fin N) : codeg E G μ y z = codeg E G μ z y := by
    rw [hcodegGram, hcodegGram]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hsCpos : 0 < sC n := by
    dsimp [sC]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  obtain ⟨k₀, hk₀⟩ := HypercubeRamsey.S11.Core.q_s11_compat_pred_exists t₀
  have hRamseyBound : Nat.choose (sC n + t₀ - 2) (sC n - 1) ≤
      (sC n + t₀ - 2) ^ k₀ := by
    have hnR : sC n + t₀ - 2 = (sC n - 1) + k₀ := by omega
    rw [Nat.choose_symm_of_eq_add hnR]
    exact Nat.choose_le_pow (sC n + t₀ - 2) k₀
  have hsampleClique (i : HighTags) (r : ℕ) (z : Fin r → Fin N)
      (hzInjective : Function.Injective z)
      (hzSelected : ∀ j, z j ∈ selected i.1)
      (hR : Nat.choose (sC n + t₀ - 2) (sC n - 1) ≤ r) :
      ∃ C : Finset (Fin r), C.card = sC n ∧
        ∀ j ∈ C, ∀ k ∈ C, j ≠ k →
          1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k) := by
    let H : SimpleGraph (Fin r) := {
      Adj := fun j k => j ≠ k ∧
        1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k)
      symm := Std.Symm.mk (by
        intro j k h
        exact ⟨h.1.symm, by simpa [hcodegSymm] using h.2⟩)
      loopless := Std.Irrefl.mk (by
        intro j h
        exact h.1 rfl)
    }
    have hs : 1 ≤ sC n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hsCpos)
    have ht : 1 ≤ t₀ := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ht₀pos)
    rcases xRamseyBinom H (sC n) t₀ hs ht (by simpa using hR) with hclique | hindep
    · rcases hclique with ⟨C, hCcard, hCedge⟩
      refine ⟨C, hCcard, ?_⟩
      intro j hj k hk hjk
      exact (hCedge j hj k hk hjk).2
    · rcases hindep with ⟨A, hAcard, hAnoAdj⟩
      let labels : Finset (Fin N) := A.image z
      have hlabelsCard : labels.card = t₀ := by
        dsimp [labels]
        rw [Finset.card_image_of_injective _ hzInjective, hAcard]
      have hlabelsSub : labels ⊆ selected i.1 := by
        intro y hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        exact hzSelected j
      have hlabelsPair : ∀ y ∈ labels, ∀ w ∈ labels, y ≠ w →
          codeg E G μ y w < 1 / 4 + (n : ℝ) ^ (-δ) := by
        intro y hy w hw hyw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        have hjk : j ≠ k := by
          intro heq
          exact hyw (congrArg z heq)
        have hnot := hAnoAdj j hj k hk hjk
        have hnotle : ¬ 1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k) := by
          intro hedge
          exact hnot ⟨hjk, hedge⟩
        exact lt_of_not_ge hnotle
      exact False.elim (hnoIndependent i.1 i.2 labels hlabelsSub hlabelsCard hlabelsPair)
  have hsamplePacking (i : HighTags) (r : ℕ) (z : Fin r → Fin N)
      (hzInjective : Function.Injective z)
      (hzSelected : ∀ j, z j ∈ selected i.1)
      (hR : Nat.choose (sC n + t₀ - 2) (sC n - 1) ≤ r) :
      ∃ P : Finset (Finset (Fin r)), ∃ V : Finset (Fin r),
        (∀ C ∈ P, C.card = sC n ∧
          ∀ j ∈ C, ∀ k ∈ C, j ≠ k →
            1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k)) ∧
        (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
        V = P.biUnion id ∧
        (Finset.univ \ V).card < Nat.choose (sC n + t₀ - 2) (sC n - 1) := by
    let IsClique (C : Finset (Fin r)) : Prop :=
      C.card = sC n ∧
        ∀ j ∈ C, ∀ k ∈ C, j ≠ k →
          1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k)
    let Cliques : Finset (Finset (Fin r)) := Finset.univ.filter IsClique
    let IsPacking (P : Finset (Finset (Fin r))) : Prop :=
      (∀ C ∈ P, C ∈ Cliques) ∧
        ∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D
    let Packings : Finset (Finset (Finset (Fin r))) := Finset.univ.filter IsPacking
    have hPackings : Packings.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [Packings, IsPacking]
    obtain ⟨P, hPmem, hPmax⟩ := Finset.exists_max_image Packings Finset.card hPackings
    have hP : IsPacking P := (Finset.mem_filter.mp hPmem).2
    let V : Finset (Fin r) := P.biUnion id
    have hNoClique : ∀ C, C ⊆ Finset.univ \ V → C.card = sC n →
        ¬ (∀ j ∈ C, ∀ k ∈ C, j ≠ k →
          1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k)) := by
      intro C hC hCcard hEdges
      have hCis : IsClique C := ⟨hCcard, hEdges⟩
      have hCmem : C ∈ Cliques := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCis⟩
      have hCne : C.Nonempty := Finset.card_pos.mp (by rw [hCcard]; exact hsCpos)
      have hCnotP : C ∉ P := by
        intro hCP
        obtain ⟨j, hj⟩ := hCne
        have hjV : j ∈ V := Finset.mem_biUnion.mpr ⟨C, hCP, hj⟩
        exact (Finset.mem_sdiff.mp (hC hj)).2 hjV
      have hCdisj (D : Finset (Fin r)) (hDP : D ∈ P) : Disjoint C D := by
        have hDsub : D ⊆ V := by
          intro j hj
          exact Finset.mem_biUnion.mpr ⟨D, hDP, hj⟩
        apply Finset.disjoint_left.mpr
        intro j hjC hjD
        exact (Finset.mem_sdiff.mp (hC hjC)).2 (hDsub hjD)
      have hP' : IsPacking (insert C P) := by
        refine ⟨?_, ?_⟩
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hDP
          · exact hCmem
          · exact hP.1 D hDP
        · intro D hD D' hD' hne
          rcases Finset.mem_insert.mp hD with rfl | hDP
          · rcases Finset.mem_insert.mp hD' with rfl | hD'P
            · exact (hne rfl).elim
            · exact hCdisj D' hD'P
          · rcases Finset.mem_insert.mp hD' with rfl | hD'P
            · exact (hCdisj D hDP).symm
            · exact hP.2 D hDP D' hD'P hne
      have hP'mem : insert C P ∈ Packings :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩
      have hmax := hPmax (insert C P) hP'mem
      have hcardInsert : (insert C P).card = P.card + 1 :=
        Finset.card_insert_of_notMem hCnotP
      omega
    have hLeftLess : (Finset.univ \ V).card <
        Nat.choose (sC n + t₀ - 2) (sC n - 1) := by
      by_contra hnot
      have hLeftLarge : Nat.choose (sC n + t₀ - 2) (sC n - 1) ≤ (Finset.univ \ V).card :=
        le_of_not_gt hnot
      let L : Finset (Fin r) := Finset.univ \ V
      let e : {j : Fin r // j ∈ L} ≃ Fin L.card := L.equivFin
      let zL : Fin L.card → Fin N := fun j => z (e.symm j).1
      have hzLinj : Function.Injective zL := by
        intro a b hab
        have hval : (e.symm a).1 = (e.symm b).1 := hzInjective hab
        have hsub : e.symm a = e.symm b := Subtype.ext hval
        exact e.symm.injective hsub
      have hzLselected : ∀ j, zL j ∈ selected i.1 := fun j => hzSelected _
      obtain ⟨C, hCcard, hCedge⟩ := hsampleClique i L.card zL hzLinj hzLselected hLeftLarge
      let C' : Finset (Fin r) := C.image fun j => (e.symm j).1
      have himageInj : Function.Injective (fun j : Fin L.card => (e.symm j).1) := by
        intro a b hab
        exact e.symm.injective (Subtype.ext hab)
      have hC'card : C'.card = sC n := by
        dsimp [C']
        rw [Finset.card_image_of_injective _ himageInj, hCcard]
      have hC'sub : C' ⊆ L := by
        intro j hj
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        exact (e.symm k).2
      have hC'edge : ∀ j ∈ C', ∀ k ∈ C', j ≠ k →
          1 / 4 + (n : ℝ) ^ (-δ) ≤ codeg E G μ (z j) (z k) := by
        intro j hj k hk hjk
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
        have hab : a ≠ b := by
          intro hab
          exact hjk (congrArg (fun c => (e.symm c).1) hab)
        simpa [zL] using hCedge a ha b hb hab
      have hC'sub' : C' ⊆ Finset.univ \ V := by simpa [L] using hC'sub
      exact hNoClique C' hC'sub' hC'card hC'edge
    refine ⟨P, V, ?_, hP.2, rfl, hLeftLess⟩
    intro C hC
    exact (Finset.mem_filter.mp (hP.1 C hC)).2
  let productRow (i : HighTags) (r : ℕ) : FinProb (Fin r → Fin N) :=
    FinProb.pi (fun _ : Fin r => rho i)
  have hcoordinateExpect (i : HighTags) (r : ℕ) (j : Fin r) (f : Fin N → ℝ) :
      (productRow i r).expect (fun z => f (z j)) = (rho i).expect f := by
    classical
    let S : Finset (Fin r) := {j}
    let j₀ : {k // k ∈ S} := ⟨j, by simp [S]⟩
    have hdefault : (default : {k // k ∈ S}) = j₀ := by
      apply Subtype.ext
      simp [S, j₀]
    let g : (∀ k : {k // k ∈ S}, Fin N) → ℝ := fun q => f (q j₀)
    let e : (∀ k : {k // k ∈ S}, Fin N) ≃ Fin N := {
      toFun := fun q => q j₀
      invFun := fun y _ => y
      left_inv := by
        intro q
        funext k
        have hkMem : k.1 ∈ ({j} : Finset (Fin r)) := k.2
        have hk : k = j₀ := Subtype.ext (Finset.mem_singleton.mp hkMem)
        exact congrArg q hk.symm
      right_inv := by intro y; rfl
    }
    have h := FinProb.pi_marginal_expect (fun _ : Fin r => rho i) S g
    calc
      (productRow i r).expect (fun z => f (z j)) =
          (FinProb.pi (fun _ : {k // k ∈ S} => rho i)).expect g := by
            simpa [productRow, S, g, j₀] using h
      _ = (rho i).expect f := by
            unfold FinProb.expect
            exact Fintype.sum_equiv e _ _ (by
              intro q
              have hq : q default = q j₀ := congrArg q hdefault
              simpa [FinProb.pi, g, e, hq])
  have hpairCollision (i : HighTags) (r : ℕ) (j k : Fin r) (hjk : j ≠ k) :
      (productRow i r).pr (fun z => z j = z k) ≤
        (1000 / etaC) * Real.exp ((n : ℝ) / 50) / N := by
    classical
    let Q := productRow i r
    have hPrIndicator {Ω : Type} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
        P.pr A = P.expect (fun x => if A x then (1 : ℝ) else 0) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : A x <;> simp [h]
    have hsingleLaw (P : Law N) (y : Fin N) :
        P.expect (fun x => if x = y then (1 : ℝ) else 0) = P.w y := by
      unfold FinProb.expect
      rw [Fintype.sum_eq_single y]
      · simp
      · intro x hxy
        simp [hxy]
    let f (y : Fin N) (z : Fin r → Fin N) : ℝ := if z j = y then 1 else 0
    let g (y : Fin N) (z : Fin r → Fin N) : ℝ := if z k = y then 1 else 0
    let collision : (Fin r → Fin N) → Prop := fun z => z j = z k
    letI : DecidablePred collision := fun z => Classical.propDecidable (collision z)
    have hdecomp (z : Fin r → Fin N) :
        (if collision z then (1 : ℝ) else 0) = ∑ y, f y z * g y z := by
      by_cases h : z j = z k
      · have hsum : (∑ y, f y z * g y z) = 1 := by
          calc
            (∑ y, f y z * g y z) = ∑ y, if z j = y then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro y hy
              simp [f, g, h]
            _ = 1 := by simp
        have hc : collision z := h
        rw [if_pos hc]
        exact hsum.symm
      · have hsum : (∑ y, f y z * g y z) = 0 := by
          apply Finset.sum_eq_zero
          intro y hy
          by_cases h₁ : z j = y
          · have h₂ : z k ≠ y := by
              intro h₂
              exact h (h₁.trans h₂.symm)
            simp [f, g, h₁, h₂]
          · simp [f, g, h₁]
        have hc : ¬ collision z := h
        rw [if_neg hc]
        exact hsum.symm
    have hfactor (y : Fin N) :
        Q.expect (fun z => f y z * g y z) = (rho i).w y ^ 2 := by
      have hfdep : FinProb.DependsOn (f y) {j} := by
        intro z z' hz
        have hzj := hz j (by simp)
        simp [f, hzj]
      have hgdep : FinProb.DependsOn (g y) {k} := by
        intro z z' hz
        have hzk := hz k (by simp)
        simp [g, hzk]
      have hdisj : Disjoint ({j} : Finset (Fin r)) {k} := by
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        simp at hx hx'
        exact hjk (hx.symm.trans hx')
      have h := FinProb.pi_expect_mul_of_disjoint (fun _ : Fin r => rho i)
        (f y) (g y) {j} {k} hfdep hgdep hdisj
      have hf : Q.expect (f y) = (rho i).w y := by
        calc
          Q.expect (f y) =
              (rho i).expect (fun x => if x = y then (1 : ℝ) else 0) := by
                simpa [f] using hcoordinateExpect i r j (fun x => if x = y then (1 : ℝ) else 0)
          _ = (rho i).w y := hsingleLaw (rho i) y
      have hg : Q.expect (g y) = (rho i).w y := by
        calc
          Q.expect (g y) =
              (rho i).expect (fun x => if x = y then (1 : ℝ) else 0) := by
                simpa [g] using hcoordinateExpect i r k (fun x => if x = y then (1 : ℝ) else 0)
          _ = (rho i).w y := hsingleLaw (rho i) y
      have hfactored : Q.expect (fun z => f y z * g y z) =
          Q.expect (f y) * Q.expect (g y) := by simpa [Q] using h
      rw [hfactored, hf, hg]
      ring
    have heq : Q.pr collision =
        ∑ y, Q.expect (fun z => f y z * g y z) := by
      rw [hPrIndicator]
      calc
        Q.expect (fun z => if collision z then (1 : ℝ) else 0) =
            Q.expect (fun z => ∑ y, f y z * g y z) := by
              have hfun : (fun z => if collision z then (1 : ℝ) else 0) =
                  (fun z => ∑ y, f y z * g y z) := by
                funext z
                simpa only [hdecomp z]
              rw [hfun]
        _ = ∑ y, Q.expect (fun z => f y z * g y z) := by
              unfold FinProb.expect
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro y hy
              rw [Finset.mul_sum]
    rw [heq]
    calc
      (∑ y, Q.expect (fun z => f y z * g y z)) = ∑ y, (rho i).w y ^ 2 := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hfactor y
      _ ≤ ∑ y, (rho i).w y * ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) := by
        apply Finset.sum_le_sum
        intro y hy
        have hAtom : (rho i).w y ≤
            (1000 / etaC) * Real.exp ((n : ℝ) / 50) / N := by
          apply (le_div_iff₀ hNr).2
          simpa [mul_comm] using hrhoCap i y
        calc
          (rho i).w y ^ 2 = (rho i).w y * (rho i).w y := by ring
          _ ≤ (rho i).w y * ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) :=
            mul_le_mul_of_nonneg_left hAtom ((rho i).nonneg y)
      _ = (1000 / etaC) * Real.exp ((n : ℝ) / 50) / N := by
        rw [← Finset.sum_mul, (rho i).sum_eq_one]
        ring
  have hrowUnique (i : HighTags) (r : ℕ)
      (hbudget : (r : ℝ) ^ 2 * ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) ≤ 1 / 2) :
      1 / 2 ≤ (productRow i r).pr (fun z => Function.Injective z) := by
    classical
    let Q := productRow i r
    let Pairs : Finset (Fin r × Fin r) := Finset.univ.filter fun q => q.1 ≠ q.2
    let collisionCount (z : Fin r → Fin N) : ℝ :=
      ∑ q ∈ Pairs, if z q.1 = z q.2 then (1 : ℝ) else 0
    have hPrIndicator {Ω : Type} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
        P.pr A = P.expect (fun x => if A x then (1 : ℝ) else 0) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : A x <;> simp [h]
    have hcollisionExists (z : Fin r → Fin N) (hnon : ¬ Function.Injective z) :
        ∃ q ∈ Pairs, z q.1 = z q.2 := by
      by_contra hnone
      apply hnon
      intro j k hEq
      by_contra hjk
      exact hnone ⟨(j, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjk⟩, hEq⟩
    have hcountZero (z : Fin r → Fin N) (hinj : Function.Injective z) :
        collisionCount z = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hneq : z q.1 ≠ z q.2 := by
        intro hEq
        exact (Finset.mem_filter.mp hq).2 (hinj hEq)
      simp [collisionCount, hneq]
    have hcountLower (z : Fin r → Fin N) (hnon : ¬ Function.Injective z) :
        1 ≤ collisionCount z := by
      obtain ⟨q, hq, hEq⟩ := hcollisionExists z hnon
      have hsingleton :
          (∑ q' ∈ ({q} : Finset (Fin r × Fin r)),
            if z q'.1 = z q'.2 then (1 : ℝ) else 0) = 1 := by
        rw [Finset.sum_singleton]
        simp [hEq]
      have hle :
          (∑ q' ∈ ({q} : Finset (Fin r × Fin r)),
            if z q'.1 = z q'.2 then (1 : ℝ) else 0) ≤
          ∑ q' ∈ Pairs, if z q'.1 = z q'.2 then (1 : ℝ) else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr hq) (by
              intro q' hq' hnot
              split_ifs <;> positivity)
      simpa [collisionCount, hsingleton] using hle
    have hpoint (z : Fin r → Fin N) :
        1 ≤ (if Function.Injective z then (1 : ℝ) else 0) + collisionCount z := by
      by_cases hinj : Function.Injective z
      · simp [hinj, hcountZero z hinj]
      · simp [hinj]
        linarith [hcountLower z hinj]
    have hpairCount : (Pairs.card : ℝ) ≤ (r : ℝ) ^ 2 := by
      have hnat : Pairs.card ≤ (Finset.univ : Finset (Fin r × Fin r)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hreal : (Pairs.card : ℝ) ≤ (r * r : ℕ) := by
        exact_mod_cast (by simpa using hnat : Pairs.card ≤ r * r)
      calc
        (Pairs.card : ℝ) ≤ (r * r : ℕ) := hreal
        _ = (r : ℝ) ^ 2 := by simp [pow_two]
    have hcollisionExpect :
        Q.expect collisionCount =
          ∑ q ∈ Pairs, Q.pr (fun z => z q.1 = z q.2) := by
      unfold FinProb.expect collisionCount
      calc
        (∑ z, Q.w z * ∑ q ∈ Pairs, if z q.1 = z q.2 then (1 : ℝ) else 0) =
            ∑ q ∈ Pairs, ∑ z, Q.w z * (if z q.1 = z q.2 then (1 : ℝ) else 0) := by
              calc
                _ = ∑ z, ∑ q ∈ Pairs, Q.w z * (if z q.1 = z q.2 then (1 : ℝ) else 0) := by
                      apply Finset.sum_congr rfl
                      intro z hz
                      rw [Finset.mul_sum]
                _ = ∑ q ∈ Pairs, ∑ z, Q.w z *
                      (if z q.1 = z q.2 then (1 : ℝ) else 0) := by rw [Finset.sum_comm]
        _ = ∑ q ∈ Pairs, Q.pr (fun z => z q.1 = z q.2) := by
              apply Finset.sum_congr rfl
              intro q hq
              simpa [FinProb.expect] using
                (hPrIndicator Q (fun z => z q.1 = z q.2)).symm
    have hcollisionBound : Q.expect collisionCount ≤ 1 / 2 := by
      calc
        Q.expect collisionCount =
            ∑ q ∈ Pairs, Q.pr (fun z => z q.1 = z q.2) := hcollisionExpect
        _ ≤ ∑ q ∈ Pairs,
              ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) := by
                apply Finset.sum_le_sum
                intro q hq
                exact hpairCollision i r q.1 q.2 (Finset.mem_filter.mp hq).2
        _ = (Pairs.card : ℝ) *
              ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) := by simp
        _ ≤ (r : ℝ) ^ 2 *
              ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) :=
                mul_le_mul_of_nonneg_right hpairCount (by positivity)
        _ ≤ 1 / 2 := hbudget
    have htotal := FinProb.expect_mono Q hpoint
    have htotal'' : 1 ≤ Q.expect
        (fun z => if Function.Injective z then (1 : ℝ) else 0) +
        Q.expect collisionCount := by
      calc
        1 = Q.expect (fun _ => (1 : ℝ)) := by simp [FinProb.expect_const]
        _ ≤ Q.expect (fun z =>
              (if Function.Injective z then (1 : ℝ) else 0) + collisionCount z) := htotal
        _ = Q.expect (fun z => if Function.Injective z then (1 : ℝ) else 0) +
              Q.expect collisionCount := FinProb.expect_add Q _ _
    have hI' : Q.expect (fun z => if Function.Injective z then (1 : ℝ) else 0) =
        Q.pr (fun z => Function.Injective z) := by
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : Function.Injective z <;> simp [h]
    have htotal' : 1 ≤ Q.pr (fun z => Function.Injective z) +
        Q.expect collisionCount := by
      calc
        1 ≤ Q.expect (fun z => if Function.Injective z then (1 : ℝ) else 0) +
            Q.expect collisionCount := htotal''
        _ = Q.pr (fun z => Function.Injective z) + Q.expect collisionCount :=
            congrArg (fun x : ℝ => x + Q.expect collisionCount) hI'
    linarith [htotal', hcollisionBound]
  let x : ℝ := (n : ℝ) ^ ((1 : ℝ) / 100)
  have hExpLargeX : (t₀ : ℝ) + 1 ≤ Real.exp x := by simpa [x] using hExpLarge'
  have hnRealPos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hpowRel : (n : ℝ) ^ ((1 : ℝ) / 100) / n = (n : ℝ) ^ (-(99 / 100 : ℝ)) := by
    rw [← Real.rpow_sub_one (ne_of_gt hnRealPos) ((1 : ℝ) / 100)]
    congr 1
    ring
  have hsmallLinear : 2 * (t₀ : ℝ) * x < (n : ℝ) / 100 := by
    have hratio : 2 * (t₀ : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 100) / n) < 1 / 100 := by
      rw [hpowRel]
      exact hsmallRatio'
    have hmul := mul_lt_mul_of_pos_right hratio hnRealPos
    have hmulEq :
        (2 * (t₀ : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 100) / n)) * n =
          2 * (t₀ : ℝ) * x := by
      dsimp [x]
      field_simp [ne_of_gt hnRealPos]
    calc
      2 * (t₀ : ℝ) * x =
          (2 * (t₀ : ℝ) * ((n : ℝ) ^ ((1 : ℝ) / 100) / n)) * n := hmulEq.symm
      _ < (1 / 100) * n := hmul
      _ = (n : ℝ) / 100 := by ring
  have hsCeil : (sC n : ℝ) < Real.exp x + 1 := by
    change (Nat.ceil (Real.exp x) : ℝ) < Real.exp x + 1
    exact Nat.ceil_lt_add_one (Real.exp_pos x).le
  let b : ℕ := sC n + t₀ - 2
  have hbLE : b ≤ sC n + t₀ := by dsimp [b]; exact Nat.sub_le _ _
  have hbaseLt : (b : ℝ) < 2 * Real.exp x := by
    calc
      (b : ℝ) ≤ ((sC n + t₀ : ℕ) : ℝ) := Nat.cast_le.mpr hbLE
      _ = (sC n : ℝ) + (t₀ : ℝ) := by rw [Nat.cast_add]
      _ < Real.exp x + 1 + t₀ := add_lt_add_left hsCeil (t₀ : ℝ)
      _ ≤ 2 * Real.exp x := by
        calc
          Real.exp x + 1 + t₀ = Real.exp x + (t₀ + 1) := by ring
          _ = (t₀ + 1) + Real.exp x := by ring
          _ ≤ Real.exp x + Real.exp x := add_le_add_left hExpLargeX (Real.exp x)
          _ = 2 * Real.exp x := by ring
  have hbase : (b : ℝ) ≤ 2 * Real.exp x := hbaseLt.le
  have hExpAtLeastTwo : 2 ≤ Real.exp x := by
    have ht₀ : (2 : ℝ) ≤ (t₀ : ℝ) + 1 := by norm_num [t₀, q_s11_compat_t₀]
    exact ht₀.trans hExpLargeX
  have hbaseExp : (b : ℝ) ≤ Real.exp (2 * x) := by
    calc
      (b : ℝ) ≤ 2 * Real.exp x := hbase
      _ ≤ Real.exp x * Real.exp x := by
        calc
          2 * Real.exp x = Real.exp x * 2 := by ring
          _ ≤ Real.exp x * Real.exp x :=
            mul_le_mul_of_nonneg_left hExpAtLeastTwo (Real.exp_pos x).le
      _ = Real.exp (2 * x) := by rw [← Real.exp_add]; congr 1 <;> ring
  let r₀ : ℕ := Nat.ceil (Real.exp (3 * (n : ℝ) / 100))
  have hRamseyReal : (Nat.choose (sC n + t₀ - 2) (sC n - 1) : ℝ) ≤
      Real.exp ((n : ℝ) / 100) := by
    have hbRamseyBound : Nat.choose (sC n + t₀ - 2) (sC n - 1) ≤ b ^ k₀ := by
      dsimp [b]
      exact hRamseyBound
    have hcast : (Nat.choose (sC n + t₀ - 2) (sC n - 1) : ℝ) ≤
        (b : ℝ) ^ k₀ := by
      exact HypercubeRamsey.S11.Core.q_s11_compat_cast_pow_bound
        (Nat.choose (sC n + t₀ - 2) (sC n - 1)) b k₀ hbRamseyBound
    have hExponent : k₀ * (2 * x) ≤ (n : ℝ) / 100 := by
      have hk₀le : k₀ ≤ t₀ := by omega
      have ht₀' : (k₀ : ℝ) ≤ (t₀ : ℝ) := Nat.cast_le.mpr hk₀le
      have hx : 0 ≤ x := by positivity
      calc
        (k₀ : ℝ) * (2 * x) ≤ (t₀ : ℝ) * (2 * x) :=
          mul_le_mul_of_nonneg_right ht₀' (by positivity)
        _ = 2 * (t₀ : ℝ) * x := by
          calc
            (t₀ : ℝ) * (2 * x) = ((t₀ : ℝ) * 2) * x := by rw [← mul_assoc]
            _ = (2 * (t₀ : ℝ)) * x := by rw [mul_comm (t₀ : ℝ) 2]
            _ = 2 * (t₀ : ℝ) * x := rfl
        _ ≤ (n : ℝ) / 100 := hsmallLinear.le
    have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    calc
      (Nat.choose (sC n + t₀ - 2) (sC n - 1) : ℝ) ≤
          (b : ℝ) ^ k₀ := hcast
      _ ≤ (Real.exp (2 * x)) ^ k₀ :=
          HypercubeRamsey.S11.Core.q_s11_compat_pow_mono
            (b : ℝ) (Real.exp (2 * x)) hbNonneg hbaseExp k₀
      _ ≤ Real.exp ((n : ℝ) / 100) :=
          HypercubeRamsey.S11.Core.q_s11_compat_exp_pow_le k₀ (2 * x)
            ((n : ℝ) / 100) hExponent
  have hRamseySize : Nat.choose (sC n + t₀ - 2) (sC n - 1) ≤ r₀ := by
    have hsizeReal : (Nat.choose (sC n + t₀ - 2) (sC n - 1) : ℝ) ≤ (r₀ : ℝ) := by
      calc
        (Nat.choose (sC n + t₀ - 2) (sC n - 1) : ℝ) ≤
            Real.exp ((n : ℝ) / 100) := hRamseyReal
        _ ≤ Real.exp (3 * (n : ℝ) / 100) :=
          Real.exp_le_exp.mpr (by nlinarith [hn1])
        _ ≤ (r₀ : ℝ) := by simpa [r₀] using Nat.le_ceil (Real.exp (3 * (n : ℝ) / 100))
    exact Nat.cast_le.mp hsizeReal
  have hr₀Upper : (r₀ : ℝ) ≤ 2 * Real.exp (3 * (n : ℝ) / 100) := by
    dsimp [r₀]
    have harg : 0 ≤ 3 * (n : ℝ) / 100 := by positivity
    have hhalf : (1 / 2 : ℝ) ≤ Real.exp (3 * (n : ℝ) / 100) := by
      have hone : 1 ≤ Real.exp (3 * (n : ℝ) / 100) := Real.one_le_exp_iff.mpr harg
      linarith
    have hhalf' : (2 : ℝ)⁻¹ ≤ Real.exp (3 * (n : ℝ) / 100) := by
      exact (by norm_num : (2 : ℝ)⁻¹ ≤ (1 / 2 : ℝ)).trans hhalf
    exact Nat.ceil_le_two_mul hhalf'
  have hExpHalfSq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    calc
      Real.exp (1 / 2 : ℝ) ^ 2 =
          Real.exp ((1 / 2 : ℝ) + 1 / 2) := by rw [pow_two, ← Real.exp_add]
      _ = Real.exp 1 := by congr 1 <;> norm_num
  have hExpHalfLt : Real.exp (1 / 2 : ℝ) < 2 := by
    by_contra hnot
    have hge : (2 : ℝ) ≤ Real.exp (1 / 2 : ℝ) := le_of_not_gt hnot
    nlinarith [sq_nonneg (Real.exp (1 / 2 : ℝ) - 2), hExpHalfSq, Real.exp_one_lt_three]
  have hExpN : Real.exp ((n : ℝ) / 2) ≤ (2 : ℝ) ^ n := by
    have heq : Real.exp ((n : ℝ) / 2) = Real.exp (1 / 2 : ℝ) ^ n := by
      calc
        Real.exp ((n : ℝ) / 2) = Real.exp ((n : ℝ) * (1 / 2 : ℝ)) := by congr 1 <;> ring
        _ = Real.exp (1 / 2 : ℝ) ^ n := Real.exp_nat_mul (1 / 2 : ℝ) n
    rw [heq]
    exact HypercubeRamsey.S11.Core.q_s11_compat_pow_mono
      (Real.exp (1 / 2 : ℝ)) 2 (Real.exp_pos _).le hExpHalfLt.le n
  have hNexp : Real.exp ((n : ℝ) / 2) ≤ (N : ℝ) := by
    exact hExpN.trans (by exact_mod_cast hN)
  have hFactor : 1 ≤ 2 * (t₀ : ℝ) := by norm_num [t₀, q_s11_compat_t₀]
  have hxNonneg : 0 ≤ x := by positivity
  have hxLinear : x ≤ (n : ℝ) / 100 := by
    calc
      x = 1 * x := by ring
      _ ≤ (2 * (t₀ : ℝ)) * x := mul_le_mul_of_nonneg_right hFactor hxNonneg
      _ ≤ (n : ℝ) / 100 := hsmallLinear.le
  have hCexp : 1000 / etaC ≤ Real.exp ((n : ℝ) / 100) := by
    have hCbase : 1000 / etaC ≤ (t₀ : ℝ) + 1 := by norm_num [etaC, t₀, q_s11_compat_t₀]
    exact hCbase.trans (hExpLargeX.trans (Real.exp_le_exp.mpr hxLinear))
  have hr₀Square : (r₀ : ℝ) ^ 2 ≤ 4 * Real.exp (3 * (n : ℝ) / 50) := by
    calc
      (r₀ : ℝ) ^ 2 ≤ (2 * Real.exp (3 * (n : ℝ) / 100)) ^ 2 :=
        HypercubeRamsey.S11.Core.q_s11_compat_pow_mono
          (r₀ : ℝ) (2 * Real.exp (3 * (n : ℝ) / 100)) (by positivity) hr₀Upper 2
      _ = 4 * Real.exp (3 * (n : ℝ) / 50) := by
        calc
          (2 * Real.exp (3 * (n : ℝ) / 100)) ^ 2 =
              4 * (Real.exp (3 * (n : ℝ) / 100) * Real.exp (3 * (n : ℝ) / 100)) := by ring
          _ = 4 * Real.exp (3 * (n : ℝ) / 50) := by
                rw [← Real.exp_add]
                congr 2 <;> ring
  have hNumerator :
      (r₀ : ℝ) ^ 2 * (1000 / etaC) * Real.exp ((n : ℝ) / 50) ≤
        4 * Real.exp (9 * (n : ℝ) / 100) := by
    calc
      (r₀ : ℝ) ^ 2 * (1000 / etaC) * Real.exp ((n : ℝ) / 50) =
          (r₀ : ℝ) ^ 2 * ((1000 / etaC) * Real.exp ((n : ℝ) / 50)) := by ring
      _ ≤ (4 * Real.exp (3 * (n : ℝ) / 50)) *
            ((1000 / etaC) * Real.exp ((n : ℝ) / 50)) :=
          mul_le_mul_of_nonneg_right hr₀Square (by positivity)
      _ ≤ (4 * Real.exp (3 * (n : ℝ) / 50)) *
            (Real.exp ((n : ℝ) / 100) * Real.exp ((n : ℝ) / 50)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le) (by positivity)
      _ = 4 * Real.exp (9 * (n : ℝ) / 100) := by
          calc
            _ = 4 * (Real.exp (3 * (n : ℝ) / 50) *
                (Real.exp ((n : ℝ) / 100) * Real.exp ((n : ℝ) / 50))) := by ring
            _ = 4 * Real.exp (9 * (n : ℝ) / 100) := by
              rw [← Real.exp_add, ← Real.exp_add]
              congr 2 <;> ring
  have hExp4Lt : 8 < Real.exp 4 := by
    have hExp4Eq : Real.exp 4 = Real.exp 1 ^ 4 := by
      simpa using (Real.exp_nat_mul (1 : ℝ) 4)
    calc
      (8 : ℝ) < 16 := by norm_num
      _ = (2 : ℝ) ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 := pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
      _ = Real.exp 4 := hExp4Eq.symm
  have hExp4 : 8 ≤ Real.exp 4 := hExp4Lt.le
  have hGap : 8 * Real.exp (9 * (n : ℝ) / 100) ≤ Real.exp ((n : ℝ) / 2) := by
    have hn10R : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10
    have hArg : (4 : ℝ) ≤ 41 * (n : ℝ) / 100 := by nlinarith [hn10R]
    have hExpGap : 8 ≤ Real.exp (41 * (n : ℝ) / 100) :=
      hExp4.trans (Real.exp_le_exp.mpr hArg)
    calc
      8 * Real.exp (9 * (n : ℝ) / 100) ≤
          Real.exp (41 * (n : ℝ) / 100) * Real.exp (9 * (n : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hExpGap (Real.exp_pos _).le
      _ = Real.exp ((n : ℝ) / 2) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hCollisionBudget :
      (r₀ : ℝ) ^ 2 * ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) ≤ 1 / 2 := by
    have hBudgetDiv :
        ((r₀ : ℝ) ^ 2 * (1000 / etaC) * Real.exp ((n : ℝ) / 50)) / N ≤ 1 / 2 := by
      apply (div_le_iff₀ hNr).2
      calc
        (r₀ : ℝ) ^ 2 * (1000 / etaC) * Real.exp ((n : ℝ) / 50) ≤
            4 * Real.exp (9 * (n : ℝ) / 100) := hNumerator
        _ ≤ (N : ℝ) / 2 := by
          have hN8 : 8 * Real.exp (9 * (n : ℝ) / 100) ≤ (N : ℝ) := hGap.trans hNexp
          calc
            4 * Real.exp (9 * (n : ℝ) / 100) =
                (8 * Real.exp (9 * (n : ℝ) / 100)) / 2 := by ring
            _ ≤ (N : ℝ) / 2 := div_le_div_of_nonneg_right hN8 (by positivity)
        _ = (1 / 2) * (N : ℝ) := by ring
    calc
      (r₀ : ℝ) ^ 2 * ((1000 / etaC) * Real.exp ((n : ℝ) / 50) / N) =
          ((r₀ : ℝ) ^ 2 * (1000 / etaC) * Real.exp ((n : ℝ) / 50)) / N := by ring
      _ ≤ 1 / 2 := hBudgetDiv
  sorry

/-- Discards (11:118, 161): the signed outliers, the removed cliques of the good-degree labels and the
high-degree violators number `o(N) ≤ κN/4`; a tag whose first support avoids them meets both conditions of
compatibility (its support lies in the good-degree, clique-free, violator-free labels of `X`). -/
theorem discard_set (δ x₀ K κ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hκ : 0 < κ) (hSO : SignedOutliersEv δ x₀ K) (hCR : CliqueRemovalEv δ K)
    (hHD : HighDegreeEv δ K) : DiscardEv δ x₀ K κ := by
  classical
  rcases hSO with ⟨nSO, hSO⟩
  rcases hCR with ⟨nCR, hCR⟩
  rcases hHD with ⟨nHD, hHD⟩
  have ha : 0 < 1 - δ / 16 := by nlinarith [hδ']
  have hsmallExp (r : ℝ) (hr : 0 < r) :
      ∀ᶠ n : ℕ in Filter.atTop, Real.exp (-((n : ℝ) ^ r)) < κ / 16 := by
    have hp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ r) Filter.atTop Filter.atTop :=
      (_root_.tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
    have hneg : Filter.Tendsto (fun n : ℕ => -((n : ℝ) ^ r)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hp
    have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ r)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp hneg
    exact hexp.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨nA, hnAevent⟩ := Filter.eventually_atTop.1 (hsmallExp _ ha)
  obtain ⟨nδ, hnδevent⟩ := Filter.eventually_atTop.1 (hsmallExp δ hδ)
  refine ⟨max nA (max nδ (max nSO (max nCR nHD))), ?_⟩
  intro n hn N E X Y G ι hι μ ν π α p hin hbal hdisc hXY hYX
  have hnA : nA ≤ n := by omega
  have hnδ : nδ ≤ n := by omega
  have hnSO : nSO ≤ n := by omega
  have hnCR : nCR ≤ n := by omega
  have hnHD : nHD ≤ n := by omega
  have hsmallA : Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) < κ / 16 := hnAevent n hnA
  have hsmallδ : Real.exp (-((n : ℝ) ^ δ)) < κ / 16 := hnδevent n hnδ
  have hrate : 2 * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) +
      2 * Real.exp (-((n : ℝ) ^ δ)) < κ / 4 := by nlinarith
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by norm_num : 0 < 2)) hin.host
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hNone : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos)
  let πbar : Fin N → ℝ := mixW p π
  have hπbarNonneg : ∀ y, 0 ≤ πbar y := by
    intro y
    dsimp [πbar, mixW]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (hin.π_nonneg i y)
  have hπbarSum : ∑ y, πbar y = 1 := by
    simp only [πbar, mixW]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hin.π_sum]
    simp [p.sum_eq_one]
  have hπbarSupp : ∀ y, πbar y ≠ 0 → y ∈ Y := by
    intro y hy
    by_contra hyY
    have hrowZero : ∀ i, π i y = 0 := by
      intro i
      by_contra hne
      have hν := hin.π_supp i y hne
      exact hν (hin.ν_supp i y hyY)
    have hzero : πbar y = 0 := by
      simp [πbar, mixW, hrowZero]
    exact hy hzero
  have hπbarCap : ∀ y, (N : ℝ) * πbar y ≤ K := hbal
  have hπsuppY : ∀ i y, π i y ≠ 0 → y ∈ Y := by
    intro i y hπ
    have hν := hin.π_supp i y hπ
    by_contra hyY
    exact hν (hin.ν_supp i y hyY)
  let πlaw : Law N := ⟨πbar, hπbarNonneg, hπbarSum⟩
  let Out : Finset (Fin N) := X.filter fun x =>
    4 * bS n < |sMean E G πbar x|
  have hOutcard : (Out.card : ℝ) <
      2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) := by
    simpa [Out] using hSO n hnSO (G := G) (π := πbar) hNone hπbarNonneg hπbarSum
      hπbarSupp hπbarCap hdisc
  let Good : Finset (Fin N) := X \ Out
  have hGoodMean : ∀ x ∈ Good, |sMean E G πbar x| ≤ 4 * bS n := by
    intro x hx
    have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
    have hxnot : x ∉ Out := (Finset.mem_sdiff.mp hx).2
    by_contra hlarge
    exact hxnot (Finset.mem_filter.mpr ⟨hxX, lt_of_not_ge hlarge⟩)
  obtain ⟨V, hVsub, hVcard, hNoClique⟩ :=
    hCR n hnCR (G := G) (π := πbar) hNone hπbarNonneg hπbarSum hπbarSupp hπbarCap
      hYX Good (by intro x hx; exact (Finset.mem_sdiff.mp hx).1) hGoodMean
  let High : Finset (Fin N) := X.filter fun x =>
    |sMean E G (mixW p π) x| ≤ 4 * bS n ∧
      etaC < ∑ i ∈ Finset.univ.filter (fun i => (4 / 5 : ℝ) < deg E G (π i) x), p.w i
  have hHighcard : (High.card : ℝ) < (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) := by
    simpa [High] using hHD n hnHD (G := G) (π := π) (p := p) hin.host
      hin.π_nonneg hin.π_sum hπsuppY hin.π_cap hbal hXY
  let D : Finset (Fin N) := Out ∪ V ∪ High
  have hDcard : (D.card : ℝ) ≤ κ / 4 * N := by
    have hcard : (D.card : ℝ) ≤ (Out.card : ℝ) + (V.card : ℝ) + (High.card : ℝ) := by
      dsimp [D]
      have h1 : ((Out ∪ V).card : ℝ) ≤ (Out.card : ℝ) + (V.card : ℝ) := by
        exact_mod_cast (Finset.card_union_le Out V)
      have h2 : ((Out ∪ V ∪ High).card : ℝ) ≤ ((Out ∪ V).card : ℝ) + (High.card : ℝ) := by
        exact_mod_cast (Finset.card_union_le (Out ∪ V) High)
      nlinarith [h1, h2]
    have hsmallN :
        2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) +
          2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) < κ / 4 * N := by
      have h := mul_lt_mul_of_pos_left hrate hNr
      nlinarith [h]
    have hVcard' : (V.card : ℝ) < (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) := hVcard
    have hHighcard' : (High.card : ℝ) < (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) := hHighcard
    have hOutcard' : (Out.card : ℝ) <
        2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) := hOutcard
    have hsum : (Out.card : ℝ) + (V.card : ℝ) + (High.card : ℝ) <
        2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ ((1 : ℝ) - δ / 16))) +
          2 * (N : ℝ) * Real.exp (-((n : ℝ) ^ δ)) := by
      nlinarith [hOutcard', hVcard', hHighcard']
    exact le_of_lt (lt_of_le_of_lt hcard (lt_trans hsum hsmallN))
  refine ⟨D, hDcard, ?_⟩
  intro i havoid
  have hμsupp : ∀ x, (μ i).w x ≠ 0 → x ∈ X := by
    intro x hx
    by_contra hxX
    exact hx (hin.μ_supp i x hxX)
  have hnotOut : ∀ x, (μ i).w x ≠ 0 → x ∉ Out := by
    intro x hxOut
    intro hx
    have hDmem : x ∈ D := Finset.mem_union_left High (Finset.mem_union_left V hx)
    exact hxOut (havoid x hDmem)
  have hnotV : ∀ x, (μ i).w x ≠ 0 → x ∉ V := by
    intro x hxMu hxV
    have hDmem : x ∈ D := Finset.mem_union_left High (Finset.mem_union_right Out hxV)
    exact hxMu (havoid x hDmem)
  have hnotHigh : ∀ x, (μ i).w x ≠ 0 → x ∉ High := by
    intro x hxMu hxH
    exact hxMu (havoid x (Finset.mem_union_right (Out ∪ V) hxH))
  have hdeg : ∀ x, (μ i).w x ≠ 0 → |sMean E G (mixW p π) x| ≤ 4 * bS n := by
    intro x hxMu
    have hxX := hμsupp x hxMu
    have hxnotOut := hnotOut x hxMu
    have hxnotLarge : ¬ 4 * bS n < |sMean E G πbar x| := by
      intro hxLarge
      exact hxnotOut (Finset.mem_filter.mpr ⟨hxX, hxLarge⟩)
    exact le_of_not_gt (by simpa [πbar] using hxnotLarge)
  have hmass : ∀ x, (μ i).w x ≠ 0 →
      (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p.w i') ≤ etaC := by
    intro x hxMu
    by_contra hlarge
    have hxX := hμsupp x hxMu
    have hfirst : |sMean E G (mixW p π) x| ≤ 4 * bS n := hdeg x hxMu
    have hHigh : x ∈ High := Finset.mem_filter.mpr ⟨hxX, hfirst, lt_of_not_ge hlarge⟩
    exact hnotHigh x hxMu hHigh
  have hSuppSub : (Finset.univ.filter fun x => (μ i).w x ≠ 0) ⊆ Good \ V := by
    intro x hx
    have hxMu := (Finset.mem_filter.mp hx).2
    have hxX := hμsupp x hxMu
    have hxnotOut := hnotOut x hxMu
    have hxnotV := hnotV x hxMu
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxX, hxnotOut⟩, hxnotV⟩
  have hNoCompat : NoClique E G (mixW p π) n δ
      (Finset.univ.filter fun x => (μ i).w x ≠ 0) := by
    intro C hC hcardC
    have hC' : C ⊆ Good \ V := Finset.Subset.trans hC hSuppSub
    simpa [πbar] using hNoClique C hC' hcardC
  exact ⟨hdeg, hmass, hNoCompat⟩

/-- L11.2c (11:117–118, 161).  On the compact convex domain of profiles balanced with `K = 16/κ` (nonempty by
`BalancedSub` at tolerance `κ`), the response `R(p) = {q ∈ Dom : q_i > 0 → tag i compatible with p}` is nonempty
(the compatible tags retain availability at tolerance `κ/2` after the `κN/4` discards; `BalancedSub` gives
balance `8/κ`), convex, and has closed graph (the degree conditions are linear in `p`; each fixed candidate clique
gives a closed condition; there are finitely many).  Kakutani's theorem gives a fixed point. -/
theorem fixed_point (hBS : S07.BalancedSub) {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (G : Colour) {ι : Type} [Fintype ι] (δ κ : ℝ) (hκ : 0 < κ) (μ ν : ι → Law N) (π α : ι → Fin N → ℝ)
    (hin : ProfileInput n N E X Y κ μ ν π α)
    (hdisc : ∀ p : FinProb ι, Balanced (16 / κ) p π α →
      ∃ D : Finset (Fin N), (D.card : ℝ) ≤ κ / 4 * N ∧
        ∀ i, (∀ x ∈ D, (μ i).w x = 0) → CompatTag E G n δ μ π p i) :
    ∃ p : FinProb ι, Balanced (16 / κ) p π α ∧ ∀ i, p.w i ≠ 0 → CompatTag E G n δ μ π p i := by
  classical
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.pow_pos (by norm_num : 0 < 2)) hin.host
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hκ4 : 0 < κ / 4 := by positivity
  have hκN : 0 ≤ κ * (N : ℝ) := mul_nonneg hκ.le (Nat.cast_nonneg N)
  have hbalancedMixture (D : Finset (Fin N))
      (hD : (D.card : ℝ) ≤ κ / 4 * N) :
      ∃ q : FinProb ι,
        (∀ y, (N : ℝ) * (∑ i, q.w i * π i y) ≤ 16 / κ) ∧
        (∀ x, (N : ℝ) * (∑ i, q.w i * α i x) ≤ 16 / κ) ∧
        (∀ i, q.w i ≠ 0 → ∀ x ∈ D, (μ i).w x = 0) := by
    let Good : ι → Prop := fun i => ∀ x ∈ D, (μ i).w x = 0
    let I := {i : ι // Good i}
    have hDκ : (D.card : ℝ) ≤ κ * N := by
      nlinarith [hD, hκN]
    have hIne : Nonempty I := by
      obtain ⟨i, hiμ, _⟩ := hin.avail D ∅ hDκ (by simpa using hκN)
      exact ⟨⟨i, hiμ⟩⟩
    let πI : I → Law N := fun i =>
      ⟨π i.1, hin.π_nonneg i.1, hin.π_sum i.1⟩
    let αI : I → Fin N → ℝ := fun i => α i.1
    have hαnonneg : ∀ i x, 0 ≤ αI i x := by
      intro i x
      exact hin.α_nonneg i.1 x
    have hαsum : ∀ i, ∑ x, αI i x ≤ 1 := by
      intro i
      exact hin.α_sum i.1
    have hAvailI : ∀ RX RY : Finset (Fin N),
        (RX.card : ℝ) ≤ κ / 4 * N → (RY.card : ℝ) ≤ κ / 4 * N →
        ∃ i : I, (∀ y ∈ RX, (πI i).w y = 0) ∧ (∀ x ∈ RY, αI i x = 0) := by
      intro RX RY hRX hRY
      have hDunion : ((D ∪ RY).card : ℝ) ≤ κ * N := by
        have hcard : ((D ∪ RY).card : ℝ) ≤ (D.card : ℝ) + (RY.card : ℝ) := by
          exact_mod_cast (Finset.card_union_le D RY)
        nlinarith [hcard, hD, hRY, hκN]
      have hRX' : (RX.card : ℝ) ≤ κ * N := by nlinarith [hRX, hκN]
      obtain ⟨i, hiμ, hiν⟩ := hin.avail (D ∪ RY) RX hDunion hRX'
      have hpi : ∀ y ∈ RX, π i y = 0 := by
        intro y hy
        by_contra hne
        exact (hin.π_supp i y hne) (hiν y hy)
      have halpha : ∀ x ∈ RY, α i x = 0 := by
        intro x hx
        by_contra hne
        exact (hin.α_supp i x hne) (hiμ x (Finset.mem_union_right D hx))
      refine ⟨⟨i, fun x hx => hiμ x (Finset.mem_union_left RY hx)⟩, ?_, halpha⟩
      exact hpi
    obtain ⟨t, hπcap, hαcap⟩ := hBS hNpos πI αI (κ / 4) hκ4
      hαnonneg hαsum hAvailI
    let q : FinProb ι := FinProb.map t Subtype.val
    have hmapπ (y : Fin N) :
        (∑ i, q.w i * π i y) = ∑ j : I, t.w j * π j.1 y := by
      change (FinProb.map t Subtype.val).expect (fun i => π i y) =
        t.expect (fun j => π j.1 y)
      rw [FinProb.map_expect]
    have hmapα (x : Fin N) :
        (∑ i, q.w i * α i x) = ∑ j : I, t.w j * α j.1 x := by
      change (FinProb.map t Subtype.val).expect (fun i => α i x) =
        t.expect (fun j => α j.1 x)
      rw [FinProb.map_expect]
    have hscale : 4 / ((κ / 4) * (N : ℝ)) = 16 / (κ * (N : ℝ)) := by
      field_simp [ne_of_gt hκ, ne_of_gt hNr]
      ring
    have hpiScale : 16 / (κ * (N : ℝ)) = (16 / κ) / N := by
      field_simp [ne_of_gt hκ, ne_of_gt hNr]
      <;> ring
    refine ⟨q, ?_, ?_, ?_⟩
    · intro y
      rw [hmapπ y]
      have hbound : (∑ j : I, t.w j * π j.1 y) ≤ (16 / κ) / N := by
        calc
          (∑ j : I, t.w j * π j.1 y) ≤ 4 / ((κ / 4) * (N : ℝ)) := by
            simpa [πI] using hπcap y
          _ = (16 / κ) / N := by rw [hscale, hpiScale]
      calc
        (N : ℝ) * (∑ j : I, t.w j * π j.1 y) ≤ (N : ℝ) * ((16 / κ) / N) :=
          mul_le_mul_of_nonneg_left hbound hNr.le
        _ = 16 / κ := by field_simp [ne_of_gt hNr]
    · intro x
      rw [hmapα x]
      have hbound : (∑ j : I, t.w j * α j.1 x) ≤ (16 / κ) / N := by
        calc
          (∑ j : I, t.w j * α j.1 x) ≤ 4 / ((κ / 4) * (N : ℝ)) := by
            simpa [αI] using hαcap x
          _ = (16 / κ) / N := by rw [hscale, hpiScale]
      calc
        (N : ℝ) * (∑ j : I, t.w j * α j.1 x) ≤ (N : ℝ) * ((16 / κ) / N) :=
          mul_le_mul_of_nonneg_left hbound hNr.le
        _ = 16 / κ := by field_simp [ne_of_gt hNr]
    · intro i hqi
      by_contra hnot
      have hqzero : q.w i = 0 := by
        change (Finset.univ.sum fun j : I => if Subtype.val j = i then t.w j else 0) = 0
        apply Finset.sum_eq_zero
        intro j hj
        by_cases hji : j.1 = i
        · subst i
          exact (hnot j.2).elim
        · simp [hji]
      exact hqi hqzero
  let mixRaw (p : ι → ℝ) (f : ι → Fin N → ℝ) (x : Fin N) : ℝ :=
    ∑ i, p i * f i x
  let Simplex : Set (ι → ℝ) := stdSimplex ℝ ι
  let toProb : ∀ p : ι → ℝ, p ∈ Simplex → FinProb ι :=
    fun p hp => ⟨p, hp.1, hp.2⟩
  let bal (p : ι → ℝ) : Prop :=
    (∀ y, (N : ℝ) * mixRaw p π y ≤ 16 / κ) ∧
    (∀ x, (N : ℝ) * mixRaw p α x ≤ 16 / κ)
  let S : Set (ι → ℝ) := {p | p ∈ Simplex ∧ bal p}
  have hmixCont (f : ι → Fin N → ℝ) (x : Fin N) :
      Continuous (fun p : ι → ℝ => mixRaw p f x) := by
    unfold mixRaw
    fun_prop
  have hmixLinear (p q : ι → ℝ) (a b : ℝ) (f : ι → Fin N → ℝ) (x : Fin N) :
      mixRaw (a • p + b • q) f x = a * mixRaw p f x + b * mixRaw q f x := by
    unfold mixRaw
    calc
      (∑ i, (a * p i + b * q i) * f i x) =
          ∑ i, (a * (p i * f i x) + b * (q i * f i x)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = a * (∑ i, p i * f i x) + b * (∑ i, q i * f i x) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hbalClosed : IsClosed {p : ι → ℝ | bal p} := by
    rw [show {p : ι → ℝ | bal p} =
      (⋂ y, {p | (N : ℝ) * mixRaw p π y ≤ 16 / κ}) ∩
      (⋂ x, {p | (N : ℝ) * mixRaw p α x ≤ 16 / κ}) by
        ext p
        simp [bal]]
    apply IsClosed.inter
    · apply isClosed_iInter
      intro y
      exact isClosed_le (continuous_const.mul (hmixCont π y)) continuous_const
    · apply isClosed_iInter
      intro x
      exact isClosed_le (continuous_const.mul (hmixCont α x)) continuous_const
  have hSclosed : IsClosed S := by
    change IsClosed (Simplex ∩ {p | bal p})
    exact (isClosed_stdSimplex ℝ ι).inter hbalClosed
  have hScompact : IsCompact S := by
    apply (isCompact_stdSimplex ℝ ι).of_isClosed_subset hSclosed
    intro p hp
    exact hp.1
  have hSconv : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    refine ⟨convex_stdSimplex ℝ ι hp.1 hq.1 ha hb hab, ?_⟩
    constructor
    · intro y
      rw [hmixLinear p q a b π y]
      calc
        (N : ℝ) * (a * mixRaw p π y + b * mixRaw q π y) =
            a * ((N : ℝ) * mixRaw p π y) + b * ((N : ℝ) * mixRaw q π y) := by ring
        _ ≤ a * (16 / κ) + b * (16 / κ) :=
          add_le_add (mul_le_mul_of_nonneg_left (hp.2.1 y) ha)
            (mul_le_mul_of_nonneg_left (hq.2.1 y) hb)
        _ = 16 / κ := by rw [← add_mul, hab]; ring
    · intro x
      rw [hmixLinear p q a b α x]
      calc
        (N : ℝ) * (a * mixRaw p α x + b * mixRaw q α x) =
            a * ((N : ℝ) * mixRaw p α x) + b * ((N : ℝ) * mixRaw q α x) := by ring
        _ ≤ a * (16 / κ) + b * (16 / κ) :=
          add_le_add (mul_le_mul_of_nonneg_left (hp.2.2 x) ha)
            (mul_le_mul_of_nonneg_left (hq.2.2 x) hb)
        _ = 16 / κ := by rw [← add_mul, hab]; ring
  have hSnonempty : S.Nonempty := by
    have hEmpty : ((∅ : Finset (Fin N)).card : ℝ) ≤ κ / 4 * N := by
      simp
      positivity
    obtain ⟨p, hpπ, hpα, _⟩ := hbalancedMixture ∅ hEmpty
    refine ⟨p.w, ?_⟩
    exact ⟨⟨p.nonneg, p.sum_eq_one⟩, ⟨hpπ, hpα⟩⟩
  let CompatRaw (p : ι → ℝ) (i : ι) : Prop :=
    (∀ x, (μ i).w x ≠ 0 → |sMean E G (mixRaw p π) x| ≤ 4 * bS n) ∧
    (∀ x, (μ i).w x ≠ 0 →
      (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p i') ≤ etaC) ∧
    NoClique E G (mixRaw p π) n δ (Finset.univ.filter fun x => (μ i).w x ≠ 0)
  have hCompatClosed (i : ι) : IsClosed {p : ι → ℝ | CompatRaw p i} := by
    have hsmCont (x : Fin N) :
        Continuous (fun p : ι → ℝ => sMean E G (mixRaw p π) x) := by
      unfold sMean mixRaw
      fun_prop
    have hcorrCont (x z : Fin N) :
        Continuous (fun p : ι → ℝ => corr E G (mixRaw p π) x z) := by
      unfold corr mixRaw
      fun_prop
    have hmassCont (x : Fin N) : Continuous (fun p : ι → ℝ =>
        ∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p i') := by
      fun_prop
    have hfirst : IsClosed {p : ι → ℝ |
        ∀ x, (μ i).w x ≠ 0 → |sMean E G (mixRaw p π) x| ≤ 4 * bS n} := by
      rw [show {p : ι → ℝ | ∀ x, (μ i).w x ≠ 0 →
          |sMean E G (mixRaw p π) x| ≤ 4 * bS n} =
        ⋂ x, {p : ι → ℝ | (μ i).w x ≠ 0 →
          |sMean E G (mixRaw p π) x| ≤ 4 * bS n} by
            ext p
            simp]
      apply isClosed_iInter
      intro x
      by_cases hx : (μ i).w x ≠ 0
      · simpa [hx] using
          (isClosed_le (continuous_abs.comp (hsmCont x)) continuous_const)
      · simp [hx]
    have hsecond : IsClosed {p : ι → ℝ |
        ∀ x, (μ i).w x ≠ 0 →
          (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p i') ≤ etaC} := by
      rw [show {p : ι → ℝ | ∀ x, (μ i).w x ≠ 0 →
          (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p i') ≤ etaC} =
        ⋂ x, {p : ι → ℝ | (μ i).w x ≠ 0 →
          (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p i') ≤ etaC} by
            ext p
            simp]
      apply isClosed_iInter
      intro x
      by_cases hx : (μ i).w x ≠ 0
      · simpa [hx] using (isClosed_le (hmassCont x) continuous_const)
      · simp [hx]
    let Sᵢ : Finset (Fin N) := Finset.univ.filter fun x => (μ i).w x ≠ 0
    have hno : IsClosed {p : ι → ℝ | NoClique E G (mixRaw p π) n δ Sᵢ} := by
      rw [show {p : ι → ℝ | NoClique E G (mixRaw p π) n δ Sᵢ} =
        ⋂ C : Finset (Fin N), {p : ι → ℝ | C ⊆ Sᵢ → C.card = sC n →
          ∃ x ∈ C, ∃ z ∈ C, x ≠ z ∧
            corr E G (mixRaw p π) x z ≤ 8 * (n : ℝ) ^ (-δ)} by
              ext p
              simp [NoClique, Sᵢ]]
      apply isClosed_iInter
      intro C
      by_cases hsub : C ⊆ Sᵢ
      · by_cases hcard : C.card = sC n
        · have hpair : IsClosed {p : ι → ℝ |
              ∃ x ∈ C, ∃ z ∈ C, x ≠ z ∧
                corr E G (mixRaw p π) x z ≤ 8 * (n : ℝ) ^ (-δ)} := by
            rw [show {p : ι → ℝ | ∃ x ∈ C, ∃ z ∈ C, x ≠ z ∧
                corr E G (mixRaw p π) x z ≤ 8 * (n : ℝ) ^ (-δ)} =
              ⋃ x ∈ (C : Set (Fin N)), ⋃ z ∈ (C : Set (Fin N)),
                {p : ι → ℝ | x ≠ z ∧ corr E G (mixRaw p π) x z ≤ 8 * (n : ℝ) ^ (-δ)} by
                  ext p
                  simp [and_assoc, and_left_comm, and_comm]]
            refine C.finite_toSet.isClosed_biUnion ?_
            intro x hx
            refine C.finite_toSet.isClosed_biUnion ?_
            intro z hz
            by_cases hxz : x ≠ z
            · simpa [hxz] using
                (isClosed_le (hcorrCont x z) continuous_const)
            · simp [hxz]
          simpa [hsub, hcard] using hpair
        · simp [hsub, hcard]
      · simp [hsub]
    rw [show {p : ι → ℝ | CompatRaw p i} =
        {p | ∀ x, (μ i).w x ≠ 0 → |sMean E G (mixRaw p π) x| ≤ 4 * bS n} ∩
        {p | ∀ x, (μ i).w x ≠ 0 →
          (∑ i' ∈ Finset.univ.filter (fun i' => (4 / 5 : ℝ) < deg E G (π i') x), p i') ≤ etaC} ∩
        {p | NoClique E G (mixRaw p π) n δ Sᵢ} by
          ext p
          simp [CompatRaw, Sᵢ, and_assoc]]
    exact (hfirst.inter hsecond).inter hno
  let response (p : S) : Set (ι → ℝ) :=
    {q | q ∈ S ∧ ∀ i, ¬ CompatRaw p.1 i → q i = 0}
  have hresponse_subset (p : S) : response p ⊆ S := by
    intro q hq
    exact hq.1
  have hresponse_convex (p : S) : Convex ℝ (response p) := by
    intro q hq r hr a b ha hb hab
    refine ⟨hSconv hq.1 hr.1 ha hb hab, ?_⟩
    intro i hi
    change a * q i + b * r i = 0
    rw [hq.2 i hi, hr.2 i hi]
    ring
  have hresponse_nonempty (p : S) : (response p).Nonempty := by
    let pLaw := toProb p.1 p.2.1
    have hpbal : Balanced (16 / κ) pLaw π α := by
      exact ⟨p.2.2.1, p.2.2.2⟩
    obtain ⟨D, hD, hDcompat⟩ := hdisc pLaw hpbal
    obtain ⟨q, hqπ, hqα, hqgood⟩ := hbalancedMixture D hD
    refine ⟨q.w, ?_⟩
    constructor
    · exact ⟨⟨q.nonneg, q.sum_eq_one⟩, ⟨hqπ, hqα⟩⟩
    · intro i hnot
      by_contra hnonzero
      have hGood : (∀ x ∈ D, (μ i).w x = 0) := hqgood i hnonzero
      have hCompat : CompatRaw p.1 i := by
        change CompatTag E G n δ μ π pLaw i
        exact hDcompat i hGood
      exact hnot hCompat
  have hgraph : closedGraph response := by
    rw [closedGraph]
    rw [show {z : S × (ι → ℝ) | z.2 ∈ response z.1} =
      {z | z.2 ∈ S} ∩ ⋂ i : ι,
        ({z : S × (ι → ℝ) | CompatRaw z.1.1 i} ∪
          {z : S × (ι → ℝ) | z.2 i = 0}) by
            ext z
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
              Set.mem_union, response]
            constructor
            · rintro ⟨hzS, hresp⟩
              refine ⟨hzS, ?_⟩
              intro i
              by_cases hc : CompatRaw z.1.1 i
              · exact Or.inl hc
              · exact Or.inr (hresp i hc)
            · rintro ⟨hzS, hcompat⟩
              refine ⟨hzS, ?_⟩
              intro i hnot
              rcases hcompat i with hc | hz
              · exact (hnot hc).elim
              · exact hz]
    apply IsClosed.inter
    · exact hSclosed.preimage continuous_snd
    · apply isClosed_iInter
      intro i
      apply IsClosed.union
      · exact (hCompatClosed i).preimage
          (continuous_subtype_val.comp continuous_fst)
      · exact isClosed_eq ((continuous_apply i).comp continuous_snd) continuous_const
  have hresponseConditions : ∀ p : S,
      response p ⊆ S ∧ Convex ℝ (response p) ∧ (response p).Nonempty := by
    intro p
    exact ⟨hresponse_subset p, hresponse_convex p, hresponse_nonempty p⟩
  obtain ⟨p, hp⟩ := kakutani_fixed_point S hSconv hScompact hSnonempty
    response hgraph hresponseConditions
  let pLaw := toProb p.1 p.2.1
  refine ⟨pLaw, ?_, ?_⟩
  · exact ⟨p.2.2.1, p.2.2.2⟩
  · intro i hpos
    have hCompat : CompatRaw p.1 i := by
      by_contra hnot
      have hzero := hp.2 i hnot
      exact hpos (by simpa [pLaw, toProb] using hzero)
    change CompatTag E G n δ μ π pLaw i
    exact hCompat

/-- Lemma 11.2 (11:104–161) assembled. -/
theorem compatible_profile (δ x₀ κ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀)
    (hx₀' : x₀ < 1) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} (G : Colour)
      {ι : Type} [Fintype ι] (μ ν : ι → Law N) (π α : ι → Fin N → ℝ),
      ProfileInput n N E X Y κ μ ν π α →
      DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - δ / 16)) ((n : ℝ) ^ x₀) ((n : ℝ) ^ (-(19 : ℝ) / 20)) →
      ClusterAbsXY n N E X Y δ → ClusterAbsYX n N E X Y δ →
      ∃ p : FinProb ι, Balanced (16 / κ) p π α ∧ ∀ i, p.w i ≠ 0 → CompatTag E G n δ μ π p i := by
  have hK : (0 : ℝ) < 16 / κ := by positivity
  obtain ⟨n₀, hD⟩ := discard_set δ x₀ (16 / κ) κ hδ hδ' hx₀ hx₀' hK hκ
    (signed_outliers δ x₀ (16 / κ) hδ hδ' hx₀ hx₀' hK) (clique_removal δ (16 / κ) hδ hδ' hK)
    (high_degree δ (16 / κ) hδ hδ' hK)
  refine ⟨n₀, ?_⟩
  intro n hn N E X Y G ι hι μ ν π α hin hdisc hXY hYX
  exact fixed_point S07.balanced_mixture_sub G δ κ hκ μ ν π α hin
    (fun p hp => hD n hn G μ ν π α p hin hp.1 hdisc hXY hYX)

end HypercubeRamsey.S11.Core
