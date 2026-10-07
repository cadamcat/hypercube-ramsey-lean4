import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S07.Profiles
import HypercubeRamsey.Tools.Ramsey

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
  sorry

/-- L11.2a(ii) (11:120–128).  Take a maximal family of disjoint `s_c`-cliques of the graph `K_π > 8n^{-δ}` on `S`,
with union `V`; `S \ V` has no clique.  If `|V| ≥ N e^{-n^δ}`: first law `π` (width `log K ≤ n^δ`), clusters
uniform on the cliques weighted by size (aggregate uniform on `V`, width `≤ n^δ`; atoms `1/s_c ≤ e^{-n^ζ}`), and
codegree `(1 + m_x + m_{x'} + K_π)/4 ≥ 1/4 + n^{-δ}` (diagonal `(1 + m_x)/2`, as `b_* = o(n^{-δ})`): a reversed
cluster witness, excluded. -/
theorem clique_removal (δ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hK : 0 < K) :
    CliqueRemovalEv δ K := by
  sorry

/-- L11.2b (11:130–159).  Suppose the violators `U` number at least `N e^{-n^δ}`; let `μ_U` be uniform on `U`.
`E_i D_i(x) = (1 + m_x)/2` and tag mass `> η` has `D_i(x) > .8`, so `E_i D_i(x)² ≥ 1/4 + cη`.  In `L²(μ_U)` a
positive `p`-fraction of tags has `‖v_i‖ > 1/2 + c'`; each such tag gives `ρ_i ≤ Cπ_i` on labels with projection
`≥ 1/2 + c''` on `v_i/‖v_i‖`; the graph `codeg_{μ_U} ≥ 1/4 + c'''` on them has independence number below an
absolute `t₀`.  Draw `r₀ = ⌊e^{.03n}⌋` distinct labels from `ρ_i` (collisions `O(r₀² e^{.02n}/N) = o(1)`), pack
all but `binom(s_c + t₀, t₀)` of them into `s_c`-cliques (X-RamseyBinom), and average the cluster mixtures over
samples and tags (aggregate `O(1) π`): an `(X, Y)` cluster witness with first law `μ_U`, excluded. -/
theorem high_degree (δ K : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hK : 0 < K) :
    HighDegreeEv δ K := by
  sorry

/-- Discards (11:118, 161): the signed outliers, the removed cliques of the good-degree labels and the
high-degree violators number `o(N) ≤ κN/4`; a tag whose first support avoids them meets both conditions of
compatibility (its support lies in the good-degree, clique-free, violator-free labels of `X`). -/
theorem discard_set (δ x₀ K κ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000) (hx₀ : 0 < x₀) (hx₀' : x₀ < 1)
    (hK : 0 < K) (hκ : 0 < κ) (hSO : SignedOutliersEv δ x₀ K) (hCR : CliqueRemovalEv δ K)
    (hHD : HighDegreeEv δ K) : DiscardEv δ x₀ K κ := by
  sorry

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
  sorry

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
