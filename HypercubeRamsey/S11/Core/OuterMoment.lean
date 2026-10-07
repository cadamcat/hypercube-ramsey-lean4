import HypercubeRamsey.S11.Core.Definitions
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
