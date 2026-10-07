import HypercubeRamsey.S11.Core.Parameters
import HypercubeRamsey.S11.Needs
import HypercubeRamsey.S03.Mixtures

/-! P11.1's menu and slice nodes, followed by L11.2's compatibility profile. -/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey
open Classical
open scoped BigOperators

/-- P11.1-menu: one-colour finite menu obtained from the available linear-bias patch. -/
theorem biased_menu {n N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (δ x₀ h₀ κ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 20000)
    (hx₀ : 0 < x₀) (hx₀' : x₀ < 1) (hh₀ : 0 < h₀) (hh₀' : h₀ < 1 / 100)
    (hκ : 0 < κ) (hscale : ScaleBounds n δ x₀ h₀ κ)
    (havail : AvailableAt κ
      ((PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) h₀).toPatch)
      n N E X Y) :
    ∃ M : BiasedMenu n N E X Y κ h₀, True := by
  sorry

/-- P11.1a: select the deterministic base labels and the finite mean odd-row laws. -/
theorem slice_seed {n N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (δ x₀ h₀ κ : ℝ) (hscale : ScaleBounds n δ x₀ h₀ κ)
    (M : BiasedMenu n N E X Y κ h₀) :
    ∃ S : SliceSeed M (innerDimension n) (tupleLength n) (sliceSurplus n), True := by
  sorry

/-- P11.1b: the common-neighbour rows lose mass only on the stated exponential tail. -/
theorem common_rows {n N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N))
    (δ x₀ h₀ κ : ℝ) (hscale : ScaleBounds n δ x₀ h₀ κ)
    (M : BiasedMenu n N E X Y κ h₀)
    (S : SliceSeed M (innerDimension n) (tupleLength n) (sliceSurplus n)) :
    ∃ R : CommonRows S, True := by
  sorry

/-- The two aggregate bounds defining the compact profile domain in L11.2. -/
def BalancedProfile {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} {M : BiasedMenu n N E X Y κ h₀}
    {h k : ℕ} {g : ℝ} (S : SliceSeed M h k g) (R : CommonRows S)
    (p : FinProb M.mix.ι) (K : ℝ) : Prop :=
  (∀ y, (N : ℝ) * (profileLaw p S.π).w y ≤ K) ∧
  (∀ x, (N : ℝ) * profileSubWeight p R.α x ≤ K)

/-- A tag is compatible with the input profile: its rows have small signed degree, few high-degree tags,
and its support has no large correlation clique. -/
def CompatibleTag {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g : ℝ}
    (S : SliceSeed M h k g) (p : FinProb M.mix.ι) (δ η : ℝ) (i : M.mix.ι) : Prop :=
  (∀ x, (M.mix.μ i).w x ≠ 0 →
    |signedMean E M.G (profileLaw p S.π) x| ≤ 4 * signedBiasScale n) ∧
  (∀ x, (M.mix.μ i).w x ≠ 0 →
    (∑ i' ∈ Finset.univ.filter
      (fun i' => rowDeg E M.G x (S.π i') > (4 / 5 : ℝ)), p.w i') ≤ η) ∧
  (∀ C : Finset (Fin N),
    (∀ x ∈ C, (M.mix.μ i).w x ≠ 0) →
    C.card = Nat.ceil (Real.exp ((n : ℝ) ^ (1 / 100 : ℝ))) →
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧
      signedCorrelation E M.G (profileLaw p S.π) x y ≤ 8 * (n : ℝ) ^ (-δ))

/-- L11.2's fixed-point conclusion for a profile. -/
def CompatibleProfile {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (p : FinProb M.mix.ι) (K δ η : ℝ) : Prop :=
  BalancedProfile S R p K ∧ ∀ i, p.w i > 0 → CompatibleTag M S p δ η i

/-- L11.2a output: signed-degree and correlation-clique labels that must be discarded. -/
def CompatibilityDiscard {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g δ K : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (p : FinProb M.mix.ι)
    (hp : BalancedProfile S R p K) : Prop :=
  ∃ signedOutliers : Finset (Fin N),
    (signedOutliers.card : ℝ) < 2 * N * Real.exp (-((n : ℝ) ^ (1 - δ / 16))) ∧
    signedOutliers ⊆ X ∧
    (∀ x, x ∈ signedOutliers ↔
      x ∈ X ∧ |signedMean E M.G (profileLaw p S.π) x| > 4 * signedBiasScale n) ∧
    ∃ cliqueRemoved : Finset (Fin N),
      (cliqueRemoved.card : ℝ) < N * Real.exp (-((n : ℝ) ^ δ))

/-- L11.2b output: labels that see too much profile mass on high-degree tags. -/
def HighDegreeDiscard {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g K : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (p : FinProb M.mix.ι)
    (hp : BalancedProfile S R p K) : Prop :=
  ∃ labels : Finset (Fin N),
    (labels.card : ℝ) < N * Real.exp (-((n : ℝ) ^ (1 / 100 : ℝ))) ∧
    labels ⊆ X ∧
    ∀ x ∈ labels,
      |signedMean E M.G (profileLaw p S.π) x| ≤ 4 * signedBiasScale n ∧
      (∑ i' ∈ Finset.univ.filter
        (fun i' => rowDeg E M.G x (S.π i') > (4 / 5 : ℝ)), p.w i') >
          (1 / 100000000 : ℝ)

/-- L11.2a: signed outliers and the union of greedily removed correlation cliques are small. -/
theorem discard_signed_and_cliques {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g δ x₀ K : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (p : FinProb M.mix.ι)
    (hp : BalancedProfile S R p K) (hscale : ScaleBounds n δ x₀ h₀ κ) :
    CompatibilityDiscard (δ := δ) M S R p hp := by
  sorry

/-- L11.2b: few labels see profile mass above the high-degree cutoff. -/
theorem discard_high_degree_tags {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g δ x₀ K : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (p : FinProb M.mix.ι)
    (hp : BalancedProfile S R p K) (hscale : ScaleBounds n δ x₀ h₀ κ) :
    HighDegreeDiscard M S R p hp := by
  sorry

/-- L11.2c: Kakutani's closed response correspondence has a compatible balanced fixed point. -/
theorem fixed_compatible_profile {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g δ η : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (hκ : 0 < κ) (hη : 0 < η)
    (hDiscard : ∀ K : ℝ, 100 / κ < K → ∀ p : FinProb M.mix.ι,
      ∀ hp : BalancedProfile S R p K, CompatibilityDiscard (δ := δ) M S R p hp)
    (hHigh : ∀ K : ℝ, 100 / κ < K → ∀ p : FinProb M.mix.ι,
      (hp : BalancedProfile S R p K) → HighDegreeDiscard M S R p hp) :
    ∃ K : ℝ, 100 / κ < K ∧ ∃ p : FinProb M.mix.ι, CompatibleProfile M S R p K δ η := by
  sorry

/-- L11.2: assemble the fixed point from its two discard estimates and the Kakutani node. -/
theorem compatible_balanced_profile {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g δ η x₀ : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (hκ : 0 < κ) (hη : 0 < η)
    (hscale : ScaleBounds n δ x₀ h₀ κ) :
    ∃ K : ℝ, 100 / κ < K ∧ ∃ p : FinProb M.mix.ι, CompatibleProfile M S R p K δ η := by
  apply fixed_compatible_profile M S R hκ hη
  · intro K hK p hp
    exact discard_signed_and_cliques M S R p hp hscale
  · intro K hK p hp
    exact discard_high_degree_tags M S R p hp hscale

end HypercubeRamsey.S11.Core
