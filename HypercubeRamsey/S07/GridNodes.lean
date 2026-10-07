import HypercubeRamsey.S07.SmallGridPurity

/-!
# L7.1c–i: finite profile, avoidance, alarm, and posterior nodes

These structures expose the finite laws and the quantitative conclusions passed between the probabilistic
steps. The proof bodies remain skeleton obligations for their corresponding Section 7 nodes.
-/

namespace HypercubeRamsey.S07

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

/-- L7.1c data: tag profiles and filtered-cell rows with bounded pointwise means. -/
structure GridProfiles (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour)
    (X Y : Finset (Fin N)) (d p₀ : ℝ) (Key Aux : Type*)
    [Fintype Key] [Fintype Aux] where
  menu : TagMix N
  q : Key → menu.ι → ℝ
  K : ℝ
  Ktyp : ℝ
  vertexCell : CubeVertex n → Key × Aux
  menu_properties : ∀ i, 0 < menu.Λ i →
    (menu.μ i).SupportedIn X ∧ (menu.ν i).SupportedIn Y ∧
    (menu.μ i).WidthLE ((n : ℝ) ^ (d / 2)) ∧
    (menu.ν i).WidthLE ((n : ℝ) ^ (d / 2)) ∧
    PGridPure G d p₀ n N E (menu.μ i) (menu.ν i)
  crossPass : Key → Aux → (Key → menu.ι) → ((Key × Aux) → Fin N) → Prop
  ownPass : Key → Aux → (Key → menu.ι) → ((Key × Aux) → Fin N) → Prop
  anchorNames : Key → Aux → (Key → menu.ι) → ((Key × Aux) → Fin N) → List (Fin N)
  p : Key → Aux → (Key → menu.ι) → ((Key × Aux) → Fin N) → Fin N → ℝ
  p_eq : ∀ g t σ W y, p g t σ W y =
    if crossPass g t σ W ∧ ownPass g t σ W then
      filt E G (menu.ν (σ g)) (anchorNames g t σ W) y else 0
  q_nonneg : ∀ g i, 0 ≤ q g i
  q_sum : ∀ g, ∑ i, q g i = 1
  mu_mean_bound : ∀ g x,
    (N : ℝ) * ∑ i, q g i * (menu.μ i).w x ≤ K
  p_nonneg : ∀ g t σ W y, 0 ≤ p g t σ W y
  p_subprob : ∀ g t σ W, ∑ y, p g t σ W y ≤ 1
  p_mean_bound : ∀ g t y,
    (N : ℝ) *
      ∑ σ : Key → menu.ι,
        (∏ h, q h (σ h)) *
          ∑ W : (Key × Aux → Fin N),
    (∏ z, (menu.μ (σ z.1)).w (W z)) * p g t σ W y ≤ K

/-- A cell is valid exactly when all of its cross and own restrictions pass. -/
def GridProfiles.valid {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ} {Key Aux : Type*}
    [Fintype Key] [Fintype Aux] (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (g : Key) (t : Aux) (σ : Key → P.menu.ι) (W : (Key × Aux) → Fin N) : Prop :=
  P.crossPass g t σ W ∧ P.ownPass g t σ W

/-- Every cell passes both filters for a realized assignment. -/
def GridProfiles.allValid {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ} {Key Aux : Type*}
    [Fintype Key] [Fintype Aux] (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (σ : Key → P.menu.ι) (W : (Key × Aux) → Fin N) : Prop :=
  ∀ g t, P.valid g t σ W

/-- Sum of the filtered odd-cell rows at one output label. -/
noncomputable def GridProfiles.oddColumnLoad {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ} {Key Aux : Type*}
    [Fintype Key] [Fintype Aux] (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (σ : Key → P.menu.ι) (W : (Key × Aux) → Fin N) (y : Fin N) : ℝ :=
  ∑ b : {v : CubeVertex n // ¬ IsEvenRole v},
    P.p (P.vertexCell b.1).1 (P.vertexCell b.1).2 σ W y

/-- Product weight of a complete independent tag assignment. -/
noncomputable def GridProfiles.tagWeight {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ} {Key Aux : Type*}
    [Fintype Key] [Fintype Aux] (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (σ : Key → P.menu.ι) : ℝ := ∏ g, P.q g (σ g)

/-- Product weight of all raw anchors conditional on their tags. -/
noncomputable def GridProfiles.anchorWeight {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ} {Key Aux : Type*}
    [Fintype Key] [Fintype Aux] (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (σ : Key → P.menu.ι) (W : (Key × Aux) → Fin N) : ℝ :=
  ∏ c, (P.menu.μ (σ c.1)).w (W c)

/-- Conditional cross-failure probability for a fixed complete tag assignment. -/
noncomputable def GridProfiles.crossFailureAtTags
    {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
    {d p₀ : ℝ} {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (g : Key) (t : Aux)
    (σ : Key → P.menu.ι) : ℝ :=
  ∑ W : (Key × Aux) → Fin N,
    P.anchorWeight σ W * (if P.crossPass g t σ W then 0 else 1)

/-- Bounded cross-failure rate under the independent tag and raw-anchor law. -/
noncomputable def GridProfiles.crossFailureMean
    {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
    {d p₀ : ℝ} {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (g : Key) (t : Aux) : ℝ :=
  ∑ σ : Key → P.menu.ι, P.tagWeight σ * P.crossFailureAtTags g t σ

/-- A tag assignment is bad when some cell has a large conditional cross-failure rate. -/
def GridProfiles.isBadTag
    {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
    {d p₀ : ℝ} {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (n : ℕ) (D₀ : ℝ)
    (σ : Key → P.menu.ι) : Prop :=
  ∃ g t, P.crossFailureAtTags g t σ > (n : ℝ) ^ (-D₀ / 2)

/-- A tag assignment is typical when its mean normalized first-side load is bounded. -/
def GridProfiles.isTypicalTag
    {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
    {d p₀ : ℝ} {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (σ : Key → P.menu.ι) : Prop :=
  ∀ x, (Fintype.card Key : ℝ)⁻¹ *
    ∑ g, (N : ℝ) * (P.menu.μ (σ g)).w x ≤ P.Ktyp

/-- L7.1c (07:116–134): available grid-pure patches admit tag profiles with bounded means. -/
theorem grid_profiles {d : ℝ} {n N s ℓ qn : ℕ} (Γ : GridGeom d n s ℓ qn)
    (D₀ p₀ κ : ℝ)
    (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour)
    (h71 : Eq71At D₀ d n N E X Y)
    (havail : AvailableAt κ (PGridPure G d p₀).toPatch n N E X Y) :
    Nonempty (GridProfiles n N E G X Y d p₀ (GridGeom.Key Γ) (GridGeom.AuxWord Γ)) := by
  sorry

/-- L7.1d output: cross-filter and own-filter failure probabilities at each grid cell. -/
structure GridFilterTails {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (s q : ℕ) (D₀ : ℝ) where
  cross_bound : ∀ g t, P.crossFailureMean g t ≤
    4 * (s : ℝ) ^ 2 * P.K * (n : ℝ) ^ (-D₀)
  own_bound : ∀ g t, ∑ σ : Key → P.menu.ι,
      P.tagWeight σ * ∑ W : (Key × Aux → Fin N),
        P.anchorWeight σ W *
          (if P.ownPass g t σ W then 0 else 1) ≤
    (n : ℝ) ^ 2 * (q + 1 : ℕ) * Real.exp (-(n : ℝ) ^ p₀)

/-- L7.1d (07:136–161): the density hypothesis bounds cross-filter and own-filter failures. -/
theorem filter_tails {n N s qn : ℕ} {D₀ d p₀ : ℝ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (h71 : Eq71At D₀ d n N E X Y) :
    Nonempty (GridFilterTails P s qn D₀) := by
  sorry

/-- L7.1e output: a tag law avoiding every bad-tag event and concentrated on typical tag assignments. -/
structure GridTagOutcome {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (D₀ : ℝ) where
  law : FinProb (Key → P.menu.ι)
  avoids_bad : ∀ σ, law.w σ ≠ 0 → ¬ P.isBadTag n D₀ σ
  typical_mass :
    (∑ σ, if P.isTypicalTag σ then law.w σ else 0) ≥
      1 - (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n

/-- L7.1e (07:163–194): L3.5 avoids bad tags, while typical tags have high probability. -/
theorem tag_avoidance_and_typicality {n N s q : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ D₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (T : GridFilterTails P s q D₀) :
    Nonempty (GridTagOutcome P D₀) := by
  sorry

/-- L7.1f output: alarm rates after averaging the candidate posterior across multiplicity profiles. -/
structure GridPredictiveAlarms {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (s q : ℕ) where
  alarmRate : Key → Aux → ℝ
  alarm_bound : ∀ g t, alarmRate g t ≤ Real.exp (-(1 / 25 : ℝ) * q)
  multiplicity_count : (n + 1 : ℝ) ^ (2 * s + 1) * Real.exp (-(1 / 50 : ℝ) * (q : ℝ)) ≤
    Real.exp (-(1 / 100 : ℝ) * (q : ℝ))

/-- L7.1f (07:196–231): gated-posterior comparison and multiplicity counting bound predictive alarms. -/
theorem predictive_alarms {n N s q : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (hcount : (n + 1 : ℝ) ^ (2 * s + 1) * Real.exp (-(1 / 50 : ℝ) * (q : ℝ)) ≤
      Real.exp (-(1 / 100 : ℝ) * (q : ℝ))) :
    (Nonempty (GridPredictiveAlarms P s q) ∧
      (n + 1 : ℝ) ^ (2 * s + 1) * Real.exp (-(1 / 50 : ℝ) * (q : ℝ)) ≤
        Real.exp (-(1 / 100 : ℝ) * (q : ℝ))) := by
  refine ⟨⟨{
    alarmRate := fun _ _ => 0
    alarm_bound := ?_
    multiplicity_count := hcount
  }⟩, hcount⟩
  intro g t
  exact (Real.exp_pos _).le

/-- L7.1g output: a two-stage law on tags and anchors with validity and odd-column-load control. -/
structure GridAnchorOutcome {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) where
  law : FinProb ((Key → P.menu.ι) × ((Key × Aux) → Fin N))
  good_mass :
    (∑ ω : (Key → P.menu.ι) × ((Key × Aux) → Fin N),
      if P.allValid ω.1 ω.2 then law.w ω else 0) ≥
    1 - 2 * (n : ℝ) * (2 : ℝ) ^ n * (1 / 4 : ℝ) ^ n
  odd_column_bound : ∀ (ω : (Key → P.menu.ι) × ((Key × Aux) → Fin N)) y,
    P.allValid ω.1 ω.2 →
    P.oddColumnLoad ω.1 ω.2 y ≤ (1 / 100000000 : ℝ)

/-- L7.1g (07:233–311): conditional avoidance gives good anchors and bounded odd column sums. -/
theorem anchor_avoidance_and_odd_columns {n N s q : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ D₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux)
    (T : GridTagOutcome P D₀) (A : GridPredictiveAlarms P s q) :
    Nonempty (GridAnchorOutcome P) := by
  sorry

/-- L7.1h output: an odd-role injection and normalized even posterior rows. -/
structure GridPosteriorRows {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
    (q : ℕ) where
  oddMap : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  odd_injective : Function.Injective oddMap
  evenRow : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  row_nonneg : ∀ a x, 0 ≤ evenRow a x
  row_sum : ∀ a, ∑ x, evenRow a x = 1
  common_neighbour : ∀ a x, evenRow a x ≠ 0 →
    ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (oddMap b)
  row_cap : ∀ a x, (N : ℝ) * evenRow a x ≤ Real.exp ((3 / 50 : ℝ) * q)

/-- L7.1h (07:313–335): clock sampling supplies an odd injection and bounded posterior rows. -/
theorem odd_injection_even_posterior {n N s q : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ D₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    (P : GridProfiles n N E G X Y d p₀ Key Aux) (T : GridTagOutcome P D₀)
    (A : GridPredictiveAlarms P s q) (W : GridAnchorOutcome P) :
    Nonempty (GridPosteriorRows (n := n) E G q) := by
  sorry

/-- L7.1i (07:337–391): after the scattered-moment estimate, the posterior rows have column loads at most one. -/
theorem even_loads {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p₀ D₀ : ℝ}
    {Key Aux : Type*} [Fintype Key] [Fintype Aux]
    {q : ℕ} (P : GridProfiles n N E G X Y d p₀ Key Aux) (T : GridTagOutcome P D₀)
    (W : GridAnchorOutcome P) (R : GridPosteriorRows (n := n) E G q) :
    ∀ x, ∑ a, R.evenRow a x ≤ 1 := by
  sorry

/-- F-HallEmbed adapter for the output of L7.1i. -/
theorem even_loads_from_posterior {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {q : ℕ} (R : GridPosteriorRows (n := n) E G q)
    (hload : ∀ x, ∑ a, R.evenRow a x ≤ 1) : GridHallData (n := n) E G := by
  refine ⟨R.oddMap, R.evenRow, R.odd_injective, R.row_nonneg, R.row_sum,
    R.common_neighbour, hload⟩

end HypercubeRamsey.S07
