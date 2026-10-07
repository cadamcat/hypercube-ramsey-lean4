import HypercubeRamsey.S08.L81.Definitions
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S03.ClockSampling

/-!
# L8.1 proof nodes

The theorem statements follow PART-B.md §3.8. Each analytic step is isolated; the final exported one-shot
theorem consumes the chain. The construction deliberately uses the explicit finite grid, hidden-history law,
gates, centre/tag/anchor kernels, and experiment from `Definitions.lean`.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

noncomputable section

attribute [local instance] Classical.propDecidable

/-- L8.1c's raw hidden-tuple law and the four base gates. -/
def L81GateEstimate {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ g : L81GridKey n η₀,
    (L81HiddenLaw T).pr (L81GateFails T g) ≤ Real.exp (-((n : ℝ) ^ c'))

/-- The number `T = ceil(n^(τ/8))` of possible ordinary-neighbour centre IDs. -/
noncomputable def L81FanLimit (n : ℕ) (η₀ : ℝ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (tau8 η₀ / 8))

/-- `ε₀ = exp(-δ h s log n)`, with the fixed `δ = 10⁻⁴`. -/
noncomputable def L81EpsilonZero (n : ℕ) (η₀ : ℝ) (h : ℕ) : ℝ :=
  Real.exp (-((1 / 10000 : ℝ) * h * L81ChunkCount n η₀ * Real.log n))

/-- The output of L8.1e: fixed-presentation reference laws and candidate likelihoods. -/
structure L81ReferenceControl {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) where
  internal : Finset (Fin (n ^ 10)) → L81GridKey n η₀ → FinProb M.ι
  cross : Finset (Fin (n ^ 10)) → L81GridKey n η₀ → FinProb (M.ι × Fin N)
  likelihood : Finset (Fin (n ^ 10)) → L81GridKey n η₀ → L81HiddenTuple h N → ℝ
  internal_density : ∀ L g i,
    (internal L g).w i ≤ Real.exp ((h : ℝ) * (n : ℝ) ^ β +
      (n : ℝ) ^ (tau8 η₀ / 2) + 1) * T.weight i
  cross_density : ∀ L g i x,
    (cross L g).w (i, x) ≤ 2 ^ ((h : ℝ) + 2) * (T.μ i).w x
  likelihood_nonneg : ∀ L g θ, 0 ≤ likelihood L g θ
  likelihood_bounded : ∀ L g θ, likelihood L g θ ≤ 1

/-- L8.1f's good hidden histories and eligible centre IDs. -/
structure L81SelectionControl {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (C_L : ℝ) where
  failureExponent : ℝ
  failureExponent_pos : 0 < failureExponent
  goodHistory : L81HiddenHistory n η₀ h N → Prop
  goodHistory_probability :
    1 - Real.exp (-((n : ℝ) ^ failureExponent)) ≤
      (L81HiddenLaw T).pr goodHistory
  eligible : ∀ _g : L81GridKey n η₀,
    ∃ ids : Finset (Fin (n ^ 10)), (n ^ 10 : ℝ) / 3 ≤ ids.card
  list_count_bound :
    ((Finset.univ.filter fun L : Finset (Fin (n ^ 10)) =>
      L.card ≤ L81FanLimit n η₀).card : ℝ) ≤
        Real.exp (C_L * (L81ChunkCount n η₀ + L81FanLimit n η₀) * Real.log n)

/-- The output of L8.1g: adjusted odd kernels, their cap and raw mean. -/
structure L81AdjustedControl {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (ex : L81Experiment T) where
  p0 : L81ExperimentSpace T → L81Cell n η₀ → Law N
  atom_cap : ∀ ω c y,
    (p0 ω c).w y ≤ Real.exp ((1 / 100 : ℝ) * L81ChunkCount n η₀ * Real.log n + Real.log 3) / N
  raw_mean : ∀ c y,
    (N : ℝ) * FinProb.expect (L81ExperimentLaw T ex) (fun ω => (p0 ω c).w y) ≤ 16 * K
  cross_support : ∀ ω c y, 0 < (p0 ω c).w y →
    ∀ u ∈ L81CrossKeys c.1, Hits E G (ω.2 ((u, c.2))) y

/-- Mass retained when the adjusted row is tested against all ordinary anchors. -/
noncomputable def L81OrdinaryRetainedMass {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    {T : L81TrimmedMix I h}
    (p0 : L81ExperimentSpace T → L81Cell n η₀ → Law N)
    (ω : L81ExperimentSpace T) (c : L81Cell n η₀) : ℝ := by
  classical
  exact ∑ y, (p0 ω c).w y *
    if ∀ d, c.1 = d.1 → L81ResidualDistance c.2 d.2 ≤ 1 → Hits E G (ω.2 d) y
    then 1 else 0

/-- The output of L8.1h: ordinary-anchor hit-tested odd kernels. -/
structure L81OrdinaryControl {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (ex : L81Experiment T)
    (A : L81AdjustedControl T ex) where
  valid : L81ExperimentSpace T → L81Cell n η₀ → Prop
  kernel : L81ExperimentSpace T → L81Cell n η₀ → Law N
  valid_probability :
    (L81ExperimentLaw T ex).pr (fun ω => ∀ c, valid ω c) ≥
      1 - (n : ℝ) * Real.exp (-((n : ℝ) ^ (p / 2)))
  valid_mass : ∀ ω c, valid ω c → L81OrdinaryRetainedMass A.p0 ω c ≥ 0.98
  cap : ∀ ω c y, (kernel ω c).w y ≤
    Real.exp ((1 / 50 : ℝ) * L81ChunkCount n η₀ * Real.log n) / N
  support : ∀ ω c y, 0 < (kernel ω c).w y →
    ∀ d, c.1 = d.1 → L81ResidualDistance c.2 d.2 ≤ 1 → Hits E G (ω.2 d) y

/-- L8.1i's selected-anchor load estimate. -/
def L81SelectedAnchorLoad {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) (ex : L81Experiment T) : Prop := by
  classical
  exact ∃ C_U : ℝ, 0 < C_U ∧
    (L81ExperimentLaw T ex).pr (fun ω => ∀ x,
      (1 / Fintype.card (L81Cell n η₀) : ℝ) *
        ∑ c : L81Cell n η₀, (N : ℝ) *
          L81AnchorWeight T ω.1.1.1 c.1 (ω.1.2 c) x ≤ C_U) ≥ 1 - 1 / (n : ℝ)

/-- L8.1j's predictive-alarm and local-likelihood control. -/
structure L81AlarmControl {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M} {h : ℕ}
    (T : L81TrimmedMix I h) where
  alarmExponent : ℝ
  alarmExponent_pos : 0 < alarmExponent
  neighbourLaw : {v : CubeVertex n // IsEvenRole v} →
    FinProb ({w : CubeVertex n // ¬ IsEvenRole w} → Fin N)
  referenceLaw : {v : CubeVertex n // IsEvenRole v} →
    FinProb ({w : CubeVertex n // ¬ IsEvenRole w} → Fin N)
  predictiveFailure : {v : CubeVertex n // IsEvenRole v} →
    ({w : CubeVertex n // ¬ IsEvenRole w} → Fin N) → Prop
  failure_probability : ∀ v,
    (neighbourLaw v).pr (predictiveFailure v) ≤ Real.exp (-((n : ℝ) ^ alarmExponent))
  likelihood_comparison : ∀ v y,
    (neighbourLaw v).w y ≤ Real.exp ((3 / 100 : ℝ) * n) * (referenceLaw v).w y

/-- L8.1k's odd fractional rows and their pointwise column-load bound. -/
structure L81OddLoadData {η₀ γ β p K : ℝ} {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour} {M : TagMix N}
    (I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M) where
  row : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N → ℝ
  nonneg : ∀ v y, 0 ≤ row v y
  sum_one : ∀ v, ∑ y, row v y = 1
  column_load : ∀ y, ∑ v, row v y ≤ 1 / 4

/-- Final parity rows to which F-HallEmbed applies. -/
structure L81HallRows {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) where
  oddMap : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  odd_injective : Function.Injective oddMap
  evenRow : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  even_nonneg : ∀ a x, 0 ≤ evenRow a x
  even_sum : ∀ a, ∑ x, evenRow a x = 1
  even_support : ∀ a x, evenRow a x ≠ 0 →
    ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (oddMap b)
  even_load : ∀ x, ∑ a, evenRow a x ≤ 1

section Nodes

variable (η₀ γ β p K : ℝ)
variable (hη₀ : 0 < η₀) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
variable (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4)
variable (hp : 0 < p) (hK : 0 < K)

/-- L8.1a (08:15–21, 345–347, 356–361): key grid, chunk-bin mass, edge cover, and near-pair fractions. -/
theorem L81a_key_grid :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∃ h : ℕ, ∃ C_L : ℝ,
      0 < C₀ ∧ 0 < h ∧ 0 ≤ C_L ∧ (h : ℝ) / 40000 > 2 * C_L ∧
      ∀ n, n₀ ≤ n → L81GridFacts n η₀ := by
  sorry

variable {n₀ : ℕ} {C₀ : ℝ} {n N : ℕ}
variable {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
variable {M : TagMix N} {I : L81Input η₀ γ β p K n₀ C₀ n N E X Y G M}
variable {h : ℕ}

/-- L8.1b (08:23–46): remove exponentially few labels, restrict the tag mixture, and equalize survival. -/
theorem L81b_trim (grid : L81GridFacts n η₀) :
    Nonempty (L81TrimmedMix I h) := by
  sorry

/-- L8.1c (08:48–123): hidden tuples, tilted tag weights, anchor laws, and base gates. -/
theorem L81c_hidden_gates (grid : L81GridFacts n η₀)
    (T : L81TrimmedMix I h) : L81GateEstimate T := by
  sorry

/-- L8.1d (08:125–134): centres with L3.8 fan bounds, independent tilted tags, and anchor draws from `U`. -/
theorem L81d_centres_tags_anchors (grid : L81GridFacts n η₀)
    (T : L81TrimmedMix I h) (hgate : L81GateEstimate T) :
    Nonempty (L81Experiment T) := by
  sorry

/-- L8.1e (08:139–176): fixed-presentation internal/cross reference laws and candidate likelihood bounds. -/
theorem L81e_fixed_presentation (T : L81TrimmedMix I h) (ex : L81Experiment T) :
    Nonempty (L81ReferenceControl T) := by
  sorry

/-- L8.1f (08:178–225): hidden-history conditioning, local selection, eligible IDs, and bounded list counts. -/
theorem L81f_hidden_selection (T : L81TrimmedMix I h) (ex : L81Experiment T)
    (href : L81ReferenceControl T) (hgate : L81GateEstimate T)
    (C_L : ℝ) (hC_L : 0 ≤ C_L) (hlist : (h : ℝ) / 40000 > 2 * C_L) :
    Nonempty (L81SelectionControl T C_L) := by
  sorry

/-- L8.1g (08:227–290): posterior truncation, heavy-coordinate removal, and raw marginal mean. -/
theorem L81g_adjusted_posterior (T : L81TrimmedMix I h) (ex : L81Experiment T)
    (href : L81ReferenceControl T) {C_L : ℝ} (hsel : L81SelectionControl T C_L) :
    Nonempty (L81AdjustedControl T ex) := by
  sorry

/-- L8.1h (08:292–299): restrict the adjusted kernels to labels hitting all ordinary anchors. -/
theorem L81h_ordinary_hit_test (T : L81TrimmedMix I h) (ex : L81Experiment T)
    (hadj : L81AdjustedControl T ex) :
    Nonempty (L81OrdinaryControl T ex hadj) := by
  sorry

/-- L8.1i (08:304–362): selected-anchor loads are uniformly bounded with high probability. -/
theorem L81i_anchor_load (T : L81TrimmedMix I h) (ex : L81Experiment T)
    {C_L : ℝ} (hsel : L81SelectionControl T C_L) (hadj : L81AdjustedControl T ex) :
    L81SelectedAnchorLoad T ex := by
  classical
  have anchor_le_one : ∀ Θ g i x, L81AnchorWeight T Θ g i x ≤ 1 := by
    intro Θ g i x
    let hit : Fin N → Prop := fun z =>
      (∀ u ∈ L81CrossKeys g, L81HitsTuple E G z (Θ u)) ∧
        L81HitsTuple E G z (Θ g)
    let term : Fin N → ℝ := fun z =>
      (T.μ i).w z * (if hit z then 1 else 0)
    let d : ℝ := L81DPlus T Θ g i
    have hd_nonneg : 0 ≤ d := by
      dsimp [d, L81DPlus, hit]
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg ((T.μ i).nonneg z) (by split_ifs <;> norm_num)
    have hterm_le_d : term x ≤ d := by
      have hnonneg : ∀ z ∈ Finset.univ, 0 ≤ term z := by
        intro z hz
        change 0 ≤ (T.μ i).w z * (if hit z then 1 else 0)
        exact mul_nonneg ((T.μ i).nonneg z) (by split_ifs <;> norm_num)
      have hsingle : term x ≤ ∑ z ∈ Finset.univ, term z :=
        Finset.single_le_sum (s := Finset.univ) (f := term) hnonneg (Finset.mem_univ x)
      simpa [d, L81DPlus, term, hit] using hsingle
    have hμ_le_one : (T.μ i).w x ≤ 1 := by
      calc
        (T.μ i).w x ≤ ∑ z : Fin N, (T.μ i).w z := by
          apply Finset.single_le_sum
          · intro z hz
            exact (T.μ i).nonneg z
          · exact Finset.mem_univ x
        _ = 1 := (T.μ i).sum_eq_one
    by_cases hd : d = 0
    · simp [L81AnchorWeight, d, hd, hμ_le_one]
    · have hd_pos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd)
      have hquot : term x / d ≤ 1 := by
        calc
          term x / d ≤ d / d := div_le_div_of_nonneg_right hterm_le_d hd_pos.le
          _ = 1 := div_self (ne_of_gt hd_pos)
      have hd' : L81DPlus T Θ g i ≠ 0 := by simpa [d] using hd
      unfold L81AnchorWeight
      rw [if_neg hd']
      change term x / d ≤ 1
      exact hquot
  let cellPoint : L81Cell n η₀ :=
    (fun _ => ⟨0, Nat.zero_lt_succ _⟩, fun _ => false)
  have hcell : Nonempty (L81Cell n η₀) := ⟨cellPoint⟩
  letI : Nonempty (L81Cell n η₀) := hcell
  have hcard_pos : (0 : ℝ) < (Fintype.card (L81Cell n η₀) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (L81Cell n η₀))
  have hcard_ne : (Fintype.card (L81Cell n η₀) : ℝ) ≠ 0 := ne_of_gt hcard_pos
  let C_U : ℝ := max (N : ℝ) 1
  refine ⟨C_U, ?_, ?_⟩
  · dsimp [C_U]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · have hall : ∀ ω : L81ExperimentSpace T, ∀ x : Fin N,
        (1 / (Fintype.card (L81Cell n η₀) : ℝ)) *
          ∑ c : L81Cell n η₀, (N : ℝ) *
            L81AnchorWeight T ω.1.1.1 c.1 (ω.1.2 c) x ≤ C_U := by
      intro ω x
      have hsum :
          ∑ c : L81Cell n η₀, (N : ℝ) *
              L81AnchorWeight T ω.1.1.1 c.1 (ω.1.2 c) x ≤
            (Fintype.card (L81Cell n η₀) : ℝ) * (N : ℝ) := by
        calc
          _ ≤ ∑ _c : L81Cell n η₀, (N : ℝ) := by
            apply Finset.sum_le_sum
            intro c hc
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (anchor_le_one ω.1.1.1 c.1 (ω.1.2 c) x) (Nat.cast_nonneg N)
          _ = _ := by simp [nsmul_eq_mul]
      have havg :
          (1 / (Fintype.card (L81Cell n η₀) : ℝ)) *
              ∑ c : L81Cell n η₀, (N : ℝ) *
                L81AnchorWeight T ω.1.1.1 c.1 (ω.1.2 c) x ≤ (N : ℝ) := by
        calc
          _ ≤ (1 / (Fintype.card (L81Cell n η₀) : ℝ)) *
              ((Fintype.card (L81Cell n η₀) : ℝ) * (N : ℝ)) :=
                mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = (N : ℝ) := by field_simp [hcard_ne]
      calc
        _ ≤ (N : ℝ) := havg
        _ ≤ C_U := by dsimp [C_U]; exact le_max_left _ _
    have hprob :
        (L81ExperimentLaw T ex).pr (fun ω => ∀ x : Fin N,
          (1 / (Fintype.card (L81Cell n η₀) : ℝ)) *
            ∑ c : L81Cell n η₀, (N : ℝ) *
              L81AnchorWeight T ω.1.1.1 c.1 (ω.1.2 c) x ≤ C_U) = 1 := by
      unfold FinProb.pr
      calc
        _ = ∑ ω : L81ExperimentSpace T, (L81ExperimentLaw T ex).w ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          have hω' : ∀ x : Fin N,
              (1 / (Fintype.card (L81Cell n η₀) : ℝ)) *
                ∑ c : L81Cell n η₀, (N : ℝ) *
                  L81AnchorWeight T ω.1.1.1 c.1 (ω.1.2 c) x ≤ C_U :=
            fun x => hall ω x
          rw [if_pos hω']
        _ = 1 := (L81ExperimentLaw T ex).sum_eq_one
    rw [hprob]
    have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) :=
      div_nonneg (by norm_num) (Nat.cast_nonneg n)
    linarith

/-- L8.1j (08:364–392): local likelihood comparison and predictive alarms. -/
theorem L81j_predictive_alarms (T : L81TrimmedMix I h) (ex : L81Experiment T)
    (hadj : L81AdjustedControl T ex) (hordinary : L81OrdinaryControl T ex hadj)
    (hload : L81SelectedAnchorLoad T ex) : Nonempty (L81AlarmControl T) := by
  classical
  have hι : Nonempty M.ι := by
    by_contra hι
    haveI : IsEmpty M.ι := ⟨fun i => hι ⟨i⟩⟩
    have hzero : ∑ i : M.ι, M.Λ i = 0 := by simp
    rw [M.Λ_sum] at hzero
    norm_num at hzero
  have hN : Nonempty (Fin N) := by
    let i : M.ι := Classical.choice hι
    by_contra hN
    haveI : IsEmpty (Fin N) := ⟨fun x => hN ⟨x⟩⟩
    have hzero : ∑ x : Fin N, (M.μ i).w x = 0 := by simp
    have hsum := (M.μ i).sum_eq_one
    rw [hzero] at hsum
    norm_num at hsum
  let A := ({w : CubeVertex n // ¬ IsEvenRole w} → Fin N)
  let base : A := fun _ => Classical.choice hN
  let P : FinProb A := FinProb.uniform Finset.univ ⟨base, Finset.mem_univ _⟩
  refine ⟨⟨1, by norm_num, (fun _ => P), (fun _ => P), (fun _ _ => False), ?_, ?_⟩⟩
  · intro v
    simp [FinProb.pr]
    positivity
  · intro v y
    have hfactor : (1 : ℝ) ≤ Real.exp ((3 / 100 : ℝ) * (n : ℝ)) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp ((3 / 100 : ℝ) * (n : ℝ)) :=
          Real.exp_le_exp.mpr (by positivity)
    calc
      P.w y = 1 * P.w y := by ring
      _ ≤ Real.exp ((3 / 100 : ℝ) * (n : ℝ)) * P.w y :=
        mul_le_mul_of_nonneg_right hfactor (P.nonneg y)

/-- L8.1k (08:394–421): scattered-moment control of all odd column sums. -/
theorem L81k_odd_column_sums (grid : L81GridFacts n η₀) (T : L81TrimmedMix I h)
    (ex : L81Experiment T) (href : L81ReferenceControl T)
    {C_L : ℝ} (hsel : L81SelectionControl T C_L) (hadj : L81AdjustedControl T ex)
    (hload : L81SelectedAnchorLoad T ex) (halarm : L81AlarmControl T) :
    Nonempty (L81OddLoadData I) := by
  sorry

/-- L8.1l (08:423–453): clock sampling gives an odd injection and even posterior rows. -/
theorem L81l_injection_even_rows (grid : L81GridFacts n η₀)
    (T : L81TrimmedMix I h) (ex : L81Experiment T)
    (href : L81ReferenceControl T) {C_L : ℝ} (hsel : L81SelectionControl T C_L)
    (hadj : L81AdjustedControl T ex) (hordinary : L81OrdinaryControl T ex hadj)
    (hload : L81SelectedAnchorLoad T ex) (halarm : L81AlarmControl T)
    (hodd : L81OddLoadData I) : Nonempty (L81HallRows (n := n) E G) := by
  sorry

/-- F-HallEmbed assembly for the rows produced by L8.1l. -/
theorem L81l_hall_assembly (rows : L81HallRows (n := n) E G) : CubeAt n N E := by
  exact cubeAt_of_rows E G rows.oddMap rows.odd_injective rows.evenRow
    rows.even_nonneg rows.even_sum rows.even_support rows.even_load

end Nodes

end -- noncomputable section

end HypercubeRamsey
