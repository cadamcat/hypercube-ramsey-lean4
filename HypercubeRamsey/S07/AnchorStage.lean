import HypercubeRamsey.S07.TagStage
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S07.AnchorStage_q_s07_anchor
import HypercubeRamsey.S07.AnchorStage_q_s07_anchor_odd
import HypercubeRamsey.S07.AnchorStage_q_s07_anchor_moments
import HypercubeRamsey.S07.AnchorStage_q_s07_anchor_product
import HypercubeRamsey.S07.AnchorStage_q_s07_anchor_invalid

/-!
# L7.1, Steps 2–4: cell failure, predictive alarms, anchor avoidance and odd column sums

Source: `sections/07-…tex`, lines 150–161 (cell failure at fixed tags), 196–245 (alarms), 247–311 (anchor
conditioning and odd loads).
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

/-- L7.1d at fixed tags (07:150–161, 166): the raw failure probability of a cell is at most the key's
cross-failure probability (the cross anchors `W (h, t)` are independent with laws `μ_{σ h}`, as in
`crossFailKey`, for every `t`) plus `n²(q+1)e^{-n^p}` (the `q + 1` own anchors are independent draws from
`μ_{σ g}` and every label of `ν_{σ g}` has degree `≥ 1 - e^{-n^p}` into it; Markov's inequality). -/
theorem cell_invalid_prob (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hn : 1 ≤ n)
    (hloc : GeomLocal Γ) (σ : Γ.Key → M.ι) : CellInvalidBound Γ M σ := by
  classical
  intro c
  let CrossBad : (Γ.Cell → Fin N) → Prop := fun W =>
    ¬ CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1
  let OwnBad : (Γ.Cell → Fin N) → Prop := fun W =>
    ¬ OwnValid Γ M (σ c.1) W c
  have hUnion := FinProb.pr_union (rawAnchors Γ M σ) CrossBad OwnBad
  have hCross := crossFail_pr_eq_key_q_s07_anchor Γ M σ c
  have hOwn : (rawAnchors Γ M σ).pr OwnBad ≤
      (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) := by
    simpa [OwnBad] using ownFail_pr_bound_q_s07_anchor Γ M hn hloc σ c
  have hbad (W : Γ.Cell → Fin N) :
      (¬ CellValid Γ M σ W c) ↔ CrossBad W ∨ OwnBad W := by
    unfold CellValid CrossBad OwnBad
    constructor
    · intro h
      by_cases hc : CrossValidRow Γ M (σ c.1) (fun h => W (h, c.2)) c.1
      · right
        intro ho
        exact h ⟨hc, ho⟩
      · exact Or.inl hc
    · intro h hv
      rcases h with hcross | hown
      · exact hcross hv.1
      · exact hown hv.2
  have hbadPred : (fun W => ¬ CellValid Γ M σ W c) =
      (fun W => CrossBad W ∨ OwnBad W) := by
    funext W
    exact propext (hbad W)
  have hUnion' : (rawAnchors Γ M σ).pr (fun W => ¬ CellValid Γ M σ W c) ≤
      (rawAnchors Γ M σ).pr CrossBad + (rawAnchors Γ M σ).pr OwnBad := by
    calc
      (rawAnchors Γ M σ).pr (fun W => ¬ CellValid Γ M σ W c) =
          (rawAnchors Γ M σ).pr (fun W => CrossBad W ∨ OwnBad W) :=
        congrArg (fun A => (rawAnchors Γ M σ).pr A) hbadPred
      _ ≤ (rawAnchors Γ M σ).pr CrossBad + (rawAnchors Γ M σ).pr OwnBad := hUnion
  calc
    (rawAnchors Γ M σ).pr (fun W => ¬ CellValid Γ M σ W c) ≤
        (rawAnchors Γ M σ).pr CrossBad + (rawAnchors Γ M σ).pr OwnBad := by
      exact hUnion'
    _ ≤ (rawAnchors Γ M σ).pr CrossBad +
        (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) :=
      by linarith [hOwn]
    _ = crossFailKey Γ M σ c.1 +
        (n : ℝ) ^ 2 * ((q : ℝ) + 1) * Real.exp (-(n : ℝ) ^ p) := by rw [hCross]

/-- L7.1f(ii) (07:219–231): `E_{W_{g,t}} r_v ≤ e^{-.04q}` with everything else fixed: the integrand of `r_v`
over the role's anchor is the data subdensity `M_v`, `Q_v` does not move, and Lemma 3.7's first assertion
(`gated_posterior`, `ε = e^{-.04q}`) bounds the failure mass. -/
theorem alarm_mean (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hupd : StarRefUpdate Γ M) : AlarmMean Γ M := by
  classical
  unfold AlarmMean
  intro σ W a
  let c : Γ.Cell := Γ.key a.1
  let π : Law N := M.μ (σ (Γ.key a.1).1)
  let Q : FinProb (Fin n → Fin N) :=
    FinProb.pi fun j => delRow Γ M σ W (Γ.key (cubeFlip a.1 j)) c
  let F : Fin N → (Fin n → Fin N) → ℝ := fun z y => starLik Γ M σ W a.1 z y
  let m : (Fin n → Fin N) → ℝ := fun y => ∑ z, π.w z * F z y
  let ε : ℝ := Real.exp (-(4 / 100 : ℝ) * q)
  have hε : 0 < ε := Real.exp_pos _
  change (∑ z, π.w z * alarmRate Γ M σ (Function.update W c z) a.1) ≤ ε
  have hrow : ∀ W' c' y, 0 ≤ cellRow Γ M σ W' c' y := by
    intro W' c' y
    unfold cellRow
    split_ifs with hv
    · by_cases hm : 0 < filterMass E G (M.ν (σ c'.1)) (cellLabels Γ W' c')
      · exact (filt_probability_and_support E G (M.ν (σ c'.1))
          (cellLabels Γ W' c') hm).1 y
      · simp [filt, hm]
    · exact le_rfl
  have hF0 : ∀ z y, 0 ≤ F z y := by
    intro z y
    dsimp [F, starLik]
    exact Finset.prod_nonneg fun j hj => hrow _ _ _
  have hQ : ∀ y, Q.w y = starRef Γ M σ W a.1 y := by
    intro y
    simp [Q, starRef, FinProb.pi, c]
  have hmarg : ∀ z y,
      starMarg Γ M σ (Function.update W c z) a.1 y = m y := by
    intro z y
    simp [starMarg, starLik, m, F, π, c, Function.update]
  have hRef : ∀ z y,
      starRef Γ M σ (Function.update W c z) a.1 y = Q.w y := by
    intro z y
    rw [show Function.update W c z = Function.update W (Γ.key a.1) z by rfl]
    rw [hupd σ W a.1 z]
    exact (hQ y).symm
  have hbad : ∀ z y,
      PredFail Γ M σ (Function.update W c z) a.1 y ↔
        (m y < ε * Q.w y ∨ m y = 0) := by
    intro z y
    simp [PredFail, hmarg z y, hRef z y, ε, or_comm]
  have hlik : ∀ z y,
      (∏ j, cellRow Γ M σ (Function.update W c z)
        (Γ.key (cubeFlip a.1 j)) (y j)) = F z y := by
    intro z y
    simp [F, starLik, c, Function.update]
  have hgate :
      (∑ y, if m y < ε * Q.w y ∨ m y = 0 then m y else 0) ≤ ε := by
    simpa [m, F, π, starMarg] using
      (gated_posterior π F hF0 Q ε 0 hε).1
  have hrate :
      (∑ z, π.w z * alarmRate Γ M σ (Function.update W c z) a.1) =
        ∑ y, if m y < ε * Q.w y ∨ m y = 0 then m y else 0 := by
    unfold alarmRate
    calc
      (∑ z, π.w z *
          ∑ y, (∏ j, cellRow Γ M σ (Function.update W c z)
            (Γ.key (cubeFlip a.1 j)) (y j)) *
              (if PredFail Γ M σ (Function.update W c z) a.1 y then 1 else 0)) =
          ∑ z, ∑ y, π.w z * (F z y *
            (if m y < ε * Q.w y ∨ m y = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [hlik z y, (propext (hbad z y))]
        simp
      _ = ∑ y, ∑ z, π.w z * (F z y *
            (if m y < ε * Q.w y ∨ m y = 0 then 1 else 0)) := by
        rw [Finset.sum_comm]
      _ = ∑ y, if m y < ε * Q.w y ∨ m y = 0 then m y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hb : m y < ε * Q.w y ∨ m y = 0
        · simp [hb, m]
        · simp [hb]
  rw [hrate]
  exact hgate

/-- L7.1f(iii) (07:233–240): the alarm rate of an even role depends on it only through its cell and the
multiset of its neighbours' cells; at a cell `(g, t)` that multiset is fixed by the counts at `(g, t)` and at
the `≤ 2s` cells `(h, t)`, `h ∈ E(g)` (each auxiliary neighbour occurs once), so at most `(n+1)^{2s+1}` formulas
occur. -/
theorem alarm_reps (Γ : GridGeom d n s ℓ q) (hloc : GeomLocal Γ) (M : Menu7 n N E G X Y d p κ) :
    AlarmReps Γ M := by
  exact alarm_reps_q_s07_anchor Γ hloc M

/-- L7.1f (07:240–245): a union over the alarm formulas of one cell and Markov's inequality,
`(n+1)^{2s+1} e^{.02q} e^{-.04q}`. -/
theorem alarm_prob (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hmean : AlarmMean Γ M)
    (hreps : AlarmReps Γ M) (σ : Γ.Key → M.ι) : AlarmProb Γ M σ := by
  classical
  unfold AlarmProb
  intro W c
  obtain ⟨S, hScard, hSkey, hrep⟩ := hreps c
  let μ : Law N := M.μ (σ c.1)
  let t : ℝ := Real.exp (-(2 / 100 : ℝ) * q)
  let r : EvenRole n → Fin N → ℝ := fun a z =>
    alarmRate Γ M σ (Function.update W c z) a.1
  have ht : 0 < t := Real.exp_pos _
  change (∑ z, μ.w z *
    (if Alarm Γ M σ (Function.update W c z) c then 1 else 0)) ≤
      ((n : ℝ) + 1) ^ (2 * s + 1) * t
  have hrow : ∀ W' c' y, 0 ≤ cellRow Γ M σ W' c' y := by
    intro W' c' y
    unfold cellRow
    split_ifs with hv
    · by_cases hm : 0 < filterMass E G (M.ν (σ c'.1)) (cellLabels Γ W' c')
      · exact (filt_probability_and_support E G (M.ν (σ c'.1))
          (cellLabels Γ W' c') hm).1 y
      · simp [filt, hm]
    · exact le_rfl
  have hrnonneg (a : EvenRole n) (z : Fin N) : 0 ≤ r a z := by
    unfold r alarmRate
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg
    · exact Finset.prod_nonneg fun j hj => hrow _ _ _
    · split_ifs <;> norm_num
  have hAlarm (z : Fin N) :
      Alarm Γ M σ (Function.update W c z) c ↔
        ∃ a ∈ S, t < r a z := by
    constructor
    · rintro ⟨a, ha, hlt⟩
      obtain ⟨a', ha', heq⟩ := hrep a ha
      refine ⟨a', ha', ?_⟩
      simpa [r, t, heq σ (Function.update W c z)] using hlt
    · rintro ⟨a, ha, hlt⟩
      exact ⟨a, hSkey a ha, by simpa [r, t] using hlt⟩
  have hmean' (a : EvenRole n) (ha : a ∈ S) :
      μ.expect (r a) ≤ Real.exp (-(4 / 100 : ℝ) * q) := by
    change (∑ z, (M.μ (σ c.1)).w z *
      alarmRate Γ M σ (Function.update W c z) a.1) ≤ _
    simpa [μ, r, hSkey a ha] using hmean σ W a
  have hExp : Real.exp (-(4 / 100 : ℝ) * q) / t =
      Real.exp (-(2 / 100 : ℝ) * q) := by
    rw [show t = Real.exp (-(2 / 100 : ℝ) * q) by rfl, ← Real.exp_sub]
    congr 1
    ring
  have htail (a : EvenRole n) (ha : a ∈ S) :
      μ.pr (fun z => t < r a z) ≤ Real.exp (-(2 / 100 : ℝ) * q) := by
    have hMarkov := FinProb.markov μ (r a) t (fun z => hrnonneg a z) ht
    have hstrict : μ.pr (fun z => t < r a z) ≤ μ.pr (fun z => t ≤ r a z) := by
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro z hz
      by_cases hs : t < r a z
      · simp [hs, le_of_lt hs]
      · simp [hs]
        split_ifs
        · exact μ.nonneg z
        · rfl
    calc
      μ.pr (fun z => t < r a z) ≤ μ.pr (fun z => t ≤ r a z) := hstrict
      _ ≤ μ.expect (r a) / t := hMarkov
      _ ≤ Real.exp (-(4 / 100 : ℝ) * q) / t :=
        div_le_div_of_nonneg_right (hmean' a ha) ht.le
      _ = Real.exp (-(2 / 100 : ℝ) * q) := hExp
  have hIndicator (z : Fin N) :
      (if (∃ a ∈ S, t < r a z) then (1 : ℝ) else 0) ≤
        ∑ a ∈ S, if t < r a z then (1 : ℝ) else 0 := by
    by_cases hex : ∃ a ∈ S, t < r a z
    · obtain ⟨a, ha, hlt⟩ := hex
      have hfiltered : (S.filter (fun b => t < r b z)).Nonempty :=
        ⟨a, Finset.mem_filter.mpr ⟨ha, hlt⟩⟩
      have hcard : 1 ≤ (S.filter (fun b => t < r b z)).card := by
        have hpos := Finset.card_pos.mpr hfiltered
        omega
      have hsumcard :
          (∑ b ∈ S, if t < r b z then (1 : ℝ) else 0) =
            ((S.filter (fun b => t < r b z)).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [nsmul_eq_mul]
      calc
        (if (∃ b ∈ S, t < r b z) then (1 : ℝ) else 0) = 1 := by
          simp [show ∃ b ∈ S, t < r b z from ⟨a, ha, hlt⟩]
        _ ≤ (S.filter (fun b => t < r b z)).card := by exact_mod_cast hcard
        _ = ∑ b ∈ S, if t < r b z then (1 : ℝ) else 0 := hsumcard.symm
    · have hzero : (if (∃ a ∈ S, t < r a z) then (1 : ℝ) else 0) = 0 := by
        simp [hex]
      rw [hzero]
      exact Finset.sum_nonneg fun a ha => by split_ifs <;> norm_num
  calc
    (∑ z, μ.w z *
        (if Alarm Γ M σ (Function.update W c z) c then 1 else 0)) =
      ∑ z, μ.w z * (if (∃ a ∈ S, t < r a z) then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [propext (hAlarm z)]
        simp
    _ ≤ ∑ z, μ.w z * ∑ a ∈ S, if t < r a z then 1 else 0 := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hIndicator z) (μ.nonneg z)
    _ = ∑ a ∈ S, μ.pr (fun z => t < r a z) := by
        calc
          (∑ z, μ.w z * ∑ a ∈ S, if t < r a z then 1 else 0) =
              ∑ z, ∑ a ∈ S, μ.w z * (if t < r a z then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.mul_sum]
          _ = ∑ a ∈ S, ∑ z, μ.w z * (if t < r a z then 1 else 0) := by
            rw [Finset.sum_comm]
          _ = ∑ a ∈ S, μ.pr (fun z => t < r a z) := by
            apply Finset.sum_congr rfl
            intro a ha
            unfold FinProb.pr
            apply Finset.sum_congr rfl
            intro z hz
            by_cases h : t < r a z <;> simp [h]
    _ ≤ ∑ a ∈ S, Real.exp (-(2 / 100 : ℝ) * q) := by
        apply Finset.sum_le_sum
        intro a ha
        exact htail a ha
    _ = (S.card : ℝ) * Real.exp (-(2 / 100 : ℝ) * q) := by
        simp [nsmul_eq_mul]
    _ ≤ ((n : ℝ) + 1) ^ (2 * s + 1) * t := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        · exact_mod_cast hScard

end Nodes

/-- L7.1g, first part (07:247–259): at tags avoiding every `B_g` the cell events satisfy the local-lemma input
with charge `n^{-D₀/4}`: `CellBad` at `c` reads the anchors within distance two of `c`, two events meet only
within distance four (at most `(2s+q+1)^4` cells), and
`Pr(CellBad) ≤ n^{-D₀/2} + n²(q+1)e^{-n^p} + (n+1)^{2s+1}e^{-.02q} ≤ n^{-D₀/4}(1 - n^{-D₀/4})^{(2s+q+1)^4}`
for large `n`, since `16d < D₀/4`. -/
theorem anchor_lll (D₀ d p : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι),
      GeomFacts Γ → CellInvalidBound Γ M σ → AlarmProb Γ M σ → (∀ g, ¬ TagBad Γ M D₀ σ g) →
      AnchorLLL Γ M D₀ σ := by
  obtain ⟨n₀, hnum⟩ := anchor_lll_numeric_q_s07_anchor D₀ d p hD₀ hd hd' hp
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y κ Γ M σ hGeom hInvalid hAlarm hTag
  have hbound := hnum n hn
  exact anchorLLL_of_local_bounds_q_s07_anchor Γ M σ hGeom hInvalid hAlarm hTag
    hbound.1 hbound.2.1 (by simpa [Geom] using hbound.2.2.2)

/-- L7.1g, moments (07:280–298): for odd roles whose grid keys are pairwise at distance at least three, the
two-stage law (tag law, then anchor law) satisfies `E ∏ Z_{u_j} ≤ 4^m ∏ d_{u_j}`, `Z_u = N p_{g(u),t(u)}(y)`,
`d_u` the raw mean.  First remove the cell events touching the disjoint lists (at most `(2s+q+1)^3` each, factor
`2` per role) and integrate the raw anchors; then remove the tag events touching the disjoint key balls (at most
`(2s+1)^2` each, factor `2` per role) and integrate the raw tags; `12d < D₀/4`. -/
theorem odd_moment (D₀ d : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (Q : Γ.Key → FinProb M.ι),
      CondProductBound → GeomFacts Γ → TagLLL Γ M Q D₀ →
      (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ) → OddMoment Γ M Q D₀ := by
  obtain ⟨n₀, hnum⟩ := anchor_lll_numeric_q_s07_anchor D₀ d 1 hD₀ hd hd' (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y p κ Γ M Q hCPB hGeom hTag hAnchor
  have hbound := hnum n hn
  have hcharge : xL D₀ n * ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 4 ≤ 1 / 2 :=
    hbound.2.2.1
  exact odd_moment_at_n_q_s07_anchor Γ M Q D₀ hCPB hGeom hTag hAnchor
    hbound.1 hbound.2.1 (by simpa [Geom] using hcharge)

/-- L7.1g, odd loads (07:300–311): Lemma 3.6 with near = grid distance at most two (fraction
`(2s+1)²(2n^{-d/4})^s`, cap `L`), comparison means of average at most `K` (profile (ii) and the uniform
auxiliary word), and a union over labels; the column sum is `|B|/N` times the normalized average, at most
`θ₀ = 10⁻⁸` once `N ≥ C₀ 2^n`. -/
theorem odd_loads (D₀ d K : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (P : Profiles7 Γ M K),
        GeomFacts Γ → RowCap Γ M → OddMoment Γ M P.Q D₀ →
      (FinProb.bind (tagLaw Γ M P.Q D₀) (anchorLaw Γ M)).pr
            (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  obtain ⟨nSmall, hsmall⟩ := odd_loads_small_q_s07_anchor d hd
  let C₀ : ℝ := 800000000 * (K + 1)
  refine ⟨max nSmall 2, C₀, ?_⟩
  intro n N hLarge E G X Y p κ Γ M P hGeom hRowCap hMoment
  have hnSmall : nSmall ≤ n := le_trans (le_max_left _ _) hLarge.1
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hLarge.1
  have hSmall := hsmall n hnSmall
  let R : FinProb ((Γ.Key → M.ι) × (Γ.Cell → Fin N)) :=
    FinProb.bind (tagLaw Γ M P.Q D₀) (anchorLaw Γ M)
  let Z : OddRole n → Fin N → ((Γ.Key → M.ι) × (Γ.Cell → Fin N)) → ℝ :=
    fun u y ω => (N : ℝ) * cellRow Γ M ω.1 ω.2 (Γ.key u.1) y
  let dmean : OddRole n → Fin N → ℝ :=
    fun u y => (N : ℝ) * rawRowMean Γ M P.Q (Γ.key u.1) y
  let near : OddRole n → Finset (OddRole n) := fun u =>
    Finset.univ.filter fun v => Γ.keyDist (Γ.key v.1).1 (Γ.key u.1).1 ≤ 2
  let f : ℝ := ((2 * gS d n + 1 : ℕ) : ℝ) ^ 2 *
    (2 * (n : ℝ) ^ (-(d / 4))) ^ (gS d n)
  let Lcell : ℝ := cellCap d n (gS d n)
  have hcardPos : 0 < (Fintype.card (OddRole n) : ℝ) := by
    rw [hGeom.counts.odd_card]
    positivity
  have hcardNatPos : 0 < Fintype.card (OddRole n) := by exact_mod_cast hcardPos
  letI : Nonempty (OddRole n) := Fintype.card_pos_iff.mp hcardNatPos
  have hZ0 : ∀ u y ω, 0 ≤ Z u y ω := by
    intro u y ω
    dsimp [Z]
    apply mul_nonneg (Nat.cast_nonneg N)
    unfold cellRow
    split_ifs with hv
    · by_cases hm : 0 < filterMass E G (M.ν (ω.1 (Γ.key u.1).1))
        (cellLabels Γ ω.2 (Γ.key u.1))
      · exact (filt_probability_and_support E G
          (M.ν (ω.1 (Γ.key u.1).1)) (cellLabels Γ ω.2 (Γ.key u.1)) hm).1 y
      · simp [filt, hm]
    · exact le_rfl
  have hZL : ∀ u y ω, ω ∈ Finset.univ → Z u y ω ≤ Lcell := by
    intro u y ω _
    exact hRowCap ω.1 ω.2 (Γ.key u.1) y
  have hDmean0 : ∀ u y, 0 ≤ dmean u y := by
    intro u y
    dsimp [dmean]
    exact mul_nonneg (Nat.cast_nonneg N)
      (odd_raw_row_mean_nonneg_q_s07_anchor Γ M P.Q (Γ.key u.1) y)
  have hmean : ∀ y, (Fintype.card (OddRole n) : ℝ)⁻¹ *
      ∑ u, dmean u y ≤ K := by
    intro y
    simpa [dmean] using
      (odd_raw_row_mean_average_le_q_s07_anchor Γ M P hGeom.counts y)
  have hself : ∀ u, u ∈ near u := by
    intro u
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [GridGeom.keyDist]
  have hnear : ∀ u, ((near u).card : ℝ) ≤ f * Fintype.card (OddRole n) := by
    intro u
    simpa [near, f, mul_assoc, mul_left_comm, mul_comm] using
      hGeom.near.odd_nearKey u
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hLcell : 0 ≤ Lcell := by dsimp [Lcell, cellCap]; positivity
  have hsmall' : (n : ℝ) * f * Lcell ≤ 1 := by
    simpa [f, Lcell, mul_assoc, mul_left_comm, mul_comm] using hSmall
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    have hNle : Fintype.card (Fin N) ≤ n * 2 ^ n := by
      simpa using hLarge.2.2
    exact_mod_cast hNle
  have hjoint : ∀ y (m : ℕ), m ≤ n → ∀ u : Fin m → OddRole n,
      (∀ i j, j < i → u i ∉ near (u j)) →
        ∑ ω ∈ Finset.univ, R.w ω * ∏ i, Z (u i) y ω ≤
          4 ^ m * ∏ i, dmean (u i) y := by
    intro y m hm u hsep
    have hsepKeys : ∀ i j, i ≠ j →
        3 ≤ Γ.keyDist (Γ.key (u i).1).1 (Γ.key (u j).1).1 := by
      intro i j hne
      by_cases hji : j < i
      · have hnot := hsep i j hji
        have hdist : ¬ Γ.keyDist (Γ.key (u i).1).1 (Γ.key (u j).1).1 ≤ 2 := by
          simpa [near] using hnot
        omega
      · have hij : i < j := by omega
        have hnot := hsep j i hij
        have hdist : ¬ Γ.keyDist (Γ.key (u j).1).1 (Γ.key (u i).1).1 ≤ 2 := by
          simpa [near] using hnot
        have hsymm : Γ.keyDist (Γ.key (u i).1).1 (Γ.key (u j).1).1 =
            Γ.keyDist (Γ.key (u j).1).1 (Γ.key (u i).1).1 := by
          simp [GridGeom.keyDist, Nat.dist_comm]
        rw [hsymm]
        omega
    have hmoment := hMoment y m hm u hsepKeys
    simpa [R, Z, dmean, FinProb.expect] using hmoment
  have hnpos : 0 < n := by omega
  have hsc := HypercubeRamsey.scatteredMoments_union_labels
    R Finset.univ Z hZ0 Lcell hLcell hZL near hself f hf hnear n hnpos
    (4 : ℝ) K (by norm_num) hK dmean hDmean0 hmean hjoint hsmall' hlabels
  have hC₀pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hNlow : C₀ * (2 : ℝ) ^ n ≤ (N : ℝ) := hLarge.2.1
  have hTwoPow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ n = (2 : ℝ) ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = (2 : ℝ) ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (n - 1) := by ring
  have hCardEq : (Fintype.card (OddRole n) : ℝ) = (2 : ℝ) ^ (n - 1) :=
    by exact_mod_cast hGeom.counts.odd_card
  have hNbase : (2 * C₀) * (Fintype.card (OddRole n) : ℝ) ≤ (N : ℝ) := by
    have hEq : C₀ * (2 : ℝ) ^ n =
        (2 * C₀) * (Fintype.card (OddRole n) : ℝ) := by
      rw [hTwoPow, hCardEq]
      ring
    rw [← hEq]
    exact hNlow
  have hNratio : 2 * C₀ ≤ (N : ℝ) / (Fintype.card (OddRole n) : ℝ) :=
    (le_div_iff₀ hcardPos).2 hNbase
  have hRatioPos : 0 < (N : ℝ) / (Fintype.card (OddRole n) : ℝ) :=
    lt_of_lt_of_le (by dsimp [C₀]; positivity) hNratio
  have hThresholdEq : (4 : ℝ) * 4 * (K + 1) = (2 * C₀) * (1e-8 : ℝ) := by
    dsimp [C₀]
    norm_num
    ring
  have havgEq (ω : (Γ.Key → M.ι) × (Γ.Cell → Fin N)) (y : Fin N) :
      (Fintype.card (OddRole n) : ℝ)⁻¹ * ∑ u, Z u y ω =
        ((N : ℝ) / (Fintype.card (OddRole n) : ℝ)) *
          oddColumn Γ M ω.1 ω.2 y := by
    dsimp [Z, oddColumn]
    rw [← Finset.mul_sum]
    ring
  have hbadSubset (ω : (Γ.Key → M.ι) × (Γ.Cell → Fin N))
      (hbad : ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) :
      ∃ y, 4 * 4 * (K + 1) <
        (Fintype.card (OddRole n) : ℝ)⁻¹ * ∑ u, Z u y ω := by
    obtain ⟨y, hy⟩ := hbad
    refine ⟨y, ?_⟩
    rw [havgEq]
    calc
      4 * 4 * (K + 1) = (2 * C₀) * (1e-8 : ℝ) := hThresholdEq
      _ ≤ ((N : ℝ) / (Fintype.card (OddRole n) : ℝ)) * (1e-8 : ℝ) :=
        mul_le_mul_of_nonneg_right hNratio (by positivity)
      _ < ((N : ℝ) / (Fintype.card (OddRole n) : ℝ)) * oddColumn Γ M ω.1 ω.2 y :=
        mul_lt_mul_of_pos_left hy hRatioPos
  have hsum := hsc
  have hpr :
      (∑ ω, if ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y then R.w ω else 0) ≤
        (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
    calc
      (∑ ω, if ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y then R.w ω else 0) ≤
          ∑ ω, if ∃ y, 4 * 4 * (K + 1) <
              (Fintype.card (OddRole n) : ℝ)⁻¹ * ∑ u, Z u y ω then R.w ω else 0 := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hb : ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y
        · have hu := hbadSubset ω hb
          rw [if_pos hb, if_pos hu]
        · rw [if_neg hb]
          split_ifs <;> simp [R.nonneg ω]
      _ ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
        simpa using hsum
  change R.pr (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤ _
  simpa [FinProb.pr, R] using hpr

/-- Steps 2–4 assembled: at tags avoiding every `B_g` the cell events satisfy the local-lemma input, and under
the two-stage law the odd column sums exceed `θ₀` with probability at most `n 2^n 4^{-n}`. -/
theorem anchor_stage (D₀ d p K : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hp : 0 < p) (hK : 0 ≤ K) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (P : Profiles7 Γ M K),
        GeomFacts Γ → FilterFacts Γ M → TagLLL Γ M P.Q D₀ →
        (∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ) ∧
          (FinProb.bind (tagLaw Γ M P.Q D₀) (anchorLaw Γ M)).pr
              (fun ω => ∃ y, (1e-8 : ℝ) < oddColumn Γ M ω.1 ω.2 y) ≤
            (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨n₁, hA⟩ := anchor_lll D₀ d p hD₀ hd hd' hp
  obtain ⟨n₂, hmom⟩ := odd_moment D₀ d hD₀ hd hd'
  obtain ⟨n₃, C₃, hodd⟩ := odd_loads D₀ d K hd hd8 hK
  refine ⟨max (max n₁ n₂) (max n₃ 1), C₃, ?_⟩
  intro n N hL E G X Y κ Γ M P hG hF hT
  have hn₁ : n₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL.1
  have hn₂ : n₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL.1
  have hn₃ : n₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL.1
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL.1
  have hAll : ∀ σ, (∀ g, ¬ TagBad Γ M D₀ σ g) → AnchorLLL Γ M D₀ σ := fun σ hσ =>
    hA n hn₁ Γ M σ hG (cell_invalid_prob Γ M hn1 hG.loc σ)
      (alarm_prob Γ M (alarm_mean Γ M hF.starRef_update) (alarm_reps Γ hG.loc M) σ) hσ
  refine ⟨hAll, ?_⟩
  exact hodd n N ⟨hn₃, hL.2.1, hL.2.2⟩ Γ M P hG hF.row_cap
    (hmom n hn₂ Γ M P.Q cond_product_bound hG hT hAll)

end HypercubeRamsey.S07
