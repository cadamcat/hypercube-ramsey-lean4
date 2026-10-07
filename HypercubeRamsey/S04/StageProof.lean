import HypercubeRamsey.S04.Defs
import HypercubeRamsey.S03.Stabilization
import HypercubeRamsey.S03.Mixtures

namespace HypercubeRamsey

open Filter
open scoped BigOperators

/-- The stage argument, with the two frozen Section 4 substatements passed explicitly. -/
theorem l41_stage_proof (β γ : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (plateau : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N (E : Fin N → Fin N → Prop)
      (A B : Finset (Fin N)) (q : Law N × Law N),
      PBias (pw β) (pw γ) (h4 β γ) n N E q.1 q.2 →
      q.1.SupportedIn A → q.2.SupportedIn B →
      ∃ G : Colour, ∃ μ ν : Law N,
        PrepLaw β γ G n N E μ ν ∧ μ.SupportedIn A ∧ ν.SupportedIn B)
    (core : ∀ (K : ℝ) (hK : 0 < K), ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n ≥ n₀, ∀ N,
      LargeHost C₀ n N → ∀ (E : Fin N → Fin N → Prop) (G : Colour)
      (X' Y' : Finset (Fin N)) {ι : Type} [Fintype ι]
      (ρ : FinProb ι) (μ ν : ι → Law N),
      (∀ i, PrepLaw β γ G n N E (μ i) (ν i)) →
      (∀ i, (μ i).SupportedIn X' ∧ (ν i).SupportedIn Y') →
      (∀ x, ∑ i, ρ.w i * (μ i).w x ≤ K / N) →
      (∀ y, ∑ i, ρ.w i * (ν i).w y ≤ K / N) →
      (∀ μ' ν' : Law N,
        μ'.WidthLE (2 * (n : ℝ) ^ β) → ν'.WidthLE (2 * (n : ℝ) ^ γ) →
        dens E G μ' ν' ≤ Real.exp (-(n : ℝ) ^ h4 β γ) →
        ¬ (μ'.SupportedIn X' ∧ ν'.SupportedIn Y')) →
      Nonempty ((OAI.HypercubeRamsey.cube n).Copy
        (OAI.HypercubeRamsey.crossGraph (Hits E G)))) :
    ∃ h > (0 : ℝ), ∀ h' : ℝ, 0 < h' → h' ≤ h → ∀ T : Stage,
      Available T (PBias (pw β) (pw γ) h').toPatch →
      EventuallyAbsent T (PPure β γ h').toPatch → False := by
  have hω : 0 < omega4 β γ := by
    apply div_pos
    · exact lt_min hβ (by linarith)
    · positivity
  have hh : 0 < h4 β γ := by
    unfold h4
    exact div_pos hω (by positivity)
  refine ⟨h4 β γ, hh, ?_⟩
  intro h' hh' h'h T hav hAbs
  obtain ⟨nPlateau, hPlateau⟩ := plateau
  let nMin := max nPlateau 2
  have hnMin : nPlateau ≤ nMin := Nat.le_max_left _ _
  have hnMin2 : 2 ≤ nMin := Nat.le_max_right _ _
  have htail : ∀ᶠ k in atTop, nMin ≤ T.S.n k :=
    T.S.n_tendsto.eventually (Filter.eventually_atTop.2 ⟨nMin, fun _ hk => hk⟩)
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 htail
  let φ : ℕ → ℕ := fun k => k₀ + k
  have hφ : StrictMono φ := by
    intro a b hab
    dsimp [φ]
    omega
  let T₀ := T.sub φ hφ
  have hRef₀ : T₀.Refines T := Stage.Refines.sub T φ hφ
  have hav₀ := Available.refine hav hRef₀
  have hAbs₀ := EventuallyAbsent.refine hAbs hRef₀
  have hlarge₀ : ∀ k, nMin ≤ T₀.S.n k := by
    intro k
    dsimp [T₀, Stage.sub, φ]
    exact hk₀ (k₀ + k) (Nat.le_add_right _ _)

  let colorOf : Fin 2 → Colour := fun i => decide (i.val = 1)
  let Q : Fin 2 → LawProp := fun i n N E =>
    {q | PrepLaw β γ (colorOf i) n N E q.1 q.2}
  let P : Fin 2 → PatchProp := fun i n N E =>
    if n < nMin then (PBias (pw β) (pw γ) h').toPatch n N E
    else (Q i).toPatchProp n N E
  have hmono : ∀ n N E, (PBias (pw β) (pw γ) h').toPatch n N E ⊆
      PatchProp.union P n N E := by
    intro n N E AB hAB
    by_cases hnsmall : n < nMin
    · refine ⟨⟨0, by decide⟩, ?_⟩
      simpa [P, hnsmall] using hAB
    · have hn : nPlateau ≤ n := le_trans hnMin (Nat.le_of_not_gt hnsmall)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (by decide : 1 ≤ 2)
          (le_trans hnMin2 (Nat.le_of_not_gt hnsmall)))
      rcases hAB with ⟨μ, ν, hμAB, hνAB, hbias⟩
      have hpow : (n : ℝ) ^ (-h4 β γ) ≤ (n : ℝ) ^ (-h') :=
        Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg h'h)
      have hbias4 : PBias (pw β) (pw γ) (h4 β γ) n N E μ ν := by
        refine ⟨hbias.1, hbias.2.1, ?_⟩
        exact hpow.trans hbias.2.2
      obtain ⟨G, μ', ν', hprep, hμ', hν'⟩ :=
        hPlateau n hn N E AB.1 AB.2 (μ, ν) hbias4 hμAB hνAB
      let j : Fin 2 := if G then ⟨1, by decide⟩ else ⟨0, by decide⟩
      have hj : colorOf j = G := by
        cases G <;> simp [colorOf, j]
      refine ⟨j, ?_⟩
      simp only [P, if_neg hnsmall]
      change ∃ q ∈ Q j n N E, q.1.SupportedIn AB.1 ∧ q.2.SupportedIn AB.2
      refine ⟨(μ', ν'), ?_, hμ', hν'⟩
      simpa [Q, hj] using hprep
  have havUnion := Available.mono hmono hav₀
  obtain ⟨T₁, hRef₁, i, havI⟩ := Available.union_fin havUnion
  have hAbs₁ := EventuallyAbsent.refine hAbs₀ hRef₁

  have htail₁ : ∀ᶠ k in atTop, nMin ≤ T₁.S.n k :=
    T₁.S.n_tendsto.eventually (Filter.eventually_atTop.2 ⟨nMin, fun _ hk => hk⟩)
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.1 htail₁
  let ψ : ℕ → ℕ := fun k => k₁ + k
  have hψ : StrictMono ψ := by
    intro a b hab
    dsimp [ψ]
    omega
  let T₂ := T₁.sub ψ hψ
  have hRef₂ : T₂.Refines T₁ := Stage.Refines.sub T₁ ψ hψ
  have havI₂ := Available.refine havI hRef₂
  have hAbs₂ := EventuallyAbsent.refine hAbs₁ hRef₂
  have hlarge₂ : ∀ k, nMin ≤ T₂.S.n k := by
    intro k
    dsimp [T₂, Stage.sub, ψ]
    exact hk₁ (k₁ + k) (Nat.le_add_right _ _)
  have havQ : Available T₂ (Q i).toPatchProp := by
    rcases havI₂ with ⟨κ, hκ, hav⟩
    refine ⟨κ, hκ, ?_⟩
    filter_upwards [hav] with k hk RX RY hRX hRY
    have hn : ¬ T₂.S.n k < nMin := Nat.not_lt_of_ge (hlarge₂ k)
    obtain ⟨A, B, hmem, hA, hB⟩ := hk RX RY hRX hRY
    refine ⟨A, B, ?_, hA, hB⟩
    simpa [P, hn] using hmem

  obtain ⟨κ, hκ, hmenu⟩ := Available.menu havQ
  let K : ℝ := 4 / κ
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (by norm_num) hκ
  obtain ⟨nCore, C₀, hCore⟩ := core K hK

  have hmenu' := hmenu
  have habs' : ∀ᶠ k in atTop, ∀ A B,
      (A, B) ∈ (PPure β γ h').toPatch (T₂.S.n k) (T₂.S.N k) (T₂.S.E k) →
      ¬ (A ⊆ T₂.X k ∧ B ⊆ T₂.Y k) := hAbs₂
  have hlarge : ∀ᶠ k in atTop,
      nCore ≤ T₂.S.n k ∧ LargeHost C₀ (T₂.S.n k) (T₂.S.N k) :=
    BadSeq.eventually_large T₂.S C₀ nCore
  have hnlarge : ∀ᶠ k in atTop, 2 ≤ T₂.S.n k :=
    T₂.S.n_tendsto.eventually (Filter.eventually_atTop.2 ⟨2, fun _ hk => hk⟩)
  obtain ⟨k, hk⟩ := ((hmenu'.and habs').and (hlarge.and hnlarge)).exists
  rcases hk with ⟨⟨⟨w, hw⟩, habsk⟩, ⟨⟨hcoreN, hhost⟩, hn2⟩⟩

  let N := T₂.S.N k
  let E := T₂.S.E k
  let X := T₂.X k
  let Y := T₂.Y k
  let ι := {R : Finset (Fin N) × Finset (Fin N) //
    (R.1.card : ℝ) ≤ κ * N ∧ (R.2.card : ℝ) ≤ κ * N}
  letI : Fintype ι := Fintype.ofFinite ι
  let μ : ι → Law N := fun j => (w j.val).1
  let ν : ι → Law N := fun j => (w j.val).2
  have hmenuAvail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N →
      (RY.card : ℝ) ≤ κ * N → ∃ j : ι,
        (∀ x ∈ RX, (μ j).w x = 0) ∧ (∀ y ∈ RY, (ν j).w y = 0) := by
    intro RX RY hRX hRY
    let j : ι := ⟨(RX, RY), ⟨hRX, hRY⟩⟩
    refine ⟨j, ?_, ?_⟩
    · intro x hx
      have hsup := (hw RX RY hRX hRY).2.1
      have hzero : (w (RX, RY)).1.w x = 0 := by
        apply hsup x
        simp only [Finset.mem_sdiff]
        intro hx'
        exact hx'.2 hx
      simpa [μ, j] using hzero
    · intro y hy
      have hsup := (hw RX RY hRX hRY).2.2
      have hzero : (w (RX, RY)).2.w y = 0 := by
        apply hsup y
        simp only [Finset.mem_sdiff]
        intro hy'
        exact hy'.2 hy
      simpa [ν, j] using hzero
  have hNpos : 0 < N := T₂.S.N_pos k
  obtain ⟨t, ht0, ht1, htX, htY⟩ :=
    balanced_mixture hNpos μ ν κ hκ hmenuAvail
  let ρ : FinProb ι := ⟨t, ht0, ht1⟩
  have hprep : ∀ j, PrepLaw β γ (colorOf i) (T₂.S.n k) N E (μ j) (ν j) := by
    intro j
    have hj := hw j.val.1 j.val.2 j.property.1 j.property.2
    simpa [Q, μ, ν, N, E] using hj.1
  have hsupp : ∀ j, (μ j).SupportedIn X ∧ (ν j).SupportedIn Y := by
    intro j
    have hj := hw j.val.1 j.val.2 j.property.1 j.property.2
    constructor
    · intro x hx
      apply hj.2.1 x
      intro hmem
      exact hx (Finset.mem_sdiff.mp hmem).1
    · intro y hy
      apply hj.2.2 y
      intro hmem
      exact hy (Finset.mem_sdiff.mp hmem).1
  have hden : (4 : ℝ) / (κ * (N : ℝ)) = K / (N : ℝ) := by
    dsimp [K]
    field_simp
    <;> ring
  have hmassX : ∀ x, ∑ j, ρ.w j * (μ j).w x ≤ K / N := by
    intro x
    rw [← hden]
    simpa [ρ, μ] using htX x
  have hmassY : ∀ y, ∑ j, ρ.w j * (ν j).w y ≤ K / N := by
    intro y
    rw [← hden]
    simpa [ρ, ν] using htY y
  have hexcl : ∀ μ' ν' : Law N,
      μ'.WidthLE (2 * (T₂.S.n k : ℝ) ^ β) →
      ν'.WidthLE (2 * (T₂.S.n k : ℝ) ^ γ) →
      dens E (colorOf i) μ' ν' ≤ Real.exp (-((T₂.S.n k : ℝ) ^ h4 β γ)) →
      ¬ (μ'.SupportedIn X ∧ ν'.SupportedIn Y) := by
    intro μ' ν' hwX hwY hdensity hsupp'
    have hn1 : (1 : ℝ) ≤ (T₂.S.n k : ℝ) := by
      exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2) hn2)
    have hpow : (T₂.S.n k : ℝ) ^ h' ≤ (T₂.S.n k : ℝ) ^ h4 β γ :=
      Real.rpow_le_rpow_of_exponent_le hn1 h'h
    have hexp : Real.exp (-((T₂.S.n k : ℝ) ^ h4 β γ)) ≤
        Real.exp (-((T₂.S.n k : ℝ) ^ h')) :=
      Real.exp_le_exp.mpr (neg_le_neg hpow)
    have hpure : PPure β γ h' (T₂.S.n k) N E μ' ν' := by
      refine ⟨hwX, hwY, ?_⟩
      refine ⟨!(colorOf i), ?_⟩
      simpa using le_trans hdensity hexp
    have hmem : (X, Y) ∈ (PPure β γ h').toPatch (T₂.S.n k) N E :=
      ⟨μ', ν', hsupp'.1, hsupp'.2, hpure⟩
    exact habsk X Y hmem ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
  have hcube := hCore (T₂.S.n k) hcoreN N hhost E (colorOf i) X Y
    ρ μ ν hprep hsupp hmassX hmassY hexcl
  exact T₂.S.no_cube k (colorOf i) hcube

end HypercubeRamsey
