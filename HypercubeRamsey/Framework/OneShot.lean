import HypercubeRamsey.Framework.Disc
import HypercubeRamsey.Framework.Hall
import HypercubeRamsey.S03.Stabilization

/-!
# Single-dimension statements and their bridge to stages

Conventions: every embedding lemma is stated at one
dimension `(n, N, E, X, Y)` in the large regime `LargeAt`, concluding `CubeAt`; `OneShot` lemmas turn such
statements into non-availability along a stage. One stabilization covers a fixed countable family of properties.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey Filter

/-- Discrepancy at one dimension: every pair of laws supported in `X`, `Y` within the width budgets has both
colour densities within `err` of `1/2`. -/
def DiscOne {N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (wX wY err : ℝ) : Prop :=
  ∀ μ ν : Law N, μ.SupportedIn X → ν.SupportedIn Y → μ.WidthLE wX → ν.WidthLE wY →
    ∀ c : Colour, |dens E c μ ν - 1 / 2| ≤ err

theorem discAt_iff_eventually_discOne (T : Stage) (wX wY err : ℝ → ℝ) :
    DiscAt T wX wY err ↔ ∀ᶠ k in atTop, DiscOne (T.S.E k) (T.X k) (T.Y k)
      (wX (T.S.n k)) (wY (T.S.n k)) (err (T.S.n k)) := by
  constructor
  · intro h
    filter_upwards [h] with k hk
    intro μ ν hμ hν hwX hwY c
    exact hk c μ ν hμ hν hwX hwY
  · intro h
    filter_upwards [h] with k hk
    intro c μ ν hμ hν hwX hwY
    exact hk μ ν hμ hν hwX hwY c

/-- Availability at a single dimension with tolerance `κ`. -/
def AvailableAt (κ : ℝ) (P : PatchProp) (n N : ℕ) (E : Fin N → Fin N → Prop)
    (X Y : Finset (Fin N)) : Prop :=
  ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N → (RY.card : ℝ) ≤ κ * N →
    ∃ A B, (A, B) ∈ P n N E ∧ A ⊆ X \ RX ∧ B ⊆ Y \ RY

theorem available_iff_availableAt (T : Stage) (P : PatchProp) :
    Available T P ↔ ∃ κ > (0 : ℝ), ∀ᶠ k in atTop,
      AvailableAt κ P (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := Iff.rfl

/-- A monochromatic cube at one dimension, in either colour. -/
def CubeAt (n N : ℕ) (E : Fin N → Fin N → Prop) : Prop :=
  ∃ c : Colour, Nonempty ((cube n).Copy (crossGraph (Hits E c)))

/-- The large regime of a one-shot statement. -/
def LargeAt (n₀ : ℕ) (C₀ : ℝ) (n N : ℕ) : Prop :=
  n₀ ≤ n ∧ C₀ * 2 ^ n ≤ (N : ℝ) ∧ N ≤ n * 2 ^ n

/-- A finite tag mixture of patch laws. -/
structure TagMix (N : ℕ) where
  ι : Type
  [fin : Fintype ι]
  Λ : ι → ℝ
  Λ_nonneg : ∀ i, 0 ≤ Λ i
  Λ_sum : ∑ i, Λ i = 1
  μ : ι → Law N
  ν : ι → Law N

attribute [instance] TagMix.fin

/-- Balance: both pointwise tag averages are at most `K / N`. -/
def TagMix.Balanced {N : ℕ} (M : TagMix N) (K : ℝ) : Prop :=
  (∀ x, (N : ℝ) * ∑ i, M.Λ i * (M.μ i).w x ≤ K) ∧ (∀ y, (N : ℝ) * ∑ i, M.Λ i * (M.ν i).w y ≤ K)

/-- Stabilization on a set of patch properties. -/
def StabilizedOn (T : Stage) (F : Set PatchProp) : Prop :=
  ∀ P ∈ F, Available T P ∨ EventuallyAbsent T P

/-- Pair-law property: a support pair carries a witness when two laws supported in it satisfy `Q`. -/
def PairProp := ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Law N → Law N → Prop

def PairProp.toPatch (Q : PairProp) : PatchProp :=
  fun n N E => {AB | ∃ μ ν : Law N, μ.SupportedIn AB.1 ∧ ν.SupportedIn AB.2 ∧ Q n N E μ ν}

/-- A patch property read in the reversed orientation. -/
def PatchProp.swap (P : PatchProp) : PatchProp :=
  fun n N E => {AB | (AB.2, AB.1) ∈ P n N (transposeRel E)}

/-- Power and linear width budgets. -/
noncomputable def pw (x : ℝ) : ℝ → ℝ := fun n => n ^ x
def lw (α : ℝ) : ℝ → ℝ := fun n => α * n

private theorem badSeq_eventually_large_direct (S : BadSeq) (C₀ : ℝ) (n₀ : ℕ) :
    ∀ᶠ k in atTop, n₀ ≤ S.n k ∧ LargeHost C₀ (S.n k) (S.N k) := by
  have hn : ∀ᶠ k in atTop, n₀ ≤ S.n k :=
    S.n_tendsto.eventually (eventually_ge_atTop n₀)
  have hratio : ∀ᶠ k in atTop, C₀ ≤ (S.N k : ℝ) / (2 : ℝ) ^ S.n k :=
    S.ratio_tendsto.eventually (eventually_ge_atTop C₀)
  filter_upwards [hn, hratio] with k hn hk
  refine ⟨hn, ?_⟩
  constructor
  · have hpow : 0 < (2 : ℝ) ^ S.n k := pow_pos (by norm_num) _
    exact (le_div_iff₀ hpow).mp hk
  · exact S.N_le k

/-- F-OneShot: a single-dimension embedding statement whose side conditions hold eventually along the stage
excludes availability. -/
theorem not_available_of_oneShot {T : Stage} {P : PatchProp} {κ : ℝ} (hκ : 0 < κ)
    (side : ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Finset (Fin N) → Finset (Fin N) → Prop)
    (hside : ∀ᶠ k in atTop, side (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k))
    (n₀ : ℕ) (C₀ : ℝ)
    (hshot : ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)), LargeAt n₀ C₀ n N →
      side n N E X Y → AvailableAt κ P n N E X Y → CubeAt n N E) :
    ¬ (∀ᶠ k in atTop, AvailableAt κ P (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k)) := by
  intro havail
  have hlarge := badSeq_eventually_large_direct T.S C₀ n₀
  have hfalse : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hside, havail, hlarge] with k hsidek havailk hlargek
    obtain ⟨hn₀, hhost⟩ := hlargek
    obtain ⟨c, hcopy⟩ := hshot (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k)
      ⟨hn₀, hhost.1, hhost.2⟩ hsidek havailk
    exact T.S.no_cube k c hcopy
  obtain ⟨k, hk⟩ := hfalse.exists
  exact hk.elim

/-- F-OneShot, packaged for `Available`: the one-shot statement holds for every tolerance. -/
theorem not_available_of_oneShot' {T : Stage} {P : PatchProp}
    (side : ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Finset (Fin N) → Finset (Fin N) → Prop)
    (hside : ∀ᶠ k in atTop, side (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k))
    (hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N → side n N E X Y → AvailableAt κ P n N E X Y → CubeAt n N E) :
    ¬ Available T P := by
  intro havail
  obtain ⟨κ, hκ, havailκ⟩ := (available_iff_availableAt T P).mp havail
  obtain ⟨n₀, C₀, hshotκ⟩ := hshot κ hκ
  exact (not_available_of_oneShot hκ side hside n₀ C₀ hshotκ) havailκ

/-- F-UnionAvail. -/
theorem AvailableAt.union {κ : ℝ} {P Q : PatchProp} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)}
    (h : AvailableAt κ (fun n N E => P n N E ∪ Q n N E) n N E X Y) :
    AvailableAt (κ / 2) P n N E X Y ∨ AvailableAt (κ / 2) Q n N E X Y := by
  classical
  by_cases hP : AvailableAt (κ / 2) P n N E X Y
  · exact Or.inl hP
  by_cases hQ : AvailableAt (κ / 2) Q n N E X Y
  · exact Or.inr hQ
  have badP : ∃ RX RY, (RX.card : ℝ) ≤ (κ / 2) * N ∧ (RY.card : ℝ) ≤ (κ / 2) * N ∧
      ∀ A B, (A, B) ∈ P n N E → A ⊆ X \ RX → ¬ B ⊆ Y \ RY := by
    change ¬ (∀ RX RY, (RX.card : ℝ) ≤ (κ / 2) * N → (RY.card : ℝ) ≤ (κ / 2) * N →
      ∃ A B, (A, B) ∈ P n N E ∧ A ⊆ X \ RX ∧ B ⊆ Y \ RY) at hP
    push_neg at hP
    exact hP
  have badQ : ∃ RX RY, (RX.card : ℝ) ≤ (κ / 2) * N ∧ (RY.card : ℝ) ≤ (κ / 2) * N ∧
      ∀ A B, (A, B) ∈ Q n N E → A ⊆ X \ RX → ¬ B ⊆ Y \ RY := by
    change ¬ (∀ RX RY, (RX.card : ℝ) ≤ (κ / 2) * N → (RY.card : ℝ) ≤ (κ / 2) * N →
      ∃ A B, (A, B) ∈ Q n N E ∧ A ⊆ X \ RX ∧ B ⊆ Y \ RY) at hQ
    push_neg at hQ
    exact hQ
  obtain ⟨RX₁, RY₁, hRX₁, hRY₁, hbadP⟩ := badP
  obtain ⟨RX₂, RY₂, hRX₂, hRY₂, hbadQ⟩ := badQ
  let RX := RX₁ ∪ RX₂
  let RY := RY₁ ∪ RY₂
  have hRX : (RX.card : ℝ) ≤ κ * N := by
    dsimp [RX]
    calc
      ((RX₁ ∪ RX₂).card : ℝ) ≤ RX₁.card + RX₂.card := by
        exact_mod_cast Finset.card_union_le RX₁ RX₂
      _ ≤ (κ / 2) * N + (κ / 2) * N := add_le_add hRX₁ hRX₂
      _ = κ * N := by ring
  have hRY : (RY.card : ℝ) ≤ κ * N := by
    dsimp [RY]
    calc
      ((RY₁ ∪ RY₂).card : ℝ) ≤ RY₁.card + RY₂.card := by
        exact_mod_cast Finset.card_union_le RY₁ RY₂
      _ ≤ (κ / 2) * N + (κ / 2) * N := add_le_add hRY₁ hRY₂
      _ = κ * N := by ring
  obtain ⟨A, B, hAB, hA, hB⟩ := h RX RY hRX hRY
  change ((A, B) ∈ P n N E) ∨ ((A, B) ∈ Q n N E) at hAB
  rcases hAB with hAB | hAB
  · exfalso
    have hA₁ : A ⊆ X \ RX₁ := by
      intro x hx
      have hx' := Finset.mem_sdiff.mp (hA hx)
      exact Finset.mem_sdiff.mpr ⟨hx'.1, fun hx₁ => hx'.2 (Finset.mem_union.mpr (Or.inl hx₁))⟩
    have hB₁ : B ⊆ Y \ RY₁ := by
      intro y hy
      have hy' := Finset.mem_sdiff.mp (hB hy)
      exact Finset.mem_sdiff.mpr ⟨hy'.1, fun hy₁ => hy'.2 (Finset.mem_union.mpr (Or.inl hy₁))⟩
    exact (hbadP A B hAB hA₁) hB₁
  · exfalso
    have hA₂ : A ⊆ X \ RX₂ := by
      intro x hx
      have hx' := Finset.mem_sdiff.mp (hA hx)
      exact Finset.mem_sdiff.mpr ⟨hx'.1, fun hx₂ => hx'.2 (Finset.mem_union.mpr (Or.inr hx₂))⟩
    have hB₂ : B ⊆ Y \ RY₂ := by
      intro y hy
      have hy' := Finset.mem_sdiff.mp (hB hy)
      exact Finset.mem_sdiff.mpr ⟨hy'.1, fun hy₂ => hy'.2 (Finset.mem_union.mpr (Or.inr hy₂))⟩
    exact (hbadQ A B hAB hA₂) hB₂

/-- F-AvailMono. -/
theorem AvailableAt.mono {κ : ℝ} {P Q : PatchProp} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (hPQ : P n N E ⊆ Q n N E) (h : AvailableAt κ P n N E X Y) :
    AvailableAt κ Q n N E X Y := by
  intro RX RY hRX hRY
  obtain ⟨A, B, hAB, hA, hB⟩ := h RX RY hRX hRY
  exact ⟨A, B, hPQ hAB, hA, hB⟩

theorem Available.mono {T : Stage} {P Q : PatchProp} (hPQ : ∀ n N E, P n N E ⊆ Q n N E)
    (h : Available T P) : Available T Q := by
  obtain ⟨κ, hκ, hk⟩ := (available_iff_availableAt T P).mp h
  apply (available_iff_availableAt T Q).mpr
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hk] with k hk
  exact AvailableAt.mono (hPQ _ _ _) hk

private theorem availableAt_swap_iff {κ : ℝ} {P : PatchProp} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} :
    AvailableAt κ P.swap n N E X Y ↔ AvailableAt κ P n N (transposeRel E) Y X := by
  constructor
  · intro h RX RY hRX hRY
    obtain ⟨A, B, hAB, hA, hB⟩ := h RY RX hRY hRX
    exact ⟨B, A, hAB, hB, hA⟩
  · intro h RX RY hRX hRY
    obtain ⟨A, B, hAB, hA, hB⟩ := h RY RX hRY hRX
    exact ⟨B, A, hAB, hB, hA⟩

/-- F-SwapAvail. -/
theorem available_swap_iff (T : Stage) (P : PatchProp) :
    Available T P.swap ↔ Available T.swap P := by
  rw [available_iff_availableAt, available_iff_availableAt]
  change
    (∃ κ > (0 : ℝ), ∀ᶠ k in atTop,
      AvailableAt κ P.swap (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k)) ↔
    (∃ κ > (0 : ℝ), ∀ᶠ k in atTop,
      AvailableAt κ P (T.S.n k) (T.S.N k) (transposeRel (T.S.E k)) (T.Y k) (T.X k))
  constructor
  · rintro ⟨κ, hκ, hk⟩
    refine ⟨κ, hκ, ?_⟩
    filter_upwards [hk] with k hk
    exact availableAt_swap_iff.mp hk
  · rintro ⟨κ, hκ, hk⟩
    refine ⟨κ, hκ, ?_⟩
    filter_upwards [hk] with k hk
    exact availableAt_swap_iff.mpr hk

private theorem absentAt_swap_iff {P : PatchProp} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} :
    (∀ A B, (A, B) ∈ P.swap n N E → ¬ (A ⊆ X ∧ B ⊆ Y)) ↔
    (∀ A B, (A, B) ∈ P n N (transposeRel E) → ¬ (A ⊆ Y ∧ B ⊆ X)) := by
  constructor
  · intro h A B hAB hsub
    exact h B A hAB ⟨hsub.2, hsub.1⟩
  · intro h A B hAB hsub
    exact h B A hAB ⟨hsub.2, hsub.1⟩

theorem eventuallyAbsent_swap_iff (T : Stage) (P : PatchProp) :
    EventuallyAbsent T P.swap ↔ EventuallyAbsent T.swap P := by
  change
    (∀ᶠ k in atTop, ∀ A B, (A, B) ∈ P.swap (T.S.n k) (T.S.N k) (T.S.E k) →
      ¬ (A ⊆ T.X k ∧ B ⊆ T.Y k)) ↔
    (∀ᶠ k in atTop, ∀ A B, (A, B) ∈ P (T.S.n k) (T.S.N k) (transposeRel (T.S.E k)) →
      ¬ (A ⊆ T.Y k ∧ B ⊆ T.X k))
  constructor
  · intro h
    filter_upwards [h] with k hk
    exact absentAt_swap_iff.mp hk
  · intro h
    filter_upwards [h] with k hk
    exact absentAt_swap_iff.mpr hk

/-- F-SwapStab. -/
theorem StabilizedOn.swap {T : Stage} {F : Set PatchProp} (h : StabilizedOn T F)
    (hF : ∀ P ∈ F, P.swap ∈ F) : StabilizedOn T.swap F := by
  intro P hP
  obtain hAvail | hAbsent := h (P.swap) (hF P hP)
  · exact Or.inl ((available_swap_iff T P).mp hAvail)
  · exact Or.inr ((eventuallyAbsent_swap_iff T P).mp hAbsent)

private theorem available_refine_direct {T T' : Stage} {P : PatchProp}
    (h : Available T P) (hr : T'.Refines T) : Available T' P := by
  revert h
  induction hr with
  | refl T =>
      intro h
      exact h
  | sub T φ hφ =>
      intro h
      obtain ⟨κ, hκ, hk⟩ := (available_iff_availableAt T P).mp h
      apply (available_iff_availableAt (T.sub φ hφ) P).mpr
      refine ⟨κ, hκ, ?_⟩
      have hkφ := hφ.tendsto_atTop.eventually hk
      filter_upwards [hkφ] with k hk
      simpa [Stage.sub, BadSeq.comp] using hk
  | remove T X' Y' hX hY hsmall =>
      intro h
      obtain ⟨κ, hκ, hk⟩ := (available_iff_availableAt T P).mp h
      have hκ2 : 0 < κ / 2 := by linarith
      have hcomp : ∀ᶠ k in atTop,
          ((X' k)ᶜ.card : ℝ) ≤ (κ / 2) * T.S.N k ∧
          ((Y' k)ᶜ.card : ℝ) ≤ (κ / 2) * T.S.N k := by
        have hsmallk := hsmall.eventually (isOpen_Iio.mem_nhds hκ2)
        filter_upwards [hsmallk, Filter.Eventually.of_forall (fun k => T.S.N_pos k)] with k hsmallk hNk
        have hratio :
            (((X' k)ᶜ.card : ℝ) + ((Y' k)ᶜ.card : ℝ)) / (T.S.N k : ℝ) < κ / 2 := by
          simpa only [Nat.cast_add] using hsmallk
        have htotal :
            ((X' k)ᶜ.card : ℝ) + ((Y' k)ᶜ.card : ℝ) < (κ / 2) * T.S.N k := by
          exact (div_lt_iff₀ (Nat.cast_pos.mpr hNk)).mp hratio
        constructor
        · have hnonneg : 0 ≤ ((Y' k)ᶜ.card : ℝ) := Nat.cast_nonneg _
          linarith
        · have hnonneg : 0 ≤ ((X' k)ᶜ.card : ℝ) := Nat.cast_nonneg _
          linarith
      apply (available_iff_availableAt ⟨T.S, X', Y', hsmall⟩ P).mpr
      refine ⟨κ / 2, hκ2, ?_⟩
      filter_upwards [hk, hcomp] with k hk hcomp
      intro RX RY hRX hRY
      let UX := T.X k \ X' k
      let UY := T.Y k \ Y' k
      have hUX : (UX.card : ℝ) ≤ (κ / 2) * T.S.N k := by
        have hsub : UX ⊆ (X' k)ᶜ := by
          intro x hx
          exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
        calc
          (UX.card : ℝ) ≤ ((X' k)ᶜ.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ (κ / 2) * T.S.N k := hcomp.1
      have hUY : (UY.card : ℝ) ≤ (κ / 2) * T.S.N k := by
        have hsub : UY ⊆ (Y' k)ᶜ := by
          intro y hy
          exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hy).2
        calc
          (UY.card : ℝ) ≤ ((Y' k)ᶜ.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ (κ / 2) * T.S.N k := hcomp.2
      have hRXold : ((RX ∪ UX).card : ℝ) ≤ κ * T.S.N k := by
        calc
          ((RX ∪ UX).card : ℝ) ≤ RX.card + UX.card := by
            exact_mod_cast Finset.card_union_le RX UX
          _ ≤ (κ / 2) * T.S.N k + (κ / 2) * T.S.N k := add_le_add hRX hUX
          _ = κ * T.S.N k := by ring
      have hRYold : ((RY ∪ UY).card : ℝ) ≤ κ * T.S.N k := by
        calc
          ((RY ∪ UY).card : ℝ) ≤ RY.card + UY.card := by
            exact_mod_cast Finset.card_union_le RY UY
          _ ≤ (κ / 2) * T.S.N k + (κ / 2) * T.S.N k := add_le_add hRY hUY
          _ = κ * T.S.N k := by ring
      obtain ⟨A, B, hAB, hA, hB⟩ := hk (RX ∪ UX) (RY ∪ UY) hRXold hRYold
      refine ⟨A, B, hAB, ?_, ?_⟩
      · intro x hx
        have hx' := Finset.mem_sdiff.mp (hA hx)
        have hxnotRX : x ∉ RX := fun hxRX => hx'.2 (Finset.mem_union.mpr (Or.inl hxRX))
        have hxnotUX : x ∉ UX := fun hxUX => hx'.2 (Finset.mem_union.mpr (Or.inr hxUX))
        have hxX' : x ∈ X' k := by
          by_contra hxnot
          exact hxnotUX (Finset.mem_sdiff.mpr ⟨hx'.1, hxnot⟩)
        exact Finset.mem_sdiff.mpr ⟨hxX', hxnotRX⟩
      · intro y hy
        have hy' := Finset.mem_sdiff.mp (hB hy)
        have hynotRY : y ∉ RY := fun hyRY => hy'.2 (Finset.mem_union.mpr (Or.inl hyRY))
        have hynotUY : y ∉ UY := fun hyUY => hy'.2 (Finset.mem_union.mpr (Or.inr hyUY))
        have hyY' : y ∈ Y' k := by
          by_contra hynot
          exact hynotUY (Finset.mem_sdiff.mpr ⟨hy'.1, hynot⟩)
        exact Finset.mem_sdiff.mpr ⟨hyY', hynotRY⟩
  | trans hAB hBC ihAB ihBC =>
      intro h
      exact ihAB (ihBC h)

private theorem absent_refine_direct {T T' : Stage} {P : PatchProp}
    (h : EventuallyAbsent T P) (hr : T'.Refines T) : EventuallyAbsent T' P := by
  revert h
  induction hr with
  | refl T =>
      intro h
      exact h
  | sub T φ hφ =>
      intro h
      change ∀ᶠ k in atTop, ∀ A B,
        (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) → ¬ (A ⊆ T.X k ∧ B ⊆ T.Y k) at h
      have hkφ := hφ.tendsto_atTop.eventually h
      change ∀ᶠ k in atTop, ∀ A B,
        (A, B) ∈ P ((T.sub φ hφ).S.n k) ((T.sub φ hφ).S.N k) ((T.sub φ hφ).S.E k) →
          ¬ (A ⊆ (T.sub φ hφ).X k ∧ B ⊆ (T.sub φ hφ).Y k)
      exact hkφ
  | remove T X' Y' hX hY hsmall =>
      intro h
      change ∀ᶠ k in atTop, ∀ A B,
        (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) → ¬ (A ⊆ T.X k ∧ B ⊆ T.Y k) at h
      change ∀ᶠ k in atTop, ∀ A B,
        (A, B) ∈ P (T.S.n k) (T.S.N k) (T.S.E k) → ¬ (A ⊆ X' k ∧ B ⊆ Y' k)
      filter_upwards [h] with k hk A B hAB hsub
      apply hk A B hAB
      constructor
      · intro x hx
        exact hX k (hsub.1 hx)
      · intro y hy
        exact hY k (hsub.2 hy)
  | trans hAB hBC ihAB ihBC =>
      intro h
      exact ihAB (ihBC h)

theorem StabilizedOn.refine {T T' : Stage} {F : Set PatchProp} (h : StabilizedOn T F)
    (hr : T'.Refines T) : StabilizedOn T' F := by
  intro P hP
  rcases h P hP with hAvail | hAbsent
  · exact Or.inl (available_refine_direct hAvail hr)
  · exact Or.inr (absent_refine_direct hAbsent hr)

theorem StabilizedOn.subset {T : Stage} {F G : Set PatchProp} (h : StabilizedOn T G) (hFG : F ⊆ G) :
    StabilizedOn T F := by
  intro P hP
  exact h P (hFG hP)

/-- Master stabilization for a countable family. -/
theorem exists_stabilizedOn (T : Stage) (F : Set PatchProp) (hF : F.Countable) :
    ∃ T', T'.Refines T ∧ StabilizedOn T' F := by
  classical
  let default : PatchProp := fun _ _ _ => ∅
  let P : ℕ → PatchProp := Set.enumerateCountable hF default
  obtain ⟨T', href, hstab⟩ := stabilization T P
  refine ⟨T', href, ?_⟩
  intro Q hQ
  obtain ⟨j, hj⟩ := Set.subset_range_enumerate hF default hQ
  simpa [P, hj] using hstab j

/-- F-DensCompl and degree forms. -/
theorem dens_false {N : ℕ} (E : Fin N → Fin N → Prop) (μ ν : Law N) :
    dens E false μ ν = 1 - dens E true μ ν := by
  classical
  have hsum : dens E true μ ν + dens E false μ ν = 1 := by
    unfold dens
    calc
      (∑ x, ∑ y, μ.w x * ν.w y * (if Hits E true x y then 1 else 0)) +
          (∑ x, ∑ y, μ.w x * ν.w y * (if Hits E false x y then 1 else 0))
          = ∑ x, (∑ y, μ.w x * ν.w y * (if Hits E true x y then 1 else 0) +
              ∑ y, μ.w x * ν.w y * (if Hits E false x y then 1 else 0)) := by
        rw [← Finset.sum_add_distrib]
      _ = ∑ x, ∑ y,
          (μ.w x * ν.w y * (if Hits E true x y then 1 else 0) +
            μ.w x * ν.w y * (if Hits E false x y then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Finset.sum_add_distrib]
      _ = ∑ x, ∑ y, μ.w x * ν.w y := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hE : E x y <;> simp [Hits, hE]
      _ = ∑ x, μ.w x * ∑ y, ν.w y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
      _ = 1 := by simp [μ.sum_eq_one, ν.sum_eq_one]
  linarith

theorem colDeg_transpose {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour) (μ : Law N) (x : Fin N) :
    colDeg (transposeRel E) c μ x = rowDeg E c x μ := by
  unfold colDeg rowDeg
  apply Finset.sum_congr rfl
  intro y hy
  rw [hits_transpose E c y x]

private theorem crossGraph_hits_swap_adj {N : ℕ} {E : Fin N → Fin N → Prop} {c : Colour}
    {u v : Fin N ⊕ Fin N}
    (h : (crossGraph (Hits (transposeRel E) c)).Adj u v) :
    (crossGraph (Hits E c)).Adj (Sum.swap u) (Sum.swap v) := by
  cases u with
  | inl x =>
      cases v with
      | inl y => simpa [crossGraph] using h
      | inr y =>
          change Hits E c y x
          change Hits (transposeRel E) c x y at h
          exact (hits_transpose E c x y).mp h
  | inr x =>
      cases v with
      | inl y =>
          change Hits E c x y
          change Hits (transposeRel E) c y x at h
          exact (hits_transpose E c y x).mp h
      | inr y => simpa [crossGraph] using h

/-- F-CubeSwap. -/
theorem CubeAt.of_transpose {n N : ℕ} {E : Fin N → Fin N → Prop} (h : CubeAt n N (transposeRel E)) :
    CubeAt n N E := by
  obtain ⟨c, hcopy⟩ := h
  refine ⟨c, ?_⟩
  rcases hcopy with ⟨copy⟩
  let f : CubeVertex n → Fin N ⊕ Fin N := fun v => Sum.swap (copy.toHom v)
  refine ⟨{
    toHom := {
      toFun := f
      map_rel' := ?_
    }
    injective' := ?_
  }⟩
  · intro u v huv
    exact crossGraph_hits_swap_adj (copy.toHom.map_rel huv)
  · intro u v huv
    apply copy.injective'
    simpa [f] using congrArg Sum.swap huv

/-- F-DiscMono at one dimension. -/
theorem DiscOne.mono {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {wX wY err wX' wY' err' : ℝ}
    (h : DiscOne E X Y wX wY err) (h₁ : wX' ≤ wX) (h₂ : wY' ≤ wY) (h₃ : err ≤ err') :
    DiscOne E X Y wX' wY' err' := by
  intro μ ν hμ hν hwX hwY c
  have hwXold : μ.WidthLE wX := fun x =>
    le_trans (hwX x) (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h₁) (by positivity))
  have hwYold : ν.WidthLE wY := fun y =>
    le_trans (hwY y) (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr h₂) (by positivity))
  exact le_trans (h μ ν hμ hν hwXold hwYold c) h₃

private theorem dens_transpose_direct {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (μ ν : Law N) : dens (transposeRel E) c μ ν = dens E c ν μ := by
  classical
  unfold dens
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  rw [hits_transpose]
  ring

/-- Swapping orientation at one dimension. -/
theorem DiscOne.transpose_iff {N : ℕ} (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (wX wY err : ℝ) :
    DiscOne (transposeRel E) Y X wY wX err ↔ DiscOne E X Y wX wY err := by
  constructor
  · intro h μ ν hμ hν hwX hwY c
    have h' := h ν μ hν hμ hwY hwX c
    rw [dens_transpose_direct E c ν μ] at h'
    exact h'
  · intro h μ ν hμ hν hwY hwX c
    have h' := h ν μ hν hμ hwX hwY c
    rw [dens_transpose_direct E c μ ν]
    exact h'

open Classical in
/-- F-HallEmbed: an injective odd map and even probability rows on common neighbourhoods with column sums at most
one give a cube (even roles on the first side). -/
theorem cubeAt_of_rows {n N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N) (hB : Function.Injective fB)
    (p : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ)
    (hp0 : ∀ a x, 0 ≤ p a x) (hp1 : ∀ a, ∑ x, p a x = 1)
    (hsupp : ∀ a x, p a x ≠ 0 → ∀ b : {v : CubeVertex n // ¬ IsEvenRole v}, (cube n).Adj a.1 b.1 →
      Hits E c x (fB b))
    (hcol : ∀ x, ∑ a, p a x ≤ 1) : CubeAt n N E := by
  classical
  let L : {v : CubeVertex n // IsEvenRole v} → Finset (Fin N) :=
    fun a => Finset.univ.filter (fun x => p a x ≠ 0)
  obtain ⟨fA, hfA, hmem⟩ := exists_injective_of_fractional p L hp0 hp1
    (by
      intro a x hx
      by_contra hne
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩)) hcol
  have hedge : ∀ a b, (cube n).Adj a.1 b.1 → Hits E c (fA a) (fB b) := by
    intro a b hab
    have hnonzero : p a (fA a) ≠ 0 := (Finset.mem_filter.mp (hmem a)).2
    exact hsupp a (fA a) hnonzero b hab
  exact ⟨c, cube_copy_of_parts fA fB hfA hB hedge⟩

end HypercubeRamsey
