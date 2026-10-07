import HypercubeRamsey.S10.LocalNodes
import HypercubeRamsey.Interface

/-!
# Section 10: cluster exclusion

The stochastic construction is separated into its source nodes.  The hard row
construction and its even-side transfer are statement skeletons; the two exports
below are proved by composing those nodes with the framework's Hall and one-shot
interfaces.
-/

namespace HypercubeRamsey.S10

open Filter OAI.HypercubeRamsey
open Classical

/-- Odd-role injection produced by the tag and clock construction. -/
structure OddEmbeddingData (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) where
  label : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  injective : Function.Injective label

/-- Fractional even rows supported on common neighborhoods of the odd injection. -/
structure HallRows (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) where
  odd : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N
  odd_injective : Function.Injective odd
  row : {v : CubeVertex n // IsEvenRole v} → Fin N → ℝ
  row_nonnegative : ∀ a x, 0 ≤ row a x
  row_sum : ∀ a, ∑ x, row a x = 1
  common_neighbor : ∀ a x, row a x ≠ 0 →
    ∀ b : {v : CubeVertex n // ¬ IsEvenRole v},
      (cube n).Adj a.1 b.1 → Hits E G x (odd b)
  column_load : ∀ x, ∑ a, row a x ≤ 1

/-- P10.1j (10:263–281): the profile, cluster and odd-injection construction. -/
theorem p10_1j_tag_profiles_and_odd_injection
    (η₀ ζ δ κ : ℝ) (hη₀ : 0 < η₀) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (hκ : 0 < κ)
    (hscale : ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ (500 * δ) < (n : ℝ) ^ η₀ ∧
      3 * (n : ℝ) ^ (500 * δ) < (n : ℝ) ^ ζ ∧
      4 * (n : ℝ) ^ (200 * δ) < (n : ℝ) ^ (1 - δ) ∧
      ((n : ℝ) ^ (200 * δ) + (n : ℝ) ^ (141 * δ)) * Real.log n <
        (n : ℝ) ^ (298 * δ))
    (hprojection : P10_1aProjectionStatement)
    (hfixed : P10_1cFixedListTest η₀ δ hη₀ hδ
      (by
        have hmin : min (min η₀ ζ) 1 ≤ η₀ :=
          le_trans (min_le_left _ _) (min_le_left _ _)
        calc
          δ < min (min η₀ ζ) 1 / 2000 := hδsmall
          _ ≤ η₀ / 2000 := div_le_div_of_nonneg_right hmin (by norm_num))) :
    ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
      AvailableAt κ (PCluster G ζ δ) n N E X Y →
      Nonempty (OddEmbeddingData n N E G) := by
  sorry

/-- P10.1k (10:283–294): transfer the successful odd construction to fractional
even rows. -/
theorem p10_1k_transfer_to_even_rows
    (η₀ ζ δ κ : ℝ) {n₀ n N : ℕ} {C₀ : ℝ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {G : Colour}
    (hlarge : LargeAt n₀ C₀ n N)
    (hdisc : DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)))
    (havail : AvailableAt κ (PCluster G ζ δ) n N E X Y)
    (odd : OddEmbeddingData n N E G) : Nonempty (HallRows n N E G) := by
  sorry

/-- P10.1k / F-HallEmbed: turn the odd injection and even rows into a cube. -/
theorem p10_1k_hall_embed {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (rows : HallRows n N E G) : CubeAt n N E := by
  exact cubeAt_of_rows E G rows.odd rows.odd_injective rows.row rows.row_nonnegative
    rows.row_sum rows.common_neighbor rows.column_load

/-- P10.1 (10:12–20): an available full-dimensional cluster patch and initial
discrepancy force a monochromatic cube. -/
theorem cluster_exclusion_oneShot
    (η₀ : ℝ) (hη₀ : 0 < η₀) (ζ δ : ℝ) (hζ : 0 < ζ) (hδ : 0 < δ)
    (hδsmall : δ < min (min η₀ ζ) 1 / 2000) (κ : ℝ) (hκ : 0 < κ) :
    ∃ n₀ C₀, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
      AvailableAt κ (PCluster G ζ δ) n N E X Y → CubeAt n N E := by
  have hδeta : δ < η₀ / 2000 := by
    have hmin : min (min η₀ ζ) 1 ≤ η₀ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    exact lt_of_lt_of_le hδsmall (div_le_div_of_nonneg_right hmin (by norm_num))
  obtain ⟨n₀, C₀, hconstruct⟩ :=
    p10_1j_tag_profiles_and_odd_injection η₀ ζ δ κ hη₀ hζ hδ hδsmall hκ
      (p10_1b_scale_separation η₀ ζ δ hη₀ hζ hδ hδsmall)
      p10_1a_hamming_projection
      (p10_1c_fixed_list_squared_mass_test η₀ δ hη₀ hδ hδeta)
  refine ⟨n₀, C₀, ?_⟩
  intro n N E X Y G hlarge hdisc havail
  obtain ⟨odd⟩ := hconstruct n N E X Y G hlarge hdisc havail
  obtain ⟨rows⟩ := p10_1k_transfer_to_even_rows η₀ ζ δ κ hlarge hdisc havail odd
  exact p10_1k_hall_embed rows

private theorem cluster_absence_of_stabilized
    (η₀ : ℝ) (hη₀ : 0 < η₀) (T : Stage) (hT : StabilizedOn T FamB)
    (hdisc : DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))) :
    ∀ (G : Colour) (ζ δ : ℚ), 0 < ζ → 0 < δ →
      (δ : ℝ) < min (min η₀ ζ) 1 / 2000 →
      EventuallyAbsent T (PCluster G ζ δ) := by
  intro G ζ δ hζ hδ hδsmall
  have hζr : (0 : ℝ) < ζ := by exact_mod_cast hζ
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  let P : PatchProp := PCluster G ζ δ
  have hP : P ∈ FamB := by
    change PCluster G ζ δ ∈
      ({P | ∃ D₀ c : ℚ, P = (PViol D₀ c).toPatch ∨ P = (PViol D₀ c).toPatch.swap} ∪
        {P | ∃ β γ h : ℚ, P = (PPure β γ h).toPatch ∨ P = (PPure β γ h).toPatch.swap} ∪
        {P | ∃ x y h : ℚ, P = (PBias (pw x) (pw y) h).toPatch ∨
          P = (PBias (pw x) (pw y) h).toPatch.swap} ∪
        {P | ∃ x α h : ℚ, P = (PBias (pw x) (lw α) h).toPatch ∨
          P = (PBias (pw x) (lw α) h).toPatch.swap} ∪
        {P | ∃ (G : Colour) (ζ δ : ℚ), P = PCluster G ζ δ ∨
          P = (PCluster G ζ δ).swap})
    exact Or.inr ⟨G, ζ, δ, Or.inl rfl⟩
  let side : ∀ (n N : ℕ), (Fin N → Fin N → Prop) → Finset (Fin N) → Finset (Fin N) → Prop :=
    fun n N E X Y =>
      DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀))
  have hside : ∀ᶠ k in atTop,
      side (T.S.n k) (T.S.N k) (T.S.E k) (T.X k) (T.Y k) := by
    have h := (discAt_iff_eventually_discOne T (pw η₀) (pw η₀)
      (fun n => n ^ (-η₀))).mp hdisc
    simpa [side, pw] using h
  have hshot : ∀ κ > (0 : ℝ), ∃ n₀ C₀,
      ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
        LargeAt n₀ C₀ n N → side n N E X Y →
          AvailableAt κ P n N E X Y → CubeAt n N E := by
    intro κ hκ
    obtain ⟨n₀, C₀, hshotAll⟩ :=
      cluster_exclusion_oneShot η₀ hη₀ ζ δ hζr hδr hδsmall κ hκ
    refine ⟨n₀, C₀, ?_⟩
    intro n N E X Y hlarge hside havail
    exact hshotAll n N E X Y G hlarge hside havail
  have hnot : ¬ Available T P :=
    not_available_of_oneShot' side hside hshot
  rcases hT P hP with havailable | habsent
  · exact (hnot havailable).elim
  · exact habsent

/-- Corollary 10.2 (10:298–304), with exactly the interface type. -/
theorem eventual_cluster_absence_proof
    (η₀ : ℝ) (hη₀ : 0 < η₀) (T : Stage) (hT : StabilizedOn T FamB)
    (h2 : DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))) :
    ∀ (G : Colour) (ζ δ : ℚ), 0 < ζ → 0 < δ →
      (δ : ℝ) < min (min η₀ ζ) 1 / 2000 →
      EventuallyAbsent T (PCluster G ζ δ) ∧
        EventuallyAbsent T.swap (PCluster G ζ δ) := by
  intro G ζ δ hζ hδ hδsmall
  have h2swap : DiscAt T.swap (pw η₀) (pw η₀) (fun n => n ^ (-η₀)) :=
    (DiscAt.swap_iff T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))).2 h2
  have hTswap : StabilizedOn T.swap FamB := StabilizedOn.swap hT FamB_swap
  exact ⟨cluster_absence_of_stabilized η₀ hη₀ T hT h2 G ζ δ hζ hδ hδsmall,
    cluster_absence_of_stabilized η₀ hη₀ T.swap hTswap h2swap G ζ δ hζ hδ hδsmall⟩

end HypercubeRamsey.S10
