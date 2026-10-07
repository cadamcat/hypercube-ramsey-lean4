import HypercubeRamsey.S11.Core.OuterMoment
import HypercubeRamsey.S11.Needs
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.S03.ScatteredMoments
import HypercubeRamsey.S03.ClockSampling

/-! P11.1d1–d3 and the Hall assembly of the complete one-shot embedding. -/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open scoped BigOperators

/-- Outer words indexing the independent inner slices. -/
abbrev OuterWord (n : ℕ) := CubeVertex (outerDimension n)

/-- A tag assignment to every outer word. -/
abbrev TagField (n : ℕ) (ι : Type*) := OuterWord n → ι

/-- Flip one outer coordinate. -/
noncomputable def outerFlip {d : ℕ} (s : CubeVertex d) (j : Fin d) : CubeVertex d :=
  Function.update s j (!s j)

/-- The high-degree-neighbour count in the tag gate T2. -/
noncomputable def highDegreeNeighbourCount {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀)
    {h k : ℕ} {g : ℝ} (S : SliceSeed M h k g) (t : TagField n M.mix.ι)
    (s : OuterWord n) (x : Fin N) : ℝ := by
  classical
  exact ∑ j : Fin (outerDimension n),
    if rowDeg E M.G x (S.π (t (outerFlip s j))) > (4 / 5 : ℝ) then 1 else 0

/-- The comparison mean `A_s(y)=N π_{i(s)}(y)`. -/
noncomputable def oddComparisonWeight {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀)
    {h k : ℕ} {g : ℝ} (S : SliceSeed M h k g) (t : TagField n M.mix.ι)
    (s : OuterWord n) (y : Fin N) : ℝ := (N : ℝ) * (S.π (t s)).w y

/-- The comparison mean `B_s(x)` for expected even rows and the outer degree ratios. -/
noncomputable def evenComparisonWeight {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀)
    {h k : ℕ} {g : ℝ} (S : SliceSeed M h k g) (R : CommonRows S)
    (p : FinProb M.mix.ι) (t : TagField n M.mix.ι) (s : OuterWord n) (x : Fin N) : ℝ := by
  classical
  let π := profileLaw p S.π
  let D := lawDegree E M.G π x
  exact if D = 0 then 0 else
    (N : ℝ) * (R.α (t s)).w x *
      ∏ j : Fin (outerDimension n),
        rowDeg E M.G x (S.π (t (outerFlip s j))) / D

/-- The L3.10 near-product comparison for tag choices on at most `n` outer words. -/
def TagNearProduct {n : ℕ} {ι : Type*} [Fintype ι]
    (p : FinProb ι) (J : FinProb (TagField n ι)) : Prop :=
  ∀ (U : Finset (OuterWord n)) (labels : ∀ s : U, ι),
    (U.card : ℝ) ≤ (n : ℝ) ^ (4 : ℕ) →
    J.pr (fun t => ∀ s : U, t s.1 = labels s) ≤
      2 * ∏ s : U, p.w (labels s)

/-- Output of P11.1d1: an avoided tag law with raw failure bounds and bounded comparison means. -/
structure TagReferenceData {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀) {h k : ℕ} {g : ℝ}
    (S : SliceSeed M h k g) (R : CommonRows S) (p : FinProb M.mix.ι)
    (P K : ℝ) where
  law : FinProb (TagField n M.mix.ι)
  nearProduct : TagNearProduct p law
  rawFailure : TagField n M.mix.ι → OuterWord n → ℝ
  rawFailure_nonneg : ∀ t s, 0 ≤ rawFailure t s
  rawFailure_small : ∀ t s, law.w t > 0 → rawFailure t s ≤ (n : ℝ) ^ (-2 * P)
  degree_gate : ∀ t s x, law.w t > 0 → (M.mix.μ (t s)).w x ≠ 0 →
    highDegreeNeighbourCount M S t s x ≤ (outerDimension n : ℝ) / 2
  oddComparison_average : ∀ y,
    (∑ t, law.w t * ∑ s : OuterWord n, oddComparisonWeight M S t s y) ≤
      K * (2 : ℝ) ^ outerDimension n
  evenComparison_average : ∀ x,
    (∑ t, law.w t * ∑ s : OuterWord n, evenComparisonWeight M S R p t s x) ≤
      K * (2 : ℝ) ^ outerDimension n

/-- A selected injective label on every odd role of the target cube. -/
structure OddInjectionData (n N : ℕ) where
  label : OddRole n → Fin N
  injective : Function.Injective label

/-- Fractional rows on the even roles with common-neighbour support and unit capacity. -/
structure FractionalHallRows {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) where
  oddLabel : OddRole n → Fin N
  odd_injective : Function.Injective oddLabel
  row : EvenRole n → Fin N → ℝ
  row_nonneg : ∀ v x, 0 ≤ row v x
  row_sum : ∀ v, ∑ x, row v x = 1
  common_neighbour : ∀ v x, row v x ≠ 0 → ∀ b : OddRole n,
    (cube n).Adj v.1 b.1 → Hits E G x (oddLabel b)
  column_load : ∀ x, ∑ v : EvenRole n, row v x ≤ 1

/-- F-HallEmbed: the fractional rows give a monochromatic cube. -/
theorem cube_of_fractional_rows {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (H : FractionalHallRows (n := n) E G) : CubeAt n N E := by
  exact cubeAt_of_rows E G H.oddLabel H.odd_injective H.row H.row_nonneg H.row_sum
    H.common_neighbour H.column_load

/-- P11.1d1: conditional avoidance at the tag stage and bounded comparison means. -/
theorem reference_failure_and_tag_avoidance {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀)
    {h k : ℕ} {g δ x₀ : ℝ} (S : SliceSeed M h k g) (R : CommonRows S)
    (p : FinProb M.mix.ι) (K : ℝ) (hProfile : CompatibleProfile M S R p K δ (1 / 100000000 : ℝ))
    (P : ℝ) (hHost : 2 ^ n ≤ N) (hscale : ScaleBounds n δ x₀ h₀ κ)
    (hDisc : DiscOne E X Y ((n : ℝ) ^ (1 - δ / 16)) ((n : ℝ) ^ x₀) (signedBiasScale n))
    (hClusterXY : ∀ G' A B, A ⊆ X → B ⊆ Y →
      (A, B) ∉ PCluster G' ((1 / 100 : ℚ) : ℝ) δ n N E)
    (hClusterYX : ∀ G' A B, A ⊆ Y → B ⊆ X →
      (A, B) ∉ PCluster G' ((1 / 100 : ℚ) : ℝ) δ n N (transposeRel E))
    (hTail : ∀ K' : ℝ, 0 < K' → ∀ O : OuterSetup (n := n) E X Y δ x₀ K',
      outerFailureMass O ≤ (n : ℝ) ^ (-P)) :
    ∃ D : TagReferenceData M S R p P K, True := by
  sorry

/-- P11.1d2: tuple-stage avoidance and the odd-role injection. -/
theorem odd_injection_from_reference {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀)
    {h k : ℕ} {g δ x₀ : ℝ} (S : SliceSeed M h k g) (R : CommonRows S)
    (p : FinProb M.mix.ι) {K P : ℝ} (D : TagReferenceData M S R p P K)
    (hHost : 2 ^ n ≤ N) (hscale : ScaleBounds n δ x₀ h₀ κ) :
    ∃ H : OddInjectionData n N, True := by
  sorry

/-- P11.1d3: even-row normalization and the final common-neighbour Hall rows. -/
theorem fractional_rows_from_assignment {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} {κ h₀ : ℝ} (M : BiasedMenu n N E X Y κ h₀)
    {h k : ℕ} {g δ x₀ : ℝ} (S : SliceSeed M h k g) (R : CommonRows S)
    (p : FinProb M.mix.ι) {K P : ℝ} (D : TagReferenceData M S R p P K)
    (H : OddInjectionData n N) (hHost : 2 ^ n ≤ N)
    (hscale : ScaleBounds n δ x₀ h₀ κ) :
    ∃ Q : FractionalHallRows (n := n) E M.G, True := by
  sorry

/-- P11.1c: assemble P11.1-menu/a/b, L11.2, L11.3 and P11.1d1–d3 into the one-shot cube embedding. -/
theorem linear_jump_core_from_nodes (δ x₀ h₀ : ℚ) (κ : ℝ)
    (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1 / 20000)
    (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1)
    (hh₀ : 0 < h₀) (hh₀1 : h₀ < 1 / 100) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)),
      LargeAt n₀ C₀ n N →
      DiscOne E X Y ((n : ℝ) ^ ((1 : ℝ) - (δ : ℝ) / 16))
        ((n : ℝ) ^ (x₀ : ℝ)) ((n : ℝ) ^ (-(19 : ℝ) / 20)) →
      (∀ (G : Colour) A B, A ⊆ X → B ⊆ Y →
        (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) (δ : ℝ) n N E) →
      (∀ (G : Colour) A B, A ⊆ Y → B ⊆ X →
        (A, B) ∉ PCluster G ((1 / 100 : ℚ) : ℝ) (δ : ℝ) n N (transposeRel E)) →
      AvailableAt κ
        (PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) (h₀ : ℝ)).toPatch
        n N E X Y → CubeAt n N E := by
  obtain ⟨n₀, hscaleAll⟩ := exists_scale_bounds (δ : ℝ) (x₀ : ℝ) (h₀ : ℝ) κ
    (by exact_mod_cast hδ) hδ1 (by exact_mod_cast hx₀) (by exact_mod_cast hx₀1)
    (by exact_mod_cast hh₀) (by simpa using (Rat.cast_lt (K := ℝ)).mpr hh₀1) hκ
  let C₀ : ℝ := max 1 (100 / κ)
  refine ⟨n₀, C₀, ?_⟩
  intro n N E X Y hLarge hDisc hClusterXY hClusterYX hAvail
  have hscale : ScaleBounds n (δ : ℝ) (x₀ : ℝ) (h₀ : ℝ) κ := hscaleAll n hLarge.1
  have hC₀ : (1 : ℝ) ≤ C₀ := by dsimp [C₀]; exact le_max_left _ _
  have hHostR : (2 : ℝ) ^ n ≤ (N : ℝ) := by
    calc
      (2 : ℝ) ^ n = 1 * (2 : ℝ) ^ n := by ring
      _ ≤ C₀ * (2 : ℝ) ^ n := mul_le_mul_of_nonneg_right hC₀ (by positivity)
      _ ≤ (N : ℝ) := hLarge.2.1
  have hHost : 2 ^ n ≤ N := by exact_mod_cast hHostR
  obtain ⟨M, -⟩ := biased_menu E X Y (δ : ℝ) (x₀ : ℝ) (h₀ : ℝ) κ
    (by exact_mod_cast hδ) hδ1 (by exact_mod_cast hx₀) (by exact_mod_cast hx₀1)
    (by exact_mod_cast hh₀) (by simpa using (Rat.cast_lt (K := ℝ)).mpr hh₀1) hκ hscale hAvail
  obtain ⟨S, -⟩ := slice_seed E X Y (δ : ℝ) (x₀ : ℝ) (h₀ : ℝ) κ hscale M
  obtain ⟨R, -⟩ := common_rows E X Y (δ : ℝ) (x₀ : ℝ) (h₀ : ℝ) κ hscale M S
  let η : ℝ := 1 / 100000000
  obtain ⟨K, hK, p, hProfile⟩ := compatible_balanced_profile
    (M := M) (S := S) (R := R) (δ := (δ : ℝ)) (η := η) (x₀ := (x₀ : ℝ))
    hκ (by norm_num [η]) hscale
  have hTail : ∀ K' : ℝ, 0 < K' → ∀ O : OuterSetup (n := n) E X Y (δ : ℝ) (x₀ : ℝ) K',
      outerFailureMass O ≤ (n : ℝ) ^ (-100 : ℝ) := by
    intro K' hK' O
    exact outer_mass_tail O
  obtain ⟨D, -⟩ := reference_failure_and_tag_avoidance M S R p K hProfile 100 hHost hscale hDisc
    hClusterXY hClusterYX hTail
  obtain ⟨H, -⟩ := odd_injection_from_reference M S R p D hHost hscale
  obtain ⟨Q, -⟩ := fractional_rows_from_assignment M S R p D H hHost hscale
  exact cube_of_fractional_rows Q

end HypercubeRamsey.S11.Core
