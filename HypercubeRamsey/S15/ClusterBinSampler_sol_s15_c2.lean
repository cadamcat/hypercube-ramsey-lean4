import HypercubeRamsey.S15.ClusterBinStage_sol_s15_c2
import HypercubeRamsey.S15.ClusterBinCertificates_sol_s15_c2
import HypercubeRamsey.S15.ClusterBinLocality_sol_s15_c2
import HypercubeRamsey.S15.ClusterCharges_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev BinEvent {κ : CConsts} {T : Stage} {k : ℕ} (PT : ProfiledTiling κ T k) :=
  (EvenPosition T k × Bool) ⊕ CapacityCertificate PT

noncomputable def binDuplicate {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (B : ClusterBinAssignment PT) : Prop :=
  PT.tiling.mode = .highSmall ∧ ∃ g ∈ starGroupQueries PT hPT hm a,
    ∃ g' ∈ starGroupQueries PT hPT hm a, g ≠ g' ∧ (B g).1 = (B g').1

noncomputable def binEventScope {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) :
    BinEvent PT → Finset (ClusterGroupIndex PT)
  | .inl a => starGroupQueries PT hPT hm a.1
  | .inr c => c.2.2

noncomputable def binEventBad {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) : BinEvent PT → ClusterBinAssignment PT → Prop
  | .inl (a, false), B => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) <
      (clusterIndependentLabelKernel PT hPT hm W B).pr (fun I => clusterRowMass PT hPT hm W I a < 1 / 2)
  | .inl (a, true), B => binDuplicate PT hPT hm a B
  | .inr c, B => certificateEvent PT hPT hm W c B

theorem binEvent_depends {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (e : BinEvent PT) :
    FinProb.DependsOn (binEventBad PT hPT hm W e) (binEventScope PT hPT hm e) := by
  intro B B' hBB
  cases e with
  | inl a =>
    rcases a with ⟨a, flag⟩
    cases flag with
    | false =>
      apply congrArg (fun z => (T.S.n k : ℝ) ^ (-(κ.R : ℝ) / 2) < z)
      exact reference_mass_failure_bin_depends PT hPT hm W a B B' hBB
    | true =>
      apply propext
      unfold binEventBad binDuplicate
      apply and_congr_right
      intro hs
      constructor
      · rintro ⟨g, hg, g', hg', hne, heq⟩
        refine ⟨g, hg, g', hg', hne, ?_⟩
        rwa [hBB g hg, hBB g' hg'] at heq
      · rintro ⟨g, hg, g', hg', hne, heq⟩
        refine ⟨g, hg, g', hg', hne, ?_⟩
        rwa [hBB g hg, hBB g' hg']
  | inr c => exact propext (certificate_event_depends PT hPT hm W c B B' hBB)

theorem bin_output_of_avoidance {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (L : FinLaw (ClusterBinAssignment PT))
    (hraw : ∀ B, L.w B ≠ 0 → (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0)
    (havoid : ∀ B, L.w B ≠ 0 → ∀ e, ¬ binEventBad PT hPT hm W e B)
    (hcapacity : ∀ B, (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0 →
      clusterCapacityAvoided PT hPT hm W B → ∀ y, clusterGivenBinColumn PT hPT hm W B y ≤ κ.θ0)
    (hcomp : ∀ F : ClusterBinAssignment PT → ℝ, (∀ B, 0 ≤ F B) →
      ∀ S : Finset (ClusterGroupIndex PT), ClusterBinDependsOn F S → (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 3 →
        L.E F ≤ (1 + 1 / (T.S.n k : ℝ)) * (clusterIndependentBinKernel PT hPT hm W).E F) :
    Nonempty (BinLawOutput PT hPT hm W) := by
  refine ⟨⟨L, ?_, hcomp⟩⟩
  intro B hB
  have hBpos : 0 < (clusterIndependentBinKernel PT hPT hm W).w B :=
    lt_of_le_of_ne ((clusterIndependentBinKernel PT hPT hm W).nonneg B) (Ne.symm (hraw B hB))
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [bin_star_failure_eq PT hPT hm W B a hBpos]
    exact le_of_not_gt (havoid B hB (.inl (a, false)))
  · apply hcapacity B (hraw B hB)
    apply (capacity_avoided_iff_certificates PT hPT hm W B).2
    intro c
    exact havoid B hB (.inr c)
  · intro hs a b b' hab hab' hne heq
    apply havoid B hB (.inl (a, true))
    refine ⟨hs, clusterGroupIndexAt PT hPT hm b, ?_, clusterGroupIndexAt PT hPT hm b', ?_, hne, heq⟩
    · exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨b', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab'⟩, rfl⟩

end HypercubeRamsey.Lane_sol_s15_c2
