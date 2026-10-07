import HypercubeRamsey.Framework.PartC
import HypercubeRamsey.Assembly
import HypercubeRamsey.S07.InitialDiscrepancy
import HypercubeRamsey.S10.ClusterExclusion
import HypercubeRamsey.S11.Exports

/-!
# The top-level chain

Part B's three exports (`research/blueprint/PART-B.md` §1.4) on one stabilized stage feed part C's main theorem
(`research/blueprint/PART-C.md` §1.3); conversion lemmas translate between the two vocabularies.
-/

namespace HypercubeRamsey

open Filter OAI.HypercubeRamsey

/-- Corollary 7.2 (initial discrepancy, eq:source-2); `η₀` is universal. -/
theorem initial_discrepancy : ∃ η₀ > (0 : ℝ), ∀ T : Stage, StabilizedOn T FamB →
    DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀)) :=
  S07.initial_discrepancy_proof

/-- Corollary 11.4 (the remaining deep regime), both orientations. -/
theorem remaining_deep_regime (T : Stage) (hT : StabilizedOn T FamB) :
    ∀ ε : ℝ, 0 < ε → ∃ x α : ℚ, 0 < x ∧ 0 < α ∧
      DiscAt T (pw x) (lw α) (fun n => n ^ (-1 + ε)) ∧
      DiscAt T.swap (pw x) (lw α) (fun n => n ^ (-1 + ε)) :=
  S11.remaining_deep_regime_proof T hT

/-- Corollary 10.2 (eventual absence of cluster witnesses). -/
theorem eventual_cluster_absence (η₀ : ℝ) (hη₀ : 0 < η₀) (T : Stage) (hT : StabilizedOn T FamB)
    (h2 : DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))) :
    ∀ (G : Colour) (ζ δ : ℚ), 0 < ζ → 0 < δ → (δ : ℝ) < min (min η₀ ζ) 1 / 2000 →
      EventuallyAbsent T (PCluster G ζ δ) ∧ EventuallyAbsent T.swap (PCluster G ζ δ) :=
  S10.eventual_cluster_absence_proof η₀ hη₀ T hT h2

/-- Part C's main theorem (node C18.F). -/
theorem partC_main (T : Stage) (η0 : ℝ) (hη0 : 0 < η0) (hInit : InitDisc T η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε)
    (hClu : ∀ (ζ δ : ℚ), 0 < ζ → 0 < δ → (δ : ℝ) < min η0 (min (ζ : ℝ) 1) / 2000 →
      ∀ (c : Colour) (o : Bool), ∀ᶠ k in atTop, ¬ ClusterWitnessAt (T.orient o) k c ζ δ) :
    False := sorry

/-- Conversion: equal power budgets give part C's `InitDisc`. -/
theorem initDisc_of_discAt {T : Stage} {η₀ : ℝ} (h : DiscAt T (pw η₀) (pw η₀) (fun n => n ^ (-η₀))) :
    InitDisc T η₀ := by
  change ∀ᶠ k in atTop,
    TwoBudgetDisc T k ((T.S.n k : ℝ) ^ η₀) ((T.S.n k : ℝ) ^ η₀)
      ((T.S.n k : ℝ) ^ (-η₀))
  unfold DiscAt at h
  filter_upwards [h] with k hk
  intro c μ ν hμ hν hbudget
  rcases hbudget with ⟨hμw, hνw⟩ | ⟨hμw, hνw⟩
  · exact hk c μ ν hμ hν hμw hνw
  · exact hk c μ ν hμ hν hμw hνw

/-- Conversion: both orientations of the deep regime give part C's `DeepDisc`. -/
theorem deepDisc_of_discAt {T : Stage} {x α : ℚ} {ε : ℝ}
    (h₁ : DiscAt T (pw x) (lw α) (fun n => n ^ (-1 + ε)))
    (h₂ : DiscAt T.swap (pw x) (lw α) (fun n => n ^ (-1 + ε))) :
    DeepDisc T x α ε := by
  change ∀ᶠ k in atTop,
    TwoBudgetDisc T k ((T.S.n k : ℝ) ^ (x : ℝ)) ((α : ℝ) * T.S.n k)
      ((T.S.n k : ℝ) ^ (-1 + ε))
  have dens_transpose_local {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
      (μ ν : Law N) : dens (transposeRel E) c μ ν = dens E c ν μ := by
    classical
    unfold dens
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro x hx
    simp only [hits_transpose]
    ring
  unfold DiscAt at h₁ h₂
  filter_upwards [h₁, h₂] with k hk₁ hk₂
  intro c μ ν hμ hν hbudget
  rcases hbudget with ⟨hμL, hνS⟩ | ⟨hμS, hνL⟩
  · have hd : |dens (T.S.E k) c μ ν - 1 / 2| ≤ (T.S.n k : ℝ) ^ (-1 + ε) := by
      have hds :
          |dens (transposeRel (T.S.E k)) c ν μ - 1 / 2| ≤ (T.S.n k : ℝ) ^ (-1 + ε) := by
        change |dens (transposeRel (T.S.E k)) c ν μ - 1 / 2| ≤
          (T.S.n k : ℝ) ^ (-1 + ε)
        exact hk₂ c ν μ hν hμ hνS hμL
      rw [dens_transpose_local] at hds
      exact hds
    exact hd
  · exact hk₁ c μ ν hμ hν hμS hνL

/-- Conversion: absence of part B's cluster property excludes part C's witness. -/
theorem not_clusterWitnessAt_of_absent {T : Stage} {G : Colour} {ζ δ : ℝ}
    (h : EventuallyAbsent T (PCluster G ζ δ)) : ∀ᶠ k in atTop, ¬ ClusterWitnessAt T k G ζ δ := by
  classical
  unfold EventuallyAbsent at h
  filter_upwards [h] with k hk
  intro hw
  rcases hw with ⟨m, μ, lam, D, hμ, hD, hlam, hsum, hwidth, havg, hDj, hcodeg⟩
  have hcodeg_eq (y y' : Fin (T.S.N k)) :
      codeg (T.S.E k) G μ y y' =
        ∑ x, μ.w x * hit (T.S.E k) G x y * hit (T.S.E k) G x y' := by
    unfold codeg hit
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hy : Hits (T.S.E k) G x y <;>
      by_cases hy' : Hits (T.S.E k) G x y' <;> simp [hy, hy']
  have hmem : (T.X k, T.Y k) ∈ PCluster G ζ δ (T.S.n k) (T.S.N k) (T.S.E k) := by
    refine ⟨μ, m, lam, D, hμ, hD, hlam, hsum, hwidth, havg, hDj, ?_⟩
    intro j hpos y y' hy hy'
    rw [hcodeg_eq]
    exact hcodeg j y y' hy hy'
  exact (hk (T.X k) (T.Y k) hmem) ⟨subset_rfl, subset_rfl⟩

/-- `swap` and `orient` agree. -/
theorem orient_true (T : Stage) : T.orient true = T.swap := rfl

/-- No bad sequence exists. -/
theorem no_badSeq (S : BadSeq) : False := by
  obtain ⟨T, -, hT⟩ := exists_stabilizedOn (Stage.ofBadSeq S) FamB FamB_countable
  obtain ⟨η₀, hη₀, hInit⟩ := initial_discrepancy
  have hD := hInit T hT
  refine partC_main T η₀ hη₀ (initDisc_of_discAt hD) ?_ ?_
  · intro ε hε
    obtain ⟨x, α, hx, hα, h₁, h₂⟩ := remaining_deep_regime T hT ε hε
    exact ⟨x, α, by exact_mod_cast hx, by exact_mod_cast hα, deepDisc_of_discAt h₁ h₂⟩
  · intro ζ δ hζ hδ hδ' c o
    have hδ'' : (δ : ℝ) < min (min η₀ ζ) 1 / 2000 := by
      rw [min_assoc]; exact hδ'
    obtain ⟨hA, hB⟩ := eventual_cluster_absence η₀ hη₀ T hT hD c ζ δ hζ hδ hδ''
    cases o
    · exact not_clusterWitnessAt_of_absent hA
    · exact not_clusterWitnessAt_of_absent hB

theorem linear_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (ramseyNumber (cube n) : ℝ) ≤ C * (2 : ℝ) ^ n := by
  by_contra hnot
  obtain ⟨S⟩ := badSeq_of_not_linear hnot
  exact no_badSeq S

end HypercubeRamsey
