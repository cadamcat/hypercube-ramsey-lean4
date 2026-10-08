import HypercubeRamsey.S06.Steps_joint_sol_s06_g

namespace HypercubeRamsey.S06.Lane_sol_s06_g
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)
variable {Id : Type} [Fintype Id] [DecidableEq Id]

 theorem fixed_parent_marginal (pv : Par6 X.Bin N) (D : Finset (Id × X.Ty)) (F : X.Hist → ℝ)
    (hF : ∀ (I I' : X.Key → X.ι) (Z Z' : X.Hid),
      (∀ s ∈ X.locKeys D, I s = I' s) → (∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) →
      F ((pv.1, pv.2, I), Z) = F ((pv.1, pv.2, I'), Z')) :
    (FinProb.pi (X.tagLawAt pv)).expect (fun I =>
      (X.hidLaw (pv.1, pv.2, I)).expect (fun Z => F ((pv.1, pv.2, I), Z))) =
    (FinProb.pi fun s : {s : X.Key // s ∈ X.locKeys D} => X.tagLawAt pv s.1).expect (fun I =>
      (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D} =>
        X.hidPost (pv.1, pv.2, Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)) ℓ.1.1).expect
          (fun Z => F ((pv.1, pv.2, Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)),
            Lane_sol_s06_steps1.fill (X.locHid D) Z (fun _ => X.y₀)))) := by
  let S := X.locKeys D
  let T := X.locHid D
  let inner (I : X.Key → X.ι) :=
    (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ T} => X.hidPost (pv.1, pv.2, I) ℓ.1.1).expect
      (fun Z => F ((pv.1, pv.2, I), Lane_sol_s06_steps1.fill T Z (fun _ => X.y₀)))
  have hhidden (I : X.Key → X.ι) :
      (X.hidLaw (pv.1, pv.2, I)).expect (fun Z => F ((pv.1, pv.2, I), Z)) = inner I := by
    apply Lane_sol_s06_steps1.pi_expect_fill
    intro Z Z' hZ
    exact hF I I Z Z' (fun s hs => rfl) hZ
  have hdep : FinProb.DependsOn inner S := by
    intro I I' hI
    have hlaw : (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ T} => X.hidPost (pv.1, pv.2, I) ℓ.1.1) =
        FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ T} => X.hidPost (pv.1, pv.2, I') ℓ.1.1 := by
      congr 1
      funext ℓ
      unfold Ctx6.hidPost
      congr 1
      funext y
      have hC : X.C ℓ.1.1 ⊆ S := by
        intro s hs
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ℓ.1, ℓ.2, hs⟩)
      exact Lane_sol_s06_steps1.hidWeight_local X ℓ.1.1 (X.C ℓ.1.1) (Finset.Subset.refl _) (pv.1, pv.2, I) (pv.1, pv.2, I')
        (fun _ => rfl) (fun _ u hu => rfl) (fun s hs => hI s (hC hs)) y
    unfold inner
    rw [hlaw]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro Z hZ
    congr 1
    exact hF I I' _ _ hI (fun ℓ hℓ => rfl)
  simp_rw [hhidden]
  exact Lane_sol_s06_steps1.pi_expect_fill (X.tagLawAt pv) S inner (fun _ => X.i₀) hdep

end
end HypercubeRamsey.S06.Lane_sol_s06_g
