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

 theorem parent_window_marginal (v : Fin N) (D : Finset (Id × X.Ty)) (S : Finset X.Bin)
    (hS : X.binsOf (X.locKeys D) ⊆ S) (F : X.Hist → ℝ)
    (hF : ∀ (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι) (Z Z' : X.Hid),
      (∀ u ∈ S, A u = A' u) → (∀ s ∈ X.locKeys D, I s = I' s) → (∀ ℓ ∈ X.locHid D, Z ℓ = Z' ℓ) →
      F ((v, A, I), Z) = F ((v, A', I'), Z')) :
    (X.coarseLaw v).expect (fun AI => (X.hidLaw (v, AI)).expect (fun Z => F ((v, AI), Z))) =
    (FinProb.pi fun _u : {u : X.Bin // u ∈ S} => X.candLaw v).expect (fun A =>
      (FinProb.pi fun s : {s : X.Key // s ∈ X.locKeys D} =>
        X.tagLawAt (v, Lane_sol_s06_steps1.fill S A (fun _ => X.y₀)) s.1).expect (fun I =>
          (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D} =>
            X.hidPost (v, Lane_sol_s06_steps1.fill S A (fun _ => X.y₀),
              Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)) ℓ.1.1).expect
              (fun Z => F ((v, Lane_sol_s06_steps1.fill S A (fun _ => X.y₀),
                Lane_sol_s06_steps1.fill (X.locKeys D) I (fun _ => X.i₀)),
                Lane_sol_s06_steps1.fill (X.locHid D) Z (fun _ => X.y₀))))) := by
  let Kloc := X.locKeys D
  let Vloc := X.locHid D
  let inner (A : X.Bin → Fin N) :=
    (FinProb.pi fun s : {s : X.Key // s ∈ Kloc} => X.tagLawAt (v, A) s.1).expect (fun I =>
      (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ Vloc} =>
        X.hidPost (v, A, Lane_sol_s06_steps1.fill Kloc I (fun _ => X.i₀)) ℓ.1.1).expect
        (fun Z => F ((v, A, Lane_sol_s06_steps1.fill Kloc I (fun _ => X.i₀)),
          Lane_sol_s06_steps1.fill Vloc Z (fun _ => X.y₀))))
  have hfixed (A : X.Bin → Fin N) :
      (FinProb.pi (X.tagLawAt (v, A))).expect (fun I => (X.hidLaw (v, A, I)).expect (fun Z => F ((v, A, I), Z))) = inner A :=
    fixed_parent_marginal X (v, A) D F (fun I I' Z Z' hI hZ => hF A A I I' Z Z' (fun u hu => rfl) hI hZ)
  have hdep : FinProb.DependsOn inner S := by
    intro A A' hA
    have htags : (FinProb.pi fun s : {s : X.Key // s ∈ Kloc} => X.tagLawAt (v, A) s.1) =
        FinProb.pi fun s : {s : X.Key // s ∈ Kloc} => X.tagLawAt (v, A') s.1 := by
      congr 1
      funext s
      have hbin := hA s.1.1 (hS (Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩))
      cases hf : s.1.2 <;> simp only [Ctx6.tagLawAt, primaryName6, otherPrimaryName6, hf, Par6.val, hbin]
    unfold inner
    rw [htags]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro I hI
    congr 1
    have hhid : (FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ Vloc} =>
        X.hidPost (v, A, Lane_sol_s06_steps1.fill Kloc I (fun _ => X.i₀)) ℓ.1.1) =
        FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ Vloc} =>
        X.hidPost (v, A', Lane_sol_s06_steps1.fill Kloc I (fun _ => X.i₀)) ℓ.1.1 := by
      congr 1
      funext ℓ
      unfold Ctx6.hidPost
      congr 1
      funext y
      have hC : X.C ℓ.1.1 ⊆ Kloc := by
        intro s hs
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ℓ.1, ℓ.2, hs⟩)
      have hCB : X.binsOf (X.C ℓ.1.1) ⊆ S := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨s, hs, rfl⟩
        exact hS (Finset.mem_image.mpr ⟨s, hC hs, rfl⟩)
      exact Lane_sol_s06_steps1.hidWeight_local X ℓ.1.1 (X.C ℓ.1.1) (Finset.Subset.refl _)
        (v, A, Lane_sol_s06_steps1.fill Kloc I (fun _ => X.i₀))
        (v, A', Lane_sol_s06_steps1.fill Kloc I (fun _ => X.i₀))
        (fun _ => rfl) (fun _ u hu => hA u (hCB hu)) (fun s hs => rfl) y
    rw [hhid]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro Z hZ
    congr 1
    exact hF A A' _ _ _ _ hA (fun s hs => rfl) (fun ℓ hℓ => rfl)
  unfold Ctx6.coarseLaw
  rw [FinProb.bind_expect _ _ (fun A I => (X.hidLaw (v, A, I)).expect (fun Z => F ((v, A, I), Z)))]
  simp_rw [hfixed]
  exact Lane_sol_s06_steps1.pi_expect_fill (fun _ : X.Bin => X.candLaw v) S inner (fun _ => X.y₀) hdep


end
end HypercubeRamsey.S06.Lane_sol_s06_g
