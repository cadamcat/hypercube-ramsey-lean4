import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

/-! Shared input-domain bookkeeping for the d8 lane. -/

namespace HypercubeRamsey.Lane_sol_s10_d8

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10
open scoped BigOperators

set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1000000

section Height

variable (p : HDParams)

theorem reach_domain {Sites : p.Sites} {P A : p.Loc → Bool} {E : p.EligMap}
    {vq : CubeVertex p.d} {R : ℕ} {v : CubeVertex p.d} {j : ℕ}
    (h : p.Reach Sites P A E vq R v j) : v ∈ Sites ∧ hammingDist v vq ≤ R := by
  induction h with
  | start v hv hdist => exact ⟨hv, hdist⟩
  | up v j hj hreach hbad ih => exact ih
  | down v v' j hreach hv' hdist hstep ih => exact ⟨hv', hdist⟩

theorem reach_congr {Sites : p.Sites} {P A P' A' : p.Loc → Bool}
    {E E' : p.EligMap} {vq : CubeVertex p.d} {R : ℕ}
    (hbad : ∀ v, v ∈ Sites → hammingDist v vq ≤ R → ∀ j,
      p.BadN P A E v j ↔ p.BadN P' A' E' v j) {v : CubeVertex p.d} {j : ℕ} :
    p.Reach Sites P A E vq R v j ↔ p.Reach Sites P' A' E' vq R v j := by
  have forward {P A P' A' : p.Loc → Bool} {E E' : p.EligMap}
      (hb : ∀ v, v ∈ Sites → hammingDist v vq ≤ R → ∀ j,
        p.BadN P A E v j → p.BadN P' A' E' v j)
      (h : p.Reach Sites P A E vq R v j) : p.Reach Sites P' A' E' vq R v j := by
    induction h with
    | start v hv hdist => exact .start v hv hdist
    | up v j hj hreach hbad ih =>
      have hd := reach_domain p hreach
      exact .up v j hj ih (hb v hd.1 hd.2 j hbad)
    | down v v' j hreach hv' hdist hstep ih => exact .down v v' j ih hv' hdist hstep
  exact ⟨forward (fun v hv hd j => (hbad v hv hd j).mp),
    forward (fun v hv hd j => (hbad v hv hd j).mpr)⟩

theorem height_congr {Sites : p.Sites} {P A P' A' : p.Loc → Bool}
    {E E' : p.EligMap} {vq : CubeVertex p.d} {R : ℕ}
    (hbad : ∀ v, v ∈ Sites → hammingDist v vq ≤ R → ∀ j,
      p.BadN P A E v j ↔ p.BadN P' A' E' v j) :
    p.height Sites P A E R vq = p.height Sites P' A' E' R vq := by
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => reach_congr p hbad

theorem bad_congr {P A P' A' : p.Loc → Bool} {E E' : p.EligMap}
    {v : CubeVertex p.d} {j : Fin (p.H + 1)}
    (hE : E v j = E' v j)
    (hEA : ∀ ℓ ∈ E v j, A ℓ = A' ℓ)
    (hP : ∀ u : CubeVertex p.d, hammingDist u v ≤ p.r + p.D → P (u, j) = P' (u, j))
    (hA : ∀ u : CubeVertex p.d, hammingDist u v ≤ p.r + p.D → A (u, j) = A' (u, j)) :
    p.Bad P A E v j ↔ p.Bad P' A' E' v j := by
  have hnone : (∀ ℓ ∈ E v j, A ℓ = false) ↔ (∀ ℓ ∈ E' v j, A' ℓ = false) := by
    rw [← hE]
    constructor <;> intro h ℓ hℓ
    · rw [← hEA ℓ hℓ]; exact h ℓ hℓ
    · rw [hEA ℓ hℓ]; exact h ℓ hℓ
  have hball :
      (Finset.univ.filter fun u : CubeVertex p.d =>
        P (u, j) = true ∧ A (u, j) = true ∧ hammingDist u v ≤ p.r + p.D) =
      (Finset.univ.filter fun u : CubeVertex p.d =>
        P' (u, j) = true ∧ A' (u, j) = true ∧ hammingDist u v ≤ p.r + p.D) := by
    ext u
    by_cases hd : hammingDist u v ≤ p.r + p.D
    · simp [hd, hP u hd, hA u hd]
    · simp [hd]
  unfold HDParams.Bad
  rw [hball]
  exact or_congr hnone Iff.rfl

theorem selectionAt_congr {Sites : p.Sites} {P A P' A' : p.Loc → Bool}
    {E E' : p.EligMap} {τ τ' : p.Ties} {vq : CubeVertex p.d} {R : ℕ}
    (hheight : p.height Sites P A E R vq = p.height Sites P' A' E' R vq)
    (hbad : ∀ j, p.Bad P A E vq j ↔ p.Bad P' A' E' vq j)
    (hE : ∀ j, E vq j = E' vq j)
    (hA : ∀ j ℓ, ℓ ∈ E vq j → A ℓ = A' ℓ)
    (hτ : ∀ j, τ (vq, j) = τ' (vq, j)) :
    p.selectionAt Sites P A E τ R vq = p.selectionAt Sites P' A' E' τ' R vq := by
  have hactive : ∀ j, (E vq j).filter (fun ℓ => A ℓ = true) =
      (E' vq j).filter (fun ℓ => A' ℓ = true) := by
    intro j
    rw [← hE j]
    exact Finset.filter_congr fun ℓ hℓ => by rw [hA j ℓ hℓ]
  unfold HDParams.selectionAt
  simp only [hheight]
  split
  · simp only [hbad, hactive, HDParams.priority, hτ]
    rfl
  · rfl

/-- Selection reads eligibility on the consultation ball, position and activation
fields on its enlarged ball, and the tie permutation at the query itself. -/
theorem selection_congr_of_ball {Sites : p.Sites} {P A P' A' : p.Loc → Bool}
    {E E' : p.EligMap} {τ τ' : p.Ties} {vq : CubeVertex p.d} {R : ℕ}
    (hE : ∀ v, hammingDist v vq ≤ R → ∀ j, E v j = E' v j)
    (hgeom : ∀ v, hammingDist v vq ≤ R → ∀ j ℓ, ℓ ∈ E v j →
      hammingDist ℓ.1 v ≤ p.r)
    (hP : ∀ ℓ : p.Loc, hammingDist ℓ.1 vq ≤ R + p.r + p.D → P ℓ = P' ℓ)
    (hA : ∀ ℓ : p.Loc, hammingDist ℓ.1 vq ≤ R + p.r + p.D → A ℓ = A' ℓ)
    (hτ : ∀ j, τ (vq, j) = τ' (vq, j)) :
    p.selectionAt Sites P A E τ R vq = p.selectionAt Sites P' A' E' τ' R vq := by
  have hbad : ∀ v, hammingDist v vq ≤ R → ∀ j,
      p.Bad P A E v j ↔ p.Bad P' A' E' v j := by
    intro v hv j
    apply bad_congr p (hE v hv j)
    · intro ℓ hℓ
      apply hA ℓ
      have ht := hammingDist_triangle ℓ.1 v vq
      have hg := hgeom v hv j ℓ hℓ
      omega
    · intro u hu
      apply hP (u, j)
      have ht := hammingDist_triangle u v vq
      dsimp only
      omega
    · intro u hu
      apply hA (u, j)
      have ht := hammingDist_triangle u v vq
      dsimp only
      omega
  apply selectionAt_congr p
  · apply height_congr p
    intro v _ hv j
    unfold HDParams.BadN
    exact exists_congr fun hj => hbad v hv ⟨j, hj⟩
  · exact hbad vq (by simp)
  · exact hE vq (by simp)
  · intro j ℓ hℓ
    apply hA ℓ
    have hg := hgeom vq (by simp) j ℓ hℓ
    omega
  · exact hτ

end Height

section Domains

variable {n m : ℕ}

/-- A fixed primitive rectangle, including all levels when lifted to IDs. -/
noncomputable def siteDomain (q : P10_1kProjectedSite n m) (S R : ℕ) :
    Finset (P10_1kProjectedSite n m) :=
  Finset.univ.filter fun u => hammingDist q.1 u.1 ≤ S ∧ hammingDist q.2 u.2 ≤ R

theorem mem_siteDomain {q u : P10_1kProjectedSite n m} {S R : ℕ} :
    u ∈ siteDomain q S R ↔ hammingDist q.1 u.1 ≤ S ∧ hammingDist q.2 u.2 ≤ R := by
  simp [siteDomain]

theorem siteDomain_mono {q : P10_1kProjectedSite n m} {S R S' R' : ℕ}
    (hS : S ≤ S') (hR : R ≤ R') : siteDomain q S R ⊆ siteDomain q S' R' := by
  intro u hu
  exact mem_siteDomain.mpr ⟨(mem_siteDomain.mp hu).1.trans hS, (mem_siteDomain.mp hu).2.trans hR⟩

theorem envelope_dist {q u : P10_1kProjectedSite n m}
    (hu : u ∈ p10_1kProjectedNeighborEnvelope q) :
    hammingDist q.1 u.1 ≤ 1 ∧ hammingDist q.2 u.2 ≤ 3 := by
  rcases Finset.mem_union.mp hu with hs | hr
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨(Finset.mem_filter.mp hz).2.le, by simp⟩
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨by simp, (Finset.mem_filter.mp hv).2⟩

theorem siteDomain_comp {q u v : P10_1kProjectedSite n m} {S R S' R' : ℕ}
    (hu : u ∈ siteDomain q S R) (hv : v ∈ siteDomain u S' R') :
    v ∈ siteDomain q (S + S') (R + R') := by
  have hu' := mem_siteDomain.mp hu
  have hv' := mem_siteDomain.mp hv
  exact mem_siteDomain.mpr
    ⟨(hammingDist_triangle q.1 u.1 v.1).trans (Nat.add_le_add hu'.1 hv'.1),
      (hammingDist_triangle q.2 u.2 v.2).trans (Nat.add_le_add hu'.2 hv'.2)⟩

theorem siteDomain_disjoint {q q' : P10_1kProjectedSite n m} {S R : ℕ}
    (hsep : ¬ (hammingDist q.1 q'.1 ≤ 2 * S ∧ hammingDist q.2 q'.2 ≤ 2 * R)) :
    Disjoint (siteDomain q S R) (siteDomain q' S R) := by
  apply Finset.disjoint_left.mpr
  intro u hu hu'
  have hq := mem_siteDomain.mp hu
  have hq' := mem_siteDomain.mp hu'
  apply hsep
  have hs := hammingDist_triangle q.1 u.1 q'.1
  have hr := hammingDist_triangle q.2 u.2 q'.2
  rw [hammingDist_comm u.1 q'.1] at hs
  rw [hammingDist_comm u.2 q'.2] at hr
  constructor <;> omega

/-- An envelope step adds at most one special bit and three residual bits. -/
theorem envelope_in_domain {q u v : P10_1kProjectedSite n m} {S R : ℕ}
    (hu : u ∈ siteDomain q S R) (hv : v ∈ p10_1kProjectedNeighborEnvelope u) :
    v ∈ siteDomain q (S + 1) (R + 3) :=
  siteDomain_comp hu (mem_siteDomain.mpr (envelope_dist hv))

/-- The primitive ID domain includes every height at each site. -/
noncomputable def idDomain (δ : ℝ) (q : P10_1kProjectedSite n m) (S R : ℕ) :
    Finset (P10_1kProspectiveId n m δ) :=
  Finset.univ.filter fun c => (c.1, c.2.1) ∈ siteDomain q S R

theorem mem_idDomain {δ : ℝ} {q : P10_1kProjectedSite n m} {S R : ℕ}
    {c : P10_1kProspectiveId n m δ} :
    c ∈ idDomain δ q S R ↔ (c.1, c.2.1) ∈ siteDomain q S R := by
  simp [idDomain]

theorem idDomain_disjoint {δ : ℝ} {q q' : P10_1kProjectedSite n m} {S R : ℕ}
    (hsep : ¬ (hammingDist q.1 q'.1 ≤ 2 * S ∧ hammingDist q.2 q'.2 ≤ 2 * R)) :
    Disjoint (idDomain δ q S R) (idDomain δ q' S R) := by
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  exact Finset.disjoint_left.mp (siteDomain_disjoint hsep)
    (mem_idDomain.mp hc) (mem_idDomain.mp hc')

theorem eligible_geometry {p : HDParams} {P : p.Loc → Bool}
    {v : CubeVertex p.d} {j : Fin (p.H + 1)} {ℓ : p.Loc}
    (hℓ : ℓ ∈ p10_1kHeightEligibleIds p P v j) :
    P ℓ = true ∧ ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ p.r := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hℓ
  exact ⟨(Finset.mem_filter.mp hu).2.1, rfl, (Finset.mem_filter.mp hu).2.2⟩

theorem eligible_congr {p : HDParams} {P P' : p.Loc → Bool}
    {v : CubeVertex p.d} {j : Fin (p.H + 1)}
    (hP : ∀ u, hammingDist u v ≤ p.r → P (u, j) = P' (u, j)) :
    p10_1kHeightEligibleIds p P v j = p10_1kHeightEligibleIds p P' v j := by
  unfold p10_1kHeightEligibleIds
  congr 1
  ext u
  by_cases hd : hammingDist u v ≤ p.r
  · simp [hd, hP u hd]
  · simp [hd]

/-- Candidate-list tests read only IDs in the radius-r envelope balls. -/
theorem candidate_domain {δ : ℝ} {q : P10_1kProjectedSite n m}
    {P : P10_1kProspectiveId n m δ → Bool} {c : P10_1kProspectiveId n m δ}
    (hc : c ∈ p10_1kGroupPositionCandidates δ q P) :
    c ∈ idDomain δ q 1 (3 + (p10_1kHeightParams n m δ).r) := by
  obtain ⟨s, hs, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨j, _, hc⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hc
  have henv := envelope_dist hs
  have hgeom := eligible_geometry hℓ
  apply mem_idDomain.mpr
  apply mem_siteDomain.mpr
  refine ⟨henv.1, ?_⟩
  have ht := hammingDist_triangle q.2 s.2 ℓ.1
  rw [hammingDist_comm s.2 ℓ.1] at ht
  exact ht.trans (Nat.add_le_add henv.2 hgeom.2.2)

theorem candidates_congr {δ : ℝ} {q : P10_1kProjectedSite n m}
    {P P' : P10_1kProspectiveId n m δ → Bool}
    (hP : ∀ c ∈ idDomain δ q 1 (3 + (p10_1kHeightParams n m δ).r), P c = P' c) :
    p10_1kGroupPositionCandidates δ q P = p10_1kGroupPositionCandidates δ q P' := by
  unfold p10_1kGroupPositionCandidates
  apply Finset.biUnion_congr rfl
  intro s hs
  apply Finset.biUnion_congr rfl
  intro j _
  congr 1
  apply eligible_congr
  intro u hu
  apply hP (s.1, (u, j))
  apply mem_idDomain.mpr
  have henv := envelope_dist hs
  apply mem_siteDomain.mpr
  refine ⟨henv.1, ?_⟩
  have ht := hammingDist_triangle q.2 s.2 u
  rw [hammingDist_comm s.2 u] at ht
  exact ht.trans (Nat.add_le_add henv.2 hu)

/-- Eligibility removes exactly IDs forbidden by envelope groups. -/
noncomputable def eligibleFromForbidden (δ : ℝ)
    (P : P10_1kProspectiveId n m δ → Bool)
    (F : P10_1kProjectedSite n m → Finset (P10_1kProspectiveId n m δ))
    (z : P10_1kSpecialSliceWord m) : (p10_1kHeightParams n m δ).EligMap :=
  fun v j => (p10_1kHeightEligibleIds (p10_1kHeightParams n m δ)
    (fun ℓ => P (z, ℓ)) v j).filter fun ℓ =>
      ∀ q : P10_1kProjectedSite n m, (z, v) ∈ p10_1kProjectedNeighborEnvelope q →
        (z, ℓ) ∉ F q

theorem eligibleFromForbidden_geometry {δ : ℝ}
    {P : P10_1kProspectiveId n m δ → Bool}
    {F : P10_1kProjectedSite n m → Finset (P10_1kProspectiveId n m δ)}
    {z : P10_1kSpecialSliceWord m} {v : CubeVertex (n - m)}
    {j : Fin ((p10_1kHeightParams n m δ).H + 1)}
    {ℓ : (p10_1kHeightParams n m δ).Loc}
    (hℓ : ℓ ∈ eligibleFromForbidden δ P F z v j) :
    hammingDist ℓ.1 v ≤ (p10_1kHeightParams n m δ).r :=
  (eligible_geometry (Finset.mem_filter.mp hℓ).1).2.2

theorem eligibleFromForbidden_congr {δ : ℝ}
    {P P' : P10_1kProspectiveId n m δ → Bool}
    {F F' : P10_1kProjectedSite n m → Finset (P10_1kProspectiveId n m δ)}
    {z : P10_1kSpecialSliceWord m} {v : CubeVertex (n - m)}
    {j : Fin ((p10_1kHeightParams n m δ).H + 1)}
    (hP : ∀ u, hammingDist u v ≤ (p10_1kHeightParams n m δ).r →
      P (z, (u, j)) = P' (z, (u, j)))
    (hF : ∀ q, (z, v) ∈ p10_1kProjectedNeighborEnvelope q → F q = F' q) :
    eligibleFromForbidden δ P F z v j = eligibleFromForbidden δ P' F' z v j := by
  have heq := eligible_congr (p := p10_1kHeightParams n m δ)
    (P := fun ℓ => P (z, ℓ)) (P' := fun ℓ => P' (z, ℓ)) (v := v) (j := j) hP
  apply Finset.ext
  intro ℓ
  constructor
  · intro hℓ
    have hmem := Finset.mem_filter.mp hℓ
    exact Finset.mem_filter.mpr ⟨heq ▸ hmem.1, fun q hq => hF q hq ▸ hmem.2 q hq⟩
  · intro hℓ
    have hmem := Finset.mem_filter.mp hℓ
    exact Finset.mem_filter.mpr ⟨heq.symm ▸ hmem.1,
      fun q hq => (hF q hq).symm ▸ hmem.2 q hq⟩

/-- A height query at s consults forbidden lists only one envelope step from
its consultation ball. This applies even when eligibility is not legal. -/
theorem projected_selection_congr {δ : ℝ}
    {P A P' A' : P10_1kProspectiveId n m δ → Bool}
    {F F' : P10_1kProjectedSite n m → Finset (P10_1kProspectiveId n m δ)}
    {τ τ' : P10_1kProspectiveId n m δ → (p10_1kHeightParams n m δ).TiePerm}
    {s : P10_1kProjectedSite n m} {Sites : (p10_1kHeightParams n m δ).Sites}
    (hP : ∀ c ∈ idDomain δ s 0 ((p10_1kHeightParams n m δ).Rlong +
      (p10_1kHeightParams n m δ).r + (p10_1kHeightParams n m δ).D), P c = P' c)
    (hA : ∀ c ∈ idDomain δ s 0 ((p10_1kHeightParams n m δ).Rlong +
      (p10_1kHeightParams n m δ).r + (p10_1kHeightParams n m δ).D), A c = A' c)
    (hF : ∀ q ∈ siteDomain s 1 ((p10_1kHeightParams n m δ).Rlong + 3), F q = F' q)
    (hτ : ∀ j, τ (s.1, (s.2, j)) = τ' (s.1, (s.2, j))) :
    (p10_1kHeightParams n m δ).selection Sites
      (fun ℓ => P (s.1, ℓ)) (fun ℓ => A (s.1, ℓ))
      (eligibleFromForbidden δ P F s.1) (fun ℓ => τ (s.1, ℓ)) s.2 =
    (p10_1kHeightParams n m δ).selection Sites
      (fun ℓ => P' (s.1, ℓ)) (fun ℓ => A' (s.1, ℓ))
      (eligibleFromForbidden δ P' F' s.1) (fun ℓ => τ' (s.1, ℓ)) s.2 := by
  let p := p10_1kHeightParams n m δ
  apply selection_congr_of_ball p
  · intro v hv j
    apply eligibleFromForbidden_congr
    · intro u hu
      apply hP (s.1, (u, j))
      apply mem_idDomain.mpr
      apply mem_siteDomain.mpr
      refine ⟨by simp, ?_⟩
      calc
        hammingDist s.2 u ≤ hammingDist s.2 v + hammingDist v u :=
          hammingDist_triangle _ _ _
        _ = hammingDist v s.2 + hammingDist u v :=
          congrArg₂ (fun a b : ℕ => a + b) (hammingDist_comm _ _) (hammingDist_comm _ _)
        _ ≤ p.Rlong + p.r := Nat.add_le_add hv hu
        _ ≤ p.Rlong + p.r + p.D := Nat.le_add_right _ _
    · intro q hq
      apply hF q
      have henv := envelope_dist ((p10_1kProjectedNeighborEnvelope_symm q (s.1, v)).mp hq)
      apply mem_siteDomain.mpr
      refine ⟨henv.1, ?_⟩
      have ht := hammingDist_triangle s.2 v q.2
      have hv' : hammingDist s.2 v ≤ p.Rlong := by
        calc
          hammingDist s.2 v = hammingDist v s.2 := hammingDist_comm _ _
          _ ≤ p.Rlong := hv
      dsimp only at henv
      exact ht.trans (Nat.add_le_add hv' henv.2)
  · intro v hv j ℓ hℓ
    exact eligibleFromForbidden_geometry hℓ
  · intro ℓ hℓ
    apply hP (s.1, ℓ)
    apply mem_idDomain.mpr
    apply mem_siteDomain.mpr
    exact ⟨by simp, by rw [hammingDist_comm]; exact hℓ⟩
  · intro ℓ hℓ
    apply hA (s.1, ℓ)
    apply mem_idDomain.mpr
    apply mem_siteDomain.mpr
    exact ⟨by simp, by rw [hammingDist_comm]; exact hℓ⟩
  · exact hτ

/-- The largest primitive radius of a star is bounded by the common Rloc.
The twelve constant steps cover two envelope moves and the overcrowding ball. -/
theorem common_radius_bound (n m : ℕ) (δ : ℝ) :
    (p10_1kHeightParams n m δ).Rlong + (p10_1kHeightParams n m δ).r + 12 ≤
      4 * (p10_1kHeightParams n m δ).r + 40 * (p10_1kHeightParams n m δ).H +
        40 * (Nat.log 2 n + 1) := by
  simp only [HDParams.Rlong, p10_1kHeightParams]
  omega

end Domains

section Packing

universe u

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    {Ω : ι → Type u} {Ω' : ι' → Type u} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Ω' i)]

noncomputable def sumFamilyFintype (i : ι ⊕ ι') : Fintype (Sum.elim Ω Ω' i) := by
  cases i <;> dsimp <;> infer_instance

attribute [local instance] sumFamilyFintype

/-- Pack two independent arrays into one array over the disjoint union of their
coordinate sets. Iteration packs the five factors of the history law. -/
theorem prod_pi_expect (P : ∀ i, FinProb (Ω i)) (Q : ∀ i, FinProb (Ω' i))
    (f : ((∀ i, Ω i) × (∀ i, Ω' i)) → ℝ) :
    (FinProb.pi (fun i => Sum.rec (motive := fun i => FinProb (Sum.elim Ω Ω' i)) P Q i)).expect
      (fun ω => f ((Equiv.prodPiEquivSumPi Ω Ω').symm ω)) =
      ((FinProb.pi P).prod (FinProb.pi Q)).expect f := by
  let e := Equiv.prodPiEquivSumPi Ω Ω'
  unfold FinProb.expect
  rw [← Equiv.sum_comp e (fun ω =>
    (FinProb.pi (fun i => Sum.rec (motive := fun i => FinProb (Sum.elim Ω Ω' i)) P Q i)).w ω *
      f (e.symm ω))]
  apply Fintype.sum_congr
  intro ab
  simp only [Equiv.symm_apply_apply]
  change (∏ i, (Sum.rec (motive := fun i => FinProb (Sum.elim Ω Ω' i)) P Q i).w (e ab i)) * f ab =
    ((∏ i, (P i).w (ab.1 i)) * ∏ i, (Q i).w (ab.2 i)) * f ab
  rw [Fintype.prod_sum_type]
  rfl

end Packing

section Histories

variable (n m k N : ℕ) (δ : ℝ)

abbrev RawHistory :=
  ((((P10_1kProspectiveId n m δ → Bool) ×
    (P10_1kProspectiveId n m δ → Fin k → Fin N)) ×
    (P10_1kProjectedSite n m → Finset (Fin N))) ×
    (P10_1kProspectiveId n m δ → Bool)) ×
    (P10_1kProspectiveId n m δ → (p10_1kHeightParams n m δ).TiePerm)

abbrev PrimitiveIndex :=
  (((P10_1kProspectiveId n m δ ⊕ P10_1kProspectiveId n m δ) ⊕
    P10_1kProjectedSite n m) ⊕ P10_1kProspectiveId n m δ) ⊕ P10_1kProspectiveId n m δ

abbrev PrimitiveField : PrimitiveIndex n m δ → Type :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim
    (fun _ => Bool) (fun _ => Fin k → Fin N))
    (fun _ => Finset (Fin N))) (fun _ => Bool))
    (fun _ => (p10_1kHeightParams n m δ).TiePerm)

noncomputable def primitiveFieldFintype (i : PrimitiveIndex n m δ) :
    Fintype (PrimitiveField n m k N δ i) := by
  rcases i with (((c | c) | s) | c) | c <;> dsimp [PrimitiveField] <;> infer_instance

noncomputable def rawHistoryFintype : Fintype (RawHistory n m k N δ) := by
  unfold RawHistory
  infer_instance

attribute [local instance] primitiveFieldFintype rawHistoryFintype

noncomputable def historyEquiv : RawHistory n m k N δ ≃
    (∀ i : PrimitiveIndex n m δ, PrimitiveField n m k N δ i) := by
  let e₁ := Equiv.prodPiEquivSumPi
    (fun _ : P10_1kProspectiveId n m δ => Bool)
    (fun _ : P10_1kProspectiveId n m δ => Fin k → Fin N)
  let F₁ := Sum.elim (fun _ : P10_1kProspectiveId n m δ => Bool)
    (fun _ : P10_1kProspectiveId n m δ => Fin k → Fin N)
  let F₂ := Sum.elim F₁ (fun _ : P10_1kProjectedSite n m => Finset (Fin N))
  let F₃ := Sum.elim F₂ (fun _ : P10_1kProspectiveId n m δ => Bool)
  let e₂ := Equiv.prodPiEquivSumPi F₁ (fun _ : P10_1kProjectedSite n m => Finset (Fin N))
  let e₃ := Equiv.prodPiEquivSumPi F₂ (fun _ : P10_1kProspectiveId n m δ => Bool)
  let e₄ := Equiv.prodPiEquivSumPi F₃
    (fun _ : P10_1kProspectiveId n m δ => (p10_1kHeightParams n m δ).TiePerm)
  exact ((((e₁.prodCongr (Equiv.refl _)).trans e₂).prodCongr
    (Equiv.refl _)).trans e₃).prodCongr (Equiv.refl _) |>.trans e₄

def primitiveSite : PrimitiveIndex n m δ → P10_1kProjectedSite n m
  | .inl (.inl (.inl (.inl c))) => (c.1, c.2.1)
  | .inl (.inl (.inl (.inr c))) => (c.1, c.2.1)
  | .inl (.inl (.inr q)) => q
  | .inl (.inr c) => (c.1, c.2.1)
  | .inr c => (c.1, c.2.1)

noncomputable def primitiveDomain (q : P10_1kProjectedSite n m) (S R : ℕ) :
    Finset (PrimitiveIndex n m δ) :=
  Finset.univ.filter fun i => primitiveSite n m δ i ∈ siteDomain q S R

theorem primitiveDomain_disjoint {q q' : P10_1kProjectedSite n m} {S R : ℕ}
    (hsep : ¬ (hammingDist q.1 q'.1 ≤ 2 * S ∧ hammingDist q.2 q'.2 ≤ 2 * R)) :
    Disjoint (primitiveDomain n m δ q S R) (primitiveDomain n m δ q' S R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  exact Finset.disjoint_left.mp (siteDomain_disjoint hsep)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2

theorem historyEquiv_agree {q : P10_1kProjectedSite n m} {S R : ℕ}
    {h h' : RawHistory n m k N δ} :
    (∀ i ∈ primitiveDomain n m δ q S R,
      historyEquiv n m k N δ h i = historyEquiv n m k N δ h' i) ↔
    (∀ c ∈ idDomain δ q S R, h.1.1.1.1 c = h'.1.1.1.1 c) ∧
    (∀ c ∈ idDomain δ q S R, h.1.1.1.2 c = h'.1.1.1.2 c) ∧
    (∀ s ∈ siteDomain q S R, h.1.1.2 s = h'.1.1.2 s) ∧
    (∀ c ∈ idDomain δ q S R, h.1.2 c = h'.1.2 c) ∧
    (∀ c ∈ idDomain δ q S R, h.2 c = h'.2 c) := by
  constructor
  · intro H
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      apply H (.inl (.inl (.inl (.inl c))))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_idDomain.mp hc⟩
    · intro c hc
      apply H (.inl (.inl (.inl (.inr c))))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_idDomain.mp hc⟩
    · intro s hs
      apply H (.inl (.inl (.inr s)))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    · intro c hc
      apply H (.inl (.inr c))
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_idDomain.mp hc⟩
    · intro c hc
      apply H (.inr c)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_idDomain.mp hc⟩
  · rintro ⟨hP, hW, hS, hA, hτ⟩ i hi
    have hi' := (Finset.mem_filter.mp hi).2
    rcases i with (((c | c) | s) | c) | c
    · exact hP c (mem_idDomain.mpr hi')
    · exact hW c (mem_idDomain.mpr hi')
    · exact hS s hi'
    · exact hA c (mem_idDomain.mpr hi')
    · exact hτ c (mem_idDomain.mpr hi')

variable {n m k N δ}
    (P : P10_1kProspectiveId n m δ → FinProb Bool)
    (W : P10_1kProspectiveId n m δ → FinProb (Fin k → Fin N))
    (S : P10_1kProjectedSite n m → FinProb (Finset (Fin N)))
    (A : P10_1kProspectiveId n m δ → FinProb Bool)
    (τ : P10_1kProspectiveId n m δ → FinProb (p10_1kHeightParams n m δ).TiePerm)

noncomputable def packedLaw : FinProb (∀ i, PrimitiveField n m k N δ i) :=
  FinProb.pi (Ω := PrimitiveField n m k N δ) fun i : PrimitiveIndex n m δ => match i with
    | .inl (.inl (.inl (.inl c))) => P c
    | .inl (.inl (.inl (.inr c))) => W c
    | .inl (.inl (.inr q)) => S q
    | .inl (.inr c) => A c
    | .inr c => τ c

noncomputable def rawLaw : FinProb (RawHistory n m k N δ) :=
  ((((FinProb.pi P).prod (FinProb.pi W)).prod (FinProb.pi S)).prod (FinProb.pi A)).prod
    (FinProb.pi τ)

theorem packedLaw_weight (ω : ∀ i, PrimitiveField n m k N δ i) :
    (packedLaw P W S A τ).w ω =
      (rawLaw P W S A τ).w ((historyEquiv n m k N δ).symm ω) := by
  simp only [packedLaw, FinProb.pi, Fintype.prod_sum_type, rawLaw, FinProb.prod]
  rfl

theorem history_expect (f : RawHistory n m k N δ → ℝ) :
    (packedLaw P W S A τ).expect
      (fun ω => f ((historyEquiv n m k N δ).symm ω)) = (rawLaw P W S A τ).expect f := by
  let e := historyEquiv n m k N δ
  unfold FinProb.expect
  rw [← Equiv.sum_comp e (fun ω => (packedLaw P W S A τ).w ω * f (e.symm ω))]
  apply Fintype.sum_congr
  intro h
  rw [packedLaw_weight]
  simp only [e, Equiv.symm_apply_apply]

end Histories

section Products

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

theorem dependsOn_prod (s : Finset α) (f : α → (∀ i, Ω i) → ℝ) (D : α → Finset ι)
    (hf : ∀ a ∈ s, FinProb.DependsOn (f a) (D a)) :
    FinProb.DependsOn (fun ω => ∏ a ∈ s, f a ω) (s.biUnion D) := by
  intro ω ω' hω
  apply Finset.prod_congr rfl
  intro a ha
  exact hf a ha ω ω' fun i hi => hω i (Finset.mem_biUnion.mpr ⟨a, ha, hi⟩)

/-- Any finite family of calculations on disjoint primitive coordinates factors. -/
theorem pi_expect_prod (P : ∀ i, FinProb (Ω i)) (s : Finset α)
    (f : α → (∀ i, Ω i) → ℝ) (D : α → Finset ι)
    (hf : ∀ a, FinProb.DependsOn (f a) (D a))
    (hdis : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (D a) (D b)) :
    (FinProb.pi P).expect (fun ω => ∏ a ∈ s, f a ω) =
      ∏ a ∈ s, (FinProb.pi P).expect (f a) := by
  revert hdis
  induction s using Finset.induction_on with
  | empty => intro _; simp [FinProb.expect_const]
  | @insert a s ha ih =>
    intro hdis
    have hdisS : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (D a) (D b) := by
      intro a ha b hb hab
      exact hdis a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hdisA : Disjoint (D a) (s.biUnion D) := by
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      obtain ⟨b, hb, hib⟩ := Finset.mem_biUnion.mp hi'
      exact Finset.disjoint_left.mp
        (hdis a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)
          (fun hab => ha (hab.symm ▸ hb))) hi hib
    simp only [Finset.prod_insert ha]
    rw [FinProb.pi_expect_mul_of_disjoint P (f a) (fun ω => ∏ b ∈ s, f b ω)
      (D a) (s.biUnion D) (hf a)
      (dependsOn_prod s f D (fun b _ => hf b)) hdisA, ih hdisS]

theorem expect_gate_prod_le {β : Type*} [Fintype β] (P : FinProb β)
    (s : Finset α) (f : α → β → ℝ) (V : β → Prop)
    (hf : ∀ a ∈ s, ∀ ω, 0 ≤ f a ω) :
    P.expect (fun ω => if V ω then ∏ a ∈ s, f a ω else 0) ≤
      P.expect (fun ω => ∏ a ∈ s, f a ω) := by
  apply P.expect_mono
  intro ω
  split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg fun a ha => hf a ha ω

/-- Coordinates outside the read domain may have different laws. -/
theorem pi_expect_congr_on (P Q : ∀ i, FinProb (Ω i)) (D : Finset ι)
    (f : (∀ i, Ω i) → ℝ) (ω₀ : ∀ i, Ω i)
    (hf : FinProb.DependsOn f D) (hPQ : ∀ i ∈ D, P i = Q i) :
    (FinProb.pi P).expect f = (FinProb.pi Q).expect f := by
  rw [FinProb.pi_expect_depends P D f ω₀ hf, FinProb.pi_expect_depends Q D f ω₀ hf]
  have heq : (fun i : {i // i ∈ D} => P i.1) = (fun i : {i // i ∈ D} => Q i.1) :=
    funext fun i => hPQ i.1 i.2
  rw [heq]

/-- Candidate replacement preserves agreement on a fixed primitive domain. -/
theorem update_agree_on {β : Type*} (D : Finset ι) {u v : ι → β}
    (huv : ∀ i ∈ D, u i = v i) (c : ι) (w : β) :
    ∀ i ∈ D, Function.update u c w i = Function.update v c w i := by
  intro i hi
  by_cases hic : i = c
  · subst i; simp
  · simp [Function.update_of_ne hic, huv i hi]

end Products

end HypercubeRamsey.Lane_sol_s10_d8
