import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10
open scoped BigOperators

/-- Names in the balls of a specified finite site set. -/
noncomputable def positionCandidates (p : HDParams) {Z : Type*} [DecidableEq Z]
    (B : Finset (Z × CubeVertex p.d)) (P : Z × p.Loc → Bool) : Finset (Z × p.Loc) :=
  B.biUnion fun s => (Finset.univ : Finset (Fin (p.H + 1))).biUnion fun j =>
    (p10_1kHeightEligibleIds p (fun loc => P (s.1, loc)) s.2 j).image (fun loc => (s.1, loc))

/-- Position-count gates bound the total candidate count, even with overlapping balls. -/
theorem positionCandidates_card_le (p : HDParams) {Z : Type*} [DecidableEq Z]
    (B : Finset (Z × CubeVertex p.d)) (P : Z × p.Loc → Bool)
    (hpos : ∀ s ∈ B, ∀ j, (p10_1kHeightPositionCount p (fun loc => P (s.1, loc)) s.2 j : ℝ)
      ≤ 2 * p.lam) :
    ((positionCandidates p B P).card : ℝ) ≤ (B.card : ℝ) * (p.H + 1 : ℕ) * (2 * p.lam) := by
  classical
  let ids := fun (s : Z × CubeVertex p.d) (j : Fin (p.H + 1)) =>
    p10_1kHeightEligibleIds p (fun loc => P (s.1, loc)) s.2 j
  have hn : (positionCandidates p B P).card ≤ ∑ s ∈ B, ∑ j : Fin (p.H + 1), (ids s j).card := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro s hs
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun j hj => Finset.card_image_le
  have hr : ((positionCandidates p B P).card : ℝ) ≤
      ∑ s ∈ B, ∑ j : Fin (p.H + 1), ((ids s j).card : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ ∑ s ∈ B, ∑ j : Fin (p.H + 1), ((ids s j).card : ℝ) := hr
    _ ≤ ∑ s ∈ B, ∑ _j : Fin (p.H + 1), (2 * p.lam) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro j hj
      change ((p10_1kHeightEligibleIds p (fun loc => P (s.1, loc)) s.2 j).card : ℝ) ≤ _
      rw [p10_1kHeightEligibleIds_card]
      exact hpos s hs j
    _ = _ := by simp; ring

/-- Bounded-size subsets of a candidate set have the padded-tuple cardinal bound. -/
theorem candidateSubsets_card_le {I : Type*} [Fintype I] [DecidableEq I]
    (C : Finset I) (r : ℕ) :
    ((C.powerset).filter fun O => O.card ≤ r).card ≤ (C.card + 1) ^ r := by
  classical
  let F := C.powerset.filter fun O => O.card ≤ r
  let T := (Finset.univ : Finset (Finset {i // i ∈ C})).filter fun O => O.card ≤ r
  have hsub (O : {O // O ∈ F}) : ∀ c ∈ O.1, c ∈ C :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp O.2).1
  have hmap (O : {O // O ∈ F}) :
      (O.1.subtype (fun i => i ∈ C)).map (Function.Embedding.subtype _) = O.1 :=
    Finset.subtype_map_of_mem (hsub O)
  have hcard (O : {O // O ∈ F}) : (O.1.subtype (fun i => i ∈ C)).card = O.1.card := by
    calc
      _ = ((O.1.subtype (fun i => i ∈ C)).map (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
      _ = O.1.card := congrArg Finset.card (hmap O)
  let f : {O // O ∈ F} → {O // O ∈ T} := fun O =>
    ⟨O.1.subtype (fun i => i ∈ C), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by rw [hcard]; exact (Finset.mem_filter.mp O.2).2⟩⟩
  have hinj : Function.Injective f := by
    intro O Q heq
    apply Subtype.ext
    have heq' : O.1.subtype (fun i => i ∈ C) = Q.1.subtype (fun i => i ∈ C) := congrArg Subtype.val heq
    calc
      O.1 = (O.1.subtype (fun i => i ∈ C)).map (Function.Embedding.subtype _) := (hmap O).symm
      _ = (Q.1.subtype (fun i => i ∈ C)).map (Function.Embedding.subtype _) := congrArg _ heq'
      _ = Q.1 := hmap Q
  calc
    F.card = Fintype.card {O // O ∈ F} := by simp
    _ ≤ Fintype.card {O // O ∈ T} := Fintype.card_le_of_injective f hinj
    _ = T.card := by simp
    _ ≤ (C.card + 1) ^ r := p10_1kCandidateListFamily_card_le C r

end HypercubeRamsey.Lane_sol_s10_d56
