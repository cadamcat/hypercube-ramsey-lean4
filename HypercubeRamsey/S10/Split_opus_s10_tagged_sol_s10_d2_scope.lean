import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_canonical

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Restrict a selector to its queried sites. -/
noncomputable def restrictSelector {n m : ℕ} (δ : ℝ)
    (Sites : (Fin m → Bool) → (p10_1kHeightParams n m δ).Sites)
    (sel : P10_1kProjectedSite n m → Option (p10_1kHeightParams n m δ).Loc)
    (s : P10_1kProjectedSite n m) : Option (p10_1kHeightParams n m δ).Loc :=
  if s.2 ∈ Sites s.1 then sel s else none

/-- Filtering queried sites is equivalent to restricting the selector. -/
theorem filtered_scope_eq {n m : ℕ} (δ : ℝ)
    (Sites : (Fin m → Bool) → (p10_1kHeightParams n m δ).Sites)
    (sel : P10_1kProjectedSite n m → Option (p10_1kHeightParams n m δ).Loc)
    (q : P10_1kProjectedSite n m) :
    ((p10_1kProjectedNeighborEnvelope q).filter fun s => s.2 ∈ Sites s.1).biUnion
      (fun s => (sel s).elim ∅ (fun loc => {(s.1, loc)})) =
      p10_1kOddGroupTupleIdScope δ q (restrictSelector δ Sites sel) := by
  classical
  ext id
  simp only [p10_1kOddGroupTupleIdScope, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨s, ⟨hs, hQ⟩, hi⟩
    refine ⟨s, hs, ?_⟩
    have he : restrictSelector δ Sites sel s = sel s := by
      unfold restrictSelector
      exact if_pos hQ
    rw [he]
    exact hi
  · rintro ⟨s, hs, hi⟩
    by_cases hQ : s.2 ∈ Sites s.1
    · exact ⟨s, ⟨hs, hQ⟩, by simpa [restrictSelector, hQ] using hi⟩
    · simp [restrictSelector, hQ] at hi

/-- A selected external site supplies exactly one ID in its special slice. -/
theorem external_scope_singleton {n m : ℕ} (δ : ℝ)
    (q : P10_1kProjectedSite n m)
    (sel : P10_1kProjectedSite n m → Option (p10_1kHeightParams n m δ).Loc)
    (z : Fin m → Bool) (hd : _root_.hammingDist z q.1 = 1)
    (loc : (p10_1kHeightParams n m δ).Loc) (hsel : sel (z, q.2) = some loc) :
    (p10_1kOddGroupTupleIdScope δ q sel).filter (fun id => id.1 = z) = {(z, loc)} := by
  classical
  have hne : z ≠ q.1 := by
    intro he
    subst z
    simp at hd
  ext id
  constructor
  · intro h
    obtain ⟨hi, hz⟩ := Finset.mem_filter.mp h
    obtain ⟨s, hs, hid⟩ := Finset.mem_biUnion.mp hi
    cases hσ : sel s with
    | none => simp [hσ] at hid
    | some loc' =>
      have he : id = (s.1, loc') := by simpa [hσ] using hid
      have hsZ : s.1 = z := (congrArg Prod.fst he).symm.trans hz
      have hsR : s.2 = q.2 := by
        rcases Finset.mem_union.mp hs with ha | hb
        · obtain ⟨z', _, he'⟩ := Finset.mem_image.mp ha
          exact (congrArg Prod.snd he').symm
        · obtain ⟨v, _, he'⟩ := Finset.mem_image.mp hb
          have heZ := congrArg Prod.fst he'
          exact (hne (hsZ.symm.trans heZ.symm)).elim
      have hsEq : s = (z, q.2) := Prod.ext hsZ hsR
      rw [hsEq, hsel] at hσ
      have hl : loc' = loc := (Option.some.inj hσ).symm
      simp only [Finset.mem_singleton]
      rw [he, hsZ, hl]
  · intro h
    obtain rfl := Finset.mem_singleton.mp h
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨(z, q.2), ?_, ?_⟩
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      simpa [hammingDist_comm] using hd
    · simp [hsel]

end HypercubeRamsey.Lane_sol_s10_d2
