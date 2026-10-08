import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_geometry

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

theorem even_flip {n : ℕ}
    {u v : Fin n → Bool} (h : _root_.hammingDist u v = 1) :
    IsEvenRole u ↔ ¬ IsEvenRole v := by
  classical
  have hone : (Finset.univ.filter fun i : Fin n => u i ≠ v i).card = 1 := by
    simpa [_root_.hammingDist] using h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin n => u j ≠ v j) := by
    rw [hi]
    simp
  have hdiff : u i ≠ v i := (Finset.mem_filter.mp hi_mem).2
  have hsame : ∀ j, j ≠ i → u j = v j := by
    intro j hji
    by_contra hne
    have hj_mem : j ∈ Finset.univ.filter (fun t : Fin n => u t ≠ v t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hi] at hj_mem
    exact hji (Finset.mem_singleton.mp hj_mem)
  let A := Finset.univ.filter (fun j : Fin n => u j = true)
  let B := Finset.univ.filter (fun j : Fin n => v j = true)
  have hbit : (u i = false ∧ v i = true) ∨ (u i = true ∧ v i = false) := by
    cases hu : u i <;> cases hv : v i <;> simp_all
  rcases hbit with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hset : B = insert i A := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, hu, hv]
      · have hsame' := hsame j hji
        simp [A, B, hji, hsame']
    have hi_notA : i ∉ A := by simp [A, hu]
    have hcard : B.card = A.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notA]
    change Even A.card ↔ ¬ Even B.card
    rw [hcard]
    simp only [Nat.even_add_one, not_not]
  · have hset : A = insert i B := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [A, B, hu, hv]
      · have hsame' := hsame j hji
        simp [A, B, hji, hsame']
    have hi_notB : i ∉ B := by simp [B, hv]
    have hcard : A.card = B.card + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi_notB]
    change Even A.card ↔ ¬ Even B.card
    rw [hcard]
    exact Nat.even_add_one

private theorem word_flip {d : ℕ}
    (s t : Fin d → Bool) (h : _root_.hammingDist s t = 1) :
    ∃ j : Fin d, t = p10_1kFlipCoordinate s j := by
  classical
  have hcard : (Finset.univ.filter (fun i : Fin d => s i ≠ t i)).card = 1 := by
    simpa [_root_.hammingDist] using h
  obtain ⟨j, hfilter⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  funext k
  have hk : s k ≠ t k ↔ k = j := by
    have hmem : k ∈ Finset.univ.filter (fun i : Fin d => s i ≠ t i) ↔ k = j := by
      rw [hfilter]
      simp
    simpa using hmem
  by_cases hkj : k = j
  · subst k
    have hne : s j ≠ t j := hk.2 rfl
    cases hs : s j <;> cases ht : t j <;> simp_all [p10_1kFlipCoordinate]
  · have heq : s k = t k := by
      by_contra hne
      exact hkj (hk.1 hne)
    simp [p10_1kFlipCoordinate, hkj, heq]

/-- Every adjacent special slice supplies the external even site of an odd group. -/
theorem external_site_mem {n m : ℕ} (hm : m ≤ n) (q : P10_1kProjectedSite n m)
    (hq : (p10_1kOddGroupRoles hm q).Nonempty)
    (z : Fin m → Bool) (hd : _root_.hammingDist z q.1 = 1) :
    q.2 ∈ p10_1kProjectedEvenSites hm z := by
  classical
  obtain ⟨b, hb⟩ := hq
  have heq : p10_1kProjectedVertex hm b.1 = q := (Finset.mem_filter.mp hb).2
  have hs₀ := congrArg (fun s : P10_1kProjectedSite n m => s.1) heq
  have hr₀ := congrArg (fun s : P10_1kProjectedSite n m => s.2) heq
  have hs : p10_1kSpecialSlice hm b.1 = q.1 := hs₀
  have hr : p10_1k_projectedWord (n - m) (p10_1kResidualWord hm b.1) = q.2 := hr₀
  have hd' : _root_.hammingDist (p10_1kSpecialSlice hm b.1) z = 1 := by
    rw [hs]
    simpa [hammingDist_comm] using hd
  obtain ⟨e, he⟩ := word_flip (p10_1kSpecialSlice hm b.1) z hd'
  let v := p10_1kSpecialFlipVertex hm b.1 e
  have hadj : _root_.hammingDist v b.1 = 1 := by
    have ha := p10_1kSpecialFlipVertex_adjacent hm b.1 e
    change _root_.hammingDist b.1 (p10_1kSpecialFlipVertex hm b.1 e) = 1 at ha
    simpa [v, hammingDist_comm] using ha
  let a : P10_1kEvenRole n := ⟨v, (even_flip hadj).mpr b.2⟩
  have has : p10_1kSpecialSlice hm a.1 = z := by
    change p10_1kSpecialSlice hm (p10_1kSpecialFlipVertex hm b.1 e) = z
    rw [p10_1kSpecialFlipVertex_specialSlice, ← he]
  have har : p10_1k_projectedWord (n - m) (p10_1kResidualWord hm a.1) = q.2 := by
    change p10_1k_projectedWord (n - m)
      (p10_1kResidualWord hm (p10_1kSpecialFlipVertex hm b.1 e)) = q.2
    rw [p10_1kSpecialFlipVertex_residualWord]
    exact hr
  have hsite := p10_1kProjectedEvenRole_mem_sites hm a
  rwa [has, har] at hsite

end HypercubeRamsey.Lane_sol_s10_d2
