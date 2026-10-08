import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d56_rows
import HypercubeRamsey.S10.ClusterExclusion_p_s10_1k

namespace HypercubeRamsey.Lane_sol_s10_d56

open Classical HypercubeRamsey.S10
open scoped BigOperators

/-- A prescribed list is ordered into its own names followed by one name per external tag. -/
theorem namedList_order_equiv {Z I : Type*} [DecidableEq Z] [DecidableEq I] {m : ℕ}
    (z : Z) (tags : Fin m → Z) (htag : Function.Injective tags)
    (hne : ∀ i, tags i ≠ z) (L : Finset (Z × I))
    (hcover : ∀ c ∈ L, c.1 = z ∨ ∃ i, c.1 = tags i)
    (hexternal : ∀ i, (L.filter fun c => c.1 = tags i).card = 1) :
    let s := (L.filter fun c => c.1 = z).card
    ∃ e : Fin (s + m) ≃ {c // c ∈ L},
      ∀ b, (e b).1.1 = Fin.addCases (fun _ : Fin s => z) tags b := by
  classical
  dsimp only
  let O := L.filter fun c => c.1 = z
  let s := O.card
  have hex (i : Fin m) : ∃ c, c ∈ L ∧ c.1 = tags i ∧
      ∀ c' ∈ L, c'.1 = tags i → c' = c := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hexternal i)
    have hm : c ∈ L.filter (fun c => c.1 = tags i) := by rw [hc]; simp
    exact ⟨c, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2,
      fun c' hc' ht => by
        have hm' : c' ∈ L.filter (fun c => c.1 = tags i) := Finset.mem_filter.mpr ⟨hc', ht⟩
        rw [hc] at hm'
        exact Finset.mem_singleton.mp hm'⟩
  choose ext hextMem hextTag hextUnique using hex
  let f : Fin (s + m) → {c // c ∈ L} := Fin.addCases
    (fun j : Fin s => ⟨(O.equivFin.symm j).1, (Finset.mem_filter.mp (O.equivFin.symm j).2).1⟩)
    (fun j : Fin m => ⟨ext j, hextMem j⟩)
  have hprofile (b : Fin (s + m)) : (f b).1.1 = Fin.addCases (fun _ : Fin s => z) tags b := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) b
    · simpa [f] using (Finset.mem_filter.mp (O.equivFin.symm j).2).2
    · simpa [f] using hextTag j
  have hinj : Function.Injective f := by
    intro b
    refine Fin.addCases (fun i => ?_) (fun i => ?_) b
    · intro b'
      refine Fin.addCases (fun j => ?_) (fun j => ?_) b'
      · intro hij
        have ho : O.equivFin.symm i = O.equivFin.symm j :=
          Subtype.ext (by simpa [f] using congrArg Subtype.val hij)
        exact congrArg (Fin.castAdd m) (O.equivFin.symm.injective ho)
      · intro hij
        have ht := congrArg (fun c : {c // c ∈ L} => c.1.1) hij
        rw [hprofile, hprofile] at ht
        simp only [Fin.addCases_left, Fin.addCases_right] at ht
        exact False.elim (hne j ht.symm)
    · intro b'
      refine Fin.addCases (fun j => ?_) (fun j => ?_) b'
      · intro hij
        have ht := congrArg (fun c : {c // c ∈ L} => c.1.1) hij
        rw [hprofile, hprofile] at ht
        simp only [Fin.addCases_left, Fin.addCases_right] at ht
        exact False.elim (hne i ht)
      · intro hij
        have ht := congrArg (fun c : {c // c ∈ L} => c.1.1) hij
        rw [hprofile, hprofile] at ht
        simp only [Fin.addCases_left, Fin.addCases_right] at ht
        exact congrArg (Fin.natAdd s) (htag ht)
  have hsurj : Function.Surjective f := by
    intro c
    by_cases hc : c.1.1 = z
    · have hO : c.1 ∈ O := Finset.mem_filter.mpr ⟨c.2, hc⟩
      let j : Fin s := O.equivFin ⟨c.1, hO⟩
      refine ⟨Fin.castAdd m j, ?_⟩
      apply Subtype.ext
      simp [f, j]
    · obtain ⟨i, hi⟩ := (hcover c.1 c.2).resolve_left hc
      refine ⟨Fin.natAdd s i, ?_⟩
      apply Subtype.ext
      simpa [f] using (hextUnique i c.1 c.2 hi).symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hprofile⟩

/-- The Boolean words in distinct coordinate directions are distinct external tags. -/
theorem flipCoordinate_injective {m : ℕ} (z : Fin m → Bool) :
    Function.Injective (p10_1kFlipCoordinate z) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij i
  have hne' : i ≠ j := hne
  simp [p10_1kFlipCoordinate, hne'] at h

/-- Every external coordinate flip differs from its own slice. -/
theorem flipCoordinate_ne_self {m : ℕ} (z : Fin m → Bool) (i : Fin m) :
    p10_1kFlipCoordinate z i ≠ z := by
  intro h
  have hi := congrFun h i
  simp [p10_1kFlipCoordinate] at hi

/-- Hamming distance one identifies the unique coordinate direction of an external tag. -/
theorem flipCoordinate_of_hammingDist_one {m : ℕ} (s t : Fin m → Bool)
    (h : _root_.hammingDist s t = 1) : ∃ j : Fin m, t = p10_1kFlipCoordinate s j := by
  classical
  have hcard : (Finset.univ.filter fun i : Fin m => s i ≠ t i).card = 1 := by
    simpa [_root_.hammingDist] using h
  obtain ⟨j, hfilter⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  funext k
  have hk : s k ≠ t k ↔ k = j := by
    have hmem : k ∈ Finset.univ.filter (fun i : Fin m => s i ≠ t i) ↔ k = j := by
      rw [hfilter]
      simp
    simpa using hmem
  by_cases hkj : k = j
  · subst k
    have hne : s j ≠ t j := hk.mpr rfl
    cases hs : s j <;> cases ht : t j <;> simp_all [p10_1kFlipCoordinate]
  · have heq : s k = t k := by
      by_contra hne
      exact hkj (hk.mp hne)
    simp [p10_1kFlipCoordinate, hkj, heq]

end HypercubeRamsey.Lane_sol_s10_d56
