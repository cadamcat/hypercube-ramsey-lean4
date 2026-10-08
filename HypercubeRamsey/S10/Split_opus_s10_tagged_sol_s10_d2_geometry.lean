import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_fan

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

private theorem p10_1k_flipCoordinate_of_hammingDist_one {d : ℕ}
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


/-- At most `T` own IDs and at most one ID per adjacent slice give `T+m` IDs. -/
theorem prescribed_list_card_le {I : Type*} [DecidableEq I] {m T : ℕ}
    (L : Finset I) (tag : I → CubeVertex m) (z : CubeVertex m)
    (hown : (L.filter fun i => tag i = z).card ≤ T)
    (hform : ∀ i ∈ L, tag i = z ∨ _root_.hammingDist (tag i) z = 1)
    (hone : ∀ z', _root_.hammingDist z' z = 1 → (L.filter fun i => tag i = z').card ≤ 1) :
    L.card ≤ T + m := by
  classical
  let own := L.filter fun i => tag i = z
  let ext := L.filter fun i => tag i ≠ z
  let neighbors : Finset (CubeVertex m) := Finset.univ.image (p10_1kFlipCoordinate z)
  have hmap : ∀ i ∈ ext, tag i ∈ neighbors := by
    intro i hi
    obtain ⟨hiL, hiN⟩ := Finset.mem_filter.mp hi
    have hd : _root_.hammingDist (tag i) z = 1 := (hform i hiL).resolve_left hiN
    have hcomm : _root_.hammingDist z (tag i) = 1 := by
      simpa [_root_.hammingDist, ne_comm] using hd
    obtain ⟨e, he⟩ := p10_1k_flipCoordinate_of_hammingDist_one z (tag i) hcomm
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he.symm⟩
  have hinj : (ext : Set I).InjOn tag := by
    intro i hi j hj he
    obtain ⟨hiL, hiN⟩ := Finset.mem_filter.mp hi
    have hd : _root_.hammingDist (tag i) z = 1 := (hform i hiL).resolve_left hiN
    have hcard := hone (tag i) hd
    apply Finset.card_le_one.mp hcard
    · exact Finset.mem_filter.mpr ⟨hiL, rfl⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, he.symm⟩
  have hext : ext.card ≤ m := by
    calc
      ext.card ≤ neighbors.card := Finset.card_le_card_of_injOn tag hmap hinj
      _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
      _ = m := by simp
  have hpart : L.card = own.card + ext.card := by
    dsimp [own, ext]
    exact (Finset.card_filter_add_card_filter_not (s := L) (p := fun i => tag i = z)).symm
  rw [hpart]
  exact Nat.add_le_add hown hext

/-- Good heights return an active center at every queried site. -/
theorem selection_isSome_of_good (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (hgood : p.GoodHeights Sites P A E) (v : CubeVertex p.d) (hv : v ∈ Sites) :
    (p.selection Sites P A E τ v).isSome := by
  classical
  let h := p.height Sites P A E p.Rlong v
  have hh : h < p.H := (hgood v hv).1
  let j : Fin (p.H + 1) := ⟨h, by omega⟩
  have hnot : ¬ p.Bad P A E v j := by
    intro hb
    exact (hgood v hv).2.1 ⟨by omega, hb⟩
  let active := (E v j).filter fun l => A l = true
  have hactive : active.Nonempty := by
    by_contra hn
    have hf : ∀ l ∈ E v j, A l = false := by
      intro l hl
      cases ha : A l
      · rfl
      · exact (hn ⟨l, Finset.mem_filter.mpr ⟨hl, ha⟩⟩).elim
    exact hnot (Or.inl hf)
  have hprior : (active.image (fun l => p.priority τ (v, j) l)).Nonempty :=
    hactive.image _
  have hh' : p.height Sites P A E p.Rlong v < p.H := hh
  have hnot' : ¬ p.Bad P A E v ⟨p.height Sites P A E p.Rlong v, by omega⟩ := hnot
  simp [HDParams.selection, HDParams.selectionAt, hh', hnot', hprior, active, j, h]

end HypercubeRamsey.Lane_sol_s10_d2
