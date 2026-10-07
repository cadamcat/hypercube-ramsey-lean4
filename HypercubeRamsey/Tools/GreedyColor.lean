import Mathlib

/-!
# Greedy colouring of finite graphs

X-GreedyColour: the standard finite greedy argument uses at most `Δ` previously coloured neighbours at each
vertex, so one of `Δ+1` colours is available.
-/

namespace HypercubeRamsey

/-- X-GreedyColour: a finite graph of maximum degree at most `Δ` has a proper colouring with `Δ+1` colours. -/
theorem xGreedyColour {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter (fun u => G.Adj v u)).card ≤ Δ) :
    ∃ colour : V → Fin (Δ + 1),
      ∀ u v, G.Adj u v → colour u ≠ colour v := by
  classical
  let P : Finset V → Prop := fun s =>
    ∃ f : V → Fin (Δ + 1),
      ∀ ⦃u v⦄, u ∈ s → v ∈ s → G.Adj u v → f u ≠ f v
  have hP : ∀ s : Finset V, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨fun _ => 0, by simp [P]⟩
    | @insert a s has ih =>
        obtain ⟨f, hf⟩ := ih
        let N := Finset.univ.filter (fun u : V => G.Adj a u)
        let bad := N.image f
        have hN : N.card ≤ Δ := by
          simpa [N] using hdegree a
        have hbad : bad.card ≤ Δ := le_trans (Finset.card_image_le) hN
        have hlt : bad.card < (Finset.univ : Finset (Fin (Δ + 1))).card := by
          simp
          omega
        obtain ⟨c, hcuniv, hcbad⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hlt
        let g : V → Fin (Δ + 1) := fun x => if x = a then c else f x
        refine ⟨g, ?_⟩
        intro u v hu hv huv
        by_cases huEq : u = a
        · subst u
          by_cases hvEq : v = a
          · subst v
            exact (G.ne_of_adj huv rfl).elim
          · have hvS : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hvEq
            have hmem : v ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
            have hbadmem : f v ∈ bad := Finset.mem_image.mpr ⟨v, hmem, rfl⟩
            have hcf : c ≠ f v := by
              intro heq
              exact hcbad (heq.symm ▸ hbadmem)
            simpa [g, hvEq] using hcf
        · by_cases hvEq : v = a
          · subst v
            have huS : u ∈ s := (Finset.mem_insert.mp hu).resolve_left huEq
            have hmem : u ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.symm⟩
            have hbadmem : f u ∈ bad := Finset.mem_image.mpr ⟨u, hmem, rfl⟩
            have hcf : c ≠ f u := by
              intro heq
              exact hcbad (heq.symm ▸ hbadmem)
            simpa [g, huEq] using hcf.symm
          · have huS : u ∈ s := (Finset.mem_insert.mp hu).resolve_left huEq
            have hvS : v ∈ s := (Finset.mem_insert.mp hv).resolve_left hvEq
            simpa [g, huEq, hvEq] using hf huS hvS huv
  obtain ⟨f, hf⟩ := hP Finset.univ
  exact ⟨f, fun u v huv => hf (Finset.mem_univ _) (Finset.mem_univ _) huv⟩

end HypercubeRamsey
