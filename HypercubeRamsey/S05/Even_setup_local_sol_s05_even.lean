import HypercubeRamsey.S05.Even_setup_geometry_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

theorem reach_in_domain (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap)
    (v : CubeVertex p.d) (R : ℕ) (u : CubeVertex p.d) (j : ℕ)
    (h : p.Reach Sites P A E v R u j) : u ∈ p.domBall Sites v R := by
  induction h with
  | start u hu hd => exact Finset.mem_filter.mpr ⟨hu, hd⟩
  | up u j hj h hbad ih => exact ih
  | down u u' j h hu hd hstep ih => exact Finset.mem_filter.mpr ⟨hu, hd⟩

theorem reach_of_bad_agree (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (v : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ u ∈ p.domBall Sites v R, ∀ j, p.BadN P A E u j ↔ p.BadN P' A' E' u j)
    (u : CubeVertex p.d) (j : ℕ) (h : p.Reach Sites P A E v R u j) :
    p.Reach Sites P' A' E' v R u j := by
  induction h with
  | start u hu hd => exact HDParams.Reach.start u hu hd
  | up u j hj h hb ih =>
    exact HDParams.Reach.up u j hj ih ((hbad u (reach_in_domain p Sites P A E v R u j h) j).mp hb)
  | down u u' j h hu hd hstep ih => exact HDParams.Reach.down u u' j ih hu hd hstep

theorem reach_iff_of_bad_agree (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (v : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ u ∈ p.domBall Sites v R, ∀ j, p.BadN P A E u j ↔ p.BadN P' A' E' u j)
    (u : CubeVertex p.d) (j : ℕ) :
    p.Reach Sites P A E v R u j ↔ p.Reach Sites P' A' E' v R u j := by
  exact ⟨reach_of_bad_agree p Sites P A P' A' E E' v R hbad u j,
    reach_of_bad_agree p Sites P' A' P A E' E v R (fun u hu j => (hbad u hu j).symm) u j⟩

theorem height_eq_of_bad_agree (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (v : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ u ∈ p.domBall Sites v R, ∀ j, p.BadN P A E u j ↔ p.BadN P' A' E' u j) :
    p.height Sites P A E R v = p.height Sites P' A' E' R v := by
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter]
  rw [reach_iff_of_bad_agree p Sites P A P' A' E E' v R hbad v j]

theorem selectionAt_some_mem (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (R : ℕ) (v : CubeVertex p.d) (l : p.Loc)
    (hselect : p.selectionAt Sites P A E τ R v = some l) : ∃ j, l ∈ E v j := by
  classical
  let j := p.height Sites P A E R v
  have hEq : p.height Sites P A E R v = j := rfl
  by_cases hj : j < p.H
  · simp [HDParams.selectionAt, hEq, hj] at hselect
    rcases hselect with ⟨_, ⟨hne, hchosen⟩⟩
    let j' : Fin (p.H + 1) := ⟨j, by omega⟩
    let active := (E v j').filter fun l => A l = true
    let priorities := active.image (p.priority τ (v, j'))
    have hneP : priorities.Nonempty := by
      obtain ⟨l, hl⟩ := hne
      exact ⟨p.priority τ (v, j') l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    let q := priorities.min' hneP
    have hmem : ∃ l, l ∈ active ∧ p.priority τ (v, j') l = q :=
      Finset.mem_image.mp (Finset.min'_mem priorities hneP)
    have hc : Classical.choose hmem = l := by
      simpa [active, priorities, q, j'] using hchosen
    have hl := (Classical.choose_spec hmem).1
    rw [hc] at hl
    exact ⟨j', (Finset.mem_filter.mp hl).1⟩
  · simp [HDParams.selectionAt, hEq, hj] at hselect

theorem selection_some_shape (p : HDParams) (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (l : p.Loc)
    (hshape : ∀ j l, l ∈ E v j → P l = true ∧ l.2 = j ∧ hammingDist l.1 v ≤ p.r)
    (hselect : p.selection Sites P A E τ v = some l) : P l = true ∧ hammingDist l.1 v ≤ p.r := by
  obtain ⟨j, hj⟩ := selectionAt_some_mem p Sites P A E τ p.Rlong v l hselect
  exact ⟨(hshape j l hj).1, (hshape j l hj).2.2⟩

end
end HypercubeRamsey.Lane_sol_s05_even
