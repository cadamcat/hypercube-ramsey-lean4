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
    (hshape : ∀ j l, l ∈ E v j → P l = true ∧ l.2 = j ∧ _root_.hammingDist l.1 v ≤ p.r)
    (hselect : p.selection Sites P A E τ v = some l) : P l = true ∧ _root_.hammingDist l.1 v ≤ p.r := by
  obtain ⟨j, hj⟩ := selectionAt_some_mem p Sites P A E τ p.Rlong v l hselect
  exact ⟨(hshape j l hj).1, (hshape j l hj).2.2⟩

theorem bad_iff_of_agree (p : HDParams) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) (hE : E v j = E' v j)
    (hshape : ∀ l ∈ E v j, l.2 = j ∧ _root_.hammingDist l.1 v ≤ p.r)
    (hagree : ∀ l : p.Loc, l.2 = j → _root_.hammingDist l.1 v ≤ p.r + p.D → P l = P' l ∧ A l = A' l) :
    p.Bad P A E v j ↔ p.Bad P' A' E' v j := by
  have hactive : (∀ l ∈ E v j, A l = false) ↔ (∀ l ∈ E' v j, A' l = false) := by
    rw [← hE]
    constructor
    · intro h l hl
      have hs := hshape l hl
      rw [← (hagree l hs.1 (by omega)).2]
      exact h l hl
    · intro h l hl
      have hs := hshape l hl
      rw [(hagree l hs.1 (by omega)).2]
      exact h l hl
  have hcount : (Finset.univ.filter fun u : CubeVertex p.d =>
      P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D) =
      (Finset.univ.filter fun u : CubeVertex p.d =>
      P' (u, j) = true ∧ A' (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D) := by
    ext u
    by_cases hu : _root_.hammingDist u v ≤ p.r + p.D
    · have hh := hagree (u, j) rfl hu
      simp [hu, hh.1, hh.2]
    · simp [hu]
  unfold HDParams.Bad
  rw [hactive, hcount]

def selectMinimum (p : HDParams) (active : Finset p.Loc) (priority : p.Loc → Fin (Fintype.card p.Loc)) :
    Option p.Loc :=
  if hne : (active.image priority).Nonempty then
    some (Classical.choose (Finset.mem_image.mp (Finset.min'_mem (active.image priority) hne)))
  else none

theorem selectionAt_eq_of_data (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool)
    (E E' : p.EligMap) (τ τ' : p.Ties) (v : CubeVertex p.d) (R : ℕ)
    (hheight : p.height Sites P A E R v = p.height Sites P' A' E' R v)
    (hbad : ∀ j, p.Bad P A E v j ↔ p.Bad P' A' E' v j)
    (hactive : ∀ j, (E v j).filter (fun l => A l = true) = (E' v j).filter (fun l => A' l = true))
    (hpriority : ∀ j, p.priority τ (v, j) = p.priority τ' (v, j)) :
    p.selectionAt Sites P A E τ R v = p.selectionAt Sites P' A' E' τ' R v := by
  unfold HDParams.selectionAt
  simp only [hheight]
  split
  · rename_i hj
    let j' : Fin (p.H + 1) := ⟨p.height Sites P' A' E' R v, by omega⟩
    rw [propext (hbad j')]
    split
    · rfl
    · change selectMinimum p ((E v j').filter (fun l => A l = true)) (p.priority τ (v, j')) =
        selectMinimum p ((E' v j').filter (fun l => A' l = true)) (p.priority τ' (v, j'))
      rw [hactive j', hpriority j']
  · rfl

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem selLong_local (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n) :
    FinProb.DependsOn (fun ω : X.CΩ L.ht => X.selLong (L.elig H) ω v)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8)) := by
  intro ω ω' hagree
  let p := L.ht.hp
  let q : CubeVertex p.d := X.siteOf v
  let P := Setup5.pos ω
  let P' := Setup5.pos ω'
  let A := Setup5.act ω
  let A' := Setup5.act ω'
  let E₀ := L.elig H ω
  let E₁ := L.elig H ω'
  have hcell (l : p.Loc) (hl : _root_.hammingDist l.1 q ≤ p.r + L.slack + 8) : ω l = ω' l :=
    hagree l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
  have hE (u : CubeVertex p.d) (hu : _root_.hammingDist u q ≤ p.Rlong) (j : Fin (p.H + 1)) :
      E₀ u j = E₁ u j := by
    apply L.elig_local H u j ω ω'
    intro l hl
    have hdist := (Finset.mem_filter.mp hl).2
    change _root_.hammingDist l.1 u ≤ p.r + 16 at hdist
    apply hcell l
    have htri := _root_.hammingDist_triangle l.1 u q
    have hslack := L.slack_large
    change p.Rlong + 32 ≤ L.slack at hslack
    omega
  have hbadAt (u : CubeVertex p.d) (hu : _root_.hammingDist u q ≤ p.Rlong) (j : Fin (p.H + 1)) :
      p.Bad P A E₀ u j ↔ p.Bad P' A' E₁ u j := by
    apply bad_iff_of_agree p P A P' A' E₀ E₁ u j (hE u hu j)
    · intro l hl
      exact (L.elig_shape H ω u j l hl).2
    · intro l hj hdist
      have hloc : _root_.hammingDist l.1 q ≤ p.r + L.slack + 8 := by
        have htri := _root_.hammingDist_triangle l.1 u q
        have hD : p.D = 8 := rfl
        have hslack := L.slack_large
        change p.Rlong + 32 ≤ L.slack at hslack
        omega
      have hh := hcell l hloc
      exact ⟨congrArg (fun a : X.CVal L.ht => a.1) hh,
        congrArg (fun a : X.CVal L.ht => a.2.1) hh⟩
  have hbadN (u : CubeVertex p.d) (hu : u ∈ p.domBall (X.sites L.ht) q p.Rlong) (j : ℕ) :
      p.BadN P A E₀ u j ↔ p.BadN P' A' E₁ u j := by
    have hdist := (Finset.mem_filter.mp hu).2
    unfold HDParams.BadN
    constructor
    · rintro ⟨hj, hb⟩
      exact ⟨hj, (hbadAt u hdist ⟨j, hj⟩).mp hb⟩
    · rintro ⟨hj, hb⟩
      exact ⟨hj, (hbadAt u hdist ⟨j, hj⟩).mpr hb⟩
  have hheight := height_eq_of_bad_agree p (X.sites L.ht) P A P' A' E₀ E₁ q p.Rlong hbadN
  have hactive (j : Fin (p.H + 1)) :
      (E₀ q j).filter (fun l => A l = true) = (E₁ q j).filter (fun l => A' l = true) := by
    rw [← hE q (by simp) j]
    apply Finset.filter_congr
    intro l hl
    have hs := L.elig_shape H ω q j l hl
    have hdist : _root_.hammingDist l.1 q ≤ p.r := hs.2.2
    have hh := hcell l (by omega)
    exact Iff.of_eq (congrArg (fun a : X.CVal L.ht => a.2.1 = true) hh)
  have hpriority (j : Fin (p.H + 1)) : p.priority (Setup5.tie ω) (q, j) = p.priority (Setup5.tie ω') (q, j) := by
    have hh := hcell (q, j) (by simp)
    unfold HDParams.priority Setup5.tie
    rw [hh]
  exact selectionAt_eq_of_data p (X.sites L.ht) P A P' A' E₀ E₁ (Setup5.tie ω) (Setup5.tie ω') q p.Rlong
    hheight (hbadAt q (by simp)) hactive hpriority

end
end HypercubeRamsey.Lane_sol_s05_even
