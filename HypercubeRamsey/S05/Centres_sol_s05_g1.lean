import HypercubeRamsey.S03.Height.Device

namespace HypercubeRamsey.Lane_sol_s05_g1

open Classical OAI.HypercubeRamsey

noncomputable section

private theorem reach_dist {p : HDParams} {S : p.Sites} {P A : p.Loc → Bool}
    {E : p.EligMap} {q v : CubeVertex p.d} {R j : ℕ}
    (h : p.Reach S P A E q R v j) : _root_.hammingDist v q ≤ R := by
  induction h with
  | start v hv hd => exact hd
  | up v j hj h hb ih => exact ih
  | down v v' j h hv hd hstep ih => exact hd

private theorem reach_congr {p : HDParams} (S : p.Sites)
    (P A P' A' : p.Loc → Bool) (E E' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ v, _root_.hammingDist v q ≤ R → ∀ j,
      p.BadN P A E v j ↔ p.BadN P' A' E' v j) (v : CubeVertex p.d) (j : ℕ) :
    p.Reach S P A E q R v j ↔ p.Reach S P' A' E' q R v j := by
  have forward (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
      (hb : ∀ v, _root_.hammingDist v q ≤ R → ∀ j,
        p.BadN P A E v j → p.BadN P' A' E' v j)
      {v j} (h : p.Reach S P A E q R v j) : p.Reach S P' A' E' q R v j := by
    induction h with
    | start v hv hd => exact .start v hv hd
    | up v j hj h hbad ih => exact .up v j hj ih (hb v (reach_dist h) j hbad)
    | down v v' j h hv hd hstep ih => exact .down v v' j ih hv hd hstep
  exact ⟨forward P A P' A' E E' (fun v hv j => (hbad v hv j).mp),
    forward P' A' P A E' E (fun v hv j => (hbad v hv j).mpr)⟩

/-- Equality of bad tests on the consultation ball determines every path maximum. -/
theorem height_congr (p : HDParams) (S : p.Sites)
    (P A P' A' : p.Loc → Bool) (E E' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ v, _root_.hammingDist v q ≤ R → ∀ j,
      p.Bad P A E v j ↔ p.Bad P' A' E' v j) :
    p.height S P A E R q = p.height S P' A' E' R q := by
  have hb : ∀ v, _root_.hammingDist v q ≤ R → ∀ j,
      p.BadN P A E v j ↔ p.BadN P' A' E' v j := by
    intro v hv j
    simp only [HDParams.BadN]
    exact exists_congr fun hj => hbad v hv ⟨j, hj⟩
  unfold HDParams.height
  congr 1
  apply Finset.ext
  intro j
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => reach_congr S P A P' A' E E' q R hb q j

/-- The height rule reads local eligibility, local position/activation bits, and the query's ties. -/
theorem selectionAt_congr_local (p : HDParams) (S : p.Sites)
    (P A P' A' : p.Loc → Bool) (E E' : p.EligMap) (τ τ' : p.Ties)
    (q : CubeVertex p.d) (R : ℕ)
    (hE : ∀ v, _root_.hammingDist v q ≤ R → ∀ j, E v j = E' v j)
    (hshape : ∀ v, _root_.hammingDist v q ≤ R → ∀ j l, l ∈ E v j →
      _root_.hammingDist l.1 v ≤ p.r)
    (hP : ∀ l, _root_.hammingDist l.1 q ≤ R + p.r + p.D → P l = P' l)
    (hA : ∀ l, _root_.hammingDist l.1 q ≤ R + p.r + p.D → A l = A' l)
    (hτ : ∀ j, τ (q, j) = τ' (q, j)) :
    p.selectionAt S P A E τ R q = p.selectionAt S P' A' E' τ' R q := by
  have hball (v : CubeVertex p.d) (hv : _root_.hammingDist v q ≤ R)
      (l : p.Loc) (hl : _root_.hammingDist l.1 v ≤ p.r + p.D) :
      _root_.hammingDist l.1 q ≤ R + p.r + p.D := by
    have ht := _root_.hammingDist_triangle l.1 v q
    omega
  have hactive (v : CubeVertex p.d) (hv : _root_.hammingDist v q ≤ R) (j) :
      (E v j).filter (fun l => A l = true) = (E' v j).filter (fun l => A' l = true) := by
    rw [← hE v hv j]
    apply Finset.filter_congr
    intro l hl
    rw [hA l (hball v hv l (by have := hshape v hv j l hl; omega))]
  have hbad (v : CubeVertex p.d) (hv : _root_.hammingDist v q ≤ R) (j) :
      p.Bad P A E v j ↔ p.Bad P' A' E' v j := by
    have hfirst : (∀ l ∈ E v j, A l = false) ↔ (∀ l ∈ E' v j, A' l = false) := by
      rw [← hE v hv j]
      apply forall_congr'
      intro l
      apply forall_congr'
      intro hl
      rw [hA l (hball v hv l (by have := hshape v hv j l hl; omega))]
    have hcount : (Finset.univ.filter (fun u : CubeVertex p.d =>
        P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D)) =
        (Finset.univ.filter (fun u : CubeVertex p.d =>
        P' (u, j) = true ∧ A' (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D)) := by
      apply Finset.filter_congr
      intro u hu
      by_cases hd : _root_.hammingDist u v ≤ p.r + p.D
      · rw [hP (u, j) (hball v hv (u, j) hd), hA (u, j) (hball v hv (u, j) hd)]
      · simp only [hd, and_false]
    unfold HDParams.Bad
    rw [hcount]
    exact or_congr hfirst Iff.rfl
  have hh := height_congr p S P A P' A' E E' q R hbad
  have hq : _root_.hammingDist q q ≤ R := by simp
  simp only [HDParams.selectionAt, hh]
  split
  · rename_i hj
    simp only [← propext (hbad q hq _)]
    split
    · rfl
    · have he := hactive q hq ⟨p.height S P' A' E' R q, by omega⟩
      simp only [← he, HDParams.priority, hτ]
  · rfl

/-- A returned ID belongs to eligibility at the computed level. -/
theorem selectionAt_mem (p : HDParams) (S : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (R : ℕ) (v : CubeVertex p.d) (l : p.Loc)
    (hs : p.selectionAt S P A E τ R v = some l) : ∃ j, l ∈ E v j := by
  dsimp only [HDParams.selectionAt] at hs
  split at hs
  · split at hs
    · cases hs
    · split at hs
      · rename_i hj hb hne
        have hm := Classical.choose_spec (Finset.mem_image.mp
          (Finset.min'_mem _ hne))
        have he := Option.some.inj hs
        exact ⟨_, (Finset.mem_filter.mp (he ▸ hm.1)).1⟩
      · cases hs
  · cases hs

end
end HypercubeRamsey.Lane_sol_s05_g1
