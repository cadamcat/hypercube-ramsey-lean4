import HypercubeRamsey.S03.Height.Device

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey

noncomputable section
set_option maxHeartbeats 400000

variable (p : HDParams) (Sites : p.Sites) (P A P' A' : p.Loc → Bool) (E E' : p.EligMap)
variable (vq : CubeVertex p.d) (R : ℕ)

theorem reach_in_ball {v : CubeVertex p.d} {j : ℕ}
    (h : p.Reach Sites P A E vq R v j) : _root_.hammingDist v vq ≤ R := by
  induction h with
  | start v hv hd => exact hd
  | up v j hj h hb ih => exact ih
  | down v v' j h hv' hd hstep ih => exact hd

theorem reach_of_bad_congr
    (hbad : ∀ v, _root_.hammingDist v vq ≤ R → ∀ j, p.Bad P A E v j ↔ p.Bad P' A' E' v j)
    {v : CubeVertex p.d} {j : ℕ} (h : p.Reach Sites P A E vq R v j) :
    p.Reach Sites P' A' E' vq R v j := by
  induction h with
  | start v hv hd => exact HDParams.Reach.start v hv hd
  | up v j hj h hb ih =>
    obtain ⟨hlev, hbad₀⟩ := hb
    exact HDParams.Reach.up v j hj ih
      ⟨hlev, (hbad v (reach_in_ball p Sites P A E vq R h) _).mp hbad₀⟩
  | down v v' j h hv' hd hstep ih => exact HDParams.Reach.down v v' j ih hv' hd hstep

theorem height_of_bad_congr
    (hbad : ∀ v, _root_.hammingDist v vq ≤ R → ∀ j, p.Bad P A E v j ↔ p.Bad P' A' E' v j) :
    p.height Sites P A E R vq = p.height Sites P' A' E' R vq := by
  have hr (v : CubeVertex p.d) (j : ℕ) :
      p.Reach Sites P A E vq R v j ↔ p.Reach Sites P' A' E' vq R v j :=
    ⟨reach_of_bad_congr p Sites P A P' A' E E' vq R hbad,
      reach_of_bad_congr p Sites P' A' P A E' E vq R (fun v hv j => (hbad v hv j).symm)⟩
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter, hr]

def pickPriority (active : Finset p.Loc) (priority : p.Loc → Fin (Fintype.card p.Loc)) : Option p.Loc :=
  let priorities := active.image priority
  if hne : priorities.Nonempty then
    some (Classical.choose (Finset.mem_image.mp (Finset.min'_mem priorities hne)))
  else none

theorem pickPriority_mem (active : Finset p.Loc) (priority : p.Loc → Fin (Fintype.card p.Loc))
    (l : p.Loc) (h : pickPriority p active priority = some l) : l ∈ active := by
  unfold pickPriority at h
  dsimp only at h
  split_ifs at h with hne
  have hm := Classical.choose_spec (Finset.mem_image.mp (Finset.min'_mem (active.image priority) hne))
  exact (Option.some.inj h) ▸ hm.1

/-- Expose the height as an argument so equality can be used before unfolding
the dependent finite level and its tie lookup. -/
def selectionFromHeight (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (v : CubeVertex p.d) (j : ℕ) : Option p.Loc :=
  if hj : j < p.H then
    let j' : Fin (p.H + 1) := ⟨j, by omega⟩
    if p.Bad P A E v j' then none
    else pickPriority p ((E v j').filter (fun l => A l = true)) (p.priority τ (v, j'))
  else none

theorem selectionAt_mem (τ : p.Ties) (l : p.Loc)
    (hsel : p.selectionAt Sites P A E τ R vq = some l) :
    ∃ j : Fin (p.H + 1), l ∈ E vq j := by
  change selectionFromHeight p P A E τ vq (p.height Sites P A E R vq) = some l at hsel
  unfold selectionFromHeight at hsel
  dsimp only at hsel
  split_ifs at hsel with hj hbad
  exact ⟨_, (Finset.mem_filter.mp (pickPriority_mem p _ _ l hsel)).1⟩

theorem selectionAt_of_bad_congr (τ τ' : p.Ties)
    (hbad : ∀ v, _root_.hammingDist v vq ≤ R → ∀ j, p.Bad P A E v j ↔ p.Bad P' A' E' v j)
    (hE : ∀ j, E vq j = E' vq j)
    (hA : ∀ j l, l ∈ E vq j → A l = A' l)
    (hτ : ∀ j, τ (vq, j) = τ' (vq, j)) :
    p.selectionAt Sites P A E τ R vq = p.selectionAt Sites P' A' E' τ' R vq := by
  have hh := height_of_bad_congr p Sites P A P' A' E E' vq R hbad
  change selectionFromHeight p P A E τ vq (p.height Sites P A E R vq) =
    selectionFromHeight p P' A' E' τ' vq (p.height Sites P' A' E' R vq)
  rw [hh]
  by_cases hj : p.height Sites P' A' E' R vq < p.H
  · let j : Fin (p.H + 1) := ⟨p.height Sites P' A' E' R vq, by omega⟩
    have hb : p.Bad P A E vq j ↔ p.Bad P' A' E' vq j := hbad vq (by simp) j
    have hactive : (E vq j).filter (fun l => A l = true) = (E' vq j).filter (fun l => A' l = true) := by
      ext l
      simp only [Finset.mem_filter, ← hE j]
      constructor
      · rintro ⟨hl, ha⟩
        exact ⟨hl, (hA j l hl).symm.trans ha⟩
      · rintro ⟨hl, ha⟩
        exact ⟨hl, (hA j l hl).trans ha⟩
    by_cases hbp : p.Bad P' A' E' vq j
    · have hb₀ := hb.mpr hbp
      simp only [selectionFromHeight, dite_eq_left hj]
      change (if p.Bad P A E vq j then none else _) = (if p.Bad P' A' E' vq j then none else _)
      simp only [hb₀, hbp, ite_true]
    · have hb₀ : ¬ p.Bad P A E vq j := fun h => hbp (hb.mp h)
      simp only [selectionFromHeight, dite_eq_left hj]
      change (if p.Bad P A E vq j then none else _) = (if p.Bad P' A' E' vq j then none else _)
      simp only [hb₀, hbp, ite_false]
      rw [hactive]
      apply congrArg (pickPriority p _)
      funext l
      exact congrArg (fun e : p.TiePerm => e (Fintype.equivFin p.Loc l)) (hτ j)
  · simp only [selectionFromHeight, dite_eq_right hj]

theorem location_pool_card_le (v : CubeVertex p.d) (B : ℝ)
    (hcount : ∀ j : Fin (p.H + 1),
      ((Finset.univ.filter (fun u : CubeVertex p.d => P (u, j) = true ∧
        _root_.hammingDist u v ≤ p.r)).card : ℝ) ≤ B) :
    ((Finset.univ.filter (fun l : p.Loc => P l = true ∧
      _root_.hammingDist l.1 v ≤ p.r)).card : ℝ) ≤ (p.H + 1 : ℕ) * B := by
  let S := fun j : Fin (p.H + 1) => Finset.univ.filter (fun u : CubeVertex p.d =>
    P (u, j) = true ∧ _root_.hammingDist u v ≤ p.r)
  have he : Finset.univ.filter (fun l : p.Loc => P l = true ∧ _root_.hammingDist l.1 v ≤ p.r) =
      Finset.univ.biUnion (fun j : Fin (p.H + 1) => (S j).image (fun u => (u, j))) := by
    ext l
    rcases l with ⟨u, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hu
      exact ⟨j, u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
    · rintro ⟨j', u', hu', he⟩
      cases he
      exact (Finset.mem_filter.mp hu').2
  rw [he]
  calc
    _ ≤ ((∑ j : Fin (p.H + 1), ((S j).image (fun u => (u, j))).card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (p.H + 1), ((S j).card : ℝ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum fun j _ => Nat.cast_le.mpr Finset.card_image_le
    _ ≤ ∑ _j : Fin (p.H + 1), B := Finset.sum_le_sum fun j _ => hcount j
    _ = _ := by simp

end
end HypercubeRamsey.Lane_sol_s05_k1
