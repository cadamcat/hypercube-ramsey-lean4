import HypercubeRamsey.S18.Nodes_sol_s18_n5

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT)

theorem initialPrior_local (hD : D.Spec) (v : Pos T k) (s s' : Config D.fresh)
    (hs : ∀ C ∈ D.directCells v, s C = s' C) : D.initialPrior v s = D.initialPrior v s' := by
  simp only [S18.LateData.initialPrior,
    S18.Lane_sol_s18_n5.initialValid_local D hD v s s' hs, hD.prior_local v s s' hs]

/-- A current list consults its initial direct-cell scope and labels of processed neighbors. -/
theorem priorAt_local (hD : D.Spec) (j : Fin (D.geom.r + 1)) (v : Pos T k)
    (h h' : D.encoding.base.History j)
    (hs : ∀ C ∈ D.directCells v, h.1 C = h'.1 C)
    (hl : ∀ b : D.encoding.base.ProcessedRole j,
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 →
      D.encoding.base.rowLabel (h.2 b) = D.encoding.base.rowLabel (h'.2 b)) :
    D.priorAt j v h = D.priorAt j v h' := by
  have hv := S18.Lane_sol_s18_n5.initialValid_local D hD v h.1 h'.1 hs
  have hp := initialPrior_local D hD v h.1 h'.1 hs
  have hw : (fun x => (D.initialPrior v h.1).w x *
      ∏ b : D.encoding.base.ProcessedRole j,
        if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
          if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h.2 b)) then 1 else 0
        else 1) =
      (fun x => (D.initialPrior v h'.1).w x *
      ∏ b : D.encoding.base.ProcessedRole j,
        if (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1 then
          if Hits (T.S.E k) PT.tiling.c x (D.encoding.base.rowLabel (h'.2 b)) then 1 else 0
        else 1) := by
    funext x
    rw [hp]
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    by_cases ha : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b.1
    · simp only [ha, ite_true, hl b ha]
    · simp only [ha, ite_false]
  simp only [S18.LateData.priorAt, hv, hw]

/-- The approved producer input determines a row kernel from its neighbor lists. -/
theorem referenceRow_local (H : S18.TransitionData D) (j : Fin D.geom.r)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h h' : D.encoding.base.History j.castSucc)
    (hp : ∀ a, D.currentPrior j (flipPos b.1 a) h = D.currentPrior j (flipPos b.1 a) h') :
    D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h' := by
  apply Lane_q_s16_comp1.finlaw_ext
  intro out
  rw [H.reference_formula, H.reference_formula]
  simp_rw [hp]

end HypercubeRamsey.Lane_sol_s18_n4
