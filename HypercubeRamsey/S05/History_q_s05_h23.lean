import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.History_q_s05_hist2

/-!
# Helpers for the Stage 2 and Stage 3 history restrictions
-/

namespace HypercubeRamsey.Lane_q_s05_h23

open Classical
open scoped BigOperators

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

noncomputable abbrev CoarsePairLaw5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (w : BinVector5 n) : FinProb (Fin N × X.Stream) :=
  FinProb.bind (X.P.prior.partner v w) fun a =>
    FinProb.pi fun _s : Fin (X.p.streamSegs n) => X.segLaw v a

noncomputable def coarsePairEquiv5 (X : Setup5 γ K' χ n N E G) :
    (BinVector5 n → Fin N × X.Stream) ≃ X.Coarse where
  toFun z := (fun w => (z w).1, fun w => (z w).2)
  invFun c := fun w => (c.1 w, c.2 w)
  left_inv := by
    intro z
    funext w
    change ((z w).1, (z w).2) = z w
    exact Prod.ext rfl rfl
  right_inv := by
    intro c
    cases c with
    | mk a W =>
      apply Prod.ext
      · funext w
        rfl
      · funext w
        funext s
        funext x
        rfl

set_option maxHeartbeats 0 in
theorem coarseLaw_eq_map_pi5 (X : Setup5 γ K' χ n N E G) (v : Fin N) :
    X.coarseLaw v = FinProb.map (FinProb.pi (CoarsePairLaw5 X v)) (coarsePairEquiv5 X) := by
  classical
  let e := coarsePairEquiv5 X
  apply FinProb.ext
  intro c
  simp only [FinProb.map]
  rw [Finset.sum_eq_single (e.symm c)]
  · have he : coarsePairEquiv5 X (e.symm c) = c := by
      simpa [e] using e.apply_symm_apply c
    have hleft : (X.coarseLaw v).w c =
        (∏ w, (X.P.prior.partner v w).w (c.1 w)) *
          ∏ w, ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s) := by
      rfl
    have hright : (FinProb.pi (CoarsePairLaw5 X v)).w (e.symm c) =
        ∏ w, ((X.P.prior.partner v w).w (c.1 w) *
          ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s)) := by
      rfl
    rw [if_pos he]
    rw [hleft, hright]
    apply (Finset.prod_mul_distrib).symm
  · intro z hz hne
    have hz' : coarsePairEquiv5 X z ≠ c := by
      intro heq
      apply hne
      exact e.injective (by simpa [e] using heq)
    simp [hz']
  · intro h
    exact (h (Finset.mem_univ _)).elim

end HypercubeRamsey.Lane_q_s05_h23
