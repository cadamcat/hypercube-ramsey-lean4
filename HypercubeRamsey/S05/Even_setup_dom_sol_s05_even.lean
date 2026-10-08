import HypercubeRamsey.S05.Even_setup_laws_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem highDeletedOutLaw_data_congr {Id : Type} (H : X.KeyHist) (r r' : X.RecordOn Id)
    (a : X.ArraysOn Id) (c) (hs : 0 < X.p.s n) (hr : r.1.isRight) (hr' : r'.1.isRight)
    (hk : r.1 = r'.1) (ho : r.2.1 = r'.2.1) (hm : r.2.2.2 = r'.2.2.2) :
    highDeletedOutLaw X H r a c hs hr = highDeletedOutLaw X H r' a c hs hr' := by
  obtain ⟨k, obs, refs, mask⟩ := r
  obtain ⟨k', obs', refs', mask'⟩ := r'
  dsimp only at hk ho hm
  cases hk
  cases ho
  cases hm
  rfl

theorem lowMixture_dominates_row (L : X.CentreLayer5) {cL cH : ℝ} (LR : X.LowRows5 L cL cH)
    (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (b : OddRole5 n)
    (c : X.CRef L.ht) (hv : v ∈ Setup5.evenNbrs b) (hb : L.valid H ω b)
    (hvl : X.g.low (X.p.J n) v.1) (hbl : X.g.low (X.p.J n) b.1)
    (hc : X.evenRefOf (L.elig H) H ω v = some c) (o : X.OddOut) :
    X.oddRow LR HR H ω b o ≤
      (Real.exp (X.p.a 4 * X.refLen (X.g.evenType (X.p.J n) v.1) c.2) *
        (lowConfigSet X b (candidatePositions X L ω b)).card) * (lowMixture X L H ω v b c).w o := by
  obtain ⟨cfg, hcfg, hfrom, heq⟩ := actual_lowConfig X L H ω v b c hv hb hc
  have hcomp := mixtureOrUniform_component X (lowConfigSet X b (candidatePositions X L ω b))
    (lowConfigLaw X H (Setup5.arraysOf ω) v c) cfg hcfg o
  change (lowDeletedOutLaw X H (liftRecord X cfg.1 cfg.2) (Setup5.arraysOf ω)
      (c.1, X.g.evenType (X.p.J n) v.1, c.2)).w o ≤ _ at hcomp
  rw [heq] at hcomp
  have href := selected_low_ref_mem X H ω (L.elig H) v b c (Finset.mem_filter.mp hv).2 hvl hbl hc
  have hleft : (X.actualRecord (L.elig H) H ω b).1.isLeft := by
    have hsev : X.g.severity b.1 ≤ X.p.J n := hbl
    simp [Setup5.actualRecord, Setup5.actualRecordAt, ChunkGeometry5.roleKey, hsev]
  have hrow := lowDeletion_dominates_row X H _ (Setup5.arraysOf ω)
    (c.1, X.g.evenType (X.p.J n) v.1, c.2) hleft (LR.row H ω b)
    (LR.row_index H ω b) (LR.row_deletion H ω b hb hbl _ href) o
  rw [Setup5.oddRow, HR.row_low H ω b o hbl, add_zero]
  calc
    _ ≤ Real.exp (X.p.a 4 * X.refLen (X.g.evenType (X.p.J n) v.1) c.2) *
        (lowDeletedOutLaw X H _ (Setup5.arraysOf ω) (c.1, X.g.evenType (X.p.J n) v.1, c.2)).w o := hrow
    _ ≤ Real.exp (X.p.a 4 * X.refLen (X.g.evenType (X.p.J n) v.1) c.2) *
        ((lowConfigSet X b (candidatePositions X L ω b)).card * (lowMixture X L H ω v b c).w o) :=
      mul_le_mul_of_nonneg_left hcomp (Real.exp_pos _).le
    _ = _ := by ring

theorem highMixture_dominates_row (L : X.CentreLayer5) {cL cH : ℝ} (LR : X.LowRows5 L cL cH)
    (HR : X.HighRows5 L) (H : X.KeyHist) (ω : X.CΩ L.ht) (v : EvenRole5 n) (b : OddRole5 n)
    (c : X.CRef L.ht) (hv : v ∈ Setup5.evenNbrs b) (hb : L.valid H ω b)
    (hbl : ¬ X.g.low (X.p.J n) b.1) (hs : 0 < X.p.s n)
    (hc : X.evenRefOf (L.elig H) H ω v = some c) (o : X.OddOut) :
    X.oddRow LR HR H ω b o ≤
      (Real.exp (X.highCost H (X.actualRecord (L.elig H) H ω b) (Setup5.arraysOf ω)
        (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b) o) *
        (highConfigSet X b (candidatePositions X L ω b)).card) * (highMixture X L H ω v b c).w o := by
  obtain ⟨cfg, hcfg, hk, ho, hm⟩ := actual_highConfig X L H ω v b c hv hb hbl hc
  have hright : (X.g.roleKey (X.p.J n) b.1).isRight := by
    have hsev : ¬ X.g.severity b.1 ≤ X.p.J n := hbl
    simp [ChunkGeometry5.roleKey, hsev]
  have hright' : (X.actualRecord (L.elig H) H ω b).1.isRight := hright
  have hcomp := mixtureOrUniform_component X (highConfigSet X b (candidatePositions X L ω b))
    (highConfigLaw X H (Setup5.arraysOf ω) v b c) cfg hcfg o
  have hcond : 0 < X.p.s n ∧ (X.g.roleKey (X.p.J n) b.1).isRight := ⟨hs, hright⟩
  simp only [highConfigLaw, dif_pos hcond] at hcomp
  rw [highDeletedOutLaw_data_congr X H _ _ (Setup5.arraysOf ω) _ hs hright hright' hk ho hm] at hcomp
  have hrow := highCost_dominates_row X H _ (Setup5.arraysOf ω)
    (c.1, X.g.evenType (X.p.J n) v.1, c.2) (HR.row H ω b)
    (HR.row_nonneg H ω b) (HR.row_index H ω b) hs hright' o
  rw [Setup5.oddRow, LR.row_high H ω b o hbl, zero_add]
  calc
    _ ≤ Real.exp (X.highCost H _ (Setup5.arraysOf ω) (c.1, X.g.evenType (X.p.J n) v.1, c.2)
        (HR.row H ω b) o) * (highDeletedOutLaw X H _ (Setup5.arraysOf ω)
          (c.1, X.g.evenType (X.p.J n) v.1, c.2) hs hright').w o := hrow
    _ ≤ Real.exp (X.highCost H _ (Setup5.arraysOf ω) (c.1, X.g.evenType (X.p.J n) v.1, c.2)
        (HR.row H ω b) o) * ((highConfigSet X b (candidatePositions X L ω b)).card *
          (highMixture X L H ω v b c).w o) := mul_le_mul_of_nonneg_left hcomp (Real.exp_pos _).le
    _ = _ := by ring

def localReferenceQ (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht) : FinProb X.OddOut :=
  if (cube n).Adj v.1 b.1 then
    if X.g.low (X.p.J n) v.1 ∧ X.g.low (X.p.J n) b.1 then lowMixture X L H ω v b c
    else if ¬ X.g.low (X.p.J n) v.1 ∧ ¬ X.g.low (X.p.J n) b.1 then highMixture X L H ω v b c
    else uniformOdd X
  else uniformOdd X

theorem localReferenceQ_delete_replace (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht) (z) :
    localReferenceQ X L H (replaceBlockData X ω c.1 (X.g.evenType (X.p.J n) v.1)
      (refIndices X (X.g.evenType (X.p.J n) v.1) c.2) z) v b c = localReferenceQ X L H ω v b c := by
  unfold localReferenceQ
  split_ifs with ha hl hh
  · exact lowMixture_delete_replace X L H ω v b c hl.1 z
  · exact highMixture_delete_replace X L H ω v b c z
  · rfl
  · rfl

theorem localReferenceQ_local (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n)
    (b : OddRole5 n) (c : X.CRef L.ht) :
    FinProb.DependsOn (fun ω => localReferenceQ X L H ω v b c)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8)) := by
  intro ω ω' hagree
  dsimp only
  unfold localReferenceQ
  split_ifs with ha hl hh
  · exact lowMixture_local X L H v b c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩) ω ω' hagree
  · exact highMixture_local X L H v b c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩) ω ω' hagree
  · rfl
  · rfl

end
end HypercubeRamsey.Lane_sol_s05_even
