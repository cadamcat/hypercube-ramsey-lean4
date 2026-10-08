import HypercubeRamsey.S05.Even_setup_mixtures_sol_s05_even
import HypercubeRamsey.S05.History_sol_s05_hist1f

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def uniformOdd : FinProb X.OddOut :=
  FinProb.uniformAll ⟨(0, X.y₀)⟩

def mixtureOrUniform {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (Q : I → FinProb X.OddOut) : FinProb X.OddOut :=
  if hS : S.Nonempty then uniformMixture S hS Q else uniformOdd X

theorem mixtureOrUniform_component {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (Q : I → FinProb X.OddOut) (i : I) (hi : i ∈ S) (o : X.OddOut) :
    (Q i).w o ≤ (S.card : ℝ) * (mixtureOrUniform X S Q).w o := by
  rw [mixtureOrUniform, dif_pos ⟨i, hi⟩]
  exact uniformMixture_component S ⟨i, hi⟩ Q i hi o

theorem mixtureOrUniform_congr {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (Q Q' : I → FinProb X.OddOut) (hQ : ∀ i ∈ S, Q i = Q' i) :
    mixtureOrUniform X S Q = mixtureOrUniform X S Q' := by
  by_cases hS : S.Nonempty
  · simp only [mixtureOrUniform, dif_pos hS]
    apply FinProb.ext
    intro o
    rw [uniformMixture_weight, uniformMixture_weight]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => congrArg (fun Q : FinProb X.OddOut => Q.w o) (hQ i hi))
  · simp only [mixtureOrUniform, dif_neg hS]

def lowConfigLaw {h : X.HeightChoice5} (H : X.KeyHist) (a : X.ArraysOn h.hp.Loc)
    (v : EvenRole5 n) (c : X.CRef h) (cfg : X.AbsRecord × (Fin (X.p.T n) → h.hp.Loc)) :
    FinProb X.OddOut :=
  lowDeletedOutLaw X H (liftRecord X cfg.1 cfg.2) a (c.1, X.g.evenType (X.p.J n) v.1, c.2)

def highConfigLaw {h : X.HeightChoice5} (H : X.KeyHist) (a : X.ArraysOn h.hp.Loc)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h)
    (cfg : Finset (Fin (X.p.T n) × X.Ty) × (Fin (X.p.T n) → h.hp.Loc)) : FinProb X.OddOut :=
  if h : 0 < X.p.s n ∧ (X.g.roleKey (X.p.J n) b.1).isRight then
    highDeletedOutLaw X H (highConfigRecord X b cfg) a
      (c.1, X.g.evenType (X.p.J n) v.1, c.2) h.1 h.2
  else uniformOdd X

def lowMixture (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht) : FinProb X.OddOut :=
  mixtureOrUniform X (lowConfigSet X b (candidatePositions X L ω b))
    (lowConfigLaw X H (Setup5.arraysOf ω) v c)

def highMixture (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht) : FinProb X.OddOut :=
  mixtureOrUniform X (highConfigSet X b (candidatePositions X L ω b))
    (highConfigLaw X H (Setup5.arraysOf ω) v b c)

theorem lowConfig_mask_distinct {h : X.HeightChoice5} (v : EvenRole5 n) (b : OddRole5 n)
    (c : X.CRef h) (D : Finset h.hp.Loc) (cfg : X.AbsRecord × (Fin (X.p.T n) → h.hp.Loc))
    (hcfg : cfg ∈ lowConfigSet X b D) (hv : X.g.low (X.p.J n) v.1)
    (d : h.hp.Loc × X.Ty) (M : Finset (Fin X.blockBound))
    (hd : (liftRecord X cfg.1 cfg.2).2.2.2 = some (d.1, d.2, M)) :
    d ≠ (c.1, X.g.evenType (X.p.J n) v.1) := by
  have hocc := (Finset.mem_filter.mp (Finset.mem_product.mp hcfg).1).2.1
  obtain ⟨b', μ, hr, _, _⟩ := hocc
  have hr' := liftRecord_from X cfg.1 cfg.2 b' μ hr
  have hm := hr'.2.2.2
  rw [hd] at hm
  obtain ⟨_, a, ha, hK, hnone, _, _⟩ := hm
  intro heq
  have ht := congrArg (fun d : h.hp.Loc × X.Ty => d.2.2.2) heq
  rw [hnone] at ht
  have hsev : X.g.severity v.1 ≤ X.p.J n := hv
  simp [ChunkGeometry5.evenType, hsev] at ht

theorem lowConfigLaw_delete_replace {h : X.HeightChoice5} (H : X.KeyHist) (a : X.ArraysOn h.hp.Loc)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h) (D : Finset h.hp.Loc)
    (cfg : X.AbsRecord × (Fin (X.p.T n) → h.hp.Loc)) (hcfg : cfg ∈ lowConfigSet X b D)
    (hv : X.g.low (X.p.J n) v.1) (z) :
    lowConfigLaw X H (replaceArrays X a (c.1, X.g.evenType (X.p.J n) v.1, c.2) z) v c cfg =
      lowConfigLaw X H a v c cfg := by
  exact lowDeletedOutLaw_delete_replace X H _ a _ z (lowConfig_mask_distinct X v b c D cfg hcfg hv)

theorem highConfigLaw_delete_replace {h : X.HeightChoice5} (H : X.KeyHist) (a : X.ArraysOn h.hp.Loc)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h) (cfg) (z) :
    highConfigLaw X H (replaceArrays X a (c.1, X.g.evenType (X.p.J n) v.1, c.2) z) v b c cfg =
      highConfigLaw X H a v b c cfg := by
  unfold highConfigLaw
  split_ifs with hs
  · exact highDeletedOutLaw_delete_replace X H _ a _ z
      (fun d M hd => by cases hd) hs.1 hs.2
  · rfl

theorem step3Post_arrays_congr {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a a' : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = a' c) (excl) :
    X.step3PostOn H r a excl = X.step3PostOn H r a' excl := by
  funext θ
  unfold Setup5.step3PostOn
  rw [Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r a a' hmask hab θ,
    Lane_sol_s05_hist1b.obsLikOn_arrays_congr X H r a a' hab θ excl,
    Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r a a' hmask hab excl]

theorem lowDeletedOutLaw_arrays_congr {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a a' : X.ArraysOn Id) (c)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ∈ r.2.1)
    (hab : ∀ d ∈ r.2.1, a d = a' d) :
    lowDeletedOutLaw X H r a c = lowDeletedOutLaw X H r a' c := by
  unfold lowDeletedOutLaw lowDeletedLaw
  rw [step3Post_arrays_congr X H r a a' hmask hab]

theorem highDeletedOutLaw_arrays_congr {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id)
    (a a' : X.ArraysOn Id) (c) (hs : 0 < X.p.s n) (hr : r.1.isRight)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ∈ r.2.1)
    (hab : ∀ d ∈ r.2.1, a d = a' d) :
    highDeletedOutLaw X H r a c hs hr = highDeletedOutLaw X H r a' c hs hr := by
  unfold highDeletedOutLaw Setup5.highDeleted
  rw [step3Post_arrays_congr X H r a a' hmask hab]

theorem lowConfigLaw_arrays_congr {h : X.HeightChoice5} (H : X.KeyHist)
    (a a' : X.ArraysOn h.hp.Loc) (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h)
    (D : Finset h.hp.Loc) (cfg) (hcfg : cfg ∈ lowConfigSet X b D)
    (hab : ∀ l ∈ D, ∀ K, a (l, K) = a' (l, K)) :
    lowConfigLaw X H a v c cfg = lowConfigLaw X H a' v c cfg := by
  have hocc := (Finset.mem_filter.mp (Finset.mem_product.mp hcfg).1).2.1
  obtain ⟨b', μ, hr, _, _⟩ := hocc
  have hr' := liftRecord_from X cfg.1 cfg.2 b' μ hr
  apply lowDeletedOutLaw_arrays_congr X H _ a a' _
  · exact record_mask_observed X _ b' _ hr'
  · intro d hd
    exact hab d.1 (lowConfig_observed_local X b D cfg hcfg d hd) d.2

theorem highConfigLaw_arrays_congr {h : X.HeightChoice5} (H : X.KeyHist)
    (a a' : X.ArraysOn h.hp.Loc) (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef h)
    (D : Finset h.hp.Loc) (cfg) (hcfg : cfg ∈ highConfigSet X b D)
    (hab : ∀ l ∈ D, ∀ K, a (l, K) = a' (l, K)) :
    highConfigLaw X H a v b c cfg = highConfigLaw X H a' v b c cfg := by
  unfold highConfigLaw
  split_ifs with hs
  · apply highDeletedOutLaw_arrays_congr X H _ a a' _ hs.1 hs.2
    · intro d M hd
      cases hd
    · intro d hd
      exact hab d.1 (highConfig_observed_local X b D cfg hcfg d hd) d.2
  · rfl

theorem pos_replaceBlockData {h : X.HeightChoice5} (ω : X.CΩ h) (l : h.hp.Loc) (K : X.Ty)
    (M : Finset (Fin (X.p.typeBlocks n K))) (z) :
    Setup5.pos (replaceBlockData X ω l K M z) = Setup5.pos ω := by
  funext l'
  by_cases hl : l' = l
  · subst l'
    simp [Setup5.pos, replaceBlockData]
  · simp [Setup5.pos, replaceBlockData, Function.update_of_ne hl]

theorem candidatePositions_replaceBlockData (L : X.CentreLayer5) (ω : X.CΩ L.ht)
    (l : L.ht.hp.Loc) (K : X.Ty) (M : Finset (Fin (X.p.typeBlocks n K))) (z) (b : OddRole5 n) :
    candidatePositions X L (replaceBlockData X ω l K M z) b = candidatePositions X L ω b := by
  unfold candidatePositions
  rw [pos_replaceBlockData]

theorem lowMixture_delete_replace (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht)
    (hv : X.g.low (X.p.J n) v.1) (z) :
    lowMixture X L H
      (replaceBlockData X ω c.1 (X.g.evenType (X.p.J n) v.1)
        (refIndices X (X.g.evenType (X.p.J n) v.1) c.2) z) v b c = lowMixture X L H ω v b c := by
  unfold lowMixture
  rw [candidatePositions_replaceBlockData, arraysOf_replaceBlockData]
  apply mixtureOrUniform_congr
  intro cfg hcfg
  exact lowConfigLaw_delete_replace X H _ v b c _ cfg hcfg hv z

theorem highMixture_delete_replace (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht) (z) :
    highMixture X L H
      (replaceBlockData X ω c.1 (X.g.evenType (X.p.J n) v.1)
        (refIndices X (X.g.evenType (X.p.J n) v.1) c.2) z) v b c = highMixture X L H ω v b c := by
  unfold highMixture
  rw [candidatePositions_replaceBlockData, arraysOf_replaceBlockData]
  apply mixtureOrUniform_congr
  intro cfg _
  exact highConfigLaw_delete_replace X H _ v b c cfg z

theorem lowMixture_local (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n)
    (b : OddRole5 n) (c : X.CRef L.ht) (hv : v ∈ Setup5.evenNbrs b) :
    FinProb.DependsOn (fun ω => lowMixture X L H ω v b c)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8)) := by
  intro ω ω' hagree
  have hD := candidatePositions_local X L v b hv ω ω' hagree
  dsimp only at hD ⊢
  unfold lowMixture
  rw [← hD]
  apply mixtureOrUniform_congr
  intro cfg hcfg
  apply lowConfigLaw_arrays_congr X H _ _ v b c _ cfg hcfg
  intro l hl K
  have heq := hagree l (candidatePositions_scope X L ω v b hv hl)
  exact congrArg (fun u : X.CVal L.ht => u.2.2.2 K) heq

theorem highMixture_local (L : X.CentreLayer5) (H : X.KeyHist) (v : EvenRole5 n)
    (b : OddRole5 n) (c : X.CRef L.ht) (hv : v ∈ Setup5.evenNbrs b) :
    FinProb.DependsOn (fun ω => highMixture X L H ω v b c)
      (X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8)) := by
  intro ω ω' hagree
  have hD := candidatePositions_local X L v b hv ω ω' hagree
  dsimp only at hD ⊢
  unfold highMixture
  rw [← hD]
  apply mixtureOrUniform_congr
  intro cfg hcfg
  apply highConfigLaw_arrays_congr X H _ _ v b c _ cfg hcfg
  intro l hl K
  have heq := hagree l (candidatePositions_scope X L ω v b hv hl)
  exact congrArg (fun u : X.CVal L.ht => u.2.2.2 K) heq

end
end HypercubeRamsey.Lane_sol_s05_even
