import HypercubeRamsey.S05.Even_setup_records_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def lowRecordSet (b : OddRole5 n) : Finset X.AbsRecord :=
  Finset.univ.filter fun r => X.RecOccursAt r (X.g.sign b.1) (X.g.severity b.1) ∧
    r.1 = X.g.roleKey (X.p.J n) b.1

theorem lowRecordSet_card (C : ℝ) (hC : X.RecordCount C) (b : OddRole5 n) :
    ((lowRecordSet X b).card : ℝ) ≤
      Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        (((X.g.roleKey (X.p.J n) b.1).level : ℝ) + 1) * Real.log (X.p.m n) +
        (if (X.g.roleKey (X.p.J n) b.1).isLeft ∧ (X.g.roleKey (X.p.J n) b.1).level = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))) :=
  hC _ _ _

def placementSet {h : X.HeightChoice5} (D : Finset h.hp.Loc) : Finset (Fin (X.p.T n) → h.hp.Loc) :=
  Fintype.piFinset fun _ => D

theorem placementSet_card {h : X.HeightChoice5} (D : Finset h.hp.Loc) :
    (placementSet X D).card = D.card ^ X.p.T n := by
  simp [placementSet, Fintype.card_piFinset]

def lowConfigSet {h : X.HeightChoice5} (b : OddRole5 n) (D : Finset h.hp.Loc) :
    Finset (X.AbsRecord × (Fin (X.p.T n) → h.hp.Loc)) :=
  (lowRecordSet X b).product (placementSet X D)

theorem lowConfigSet_card {h : X.HeightChoice5} (b : OddRole5 n) (D : Finset h.hp.Loc) :
    (lowConfigSet X b D).card = (lowRecordSet X b).card * D.card ^ X.p.T n := by
  simp [lowConfigSet, placementSet_card]

def highObservationSet (b : OddRole5 n) : Finset (Finset (Fin (X.p.T n) × X.Ty)) :=
  Finset.univ.image fun μ : X.St.Site → Fin (X.p.T n) =>
    (Setup5.evenNbrs b).image fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)

theorem highObservationSet_card (b : OddRole5 n) (hb : ¬ X.g.low (X.p.J n) b.1) (hT : 0 < X.p.T n) :
    (highObservationSet X b).card ≤ 2 ^ X.p.T n * (X.p.T n) ^ 601 := by
  letI : Nonempty (Fin (X.p.T n)) := ⟨⟨0, hT⟩⟩
  have hh := high_observation_images_card X.g X.St (Id := Fin (X.p.T n)) b hb
  simpa only [highObservationSet, Fintype.card_fin] using hh

def highConfigSet {h : X.HeightChoice5} (b : OddRole5 n) (D : Finset h.hp.Loc) :
    Finset (Finset (Fin (X.p.T n) × X.Ty) × (Fin (X.p.T n) → h.hp.Loc)) :=
  (highObservationSet X b).product (placementSet X D)

theorem highConfigSet_card {h : X.HeightChoice5} (b : OddRole5 n) (D : Finset h.hp.Loc)
    (hb : ¬ X.g.low (X.p.J n) b.1) (hT : 0 < X.p.T n) :
    (highConfigSet X b D).card ≤ (2 ^ X.p.T n * (X.p.T n) ^ 601) * D.card ^ X.p.T n := by
  unfold highConfigSet
  have hprod : ((highObservationSet X b).product (placementSet X D)).card =
      (highObservationSet X b).card * (placementSet X D).card := Finset.card_product _ _
  rw [hprod, placementSet_card]
  exact Nat.mul_le_mul_right _ (highObservationSet_card X b hb hT)

def highConfigRecord {h : X.HeightChoice5} (b : OddRole5 n)
    (cfg : Finset (Fin (X.p.T n) × X.Ty) × (Fin (X.p.T n) → h.hp.Loc)) : X.RecordOn h.hp.Loc :=
  (X.g.roleKey (X.p.J n) b.1, cfg.1.image (fun c => (cfg.2 c.1, c.2)), ∅, none)

theorem lowConfig_observed_local {h : X.HeightChoice5} (b : OddRole5 n) (D : Finset h.hp.Loc)
    (cfg : X.AbsRecord × (Fin (X.p.T n) → h.hp.Loc)) (hcfg : cfg ∈ lowConfigSet X b D)
    (c : h.hp.Loc × X.Ty) (hc : c ∈ (liftRecord X cfg.1 cfg.2).2.1) : c.1 ∈ D := by
  letI : DecidableEq h.hp.Loc := Classical.decEq _
  have hplace := (Finset.mem_product.mp hcfg).2
  have hp := (Fintype.mem_piFinset.mp hplace)
  obtain ⟨c', hc', heq⟩ := Finset.mem_image.mp hc
  have hId := congrArg Prod.fst heq
  rw [← hId]
  exact hp c'.1

theorem highConfig_observed_local {h : X.HeightChoice5} (b : OddRole5 n) (D : Finset h.hp.Loc)
    (cfg : Finset (Fin (X.p.T n) × X.Ty) × (Fin (X.p.T n) → h.hp.Loc)) (hcfg : cfg ∈ highConfigSet X b D)
    (c : h.hp.Loc × X.Ty) (hc : c ∈ (highConfigRecord X b cfg).2.1) : c.1 ∈ D := by
  have hplace := (Finset.mem_product.mp hcfg).2
  have hp := (Fintype.mem_piFinset.mp hplace)
  obtain ⟨c', hc', heq⟩ := Finset.mem_image.mp hc
  have hId := congrArg Prod.fst heq
  rw [← hId]
  exact hp c'.1

theorem actual_lowConfig (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht)
    (hv : v ∈ Setup5.evenNbrs b) (hb : L.valid H ω b)
    (hc : X.evenRefOf (L.elig H) H ω v = some c) :
    ∃ cfg ∈ lowConfigSet X b (candidatePositions X L ω b),
      (∃ μ, X.RecordFrom cfg.1 b μ) ∧
      liftRecord X cfg.1 cfg.2 = X.actualRecord (L.elig H) H ω b := by
  have hs : X.selLong (L.elig H) ω v = some c.1 := by
    unfold Setup5.evenRefOf at hc
    obtain ⟨l, hl, heq⟩ := Option.map_eq_some_iff.mp hc
    have hloc := congrArg Prod.fst heq
    exact hl.trans (congrArg some hloc)
  have hid : actualId X (L.elig H) ω c.1 (X.St.stateOf v.1) = c.1 := by
    change (X.selLong (L.elig H) ω v).getD c.1 = c.1
    rw [hs]
    rfl
  have hmem : c.1 ∈ selectedIds X L H ω b c.1 :=
    Finset.mem_image.mpr ⟨v, hv, hid⟩
  obtain ⟨index, place, hinv, hplace⟩ := finite_id_factor
    (selectedIds X L H ω b c.1) (X.p.T n) (selectedIds_card X L H ω b hb c.1) c.1 hmem
  let r := X.actualRecord (L.elig H) H ω b
  let μ := actualId X (L.elig H) ω c.1
  have hr : X.RecordFrom r b μ := actualRecord_from X L H ω b hb c.1
  have hr' := liftRecord_from X r index b μ hr
  refine ⟨(liftRecord X r index, place), Finset.mem_product.mpr ⟨?_, ?_⟩, ⟨⟨index ∘ μ, hr'⟩, ?_⟩⟩
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨⟨b, index ∘ μ, hr', rfl, rfl⟩, hr'.1.symm⟩⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    exact selectedIds_candidate X L H ω b hb c.1 (hplace i)
  · apply liftRecord_inverse X r index place b μ hr
    intro a ha
    exact hinv _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem actual_highConfig (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht)
    (hv : v ∈ Setup5.evenNbrs b) (hb : L.valid H ω b) (hhigh : ¬ X.g.low (X.p.J n) b.1)
    (hc : X.evenRefOf (L.elig H) H ω v = some c) :
    ∃ cfg ∈ highConfigSet X b (candidatePositions X L ω b),
      (highConfigRecord X b cfg).1 = (X.actualRecord (L.elig H) H ω b).1 ∧
      (highConfigRecord X b cfg).2.1 = (X.actualRecord (L.elig H) H ω b).2.1 ∧
      (highConfigRecord X b cfg).2.2.2 = (X.actualRecord (L.elig H) H ω b).2.2.2 := by
  obtain ⟨cfg, hcfg, ⟨μb, hfb⟩, heq⟩ := actual_lowConfig X L H ω v b c hv hb hc
  refine ⟨(cfg.1.2.1, cfg.2), Finset.mem_product.mpr ⟨?_, (Finset.mem_product.mp hcfg).2⟩, ?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨μb, Finset.mem_univ _, ?_⟩
    simpa only [image_classical] using hfb.2.1.symm
  · rfl
  · simpa only [highConfigRecord, liftRecord, image_classical] using congrArg (fun r => r.2.1) heq
  · have hsev : ¬ X.g.severity b.1 ≤ X.p.J n := hhigh
    simp [highConfigRecord, Setup5.actualRecord, Setup5.actualRecordAt, ChunkGeometry5.roleKey, hsev]

end
end HypercubeRamsey.Lane_sol_s05_even
