import HypercubeRamsey.S05.History

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)
variable {Id Id' Id'' : Type} [DecidableEq Id] [DecidableEq Id'] [DecidableEq Id'']

def renameRecord (f : Id → Id') (r : X.RecordOn Id) : X.RecordOn Id' :=
  (r.1, r.2.1.image (fun c => (f c.1, c.2)),
    r.2.2.1.image (fun c => (f c.1, c.2)), r.2.2.2.map (fun c => (f c.1, c.2)))

theorem renameRecord_comp (f : Id → Id') (g : Id' → Id'') (r : X.RecordOn Id) :
    renameRecord X g (renameRecord X f r) = renameRecord X (g ∘ f) r := by
  simp only [renameRecord, Finset.image_image, Option.map_map, Function.comp_apply]
  rfl

theorem recordFrom_rename (f : Id → Id') (r : X.RecordOn Id) (y : OddRole5 n)
    (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ) :
    X.RecordFrom (renameRecord X f r) y (f ∘ μ) := by
  obtain ⟨hk, ho, href, hm⟩ := hr
  refine ⟨hk, ?_, ?_, ?_⟩
  · simp only [renameRecord, ho, Finset.image_image, Function.comp_apply]
    ext c
    simp only [Finset.mem_image, Function.comp_apply]
  · simp only [renameRecord, href, Finset.image_image, Function.comp_apply]
    ext c
    simp only [Finset.mem_image, Function.comp_apply]
  · cases he : r.2.2.2 with
    | none => simpa only [renameRecord, he, Option.map_none] using hm
    | some c =>
      obtain ⟨hl, a, ha, hK, hhigh, hi, hlegit⟩ := (show r.1.isLeft ∧
        ∃ a ∈ Setup5.evenNbrs y, c.2.1 = X.g.evenType (X.p.J n) a.1 ∧
          c.2.1.2.2 = none ∧ c.1 = μ (X.St.stateOf a.1) ∧ X.LegitRef c.2.1 c.2.2 by
            simpa only [he] using hm)
      simp only [renameRecord, he, Option.map_some]
      exact ⟨hl, a, ha, hK, hhigh, congrArg f hi, hlegit⟩

def recordIds (r : X.RecordOn Id) : Finset Id := r.2.1.image Prod.fst

theorem renameRecord_recover (f : Id → Id') (g : Id' → Id) (r : X.RecordOn Id)
    (y : OddRole5 n) (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ)
    (hgf : ∀ i ∈ recordIds X r, g (f i) = i) :
    renameRecord X g (renameRecord X f r) = r := by
  rw [renameRecord_comp]
  have hobs : r.2.1.image (fun c => (g (f c.1), c.2)) = r.2.1 := by
    calc
      _ = r.2.1.image id := by
        apply Finset.image_congr
        intro c hc
        change (g (f c.1), c.2) = c
        exact Prod.ext (hgf c.1 (Finset.mem_image.mpr ⟨c, hc, rfl⟩)) rfl
      _ = _ := Finset.image_id
  have href : r.2.2.1.image (fun c => (g (f c.1), c.2)) = r.2.2.1 := by
    calc
      _ = r.2.2.1.image id := by
        apply Finset.image_congr
        intro c hc
        have ho := Lane_sol_s05_hist1b.record_ref_mem X r y μ hr c hc
        exact Prod.ext (hgf c.1 (Finset.mem_image.mpr ⟨(c.1, c.2.1), ho, rfl⟩)) rfl
      _ = _ := Finset.image_id
  have hmask : r.2.2.2.map (fun c => (g (f c.1), c.2)) = r.2.2.2 := by
    cases he : r.2.2.2 with
    | none => rfl
    | some c =>
      have ho := Lane_sol_s05_hist1b.record_mask_mem X r y μ hr (c.1, c.2.1) c.2.2 he
      have hi := hgf c.1 (Finset.mem_image.mpr ⟨(c.1, c.2.1), ho, rfl⟩)
      simp only [Option.map_some, hi]
  simpa only [renameRecord, Function.comp_apply, hobs, href, hmask] using (Prod.eta r).symm

section Count

variable [Fintype Id]

/-- Renaming into `[T]` pays for physical IDs only once per distinct ID,
rather than once per neighboring role or type. -/
theorem physicalRecord_card_le (y : OddRole5 n) (pool : Finset Id) (S : Finset (X.RecordOn Id))
    (fallback : Id) (hT : 0 < X.p.T n)
    (hfrom : ∀ r ∈ S, ∃ μ, X.RecordFrom r y μ)
    (hids : ∀ r ∈ S, recordIds X r ⊆ pool ∧ (recordIds X r).card ≤ X.p.T n) :
    S.card ≤ (Finset.univ.filter (fun r : X.AbsRecord =>
      X.RecOccursAt r (X.g.sign y.1) (X.g.severity y.1) ∧
        r.1 = X.g.roleKey (X.p.J n) y.1)).card * (pool.card + 1) ^ X.p.T n := by
  let A := Finset.univ.filter (fun r : X.AbsRecord =>
    X.RecOccursAt r (X.g.sign y.1) (X.g.severity y.1) ∧ r.1 = X.g.roleKey (X.p.J n) y.1)
  let emit : X.AbsRecord × (Fin (X.p.T n) → Option pool) → X.RecordOn Id := fun c =>
    renameRecord X (fun t => ((c.2 t).map Subtype.val).getD fallback) c.1
  have hsub : S ⊆ (A.product Finset.univ).image emit := by
    intro r hr
    obtain ⟨μ, hμ⟩ := hfrom r hr
    obtain ⟨hpool, hcard⟩ := hids r hr
    let ids := recordIds X r
    have hsize : Fintype.card ids ≤ X.p.T n := by simpa only [Fintype.card_coe] using hcard
    let e : ids → Fin (X.p.T n) := fun i =>
      ⟨(Fintype.equivFin ids i).val, (Fintype.equivFin ids i).isLt.trans_le hsize⟩
    have he : Function.Injective e := by
      intro i j hij
      apply (Fintype.equivFin ids).injective
      apply Fin.ext
      change (e i).val = (e j).val
      exact congrArg (fun t : Fin (X.p.T n) => t.val) hij
    let enc : Id → Fin (X.p.T n) := fun i => if hi : i ∈ ids then e ⟨i, hi⟩ else ⟨0, hT⟩
    have henc : ∀ i ∈ ids, ∀ j ∈ ids, enc i = enc j → i = j := by
      intro i hi j hj hij
      have heq : e ⟨i, hi⟩ = e ⟨j, hj⟩ := by simpa only [enc, dif_pos hi, dif_pos hj] using hij
      exact congrArg Subtype.val (he heq)
    let dec : Fin (X.p.T n) → Option pool := fun t =>
      if ht : ∃ i ∈ ids, enc i = t then
        some ⟨Classical.choose ht, hpool (Classical.choose_spec ht).1⟩ else none
    have hdec : ∀ i ∈ ids, ((dec (enc i)).map Subtype.val).getD fallback = i := by
      intro i hi
      have ht : ∃ j ∈ ids, enc j = enc i := ⟨i, hi, rfl⟩
      have hj : Classical.choose ht = i :=
        henc _ (Classical.choose_spec ht).1 i hi (Classical.choose_spec ht).2
      simp only [dec, dif_pos ht, Option.map_some, Option.getD_some, hj]
    let ar := renameRecord X enc r
    have har : ar ∈ A := by
      have hrecord := recordFrom_rename X enc r y μ hμ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨y, enc ∘ μ, hrecord, rfl, rfl⟩, hrecord.1.symm⟩
    apply Finset.mem_image.mpr
    refine ⟨(ar, dec), Finset.mem_product.mpr ⟨har, Finset.mem_univ _⟩, ?_⟩
    exact renameRecord_recover X enc _ r y μ hμ hdec
  calc
    _ ≤ ((A.product Finset.univ).image emit).card := Finset.card_le_card hsub
    _ ≤ (A.product (Finset.univ : Finset (Fin (X.p.T n) → Option pool))).card := Finset.card_image_le
    _ = A.card * (pool.card + 1) ^ X.p.T n := by
      first
      | rfl
      | simp [Fintype.card_fun]

end Count

section Potential

variable [Fintype Id]

def potentialRecords (y : OddRole5 n) (pool : Finset Id) : Finset (X.RecordOn Id) :=
  Finset.univ.filter fun r => (∃ μ, X.RecordFrom r y μ) ∧
    recordIds X r ⊆ pool ∧ (recordIds X r).card ≤ X.p.T n

theorem potentialRecords_card_le (y : OddRole5 n) (pool : Finset Id) (fallback : Id)
    (hT : 0 < X.p.T n) :
    (potentialRecords X y pool).card ≤ (Finset.univ.filter (fun r : X.AbsRecord =>
      X.RecOccursAt r (X.g.sign y.1) (X.g.severity y.1) ∧
        r.1 = X.g.roleKey (X.p.J n) y.1)).card * (pool.card + 1) ^ X.p.T n :=
  physicalRecord_card_le X y pool _ fallback hT
    (fun r hr => (Finset.mem_filter.mp hr).2.1)
    (fun r hr => (Finset.mem_filter.mp hr).2.2)

theorem potentialRecords_budget (C : ℝ) (hcount : X.RecordCount C)
    (y : OddRole5 n) (pool : Finset Id) (fallback : Id) (hT : 0 < X.p.T n) :
    ((potentialRecords X y pool).card : ℝ) ≤
      Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        (((X.g.roleKey (X.p.J n) y.1).level : ℝ) + 1) * Real.log (X.p.m n) +
        (if (X.g.roleKey (X.p.J n) y.1).isLeft ∧
            (X.g.roleKey (X.p.J n) y.1).level = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))) *
          (pool.card + 1 : ℕ) ^ X.p.T n := by
  have hc : ((potentialRecords X y pool).card : ℝ) ≤
      ((Finset.univ.filter (fun r : X.AbsRecord =>
        X.RecOccursAt r (X.g.sign y.1) (X.g.severity y.1) ∧
          r.1 = X.g.roleKey (X.p.J n) y.1)).card : ℝ) * (pool.card + 1 : ℕ) ^ X.p.T n := by
    exact_mod_cast potentialRecords_card_le X y pool fallback hT
  exact hc.trans (mul_le_mul_of_nonneg_right
    (hcount (X.g.roleKey (X.p.J n) y.1) (X.g.sign y.1) (X.g.severity y.1)) (by positivity))

end Potential
end
end HypercubeRamsey.Lane_sol_s05_k1
