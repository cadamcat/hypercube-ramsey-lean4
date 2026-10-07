import HypercubeRamsey.S06.Steps
import HypercubeRamsey.S05.History_sol_s05_h1
import HypercubeRamsey.S06.Stages_q_s06_stages

namespace HypercubeRamsey.S06.Lane_sol_s06_shapes

open OAI.HypercubeRamsey Classical
open scoped BigOperators

noncomputable section

set_option maxHeartbeats 400000


variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

def keyMap (e : Equiv.Perm X.Bin) : Equiv.Perm X.Key :=
  e.prodCongr (Equiv.refl _)

@[simp] theorem keyMap_apply (e : Equiv.Perm X.Bin) (h : X.Key) :
    keyMap X e h = (e h.1, h.2) := rfl

def renameCoarse (e : Equiv.Perm X.Bin) (c : X.Coarse) : X.Coarse :=
  (fun u => c.1 (e.symm u), fun h => c.2 ((keyMap X e).symm h))

def coarseEquiv (e : Equiv.Perm X.Bin) : Equiv.Perm X.Coarse where
  toFun := renameCoarse X e
  invFun := renameCoarse X e.symm
  left_inv c := by
    apply Prod.ext <;> funext a <;>
      simp [renameCoarse, keyMap, Equiv.prodCongr, Prod.map]
  right_inv c := by
    apply Prod.ext <;> funext a <;>
      simp [renameCoarse, keyMap, Equiv.prodCongr, Prod.map]

theorem tagLawAt_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h : X.Key) :
    X.tagLawAt (b.1, (renameCoarse X e b.2).1) (keyMap X e h) =
      X.tagLawAt (X.parOf b) h := by
  rcases h with ⟨w, f⟩
  cases f <;> simp [Ctx6.tagLawAt, Ctx6.parOf, primaryName6, otherPrimaryName6,
    Par6.val, renameCoarse, keyMap]

theorem coarseLaw_weight_equiv (v : Fin N) (e : Equiv.Perm X.Bin) (c : X.Coarse) :
    (X.coarseLaw v).w (coarseEquiv X e c) = (X.coarseLaw v).w c := by
  change (∏ u, (X.candLaw v).w (c.1 (e.symm u))) *
    (∏ h, (X.tagLawAt (v, fun u => c.1 (e.symm u)) h).w
      (c.2 ((keyMap X e).symm h))) =
    (∏ u, (X.candLaw v).w (c.1 u)) * (∏ h, (X.tagLawAt (v,c.1) h).w (c.2 h))
  congr 1
  · exact Equiv.prod_comp e.symm (fun u => (X.candLaw v).w (c.1 u))
  · rw [← Equiv.prod_comp (keyMap X e) (fun h => (X.tagLawAt (v, fun u => c.1 (e.symm u)) h).w (c.2 ((keyMap X e).symm h)))]
    apply Finset.prod_congr rfl
    intro h _
    change (X.tagLawAt (v, (renameCoarse X e c).1) (keyMap X e h)).w
      (c.2 ((keyMap X e).symm (keyMap X e h))) = _
    rw [Equiv.symm_apply_apply, tagLawAt_rename X e (v,c) h]
    rfl

theorem coarseLaw_expect_equiv (v : Fin N) (e : Equiv.Perm X.Bin) (F : X.Coarse → ℝ) :
    (X.coarseLaw v).expect F =
      (X.coarseLaw v).expect (fun c => F (renameCoarse X e c)) :=
  HypercubeRamsey.Lane_sol_s05_h1.expect_equiv _ _ (coarseEquiv X e)
    (coarseLaw_weight_equiv X v e) F

theorem coarseLaw_pr_equiv (v : Fin N) (e : Equiv.Perm X.Bin) (F : X.Coarse → Prop) :
    (X.coarseLaw v).pr F = (X.coarseLaw v).pr (fun c => F (renameCoarse X e c)) :=
  HypercubeRamsey.Lane_sol_s05_h1.pr_equiv _ _ (coarseEquiv X e)
    (coarseLaw_weight_equiv X v e) F

theorem parOf_set_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h s : X.Key) (y : Fin N) :
    X.tagLawAt ((X.parOf (b.1, renameCoarse X e b.2)).set
      (primaryName6 (keyMap X e h)) y) (keyMap X e s) =
      X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s := by
  rcases h with ⟨w, f⟩
  rcases s with ⟨u, g⟩
  cases f <;> cases g <;>
    simp [Ctx6.tagLawAt, Ctx6.parOf, primaryName6, otherPrimaryName6,
      Par6.val, Par6.set, renameCoarse, keyMap, Function.update_apply,
      e.injective.eq_iff]

theorem hidWeight_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h : X.Key)
    (S : Finset X.Key) (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h)) (y : Fin N) :
    X.hidWeight (b.1, renameCoarse X e b.2) (keyMap X e h)
      (S.image (keyMap X e)) y = X.hidWeight b h S y := by
  have hbins : (X.binsOf (X.C h)).image e = X.binsOf (X.C (keyMap X e h)) := by
    rw [← hC]
    simp only [Ctx6.binsOf, Finset.image_image]
    rfl
  unfold Ctx6.hidWeight
  dsimp only
  have hprod : (∏ s ∈ S.image (keyMap X e),
      (X.tagLawAt ((X.parOf (b.1, renameCoarse X e b.2)).set
        (primaryName6 (keyMap X e h)) y) s).w ((renameCoarse X e b.2).2 s)) =
      ∏ s ∈ S, (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w (b.2.2 s) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro s _
      rw [parOf_set_rename X e b h s y]
      change (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w
        (b.2.2 ((keyMap X e).symm (keyMap X e s))) = _
      rw [Equiv.symm_apply_apply]
    · exact fun a _ b _ hab => (keyMap X e).injective hab
  rw [hprod]
  congr 1
  have hflag : (keyMap X e h).2 = h.2 := rfl
  rw [hflag]
  cases hf : h.2
  · rfl
  · change X.initLaw.w y * (∏ u ∈ X.binsOf (X.C (keyMap X e h)),
      (X.candLaw y).w ((renameCoarse X e b.2).1 u)) = _
    rw [← hbins, Finset.prod_image]
    · simp [renameCoarse]
    · exact fun a _ b _ hab => e.injective hab

theorem hidPost_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h)) :
    X.hidPost (b.1, renameCoarse X e b.2) (keyMap X e h) = X.hidPost b h := by
  unfold Ctx6.hidPost
  congr 1
  funext y
  rw [← hC]
  exact hidWeight_rename X e b h (X.C h) hC y

theorem hidPostDel_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h s : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h)) :
    X.hidPostDel (b.1, renameCoarse X e b.2) (keyMap X e h) (keyMap X e s) =
      X.hidPostDel b h s := by
  unfold Ctx6.hidPostDel
  congr 1
  funext y
  rw [← hC, ← Finset.image_erase (keyMap X e).injective]
  exact hidWeight_rename X e b h ((X.C h).erase s) hC y

theorem step1OK_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h)) :
    X.Step1OK (b.1, renameCoarse X e b.2) (keyMap X e h) ↔ X.Step1OK b h := by
  unfold Ctx6.Step1OK Ctx6.Step1Cap Ctx6.Step1Del
  rw [hidPost_rename X e b h hC, ← hC]
  simp only [Finset.forall_mem_image, hidPostDel_rename X e b h _ hC]

theorem step1Rate_rename (v : Fin N) (e : Equiv.Perm X.Bin) (h : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h)) :
    (X.coarseLaw v).pr (fun c => ¬ X.Step1OK (v,c) (keyMap X e h)) =
      (X.coarseLaw v).pr (fun c => ¬ X.Step1OK (v,c) h) := by
  rw [coarseLaw_pr_equiv X v e]
  congr 1
  funext c
  exact propext (not_congr (step1OK_rename X e (v,c) h hC))

/-- Extend a bijection between two neighbor lists while matching their centers. -/
theorem pointed_finset_perm {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset A) (a b : A) (ha : a ∉ S) (hb : b ∉ T)
    (hc : S.card = T.card) :
    ∃ e : Equiv.Perm A, e a = b ∧ S.image e = T := by
  let q : S ≃ T := Fintype.equivOfCardEq (by simpa using hc)
  let f : Option S → A := fun x => match x with | none => a | some x => x.1
  let g : Option S → A := fun x => match x with | none => b | some x => (q x).1
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        change a = y.1 at h
        exact False.elim (ha (h.symm ▸ y.2))
    | some x =>
      cases y with
      | none =>
        change x.1 = a at h
        exact False.elim (ha (h ▸ x.2))
      | some y => congr 1; exact Subtype.ext h
  have hg : Function.Injective g := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        change b = (q y).1 at h
        exact False.elim (hb (h.symm ▸ (q y).2))
    | some x =>
      cases y with
      | none =>
        change (q x).1 = b at h
        exact False.elim (hb (h ▸ (q x).2))
      | some y => congr 1; exact q.injective (Subtype.ext h)
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨e, he none, ?_⟩
  ext t
  constructor
  · rintro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    have heq : e s = (q ⟨s,hs⟩).1 := he (some ⟨s,hs⟩)
    rw [heq]
    exact (q ⟨s,hs⟩).2
  · intro ht
    let s := q.symm ⟨t,ht⟩
    refine Finset.mem_image.mpr ⟨s.1, s.2, ?_⟩
    have heq := he (some s)
    simpa [g, f, s] using heq

def binNbr (w : X.Bin) : Finset X.Bin := Finset.univ.filter (binAdjacent6 w)

theorem binAdjacent_irrefl (w : X.Bin) : ¬ binAdjacent6 w w := by
  rintro ⟨i, _, h⟩
  simp at h

theorem binNbr_not_mem (w : X.Bin) : w ∉ binNbr X w := by
  simp [binNbr, binAdjacent_irrefl X w]

theorem C_interior (w : X.Bin) :
    X.C (w, .interior) = {(w, .interior), (w, .boundary)} := by
  ext h
  rcases h with ⟨u, f⟩
  cases f <;> simp [Ctx6.C, keyNeighborhood6, keyAdjacent6, eq_comm]

theorem C_boundary (w : X.Bin) :
    X.C (w, .boundary) = {(w, .interior), (w, .boundary)} ∪
      (binNbr X w).image (fun u => (u, KeyFlag6.boundary)) := by
  ext h
  rcases h with ⟨u, f⟩
  cases f <;> simp [Ctx6.C, keyNeighborhood6, keyAdjacent6, binNbr, eq_comm]

theorem C_boundary_card (w : X.Bin) : (X.C (w, .boundary)).card = 2 + (binNbr X w).card := by
  rw [C_boundary]
  have hd : Disjoint ({(w, KeyFlag6.interior), (w, KeyFlag6.boundary)} : Finset X.Key)
      ((binNbr X w).image (fun u => (u, KeyFlag6.boundary))) := by
    rw [Finset.disjoint_left]
    intro h hh hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    have heq : u = w := by simpa using hh
    subst u
    exact binNbr_not_mem X w hu
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
  simp

def step1Shape (h : X.Key) : KeyFlag6 × Fin 603 :=
  (h.2, ⟨(X.C h).card, Nat.lt_succ_of_le (X.g.flips.key_neighborhood_card h)⟩)

theorem step1Shape_perm (h h' : X.Key) (hs : step1Shape X h = step1Shape X h') :
    ∃ e : Equiv.Perm X.Bin, keyMap X e h = h' ∧ (X.C h).image (keyMap X e) = X.C h' := by
  have hflag : h.2 = h'.2 := congrArg Prod.fst hs
  have hcard : (X.C h).card = (X.C h').card := congrArg (fun s => s.2.val) hs
  rcases h with ⟨w,f⟩
  rcases h' with ⟨w',f'⟩
  change f = f' at hflag
  subst f'
  cases f
  · let e := Equiv.swap w w'
    refine ⟨e, ?_, ?_⟩
    · simp [keyMap, e]
    · simp [C_interior, keyMap, e]
  · have hc : (binNbr X w).card = (binNbr X w').card := by
      rw [C_boundary_card, C_boundary_card] at hcard
      omega
    obtain ⟨e, he, hN⟩ := pointed_finset_perm (binNbr X w) (binNbr X w') w w'
      (binNbr_not_mem X w) (binNbr_not_mem X w') hc
    refine ⟨e, ?_, ?_⟩
    · simp [keyMap, he]
    · rw [C_boundary, C_boundary, Finset.image_union]
      simp only [Finset.image_insert, Finset.image_singleton, keyMap_apply, he]
      congr 1
      rw [Finset.image_image, ← hN, Finset.image_image]
      rfl

theorem step1Rate_shape (h h' : X.Key) (hs : step1Shape X h = step1Shape X h') (v : Fin N) :
    (X.coarseLaw v).pr (fun c => ¬ X.Step1OK (v,c) h) =
      (X.coarseLaw v).pr (fun c => ¬ X.Step1OK (v,c) h') := by
  obtain ⟨e, he, hC⟩ := step1Shape_perm X h h' hs
  subst h'
  exact (step1Rate_rename X v e h hC).symm

theorem step1Shape_card_bound : ((X.step1Keys.image (step1Shape X)).card : ℝ) ≤ 10 ^ 200 := by
  have h : (X.step1Keys.image (step1Shape X)).card ≤ 2 * 603 := by
    calc
      _ ≤ Fintype.card (KeyFlag6 × Fin 603) := Finset.card_le_univ _
      _ = 2 * 603 := by
        rw [Fintype.card_prod, Fintype.card_fin]
        have hf : Fintype.card KeyFlag6 = 2 := rfl
        rw [hf]
  have hr : ((X.step1Keys.image (step1Shape X)).card : ℝ) ≤ 2 * 603 := by exact_mod_cast h
  norm_num at hr ⊢
  exact hr.trans (by norm_num)

theorem withTag_rename (e : Equiv.Perm X.Bin) (b : X.Base) (s : X.Key) (i : X.ι) :
    X.withTag (b.1, renameCoarse X e b.2) (keyMap X e s) i =
      ((X.withTag b s i).1, renameCoarse X e (X.withTag b s i).2) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext h
      simp [Ctx6.withTag, renameCoarse, Function.update_apply,
        (keyMap X e).symm.injective.eq_iff, Equiv.symm_apply_eq]

theorem hidPostRep_rename (e : Equiv.Perm X.Bin) (b : X.Base) (h s : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h)) (i : X.ι) :
    X.hidPostRep (b.1, renameCoarse X e b.2) (keyMap X e h) (keyMap X e s) i =
      X.hidPostRep b h s i := by
  unfold Ctx6.hidPostRep
  rw [withTag_rename]
  exact hidPost_rename X e (X.withTag b s i) h hC

/-- The exact local symmetry needed by Step 2, without conditions on unused signs or bins. -/
structure Step2Iso (β β' : X.Ty) where
  bins : Equiv.Perm X.Bin
  obs : β.obs ≃ β'.obs
  key : keyMap X bins β.key = β'.key
  severity : β.u = β'.u
  obs_key : ∀ (ℓ : β.obs), keyMap X bins ℓ.1.1 = (obs ℓ).1.1
  neighborhoods : ∀ (ℓ : β.obs), (X.C ℓ.1.1).image (keyMap X bins) = X.C (keyMap X bins ℓ.1.1)

theorem tagGate_iso (β β' : X.Ty) (r : Step2Iso X β β') (b : X.Base) (i : X.ι) :
    X.tagGate (b.1, renameCoarse X r.bins b.2) β' i ↔ X.tagGate b β i := by
  unfold Ctx6.tagGate
  have hpoint (ℓ : β.obs) :
      (∀ y, (X.hidPostRep (b.1, renameCoarse X r.bins b.2) (r.obs ℓ).1.1 β'.key i).w y ≤
        (n : ℝ) ^ d₁ * (X.hidPostDel (b.1, renameCoarse X r.bins b.2) (r.obs ℓ).1.1 β'.key).w y) ↔
      (∀ y, (X.hidPostRep b ℓ.1.1 β.key i).w y ≤ (n : ℝ) ^ d₁ *
        (X.hidPostDel b ℓ.1.1 β.key).w y) := by
    rw [← r.key, ← r.obs_key ℓ, hidPostRep_rename X r.bins b _ _ (r.neighborhoods ℓ) i,
      hidPostDel_rename X r.bins b _ _ (r.neighborhoods ℓ)]
  constructor
  · intro h ℓ hℓ
    exact (hpoint ⟨ℓ,hℓ⟩).1 (h _ (r.obs ⟨ℓ,hℓ⟩).2)
  · intro h ℓ hℓ
    let a := r.obs.symm ⟨ℓ,hℓ⟩
    have ha := (hpoint a).2 (h _ a.2)
    simpa [a] using ha

theorem tagMass_iso (β β' : X.Ty) (r : Step2Iso X β β') (H H' : X.Hist)
    (hb : H'.1 = (H.1.1, renameCoarse X r.bins H.1.2))
    (hZ : ∀ ℓ : β.obs, H'.2 (r.obs ℓ).1 = H.2 ℓ.1)
    (S : Finset X.HKey) (hS : S ⊆ β.obs) :
    X.tagMass H' β' (S.attach.image (fun ℓ => (r.obs ⟨ℓ.1,hS ℓ.2⟩).1)) = X.tagMass H β S := by
  unfold Ctx6.tagMass
  apply Finset.sum_congr rfl
  intro i _
  unfold Ctx6.tagWeight
  rw [hb, ← r.key]
  simp only [Ctx6.parOf]
  rw [tagLawAt_rename X r.bins H.1 β.key, tagGate_iso X β β' r H.1 i]
  congr 1
  rw [Finset.prod_image]
  · rw [← Finset.prod_attach S]
    apply Finset.prod_congr rfl
    intro ℓ _
    rw [← r.obs_key ⟨ℓ.1,hS ℓ.2⟩,
      hidPostRep_rename X r.bins H.1 _ _ (r.neighborhoods ⟨ℓ.1,hS ℓ.2⟩) i,
      hidPostDel_rename X r.bins H.1 _ _ (r.neighborhoods ⟨ℓ.1,hS ℓ.2⟩),
      hZ ⟨ℓ.1,hS ℓ.2⟩]
  · intro a _ b _ heq
    have heq' : (⟨a.1,hS a.2⟩ : β.obs) = ⟨b.1,hS b.2⟩ :=
      r.obs.injective (Subtype.ext heq)
    apply Subtype.ext
    exact congrArg (fun x : β.obs => x.1) heq'

theorem obs_image (β β' : X.Ty) (r : Step2Iso X β β') :
    β.obs.attach.image (fun ℓ => (r.obs ℓ).1) = β'.obs := by
  ext ℓ
  constructor
  · intro ha
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
    exact (r.obs a).2
  · intro hℓ
    exact Finset.mem_image.mpr ⟨r.obs.symm ⟨ℓ,hℓ⟩, Finset.mem_attach _ _, by simp⟩

theorem obs_erase_image (β β' : X.Ty) (r : Step2Iso X β β') (ℓ : β.obs) :
    (β.obs.erase ℓ.1).attach.image
      (fun a => (r.obs ⟨a.1,Finset.mem_of_mem_erase a.2⟩).1) = β'.obs.erase (r.obs ℓ).1 := by
  ext a
  constructor
  · rintro ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    refine Finset.mem_erase.mpr ⟨?_, (r.obs ⟨s.1,Finset.mem_of_mem_erase s.2⟩).2⟩
    intro heq
    have he := r.obs.injective (Subtype.ext heq)
    exact (Finset.mem_erase.mp s.2).1 (congrArg Subtype.val he)
  · intro ha
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp ha
    let s := r.obs.symm ⟨a,hmem⟩
    have hs : s.1 ∈ β.obs.erase ℓ.1 := by
      refine Finset.mem_erase.mpr ⟨?_, s.2⟩
      intro heq
      apply hne
      have he : s = ℓ := Subtype.ext heq
      have hmap := congrArg (fun q => (r.obs q).1) he
      simpa [s] using hmap
    refine Finset.mem_image.mpr ⟨⟨s.1,hs⟩, Finset.mem_attach _ _, ?_⟩
    change (r.obs s).1 = a
    simp [s]

theorem step2Tests_iso (β β' : X.Ty) (r : Step2Iso X β β') (H H' : X.Hist)
    (hb : H'.1 = (H.1.1, renameCoarse X r.bins H.1.2))
    (hZ : ∀ ℓ : β.obs, H'.2 (r.obs ℓ).1 = H.2 ℓ.1) :
    X.Step2Tests H' β' ↔ X.Step2Tests H β := by
  have hm : X.tagMass H' β' β'.obs = X.tagMass H β β.obs := by
    rw [← obs_image X β β' r]
    exact tagMass_iso X β β' r H H' hb hZ β.obs (fun _ h => h)
  have hd (ℓ : β.obs) : X.tagMass H' β' (β'.obs.erase (r.obs ℓ).1) =
      X.tagMass H β (β.obs.erase ℓ.1) := by
    rw [← obs_erase_image X β β' r ℓ]
    exact tagMass_iso X β β' r H H' hb hZ _ (fun _ h => Finset.mem_of_mem_erase h)
  unfold Ctx6.Step2Tests Ctx6.step2Thr
  rw [hm, ← r.severity]
  have hforall : (∀ ℓ ∈ β'.obs, (n : ℝ) ^ (-(δ₂ * β.u)) *
      X.tagMass H' β' (β'.obs.erase ℓ) ≤ X.tagMass H β β.obs) ↔
      (∀ ℓ ∈ β.obs, (n : ℝ) ^ (-(δ₂ * β.u)) * X.tagMass H β (β.obs.erase ℓ) ≤
        X.tagMass H β β.obs) := by
    constructor
    · intro h ℓ hℓ
      have hh := h (r.obs ⟨ℓ,hℓ⟩).1 (r.obs ⟨ℓ,hℓ⟩).2
      rwa [hd ⟨ℓ,hℓ⟩] at hh
    · intro h ℓ hℓ
      let a := r.obs.symm ⟨ℓ,hℓ⟩
      have hh := h a.1 a.2
      rw [← hd a] at hh
      simpa [a] using hh
  rw [hforall]

theorem step2Fail_iso (β β' : X.Ty) (r : Step2Iso X β β') (H H' : X.Hist)
    (hb : H'.1 = (H.1.1, renameCoarse X r.bins H.1.2))
    (hZ : ∀ ℓ : β.obs, H'.2 (r.obs ℓ).1 = H.2 ℓ.1) :
    X.Step2Fail H' β' ↔ X.Step2Fail H β := by
  unfold Ctx6.Step2Fail
  rw [step2Tests_iso X β β' r H H' hb hZ, hb, ← r.key]
  have hI : (renameCoarse X r.bins H.1.2).2 (keyMap X r.bins β.key) = H.1.2.2 β.key := by
    change H.1.2.2 ((keyMap X r.bins).symm (keyMap X r.bins β.key)) = _
    rw [Equiv.symm_apply_apply]
  rw [hI, tagGate_iso X β β' r H.1]

theorem step2BaseRate_iso (β β' : X.Ty) (r : Step2Iso X β β') (b : X.Base) :
    (X.hidLaw (b.1, renameCoarse X r.bins b.2)).pr (fun Z => X.Step2Fail ((b.1,renameCoarse X r.bins b.2),Z) β') =
      (X.hidLaw b).pr (fun Z => X.Step2Fail (b,Z) β) := by
  symm
  apply HypercubeRamsey.Lane_sol_s05_h1.pi_pr_local_equiv
    (fun ℓ => X.hidPost b ℓ.1) (fun ℓ => X.hidPost (b.1,renameCoarse X r.bins b.2) ℓ.1)
    β.obs β'.obs (fun _ => X.y₀) (fun _ => X.y₀) r.obs (fun _ => Equiv.refl _)
  · intro ℓ z
    rw [← r.obs_key ℓ, hidPost_rename X r.bins b _ (r.neighborhoods ℓ)]
    rfl
  · intro Z Z' h
    exact propext (HypercubeRamsey.Lane_q_s06_stages.step2Fail_iff_of_agree X b β Z Z' h)
  · intro Z Z' h
    exact propext (HypercubeRamsey.Lane_q_s06_stages.step2Fail_iff_of_agree X
      (b.1,renameCoarse X r.bins b.2) β' Z Z' h)
  · intro Z Z' h
    exact (step2Fail_iso X β β' r (b,Z) ((b.1,renameCoarse X r.bins b.2),Z') rfl (fun ℓ => (h ℓ).symm)).symm

theorem step2Rate_iso (β β' : X.Ty) (r : Step2Iso X β β') (v : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).pr (fun Z => X.Step2Fail ((v,c),Z) β')) =
      (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).pr (fun Z => X.Step2Fail ((v,c),Z) β)) := by
  rw [coarseLaw_expect_equiv X v r.bins]
  congr 1
  funext c
  exact step2BaseRate_iso X β β' r (v,c)

/-- The state fields read by a Step 3 rate; residual bits and exact fine counts are absent. -/
def targetShape (b : X.State) : X.Key × Mode6 × CubeVertex X.g.L.m :=
  (X.g.L.stKey b, X.stMode b, X.g.L.stSign b)

theorem s3Weight_targetShape (b b' : X.State) (hb : targetShape X b = targetShape X b')
    {Id : Type} [Fintype Id] [DecidableEq Id] (H : X.Hist) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.s3Weight H b D o drop ξ = X.s3Weight H b' D o drop ξ := by
  have hkey : X.g.L.stKey b = X.g.L.stKey b' := congrArg Prod.fst hb
  have hmode : X.stMode b = X.stMode b' := congrArg (fun s => s.2.1) hb
  have hsign : X.g.L.stSign b = X.g.L.stSign b' := congrArg (fun s => s.2.2) hb
  have htgt : X.tgt b = X.tgt b' := by
    change (X.g.L.stKey b, X.g.L.stSign b) = (X.g.L.stKey b', X.g.L.stSign b')
    rw [hkey, hsign]
  have hname : X.tgtName b = X.tgtName b' := congrArg primaryName6 hkey
  unfold Ctx6.s3Weight
  rw [hmode]
  cases X.stMode b'
  · have hg : X.LowGate H b D ξ = X.LowGate H b' D ξ := by
      unfold Ctx6.LowGate
      rw [htgt]
    simp only [Ctx6.lowWeight, Ctx6.lowLik, htgt, hg]
  · have hg : X.HighGate H b D ξ = X.HighGate H b' D ξ := by
      unfold Ctx6.HighGate
      rw [hname]
    simp only [Ctx6.highWeight, Ctx6.highLik, hname, hg]

theorem s3Fail_targetShape (b b' : X.State) (hb : targetShape X b = targetShape X b')
    {Id : Type} [Fintype Id] [DecidableEq Id] (H : X.Hist) (D : Finset (Id × X.Ty))
    (o : X.Data Id) : X.S3Fail H b D o ↔ X.S3Fail H b' D o := by
  have hkey : X.g.L.stKey b = X.g.L.stKey b' := congrArg Prod.fst hb
  have hmode : X.stMode b = X.stMode b' := congrArg (fun s => s.2.1) hb
  have hsign : X.g.L.stSign b = X.g.L.stSign b' := congrArg (fun s => s.2.2) hb
  have htgt : X.tgt b = X.tgt b' := by
    change (X.g.L.stKey b, X.g.L.stSign b) = (X.g.L.stKey b', X.g.L.stSign b')
    rw [hkey, hsign]
  have hname : X.tgtName b = X.tgtName b' := congrArg primaryName6 hkey
  have hgate : X.S3TrueGate H b D ↔ X.S3TrueGate H b' D := by
    unfold Ctx6.S3TrueGate Ctx6.trueTarget
    rw [hmode]
    cases X.stMode b'
    · simp only [Ctx6.LowGate, htgt]
    · simp only [Ctx6.HighGate, hname]
  have hmass (drop : Option (Id × X.Ty)) : X.s3Mass H b D o drop = X.s3Mass H b' D o drop := by
    unfold Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ _
    exact s3Weight_targetShape X b b' hb H D o drop ξ
  have hmatching (β : X.Ty) : X.Matching b β ↔ X.Matching b' β := by
    simp only [Ctx6.Matching, hmode, hkey]
  simp only [Ctx6.S3Fail, Ctx6.S3Tests, hgate, hmass, hmatching]

theorem step3HistRate_targetShape (b b' : X.State) (hb : targetShape X b = targetShape X b')
    (H : X.Hist) (D : Finset (Fin X.T × X.Ty)) :
    (X.dataLaw (Fin X.T) H).pr (fun o => X.S3Fail H b D o) =
      (X.dataLaw (Fin X.T) H).pr (fun o => X.S3Fail H b' D o) := by
  congr 1
  funext o
  exact propext (s3Fail_targetShape X b b' hb H D o)

theorem step3V0Rate_targetShape (b b' : X.State) (hb : targetShape X b = targetShape X b')
    (v : Fin N) (D : Finset (Fin X.T × X.Ty)) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw (Fin X.T) ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b D o))) =
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw (Fin X.T) ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b' D o))) := by
  congr 1
  funext c
  congr 1
  funext Z
  exact step3HistRate_targetShape X b b' hb ((v,c),Z) D

/-- Radius-two coordinate windows have five endpoint shapes. -/
def coordinateShape {n : ℕ} (c : Fin (n + 1)) : Fin 5 :=
  if c.val = 0 then 0 else if c.val = 1 then 1 else if c.val = n then 4
    else if c.val + 1 = n then 3 else 2

theorem coordinateShape_lower {n : ℕ} (hn : 4 ≤ n) (c c' : Fin (n + 1))
    (hc : coordinateShape c = coordinateShape c') : min c.val 2 = min c'.val 2 := by
  have hcn := c.isLt
  have hc'n := c'.isLt
  unfold coordinateShape at hc
  split_ifs at hc <;> norm_num at hc <;> omega

theorem coordinateShape_upper {n : ℕ} (hn : 4 ≤ n) (c c' : Fin (n + 1))
    (hc : coordinateShape c = coordinateShape c') : min (n - c.val) 2 = min (n - c'.val) 2 := by
  have hcn := c.isLt
  have hc'n := c'.isLt
  unfold coordinateShape at hc
  split_ifs at hc <;> norm_num at hc <;> omega

def coordinateWindow {n : ℕ} (c : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun a => Nat.dist a.val c.val ≤ 2)

theorem coordinate_shift_bounds {n : ℕ} (c c' : Fin (n + 1))
    (hl : min c.val 2 = min c'.val 2) (hu : min (n - c.val) 2 = min (n - c'.val) 2)
    (a : Fin (n + 1)) (ha : Nat.dist a.val c.val ≤ 2) :
    a.val + c'.val - c.val < n + 1 ∧
      Nat.dist (a.val + c'.val - c.val) c'.val ≤ 2 ∧
      (a.val + c'.val - c.val) + c.val = a.val + c'.val := by
  have hcn := c.isLt
  have hc'n := c'.isLt
  have han := a.isLt
  simp only [Nat.dist] at ha ⊢
  omega

def coordinateWindowEquiv {n : ℕ} (c c' : Fin (n + 1))
    (hl : min c.val 2 = min c'.val 2) (hu : min (n - c.val) 2 = min (n - c'.val) 2) :
    coordinateWindow c ≃ coordinateWindow c' where
  toFun a := by
    have ha := (Finset.mem_filter.mp a.2).2
    have hb := coordinate_shift_bounds c c' hl hu a.1 ha
    exact ⟨⟨a.1.val + c'.val - c.val,hb.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb.2.1⟩⟩
  invFun a := by
    have ha := (Finset.mem_filter.mp a.2).2
    have hb := coordinate_shift_bounds c' c hl.symm hu.symm a.1 ha
    exact ⟨⟨a.1.val + c.val - c'.val,hb.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb.2.1⟩⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    change a.1.val + c'.val - c.val + c.val - c'.val = a.1.val
    have hb := coordinate_shift_bounds c c' hl hu a.1 (Finset.mem_filter.mp a.2).2
    omega
  right_inv a := by
    apply Subtype.ext
    apply Fin.ext
    change a.1.val + c.val - c'.val + c'.val - c.val = a.1.val
    have hb := coordinate_shift_bounds c' c hl.symm hu.symm a.1 (Finset.mem_filter.mp a.2).2
    omega

theorem coordinateShape_perm {n : ℕ} (hn : 4 ≤ n) (c c' : Fin (n + 1))
    (hc : coordinateShape c = coordinateShape c') :
    ∃ e : Equiv.Perm (Fin (n + 1)), e c = c' ∧
          (∀ a, Nat.dist a.val c.val ≤ 2 → (e a).val + c.val = a.val + c'.val) ∧
      (∀ a, Nat.dist (e a).val c'.val ≤ 2 ↔ Nat.dist a.val c.val ≤ 2) := by
  have hl := coordinateShape_lower hn c c' hc
  have hu := coordinateShape_upper hn c c' hc
  let q := coordinateWindowEquiv c c' hl hu
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (fun a : coordinateWindow c => a.1) (fun a : coordinateWindow c => (q a).1)
    Subtype.val_injective (Subtype.val_injective.comp q.injective)
  have hshift (a : Fin (n + 1)) (ha : Nat.dist a.val c.val ≤ 2) :
      (e a).val + c.val = a.val + c'.val := by
    let s : coordinateWindow c := ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
    have hmap := congrArg Fin.val (he s)
    change (e a).val = a.val + c'.val - c.val at hmap
    rw [hmap]
    exact (coordinate_shift_bounds c c' hl hu a ha).2.2
  refine ⟨e, ?_, hshift, ?_⟩
  · apply Fin.ext
    have h := hshift c (by simp)
    omega
  · intro a
    constructor
    · intro ha
      let t : coordinateWindow c' := ⟨e a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
      let s := q.symm t
      have heq : e s.1 = e a := by
        have hmap := he s
        simpa [s, t] using hmap
      have hs := (Finset.mem_filter.mp s.2).2
      rwa [e.injective heq] at hs
    · intro ha
      have h := hshift a ha
      simp only [Nat.dist] at ha ⊢
      omega

theorem coordinateShape_edge_perm {n : ℕ} (hn : 4 ≤ n) (c c' : Fin (n + 1))
    (hc : coordinateShape c = coordinateShape c') :
    ∃ e : Equiv.Perm (Fin (n + 1)), e c = c' ∧
      (∀ a, Nat.dist a.val c.val ≤ 1 → Nat.dist (e a).val c'.val ≤ 1) ∧
      (∀ a, Nat.dist a.val c.val ≤ 1 → ∀ b,
        Nat.dist a.val b.val = 1 ↔ Nat.dist (e a).val (e b).val = 1) := by
  obtain ⟨e, he, hs, hw⟩ := coordinateShape_perm hn c c' hc
  have hnear (a : Fin (n + 1)) (ha : Nat.dist a.val c.val ≤ 1) :
      Nat.dist (e a).val c'.val ≤ 1 := by
    have h := hs a (ha.trans (by decide))
    simp only [Nat.dist] at ha ⊢
    omega
  refine ⟨e, he, hnear, ?_⟩
  intro a ha b
  have has := hs a (ha.trans (by decide))
  constructor
  · intro hab
    have hb : Nat.dist b.val c.val ≤ 2 := by
      simp only [Nat.dist] at ha hab ⊢
      omega
    have hbs := hs b hb
    simp only [Nat.dist] at hab ⊢
    omega
  · intro hab
    have han := hnear a ha
    have hb : Nat.dist (e b).val c'.val ≤ 2 := by
      simp only [Nat.dist] at han hab ⊢
      omega
    have hbs := hs b ((hw b).1 hb)
    simp only [Nat.dist] at hab ⊢
    omega

theorem card_fin_any (d : ℕ) (s : Fintype (Fin d)) : @Fintype.card (Fin d) s = d := by
  have h : @Fintype.card (Fin d) s = @Fintype.card (Fin d) (Fin.fintype d) :=
    @Fintype.card_congr _ _ s (Fin.fintype d) (Equiv.refl _)
  exact h.trans (Fintype.card_fin d)

def coarseShape (w : X.Bin) : Fin 5 → Fin 301 :=
  fun c =>
    letI : DecidablePred (fun i : Fin coarseChunkCount => coordinateShape (w i) = c) :=
      fun _ => Classical.propDecidable _
    ⟨Fintype.card {i : Fin coarseChunkCount // coordinateShape (w i) = c}, by
    have h := Fintype.card_le_of_injective
      (fun i : {i : Fin coarseChunkCount // coordinateShape (w i) = c} => i.1) Subtype.val_injective
    exact lt_of_le_of_lt h (by rw [card_fin_any]; norm_num [coarseChunkCount])⟩

theorem coarseShape_coordinate_perm (w w' : X.Bin) (hs : coarseShape X w = coarseShape X w') :
    ∃ p : Equiv.Perm (Fin coarseChunkCount), ∀ i, coordinateShape (w i) = coordinateShape (w' (p i)) := by
  obtain ⟨p,hp⟩ := HypercubeRamsey.Lane_sol_s05_h1.equiv_of_histogram
    (fun i => coordinateShape (w i)) (fun i => coordinateShape (w' i)) (fun c => by
      have h := congrArg Fin.val (congrFun hs c)
      dsimp only [coarseShape] at h
      exact h)
  exact ⟨p,fun i => (hp i).symm⟩

/-- Matching radius-two coordinate windows induce a bin renaming respecting every neighboring key list. -/
theorem coarseShape_local_perm (hn : 4 ≤ n) (w w' : X.Bin)
    (hs : coarseShape X w = coarseShape X w') :
    ∃ e : Equiv.Perm X.Bin, e w = w' ∧
      ∀ u, (∀ i, Nat.dist (u i).val (w i).val ≤ 1) →
        ∀ v, binAdjacent6 u v ↔ binAdjacent6 (e u) (e v) := by
  obtain ⟨p,hp⟩ := coarseShape_coordinate_perm X w w' hs
  choose es he hnear hedge using fun i => coordinateShape_edge_perm hn (w i) (w' (p i)) (hp i)
  let e : Equiv.Perm X.Bin := p.piCongr (W := fun _ => Fin (n + 1)) (Z := fun _ => Fin (n + 1)) (fun i => es i)
  have happ (u : X.Bin) (i : Fin coarseChunkCount) : e u (p i) = es i (u i) := by
    exact Equiv.piCongr_apply_apply (W := fun _ => Fin (n + 1)) (Z := fun _ => Fin (n + 1)) p (fun i => es i) u i
  have hew : e w = w' := by
    funext j
    obtain ⟨i,rfl⟩ := p.surjective j
    rw [happ, he]
  refine ⟨e, hew, ?_⟩
  intro u hu v
  constructor
  · rintro ⟨i, hsame, hdist⟩
    refine ⟨p i, ?_, ?_⟩
    · intro j hj
      obtain ⟨k,rfl⟩ := p.surjective j
      rw [happ, happ, hsame k (fun hk => hj (congrArg p hk))]
    · rw [happ, happ]
      exact (hedge i (u i) (hu i) (v i)).1 hdist
  · rintro ⟨j, hsame, hdist⟩
    obtain ⟨i,rfl⟩ := p.surjective j
    refine ⟨i, ?_, ?_⟩
    · intro k hk
      have h := hsame (p k) (fun h => hk (p.injective h))
      rw [happ, happ] at h
      exact (es k).injective h
    · rw [happ, happ] at hdist
      exact (hedge i (u i) (hu i) (v i)).2 hdist

theorem key_near_center (w : X.Bin) (h : X.Key) (hh : h ∈ X.C (w, .boundary)) :
    ∀ i, Nat.dist (h.1 i).val (w i).val ≤ 1 := by
  have hrel := (Finset.mem_filter.mp hh).2
  change keyAdjacent6 binAdjacent6 (w, .boundary) h at hrel
  rcases hrel with heq | heq | ⟨_,_,i,hsame,hdist⟩
  · subst h
    simp
  · rw [← heq]
    simp
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [Nat.dist_comm] using hdist.le
    · rw [← hsame j hji]
      simp

theorem C_image_of_local_perm (e : Equiv.Perm X.Bin) (h : X.Key)
    (he : ∀ v, binAdjacent6 h.1 v ↔ binAdjacent6 (e h.1) (e v)) :
    (X.C h).image (keyMap X e) = X.C (keyMap X e h) := by
  have hmap (u : X.Key) :
      keyAdjacent6 binAdjacent6 (keyMap X e h) (keyMap X e u) ↔
        keyAdjacent6 binAdjacent6 h u := by
    rcases h with ⟨w,f⟩
    rcases u with ⟨v,g⟩
    simp only [keyAdjacent6, keyMap_apply, Prod.mk.injEq, e.injective.eq_iff, he v]
  have hmem (u : X.Key) : u ∈ X.C h ↔ keyMap X e u ∈ X.C (keyMap X e h) := by
    simp only [Ctx6.C, keyNeighborhood6, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hmap u).symm
  ext s
  constructor
  · intro hs
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
    exact (hmem u).1 hu
  · intro hs
    refine Finset.mem_image.mpr ⟨(keyMap X e).symm s, ?_, by simp⟩
    apply (hmem _).2
    simpa using hs

def listEquiv {A : Type*} [DecidableEq A] (e : Equiv.Perm A) (S T : Finset A)
    (h : S.image e = T) : S ≃ T :=
  e.subtypeEquiv (fun a => by rw [← h]; simp)

def signFlip {m : ℕ} (t : CubeVertex m) (a : Fin m) : CubeVertex m := Function.update t a (!t a)

theorem signFlip_ne {m : ℕ} (t : CubeVertex m) (a : Fin m) : signFlip t a ≠ t := by
  intro h
  have hh := congrFun h a
  cases ht : t a <;> simp [signFlip, ht] at hh

theorem signFlip_injective {m : ℕ} (t : CubeVertex m) : Function.Injective (signFlip t) := by
  intro a b h
  by_contra hab
  have hh := congrFun h a
  cases ht : t a <;> simp [signFlip, hab, ht] at hh

/-- The low list consists of one scalar at each coarse key and |F| additional scalars at its own key. -/
def lowParamEquiv {W : Type} [Fintype W] {m : ℕ} (adj : W → W → Prop)
    (h : CoarseKey6 W) (t : CubeVertex m) (F : Finset (Fin m)) :
    (keyNeighborhood6 adj h) ⊕ F ≃ lowObservations6 adj h t F := by
  classical
  exact Equiv.ofBijective (fun a => match a with
    | .inl s => ⟨(s.1,t),Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s.1,s.2,rfl⟩)⟩
    | .inr i => ⟨(h,signFlip t i.1),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i.1,i.2,rfl⟩)⟩) (by
    constructor
    · intro a b heq
      have hval := congrArg Subtype.val heq
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          apply congrArg Sum.inl
          exact Subtype.ext (congrArg Prod.fst hval)
        | inr b =>
          exact False.elim (signFlip_ne t b.1 (congrArg Prod.snd hval).symm)
      | inr a =>
        cases b with
        | inl b => exact False.elim (signFlip_ne t a.1 (congrArg Prod.snd hval))
        | inr b =>
          apply congrArg Sum.inr
          exact Subtype.ext (signFlip_injective t (congrArg Prod.snd hval))
    · intro ℓ
      have hm := ℓ.2
      rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨s,hs,heq⟩ := Finset.mem_image.mp hm
        exact ⟨Sum.inl ⟨s,hs⟩,Subtype.ext heq⟩
      · obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hm
        exact ⟨Sum.inr ⟨i,hi⟩,Subtype.ext heq⟩)

theorem lowParamEquiv_key {W : Type} [Fintype W] {m : ℕ} (adj : W → W → Prop)
    (h : CoarseKey6 W) (t : CubeVertex m) (F : Finset (Fin m))
    (a : (keyNeighborhood6 adj h) ⊕ F) :
    (lowParamEquiv adj h t F a).1.1 =
      Sum.elim (fun s : keyNeighborhood6 adj h => s.1) (fun _ : F => h) a := by
  cases a <;> rfl

theorem lowObservation_iso (e : Equiv.Perm X.Bin) (h : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h))
    (t t' : CubeVertex X.g.L.m) (F F' : Finset (Fin X.g.L.m)) (hF : F.card = F'.card) :
    ∃ q : lowObservations6 binAdjacent6 h t F ≃ lowObservations6 binAdjacent6 (keyMap X e h) t' F',
      ∀ ℓ, (q ℓ).1.1 = keyMap X e ℓ.1.1 := by
  unfold Ctx6.C at *
  let ec := listEquiv (keyMap X e) (keyNeighborhood6 binAdjacent6 h)
    (keyNeighborhood6 binAdjacent6 (keyMap X e h)) hC
  let ef : F ≃ F' := Fintype.equivOfCardEq (by simpa using hF)
  let q := (lowParamEquiv binAdjacent6 h t F).symm.trans
    ((ec.sumCongr ef).trans (lowParamEquiv binAdjacent6 (keyMap X e h) t' F'))
  refine ⟨q, ?_⟩
  intro ℓ
  obtain ⟨a,rfl⟩ := (lowParamEquiv binAdjacent6 h t F).surjective ℓ
  simp only [q, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [lowParamEquiv_key, lowParamEquiv_key]
  cases a <;> rfl

theorem lowObservations_card (h : X.Key) (t : CubeVertex X.g.L.m) (F : Finset (Fin X.g.L.m)) :
    (lowObservations6 binAdjacent6 h t F).card = (X.C h).card + F.card := by
  have hc := Fintype.card_congr (lowParamEquiv binAdjacent6 h t F)
  simpa only [Fintype.card_sum, Fintype.card_coe,Ctx6.C] using hc.symm

theorem key_mem_C (h : X.Key) : h ∈ X.C h := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl rfl⟩

theorem C_key_near_center (h s : X.Key) (hs : s ∈ X.C h) :
    ∀ i, Nat.dist (s.1 i).val (h.1 i).val ≤ 1 := by
  have hrel := (Finset.mem_filter.mp hs).2
  change keyAdjacent6 binAdjacent6 h s at hrel
  rcases hrel with heq | heq | ⟨_,_,i,hsame,hdist⟩
  · subst s
    simp
  · rw [← heq]
    simp
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [Nat.dist_comm] using hdist.le
    · rw [← hsame j hji]
      simp

theorem makeType_key (h : X.Key) (t : CubeVertex X.g.L.m) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    (makeType6 binAdjacent6 h t F j X.J).key = h := by
  unfold makeType6
  split_ifs <;> rfl

theorem makeType_obs_key (h : X.Key) (t : CubeVertex X.g.L.m) (F : Finset (Fin X.g.L.m)) (j : ℕ)
    (ℓ : X.HKey) (hℓ : ℓ ∈ (makeType6 binAdjacent6 h t F j X.J).obs) : ℓ.1 ∈ X.C h := by
  by_cases hj : j ≤ X.J
  · have hObs : (makeType6 binAdjacent6 h t F j X.J).obs = lowObservations6 binAdjacent6 h t F := by
      unfold makeType6
      rw [if_pos hj]
      rfl
    rw [hObs] at hℓ
    let a := (lowParamEquiv binAdjacent6 h t F).symm ⟨ℓ,hℓ⟩
    have ha := lowParamEquiv_key binAdjacent6 h t F a
    have hmap : (lowParamEquiv binAdjacent6 h t F a).1.1 = ℓ.1 := by
      simp only [a,Equiv.apply_symm_apply]
    rw [hmap] at ha
    have hgood : ∀ a : (X.C h) ⊕ F,
        Sum.elim (fun s : X.C h => s.1) (fun _ : F => h) a ∈ X.C h := by
      intro z
      cases z with
      | inl s => exact s.2
      | inr i => exact key_mem_C X h
    exact ha.symm ▸ hgood a
  · have hObs : (makeType6 binAdjacent6 h t F j X.J).obs = highObservations6 h t j X.J := by
      unfold makeType6
      rw [if_neg hj]
      rfl
    rw [hObs] at hℓ
    unfold highObservations6 at hℓ
    split_ifs at hℓ
    · have heq := Finset.mem_singleton.mp hℓ
      subst ℓ
      exact key_mem_C X h
    · simp at hℓ

theorem highObservations_key (h : X.Key) (t : CubeVertex X.g.L.m) (j : ℕ)
    (ℓ : highObservations6 h t j X.J) : ℓ.1.1 = h := by
  have hm := ℓ.2
  unfold highObservations6 at hm
  split_ifs at hm
  · exact congrArg Prod.fst (Finset.mem_singleton.mp hm)
  · simp at hm

theorem makeType_observation_iso (e : Equiv.Perm X.Bin) (h : X.Key)
    (hC : (X.C h).image (keyMap X e) = X.C (keyMap X e h))
    (t t' : CubeVertex X.g.L.m) (F F' : Finset (Fin X.g.L.m)) (j j' : ℕ)
    (hmode : (makeType6 binAdjacent6 h t F j X.J).mode =
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J).mode)
    (hcard : (makeType6 binAdjacent6 h t F j X.J).obs.card =
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J).obs.card) :
    ∃ q : (makeType6 binAdjacent6 h t F j X.J).obs ≃
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J).obs,
      ∀ ℓ, (q ℓ).1.1 = keyMap X e ℓ.1.1 := by
  by_cases hj : j ≤ X.J <;> by_cases hj' : j' ≤ X.J
  · have hl : makeType6 binAdjacent6 h t F j X.J =
        (h,.low,sevFin6 X.g.L.m j,lowObservations6 binAdjacent6 h t F) := by
      unfold makeType6
      rw [if_pos hj]
    have hr : makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J =
        (keyMap X e h,.low,sevFin6 X.g.L.m j',lowObservations6 binAdjacent6 (keyMap X e h) t' F') := by
      unfold makeType6
      rw [if_pos hj']
    rw [hl,hr] at hcard ⊢
    change ∃ q : lowObservations6 binAdjacent6 h t F ≃ lowObservations6 binAdjacent6 (keyMap X e h) t' F',
      ∀ ℓ, (q ℓ).1.1 = keyMap X e ℓ.1.1
    change (lowObservations6 binAdjacent6 h t F).card =
      (lowObservations6 binAdjacent6 (keyMap X e h) t' F').card at hcard
    have hc : (X.C h).card = (X.C (keyMap X e h)).card := by
      rw [← hC, Finset.card_image_of_injective _ (keyMap X e).injective]
    rw [lowObservations_card, lowObservations_card] at hcard
    have hF : F.card = F'.card := by omega
    exact lowObservation_iso X e h hC t t' F F' hF
  · simp [makeType6, hj, hj', Type6.mode] at hmode
  · simp [makeType6, hj, hj', Type6.mode] at hmode
  · have hl : makeType6 binAdjacent6 h t F j X.J = (h,.high,0,highObservations6 h t j X.J) := by
      unfold makeType6
      rw [if_neg hj]
    have hr : makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J =
        (keyMap X e h,.high,0,highObservations6 (keyMap X e h) t' j' X.J) := by
      unfold makeType6
      rw [if_neg hj']
    rw [hl,hr] at hcard ⊢
    change ∃ q : highObservations6 h t j X.J ≃ highObservations6 (keyMap X e h) t' j' X.J,
      ∀ ℓ, (q ℓ).1.1 = keyMap X e ℓ.1.1
    change (highObservations6 h t j X.J).card =
      (highObservations6 (keyMap X e h) t' j' X.J).card at hcard
    let q : highObservations6 h t j X.J ≃ highObservations6 (keyMap X e h) t' j' X.J :=
      Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hcard)
    refine ⟨q, ?_⟩
    intro ℓ
    rw [highObservations_key, highObservations_key]

theorem makeType_step2_iso (e : Equiv.Perm X.Bin) (h : X.Key)
    (hC : ∀ s ∈ X.C h, (X.C s).image (keyMap X e) = X.C (keyMap X e s))
    (t t' : CubeVertex X.g.L.m) (F F' : Finset (Fin X.g.L.m)) (j j' : ℕ)
    (hmode : (makeType6 binAdjacent6 h t F j X.J).mode =
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J).mode)
    (hu : (makeType6 binAdjacent6 h t F j X.J).u =
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J).u)
    (hcard : (makeType6 binAdjacent6 h t F j X.J).obs.card =
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J).obs.card) :
    Nonempty (Step2Iso X (makeType6 binAdjacent6 h t F j X.J)
      (makeType6 binAdjacent6 (keyMap X e h) t' F' j' X.J)) := by
  obtain ⟨q,hq⟩ := makeType_observation_iso X e h (hC h (key_mem_C X h)) t t' F F' j j' hmode hcard
  refine ⟨⟨e,q,?_,hu,fun ℓ => (hq ℓ).symm,?_⟩⟩
  · rw [makeType_key, makeType_key]
  · intro ℓ
    exact hC ℓ.1.1 (makeType_obs_key X h t F j ℓ.1 ℓ.2)

theorem evenType_obs_card_le (x : CubeVertex n) : (X.evenType x).obs.card ≤ 602 + X.g.L.m := by
  by_cases hj : X.g.L.severity x ≤ X.J
  · have hc := Lane_q_s06_steps1.lowObservations_card_le binAdjacent6 (X.g.L.key x)
      (X.g.L.sign x) (X.g.L.flippable x)
    have hF : (X.g.L.flippable x).card ≤ X.g.L.m := by
      have h := Finset.card_le_univ (X.g.L.flippable x)
      rw [card_fin_any] at h
      exact h
    have hC := X.g.flips.key_neighborhood_card (X.g.L.key x)
    simp only [Ctx6.evenType, makeType6, if_pos hj, Type6.obs]
    omega
  · simp only [Ctx6.evenType, makeType6, if_neg hj, Type6.obs, highObservations6]
    split_ifs <;> simp <;> omega

abbrev Step2BaseShape (m : ℕ) := KeyFlag6 × (Fin 5 → Fin 301) × Mode6 × Fin (m + 603)
abbrev Step2Shape (m : ℕ) := Step2BaseShape m × Fin (m + 2)

def step2BaseShape (β : X.Ty) : Step2BaseShape X.g.L.m :=
  (β.key.2,coarseShape X β.key.1,β.mode,⟨min β.obs.card (X.g.L.m + 602),by omega⟩)

def step2Shape (β : X.Ty) : Step2Shape X.g.L.m :=
  (step2BaseShape X β,⟨β.u,by
    have hs := β.2.2.1.isLt
    unfold Type6.u
    cases hm : β.mode <;> simp [hm, Type6.sev] <;> omega⟩)

theorem occ_step2Shape_iso (hn : 4 ≤ n) (β β' : X.Ty) (hβ : β ∈ X.occTypes)
    (hβ' : β' ∈ X.occTypes) (hs : step2Shape X β = step2Shape X β') :
    Nonempty (Step2Iso X β β') := by
  have hflag : β.key.2 = β'.key.2 := congrArg (fun s => s.1.1) hs
  have hcoarse : coarseShape X β.key.1 = coarseShape X β'.key.1 := congrArg (fun s => s.1.2.1) hs
  have hmode : β.mode = β'.mode := congrArg (fun s => s.1.2.2.1) hs
  have hcard : min β.obs.card (X.g.L.m + 602) = min β'.obs.card (X.g.L.m + 602) :=
    congrArg (fun s => s.1.2.2.2.val) hs
  have hu : β.u = β'.u := congrArg (fun s => s.2.val) hs
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hβ
  obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hβ'
  rw [Nat.min_eq_left (by simpa only [Nat.add_comm] using evenType_obs_card_le X x),
    Nat.min_eq_left (by simpa only [Nat.add_comm] using evenType_obs_card_le X x')] at hcard
  have hkey : (X.evenType x).key = X.g.L.key x := makeType_key X _ _ _ _
  have hkey' : (X.evenType x').key = X.g.L.key x' := makeType_key X _ _ _ _
  rw [hkey,hkey'] at hflag hcoarse
  obtain ⟨e,he,heAdj⟩ := coarseShape_local_perm X hn _ _ hcoarse
  have hekey : keyMap X e (X.g.L.key x) = X.g.L.key x' := by
    apply Prod.ext
    · exact he
    · exact hflag
  have hC : ∀ s ∈ X.C (X.g.L.key x), (X.C s).image (keyMap X e) = X.C (keyMap X e s) := by
    intro s hs
    exact C_image_of_local_perm X e s (heAdj s.1 (C_key_near_center X _ _ hs))
  have hresult := makeType_step2_iso X e (X.g.L.key x) hC (X.g.L.sign x) (X.g.L.sign x')
    (X.g.L.flippable x) (X.g.L.flippable x') (X.g.L.severity x) (X.g.L.severity x')
    (by simpa only [hekey,Ctx6.evenType] using hmode)
    (by simpa only [hekey,Ctx6.evenType] using hu)
    (by simpa only [hekey,Ctx6.evenType] using hcard)
  simpa only [hekey,Ctx6.evenType] using hresult

def taggedStep2Shape (β : X.Ty) : Step2Shape X.g.L.m ⊕ X.Ty :=
  if β ∈ X.occTypes then Sum.inl (step2Shape X β) else Sum.inr β

theorem taggedStep2Shape_rates (hn : 4 ≤ n) (β β' : X.Ty)
    (hs : taggedStep2Shape X β = taggedStep2Shape X β') :
    β.u = β'.u ∧ ∀ v,
      (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).pr (fun Z => X.Step2Fail ((v,c),Z) β)) =
      (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).pr (fun Z => X.Step2Fail ((v,c),Z) β')) := by
  by_cases hβ : β ∈ X.occTypes <;> by_cases hβ' : β' ∈ X.occTypes
  · simp only [taggedStep2Shape, if_pos hβ, if_pos hβ', Sum.inl.injEq] at hs
    obtain ⟨r⟩ := occ_step2Shape_iso X hn β β' hβ hβ' hs
    exact ⟨r.severity,fun v => (step2Rate_iso X β β' r v).symm⟩
  · simp [taggedStep2Shape,hβ,hβ'] at hs
  · simp [taggedStep2Shape,hβ,hβ'] at hs
  · simp only [taggedStep2Shape, if_neg hβ, if_neg hβ', Sum.inr.injEq] at hs
    subst β'
    exact ⟨rfl, fun _ => rfl⟩

theorem step2_u_le (β : X.Ty) : β.u ≤ X.g.L.m + 1 := by
  have hs := β.2.2.1.isLt
  unfold Type6.u
  cases hm : β.mode <;> simp [hm,Type6.sev] <;> omega

theorem step2Shape_fiber_card (u : ℕ) :
    ((X.occTypes.filter (fun β => β.u = u)).image (taggedStep2Shape X)).card ≤
      4 * 301 ^ 5 * (X.g.L.m + 603) := by
  let S := X.occTypes.filter (fun β => β.u = u)
  let ucode : Fin (X.g.L.m + 2) := ⟨min u (X.g.L.m + 1),by omega⟩
  have htag : S.image (taggedStep2Shape X) = (S.image (step2Shape X)).image Sum.inl := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro β hβ
    have hb : β ∈ X.occTypes := (Finset.mem_filter.mp hβ).1
    simp only [taggedStep2Shape,if_pos hb,Function.comp_apply]
  have hshape : S.image (step2Shape X) = (S.image (step2BaseShape X)).image (fun c => (c,ucode)) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro β hβ
    have hbu := (Finset.mem_filter.mp hβ).2
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change β.u = min u (X.g.L.m + 1)
      rw [← hbu, Nat.min_eq_left (step2_u_le X β)]
  rw [htag]
  calc
    _ ≤ (S.image (step2Shape X)).card := Finset.card_image_le
    _ ≤ (S.image (step2BaseShape X)).card := by rw [hshape]; exact Finset.card_image_le
    _ ≤ Fintype.card (Step2BaseShape X.g.L.m) := Finset.card_le_univ _
    _ = 4 * 301 ^ 5 * (X.g.L.m + 603) := by
      simp only [Step2BaseShape,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
      have hflag : Fintype.card KeyFlag6 = 2 := rfl
      have hmode : Fintype.card Mode6 = 2 := rfl
      rw [hflag,hmode]
      ring

theorem taggedStep2Shape_card_bound (hm : 603 ≤ X.g.L.m) (u : ℕ) :
    (((X.occTypes.filter fun β => β.u = u).image (taggedStep2Shape X)).card : ℝ) ≤
      10 ^ 210 * ((X.g.L.m : ℝ) + 1) ^ (2 * u) := by
  by_cases hu : u = 0
  · subst u
    have hset : X.occTypes.filter (fun β => β.u = 0) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro β _ hz
      have hpos : 1 ≤ β.u := by
        unfold Type6.u
        cases hm : β.mode <;> simp [hm]
      omega
    rw [hset]
    simp
  · have hu1 : 1 ≤ u := by omega
    have hmR : 603 ≤ (X.g.L.m : ℝ) := by exact_mod_cast hm
    have hcard := step2Shape_fiber_card X u
    have hcardR : (((X.occTypes.filter fun β => β.u = u).image (taggedStep2Shape X)).card : ℝ) ≤
        4 * 301 ^ 5 * ((X.g.L.m : ℝ) + 603) := by exact_mod_cast hcard
    have hm2 : (X.g.L.m : ℝ) + 603 ≤ ((X.g.L.m : ℝ) + 1) ^ 2 := by nlinarith
    have hpow : ((X.g.L.m : ℝ) + 1) ^ 2 ≤ ((X.g.L.m : ℝ) + 1) ^ (2 * u) :=
      pow_le_pow_right₀ (by have h : 0 ≤ (X.g.L.m : ℝ) := Nat.cast_nonneg _; linarith) (by omega)
    calc
      _ ≤ (4 * 301 ^ 5 : ℝ) * ((X.g.L.m : ℝ) + 603) := hcardR
      _ ≤ (4 * 301 ^ 5 : ℝ) * ((X.g.L.m : ℝ) + 1) ^ (2 * u) :=
        mul_le_mul_of_nonneg_left (hm2.trans hpow) (by positivity)
      _ ≤ 10 ^ 210 * ((X.g.L.m : ℝ) + 1) ^ (2 * u) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end

end HypercubeRamsey.S06.Lane_sol_s06_shapes
