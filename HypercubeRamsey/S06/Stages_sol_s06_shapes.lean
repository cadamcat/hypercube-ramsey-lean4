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

/-! Step 3 symmetries and the generic/exceptional descriptor code. -/

def exceptionalNeighbors (b : X.State) : Finset (X.g.L.stNbr b) :=
  (Finset.univ.filter fun a => X.stMode a.1 ≠ X.stMode b) ∪
    (Finset.univ.filter fun a =>
      (X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
        (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
          X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b))

theorem neighbor_type_generic_or_exceptional (b : X.State) (a : X.g.L.stNbr b) :
    X.stType a.1 ∈ Lane_q_s06_steps2.neighborTypeForms6 X b ∨
      a ∈ exceptionalNeighbors X b := by
  by_cases hbad : a ∈ exceptionalNeighbors X b
  · exact Or.inr hbad
  have hmode : X.stMode a.1 = X.stMode b := by
    by_contra h
    exact hbad (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hvar : ¬ ((X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
      (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
        X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b)) := by
    intro h
    exact hbad (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  by_cases hnear : X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1
  · have hsign : X.g.L.stSign a.1 = X.g.L.stSign b := by
      by_contra h
      exact hvar ⟨hnear, Or.inl h⟩
    have hflip : X.g.L.stFlippable a.1 = X.g.L.stFlippable b := by
      by_contra h
      exact hvar ⟨hnear, Or.inr h⟩
    exact Or.inl (Lane_q_s06_steps2.neighbor_type_mem_forms6 X a.2 hsign hflip)
  · have hhigh : X.stMode b = .high := by
      cases h : X.stMode b with
      | low => exact False.elim (hnear (Or.inl h))
      | high => rfl
    exact Or.inl (Lane_q_s06_steps2.neighbor_type_mem_forms_high6 X a.2
      (hmode.trans hhigh) (fun h => hnear (Or.inr h)))

variable {Id : Type} [Fintype Id] [DecidableEq Id]

def hiddenTypeMap (q : Equiv.Perm X.HKey) (β : X.Ty) : X.Ty :=
  (β.key, β.mode, β.2.2.1, β.obs.image q)

def hiddenTypeEquiv (q : Equiv.Perm X.HKey) : Equiv.Perm X.Ty where
  toFun := hiddenTypeMap X q
  invFun := hiddenTypeMap X q.symm
  left_inv β := by
    rcases β with ⟨h, md, j, S⟩
    simp [hiddenTypeMap, Type6.key, Type6.mode, Type6.obs, Finset.image_image]
  right_inv β := by
    rcases β with ⟨h, md, j, S⟩
    simp [hiddenTypeMap, Type6.key, Type6.mode, Type6.obs, Finset.image_image]

def renameHid (q : Equiv.Perm X.HKey) (Z : X.Hid) : X.Hid := fun ℓ => Z (q.symm ℓ)
def renameHist (q : Equiv.Perm X.HKey) (H : X.Hist) : X.Hist := (H.1, renameHid X q H.2)

@[simp] theorem hiddenTypeMap_key (q : Equiv.Perm X.HKey) (β : X.Ty) :
    (hiddenTypeMap X q β).key = β.key := rfl
@[simp] theorem hiddenTypeMap_mode (q : Equiv.Perm X.HKey) (β : X.Ty) :
    (hiddenTypeMap X q β).mode = β.mode := rfl
@[simp] theorem hiddenTypeMap_obs (q : Equiv.Perm X.HKey) (β : X.Ty) :
    (hiddenTypeMap X q β).obs = β.obs.image q := rfl
@[simp] theorem hiddenTypeMap_u (q : Equiv.Perm X.HKey) (β : X.Ty) :
    (hiddenTypeMap X q β).u = β.u := rfl
@[simp] theorem renameHist_fst (q : Equiv.Perm X.HKey) (H : X.Hist) :
    (renameHist X q H).1 = H.1 := rfl
@[simp] theorem renameHist_hid_apply (q : Equiv.Perm X.HKey) (H : X.Hist) (ℓ : X.HKey) :
    (renameHist X q H).2 (q ℓ) = H.2 ℓ := by simp [renameHist, renameHid]

@[simp] theorem renameHid_apply (q : Equiv.Perm X.HKey) (Z : X.Hid) (ℓ : X.HKey) :
    renameHid X q Z (q ℓ) = Z ℓ := by simp [renameHid]

def hiddenNameEquiv (q : Equiv.Perm X.HKey) : Equiv.Perm X.Name where
  toFun nm := match nm with | .par p => .par p | .hid ℓ => .hid (q ℓ)
  invFun nm := match nm with | .par p => .par p | .hid ℓ => .hid (q.symm ℓ)
  left_inv nm := by cases nm <;> simp
  right_inv nm := by cases nm <;> simp

theorem reqNames_hiddenTypeMap (q : Equiv.Perm X.HKey) (β : X.Ty) :
    reqNames6 (hiddenTypeMap X q β) = (reqNames6 β).image (hiddenNameEquiv X q) := by
  have hpar (p : ParentName6 X.Bin) : hiddenNameEquiv X q (.par p) = .par p := rfl
  have hhid (ℓ : X.HKey) : hiddenNameEquiv X q (.hid ℓ) = .hid (q ℓ) := rfl
  simp only [reqNames6, hiddenTypeMap_key, hiddenTypeMap_mode, hiddenTypeMap_obs,
    Finset.image_union, Finset.image_insert, Finset.image_image, Function.comp_def, hpar, hhid]
  split_ifs with hx <;> ext nm <;> simp [hx, hpar, Finset.mem_image]

theorem labelLaw_hiddenRename (q : Equiv.Perm X.HKey) (H : X.Hist)
    (S : Finset X.Name) (i : X.ι) :
    X.labelLaw (renameHist X q H) (S.image (hiddenNameEquiv X q)) i = X.labelLaw H S i := by
  have hv (nm : X.Name) : X.varVal (renameHist X q H) (hiddenNameEquiv X q nm) = X.varVal H nm := by
    cases nm <;> simp [Ctx6.varVal, hiddenNameEquiv, renameHist, renameHid]
  have hn : X.reqNbhd (renameHist X q H) (S.image (hiddenNameEquiv X q)) = X.reqNbhd H S := by
    ext y
    simp only [Ctx6.reqNbhd, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_image, hv]
  simp only [Ctx6.labelLaw, hn]

theorem tagGate_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (base : X.Base) (β : X.Ty) (i : X.ι) :
    X.tagGate base (hiddenTypeMap X q β) i ↔ X.tagGate base β i := by
  simp only [Ctx6.tagGate, hiddenTypeMap, Type6.key, Type6.obs,
    Finset.forall_mem_image, hq]

theorem tagWeight_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) (i : X.ι) :
    X.tagWeight (renameHist X q H) (hiddenTypeMap X q β) (S.image q) i =
      X.tagWeight H β S i := by
  unfold Ctx6.tagWeight
  simp only [renameHist_fst, hiddenTypeMap_key, tagGate_hiddenRename X q hq]
  rw [Finset.prod_image]
  · simp only [hq, renameHid_apply, renameHist_hid_apply]
  · exact fun _ _ _ _ h => q.injective h

theorem tagMass_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) :
    X.tagMass (renameHist X q H) (hiddenTypeMap X q β) (S.image q) = X.tagMass H β S := by
  unfold Ctx6.tagMass
  apply Finset.sum_congr rfl
  intro i _
  exact tagWeight_hiddenRename X q hq H β S i

theorem tagPost_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) :
    X.tagPost (renameHist X q H) (hiddenTypeMap X q β) (S.image q) = X.tagPost H β S := by
  unfold Ctx6.tagPost
  congr 1
  funext i
  exact tagWeight_hiddenRename X q hq H β S i

theorem Tβ_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) :
    X.Tβ (renameHist X q H) (hiddenTypeMap X q β) = X.Tβ H β :=
  tagPost_hiddenRename X q hq H β β.obs

theorem TβDel_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) (ℓ : X.HKey) :
    X.TβDel (renameHist X q H) (hiddenTypeMap X q β) (q ℓ) = X.TβDel H β ℓ := by
  unfold Ctx6.TβDel
  change X.tagPost _ _ ((β.obs.image q).erase (q ℓ)) = _
  rw [← Finset.image_erase q.injective]
  exact tagPost_hiddenRename X q hq H β _

theorem step2Tests_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) :
    X.Step2Tests (renameHist X q H) (hiddenTypeMap X q β) ↔ X.Step2Tests H β := by
  have hu : (hiddenTypeMap X q β).u = β.u := by
    unfold Type6.u
    rfl
  have he (ℓ : X.HKey) : X.tagMass (renameHist X q H) (hiddenTypeMap X q β)
      ((β.obs.image q).erase (q ℓ)) = X.tagMass H β (β.obs.erase ℓ) := by
    rw [← Finset.image_erase q.injective]
    exact tagMass_hiddenRename X q hq H β _
  simp only [Ctx6.Step2Tests, Ctx6.step2Thr, hiddenTypeMap_obs,
    Finset.forall_mem_image, tagMass_hiddenRename X q hq, hiddenTypeMap_u, he]

theorem tupleLawOn_hiddenRename (q : Equiv.Perm X.HKey) (H : X.Hist)
    (S : Finset X.Name) (T : FinProb X.ι) :
    X.tupleLawOn (renameHist X q H) (S.image (hiddenNameEquiv X q)) T = X.tupleLawOn H S T := by
  unfold Ctx6.tupleLawOn
  congr 1
  funext i
  congr 1
  funext r
  exact labelLaw_hiddenRename X q H S i

theorem tupleLaw_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (β : X.Ty) :
    X.tupleLaw (renameHist X q H) (hiddenTypeMap X q β) = X.tupleLaw H β := by
  unfold Ctx6.tupleLaw
  rw [Tβ_hiddenRename X q hq, reqNames_hiddenTypeMap X q,
    tupleLawOn_hiddenRename X q]

theorem renameHist_withHid (q : Equiv.Perm X.HKey) (H : X.Hist) (ℓ : X.HKey) (ξ : Fin N) :
    renameHist X q (X.withHid H ℓ ξ) = X.withHid (renameHist X q H) (q ℓ) ξ := by
  apply Prod.ext
  · rfl
  funext s
  simp only [renameHist, renameHid, Ctx6.withHid, Function.update_apply]
  have he : q.symm s = ℓ ↔ s = q ℓ := by
    exact ⟨fun h => by simpa using congrArg q h,
      fun h => by rw [h, Equiv.symm_apply_apply]⟩
  simp only [he]

theorem renameHist_withPar (q : Equiv.Perm X.HKey) (H : X.Hist) (nm : ParentName6 X.Bin) (ξ : Fin N) :
    renameHist X q (X.withParH H nm ξ) = X.withParH (renameHist X q H) nm ξ := rfl

def hiddenEntryEquiv (q : Equiv.Perm X.HKey) : Equiv.Perm (Id × X.Ty) :=
  (Equiv.refl Id).prodCongr (hiddenTypeEquiv X q)

theorem hiddenEntryEquiv_apply (q : Equiv.Perm X.HKey) (e : Id × X.Ty) :
    hiddenEntryEquiv X q e = (e.1, hiddenTypeMap X q e.2) := rfl

@[simp] theorem hiddenEntryEquiv_type (q : Equiv.Perm X.HKey) (e : Id × X.Ty) :
    (hiddenEntryEquiv X q e).2 = hiddenTypeMap X q e.2 := rfl

def hiddenDescMap (q : Equiv.Perm X.HKey) (D : Finset (Id × X.Ty)) : Finset (Id × X.Ty) :=
  D.image (hiddenEntryEquiv X q)

def renameData (q : Equiv.Perm X.HKey) (o : X.Data Id) : X.Data Id :=
  fun e => o ((hiddenEntryEquiv X q).symm e)

@[simp] theorem renameData_apply (q : Equiv.Perm X.HKey) (o : X.Data Id) (e : Id × X.Ty) :
    renameData X q o (hiddenEntryEquiv X q e) = o e := by simp [renameData]

theorem locHid_hiddenRename (q : Equiv.Perm X.HKey) (D : Finset (Id × X.Ty)) :
    X.locHid (hiddenDescMap X q D) = (X.locHid D).image q := by
  ext ℓ
  constructor
  · intro h
    obtain ⟨e, he, hℓ⟩ := Finset.mem_biUnion.mp h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rw [hiddenEntryEquiv_type, hiddenTypeMap_obs] at hℓ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hℓ
    exact Finset.mem_image.mpr ⟨s, Finset.mem_biUnion.mpr ⟨a,ha,hs⟩,rfl⟩
  · intro h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨a, ha, hs⟩ := Finset.mem_biUnion.mp hs
    refine Finset.mem_biUnion.mpr ⟨hiddenEntryEquiv X q a,
      Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
    rw [hiddenEntryEquiv_type,hiddenTypeMap_obs]
    exact Finset.mem_image.mpr ⟨s,hs,rfl⟩

theorem locKeys_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (D : Finset (Id × X.Ty)) :
    X.locKeys (hiddenDescMap X q D) = X.locKeys D := by
  unfold Ctx6.locKeys
  rw [locHid_hiddenRename X q]
  congr 1
  · ext s
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨ℓ, ⟨a, ha, rfl⟩, hs⟩
      exact ⟨a, ha, by simpa only [hq] using hs⟩
    · rintro ⟨ℓ, hℓ, hs⟩
      exact ⟨q ℓ, ⟨ℓ, hℓ, rfl⟩, by simpa only [hq] using hs⟩
  · simp only [hiddenDescMap, Finset.image_image]
    rfl

theorem locDensity_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist)
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N) :
    X.locDensity (renameHist X q H) nm (hiddenDescMap X q D) ξ = X.locDensity H nm D ξ := by
  unfold Ctx6.locDensity Ctx6.locBins
  rw [locKeys_hiddenRename X q hq, locHid_hiddenRename X q]
  simp only [renameHist]
  congr 1
  rw [Finset.prod_image]
  · simp only [hq, renameHid_apply, renameHist_hid_apply]
  · exact fun _ _ _ _ h => q.injective h

theorem tupleRatio_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (Hξ H : X.Hist) (β : X.Ty)
    (T : FinProb X.ι) (drop : X.Name) (o : X.Tuple) :
    X.tupleRatio (renameHist X q Hξ) (renameHist X q H)
      (hiddenTypeMap X q β) T (hiddenNameEquiv X q drop) o =
      X.tupleRatio Hξ H β T drop o := by
  unfold Ctx6.tupleRatio
  rw [Tβ_hiddenRename X q hq, reqNames_hiddenTypeMap X q,
    labelLaw_hiddenRename X q, ← Finset.image_erase (hiddenNameEquiv X q).injective,
    labelLaw_hiddenRename X q]

theorem lowGate_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (b b' : X.State)
    (hkey : X.g.L.stKey b' = X.g.L.stKey b) (htgt : X.tgt b' = q (X.tgt b))
    (D : Finset (Id × X.Ty)) (ξ : Fin N) :
    X.LowGate (renameHist X q H) b' (hiddenDescMap X q D) ξ ↔ X.LowGate H b D ξ := by
  unfold Ctx6.LowGate
  rw [htgt, hq]
  simp only [renameHist_fst, hiddenDescMap, Finset.forall_mem_image]
  have he := renameHist_withHid X q H (X.tgt b) ξ
  rw [← he]
  simp only [hiddenEntryEquiv_type, step2Tests_hiddenRename X q hq]
  try rfl

theorem highGate_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (b b' : X.State)
    (hkey : X.g.L.stKey b' = X.g.L.stKey b) (D : Finset (Id × X.Ty)) (ξ : Fin N) :
    X.HighGate (renameHist X q H) b' (hiddenDescMap X q D) ξ ↔ X.HighGate H b D ξ := by
  have hn : X.tgtName b' = X.tgtName b := congrArg primaryName6 hkey
  unfold Ctx6.HighGate
  rw [hn, locHid_hiddenRename X q]
  simp only [renameHist_fst, hiddenDescMap, Finset.forall_mem_image, hq]
  have he := renameHist_withPar X q H (X.tgtName b) ξ
  rw [← he]
  simp only [hiddenEntryEquiv_type, step2Tests_hiddenRename X q hq]
  try rfl

theorem s3Weight_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (b b' : X.State)
    (hkey : X.g.L.stKey b' = X.g.L.stKey b) (hmode : X.stMode b' = X.stMode b)
    (htgt : X.tgt b' = q (X.tgt b)) (D : Finset (Id × X.Ty)) (o : X.Data Id)
    (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.s3Weight (renameHist X q H) b' (hiddenDescMap X q D) (renameData X q o)
      (drop.map (hiddenEntryEquiv X q)) ξ = X.s3Weight H b D o drop ξ := by
  have hn : X.tgtName b' = X.tgtName b := congrArg primaryName6 hkey
  have heq (e : Id × X.Ty) :
      drop.map (hiddenEntryEquiv X q) = some (hiddenEntryEquiv X q e) ↔ drop = some e := by
    cases drop with
    | none => simp
    | some a => simp only [Option.map_some, Option.some.injEq, (hiddenEntryEquiv X q).injective.eq_iff]
  have hl (β : X.Ty) (t : X.Tuple) :
      X.lowLik (renameHist X q H) b' ξ (hiddenTypeMap X q β) t = X.lowLik H b ξ β t := by
    unfold Ctx6.lowLik
    rw [htgt, TβDel_hiddenRename X q hq, ← renameHist_withHid X q]
    exact tupleRatio_hiddenRename X q hq _ H β _ (.hid (X.tgt b)) t
  have hh (β : X.Ty) (t : X.Tuple) :
      X.highLik (renameHist X q H) b' ξ (hiddenTypeMap X q β) t = X.highLik H b ξ β t := by
    unfold Ctx6.highLik
    rw [hn, ← renameHist_withPar X q]
    exact tupleRatio_hiddenRename X q hq _ H β _ (.par (X.tgtName b)) t
  unfold Ctx6.s3Weight
  rw [hmode]
  cases X.stMode b
  · unfold Ctx6.lowWeight
    rw [htgt, hq, lowGate_hiddenRename X q hq H b b' hkey htgt]
    simp only [renameHist_fst]
    congr 1
    unfold hiddenDescMap
    rw [Finset.prod_image]
    · simp only [heq, renameData_apply, hiddenEntryEquiv_type, hl]
    · exact fun _ _ _ _ h => (hiddenEntryEquiv X q).injective h

  · unfold Ctx6.highWeight
    rw [hn, highGate_hiddenRename X q hq H b b' hkey,
      locDensity_hiddenRename X q hq]
    simp only [Ctx6.priorOf, renameHist_fst]
    congr 1
    unfold hiddenDescMap
    rw [Finset.prod_image]
    · simp only [heq, renameData_apply, hiddenEntryEquiv_type, hh]
    · exact fun _ _ _ _ h => (hiddenEntryEquiv X q).injective h

theorem s3Fail_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (b b' : X.State)
    (hkey : X.g.L.stKey b' = X.g.L.stKey b) (hmode : X.stMode b' = X.stMode b)
    (htgt : X.tgt b' = q (X.tgt b)) (D : Finset (Id × X.Ty)) (o : X.Data Id) :
    X.S3Fail (renameHist X q H) b' (hiddenDescMap X q D) (renameData X q o) ↔
      X.S3Fail H b D o := by
  have hm (drop : Option (Id × X.Ty)) :
      X.s3Mass (renameHist X q H) b' (hiddenDescMap X q D) (renameData X q o)
        (drop.map (hiddenEntryEquiv X q)) = X.s3Mass H b D o drop := by
    unfold Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ _
    exact s3Weight_hiddenRename X q hq H b b' hkey hmode htgt D o drop ξ
  have htrue : X.trueTarget (renameHist X q H) b' = X.trueTarget H b := by
    unfold Ctx6.trueTarget
    rw [hmode]
    cases X.stMode b
    · rw [htgt]
      exact renameHid_apply X q H.2 _
    · simp only [Ctx6.tgtName, hkey, renameHist]
  have hg : X.S3TrueGate (renameHist X q H) b' (hiddenDescMap X q D) ↔
      X.S3TrueGate H b D := by
    unfold Ctx6.S3TrueGate
    rw [hmode, htrue]
    cases X.stMode b
    · exact lowGate_hiddenRename X q hq H b b' hkey htgt D _
    · exact highGate_hiddenRename X q hq H b b' hkey D _
  have ht : X.S3Tests (renameHist X q H) b' (hiddenDescMap X q D) (renameData X q o) ↔
      X.S3Tests H b D o := by
    unfold Ctx6.S3Tests
    have hn : X.s3Mass (renameHist X q H) b' (hiddenDescMap X q D) (renameData X q o) none =
        X.s3Mass H b D o none := hm none
    rw [hn]
    have hd (e : Id × X.Ty) :
        X.s3Mass (renameHist X q H) b' (hiddenDescMap X q D) (renameData X q o)
          (some (hiddenEntryEquiv X q e)) = X.s3Mass H b D o (some e) := hm (some e)
    have hmatch (e : Id × X.Ty) : X.Matching b' (hiddenEntryEquiv X q e).2 ↔ X.Matching b e.2 := by
      simp only [Ctx6.Matching, hiddenEntryEquiv_type, hiddenTypeMap_mode, hiddenTypeMap_key, hmode, hkey]
    apply and_congr_right
    intro hp
    apply and_congr_right
    intro ht
    change (∀ e ∈ D.image (hiddenEntryEquiv X q),
      X.Matching b' e.2 → X.s3Thr * X.s3Mass (renameHist X q H) b'
        (hiddenDescMap X q D) (renameData X q o) (some e) ≤ X.s3Mass H b D o none) ↔ _
    simp only [Finset.forall_mem_image,hd,hmatch]
  simp only [Ctx6.S3Fail, hg, ht]

theorem step3HistRate_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (H : X.Hist) (b b' : X.State)
    (hkey : X.g.L.stKey b' = X.g.L.stKey b) (hmode : X.stMode b' = X.stMode b)
    (htgt : X.tgt b' = q (X.tgt b)) (D : Finset (Id × X.Ty)) :
    (X.dataLaw Id (renameHist X q H)).pr (fun o => X.S3Fail (renameHist X q H) b' (hiddenDescMap X q D) o) =
      (X.dataLaw Id H).pr (fun o => X.S3Fail H b D o) := by
  have hp := HypercubeRamsey.Lane_sol_s05_h1.pi_pr_equiv
    (fun e : Id × X.Ty => X.tupleLaw H e.2)
    (fun e : Id × X.Ty => X.tupleLaw (renameHist X q H) e.2)
    (hiddenEntryEquiv X q) (fun _ => Equiv.refl X.Tuple)
    (fun e o => congrArg (fun P : FinProb X.Tuple => P.w o)
      (tupleLaw_hiddenRename X q hq H e.2))
    (fun o => X.S3Fail (renameHist X q H) b' (hiddenDescMap X q D) o)
  change (FinProb.pi _).pr _ = _
  rw [hp]
  apply HypercubeRamsey.Lane_q_s06_stages.pr_congr
  intro o
  have he : (hiddenEntryEquiv X q).piCongr (fun _ => Equiv.refl X.Tuple) o = renameData X q o := by
    funext e
    have hh := Equiv.piCongr_apply_apply (hiddenEntryEquiv X q)
      (W := fun _ : Id × X.Ty => X.Tuple) (Z := fun _ : Id × X.Ty => X.Tuple)
      (fun _ => Equiv.refl X.Tuple) o ((hiddenEntryEquiv X q).symm e)
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply, renameData] using hh
  rw [he]
  exact s3Fail_hiddenRename X q hq H b b' hkey hmode htgt D o

theorem step3V0Rate_hiddenRename (q : Equiv.Perm X.HKey)
    (hq : ∀ ℓ, (q ℓ).1 = ℓ.1) (b b' : X.State)
    (hkey : X.g.L.stKey b' = X.g.L.stKey b) (hmode : X.stMode b' = X.stMode b)
    (htgt : X.tgt b' = q (X.tgt b)) (D : Finset (Id × X.Ty)) (v : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw Id ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b' (hiddenDescMap X q D) o))) =
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw Id ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b D o))) := by
  congr 1
  funext c
  let e : Equiv.Perm X.Hid := q.piCongr
    (W := fun _ : X.HKey => Fin N) (Z := fun _ : X.HKey => Fin N)
    (fun _ => Equiv.refl (Fin N))
  have hw : ∀ Z, (X.hidLaw (v,c)).w (e Z) = (X.hidLaw (v,c)).w Z := by
    apply HypercubeRamsey.Lane_sol_s05_h1.pi_weight_equiv
    intro ℓ z
    simp only [hq, Equiv.refl_apply]
  rw [HypercubeRamsey.Lane_sol_s05_h1.expect_equiv _ _ e hw]
  congr 1
  funext Z
  have he : e Z = renameHid X q Z := by
    funext ℓ
    have hh := Equiv.piCongr_apply_apply q
      (W := fun _ : X.HKey => Fin N) (Z := fun _ : X.HKey => Fin N)
      (fun _ => Equiv.refl (Fin N)) Z (q.symm ℓ)
    simpa only [Equiv.apply_symm_apply, Equiv.refl_apply, renameHid] using hh
  rw [he]
  exact step3HistRate_hiddenRename X q hq ((v,c),Z) b b' hkey hmode htgt D

def signTranslate (t : CubeVertex X.g.L.m) : Equiv.Perm (CubeVertex X.g.L.m) where
  toFun s := fun i => Bool.xor (t i) (s i)
  invFun s := fun i => Bool.xor (t i) (s i)
  left_inv s := by
    funext i
    change (t i ^^ (t i ^^ s i)) = s i
    cases t i <;> cases s i <;> rfl
  right_inv s := by
    funext i
    change (t i ^^ (t i ^^ s i)) = s i
    cases t i <;> cases s i <;> rfl

def hiddenTranslate (t : CubeVertex X.g.L.m) : Equiv.Perm X.HKey :=
  (Equiv.refl X.Key).prodCongr (signTranslate X t)

@[simp] theorem hiddenTranslate_key (t : CubeVertex X.g.L.m) (ℓ : X.HKey) :
    (hiddenTranslate X t ℓ).1 = ℓ.1 := rfl

@[simp] theorem signTranslate_self (t : CubeVertex X.g.L.m) :
    signTranslate X t t = fun _ => false := by
  funext i
  change (t i ^^ t i) = false
  cases t i <;> rfl

theorem signTranslate_flip (t s : CubeVertex X.g.L.m) (i : Fin X.g.L.m) :
    signTranslate X t (Function.update s i (!s i)) =
      Function.update (signTranslate X t s) i (!(signTranslate X t s i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self, signTranslate, Equiv.coe_fn_mk]
    cases t i <;> cases s i <;> rfl
  · simp only [signTranslate, Equiv.coe_fn_mk, Function.update_of_ne hj]

theorem makeType_hiddenTranslate (t s : CubeVertex X.g.L.m)
    (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    hiddenTypeMap X (hiddenTranslate X t) (makeType6 binAdjacent6 h s F j X.J) =
      makeType6 binAdjacent6 h (signTranslate X t s) F j X.J := by
  unfold makeType6
  split_ifs with hj
  · apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    dsimp only [hiddenTypeMap, Type6.key, Type6.mode, Type6.obs]
    ext ℓ
    simp only [lowObservations6,
      Finset.image_union, Finset.image_image, Function.comp_def]
    simp only [hiddenTranslate, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, signTranslate_flip,
      Finset.mem_union,Finset.mem_image]
  · apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    dsimp only [hiddenTypeMap, Type6.key, Type6.mode, Type6.obs]
    unfold highObservations6
    split_ifs <;> ext ℓ <;> simp [hiddenTranslate, Prod.map]

def zeroTarget (b : X.State) : X.State :=
  (fun _ => false, b.2.1, b.2.2.1, fun _ => 0, b.2.2.2.2)

@[simp] theorem zeroTarget_key (b : X.State) : X.g.L.stKey (zeroTarget X b) = X.g.L.stKey b := rfl
@[simp] theorem zeroTarget_mode (b : X.State) : X.stMode (zeroTarget X b) = X.stMode b := rfl
@[simp] theorem zeroTarget_sign (b : X.State) : X.g.L.stSign (zeroTarget X b) = fun _ => false := by
  funext i
  simp [zeroTarget, ChunkLayout6.stSign]

def normalizedDescriptor (b : X.State) (D : Finset (Id × X.Ty)) : Finset (Id × X.Ty) :=
  hiddenDescMap X (hiddenTranslate X (X.g.L.stSign b)) D

theorem step3V0Rate_normalizedDescriptor (b : X.State) (D : Finset (Id × X.Ty)) (v : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw Id ((v,c),Z)).pr
        (fun o => X.S3Fail ((v,c),Z) (zeroTarget X b) (normalizedDescriptor X b D) o))) =
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw Id ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b D o))) := by
  apply step3V0Rate_hiddenRename X (hiddenTranslate X (X.g.L.stSign b))
    (hiddenTranslate_key X _) b (zeroTarget X b) rfl rfl _ D v
  unfold Ctx6.tgt ChunkLayout6.stTarget
  simp only [zeroTarget_key, zeroTarget_sign, hiddenTranslate, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, signTranslate_self]

def fineSetVariants (F : Finset (Fin X.g.L.m)) : Finset (Finset (Fin X.g.L.m)) :=
  insert F (Finset.univ.biUnion fun i => {F.erase i, insert i F})

def zeroSignVariants : Finset (CubeVertex X.g.L.m) :=
  insert (fun _ => false) (Finset.univ.image fun i => flipVertex6 (fun _ => false) i)

theorem fineSetVariants_card (F : Finset (Fin X.g.L.m)) :
    (fineSetVariants X F).card ≤ 2 * X.m + 1 := by
  have h : (Finset.univ.biUnion fun i : Fin X.g.L.m => {F.erase i, insert i F}).card ≤ 2 * X.m := by
    calc
      _ ≤ ∑ i : Fin X.g.L.m, ({F.erase i, insert i F} : Finset _).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin X.g.L.m, 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.card_le_two
      _ = 2 * X.m := by simp [Ctx6.m]; omega
  exact (Finset.card_insert_le _ _).trans (by simpa [Nat.add_comm] using Nat.add_le_add_right h 1)

theorem zeroSignVariants_card : (zeroSignVariants X).card ≤ X.m + 1 := by
  exact (Finset.card_insert_le _ _).trans (by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin X.g.L.m)))
      (f := fun i => flipVertex6 (fun _ => false) i)
    simpa [Ctx6.m, Nat.add_comm] using Nat.add_le_add_right h 1)

private theorem finset_variant_of_agree_off (F F' : Finset (Fin X.g.L.m)) (i : Fin X.g.L.m)
    (h : ∀ j, j ≠ i → (j ∈ F' ↔ j ∈ F)) : F' ∈ fineSetVariants X F := by
  by_cases hF : i ∈ F
  · by_cases hF' : i ∈ F'
    · have he : F' = F := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hF,hF']
        · exact h j hj
      simp [fineSetVariants, he]
    · have he : F' = F.erase i := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hF']
        · simpa [Finset.mem_erase, hj] using h j hj
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, by simp⟩)
  · by_cases hF' : i ∈ F'
    · have he : F' = insert i F := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hF']
        · simp only [Finset.mem_insert, hj, false_or, h j hj]
      rw [he]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, by simp⟩)
    · have he : F' = F := by
        ext j
        by_cases hj : j = i
        · subst j; simp [hF,hF']
        · exact h j hj
      simp [fineSetVariants, he]

private theorem sign_variant_of_agree_off (t s : CubeVertex X.g.L.m) (i : Fin X.g.L.m)
    (h : ∀ j, j ≠ i → s j = t j) : signTranslate X t s ∈ zeroSignVariants X := by
  by_cases hi : s i = t i
  · have he : s = t := by
      funext j
      by_cases hj : j = i
      · simpa [hj] using hi
      · exact h j hj
    simp [he, signTranslate_self, zeroSignVariants]
  · have he : s = Function.update t i (!t i) := by
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self]
        cases hs : s i <;> cases ht : t i <;> simp_all
      · simp only [Function.update_of_ne hj]
        exact h j hj
    rw [he, signTranslate_flip, signTranslate_self]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem neighbor_fine_variants (b : X.State) (a : X.g.L.stNbr b) :
    signTranslate X (X.g.L.stSign b) (X.g.L.stSign a.1) ∈ zeroSignVariants X ∧
      X.g.L.stFlippable a.1 ∈ fineSetVariants X (X.g.L.stFlippable b) := by
  obtain ⟨u,v,hu,hv,hub,hva,hadj⟩ :=
    (show ∃ u v : CubeVertex n, ¬ IsEvenRole u ∧ IsEvenRole v ∧
      X.g.L.stateOf u = b ∧ X.g.L.stateOf v = a.1 ∧ (cube n).Adj u v from
        by simpa only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and] using a.2)
  have hsU : X.g.L.stSign b = X.g.L.sign u := by rw [← hub]; exact X.facts.sign_eq u
  have hsV : X.g.L.stSign a.1 = X.g.L.sign v := by rw [← hva]; exact X.facts.sign_eq v
  have hfU : X.g.L.stFlippable b = X.g.L.flippable u := by rw [← hub]; exact X.facts.flippable_eq u
  have hfV : X.g.L.stFlippable a.1 = X.g.L.flippable v := by rw [← hva]; exact X.facts.flippable_eq v
  let Diff : Finset (Fin n) := Finset.univ.filter fun q => u q ≠ v q
  have hc : Diff.card = 1 := by
    change _root_.hammingDist u v = 1 at hadj
    simpa [Diff, _root_.hammingDist] using hadj
  obtain ⟨q, hDiff⟩ := Finset.card_eq_one.mp hc
  have hother : ∀ j, j ≠ q → u j = v j := by
    intro j hj
    by_contra hne
    have hm : j ∈ Diff := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne⟩
    have : j = q := by simpa only [hDiff, Finset.mem_singleton] using hm
    exact hj this
  by_cases hq : ∃ i, q ∈ X.g.L.fineChunks i
  · obtain ⟨i, hqi⟩ := hq
    have hcount : ∀ j, j ≠ i → X.g.L.fineCount v j = X.g.L.fineCount u j := by
      intro j hj
      unfold ChunkLayout6.fineCount
      congr 1
      ext r
      by_cases hr : r ∈ X.g.L.fineChunks j
      · have hrq : r ≠ q := by
          intro he
          rw [he] at hr
          exact Finset.disjoint_left.mp (X.g.L.chunks_disjoint.2.2.1 j i hj) hr hqi
        simp only [Finset.mem_filter, hr, true_and, hother r hrq]
      · simp [hr]
    constructor
    · apply sign_variant_of_agree_off X _ _ i
      intro j hj
      rw [hsV, hsU]
      simp only [ChunkLayout6.sign, hcount j hj]
    · apply finset_variant_of_agree_off X _ _ i
      intro j hj
      rw [hfV, hfU]
      simp only [ChunkLayout6.flippable, Finset.mem_filter, Finset.mem_univ, true_and,
        hcount j hj]
  · have hsame : ∀ i r, r ∈ X.g.L.fineChunks i → u r = v r := by
      intro i r hr
      by_cases hrq : r = q
      · subst r
        exact False.elim (hq ⟨i,hr⟩)
      · exact hother r hrq
    have he := X.g.flips.nonfine_flip_fine u v hadj hsame
    rw [hsU, hsV, ← he.1, hfU, hfV, ← he.2.1]
    simp [signTranslate_self, zeroSignVariants, fineSetVariants]

def nearGenericTypes (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) : Finset X.Ty :=
  (X.C h).biUnion fun s => ({j-1,j,j+1} : Finset ℕ).image
    (fun r => makeType6 binAdjacent6 s (fun _ => false) F r X.J)

def nearPossibleTypes (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) : Finset X.Ty :=
  (X.C h).biUnion fun s => (zeroSignVariants X).biUnion fun t =>
    (fineSetVariants X F).biUnion fun F' => ({j-1,j,j+1} : Finset ℕ).image
      (fun r => makeType6 binAdjacent6 s t F' r X.J)

theorem normalized_neighbor_mem_possible (b : X.State) (a : X.g.L.stNbr b) :
    hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b)) (X.stType a.1) ∈
      nearPossibleTypes X (X.g.L.stKey b) (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by
  obtain ⟨hk,hs⟩ := Lane_q_s06_steps2.neighbor_key_severity6 X a.2
  obtain ⟨ht,hF⟩ := neighbor_fine_variants X b a
  have hj : X.g.L.stSeverity a.1 ∈
      ({X.g.L.stSeverity b-1,X.g.L.stSeverity b,X.g.L.stSeverity b+1} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    unfold Nat.dist at hs
    omega
  unfold Ctx6.stType ChunkLayout6.stType
  rw [makeType_hiddenTranslate X]
  exact Finset.mem_biUnion.mpr ⟨_,hk, Finset.mem_biUnion.mpr ⟨_,ht,
    Finset.mem_biUnion.mpr ⟨_,hF, Finset.mem_image.mpr ⟨_,hj,rfl⟩⟩⟩⟩

theorem odd_flippable_card_le (b : X.State) (hb : b ∈ X.g.L.oddStates) :
    (X.g.L.stFlippable b).card ≤ X.g.L.stSeverity b := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
  rw [X.facts.flippable_eq, X.facts.severity_eq]
  apply Finset.card_le_card
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

theorem card_biUnion_uniform {A B : Type*} [DecidableEq B]
    (S : Finset A) (F : A → Finset B) (C : ℕ) (h : ∀ a ∈ S, (F a).card ≤ C) :
    (S.biUnion F).card ≤ S.card * C := by
  calc
    _ ≤ ∑ a ∈ S, (F a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, C := by
      apply Finset.sum_le_sum
      exact h
    _ = S.card * C := by simp

theorem nearGenericTypes_card (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    (nearGenericTypes X h F j).card ≤ 1806 := by
  have hc : ({j-1,j,j+1} : Finset ℕ).card ≤ 3 := Finset.card_le_three
  have h1 := card_biUnion_uniform (X.C h)
    (fun s => ({j-1,j,j+1} : Finset ℕ).image
      (fun r => makeType6 binAdjacent6 s (fun _ => false) F r X.J))
    3 (fun s hs => Finset.card_image_le.trans hc)
  have hC : (X.C h).card ≤ 602 := X.g.flips.key_neighborhood_card h
  exact h1.trans (by omega)

theorem nearPossibleTypes_card (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    (nearPossibleTypes X h F j).card ≤ 1806 * (X.m+1) * (2*X.m+1) := by
  have hc : ({j-1,j,j+1} : Finset ℕ).card ≤ 3 := Finset.card_le_three
  have hi (s : X.Key) (t : CubeVertex X.g.L.m) (F' : Finset (Fin X.g.L.m)) :
      (({j-1,j,j+1} : Finset ℕ).image (fun r => makeType6 binAdjacent6 s t F' r X.J)).card ≤ 3 :=
    Finset.card_image_le.trans hc
  have hF (s : X.Key) (t : CubeVertex X.g.L.m) :=
    (card_biUnion_uniform (fineSetVariants X F) _ 3 (fun F' hF' => hi s t F')).trans
      (Nat.mul_le_mul_right 3 (fineSetVariants_card X F))
  have ht (s : X.Key) :=
    (card_biUnion_uniform (zeroSignVariants X) _ ((2*X.m+1)*3) (fun t ht => hF s t)).trans
      (Nat.mul_le_mul_right _ (zeroSignVariants_card X))
  have hs := (card_biUnion_uniform (X.C h) _ ((X.m+1)*((2*X.m+1)*3))
    (fun s hs => ht s)).trans (Nat.mul_le_mul_right _ (X.g.flips.key_neighborhood_card h))
  simpa only [nearPossibleTypes, show (602 : ℕ)*((X.m+1)*((2*X.m+1)*3)) =
    1806*(X.m+1)*(2*X.m+1) by ring] using hs

theorem normalized_generic_forms (b : X.State) :
    (Lane_q_s06_steps2.neighborTypeForms6 X b).image
      (hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b))) =
      nearGenericTypes X (X.g.L.stKey b) (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by
  change ((X.C (X.g.L.stKey b)).biUnion fun h =>
    ({X.g.L.stSeverity b-1,X.g.L.stSeverity b,X.g.L.stSeverity b+1} : Finset ℕ).image
      (fun j => makeType6 binAdjacent6 h (X.g.L.stSign b) (X.g.L.stFlippable b) j X.J)).image _ = _
  simp only [Finset.biUnion_image, Finset.image_image, Function.comp_def,
    makeType_hiddenTranslate, signTranslate_self, nearGenericTypes]

theorem normalizedDescriptor_split (hn : 4 ≤ n) (b : X.State) (hb : b ∈ X.g.L.oddStates)
    (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs b) :
    normalizedDescriptor X b D ⊆ (Finset.univ : Finset (Fin X.T)) ×ˢ
        nearPossibleTypes X (X.g.L.stKey b) (X.g.L.stFlippable b) (X.g.L.stSeverity b) ∧
      ((normalizedDescriptor X b D) \ ((Finset.univ : Finset (Fin X.T)) ×ˢ
        nearGenericTypes X (X.g.L.stKey b) (X.g.L.stFlippable b) (X.g.L.stSeverity b))).card ≤
          43 * (X.J+1) := by
  obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hD
  have himage : normalizedDescriptor X b (X.descOf b φ) =
      Finset.univ.image (fun a : X.g.L.stNbr b =>
        (φ a, hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b)) (X.stType a.1))) := by
    simp only [normalizedDescriptor, hiddenDescMap, Ctx6.descOf, Finset.image_image]
    rfl
  rw [himage]
  constructor
  · intro e he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, normalized_neighbor_mem_possible X b a⟩
  · have hsub : ((Finset.univ.image (fun a : X.g.L.stNbr b =>
        (φ a, hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b)) (X.stType a.1)))) \
        ((Finset.univ : Finset (Fin X.T)) ×ˢ nearGenericTypes X (X.g.L.stKey b) (X.g.L.stFlippable b)
          (X.g.L.stSeverity b))) ⊆
        (exceptionalNeighbors X b).image (fun a =>
          (φ a, hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b)) (X.stType a.1))) := by
      intro e he
      obtain ⟨he,hng⟩ := Finset.mem_sdiff.mp he
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      rcases neighbor_type_generic_or_exceptional X b a with hg | hb
      · have hg' : hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b)) (X.stType a.1) ∈
            nearGenericTypes X (X.g.L.stKey b) (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by
          rw [← normalized_generic_forms X b]
          exact Finset.mem_image.mpr ⟨_,hg,rfl⟩
        exact False.elim (hng (Finset.mem_product.mpr ⟨Finset.mem_univ _,hg'⟩))
      · exact Finset.mem_image.mpr ⟨a,hb,rfl⟩
    have hcard : (exceptionalNeighbors X b).card ≤ 1+21*(X.J+2) := by
      simpa only [exceptionalNeighbors] using Lane_q_s06_steps2.descriptorBadStates6_card X b hb hn
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by omega))

def smallSubsets {A : Type*} [DecidableEq A] (S : Finset A) (r : ℕ) : Finset (Finset A) :=
  (Finset.range (r+1)).biUnion fun k => S.powersetCard k

theorem mem_smallSubsets {A : Type*} [DecidableEq A] (S : Finset A) (r : ℕ) (A' : Finset A) :
    A' ∈ smallSubsets S r ↔ A' ⊆ S ∧ A'.card ≤ r := by
  simp only [smallSubsets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨k,hk,hsub,hcard⟩
    exact ⟨hsub,by omega⟩
  · rintro ⟨hsub,hcard⟩
    exact ⟨A'.card,by omega,hsub,rfl⟩

theorem smallSubsets_card {A : Type*} [Fintype A] [DecidableEq A] (S : Finset A) (r : ℕ) :
    (smallSubsets S r).card ≤ (S.card+2)^(2*r) :=
  Lane_q_s06_steps2.smallPowersetCount6 S r

def nearDescriptorCodes (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    Finset (Finset (Fin X.T × X.Ty)) :=
  (((Finset.univ : Finset (Fin X.T)) ×ˢ nearGenericTypes X h F j).powerset).biUnion fun Dg =>
    (smallSubsets ((Finset.univ : Finset (Fin X.T)) ×ˢ nearPossibleTypes X h F j) (43*(X.J+1))).image
      (fun De => Dg ∪ De)

theorem normalizedDescriptor_mem_nearCodes (hn : 4 ≤ n) (b : X.State) (hb : b ∈ X.g.L.oddStates)
    (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs b) :
    normalizedDescriptor X b D ∈ nearDescriptorCodes X (X.g.L.stKey b)
      (X.g.L.stFlippable b) (X.g.L.stSeverity b) := by
  obtain ⟨hsub,hcard⟩ := normalizedDescriptor_split X hn b hb D hD
  let A := normalizedDescriptor X b D
  let S := (Finset.univ : Finset (Fin X.T)) ×ˢ nearGenericTypes X (X.g.L.stKey b)
    (X.g.L.stFlippable b) (X.g.L.stSeverity b)
  refine Finset.mem_biUnion.mpr ⟨A ∩ S,Finset.mem_powerset.mpr Finset.inter_subset_right,?_⟩
  refine Finset.mem_image.mpr ⟨A \ S,?_,?_⟩
  · exact (mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset.trans hsub,hcard⟩
  · rw [Finset.union_comm]
    exact Finset.sdiff_union_inter A S

theorem nearDescriptorCodes_card (h : X.Key) (F : Finset (Fin X.g.L.m)) (j : ℕ) :
    (nearDescriptorCodes X h F j).card ≤ 2^(1806*X.T) *
      (X.T*1806*(X.m+1)*(2*X.m+1)+2)^(86*(X.J+1)) := by
  have hinner (Dg : Finset (Fin X.T × X.Ty)) :
      ((smallSubsets ((Finset.univ : Finset (Fin X.T)) ×ˢ nearPossibleTypes X h F j) (43*(X.J+1))).image
        (fun De => Dg ∪ De)).card ≤
      (X.T*1806*(X.m+1)*(2*X.m+1)+2)^(86*(X.J+1)) := by
    apply Finset.card_image_le.trans
    have hsmall := smallSubsets_card ((Finset.univ : Finset (Fin X.T)) ×ˢ nearPossibleTypes X h F j) (43*(X.J+1))
    have hb : ((Finset.univ : Finset (Fin X.T)) ×ˢ nearPossibleTypes X h F j).card+2 ≤
        X.T*1806*(X.m+1)*(2*X.m+1)+2 := by
      simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have hc := Nat.mul_le_mul_left X.T (nearPossibleTypes_card X h F j)
      nlinarith
    exact hsmall.trans (by simpa only [show 2*(43*(X.J+1)) = 86*(X.J+1) by omega] using Nat.pow_le_pow_left hb (86*(X.J+1)))
  have hgeneric : (((Finset.univ : Finset (Fin X.T)) ×ˢ nearGenericTypes X h F j).powerset).card ≤ 2^(1806*X.T) := by
    rw [Finset.card_powerset, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by omega)
      ((Nat.mul_le_mul_left X.T (nearGenericTypes_card X h F j)).trans_eq (Nat.mul_comm _ _))
  exact (card_biUnion_uniform _ _ _ (fun Dg hDg => hinner Dg)).trans
    (Nat.mul_le_mul_right _ hgeneric)

def highEmptyTypes (h : X.Key) : Finset X.Ty :=
  (X.C h).image fun s => (s, Mode6.high, 0, ∅)

theorem normalizedDescriptor_high_away (b : X.State)
    (hj : X.J+2 < X.g.L.stSeverity b) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs b) :
    normalizedDescriptor X b D ⊆ (Finset.univ : Finset (Fin X.T)) ×ˢ highEmptyTypes X (X.g.L.stKey b) := by
  obtain ⟨φ,hφ,rfl⟩ := Finset.mem_image.mp hD
  intro e he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hk,hs⟩ := Lane_q_s06_steps2.neighbor_key_severity6 X a.2
  have hj' : X.J+1 < X.g.L.stSeverity a.1 := by unfold Nat.dist at hs; omega
  have htype : hiddenTypeMap X (hiddenTranslate X (X.g.L.stSign b)) (X.stType a.1) =
      (X.g.L.stKey a.1, Mode6.high, 0, ∅) := by
    simp [Ctx6.stType, ChunkLayout6.stType, makeType6, highObservations6,
      show ¬ X.g.L.stSeverity a.1 ≤ X.J by omega,
      show X.g.L.stSeverity a.1 ≠ X.J+1 by omega,
      hiddenTypeMap, Type6.key, Type6.mode, Type6.obs]
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨_,hk,htype.symm⟩⟩

abbrev NormalizedShape := X.Key × Mode6 × Finset (Fin X.T × X.Ty)

def normalizedShapeFintype : Fintype (NormalizedShape X) :=
  inferInstanceAs (Fintype (X.Key × Mode6 × Finset (Fin X.T × X.Ty)))

def normalizedShape (b : X.State) (D : Finset (Fin X.T × X.Ty)) : NormalizedShape X :=
  (X.g.L.stKey b, X.stMode b, normalizedDescriptor X b D)

theorem normalizedShape_rates (b b' : X.State) (D D' : Finset (Fin X.T × X.Ty))
    (h : normalizedShape X b D = normalizedShape X b' D') (v : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw (Fin X.T) ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b D o))) =
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v,c)).expect
      (fun Z => (X.dataLaw (Fin X.T) ((v,c),Z)).pr (fun o => X.S3Fail ((v,c),Z) b' D' o))) := by
  have hk : X.g.L.stKey b = X.g.L.stKey b' := congrArg Prod.fst h
  have hm : X.stMode b = X.stMode b' := congrArg (fun s => s.2.1) h
  have hD : normalizedDescriptor X b D = normalizedDescriptor X b' D' := congrArg (fun s => s.2.2) h
  rw [← step3V0Rate_normalizedDescriptor X b D v, ← step3V0Rate_normalizedDescriptor X b' D' v, hD]
  apply step3V0Rate_targetShape X
  apply Prod.ext hk
  apply Prod.ext hm
  exact (zeroTarget_sign X b).trans (zeroTarget_sign X b').symm

def nearShapeCodes : Finset (NormalizedShape X) :=
  (Finset.univ : Finset X.Key).biUnion fun h =>
    (smallSubsets (Finset.univ : Finset (Fin X.g.L.m)) (X.J+2)).biUnion fun F =>
      (Finset.range (X.J+3)).biUnion fun j =>
        (nearDescriptorCodes X h F j).image fun D => (h, modeOf6 X.J j, D)

def highShapeCodes : Finset (NormalizedShape X) :=
  (Finset.univ : Finset X.Key).biUnion fun h =>
    (((Finset.univ : Finset (Fin X.T)) ×ˢ highEmptyTypes X h).powerset).image fun D => (h, Mode6.high, D)

theorem normalizedShape_cover (hn : 4 ≤ n) :
    (X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)) ⊆
      nearShapeCodes X ∪ highShapeCodes X := by
  intro s hs
  obtain ⟨b,hb,hs⟩ := Finset.mem_biUnion.mp hs
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hs
  by_cases hj : X.g.L.stSeverity b ≤ X.J+2
  · apply Finset.mem_union_left
    refine Finset.mem_biUnion.mpr ⟨X.g.L.stKey b,Finset.mem_univ _,?_⟩
    refine Finset.mem_biUnion.mpr ⟨X.g.L.stFlippable b,?_,?_⟩
    · exact (mem_smallSubsets _ _ _).mpr ⟨Finset.subset_univ _,
        (odd_flippable_card_le X b hb).trans hj⟩
    · refine Finset.mem_biUnion.mpr ⟨X.g.L.stSeverity b,Finset.mem_range.mpr (by omega),?_⟩
      exact Finset.mem_image.mpr ⟨normalizedDescriptor X b D,
        normalizedDescriptor_mem_nearCodes X hn b hb D hD,rfl⟩
  · apply Finset.mem_union_right
    refine Finset.mem_biUnion.mpr ⟨X.g.L.stKey b,Finset.mem_univ _,?_⟩
    refine Finset.mem_image.mpr ⟨normalizedDescriptor X b D,
      Finset.mem_powerset.mpr (normalizedDescriptor_high_away X b (by omega) D hD),?_⟩
    simp [normalizedShape, Ctx6.stMode, modeOf6, show ¬ X.g.L.stSeverity b ≤ X.J by omega]

theorem key_card : Fintype.card X.Key = 2*(n+1)^300 := by
  have hflag : Nat.card KeyFlag6 = 2 := by
    rw [Nat.card_eq_fintype_card]
    change ({KeyFlag6.interior,KeyFlag6.boundary} : Finset KeyFlag6).card = 2
    simp
  rw [Fintype.card_eq_nat_card]
  change Nat.card ((Fin 300 → Fin (n+1)) × KeyFlag6) = _
  rw [Nat.card_prod,Nat.card_fun,hflag]
  simp only [Nat.card_fin]
  omega

theorem normalizedShape_card_preliminary (hn : 4 ≤ n) :
    (X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)).card ≤
      (2*(n+1)^300)*((X.m+2)^(2*(X.J+2))*(X.J+3)*
        (2^(1806*X.T)*(X.T*1806*(X.m+1)*(2*X.m+1)+2)^(86*(X.J+1))) + 2^(602*X.T)) := by
  let B := 2^(1806*X.T)*(X.T*1806*(X.m+1)*(2*X.m+1)+2)^(86*(X.J+1))
  have hj (h : X.Key) (F : Finset (Fin X.g.L.m)) :
      ((Finset.range (X.J+3)).biUnion fun j =>
        (nearDescriptorCodes X h F j).image fun D => (h,modeOf6 X.J j,D)).card ≤ (X.J+3)*B := by
    exact (card_biUnion_uniform _ _ B (fun j hj =>
      Finset.card_image_le.trans (nearDescriptorCodes_card X h F j))).trans_eq (by simp)
  have hF (h : X.Key) :
      ((smallSubsets (Finset.univ : Finset (Fin X.g.L.m)) (X.J+2)).biUnion fun F =>
        (Finset.range (X.J+3)).biUnion fun j =>
          (nearDescriptorCodes X h F j).image fun D => (h,modeOf6 X.J j,D)).card ≤
        (X.m+2)^(2*(X.J+2))*((X.J+3)*B) := by
    apply (card_biUnion_uniform _ _ _ (fun F hF => hj h F)).trans
    apply Nat.mul_le_mul_right
    simpa [Ctx6.m] using smallSubsets_card (Finset.univ : Finset (Fin X.g.L.m)) (X.J+2)
  have hnear : (nearShapeCodes X).card ≤
      (2*(n+1)^300)*((X.m+2)^(2*(X.J+2))*((X.J+3)*B)) := by
    exact (card_biUnion_uniform _ _ _ (fun h hh => hF h)).trans_eq (by rw [Finset.card_univ,key_card])
  have hhigh : (highShapeCodes X).card ≤ (2*(n+1)^300)*2^(602*X.T) := by
    apply (card_biUnion_uniform _ _ _ (fun h hh => ?_)).trans_eq (by rw [Finset.card_univ,key_card])
    apply Finset.card_image_le.trans
    rw [Finset.card_powerset,Finset.card_product,Finset.card_univ,Fintype.card_fin]
    apply Nat.pow_le_pow_right (by omega)
    have hc : (highEmptyTypes X h).card ≤ 602 :=
      Finset.card_image_le.trans (X.g.flips.key_neighborhood_card h)
    exact (Nat.mul_le_mul_left X.T hc).trans_eq (Nat.mul_comm _ _)
  calc
    _ ≤ (nearShapeCodes X ∪ highShapeCodes X).card := Finset.card_le_card (normalizedShape_cover X hn)
    _ ≤ (nearShapeCodes X).card+(highShapeCodes X).card := Finset.card_union_le _ _
    _ ≤ (2*(n+1)^300)*((X.m+2)^(2*(X.J+2))*((X.J+3)*B)) +
        (2*(n+1)^300)*2^(602*X.T) := Nat.add_le_add hnear hhigh
    _ = _ := by rw [←Nat.mul_add,←Nat.mul_assoc]

theorem normalizedShape_card_polynomial (hn : 4 ≤ n) (hm : 603 ≤ X.m)
    (hJ : X.J ≤ X.m) (hT : X.T ≤ X.m) :
    (X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)).card ≤
      4*(n+1)^300*(X.m+2)^(608*(X.J+1))*2^(1806*X.T) := by
  let a := X.m+2
  let g := 2^(1806*X.T)
  let B := X.T*1806*(X.m+1)*(2*X.m+1)+2
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hconst : 1806 ≤ a^2 := by dsimp [a]; nlinarith
  have htwo : 2*X.m+1 ≤ a^2 := by dsimp [a]; nlinarith
  have hB : B ≤ a^7 := by
    have h1 : X.T*1806*(X.m+1)*(2*X.m+1) ≤ a*a^2*a*a^2 := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · exact Nat.mul_le_mul (by dsimp [a]; omega) hconst
        · dsimp [a]; omega
      · exact htwo
    have hpow : a*a^2*a*a^2 = a^6 := by ring
    rw [hpow] at h1
    have h6 : 2 ≤ a^6 := by
      have hp := Nat.pow_le_pow_left ha 6
      norm_num at hp
      omega
    have h67 : a^6+2 ≤ a^7 := by rw [pow_succ]; nlinarith
    exact (Nat.add_le_add_right h1 2).trans h67
  have hF : a^(2*(X.J+2)) ≤ a^(4*(X.J+1)) := Nat.pow_le_pow_right (by omega) (by omega)
  have hsev : X.J+3 ≤ a^(2*(X.J+1)) := by
    have h1 : X.J+3 ≤ a^2 := by dsimp [a]; nlinarith
    exact h1.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hrare : B^(86*(X.J+1)) ≤ a^(602*(X.J+1)) := by
    have h := Nat.pow_le_pow_left hB (86*(X.J+1))
    simpa only [← pow_mul, show 7*(86*(X.J+1)) = 602*(X.J+1) by ring] using h
  have hnear : a^(2*(X.J+2))*(X.J+3)*(g*B^(86*(X.J+1))) ≤ a^(608*(X.J+1))*g := by
    calc
      _ ≤ (a^(4*(X.J+1))*a^(2*(X.J+1)))*(g*a^(602*(X.J+1))) :=
        Nat.mul_le_mul (Nat.mul_le_mul hF hsev) (Nat.mul_le_mul_left g hrare)
      _ = (a^(4*(X.J+1))*a^(2*(X.J+1))*a^(602*(X.J+1)))*g := by ac_rfl
      _ = a^(608*(X.J+1))*g := by rw [←pow_add,←pow_add,
        show 4*(X.J+1)+2*(X.J+1)+602*(X.J+1) = 608*(X.J+1) by omega]
  have hhigh : 2^(602*X.T) ≤ a^(608*(X.J+1))*g := by
    have h1 : 2^(602*X.T) ≤ g := Nat.pow_le_pow_right (by omega)
      (by omega)
    have hp : 1 ≤ a^(608*(X.J+1)) := Nat.one_le_pow _ _ (by omega)
    exact h1.trans (by simpa using Nat.mul_le_mul_right g hp)
  have hc := normalizedShape_card_preliminary X hn
  change _ ≤ (2*(n+1)^300)*(a^(2*(X.J+2))*(X.J+3)*(g*B^(86*(X.J+1)))+2^(602*X.T)) at hc
  calc
    _ ≤ _ := hc
    _ ≤ (2*(n+1)^300)*(2*(a^(608*(X.J+1))*g)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by
      have hmul (p q r : ℕ) : (2*p)*(2*(q*r)) = 4*p*q*r := by ring
      exact hmul ((n+1)^300) (a^(608*(X.J+1))) g

theorem coarse_factor_le_fine_power (α : ℝ) (hα : 0 < α) (C : ℕ)
    (hC : 602 ≤ α*C) (hn : 2 ≤ n) (hm : (n : ℝ)^α ≤ X.m) (hJ : C ≤ X.J+1) :
    4*(n+1)^300 ≤ (X.m+2)^(X.J+1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnat : 4*(n+1)^300 ≤ n^602 := by
    have h4 : 4 ≤ n^2 := by nlinarith
    have h1 : n+1 ≤ n^2 := by nlinarith
    calc
      _ ≤ n^2*(n^2)^300 := Nat.mul_le_mul h4 (Nat.pow_le_pow_left h1 300)
      _ = n^602 := by rw [←pow_mul,←pow_add]
  have hnm : n^602 ≤ X.m^C := by
    have h : (n : ℝ)^602 ≤ (X.m : ℝ)^C := by
      calc
        _ = (n : ℝ)^(602 : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (n : ℝ)^(α*C) := Real.rpow_le_rpow_of_exponent_le hn1 hC
        _ = ((n : ℝ)^α)^C := by rw [Real.rpow_mul hn0,Real.rpow_natCast]
        _ ≤ (X.m : ℝ)^C := pow_le_pow_left₀ (Real.rpow_nonneg hn0 _) hm C
    exact_mod_cast h
  exact hnat.trans (hnm.trans ((Nat.pow_le_pow_left (by omega) C).trans
    (Nat.pow_le_pow_right (by omega) hJ)))

theorem normalizedShape_card_exp (hn : 4 ≤ n) (hm : 603 ≤ X.m)
    (hJ : X.J ≤ X.m) (hT : X.T ≤ X.m)
    (hcoarse : 4*(n+1)^300 ≤ (X.m+2)^(X.J+1)) :
    ((X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)).card : ℝ) ≤
      Real.exp (10^4*(X.T*Real.log (X.T+2)+(X.J+1)*Real.log (X.m+2))) := by
  have hc : (X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)).card ≤
      (X.m+2)^(609*(X.J+1))*2^(1806*X.T) := by
    calc
      _ ≤ _ := normalizedShape_card_polynomial X hn hm hJ hT
      _ ≤ (X.m+2)^(X.J+1)*(X.m+2)^(608*(X.J+1))*2^(1806*X.T) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoarse)
      _ = _ := by rw [←pow_add,show (X.J+1)+608*(X.J+1) = 609*(X.J+1) by omega]
  have hr : ((X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)).card : ℝ) ≤
      (X.m+2:ℝ)^(609*(X.J+1))*(2:ℝ)^(1806*X.T) := by exact_mod_cast hc
  have hmexp := Lane_q_s06_steps2.natPow_eq_exp_log6 (X.m+2) (609*(X.J+1)) (by omega)
  have htexp := Lane_q_s06_steps2.natPow_eq_exp_log6 2 (1806*X.T) (by omega)
  have hlm : 0 ≤ Real.log (X.m+2:ℝ) := Real.log_nonneg (by have h : (0:ℝ) ≤ X.m := Nat.cast_nonneg _; linarith)
  have hlt : 0 ≤ Real.log (X.T+2:ℝ) := Real.log_nonneg (by have h : (0:ℝ) ≤ X.T := Nat.cast_nonneg _; linarith)
  have hl2 : Real.log (2:ℝ) ≤ Real.log (X.T+2:ℝ) := Real.log_le_log (by norm_num) (by have h : (0:ℝ) ≤ X.T := Nat.cast_nonneg _; linarith)
  calc
    _ ≤ _ := hr
    _ = Real.exp (((609*(X.J+1):ℕ):ℝ)*Real.log (X.m+2:ℝ)+
      ((1806*X.T:ℕ):ℝ)*Real.log (2:ℝ)) := by
      rw [show (X.m+2:ℝ)^ (609*(X.J+1)) = _ by simpa only [Nat.cast_add,Nat.cast_ofNat] using hmexp,
        show (2:ℝ)^(1806*X.T) = _ by simpa only [Nat.cast_ofNat] using htexp,←Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ (1806:ℝ)*X.T)
      have h2 := mul_nonneg (by positivity : 0 ≤ (X.J+1:ℝ)) hlm
      have h3 := mul_nonneg (Nat.cast_nonneg X.T) hlt
      push_cast
      norm_num
      push_cast at h1
      nlinarith

/-- Count the same shapes with an explicitly supplied equality instance. -/
def normalizedShapeSet (d : DecidableEq (NormalizedShape X)) : Finset (NormalizedShape X) :=
  @Finset.biUnion X.State (NormalizedShape X) d X.g.L.oddStates
    (fun b => @Finset.image (Finset (Fin X.T × X.Ty)) (NormalizedShape X) d
      (normalizedShape X b) (X.absDescs b))

def canonicalNormalizedShapeSet : Finset (NormalizedShape X) :=
  X.g.L.oddStates.biUnion fun b => (X.absDescs b).image (normalizedShape X b)

theorem normalizedShapeSet_card_exp (d : DecidableEq (NormalizedShape X))
    (hn : 4 ≤ n) (hm : 603 ≤ X.m) (hJ : X.J ≤ X.m) (hT : X.T ≤ X.m)
    (hcoarse : 4*(n+1)^300 ≤ (X.m+2)^(X.J+1)) :
    ((normalizedShapeSet X d).card : ℝ) ≤
      Real.exp (10^4*(X.T*Real.log (X.T+2)+(X.J+1)*Real.log (X.m+2))) := by
  have he : normalizedShapeSet X d = canonicalNormalizedShapeSet X := by
    ext s
    simp only [normalizedShapeSet,canonicalNormalizedShapeSet,Finset.mem_biUnion,Finset.mem_image]
  rw [he]
  exact normalizedShape_card_exp X hn hm hJ hT hcoarse

end

end HypercubeRamsey.S06.Lane_sol_s06_shapes
