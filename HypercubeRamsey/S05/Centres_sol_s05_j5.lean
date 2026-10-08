import HypercubeRamsey.S05.Centres_sol_s05_centres_marking
import HypercubeRamsey.S05.History_sol_s05_1f

namespace HypercubeRamsey.Lane_sol_s05_j5

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)
variable {I J : Type} [DecidableEq I] [DecidableEq J]

abbrev pairMap {A : Type} (f : I → J) (c : I × A) : J × A := (f c.1, c.2)

theorem pairMap_injective {A : Type} {f : I → J} (hf : Function.Injective f) :
    Function.Injective (pairMap (A := A) f) := by
  classical
  intro a b h
  exact Prod.ext (hf (congrArg Prod.fst h)) (congrArg (fun c : J × A => c.2) h)

abbrev mapRecord (f : I → J) (r : X.RecordOn I) : X.RecordOn J :=
  (r.1, r.2.1.image (pairMap f), r.2.2.1.image (pairMap f), r.2.2.2.map (pairMap f))

abbrev pullArrays (f : I → J) (a : X.ArraysOn J) : X.ArraysOn I :=
  fun c => a (pairMap f c)

theorem hitSet_map (H : X.KeyHist) (f : I → J) (a : X.ArraysOn J)
    (c : I × X.Ty) (y : Fin N) :
    X.hitSet (pullArrays X f a) c y = X.hitSet a (pairMap f c) y := rfl

theorem refSubset_map (H : X.KeyHist) (f : I → J) (a : X.ArraysOn J)
    (c : I × X.Ty) (k : Option X.Key) :
    X.refSubsetOn H (pullArrays X f a) c k = X.refSubsetOn H a (pairMap f c) k := rfl

theorem refs_map (H : X.KeyHist) (f : I → J) (r : X.RecordOn I) (a : X.ArraysOn J) :
    X.refsOn H (mapRecord X f r) a =
      (X.refsOn H r (pullArrays X f a)).image (pairMap f) := by
  classical
  classical
  classical
  simp only [Setup5.refsOn, mapRecord, Finset.image_image]
  ext c
  simp only [Finset.mem_image]
  constructor <;> rintro ⟨d, hd, he⟩ <;> refine ⟨d, hd, ?_⟩ <;>
    simpa only [Function.comp_apply, pairMap, Setup5.refSubsetOn, Setup5.hitSet, pullArrays] using he

theorem gate_map (H : X.KeyHist) (f : I → J) (r : X.RecordOn I) (a : X.ArraysOn J)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.candGateOn H (mapRecord X f r) a θ ↔
      X.candGateOn H r (pullArrays X f a) θ := by
  classical
  simp only [Setup5.candGateOn, mapRecord, Finset.forall_mem_image]
  constructor
  · rintro ⟨hg, hm⟩
    refine ⟨hg, ?_⟩
    intro c M hc h
    exact hm (pairMap f c) M (by simp [hc, pairMap]) h
  · rintro ⟨hg, hm⟩
    refine ⟨hg, ?_⟩
    intro c M hc h
    obtain ⟨d, hd, he⟩ := Option.mem_map.mp (show (c.1, c.2, M) ∈ r.2.2.2.map (pairMap f) from hc)
    have he1 : f d.1 = c.1 := congrArg Prod.fst he
    have he2 : d.2 = (c.2, M) := congrArg Prod.snd he
    have heK := congrArg Prod.fst he2
    have heM := congrArg Prod.snd he2
    have hh := hm (d.1, d.2.1) d.2.2 hd h
    change X.p.usedBlocks n ≤ (X.hitSet a (f d.1, d.2.1) (θ h)).card ∧
      X.firstK (X.hitSet a (f d.1, d.2.1) (θ h)) (X.p.usedBlocks n) = d.2.2 at hh
    simpa only [he1, heK, heM, Prod.mk.eta] using hh

theorem inRef_map (f : I → J) (hf : Function.Injective f)
    (e : Option (I × X.Ty × Finset (Fin X.blockBound))) (c : I × X.Ty)
    (i : Fin (X.p.typeBlocks n c.2)) :
    X.InRef (e.map (pairMap f)) (pairMap f c) i ↔ X.InRef e c i := by
  classical
  simp only [Setup5.InRef]
  constructor
  · rintro ⟨d, hd, hc, hi⟩
    obtain ⟨d', hd', he⟩ := Option.mem_map.mp (show d ∈ e.map (pairMap f) from hd)
    cases he
    have hec : c = (d'.1, d'.2.1) :=
      pairMap_injective hf (show pairMap f c = pairMap f (d'.1, d'.2.1) from hc)
    exact ⟨d', hd', hec, hi⟩
  · rintro ⟨d, hd, hc, hi⟩
    exact ⟨pairMap f d, by simp [hd], by simp [pairMap, hc], hi⟩

theorem likelihood_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N)
    (e : Option (I × X.Ty × Finset (Fin X.blockBound))) :
    X.obsLikOn H (mapRecord X f r) a θ (e.map (pairMap f)) =
      X.obsLikOn H r (pullArrays X f a) θ e := by
  classical
  simp only [Setup5.obsLikOn, mapRecord, Finset.filter_image]
  rw [Finset.prod_image (fun c _ d _ h => pairMap_injective hf h)]
  apply Finset.prod_congr rfl
  intro c hc
  apply Finset.prod_congr rfl
  intro i hi
  simp only [inRef_map X f hf, pullArrays, pairMap]

theorem mass_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J)
    (e : Option (I × X.Ty × Finset (Fin X.blockBound))) :
    X.step3MassOn H (mapRecord X f r) a (e.map (pairMap f)) =
      X.step3MassOn H r (pullArrays X f a) e := by
  classical
  simp only [Setup5.step3MassOn, gate_map X H f r a,
    likelihood_map X H f hf r a]

theorem post_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J)
    (e : Option (I × X.Ty × Finset (Fin X.blockBound)))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn H (mapRecord X f r) a (e.map (pairMap f)) θ =
      X.step3PostOn H r (pullArrays X f a) e θ := by
  classical
  simp only [Setup5.step3PostOn, gate_map X H f r a,
    likelihood_map X H f hf r a, mass_map X H f hf r a]

theorem source_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J) (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highSource H (mapRecord X f r) a h = X.highSource H r (pullArrays X f a) h := by
  classical
  unfold Setup5.highSource
  have hp := funext (post_map X H f hf r a none)
  simpa only [Option.map_none] using congrArg (fun P => X.condCoord P (H.2 r.1) h) hp

theorem deleted_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J)
    (c : I × X.Ty × Finset (Fin X.blockBound)) (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highDeleted H (mapRecord X f r) a (pairMap f c) h =
      X.highDeleted H r (pullArrays X f a) c h := by
  classical
  unfold Setup5.highDeleted
  have hp := funext (post_map X H f hf r a (some c))
  simpa only [Option.map_some] using
    congrArg (fun P => X.smooth (X.condCoord P (H.2 r.1) h)) hp

theorem capped_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J) :
    X.HighCapped H (mapRecord X f r) a ↔ X.HighCapped H r (pullArrays X f a) := by
  classical
  simp only [Setup5.HighCapped, source_map X H f hf r a]

def refEquiv (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J) :
    {c // c ∈ X.refsOn H r (pullArrays X f a)} ≃
      {c // c ∈ X.refsOn H (mapRecord X f r) a} :=
  Equiv.ofBijective
    (fun c => ⟨pairMap f c.1, by
      rw [refs_map]
      exact Finset.mem_image.mpr ⟨c.1, c.2, rfl⟩⟩)
    ⟨fun c d h => Subtype.ext (pairMap_injective hf (congrArg Subtype.val h)), by
      intro d
      have hd := d.2
      have hd' : d.1 ∈ (X.refsOn H r (pullArrays X f a)).image (pairMap f) :=
        (refs_map X H f r a) ▸ hd
      obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hd'
      exact ⟨⟨c, hc⟩, Subtype.ext he⟩⟩

theorem price_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J)
    (hp : X.HighPriceFeasible H r (pullArrays X f a)) :
    X.HighPriceFeasible H (mapRecord X f r) a := by
  classical
  intro price hprice hsum
  let e := refEquiv X H f hf r a
  obtain ⟨R, hcap, hsupp, hcost⟩ := hp (fun c => price (e c))
    (fun c => hprice (e c)) (by rw [← e.sum_comp] at hsum; exact hsum)
  refine ⟨R, hcap, ?_, ?_⟩
  · intro h y hR
    rw [source_map X H f hf r a]
    exact hsupp h y hR
  · rw [← e.sum_comp, ← e.sum_comp]
    convert hcost using 1
    · apply Finset.sum_congr rfl
      intro c hc
      congr 1
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro y hy
      simp only [highDeletionCost5]
      rw [show (e c).1 = pairMap f c.1 from rfl, deleted_map X H f hf r a]
    · apply Finset.sum_congr rfl
      intro c hc
      rfl

theorem fail_map (H : X.KeyHist) (f : I → J) (hf : Function.Injective f)
    (r : X.RecordOn I) (a : X.ArraysOn J)
    (h : X.step3FailOn H (mapRecord X f r) a) :
    X.step3FailOn H r (pullArrays X f a) := by
  classical
  obtain ⟨hgate, hlower | hratio | hhigh⟩ := h
  · refine ⟨(gate_map X H f r a _).mp hgate, Or.inl ?_⟩
    simpa only [← mass_map X H f hf r a none, Option.map_none, mapRecord] using hlower
  · refine ⟨(gate_map X H f r a _).mp hgate, Or.inr (Or.inl ?_)⟩
    obtain ⟨c, hc, hbad⟩ := hratio
    rw [refs_map] at hc
    obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hc
    subst c
    refine ⟨d, hd, ?_⟩
    simpa only [← mass_map X H f hf r a none, ← mass_map X H f hf r a (some d),
      Option.map_none, Option.map_some, mapRecord, pairMap] using hbad
  · refine ⟨(gate_map X H f r a _).mp hgate, Or.inr (Or.inr ⟨hhigh.1, ?_⟩)⟩
    intro hg
    exact hhigh.2 ⟨(capped_map X H f hf r a).mpr hg.1, price_map X H f hf r a hg.2⟩

theorem fail_arrays_congr (H : X.KeyHist) (r : X.RecordOn I) (a b : X.ArraysOn I)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) :
    X.step3FailOn H r a ↔ X.step3FailOn H r b := by
  classical
  have hgate := Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r a b hmask hab (H.2 r.1)
  have hm := Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r a b hmask hab
  have hr := Lane_sol_s05_centres.refsOn_arrays_congr X H r a b href hab
  have hc := Lane_sol_s05_centres.highCapped_arrays_congr X H r a b hmask hab
  have hp := Lane_sol_s05_centres.highPrice_arrays_congr X H r a b hmask href hab
  simp only [Setup5.step3FailOn, hgate, hm, hr, hc, hp]

theorem record_wellFormed (r : X.RecordOn I) (y : OddRole5 n) (μ : X.St.Site → I)
    (hr : X.RecordFrom r y μ) :
    (∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1) ∧
      (∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1) := by
  classical
  obtain ⟨hk, ho, href, hmask⟩ := hr
  constructor
  · intro c M hc
    rw [hc] at hmask
    obtain ⟨_, a, ha, hK, _, hi, _⟩ := hmask
    rw [ho]
    simp only [Finset.mem_image]
    exact ⟨a, ha, Prod.ext hi.symm hK.symm⟩
  · intro c hc
    rw [href] at hc
    simp only [Finset.mem_image] at hc
    obtain ⟨a, ha, he⟩ := hc
    rw [ho]
    simp only [Finset.mem_image]
    exact ⟨a, (Finset.mem_filter.mp ha).1, congrArg (fun d => (d.1, d.2.1)) he⟩

theorem fail_local (H : X.KeyHist) (r : X.RecordOn I) (y : OddRole5 n)
    (μ : X.St.Site → I) (hr : X.RecordFrom r y μ) :
    FinProb.DependsOn (X.step3FailOn H r) r.2.1 := by
  classical
  intro a b hab
  exact propext (fail_arrays_congr X H r a b (record_wellFormed X r y μ hr).1
    (record_wellFormed X r y μ hr).2 hab)

def arrayLaw [Fintype I] (H : X.KeyHist) : FinProb (X.ArraysOn I) :=
  FinProb.pi fun c => FinProb.pi fun _ => X.blockLaw H c.2

def bundleLaw (H : X.KeyHist) : FinProb (∀ K : X.Ty, X.Array K) :=
  FinProb.pi fun K => FinProb.pi fun _ => X.blockLaw H K

def bundleEquiv : X.ArraysOn I ≃ (I → ∀ K : X.Ty, X.Array K) where
  toFun := fun a i K => a (i, K)
  invFun := fun a c => a c.1 c.2
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

theorem bundle_pr [Fintype I] (H : X.KeyHist) (F : X.ArraysOn I → Prop) :
    (arrayLaw (I := I) X H).pr F =
      (FinProb.pi fun _ : I => bundleLaw X H).pr (fun a => F ((bundleEquiv X).symm a)) := by
  classical
  apply Lane_sol_s05_h1.pr_equiv _ _ (bundleEquiv X).symm ?_
  intro a
  simp only [arrayLaw, bundleLaw, FinProb.pi, bundleEquiv, Equiv.coe_fn_symm_mk]
  rw [Fintype.prod_prod_type]

theorem pr_indicator {A : Type} [Fintype A] (P : FinProb A) (F : A → Prop) :
    P.pr F = P.expect (fun a => if F a then (1 : ℝ) else 0) := by
  classical
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : F a <;> simp [h]

theorem injection_pr [Fintype I] [Fintype J] (H : X.KeyHist)
    (f : I → J) (hf : Function.Injective f) (F : X.ArraysOn I → Prop) :
    (arrayLaw (I := J) X H).pr (fun a => F (pullArrays X f a)) =
      (arrayLaw (I := I) X H).pr F := by
  classical
  rw [bundle_pr, bundle_pr]
  rw [pr_indicator, pr_indicator]
  have hh := Lane_sol_s05_hist1b.pi_injection_expect (fun _ : J => bundleLaw X H) f hf
    (fun a => if F ((bundleEquiv X).symm a) then (1 : ℝ) else 0)
  have hfun : ∀ a : J → ∀ K : X.Ty, X.Array K,
      pullArrays X f ((bundleEquiv X).symm a) =
        (bundleEquiv X).symm (fun i => a (f i)) := by
    intro a
    rfl
  simp_rw [hfun]
  exact hh

theorem fail_pr_map [Fintype J] (H : X.KeyHist)
    (f : Fin (X.p.T n) → J) (hf : Function.Injective f) (r : X.AbsRecord) :
    (arrayLaw (I := J) X H).pr (X.step3FailOn H (mapRecord X f r)) ≤ X.step3Rate H r := by
  classical
  letI : DecidableEq (Fin (X.p.T n)) := instDecidableEqFin _
  calc
    _ ≤ (arrayLaw (I := J) X H).pr (fun a => X.step3FailOn H r (pullArrays X f a)) :=
      FinProb.pr_mono _ _ _ (fun a ha => fail_map X H f hf r a ha)
    _ = (arrayLaw (I := Fin (X.p.T n)) X H).pr (X.step3FailOn H r) := injection_pr X H f hf _
    _ = X.step3Rate H r := by
      unfold arrayLaw Setup5.step3Rate Setup5.recArrayLaw FinProb.pr FinProb.pi
      apply Finset.sum_congr (by ext a; simp)
      intro a ha
      rfl

theorem recordFrom_map (f : I → J) (r : X.RecordOn I) (y : OddRole5 n)
    (μ : X.St.Site → I) (hr : X.RecordFrom r y μ) :
    X.RecordFrom (mapRecord X f r) y (f ∘ μ) := by
  classical
  obtain ⟨hk, ho, href, hmask⟩ := hr
  refine ⟨hk, ?_, ?_, ?_⟩
  · simp only [mapRecord, ho, Finset.image_image]
    ext c
    simp only [Finset.mem_image, Function.comp_apply, pairMap]
  · simp only [mapRecord, href, Finset.image_image]
    ext c
    simp only [Finset.mem_image, Function.comp_apply, pairMap]
  · cases hm : r.2.2.2 with
    | none => simpa only [mapRecord, hm, Option.map_none] using hmask
    | some c =>
      rw [hm] at hmask
      obtain ⟨hl, a, ha, hK, hnone, hi, hleg⟩ := hmask
      simp only [mapRecord, hm, Option.map_some]
      exact ⟨hl, a, ha, hK, hnone, congrArg f hi, hleg⟩

theorem mapRecord_roundtrip (f : I → J) (g : J → I) (r : X.RecordOn J)
    (hw : (∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1) ∧
      (∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1))
    (hi : ∀ c ∈ r.2.1, f (g c.1) = c.1) :
    mapRecord X f (mapRecord X g r) = r := by
  classical
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [mapRecord, Finset.image_image]
    calc
      (r.2.1.image (pairMap f ∘ pairMap g)) = r.2.1.image id :=
        Finset.image_congr (fun c hc => show (pairMap f ∘ pairMap g) c = id c from Prod.ext (hi c hc) rfl)
      _ = r.2.1 := Finset.image_id
  · apply Prod.ext
    · simp only [mapRecord, Finset.image_image]
      calc
        (r.2.2.1.image (pairMap f ∘ pairMap g)) = r.2.2.1.image id :=
          Finset.image_congr (fun c hc => show (pairMap f ∘ pairMap g) c = id c from
            Prod.ext (hi (c.1, c.2.1) (hw.2 c hc)) rfl)
        _ = r.2.2.1 := Finset.image_id
    · cases hm : r.2.2.2 with
      | none => simp only [mapRecord, hm, Option.map_none]
      | some c =>
        simp only [mapRecord, hm, Option.map_some]
        congr 1
        exact Prod.ext (hi (c.1, c.2.1) (hw.1 (c.1, c.2.1) c.2.2 hm)) rfl

theorem embedding_cover [Fintype J] (U S : Finset J) (T : ℕ)
    (hSU : S ⊆ U) (hS : S.card ≤ T) (hU : T ≤ U.card) (hT : 0 < T) :
    ∃ f : Fin T → U, Function.Injective f ∧ ∃ g : J → Fin T,
      ∀ i ∈ S, (f (g i)).1 = i := by
  classical
  obtain ⟨B, hSB, hBU, hB⟩ := Finset.exists_subsuperset_card_eq hSU hS hU
  let e : Fin T ≃ B := Fintype.equivOfCardEq (by simp [hB])
  let f : Fin T → U := fun i => ⟨(e i).1, hBU (e i).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply e.injective
    exact Subtype.ext (congrArg (fun u : U => u.1) hij)
  letI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  let g : J → Fin T := fun j => if hj : j ∈ B then e.symm ⟨j, hj⟩ else Classical.choice inferInstance
  refine ⟨f, hf, g, ?_⟩
  intro j hj
  simp only [g, dif_pos (hSB hj), f, e.apply_symm_apply]

abbrev concreteRecords [Fintype J] (U : Finset J) (ℓ : X.Key)
    (t : CubeVertex (X.p.m n)) (j : ℕ) :=
  (Fin (X.p.T n) ↪ U) × {r : X.AbsRecord // X.RecOccursAt r t j ∧ r.1 = ℓ}

def liftRecord [Fintype J] {U : Finset J} {ℓ : X.Key}
    {t : CubeVertex (X.p.m n)} {j : ℕ} (r : concreteRecords X U ℓ t j) : X.RecordOn J :=
  mapRecord X (fun i => (r.1 i).1) r.2.1

theorem concreteRecords_card [Fintype J] (U : Finset J) (ℓ : X.Key)
    (t : CubeVertex (X.p.m n)) (j : ℕ) :
    Fintype.card (concreteRecords X U ℓ t j) ≤ U.card ^ X.p.T n *
      (Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card := by
  classical
  have he : Fintype.card (Fin (X.p.T n) ↪ U) ≤ Fintype.card (Fin (X.p.T n) → U) :=
    Fintype.card_le_of_injective DFunLike.coe DFunLike.coe_injective
  simpa only [concreteRecords, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Fintype.card_subtype, Finset.filter_univ_mem] using Nat.mul_le_mul_right
      (Fintype.card {r : X.AbsRecord // X.RecOccursAt r t j ∧ r.1 = ℓ}) he

theorem lift_local [Fintype J] (H : X.KeyHist) {U : Finset J} {ℓ : X.Key}
    {t : CubeVertex (X.p.m n)} {j : ℕ} (r : concreteRecords X U ℓ t j) :
    FinProb.DependsOn (X.step3FailOn H (liftRecord X r)) (liftRecord X r).2.1 := by
  classical
  obtain ⟨y, μ, hy, _, _⟩ := r.2.2.1
  exact fail_local X H _ y _ (recordFrom_map X _ _ y μ hy)

theorem lift_pr [Fintype J] (H : X.KeyHist) (cL cH : ℝ)
    (hgood : X.KeyGood5 H cL cH) {U : Finset J} {ℓ : X.Key}
    {t : CubeVertex (X.p.m n)} {j : ℕ} (r : concreteRecords X U ℓ t j) :
    (arrayLaw (I := J) X H).pr (X.step3FailOn H (liftRecord X r)) ≤
      X.step3Scale (if ℓ.isLeft then cL / 4 else cH / 6) ℓ := by
  classical
  obtain ⟨y, μ, hy, _, _⟩ := r.2.2.1
  have hf : Function.Injective (fun i => (r.1 i).1) :=
    Subtype.val_injective.comp r.1.injective
  exact (fail_pr_map X H _ hf r.2.1).trans (by
    have hb := hgood.step3 r.2.1 ⟨y, μ, hy⟩
    rcases ℓ with k | k <;> simpa only [r.2.2.2, Sum.isLeft_inl, Sum.isLeft_inr,
      Bool.true_eq_false, Bool.false_eq_true, if_true, if_false] using hb)

theorem disjoint_records_bound [Fintype J] (H : X.KeyHist) (cL cH C : ℝ)
    (hgood : X.KeyGood5 H cL cH) (hcount : X.RecordCount C)
    (U : Finset J) (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j q : ℕ)
    (η : ℝ) (hη : 0 ≤ η)
    (hbudget : (U.card : ℝ) ^ X.p.T n *
      Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
        ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) +
        (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
          (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))) *
        X.step3Scale (if ℓ.isLeft then cL / 4 else cH / 6) ℓ ≤ η) :
    (arrayLaw (I := J) X H).pr (fun a => ∃ s : Fin q → concreteRecords X U ℓ t j,
      (∀ i k, i ≠ k → Disjoint (liftRecord X (s i)).2.1 (liftRecord X (s k)).2.1) ∧
        ∀ i, X.step3FailOn H (liftRecord X (s i)) a) ≤ η ^ q := by
  classical
  let ε := X.step3Scale (if ℓ.isLeft then cL / 4 else cH / 6) ℓ
  have hε : 0 ≤ ε := by
    dsimp only [ε, Setup5.step3Scale]
    split <;> exact (Real.exp_pos _).le
  have hu := Lane_sol_s05_centres.disjoint_failure_union
    (fun c : J × X.Ty => FinProb.pi fun _ => X.blockLaw H c.2)
    (fun r : concreteRecords X U ℓ t j => (liftRecord X r).2.1)
    (fun r a => X.step3FailOn H (liftRecord X r) a)
    (lift_local X H) ε hε (fun r => lift_pr X H cL cH hgood r) q
  have hc : (Fintype.card (concreteRecords X U ℓ t j) : ℝ) ≤
      (U.card : ℝ) ^ X.p.T n *
        Real.exp (C * ((X.p.T n : ℝ) * Real.log (X.p.T n) +
          ((ℓ.level : ℝ) + 1) * Real.log (X.p.m n) +
          (if ℓ.isLeft ∧ ℓ.level = X.p.J n then
            (X.p.T n : ℝ) * (X.p.q0 * X.p.uStarSeg n * X.p.usedBlocks n : ℕ) else 0))) := by
    have hh : (Fintype.card (concreteRecords X U ℓ t j) : ℝ) ≤
        (U.card : ℝ) ^ X.p.T n *
          ((Finset.univ.filter fun r : X.AbsRecord => X.RecOccursAt r t j ∧ r.1 = ℓ).card : ℝ) := by
      exact_mod_cast concreteRecords_card X U ℓ t j
    exact hh.trans (mul_le_mul_of_nonneg_left (hcount ℓ t j) (pow_nonneg (Nat.cast_nonneg U.card) (X.p.T n)))
  have hb : (Fintype.card (concreteRecords X U ℓ t j) : ℝ) * ε ≤ η :=
    (mul_le_mul_of_nonneg_right hc hε).trans hbudget
  refine hu.trans ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hε) hb q

theorem pi_pair_pr {L A B : Type} [Fintype L] [DecidableEq L]
    [Fintype A] [Fintype B] (P : L → FinProb A) (Q : L → FinProb B)
    (F : (L → A × B) → Prop) :
    (FinProb.pi fun l => (P l).prod (Q l)).pr F =
      (FinProb.pi P).expect (fun p => (FinProb.pi Q).pr (fun a => F (fun l => (p l, a l)))) := by
  classical
  let e : ((L → A) × (L → B)) ≃ (L → A × B) := {
    toFun := fun a l => (a.1 l, a.2 l)
    invFun := fun a => (fun l => (a l).1, fun l => (a l).2)
    left_inv := by intro a; rfl
    right_inv := by intro a; rfl }
  have hh := Lane_sol_s05_h1.pr_equiv
    ((FinProb.pi P).prod (FinProb.pi Q)) (FinProb.pi fun l => (P l).prod (Q l))
    e (fun a => by simp only [FinProb.pi, FinProb.prod, e, Equiv.coe_fn_mk,
      Finset.prod_mul_distrib]) F
  rw [hh]
  exact Lane_sol_s05_h1.bind_pr (FinProb.pi P) (fun _ => FinProb.pi Q) (fun a => F (e a))

theorem pi_snd_pr {L A B : Type} [Fintype L] [DecidableEq L]
    [Fintype A] [Fintype B] (P : L → FinProb A) (Q : L → FinProb B)
    (F : (L → B) → Prop) :
    (FinProb.pi fun l => (P l).prod (Q l)).pr (fun a => F (fun l => (a l).2)) =
      (FinProb.pi Q).pr F := by
  classical
  rw [pi_pair_pr]
  simp only [FinProb.expect, ← Finset.sum_mul, FinProb.sum_eq_one, one_mul]

theorem pi_pair_bound {L A B : Type} [Fintype L] [DecidableEq L]
    [Fintype A] [Fintype B] (P : L → FinProb A) (Q : L → FinProb B)
    (F : (L → A) → (L → B) → Prop) (η : ℝ)
    (h : ∀ p, (FinProb.pi Q).pr (F p) ≤ η) :
    (FinProb.pi fun l => (P l).prod (Q l)).pr
      (fun a => F (fun l => (a l).1) (fun l => (a l).2)) ≤ η := by
  classical
  rw [pi_pair_pr]
  calc
    _ ≤ ∑ p, (FinProb.pi P).w p * η := Finset.sum_le_sum fun p _ =>
      mul_le_mul_of_nonneg_left (h p) ((FinProb.pi P).nonneg p)
    _ = η := by rw [← Finset.sum_mul, FinProb.sum_eq_one, one_mul]

theorem marking_family_lift [Fintype J] (H : X.KeyHist)
    (U : Finset J) (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j q : ℕ)
    (F : X.ArraysOn J → Finset (Finset J))
    (hlift : ∀ a S, S ∈ F a → ∃ r : concreteRecords X U ℓ t j,
      (∀ c ∈ (liftRecord X r).2.1, c.1 ∈ S) ∧ X.step3FailOn H (liftRecord X r) a) :
    (arrayLaw (I := J) X H).pr
      (fun a => q ≤ (Lane_sol_s05_centres.markingFamily (F a)).card) ≤
    (arrayLaw (I := J) X H).pr (fun a => ∃ s : Fin q → concreteRecords X U ℓ t j,
      (∀ i k, i ≠ k → Disjoint (liftRecord X (s i)).2.1 (liftRecord X (s k)).2.1) ∧
        ∀ i, X.step3FailOn H (liftRecord X (s i)) a) := by
  classical
  apply FinProb.pr_mono
  intro a ha
  obtain ⟨B, hB, hcard⟩ := Finset.exists_subset_card_eq ha
  let e : Fin q ≃ B := Fintype.equivOfCardEq (by simp [hcard])
  have hF (i : Fin q) : (e i).1 ∈ F a :=
    (Lane_sol_s05_centres.markingFamily_spec (F a)).1 (hB (e i).2)
  let s : Fin q → concreteRecords X U ℓ t j := fun i => Classical.choose (hlift a (e i).1 (hF i))
  have hs (i : Fin q) : (∀ c ∈ (liftRecord X (s i)).2.1, c.1 ∈ (e i).1) ∧
      X.step3FailOn H (liftRecord X (s i)) a := Classical.choose_spec (hlift a (e i).1 (hF i))
  refine ⟨s, ?_, fun i => (hs i).2⟩
  intro i k hik
  have hne : (e i).1 ≠ (e k).1 := fun h => hik (e.injective (Subtype.ext h))
  have hsep := (Lane_sol_s05_centres.markingFamily_spec (F a)).2.1
    (e i).1 (hB (e i).2) (e k).1 (hB (e k).2) hne
  apply Finset.disjoint_left.mpr
  intro c hci hck
  exact Finset.disjoint_left.mp hsep ((hs i).1 c hci) ((hs k).1 c hck)

abbrev starRecord (H : X.KeyHist) (A : X.ArraysOn I) (μ : X.St.Site → I)
    (y : OddRole5 n) : X.RecordOn I :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs := (Setup5.evenNbrs y).image fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)
  let refs := ((Setup5.evenNbrs y).filter fun a =>
    ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
      ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome).image fun a =>
        (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)
  let mask := match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none then
        let a := Classical.choose hex
        some (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1,
          X.firstK (X.hitSet A (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
            (X.p.usedBlocks n))
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

theorem starRecord_from (H : X.KeyHist) (A : X.ArraysOn I) (μ : X.St.Site → I)
    (y : OddRole5 n) (hf : X.step3FailOn H (starRecord X H A μ y) A) :
    X.RecordFrom (starRecord X H A μ y) y μ := by
  classical
  refine ⟨rfl, ?_, ?_, ?_⟩
  · ext c
    simp only [starRecord, Finset.mem_image]
  · ext c
    simp only [starRecord, Finset.mem_image, Finset.mem_filter]
  dsimp only [starRecord] at hf ⊢
  generalize hℓ : X.g.roleKey (X.p.J n) y.1 = ℓ at hf ⊢
  cases ℓ with
  | inr k => simp
  | inl k =>
    dsimp only
    by_cases hex : ∃ a ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none
    · rw [dif_pos hex]
      let a := Classical.choose hex
      have ha := Classical.choose_spec hex
      refine ⟨by simp, a, ha.1, rfl, ha.2, rfl, ?_⟩
      have hg := hf.1.2
      have hg' := hg (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)
        (X.firstK (X.hitSet A (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
          (X.p.usedBlocks n)) (by simp [starRecord, hℓ, hex, a])
      have hh := hg' (0 : Fin 1)
      have hlen : X.p.usedBlocks n ≤
          (X.hitSet A (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card := by
        have hcol : H.2 (.inl k) (0 : Fin 1) = X.lowCol H.2 k := by
          unfold Setup5.lowCol
          congr 1
        rw [hcol] at hh
        exact hh.1
      simp only [Setup5.LegitRef, ha.2]
      refine ⟨?_, (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)⟩
      rw [Lane_sol_s05_1f.firstK_card, Nat.min_eq_left hlen]
    · rw [dif_neg hex]
      intro _ a ha
      cases hK : (X.g.evenType (X.p.J n) a.1).2.2 with
      | none => exact (hex ⟨a, ha, hK⟩).elim
      | some k => simp [hK]

theorem starRecord_ids (H : X.KeyHist) (A : X.ArraysOn I) (μ : X.St.Site → I)
    (y : OddRole5 n) (c : I × X.Ty) (hc : c ∈ (starRecord X H A μ y).2.1) :
    c.1 ∈ (X.St.neighbors (X.St.stateOf y.1)).image μ := by
  classical
  simp only [starRecord, Finset.mem_image] at hc
  obtain ⟨a, ha, he⟩ := hc
  refine Finset.mem_image.mpr ⟨X.St.stateOf a.1, ?_, congrArg Prod.fst he⟩
  exact (X.St.mem_neighbors _ _).mpr ⟨y.1, a.1, rfl, rfl,
    (Finset.mem_filter.mp ha).2.symm⟩

theorem adj_flip {n : ℕ} (x z : CubeVertex n) (h : (cube n).Adj x z) :
    ∃ i : Fin n, z = cubeFlip x i := by
  classical
  let S := Finset.univ.filter fun i : Fin n => x i ≠ z i
  change _root_.hammingDist x z = 1 at h
  change S.card = 1 at h
  obtain ⟨i, he⟩ := Finset.card_eq_one.mp h
  refine ⟨i, ?_⟩
  funext k
  by_cases hk : k = i
  · subst k
    have hi : i ∈ S := by rw [he]; simp
    have hi' := (Finset.mem_filter.mp hi).2
    cases hx : x i <;> cases hz : z i <;> simp_all [cubeFlip]
  · have hEq : x k = z k := by
      by_contra hEq
      have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEq⟩
      rw [he] at hmem
      exact hk (Finset.mem_singleton.mp hmem)
    simp only [cubeFlip, Function.update_of_ne hk]
    exact hEq.symm

theorem odd_neighbors_even (y : OddRole5 n) (t : X.St.Site)
    (ht : t ∈ X.St.neighbors (X.St.stateOf y.1)) :
    ∃ a : EvenRole5 n, X.St.stateOf a.1 = t := by
  classical
  obtain ⟨x, z, hx, hz, hadj⟩ := (X.St.mem_neighbors _ _).mp ht
  have hxodd : ¬ IsEvenRole x := fun h => y.2 ((X.St.state_determines x y.1 hx).2.2.2.1.mp h)
  have hzeven : IsEvenRole z := by
    obtain ⟨i, hi⟩ := adj_flip x z hadj
    rw [hi]
    exact (cubeFlip_parity x i).mpr hxodd
  exact ⟨⟨z, hzeven⟩, hz⟩

theorem record_lift [Fintype J] (H : X.KeyHist) (A : X.ArraysOn J)
    (U S : Finset J) (ℓ : X.Key) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (r : X.RecordOn J) (y : OddRole5 n) (μ : X.St.Site → J)
    (hr : X.RecordFrom r y μ) (hk : r.1 = ℓ) (ht : X.g.sign y.1 = t) (hj : X.g.severity y.1 = j)
    (hSU : S ⊆ U) (hS : S.card ≤ X.p.T n) (hU : X.p.T n ≤ U.card) (hT : 0 < X.p.T n)
    (hs : ∀ c ∈ r.2.1, c.1 ∈ S) (hfail : X.step3FailOn H r A) :
    ∃ r' : concreteRecords X U ℓ t j,
      (∀ c ∈ (liftRecord X r').2.1, c.1 ∈ S) ∧ X.step3FailOn H (liftRecord X r') A := by
  classical
  obtain ⟨f, hf, g, hfg⟩ := embedding_cover U S (X.p.T n) hSU hS hU hT
  let e : Fin (X.p.T n) ↪ U := ⟨f, hf⟩
  let rA : X.AbsRecord := mapRecord X g r
  have hfrom : X.RecordFrom rA y (g ∘ μ) := recordFrom_map X g r y μ hr
  let r' : concreteRecords X U ℓ t j :=
    (e, ⟨rA, ⟨⟨y, g ∘ μ, hfrom, ht, hj⟩, hk⟩⟩)
  have heq : liftRecord X r' = r :=
    mapRecord_roundtrip X (fun i => (f i).1) g r (record_wellFormed X r y μ hr)
      (fun c hc => hfg c.1 (hs c hc))
  exact ⟨r', by simpa only [heq] using hs, by simpa only [heq] using hfail⟩

theorem odd_neighbors_nonempty (hn : 0 < n) (y : OddRole5 n) :
    (X.St.neighbors (X.St.stateOf y.1)).Nonempty := by
  classical
  let i : Fin n := ⟨0, hn⟩
  exact ⟨X.St.stateOf (cubeFlip y.1 i), (X.St.mem_neighbors _ _).mpr
    ⟨y.1, cubeFlip y.1 i, rfl, rfl, cubeFlip_adj y.1 i⟩⟩

theorem level_card {V : Type} [Fintype V] [DecidableEq V] (H : ℕ)
    (P : V × Fin (H + 1) → Bool) (test : V → Prop) (j : Fin (H + 1)) :
    (Finset.univ.filter (fun l : V × Fin (H + 1) =>
      P l = true ∧ (l.2 : ℕ) = (j : ℕ) ∧ test l.1)).card =
      (Finset.univ.filter (fun u : V => P (u, j) = true ∧ test u)).card := by
  classical
  let A := Finset.univ.filter (fun u : V => P (u, j) = true ∧ test u)
  let B := Finset.univ.filter (fun l : V × Fin (H + 1) =>
    P l = true ∧ (l.2 : ℕ) = (j : ℕ) ∧ test l.1)
  have hj' (l : B) : l.1.2 = j := Fin.ext (Finset.mem_filter.mp l.2).2.2.1
  let e : B ≃ A := {
    toFun := fun l => ⟨l.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hh := (Finset.mem_filter.mp l.2).2
      exact ⟨by simpa only [← hj' l, Prod.mk.eta] using hh.1, hh.2.2⟩⟩⟩
    invFun := fun u => ⟨(u.1, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp u.2).2.1, rfl, (Finset.mem_filter.mp u.2).2.2⟩⟩
    left_inv := fun l => Subtype.ext (Prod.ext rfl (hj' l).symm)
    right_inv := fun u => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

end
end HypercubeRamsey.Lane_sol_s05_j5
