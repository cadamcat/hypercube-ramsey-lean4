import HypercubeRamsey.S05.History_q_s05_hist2

namespace HypercubeRamsey.Lane_sol_s05_h1

open Classical
open scoped BigOperators

set_option synthInstance.maxSize 1024

noncomputable section

theorem expect_equiv {A B : Type*} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : FinProb B) (e : A ≃ B)
    (hw : ∀ a, Q.w (e a) = P.w a) (f : B → ℝ) :
    Q.expect f = P.expect (fun a => f (e a)) := by
  unfold FinProb.expect
  rw [← e.sum_comp]
  simp_rw [hw]

theorem pr_equiv {A B : Type*} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : FinProb B) (e : A ≃ B)
    (hw : ∀ a, Q.w (e a) = P.w a) (F : B → Prop) :
    Q.pr F = P.pr (fun a => F (e a)) := by
  classical
  simpa [FinProb.expect, FinProb.pr, mul_ite] using
    expect_equiv P Q e hw (fun b => if F b then 1 else 0)

theorem bind_pr {A B : Type*} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : A → FinProb B) (F : A × B → Prop) :
    (FinProb.bind P Q).pr F = P.expect (fun a => (Q a).pr (fun b => F (a, b))) := by
  classical
  simpa [FinProb.pr, FinProb.expect, mul_ite] using
    FinProb.bind_expect P Q (fun a b => if F (a, b) then (1 : ℝ) else 0)

theorem pi_weight_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : I → Type*} {B : J → Type*}
    [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
    (P : ∀ i, FinProb (A i)) (Q : ∀ j, FinProb (B j))
    (e : I ≃ J) (f : ∀ i, A i ≃ B (e i))
    (hw : ∀ i a, (Q (e i)).w (f i a) = (P i).w a) (a : ∀ i, A i) :
    (FinProb.pi Q).w (e.piCongr f a) = (FinProb.pi P).w a := by
  change (∏ j, (Q j).w (e.piCongr f a j)) = ∏ i, (P i).w (a i)
  rw [← e.prod_comp]
  simp_rw [Equiv.piCongr_apply_apply, hw]

theorem pi_pr_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : I → Type*} {B : J → Type*}
    [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
    (P : ∀ i, FinProb (A i)) (Q : ∀ j, FinProb (B j))
    (e : I ≃ J) (f : ∀ i, A i ≃ B (e i))
    (hw : ∀ i a, (Q (e i)).w (f i a) = (P i).w a)
    (F : (∀ j, B j) → Prop) :
    (FinProb.pi Q).pr F = (FinProb.pi P).pr (fun a => F (e.piCongr f a)) :=
  pr_equiv _ _ _ (pi_weight_equiv P Q e f hw) F

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

def fill {I : Type*} [DecidableEq I] {A : I → Type*}
    (S : Finset I) (a₀ : ∀ i, A i) (a : ∀ i : S, A i.1) : ∀ i, A i :=
  fun i => if h : i ∈ S then a ⟨i, h⟩ else a₀ i

theorem pi_pr_restrict {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    (P : ∀ i, FinProb (A i)) (S : Finset I) (a₀ : ∀ i, A i)
    (F : (∀ i, A i) → Prop) (hF : FinProb.DependsOn F S) :
    (FinProb.pi P).pr F =
      (FinProb.pi (fun i : S => P i.1)).pr (fun a => F (fill S a₀ a)) := by
  classical
  have hi : FinProb.DependsOn (fun a => if F a then (1 : ℝ) else 0) S := by
    intro a b h
    change (if F a then (1 : ℝ) else 0) = (if F b then 1 else 0)
    rw [hF a b h]
  have h := FinProb.pi_expect_depends P S (fun a => if F a then (1 : ℝ) else 0) a₀ hi
  have hfill : ∀ a : ∀ i : S, A i.1,
      (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) A).symm
        (a, fun i => a₀ i.1) = fill S a₀ a := by
    intro a
    funext i
    simp only [fill, Equiv.piEquivPiSubtypeProd_symm_apply]
  simp_rw [hfill] at h
  simpa [FinProb.pr, FinProb.expect, mul_ite] using h

theorem pi_pr_local_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : I → Type*} {B : J → Type*}
    [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]
    (P : ∀ i, FinProb (A i)) (Q : ∀ j, FinProb (B j))
    (S : Finset I) (T : Finset J) (a₀ : ∀ i, A i) (b₀ : ∀ j, B j)
    (e : S ≃ T) (f : ∀ i : S, A i.1 ≃ B (e i).1)
    (hw : ∀ i a, (Q (e i).1).w (f i a) = (P i.1).w a)
    (F : (∀ i, A i) → Prop) (G : (∀ j, B j) → Prop)
    (hF : FinProb.DependsOn F S) (hG : FinProb.DependsOn G T)
    (hFG : ∀ a b, (∀ i : S, f i (a i.1) = b (e i).1) → (F a ↔ G b)) :
    (FinProb.pi P).pr F = (FinProb.pi Q).pr G := by
  classical
  rw [pi_pr_restrict P S a₀ F hF, pi_pr_restrict Q T b₀ G hG]
  rw [pi_pr_equiv (fun i : S => P i.1) (fun j : T => Q j.1) e f hw]
  congr 1
  funext a
  apply propext
  apply hFG
  intro i
  simp only [fill, dite_eq_left i.2, dite_eq_left (e i).2]
  exact (Equiv.piCongr_apply_apply (W := fun i : S => A i.1)
    (Z := fun j : T => B j.1) e f a i).symm

theorem equiv_of_histogram {A B D : Type*} [Fintype A] [Fintype B]
    (f : A → D) (g : B → D)
    (hc : ∀ d, Fintype.card {a // f a = d} = Fintype.card {b // g b = d}) :
    ∃ e : A ≃ B, ∀ a, g (e a) = f a := by
  classical
  let es (d : D) : {a // f a = d} ≃ {b // g b = d} := Fintype.equivOfCardEq (hc d)
  exact ⟨Equiv.ofFiberEquiv es, Equiv.ofFiberEquiv_map es⟩

theorem labelled_bins_equiv {Ω D : Type*} [Fintype Ω] [DecidableEq Ω]
    [DecidableEq D] (B B' : Finset Ω) (f : B ↪ D) (g : B' ↪ D)
    (h : Finset.univ.image f = Finset.univ.image g) :
    ∃ eb : Equiv.Perm Ω, ∃ el : B ≃ B',
      (∀ a, eb a.1 = (el a).1) ∧ (∀ a, g (el a) = f a) := by
  classical
  have hs : Set.range f = Set.range g := by
    ext d
    constructor
    · rintro ⟨a, rfl⟩
      have hm : f a ∈ Finset.univ.image g := by
        rw [← h]
        exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hm
    · rintro ⟨b, rfl⟩
      have hm : g b ∈ Finset.univ.image f := by
        rw [h]
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
      simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hm
  let el : B ≃ B' := (Equiv.ofInjective f f.injective).trans
    ((Set.equivOfEq hs).trans (Equiv.ofInjective g g.injective).symm)
  have hel : ∀ a, g (el a) = f a := by
    intro a
    have hp : (Equiv.ofInjective g g.injective) (el a) =
        (Set.equivOfEq hs) ((Equiv.ofInjective f f.injective) a) := by
      simp [el]
    exact congrArg Subtype.val hp
  obtain ⟨eb, heb⟩ := Equiv.Perm.exists_extending_pair
    (fun a : B => a.1) (fun a : B => (el a).1)
    Subtype.val_injective (Subtype.val_injective.comp el.injective)
  exact ⟨eb, el, heb, hel⟩

def labelSet {Ω D : Type*} [DecidableEq D] (B : Finset Ω) (f : B ↪ D)
    (A : Finset Ω) (hA : A ⊆ B) : Finset D :=
  A.attach.image (fun a => f ⟨a.1, hA a.2⟩)

structure BinRename {Ω D : Type*} (B B' : Finset Ω) (f : B ↪ D) (g : B' ↪ D) where
  perm : Equiv.Perm Ω
  localEquiv : B ≃ B'
  perm_local : ∀ a, perm a.1 = (localEquiv a).1
  label_local : ∀ a, g (localEquiv a) = f a

theorem labelSet_perm {Ω D : Type*} [DecidableEq Ω] [DecidableEq D]
    (B B' : Finset Ω) (f : B ↪ D) (g : B' ↪ D) (r : BinRename B B' f g)
    (A A' : Finset Ω) (hA : A ⊆ B) (hA' : A' ⊆ B')
    (hcode : labelSet B f A hA = labelSet B' g A' hA') :
    A.image r.perm = A' := by
  classical
  ext w
  constructor
  · rintro hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
    let ab : B := ⟨a, hA ha⟩
    have hd : f ab ∈ labelSet B' g A' hA' := by
      rw [← hcode]
      exact Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩
    obtain ⟨a', ha', he⟩ := Finset.mem_image.mp hd
    have heq : r.localEquiv ab = (⟨a'.1, hA' a'.2⟩ : B') := by
      apply g.injective
      exact (r.label_local ab).trans he.symm
    have hw : r.perm a = a'.1 := (r.perm_local ab).trans (congrArg Subtype.val heq)
    rw [hw]
    exact a'.2
  · intro hw
    let wb : B' := ⟨w, hA' hw⟩
    let ab : B := r.localEquiv.symm wb
    have hl : f ab = g wb := by
      simpa [ab] using (r.label_local ab).symm
    have hd : f ab ∈ labelSet B f A hA := by
      rw [hcode, hl]
      exact Finset.mem_image.mpr ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hd
    have heq : (⟨a.1, hA a.2⟩ : B) = ab := f.injective he
    refine Finset.mem_image.mpr ⟨a.1, a.2, ?_⟩
    rw [show a.1 = ab.1 from congrArg Subtype.val heq, r.perm_local]
    simp [ab, wb]

theorem binRename_exists {Ω D : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq D]
    (B B' : Finset Ω) (f : B ↪ D) (g : B' ↪ D)
    (h : Finset.univ.image f = Finset.univ.image g) : Nonempty (BinRename B B' f g) := by
  obtain ⟨eb, el, heb, hel⟩ := labelled_bins_equiv B B' f g h
  exact ⟨⟨eb, el, heb, hel⟩⟩

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {F G : Ω → Prop}
    (h : ∀ ω, F ω → G ω) : P.pr F ≤ P.pr G := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hf : F ω
  · simp [hf, h ω hf]
  · simp [hf]
    split_ifs <;> simp [P.nonneg ω]

theorem coded_markov {Ω I C : Type*} [Fintype Ω] [Fintype I] [Fintype C]
    (P : FinProb Ω) (code : I → C) (rate : I → Ω → ℝ) (threshold : I → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hnonneg : ∀ i ω, 0 ≤ rate i ω)
    (hpos : ∀ i, 0 < threshold i)
    (hraw : ∀ i, P.expect (rate i) ≤ ε * threshold i)
    (hsame : ∀ i j, code i = code j → rate i = rate j ∧ threshold i = threshold j) :
    P.pr (fun ω => ∃ i, threshold i < rate i ω) ≤ (Fintype.card C : ℝ) * ε := by
  classical
  let bad (c : C) (ω : Ω) : Prop := ∃ i, code i = c ∧ threshold i < rate i ω
  have hbad : ∀ c, P.pr (bad c) ≤ ε := by
    intro c
    by_cases hc : ∃ i, code i = c
    · obtain ⟨i, hi⟩ := hc
      have hsub : ∀ ω, bad c ω → threshold i ≤ rate i ω := by
        rintro ω ⟨j, hj, hfail⟩
        obtain ⟨hr, ht⟩ := hsame j i (hj.trans hi.symm)
        rw [hr, ht] at hfail
        exact hfail.le
      calc
        P.pr (bad c) ≤ P.pr (fun ω => threshold i ≤ rate i ω) := pr_mono P hsub
        _ ≤ P.expect (rate i) / threshold i := P.markov (rate i) (threshold i) (hnonneg i) (hpos i)
        _ ≤ ε := (div_le_iff₀ (hpos i)).2 (hraw i)
    · have hfalse : ∀ ω, ¬ bad c ω := fun ω ⟨i, hi, _⟩ => hc ⟨i, hi⟩
      simpa [FinProb.pr, hfalse] using hε
  calc
    P.pr (fun ω => ∃ i, threshold i < rate i ω) = P.pr (fun ω => ∃ c, bad c ω) := by
      congr 1
      funext ω
      apply propext
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨code i, i, rfl, hi⟩
      · rintro ⟨c, i, _, hi⟩
        exact ⟨i, hi⟩
    _ ≤ ∑ c, P.pr (bad c) := FinProb.pr_exists_le_sum5 P bad
    _ ≤ ∑ _c : C, ε := Finset.sum_le_sum fun c _ => hbad c
    _ = (Fintype.card C : ℝ) * ε := by simp

def renameCoarse (e : Equiv.Perm (BinVector5 n)) (c : X.Coarse) : X.Coarse :=
  (fun w => c.1 (e.symm w), fun w => c.2 (e.symm w))

def coarseEquiv (e : Equiv.Perm (BinVector5 n)) : X.Coarse ≃ X.Coarse where
  toFun := renameCoarse X e
  invFun := renameCoarse X e.symm
  left_inv c := by ext w <;> simp [renameCoarse]
  right_inv c := by ext w <;> simp [renameCoarse]

theorem coarseLaw_weight_equiv (v : Fin N) (e : Equiv.Perm (BinVector5 n)) (c : X.Coarse) :
    (X.coarseLaw v).w (coarseEquiv X e c) = (X.coarseLaw v).w c := by
  change (∏ w, (X.P.prior.partner v w).w (c.1 (e.symm w))) *
      (∏ w, ∏ s, (X.segLaw v (c.1 (e.symm w))).w (c.2 (e.symm w) s)) =
    (∏ w, (X.P.prior.partner v w).w (c.1 w)) *
      (∏ w, ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s))
  congr 1
  · calc
      _ = ∏ w, (X.P.prior.partner v (e.symm w)).w (c.1 (e.symm w)) := by
        apply Finset.prod_congr rfl
        intro w _
        rw [X.partner_bin_free v w (e.symm w)]
      _ = _ := e.symm.prod_comp (fun w => (X.P.prior.partner v w).w (c.1 w))
  · exact e.symm.prod_comp
      (fun w => ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s))

theorem coarseLaw_pr_equiv (v : Fin N) (e : Equiv.Perm (BinVector5 n))
    (F : X.Coarse → Prop) :
    (X.coarseLaw v).pr F = (X.coarseLaw v).pr (fun c => F (renameCoarse X e c)) :=
  pr_equiv _ _ (coarseEquiv X e) (coarseLaw_weight_equiv X v e) F

theorem colWeight_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key)
    (hlevel : ℓ.level = ℓ'.level) (hflag : ℓ.coarse.2 = ℓ'.coarse.2)
    (hbin : e ℓ.coarse.1 = ℓ'.coarse.1)
    (hlist : (binList5 ℓ.coarse).image e = binList5 ℓ'.coarse)
    (W : BinVector5 n → X.Stream)
    (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop) (y : Fin N) :
    X.colWeight (b.1, renameCoarse X e b.2) ℓ' (fun w => W (e.symm w))
      (fun w s => keep (e.symm w) s) y = X.colWeight b ℓ W keep y := by
  classical
  unfold Setup5.colWeight
  simp only [renameCoarse, ← hlevel, ← hflag]
  by_cases hf : ℓ.coarse.2 = true
  · simp only [hf, ↓reduceIte]
    congr 1
    rw [← hlist, Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro w _
      simp only [Equiv.symm_apply_apply]
      rw [X.partner_bin_free y (e w) w]
    · intro a _ b _ h
      exact e.injective h
  · have hf' : ℓ.coarse.2 = false := by cases h : ℓ.coarse.2 <;> simp_all
    simp only [hf', Bool.false_eq_true, ↓reduceIte, ← hbin, Equiv.symm_apply_apply]
    rw [X.partner_bin_free b.1 (e ℓ.coarse.1) ℓ.coarse.1]

theorem prior_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key)
    (hlevel : ℓ.level = ℓ'.level) (hflag : ℓ.coarse.2 = ℓ'.coarse.2)
    (hbin : e ℓ.coarse.1 = ℓ'.coarse.1)
    (hlist : (binList5 ℓ.coarse).image e = binList5 ℓ'.coarse) :
    X.prior (b.1, renameCoarse X e b.2) ℓ' = X.prior b ℓ := by
  unfold Setup5.prior
  congr 1
  funext y
  exact colWeight_bin_equiv X e b ℓ ℓ' hlevel hflag hbin hlist b.2.2 (fun _ _ => True) y

theorem priorDel_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key)
    (hlevel : ℓ.level = ℓ'.level) (hflag : ℓ.coarse.2 = ℓ'.coarse.2)
    (hbin : e ℓ.coarse.1 = ℓ'.coarse.1)
    (hlist : (binList5 ℓ.coarse).image e = binList5 ℓ'.coarse)
    (w : BinVector5 n) (k : ℕ) :
    X.priorDel (b.1, renameCoarse X e b.2) ℓ' (e w) k = X.priorDel b ℓ w k := by
  unfold Setup5.priorDel
  congr 1
  funext y
  have hkeep : (fun (w' : BinVector5 n) (s : Fin (X.p.streamSegs n)) =>
      ¬ (w' = e w ∧ (s : ℕ) < k)) =
      (fun (w' : BinVector5 n) (s : Fin (X.p.streamSegs n)) =>
        ¬ (e.symm w' = w ∧ (s : ℕ) < k)) := by
    funext w' s
    simp only [Equiv.symm_apply_eq]
  rw [hkeep]
  exact colWeight_bin_equiv X e b ℓ ℓ' hlevel hflag hbin hlist b.2.2
    (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) y

theorem replaceStream_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (W : BinVector5 n → X.Stream) (w : BinVector5 n) {k : ℕ}
    (z : Fin k → Word5 N X.p.q0) :
    X.replaceStream (fun w' => W (e.symm w')) (e w) z =
      fun w' => X.replaceStream W w z (e.symm w') := by
  classical
  funext w' s
  by_cases hw : w' = e w
  · subst w'
    simp [Setup5.replaceStream]
  · have hw' : e.symm w' ≠ w := by
      intro h
      apply hw
      simpa using congrArg e h
    simp [Setup5.replaceStream, Function.update_of_ne hw, Function.update_of_ne hw']

theorem priorRep_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key)
    (hlevel : ℓ.level = ℓ'.level) (hflag : ℓ.coarse.2 = ℓ'.coarse.2)
    (hbin : e ℓ.coarse.1 = ℓ'.coarse.1)
    (hlist : (binList5 ℓ.coarse).image e = binList5 ℓ'.coarse)
    (w : BinVector5 n) {k : ℕ} (z : Fin k → Word5 N X.p.q0) :
    X.priorRep (b.1, renameCoarse X e b.2) ℓ' (e w) z = X.priorRep b ℓ w z := by
  unfold Setup5.priorRep
  change normalize5
    (X.colWeight (b.1, renameCoarse X e b.2) ℓ'
      (X.replaceStream (fun w' => b.2.2 (e.symm w')) (e w) z) (fun _ _ => True)) X.y₀ = _
  rw [replaceStream_bin_equiv]
  congr 1
  funext y
  exact colWeight_bin_equiv X e b ℓ ℓ' hlevel hflag hbin hlist
    (X.replaceStream b.2.2 w z) (fun _ _ => True) y

structure PriorMatch (e : Equiv.Perm (BinVector5 n)) (ℓ ℓ' : X.Key) : Prop where
  level : ℓ.level = ℓ'.level
  flag : ℓ.coarse.2 = ℓ'.coarse.2
  bin : e ℓ.coarse.1 = ℓ'.coarse.1
  bins : (binList5 ℓ.coarse).image e = binList5 ℓ'.coarse

theorem step1Fail_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key) (hm : PriorMatch X e ℓ ℓ')
    (w : BinVector5 n) (k : ℕ) :
    X.step1Fail (b.1, renameCoarse X e b.2) ℓ' (e w) k ↔ X.step1Fail b ℓ w k := by
  simp only [Setup5.step1Fail,
    prior_bin_equiv X e b ℓ ℓ' hm.level hm.flag hm.bin hm.bins,
    priorDel_bin_equiv X e b ℓ ℓ' hm.level hm.flag hm.bin hm.bins]

theorem capFail_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key) (hm : PriorMatch X e ℓ ℓ') :
    X.capFail (b.1, renameCoarse X e b.2) ℓ' ↔ X.capFail b ℓ := by
  simp only [Setup5.capFail, ← hm.level,
    prior_bin_equiv X e b ℓ ℓ' hm.level hm.flag hm.bin hm.bins]

theorem step1Rate_bin_equiv (v : Fin N) (e : Equiv.Perm (BinVector5 n))
    (ℓ ℓ' : X.Key) (hm : PriorMatch X e ℓ ℓ') (w : BinVector5 n) (k : ℕ) :
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ' (e w) k) =
      (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ w k) := by
  rw [coarseLaw_pr_equiv X v e]
  congr 1
  funext c
  exact propext (step1Fail_bin_equiv X e (v, c) ℓ ℓ' hm w k)

theorem capRate_bin_equiv (v : Fin N) (e : Equiv.Perm (BinVector5 n))
    (ℓ ℓ' : X.Key) (hm : PriorMatch X e ℓ ℓ') :
    (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ') =
      (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := by
  rw [coarseLaw_pr_equiv X v e]
  congr 1
  funext c
  exact propext (capFail_bin_equiv X e (v, c) ℓ ℓ' hm)

def colEquiv (ℓ ℓ' : X.Key) (hlen : colLen5 (X.p.s n) ℓ = colLen5 (X.p.s n) ℓ') :
    (Fin (colLen5 (X.p.s n) ℓ) → Fin N) ≃ (Fin (colLen5 (X.p.s n) ℓ') → Fin N) :=
  Equiv.piCongrLeft' (fun _ => Fin N) (finCongr hlen)

theorem colLaw_weight_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (ℓ ℓ' : X.Key) (hm : PriorMatch X e ℓ ℓ')
    (hlen : colLen5 (X.p.s n) ℓ = colLen5 (X.p.s n) ℓ')
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    (FinProb.pi (fun _ => X.prior (b.1, renameCoarse X e b.2) ℓ')).w
      (colEquiv X ℓ ℓ' hlen θ) = (FinProb.pi (fun _ => X.prior b ℓ)).w θ := by
  rw [prior_bin_equiv X e b ℓ ℓ' hm.level hm.flag hm.bin hm.bins]
  change (∏ h, (X.prior b ℓ).w (θ ((finCongr hlen).symm h))) =
    ∏ h, (X.prior b ℓ).w (θ h)
  exact (finCongr hlen).symm.prod_comp (fun h => (X.prior b ℓ).w (θ h))

theorem colLik_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1)
    (ℓ ℓ' : X.Key) (hm : PriorMatch X e ℓ ℓ')
    (hlen : colLen5 (X.p.s n) ℓ = colLen5 (X.p.s n) ℓ')
    (z : X.Block (i, S, j)) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    X.colLik (b.1, renameCoarse X e b.2) (i', S', j) ℓ' z
      (colEquiv X ℓ ℓ' hlen θ) = X.colLik b (i, S, j) ℓ z θ := by
  unfold Setup5.colLik
  dsimp only [Setup5.Block, Params5.typeSegs] at z ⊢
  rw [← hi, priorRep_bin_equiv X e b ℓ ℓ' hm.level hm.flag hm.bin hm.bins,
    priorDel_bin_equiv X e b ℓ ℓ' hm.level hm.flag hm.bin hm.bins]
  change (∏ h, ratio5 ((X.priorRep b ℓ i.1 z).w (θ ((finCongr hlen).symm h)))
      ((X.priorDel b ℓ i.1 (X.p.typeSegs n (i, S, j))).w
        (θ ((finCongr hlen).symm h)))) = _
  exact (finCongr hlen).symm.prod_comp
    (fun h => ratio5 ((X.priorRep b ℓ i.1 z).w (θ h))
      ((X.priorDel b ℓ i.1 (X.p.typeSegs n (i, S, j))).w (θ h)))

theorem step2Fail_depends (b : X.Base) (K : X.Ty) :
    FinProb.DependsOn (fun U => X.step2Fail (b, U) K) K.2.1 := by
  intro U U' h
  have hmass := X.blockMass_ext5 (b, U) (b, U') K K.2.1 rfl h
  have herase : ∀ ℓ, X.blockMass (b, U) K (K.2.1.erase ℓ) =
      X.blockMass (b, U') K (K.2.1.erase ℓ) := by
    intro ℓ
    apply X.blockMass_ext5 (b, U) (b, U') K (K.2.1.erase ℓ) rfl
    intro k hk
    exact h k (Finset.mem_of_mem_erase hk)
  simp only [Setup5.step2Fail, hmass, herase]

theorem optFail_depends (b : X.Base) (K : X.Ty) (t : OAI.HypercubeRamsey.CubeVertex (X.p.m n)) :
    FinProb.DependsOn (fun U => X.optFail (b, U) K t) (insert (X.optKeyOf K t) K.2.1) := by
  intro U U' h
  have hmass := X.blockMass_ext5 (b, U) (b, U') K (insert (X.optKeyOf K t) K.2.1) rfl h
  have hsub : ∀ ℓ ∈ K.2.1, U ℓ = U' ℓ := fun ℓ hℓ => h ℓ (Finset.mem_insert_of_mem hℓ)
  have hbase := X.blockMass_ext5 (b, U) (b, U') K K.2.1 rfl hsub
  simp only [Setup5.optFail, hmass, hbase]

theorem blockGate_bin_equiv (e : Equiv.Perm (BinVector5 n)) (b : X.Base)
    (i i' : CoarseKey5 n) (S S' : Finset X.Key) (j : Option (Fin (X.p.J n + 1)))
    (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, j) ≃ X.gateKeys (i', S', j))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1) (z : X.Block (i, S, j)) :
    X.blockGate (b.1, renameCoarse X e b.2) (i', S', j) z ↔
      X.blockGate b (i, S, j) z := by
  classical
  dsimp only [Setup5.Block, Params5.typeSegs] at z
  have ht (ℓ : X.gateKeys (i, S, j)) (y : Fin N) :
      (X.priorRep (b.1, renameCoarse X e b.2) (eg ℓ).1 i'.1 z).w y ≤
          Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n (i', S', j))) *
            (X.priorDel (b.1, renameCoarse X e b.2) (eg ℓ).1 i'.1
              (X.p.typeSegs n (i', S', j))).w y ↔
      (X.priorRep b ℓ.1 i.1 z).w y ≤
          Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n (i, S, j))) *
            (X.priorDel b ℓ.1 i.1 (X.p.typeSegs n (i, S, j))).w y := by
    rw [← hi, priorRep_bin_equiv X e b ℓ.1 (eg ℓ).1
        (hg ℓ).level (hg ℓ).flag (hg ℓ).bin (hg ℓ).bins,
      priorDel_bin_equiv X e b ℓ.1 (eg ℓ).1
        (hg ℓ).level (hg ℓ).flag (hg ℓ).bin (hg ℓ).bins]
    rfl
  constructor
  · intro h ℓ hℓ y
    exact (ht ⟨ℓ, hℓ⟩ y).1 (h (eg ⟨ℓ, hℓ⟩).1 (eg ⟨ℓ, hℓ⟩).2 y)
  · intro h ℓ hℓ y
    obtain ⟨k, hk⟩ := eg.surjective ⟨ℓ, hℓ⟩
    have hv : (eg k).1 = ℓ := congrArg Subtype.val hk
    subst ℓ
    exact (ht k y).2 (h k.1 k.2 y)

theorem blockMass_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (U U' : X.Hidden)
    (i i' : CoarseKey5 n) (S S' A A' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, j) ≃ X.gateKeys (i', S', j))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (ea : A ≃ A') (ha : ∀ ℓ, PriorMatch X e ℓ.1 (ea ℓ).1)
    (hlen : ∀ ℓ : A, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (ea ℓ).1)
    (hcols : ∀ ℓ : A, colEquiv X ℓ.1 (ea ℓ).1 (hlen ℓ) (U ℓ.1) = U' (ea ℓ).1) :
    X.blockMass ((b.1, renameCoarse X e b.2), U') (i', S', j) A' =
      X.blockMass (b, U) (i, S, j) A := by
  classical
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [Setup5.Block, Params5.typeSegs] at z ⊢
  unfold Setup5.blockWeight
  have hb : X.blockBase (b.1, renameCoarse X e b.2) (i', S', j) z =
      X.blockBase b (i, S, j) z := by
    simp only [Setup5.blockBase, renameCoarse, ← hi, Equiv.symm_apply_apply] <;> rfl
  rw [hb, blockGate_bin_equiv X e b i i' S S' j hi eg hg z]
  congr 1
  rw [← Finset.prod_coe_sort A', ← Finset.prod_coe_sort A]
  rw [← ea.prod_comp]
  apply Finset.prod_congr rfl
  intro ℓ _
  change X.colLik (b.1, renameCoarse X e b.2) (i', S', j) (ea ℓ).1 z (U' (ea ℓ).1) =
    X.colLik b (i, S, j) ℓ.1 z (U ℓ.1)
  rw [← hcols ℓ]
  exact colLik_bin_equiv X e b i i' S S' j hi ℓ.1 (ea ℓ).1 (ha ℓ) (hlen ℓ) z (U ℓ.1)

theorem blockMass_erase_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (U U' : X.Hidden)
    (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, j) ≃ X.gateKeys (i', S', j))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hlen : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1)
    (hcols : ∀ ℓ : S, colEquiv X ℓ.1 (es ℓ).1 (hlen ℓ) (U ℓ.1) = U' (es ℓ).1)
    (q : S) :
    X.blockMass ((b.1, renameCoarse X e b.2), U') (i', S', j) (S'.erase (es q).1) =
      X.blockMass (b, U) (i, S, j) (S.erase q.1) := by
  classical
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [Setup5.Block, Params5.typeSegs] at z ⊢
  unfold Setup5.blockWeight
  have hb : X.blockBase (b.1, renameCoarse X e b.2) (i', S', j) z =
      X.blockBase b (i, S, j) z := by
    simp only [Setup5.blockBase, renameCoarse, ← hi, Equiv.symm_apply_apply] <;> rfl
  rw [hb, blockGate_bin_equiv X e b i i' S S' j hi eg hg z]
  congr 1
  rw [← Finset.filter_ne' S' (es q).1, ← Finset.filter_ne' S q.1]
  simp only [Finset.prod_filter]
  rw [← Finset.prod_coe_sort S', ← Finset.prod_coe_sort S, ← es.prod_comp]
  apply Finset.prod_congr rfl
  intro ℓ _
  have heq : (es ℓ).1 = (es q).1 ↔ ℓ.1 = q.1 := by
    rw [Subtype.val_inj, es.injective.eq_iff, Subtype.val_inj]
  simp only [ne_eq, heq]
  split_ifs with hne
  · rfl
  · change X.colLik (b.1, renameCoarse X e b.2) (i', S', j) (es ℓ).1 z (U' (es ℓ).1) =
      X.colLik b (i, S, j) ℓ.1 z (U ℓ.1)
    rw [← hcols ℓ]
    exact colLik_bin_equiv X e b i i' S S' j hi ℓ.1 (es ℓ).1 (hs ℓ) (hlen ℓ) z (U ℓ.1)

theorem trueBlock_bin_equiv (e : Equiv.Perm (BinVector5 n)) (b : X.Base)
    (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1) :
    X.trueBlock (b.1, renameCoarse X e b.2) (i', S', j) = X.trueBlock b (i, S, j) := by
  dsimp only [Setup5.Block, Params5.typeSegs]
  funext h
  simp [Setup5.trueBlock, renameCoarse, ← hi]

theorem step2Fail_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (U U' : X.Hidden)
    (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, j) ≃ X.gateKeys (i', S', j))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hlen : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1)
    (hcols : ∀ ℓ : S, colEquiv X ℓ.1 (es ℓ).1 (hlen ℓ) (U ℓ.1) = U' (es ℓ).1) :
    X.step2Fail ((b.1, renameCoarse X e b.2), U') (i', S', j) ↔
      X.step2Fail (b, U) (i, S, j) := by
  classical
  have hm := blockMass_bin_equiv X e b U U' i i' S S' S S' j hi eg hg es hs hlen hcols
  have he := blockMass_erase_bin_equiv X e b U U' i i' S S' j hi eg hg es hs hlen hcols
  have hl : (∑ ℓ ∈ S', (colLen5 (X.p.s n) ℓ : ℝ)) =
      ∑ ℓ ∈ S, (colLen5 (X.p.s n) ℓ : ℝ) := by
    rw [← Finset.sum_coe_sort S', ← Finset.sum_coe_sort S, ← es.sum_comp]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [hlen ℓ]
  unfold Setup5.step2Fail
  dsimp only [Prod.fst, Prod.snd]
  rw [trueBlock_bin_equiv X e b i i' S S' j hi,
    blockGate_bin_equiv X e b i i' S S' j hi eg hg, hm, hl]
  have htests : (∃ ℓ ∈ S', X.blockMass (b, U) (i, S, j) S <
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n (i', S', j))) * colLen5 (X.p.s n) ℓ) *
          X.blockMass ((b.1, renameCoarse X e b.2), U') (i', S', j) (S'.erase ℓ)) ↔
      (∃ ℓ ∈ S, X.blockMass (b, U) (i, S, j) S <
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n (i, S, j))) * colLen5 (X.p.s n) ℓ) *
          X.blockMass (b, U) (i, S, j) (S.erase ℓ)) := by
    constructor
    · rintro ⟨ℓ, hℓ, htest⟩
      obtain ⟨q, hq⟩ := es.surjective ⟨ℓ, hℓ⟩
      have hv : (es q).1 = ℓ := congrArg Subtype.val hq
      subst ℓ
      rw [he q, ← hlen q] at htest
      exact ⟨q.1, q.2, htest⟩
    · rintro ⟨ℓ, hℓ, htest⟩
      let q : S := ⟨ℓ, hℓ⟩
      refine ⟨(es q).1, (es q).2, ?_⟩
      rw [he q, ← hlen q]
      exact htest
  rw [htests]
  rfl

theorem step2Conditional_bin_equiv (e : Equiv.Perm (BinVector5 n))
    (b : X.Base) (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, j) ≃ X.gateKeys (i', S', j))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hlen : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1) :
    (X.hiddenLaw (b.1, renameCoarse X e b.2)).pr
        (fun U => X.step2Fail ((b.1, renameCoarse X e b.2), U) (i', S', j)) =
      (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) (i, S, j)) := by
  classical
  symm
  apply pi_pr_local_equiv
    (fun ℓ => FinProb.pi fun _ => X.prior b ℓ)
    (fun ℓ => FinProb.pi fun _ => X.prior (b.1, renameCoarse X e b.2) ℓ)
    S S' (fun _ _ => X.y₀) (fun _ _ => X.y₀)
    es (fun ℓ => colEquiv X ℓ.1 (es ℓ).1 (hlen ℓ))
    (fun ℓ θ => colLaw_weight_equiv X e b ℓ.1 (es ℓ).1 (hs ℓ) (hlen ℓ) θ)
    _ _ (step2Fail_depends X b (i, S, j))
    (step2Fail_depends X (b.1, renameCoarse X e b.2) (i', S', j))
  intro U U' hcols
  exact (step2Fail_bin_equiv X e b U U' i i' S S' j hi eg hg es hs hlen hcols).symm

theorem step2Rate_bin_equiv (v : Fin N) (e : Equiv.Perm (BinVector5 n))
    (i i' : CoarseKey5 n) (S S' : Finset X.Key)
    (j : Option (Fin (X.p.J n + 1))) (hi : e i.1 = i'.1)
    (eg : X.gateKeys (i, S, j) ≃ X.gateKeys (i', S', j))
    (hg : ∀ ℓ, PriorMatch X e ℓ.1 (eg ℓ).1)
    (es : S ≃ S') (hs : ∀ ℓ, PriorMatch X e ℓ.1 (es ℓ).1)
    (hlen : ∀ ℓ : S, colLen5 (X.p.s n) ℓ.1 = colLen5 (X.p.s n) (es ℓ).1) :
    (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (i', S', j)) =
      (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) (i, S, j)) := by
  classical
  simp only [Setup5.keyLawAt, bind_pr]
  rw [expect_equiv (X.coarseLaw v) (X.coarseLaw v) (coarseEquiv X e)
    (coarseLaw_weight_equiv X v e)]
  congr 1
  funext c
  exact step2Conditional_bin_equiv X e (v, c) i i' S S' j hi eg hg es hs hlen

theorem binList_subset_near {n : ℕ} (i : CoarseKey5 n) :
    binList5 i ⊆ nearBinVectors5 i.1 := by
  classical
  intro w hw
  have hdist : ∀ h, Nat.dist (i.1 h).val (w h).val ≤ 1 := by
    by_cases hi : i.2 = true
    · simp only [binList5, hi, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
        true_and] at hw
      rcases hw with hw | hw
      · subst w
        simp
      · exact hw.2
    · have hi' : i.2 = false := by cases h : i.2 <;> simp_all
      simp only [binList5, hi', Bool.false_eq_true, ↓reduceIte,
        Finset.mem_singleton] at hw
      subst w
      simp
  have hvals : ∀ h, w h ∈ binNeighborVals5 i.1 h := by
    intro h
    have hd := hdist h
    unfold Nat.dist at hd
    obtain ⟨d, he⟩ := exists_binNeighborVal5 (i.1 h) (w h) (by omega) (by omega)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, he.symm⟩
  unfold nearBinVectors5
  apply Finset.mem_image.mpr
  refine ⟨fun h _ => w h, ?_, rfl⟩
  simp only [Finset.mem_pi]
  intro h hh
  exact hvals h

theorem binList_card_le {n : ℕ} (i : CoarseKey5 n) :
    (binList5 i).card ≤ 3 ^ coarseChunkCount5 :=
  (Finset.card_le_card (binList_subset_near i)).trans (nearBinVectors5_card_le i.1)

theorem keyAt_coarse {n m : ℕ} (J : ℕ) (i : CoarseKey5 n) (t : OAI.HypercubeRamsey.CubeVertex m)
    (j : ℕ) : (keyAt5 J i t j).coarse = i := by
  unfold keyAt5
  split_ifs <;> rfl

theorem typeKeys_coarse_subset {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : OAI.HypercubeRamsey.CubeVertex n) :
    ∀ ℓ ∈ g.typeKeys J x, ℓ.coarse ∈ g.coarseRange x := by
  classical
  have hself : g.key x ∈ g.coarseRange x := by simp [ChunkGeometry5.coarseRange]
  intro ℓ hℓ
  unfold ChunkGeometry5.typeKeys at hℓ
  by_cases hlow : g.severity x ≤ J
  · rw [ite_eq_left hlow] at hℓ
    rcases Finset.mem_union.mp hℓ with hℓ | hℓ
    · rcases Finset.mem_union.mp hℓ with hℓ | hℓ
      · rcases Finset.mem_image.mp hℓ with ⟨i, hi, rfl⟩
        rwa [keyAt_coarse]
      · rcases Finset.mem_image.mp hℓ with ⟨h, hh, rfl⟩
        rwa [keyAt_coarse]
    · rcases Finset.mem_image.mp hℓ with ⟨j, hj, rfl⟩
      rwa [keyAt_coarse]
  · rw [ite_eq_right hlow] at hℓ
    rcases Finset.mem_image.mp hℓ with ⟨i, hi, rfl⟩
    exact hi

theorem typeKeys_card_le {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : OAI.HypercubeRamsey.CubeVertex n) :
    (g.typeKeys J x).card ≤ coarseChunkCount5 * 4 + 1 + m + 2 := by
  classical
  unfold ChunkGeometry5.typeKeys
  by_cases hlow : g.severity x ≤ J
  · rw [ite_eq_left hlow]
    calc
      _ ≤ (g.coarseRange x).card + (g.flippable x).card + 2 := by
        have hlast : (({g.severity x + 1} : Finset ℕ) ∪
            (if 0 < g.severity x then {g.severity x - 1} else ∅)).card ≤ 2 := by
          split_ifs
          · exact (Finset.card_union_le _ _).trans (by simp)
          · simp
        have h1 := Finset.card_union_le
          ((g.coarseRange x).image (fun i => keyAt5 J i (g.sign x) (g.severity x)))
          ((g.flippable x).image (fun h => keyAt5 J (g.key x)
            (Function.update (g.sign x) h (!g.sign x h)) (g.severity x)))
        have h2 := Finset.card_union_le
          (((g.coarseRange x).image (fun i => keyAt5 J i (g.sign x) (g.severity x))) ∪
            ((g.flippable x).image (fun h => keyAt5 J (g.key x)
              (Function.update (g.sign x) h (!g.sign x h)) (g.severity x))))
          (Finset.image (fun j' => keyAt5 J (g.key x) (g.sign x) j')
            (({g.severity x + 1} : Finset ℕ) ∪
              (if 0 < g.severity x then {g.severity x - 1} else ∅)))
        have h3 := Finset.card_image_le
          (s := g.coarseRange x) (f := fun i => keyAt5 J i (g.sign x) (g.severity x))
        have h4 := Finset.card_image_le
          (s := g.flippable x) (f := fun h => keyAt5 J (g.key x)
            (Function.update (g.sign x) h (!g.sign x h)) (g.severity x))
        have h5 := Finset.card_image_le
          (s := ({g.severity x + 1} : Finset ℕ) ∪
            (if 0 < g.severity x then {g.severity x - 1} else ∅))
          (f := fun j' => keyAt5 J (g.key x) (g.sign x) j')
        omega
      _ ≤ coarseChunkCount5 * 4 + 1 + m + 2 := by
        have hc := g.coarseRange_card_le x
        have hf : (g.flippable x).card ≤ m := by
          simpa using Finset.card_le_univ (g.flippable x)
        omega
  · rw [ite_eq_right hlow]
    have hc := g.coarseRange_card_le x
    have hi := Finset.card_image_le (s := g.coarseRange x)
      (f := fun i => (Sum.inr i : HiddenKey5 n m J))
    omega

theorem keyAt_inl_level {n m J : ℕ} (i : CoarseKey5 n)
    (t : OAI.HypercubeRamsey.CubeVertex m) (j : ℕ)
    (k : CoarseKey5 n × OAI.HypercubeRamsey.CubeVertex m × Fin (J + 1))
    (hk : keyAt5 J i t j = .inl k) : k.2.2.val = j := by
  unfold keyAt5 at hk
  split_ifs at hk with hj
  · have he : (i, t, (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (J + 1))) = k := Sum.inl.inj hk
    rw [← he]

theorem typeKeys_low_levels {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : OAI.HypercubeRamsey.CubeVertex n) (hx : g.severity x ≤ J)
    (k : CoarseKey5 n × OAI.HypercubeRamsey.CubeVertex m × Fin (J + 1))
    (hk : Sum.inl k ∈ g.typeKeys J x) :
    k.2.2.val ∈ ({g.severity x, g.severity x + 1, g.severity x - 1} : Finset ℕ) := by
  classical
  unfold ChunkGeometry5.typeKeys at hk
  rw [ite_eq_left hx] at hk
  rcases Finset.mem_union.mp hk with hk | hk
  · rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hk
      simp [keyAt_inl_level i (g.sign x) (g.severity x) k he]
    · obtain ⟨h, hh, he⟩ := Finset.mem_image.mp hk
      simp [keyAt_inl_level (g.key x) (Function.update (g.sign x) h (!g.sign x h))
        (g.severity x) k he]
  · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hk
    rw [keyAt_inl_level (g.key x) (g.sign x) j k he]
    rcases Finset.mem_union.mp hj with hj | hj
    · simp only [Finset.mem_singleton] at hj
      simp [hj]
    · by_cases hs : 0 < g.severity x
      · simp only [ite_eq_left hs, Finset.mem_singleton] at hj
        simp [hj]
      · simp [hs] at hj

def localBins {n m : ℕ} (g : ChunkGeometry5 n m) (x : OAI.HypercubeRamsey.CubeVertex n) :
    Finset (BinVector5 n) := (g.coarseRange x).biUnion binList5

theorem localBins_card_le {n m : ℕ} (g : ChunkGeometry5 n m)
    (x : OAI.HypercubeRamsey.CubeVertex n) :
    (localBins g x).card ≤ (coarseChunkCount5 * 4 + 1) * 3 ^ coarseChunkCount5 := by
  classical
  unfold localBins
  calc
    _ ≤ ∑ i ∈ g.coarseRange x, (binList5 i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ g.coarseRange x, 3 ^ coarseChunkCount5 :=
      Finset.sum_le_sum fun i _ => binList_card_le i
    _ = (g.coarseRange x).card * 3 ^ coarseChunkCount5 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (g.coarseRange_card_le x)

theorem bin_mem_binList {n : ℕ} (i : CoarseKey5 n) : i.1 ∈ binList5 i := by
  classical
  unfold binList5
  split_ifs <;> simp

theorem typeKey_bins_subset {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : OAI.HypercubeRamsey.CubeVertex n) (ℓ : HiddenKey5 n m J)
    (hℓ : ℓ ∈ g.typeKeys J x) : binList5 ℓ.coarse ⊆ localBins g x := by
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨ℓ.coarse, typeKeys_coarse_subset g J x ℓ hℓ, hw⟩

theorem central_bins_subset {n m : ℕ} (g : ChunkGeometry5 n m)
    (x : OAI.HypercubeRamsey.CubeVertex n) : binList5 (g.key x) ⊆ localBins g x := by
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨g.key x, by simp [ChunkGeometry5.coarseRange], hw⟩

def shapeBinBound : ℕ := (coarseChunkCount5 * 4 + 1) * 3 ^ coarseChunkCount5

abbrev CoarseCode := Bool × Fin shapeBinBound × Finset (Fin shapeBinBound)

structure BinNaming (n : ℕ) where
  bins : Finset (BinVector5 n)
  labels : bins ↪ Fin shapeBinBound

def namingOfBound (B : Finset (BinVector5 n)) (hB : B.card ≤ shapeBinBound) : BinNaming n :=
  ⟨B, Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_coe, Fintype.card_fin] using hB))⟩

def localNaming {n m : ℕ} (g : ChunkGeometry5 n m)
    (x : OAI.HypercubeRamsey.CubeVertex n) : BinNaming n :=
  namingOfBound (localBins g x) (localBins_card_le g x)

def coarseCode (b : BinNaming n) (i : CoarseKey5 n)
    (hi : binList5 i ⊆ b.bins) : CoarseCode :=
  (i.2, b.labels ⟨i.1, hi (bin_mem_binList i)⟩, labelSet b.bins b.labels (binList5 i) hi)

theorem coarseCode_match (b b' : BinNaming n)
    (r : BinRename b.bins b'.bins b.labels b'.labels)
    (i i' : CoarseKey5 n) (hi : binList5 i ⊆ b.bins) (hi' : binList5 i' ⊆ b'.bins)
    (hc : coarseCode b i hi = coarseCode b' i' hi') :
    i.2 = i'.2 ∧ r.perm i.1 = i'.1 ∧ (binList5 i).image r.perm = binList5 i' := by
  have hf : i.2 = i'.2 := congrArg Prod.fst hc
  have hl : b.labels ⟨i.1, hi (bin_mem_binList i)⟩ =
      b'.labels ⟨i'.1, hi' (bin_mem_binList i')⟩ := congrArg (fun c : CoarseCode => c.2.1) hc
  have hs : labelSet b.bins b.labels (binList5 i) hi =
      labelSet b'.bins b'.labels (binList5 i') hi' := congrArg (fun c : CoarseCode => c.2.2) hc
  let a : b.bins := ⟨i.1, hi (bin_mem_binList i)⟩
  have he : r.localEquiv a = (⟨i'.1, hi' (bin_mem_binList i')⟩ : b'.bins) :=
    b'.labels.injective ((r.label_local a).trans hl)
  exact ⟨hf, (r.perm_local a).trans (congrArg Subtype.val he),
    labelSet_perm b.bins b'.bins b.labels b'.labels r (binList5 i) (binList5 i') hi hi' hs⟩

theorem priorMatch_of_code (b b' : BinNaming n)
    (r : BinRename b.bins b'.bins b.labels b'.labels) (ℓ ℓ' : X.Key)
    (hℓ : binList5 ℓ.coarse ⊆ b.bins) (hℓ' : binList5 ℓ'.coarse ⊆ b'.bins)
    (hc : coarseCode b ℓ.coarse hℓ = coarseCode b' ℓ'.coarse hℓ')
    (hl : ℓ.level = ℓ'.level) : PriorMatch X r.perm ℓ ℓ' := by
  obtain ⟨hf, hb, hs⟩ := coarseCode_match b b' r ℓ.coarse ℓ'.coarse hℓ hℓ' hc
  exact ⟨hl, hf, hb, hs⟩

theorem colLen_of_kind (ℓ ℓ' : X.Key) (hk : ℓ.isLeft = ℓ'.isLeft) :
    colLen5 (X.p.s n) ℓ = colLen5 (X.p.s n) ℓ' := by
  cases ℓ <;> cases ℓ' <;> simp_all [colLen5]

end
end HypercubeRamsey.Lane_sol_s05_h1
