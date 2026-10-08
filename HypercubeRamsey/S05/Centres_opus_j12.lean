import HypercubeRamsey.S05.Centres_sol_s05_centres_marking

/-!
# J12 helpers: key and array locality of the short presentation

Generic facts used by `Lane_opus_s05.presentation_local` (05:991–1001): the Step 3 record tests read
only the record's arrays and columns; keys of an even type, role or optional column lie within one
sign step; selections read eligibility only within their radius; and the finite-law identities used
to integrate out unread arrays. Adapted from the GPT-6.1 Sol lane `sol-s05-j12`.
-/

namespace HypercubeRamsey.Setup5.Lane_opus_s05_j12

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

section Records

variable {Id : Type} [DecidableEq Id]
/-- All arrays explicitly named by a record. -/
def recordArrays (r : X.RecordOn Id) : Finset (Id × X.Ty) :=
  r.2.1 ∪ r.2.2.1.image (fun c => (c.1, c.2.1)) ∪
    (r.2.2.2.toFinset.image fun c => (c.1, c.2.1))

/-- Columns read by the record's array kernels, its target and its optional entries. -/
def recordKeys (r : X.RecordOn Id) : Finset X.Key :=
  insert r.1 ((recordArrays X r).biUnion (fun c => c.2.2.1) ∪
    r.2.2.1.biUnion (fun c => c.2.2.toFinset))

private theorem obs_mem (r : X.RecordOn Id) (c) (hc : c ∈ r.2.1) :
    c ∈ recordArrays X r := by simp [recordArrays, hc]

private theorem ref_mem (r : X.RecordOn Id) (c) (hc : c ∈ r.2.2.1) :
    (c.1, c.2.1) ∈ recordArrays X r := by
  simp only [recordArrays, Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inr ⟨c, hc, rfl⟩)

private theorem pool_mem (r : X.RecordOn Id) (c M) (hc : r.2.2.2 = some (c.1, c.2, M)) :
    c ∈ recordArrays X r := by
  simp only [recordArrays, hc, Option.toFinset_some, Finset.image_singleton,
    Finset.mem_union, Finset.mem_singleton]
  exact Or.inr trivial

theorem blockLawOn_ext (H H' : X.KeyHist) (K : X.Ty) (S : Finset X.Key)
    (hb : H.1 = H'.1) (hc : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    X.blockLawOn H K S = X.blockLawOn H' K S := by
  unfold Setup5.blockLawOn
  congr 1
  funext z
  unfold Setup5.blockWeight
  rw [hb]
  congr 1
  exact Finset.prod_congr rfl (fun ℓ hℓ => by rw [hc ℓ hℓ])

private theorem replaced_cols (H H' : X.KeyHist) (target : X.Key)
    (θ : Fin (colLen5 (X.p.s n) target) → Fin N) (S : Finset X.Key)
    (hc : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    ∀ ℓ ∈ S, (X.withCol H target θ).2 ℓ = (X.withCol H' target θ).2 ℓ := by
  intro ℓ hℓ
  by_cases he : ℓ = target
  · subst ℓ; simp [Setup5.withCol]
  · simp only [Setup5.withCol, Function.update_of_ne he, hc ℓ hℓ]

/-- The record test is unchanged when its named arrays and columns are unchanged. -/
theorem record_tests_ext (H H' : X.KeyHist) (r : X.RecordOn Id)
    (a a' : X.ArraysOn (Id)) (hb : H.1 = H'.1)
    (hcol : ∀ ℓ ∈ recordKeys X r, H.2 ℓ = H'.2 ℓ)
    (ha : ∀ c ∈ recordArrays X r, a c = a' c) :
    X.step3FailOn H r a = X.step3FailOn H' r a' ∧
      (∀ excl θ, X.step3PostOn H r a excl θ = X.step3PostOn H' r a' excl θ) ∧
      (∀ θ, X.candGateOn H r a θ = X.candGateOn H' r a' θ) := by
  have ht : H.2 r.1 = H'.2 r.1 := hcol _ (by simp [recordKeys])
  have htypes (c) (hc : c ∈ recordArrays X r) :
      ∀ ℓ ∈ c.2.2.1, H.2 ℓ = H'.2 ℓ := by
    intro ℓ hℓ
    apply hcol
    simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
    exact Or.inr (Or.inl ⟨c, hc, hℓ⟩)
  have hmass (c) (hc : c ∈ recordArrays X r) (S : Finset X.Key) (hS : S ⊆ c.2.2.1) :
      X.blockMass H c.2 S = X.blockMass H' c.2 S :=
    X.blockMass_ext5 H H' c.2 S hb (fun ℓ hℓ => htypes c hc ℓ (hS hℓ))
  have hlaw (c : Id × X.Ty) (hc : c ∈ recordArrays X r)
      (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
      X.blockLaw (X.withCol H r.1 θ) c.2 = X.blockLaw (X.withCol H' r.1 θ) c.2 := by
    exact blockLawOn_ext X (X.withCol H r.1 θ) (X.withCol H' r.1 θ) c.2 c.2.2.1 hb
      (replaced_cols X H H' r.1 θ c.2.2.1 (htypes c hc))
  have hdel (c) (hc : c ∈ recordArrays X r) :
      X.blockLawDel H c.2 r.1 = X.blockLawDel H' c.2 r.1 := by
    exact blockLawOn_ext X H H' c.2 (c.2.2.1.erase r.1) hb
      (fun ℓ hℓ => htypes c hc ℓ (Finset.mem_of_mem_erase hℓ))
  have hhit (c) (hc : c ∈ recordArrays X r) (y) : X.hitSet a c y = X.hitSet a' c y := by
    unfold Setup5.hitSet
    rw [ha c hc]
  have hgate (θ) : X.candGateOn H r a θ = X.candGateOn H' r a' θ := by
    apply propext
    unfold Setup5.candGateOn
    constructor <;> intro hh
    · constructor
      · intro c hc htarget
        have hc' := obs_mem X r c hc
        have hr := X.blockMass_ext5 (X.withCol H r.1 θ) (X.withCol H' r.1 θ)
          c.2 c.2.2.1 hb (replaced_cols X H H' r.1 θ _ (htypes c hc'))
        simpa only [hmass c hc' _ (Finset.erase_subset _ _), hr] using hh.1 c hc htarget
      · intro c M hc h
        simpa only [hhit c (pool_mem X r c M hc)] using hh.2 c M hc h
    · constructor
      · intro c hc htarget
        have hc' := obs_mem X r c hc
        have hr := X.blockMass_ext5 (X.withCol H r.1 θ) (X.withCol H' r.1 θ)
          c.2 c.2.2.1 hb (replaced_cols X H H' r.1 θ _ (htypes c hc'))
        simpa only [hmass c hc' _ (Finset.erase_subset _ _), hr] using hh.1 c hc htarget
      · intro c M hc h
        simpa only [hhit c (pool_mem X r c M hc)] using hh.2 c M hc h
  have hlik (θ excl) : X.obsLikOn H r a θ excl = X.obsLikOn H' r a' θ excl := by
    unfold Setup5.obsLikOn
    apply Finset.prod_congr rfl
    intro c hc
    have hc' := obs_mem X r c (Finset.mem_filter.mp hc).1
    rw [ha c hc', hlaw c hc' θ, hdel c hc']
  have hm (excl) : X.step3MassOn H r a excl = X.step3MassOn H' r a' excl := by
    unfold Setup5.step3MassOn
    rw [hb]
    simp_rw [hgate, hlik]
  have hp (excl θ) : X.step3PostOn H r a excl θ = X.step3PostOn H' r a' excl θ := by
    unfold Setup5.step3PostOn
    rw [hb, hgate, hlik, hm]
  have hsub (c) (hc : c ∈ r.2.2.1) :
      X.refSubsetOn H a (c.1, c.2.1) c.2.2 = X.refSubsetOn H' a' (c.1, c.2.1) c.2.2 := by
    have ha' := hhit (c.1, c.2.1) (ref_mem X r c hc)
    unfold Setup5.refSubsetOn
    split
    · rfl
    · cases ho : c.2.2 with
      | none => rfl
      | some ℓ =>
        cases ℓ with
        | inr i => rfl
        | inl k =>
          have hk : H.2 (.inl k) = H'.2 (.inl k) := by
            apply hcol
            simp only [recordKeys, Finset.mem_insert, Finset.mem_union, Finset.mem_biUnion]
            exact Or.inr (Or.inr ⟨c, hc, by simp [ho]⟩)
          simp only [Setup5.lowCol, hk, ha']
          rfl
  have href : X.refsOn H r a = X.refsOn H' r a' := by
    unfold Setup5.refsOn
    ext d
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨c, hc, he⟩
      refine ⟨c, hc, ?_⟩
      rw [← hsub c hc]
      exact he
    · rintro ⟨c, hc, he⟩
      refine ⟨c, hc, ?_⟩
      rw [hsub c hc]
      exact he
  have hpf (excl) : X.step3PostOn H r a excl = X.step3PostOn H' r a' excl := funext (hp excl)
  have hs (h) : X.highSource H r a h = X.highSource H' r a' h := by
    unfold Setup5.highSource
    rw [hpf, ht]
  have hd (c h) : X.highDeleted H r a c h = X.highDeleted H' r a' c h := by
    unfold Setup5.highDeleted
    rw [hpf, ht]
  have hcap : X.HighCapped H r a = X.HighCapped H' r a' := by
    simp only [Setup5.HighCapped, hs]
  have hprice : X.HighPriceFeasible H r a = X.HighPriceFeasible H' r a' := by
    unfold Setup5.HighPriceFeasible
    rw [href]
    simp only [hs, hd]
  refine ⟨?_, (fun excl θ => hp excl θ), hgate⟩
  simp only [Setup5.step3FailOn, ht, hgate, hm, href, hcap, hprice]



end Records

section Signs

theorem update_distance {m : ℕ} (t : CubeVertex m) (i : Fin m) (b : Bool) :
    _root_.hammingDist (Function.update t i b) t ≤ 1 := by
  change (Finset.univ.filter fun j => Function.update t i b j ≠ t j).card ≤ 1
  have h : (Finset.univ.filter fun j => Function.update t i b j ≠ t j) ⊆ {i} := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    by_contra hh
    have hji : j ≠ i := by simpa using hh
    exact hj' (Function.update_of_ne hji _ _)
  simpa using Finset.card_le_card h

theorem adjacent_sign (x y : CubeVertex n) (hxy : (cube n).Adj x y) :
    _root_.hammingDist (X.g.sign y) (X.g.sign x) ≤ 1 := by
  have h := Lane_sol_s05_h5l.adjacent_sign_mem X.g x y hxy
  rcases Finset.mem_insert.mp h with he | h
  · simp [he]
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    rw [← he]
    exact update_distance _ _ _

def within (t : CubeVertex (X.p.m n)) (q : ℕ) : X.Key → Prop
  | .inl k => _root_.hammingDist k.2.1 t ≤ q
  | .inr _ => True

theorem within_mono {t : CubeVertex (X.p.m n)} {q r : ℕ} (hq : q ≤ r)
    {ℓ : X.Key} (h : within X t q ℓ) : within X t r ℓ := by
  cases ℓ with
  | inl k => exact h.trans hq
  | inr i => trivial

theorem keyAt_sign (i : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : ℕ)
    (k : X.LowIdx) (h : keyAt5 (X.p.J n) i t j = .inl k) : k.2.1 = t := by
  unfold keyAt5 at h
  split at h
  · exact congrArg (fun k => k.2.1) (Sum.inl.inj h).symm
  · simp at h

theorem type_keys_within (x : CubeVertex n) (t : CubeVertex (X.p.m n)) (q : ℕ)
    (hx : _root_.hammingDist (X.g.sign x) t ≤ q) :
    ∀ ℓ ∈ (X.g.evenType (X.p.J n) x).2.1, within X t (q + 1) ℓ := by
  intro ℓ hℓ
  cases ℓ with
  | inr i => trivial
  | inl k =>
    change _root_.hammingDist k.2.1 t ≤ q + 1
    change Sum.inl k ∈ X.g.typeKeys (X.p.J n) x at hℓ
    unfold ChunkGeometry5.typeKeys at hℓ
    split at hℓ
    · rcases Finset.mem_union.mp hℓ with hℓ | hℓ
      · rcases Finset.mem_union.mp hℓ with hℓ | hℓ
        · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hℓ
          rw [keyAt_sign X _ _ _ k he]
          omega
        · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hℓ
          rw [keyAt_sign X _ _ _ k he]
          have h1 := update_distance (X.g.sign x) i (!X.g.sign x i)
          have h2 := _root_.hammingDist_triangle
            (Function.update (X.g.sign x) i (!X.g.sign x i)) (X.g.sign x) t
          omega
      · obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hℓ
        rw [keyAt_sign X _ _ _ k he]
        omega
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hℓ
      simp at he

theorem role_key_within (x : CubeVertex n) (t : CubeVertex (X.p.m n)) (q : ℕ)
    (hx : _root_.hammingDist (X.g.sign x) t ≤ q) :
    within X t q (X.g.roleKey (X.p.J n) x) := by
  unfold ChunkGeometry5.roleKey
  split
  · exact hx
  · trivial

theorem optional_key_within (x : CubeVertex n) (t : CubeVertex (X.p.m n)) (q : ℕ)
    (hx : _root_.hammingDist (X.g.sign x) t ≤ q) :
    ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) x).toFinset, within X t q ℓ := by
  unfold ChunkGeometry5.optionalKey
  split
  · simpa [within] using hx
  · simp

theorem reach_site (p : HDParams) (S : p.Sites) (P A : p.Loc → Bool) (e : p.EligMap)
    (v : CubeVertex p.d) (R : ℕ) {u j} (h : p.Reach S P A e v R u j) :
    u ∈ S ∧ _root_.hammingDist u v ≤ R := by
  induction h with
  | start u hu hd => exact ⟨hu, hd⟩
  | up u j hj h hb ih => exact ih
  | down u u' j h hu hd hdu ih => exact ⟨hu, hd⟩

theorem selection_congr (p : HDParams) (S : p.Sites) (P A : p.Loc → Bool)
    (e e' : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (R : ℕ)
    (hv : v ∈ S) (he : ∀ u ∈ S, _root_.hammingDist u v ≤ R → e u = e' u) :
    p.selectionAt S P A e τ R v = p.selectionAt S P A e' τ R v := by
  have hre (e e' : p.EligMap)
      (he : ∀ u ∈ S, _root_.hammingDist u v ≤ R → e u = e' u)
      {u j} (h : p.Reach S P A e v R u j) : p.Reach S P A e' v R u j := by
    induction h with
    | start u hu hd => exact .start u hu hd
    | up u j hj h hb ih =>
      have hs := reach_site p S P A e v R h
      have hb' : p.BadN P A e' u j := by
        simpa only [HDParams.BadN, HDParams.Bad, he u hs.1 hs.2] using hb
      exact .up u j hj ih hb'
    | down u u' j h hu hd hdu ih => exact .down u u' j ih hu hd hdu
  have hh : p.height S P A e R v = p.height S P A e' R v := by
    unfold HDParams.height
    congr 1
    apply Finset.filter_congr
    intro j hj
    exact ⟨hre e e' he, hre e' e (fun u hu hd => (he u hu hd).symm)⟩
  have hev : e v = e' v := he v hv (by simp)
  unfold HDParams.selectionAt
  simp only [hh, hev, HDParams.Bad]


/-- Types whose low keys all lie within sign distance `q` of `t`. -/
def localTypes (t : CubeVertex (X.p.m n)) (q : ℕ) : Finset X.Ty :=
  Finset.univ.filter fun K => ∀ ℓ ∈ K.2.1, within X t q ℓ

theorem refSubset_ext {Id : Type} (H H' : X.KeyHist) (A A' : X.ArraysOn Id)
    (c : Id × X.Ty) (opt : Option X.Key) (ha : A c = A' c)
    (hc : ∀ ℓ ∈ opt.toFinset, H.2 ℓ = H'.2 ℓ) :
    X.refSubsetOn H A c opt = X.refSubsetOn H' A' c opt := by
  have hhit (y) : X.hitSet A c y = X.hitSet A' c y := by simp only [Setup5.hitSet, ha]
  unfold Setup5.refSubsetOn
  cases c.2.2.2
  · cases opt with
    | none => rfl
    | some ℓ =>
      cases ℓ with
      | inr i => rfl
      | inl k =>
        have hk := hc (.inl k) (by simp)
        simp only [Setup5.lowCol, hk, hhit]
        rfl
  · rfl


theorem neighbor_sign_bound (y : OddRole5 n) (v : EvenRole5 n) (hv : v ∈ evenNbrs y)
    (t : CubeVertex (X.p.m n)) (q : ℕ) (hy : _root_.hammingDist (X.g.sign y.1) t ≤ q) :
    _root_.hammingDist (X.g.sign v.1) t ≤ q + 1 := by
  have h1 := adjacent_sign X y.1 v.1 ((Finset.mem_filter.mp hv).2.symm)
  have h2 := _root_.hammingDist_triangle (X.g.sign v.1) (X.g.sign y.1) t
  omega

theorem incident_sign (v : EvenRole5 n) (b : X.St.Site)
    (hv : X.St.stateOf v.1 ∈ X.St.neighbors b) (y : OddRole5 n) (hy : X.St.stateOf y.1 = b) :
    _root_.hammingDist (X.g.sign y.1) (X.g.sign v.1) ≤ 1 := by
  obtain ⟨x, z, hx, hz, hadj⟩ := (X.St.mem_neighbors b (X.St.stateOf v.1)).mp hv
  have hxs := (X.St.state_determines x y.1 (hx.trans hy.symm)).2.1
  have hzs := (X.St.state_determines z v.1 hz).2.1
  have h := adjacent_sign X z x hadj.symm
  simpa only [hxs, hzs] using h


/-- Arrays of types outside `U` replaced by the fallback array. -/
def maskArrays (U : Finset X.Ty) (A : ∀ K : X.Ty, X.Array K) : ∀ K : X.Ty, X.Array K :=
  fun K => if K ∈ U then A K else fun _ => X.fallbackBlock K

end Signs

section Laws

theorem prob_ext {A : Type} [Fintype A] {P Q : FinProb A} (h : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem map_pi {I : Type} [Fintype I] [DecidableEq I]
    {A B : I → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (B i)] (P : ∀ i, FinProb (A i)) (g : ∀ i, A i → B i) :
    FinProb.map (FinProb.pi P) (fun a i => g i (a i)) =
      FinProb.pi (fun i => FinProb.map (P i) (g i)) := by
  apply prob_ext
  funext b
  change (∑ a : ∀ i, A i, if (fun i => g i (a i)) = b then ∏ i, (P i).w (a i) else 0) =
    ∏ i, ∑ a, if g i a = b i then (P i).w a else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : (fun i => g i (a i)) = b
  · have hall : ∀ i, g i (a i) = b i := fun i => congrFun h i
    simp [h, hall]
  · rw [if_neg h]
    have hn : ¬ ∀ i, g i (a i) = b i := fun hh => h (funext hh)
    obtain ⟨i, hi⟩ := not_forall.mp hn
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem map_prod {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq C] [DecidableEq D] (P : FinProb A) (Q : FinProb B)
    (f : A → C) (g : B → D) :
    FinProb.map (P.prod Q) (fun ab => (f ab.1, g ab.2)) =
      (FinProb.map P f).prod (FinProb.map Q g) := by
  apply prob_ext
  funext cd
  change (∑ ab : A × B, if (f ab.1, g ab.2) = cd then P.w ab.1 * Q.w ab.2 else 0) =
    (∑ a, if f a = cd.1 then P.w a else 0) * (∑ b, if g b = cd.2 then Q.w b else 0)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hf : f a = cd.1 <;> by_cases hg : g b = cd.2 <;> simp [hf, hg, Prod.ext_iff]

theorem map_id {A : Type} [Fintype A] [DecidableEq A] (P : FinProb A) :
    FinProb.map P id = P := by
  apply prob_ext
  funext a
  simp [FinProb.map]

theorem map_prod_snd {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq C] (P : FinProb A) (Q : FinProb B) (g : B → C) :
    FinProb.map (P.prod Q) (fun ab => (ab.1, g ab.2)) = P.prod (FinProb.map Q g) := by
  simpa only [id, map_id] using map_prod P Q id g

theorem map_const {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (P Q : FinProb A) (b : B) : FinProb.map P (fun _ => b) = FinProb.map Q (fun _ => b) := by
  apply prob_ext
  funext b'
  change (∑ a, if b = b' then P.w a else 0) = ∑ a, if b = b' then Q.w a else 0
  split_ifs <;> simp [P.sum_eq_one, Q.sum_eq_one]

theorem pr_map {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinProb A) (f : A → B) (F : B → Prop) :
    (FinProb.map P f).pr F = P.pr (fun a => F (f a)) := by
  simpa [FinProb.expect, FinProb.pr, mul_ite] using
    FinProb.map_expect P f (fun b => if F b then (1 : ℝ) else 0)


end Laws

end

end HypercubeRamsey.Setup5.Lane_opus_s05_j12
