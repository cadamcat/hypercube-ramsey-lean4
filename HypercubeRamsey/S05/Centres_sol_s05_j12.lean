import HypercubeRamsey.S05.History
import HypercubeRamsey.S03.Height.Selection
import HypercubeRamsey.S05.Centres_sol_s05_centres_marking

namespace HypercubeRamsey.Lane_sol_s05_j12

open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

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


end
end HypercubeRamsey.Lane_sol_s05_j12

namespace HypercubeRamsey.Lane_sol_s05_j12
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

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

end
end HypercubeRamsey.Lane_sol_s05_j12

namespace HypercubeRamsey.Lane_sol_s05_j12
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section

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

end
end HypercubeRamsey.Lane_sol_s05_j12

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)
abbrev hp (q : HDParams) : HDParams := { q with d := X.St.d }
/-- What is drawn at one ambient location: presence, activation, tie permutation, and an array of every type. -/
abbrev CVal (h : HDParams) := Bool × Bool × (hp X h).TiePerm × (∀ K : X.Ty, X.Array K)

/-- The center experiment's sample space. -/
abbrev CΩ (h : HDParams) := ∀ l : (hp X h).Loc, CVal X h

/-- The center law at a key history: independent presence, activations, ties, and arrays of independent
`P_K`-blocks generated at every ID, present or not (05:181–187, 05:249–254). -/
def centreLaw (h : HDParams) (H : X.KeyHist) : FinProb (CΩ X h) :=
  FinProb.pi fun _ =>
    (FinProb.bernoulli ((hp X h).lam / ((hp X h).V : ℝ))).prod
      ((FinProb.bernoulli ((n : ℝ) ^ h.b₀ / (hp X h).lam)).prod
        ((FinProb.uniformAll (Ω := (hp X h).TiePerm) ⟨1⟩).prod
          (FinProb.pi fun K : X.Ty => FinProb.pi fun _ : Fin (X.p.typeBlocks n K) => X.blockLaw H K)))

variable {X}
variable {h : HDParams}

/-- Prospective presence. -/
def pos (ω : CΩ X h) : (hp X h).Loc → Bool := fun l => (ω l).1
/-- Activations. -/
def act (ω : CΩ X h) : (hp X h).Loc → Bool := fun l => (ω l).2.1
/-- Tie permutations. -/
def tie (ω : CΩ X h) : (hp X h).Ties := fun l => (ω l).2.2.1
/-- The array of type `K` at a location. -/
def arr (ω : CΩ X h) (l : (hp X h).Loc) (K : X.Ty) : X.Array K := (ω l).2.2.2 K
/-- All arrays, indexed by (location, type). -/
def arraysOf (ω : CΩ X h) : X.ArraysOn (hp X h).Loc := fun c => arr ω c.1 c.2

variable (X)

/-- Height sites: the one-hot images of the even states (05:315–317). -/
def sites (h : HDParams) : (hp X h).Sites :=
  Finset.univ.image fun v : EvenRole5 n => X.St.oneHot (X.St.stateOf v.1)

/-- The site of an even role. -/
def siteOf (v : EvenRole5 n) : CubeVertex X.St.d := X.St.oneHot (X.St.stateOf v.1)

/-- Selection with either consultation radius, using the same eligibility and ties (05:861–879). -/
def selAt (elig : CΩ X h → (hp X h).EligMap) (ω : CΩ X h) (R : ℕ) (v : EvenRole5 n) : Option (hp X h).Loc :=
  (hp X h).selectionAt (sites X h) (pos ω) (act ω) (elig ω) (tie ω) R (siteOf X v)

/-- The long-rule selection at an even role (05:851–853). -/
def selLong (elig : CΩ X h → (hp X h).EligMap) (ω : CΩ X h) (v : EvenRole5 n) : Option (hp X h).Loc :=
  (hp X h).selection (sites X h) (pos ω) (act ω) (elig ω) (tie ω) (siteOf X v)

/-- The short-rule selection, consultation radius `D ⌊√m⌋` (05:328–329). -/
def selShort (elig : CΩ X h → (hp X h).EligMap) (ω : CΩ X h) (v : EvenRole5 n) : Option (hp X h).Loc :=
  (hp X h).selectionAt (sites X h) (pos ω) (act ω) (elig ω) (tie ω) ((hp X h).Rshort (X.p.m n)) (siteOf X v)

/-- The block subset of the tuple used at even role `v` with array at `l` (05:155–160): the whole low array; at a
high type the first `k_*/u_*` pool blocks hitting the optional column if there are enough, otherwise the first
blocks. -/
def refSubset (H : X.KeyHist) (ω : CΩ X h) (v : EvenRole5 n) (l : (hp X h).Loc) : Finset (Fin X.blockBound) :=
  X.refSubsetOn H (arraysOf ω) (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)

/-- A center reference: location and block subset. -/
abbrev CRef (h : HDParams) := (hp X h).Loc × Finset (Fin X.blockBound)

/-- The reference selected at an even role by the long rule. -/
def evenRefOf (elig : CΩ X h → (hp X h).EligMap) (H : X.KeyHist) (ω : CΩ X h) (v : EvenRole5 n) :
    Option (CRef X h) :=
  (selLong X elig ω v).map fun l => (l, refSubset X H ω v l)

/-- The record of an odd role at a specified consultation radius (05:331–343,861–879): its neighbours' selected arrays, the needed same-mode
references, and at a low role with a high neighbour, that pool and the mask hit by the actual target. -/
def actualRecordAt (elig : CΩ X h → (hp X h).EligMap) (H : X.KeyHist) (ω : CΩ X h) (R : ℕ) (y : OddRole5 n) :
    X.RecordOn (hp X h).Loc :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs : Finset ((hp X h).Loc × X.Ty) := (evenNbrs y).biUnion fun a =>
    match selAt X elig ω R a with
    | some l => {(l, X.g.evenType (X.p.J n) a.1)}
    | none => ∅
  let refs : Finset ((hp X h).Loc × X.Ty × Option X.Key) := (evenNbrs y).biUnion fun a =>
    match selAt X elig ω R a with
    | some l =>
      if ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
    | none => ∅
  let mask : Option ((hp X h).Loc × X.Ty × Finset (Fin X.blockBound)) :=
    match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (selAt X elig ω R a).isSome then
        let a := Classical.choose hex
        match selAt X elig ω R a with
        | some l =>
          some (l, X.g.evenType (X.p.J n) a.1,
            X.firstK (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
              (X.p.usedBlocks n))
        | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

/-- The actual long-rule record. -/
def actualRecord (elig : CΩ X h → (hp X h).EligMap) (H : X.KeyHist) (ω : CΩ X h) (y : OddRole5 n) :
    X.RecordOn (hp X h).Loc :=
  actualRecordAt X elig H ω (hp X h).Rlong y

/-- The tuple of a reference: its blocks in the array of the even role's type. -/
def refBlocks (ω : CΩ X h) (v : EvenRole5 n) (c : CRef X h) :
    Finset (X.Block (X.g.evenType (X.p.J n) v.1)) :=
  (Finset.univ.filter fun i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)) =>
    ∃ j ∈ c.2, X.blockIdx _ j = some i).image (arr ω c.1 (X.g.evenType (X.p.J n) v.1))

/-- The average coordinate marginal `P̄_K` of a block law (05:787–789). -/
def avgMarg (H : X.KeyHist) (K : X.Ty) (x : Fin N) : ℝ :=
  ((X.p.q0 * X.p.typeSegs n K : ℕ) : ℝ)⁻¹ *
    ∑ z, (X.blockLaw H K).w z * ((Finset.univ.filter fun e : Fin (X.p.typeSegs n K) × Fin X.p.q0 =>
      z e.1 e.2 = x).card : ℝ)

/-- Prior-heavy labels for a type: `N P̄_K(x) > B_K = A_K^{K_B}` (05:789–791). -/
def PriorHeavy (H : X.KeyHist) (K : X.Ty) (x : Fin N) : Prop :=
  X.blockConst K ^ X.p.KB < (N : ℝ) * avgMarg X H K x

/-- The number of prior-heavy entries in the tuple of a reference. -/
def heavyCount (H : X.KeyHist) (ω : CΩ X h) (v : EvenRole5 n) (c : CRef X h) : ℕ :=
  ∑ i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)),
    if ∃ j ∈ c.2, X.blockIdx _ j = some i then
      (Finset.univ.filter fun e : Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) × Fin X.p.q0 =>
        PriorHeavy X H (X.g.evenType (X.p.J n) v.1) (arr ω c.1 (X.g.evenType (X.p.J n) v.1) i e.1 e.2)).card
    else 0


variable (ht : HDParams)
/-- Prospective IDs at a site and level (05:820–824). -/
def prosp (P : (hp X ht).Loc → Bool) (s : CubeVertex (hp X ht).d) (j : ℕ) : Finset (hp X ht).Loc :=
  Finset.univ.filter fun l => P l = true ∧ (l.2 : ℕ) = j ∧ _root_.hammingDist l.1 s ≤ (hp X ht).r

/-- The record of an odd role for given choices at its even neighbours: the body of
`actualRecordAt` with the selections replaced by `σ` (05:331–343). -/
def recordOf (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc) (σ : EvenRole5 n → Option (hp X ht).Loc)
    (y : OddRole5 n) : X.RecordOn (hp X ht).Loc :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs : Finset ((hp X ht).Loc × X.Ty) := (evenNbrs y).biUnion fun a =>
    match σ a with
    | some l => {(l, X.g.evenType (X.p.J n) a.1)}
    | none => ∅
  let refs : Finset ((hp X ht).Loc × X.Ty × Option X.Key) := (evenNbrs y).biUnion fun a =>
    match σ a with
    | some l =>
      if ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
    | none => ∅
  let mask : Option ((hp X ht).Loc × X.Ty × Finset (Fin X.blockBound)) :=
    match ℓ with
    | .inl k =>
      if hex : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome then
        let a := Classical.choose hex
        match σ a with
        | some l =>
          some (l, X.g.evenType (X.p.J n) a.1,
            X.firstK (X.hitSet A (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k))
              (X.p.usedBlocks n))
        | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

theorem actualRecordAt_eq (elig : CΩ X ht → (hp X ht).EligMap) (H : X.KeyHist) (ω : CΩ X ht) (R : ℕ)
    (y : OddRole5 n) :
    actualRecordAt X elig H ω R y = recordOf X ht H (arraysOf ω) (fun a => selAt X elig ω R a) y := rfl

/-- `heavyCount` on a given array assignment. -/
def heavyCountOn (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc) (v : EvenRole5 n) (c : CRef X ht) : ℕ :=
  ∑ i : Fin (X.p.typeBlocks n (X.g.evenType (X.p.J n) v.1)),
    if ∃ j ∈ c.2, X.blockIdx _ j = some i then
      (Finset.univ.filter fun e : Fin (X.p.typeSegs n (X.g.evenType (X.p.J n) v.1)) × Fin X.p.q0 =>
        PriorHeavy X H (X.g.evenType (X.p.J n) v.1)
          (A (c.1, X.g.evenType (X.p.J n) v.1) i e.1 e.2)).card
    else 0

/-- The singleton tests of an ID for an even role: prior-heavy fraction and optional hits (05:820–824). -/
def singletonOK (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc) (v : EvenRole5 n) (l : (hp X ht).Loc) : Prop :=
  let c : CRef X ht := (l, X.refSubsetOn H A (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1))
  (heavyCountOn X ht H A v c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) v.1) c.2 : ℝ) ∧
    ∀ k, X.g.optionalKey (X.p.J n) v.1 = some (.inl k) →
      X.p.usedBlocks n ≤ (X.hitSet A (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H.2 k)).card

/-- Failed ID sets at an odd state `b` on levels `j, j+1`: mappings of all neighbouring even states
into prospective IDs with at most `T` IDs whose record fails Step 3 at some role of `b`
(05:826–833). -/
def failSets (H : X.KeyHist) (P : (hp X ht).Loc → Bool) (A : X.ArraysOn (hp X ht).Loc) (b : X.St.Site) (j : ℕ) :
    Finset (Finset (hp X ht).Loc) :=
  ((Finset.univ : Finset (X.St.Site → (hp X ht).Loc)).filter fun μ =>
      (∀ t ∈ X.St.neighbors b, μ t ∈ prosp X ht P (X.St.oneHot t) j ∪ prosp X ht P (X.St.oneHot t) (j + 1)) ∧
      ((X.St.neighbors b).image μ).card ≤ X.p.T n ∧
      ∃ y : OddRole5 n, X.St.stateOf y.1 = b ∧
        X.step3FailOn H (recordOf X ht H A (fun a => some (μ (X.St.stateOf a.1))) y) A).image
    fun μ => (X.St.neighbors b).image μ

/-- Marked IDs at a site-level: the union of the maximal disjoint failure families of the incident
stars on the two level pairs containing it (05:828–833). -/
def marks (H : X.KeyHist) (P : (hp X ht).Loc → Bool) (A : X.ArraysOn (hp X ht).Loc) (s : CubeVertex (hp X ht).d)
    (j : ℕ) : Finset (hp X ht).Loc :=
  (((Finset.univ.filter fun b : X.St.Site => ∃ t ∈ X.St.neighbors b, X.St.oneHot t = s).biUnion fun b =>
    ((Finset.range ((hp X ht).H + 1)).filter fun j' => j' = j ∨ j' + 1 = j).biUnion fun j' =>
      (Lane_sol_s05_centres.markingFamily (failSets X ht H P A b j')).biUnion id)).filter
    fun l => (l.2 : ℕ) = j

/-- Pre-activation eligibility from presence and arrays. -/
def eligOf (H : X.KeyHist) (P : (hp X ht).Loc → Bool) (A : X.ArraysOn (hp X ht).Loc) : (hp X ht).EligMap :=
  fun s j => (prosp X ht P s j).filter fun l =>
    (∀ v : EvenRole5 n, siteOf X v = s → singletonOK X ht H A v l) ∧ l ∉ marks X ht H P A s j

/-- The marking eligibility of L5.1j. -/
def markElig (H : X.KeyHist) (ω : CΩ X ht) : (hp X ht).EligMap := eligOf X ht H (pos ω) (arraysOf ω)


/-- The displayed star tests, with one common definition for both height truncations
(05:869–894). Step 1 belongs to the fixed base; all other tests use the replaced keys and arrays. -/
def LocalValidAt (ht : HDParams) (elig : X.KeyHist → CΩ X ht → (hp X ht).EligMap)
    (H : X.KeyHist) (ω : CΩ X ht) (R : ℕ) (y : OddRole5 n) : Prop :=
  let r := actualRecordAt X (elig H) H ω R y
  X.baseLaw.w H.1 ≠ 0 ∧ X.Step1Pass H.1 ∧
  (∀ a ∈ evenNbrs y, (selAt X (elig H) ω R a).isSome) ∧
  (∀ a ∈ evenNbrs y, ∀ j : Fin ((hp X ht).H + 1),
    ((Finset.univ.filter fun u : CubeVertex (hp X ht).d =>
      pos ω (u, j) = true ∧ _root_.hammingDist u (siteOf X a) ≤ (hp X ht).r).card : ℝ) ≤ 2 * (hp X ht).lam) ∧
  ((evenNbrs y).image fun a => selAt X (elig H) ω R a).card ≤ X.p.T n ∧
  (∀ a ∈ evenNbrs y, ∀ l k, selAt X (elig H) ω R a = some l →
    X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
    X.p.usedBlocks n ≤ (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card) ∧
  (∀ a ∈ evenNbrs y, ∀ l, selAt X (elig H) ω R a = some l →
    let c := (l, refSubset X H ω a l)
    (heavyCount X H ω a c : ℝ) ≤ X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) c.2 : ℝ)) ∧
  (∀ c ∈ r.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) ∧
  0 < X.step3PostOn H r (arraysOf ω) none (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
  X.candGateOn H r (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
  ¬ X.step3FailOn H r (arraysOf ω)


end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

theorem recordOf_congr (H H' : X.KeyHist) (A A' : X.ArraysOn (hp X ht).Loc)
    (σ σ' : EvenRole5 n → Option (hp X ht).Loc) (y : OddRole5 n)
    (hσ : ∀ a ∈ evenNbrs y, σ a = σ' a)
    (hA : ∀ a ∈ evenNbrs y, ∀ l, A (l, X.g.evenType (X.p.J n) a.1) =
      A' (l, X.g.evenType (X.p.J n) a.1))
    (htarget : H.2 (X.g.roleKey (X.p.J n) y.1) = H'.2 (X.g.roleKey (X.p.J n) y.1)) :
    recordOf X ht H A σ y = recordOf X ht H' A' σ' y := by
  have hobs : (evenNbrs y).biUnion (fun a => match σ a with
      | some l => {(l, X.g.evenType (X.p.J n) a.1)} | none => ∅) =
      (evenNbrs y).biUnion (fun a => match σ' a with
      | some l => {(l, X.g.evenType (X.p.J n) a.1)} | none => ∅) := by
    apply Finset.biUnion_congr rfl
    intro a ha
    rw [hσ a ha]
  have href : (evenNbrs y).biUnion (fun a => match σ a with
      | some l => if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
          {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
      | none => ∅) =
      (evenNbrs y).biUnion (fun a => match σ' a with
      | some l => if X.g.roleKey (X.p.J n) y.1 ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
          (X.g.roleKey (X.p.J n) y.1).isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome then
          {(l, X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)} else ∅
      | none => ∅) := by
    apply Finset.biUnion_congr rfl
    intro a ha
    rw [hσ a ha]
  dsimp only [recordOf]
  rw [hobs, href]
  congr 1
  split
  · next k hk =>
      have ht' : X.lowCol H.2 k = X.lowCol H'.2 k := by
        have he := htarget
        rw [hk] at he
        exact congrFun he ⟨0, by simp [colLen5]⟩
      have hex : (∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome) ↔
          ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ' a).isSome := by
        constructor <;> rintro ⟨a, ha, htype, hs⟩
        · exact ⟨a, ha, htype, (hσ a ha) ▸ hs⟩
        · exact ⟨a, ha, htype, (hσ a ha).symm ▸ hs⟩
      by_cases hh : ∃ a ∈ evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none ∧ (σ a).isSome
      · have hh' := hex.mp hh
        rw [dif_pos hh, dif_pos hh']
        have ha := (Classical.choose_spec hh).1
        have heq : Classical.choose hh = Classical.choose hh' := by
          congr 1
          exact funext fun a => propext (by
            by_cases ha : a ∈ evenNbrs y
            · simp only [ha, true_and, hσ a ha]
            · simp [ha])
        rw [← heq, ← hσ _ ha]
        cases hs : σ (Classical.choose hh) with
        | none => rfl
        | some l =>
          dsimp only
          have hhit : X.hitSet A (l, X.g.evenType (X.p.J n) (Classical.choose hh).1) (X.lowCol H.2 k) =
              X.hitSet A' (l, X.g.evenType (X.p.J n) (Classical.choose hh).1) (X.lowCol H'.2 k) := by
            simp only [Setup5.hitSet, hA _ ha l, ht']
          rw [hhit]
      · rw [dif_neg hh, dif_neg (mt hex.mpr hh)]
  · rfl

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

theorem recordOf_obs_type (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc)
    (σ : EvenRole5 n → Option (hp X ht).Loc) (y : OddRole5 n) (c)
    (hc : c ∈ (recordOf X ht H A σ y).2.1) :
    ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1 := by
  obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
  cases hs : σ a with
  | none => simp [hs] at hc
  | some l =>
    have he : c = (l, X.g.evenType (X.p.J n) a.1) := by simpa [hs] using hc
    exact ⟨a, ha, congrArg Prod.snd he⟩

theorem recordOf_ref_type (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc)
    (σ : EvenRole5 n → Option (hp X ht).Loc) (y : OddRole5 n) (c)
    (hc : c ∈ (recordOf X ht H A σ y).2.2.1) :
    ∃ a ∈ evenNbrs y, c.2.1 = X.g.evenType (X.p.J n) a.1 ∧
      c.2.2 = X.g.optionalKey (X.p.J n) a.1 := by
  obtain ⟨a, ha, hc⟩ := Finset.mem_biUnion.mp hc
  cases hs : σ a with
  | none => simp [hs] at hc
  | some l =>
    simp only [hs] at hc
    split_ifs at hc with hh
    · have he := Finset.mem_singleton.mp hc
      exact ⟨a, ha, congrArg (fun c => c.2.1) he, congrArg (fun c => c.2.2) he⟩
    · simp at hc

theorem recordOf_mask_type (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc)
    (σ : EvenRole5 n → Option (hp X ht).Loc) (y : OddRole5 n) (c : (hp X ht).Loc × X.Ty) (M : Finset (Fin X.blockBound))
    (hc : (recordOf X ht H A σ y).2.2.2 = some (c.1, c.2, M)) :
    ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1 := by
  dsimp only [recordOf] at hc
  split at hc
  · split_ifs at hc with hh
    · have ha := (Classical.choose_spec hh).1
      cases hs : σ (Classical.choose hh) with
      | none => simp [hs] at hc
      | some l =>
        simp only [hs, Option.some.injEq, Prod.mk.injEq] at hc
        exact ⟨Classical.choose hh, ha, hc.2.1.symm⟩
  · simp at hc

theorem recordOf_data (H : X.KeyHist) (A : X.ArraysOn (hp X ht).Loc)
    (σ : EvenRole5 n → Option (hp X ht).Loc) (y : OddRole5 n)
    {t : CubeVertex (X.p.m n)} {q : ℕ}
    (htarget : within X t q (X.g.roleKey (X.p.J n) y.1))
    (htypes : ∀ a ∈ evenNbrs y, ∀ ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1, within X t q ℓ)
    (hopts : ∀ a ∈ evenNbrs y, ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) a.1).toFinset, within X t q ℓ) :
    (∀ ℓ ∈ recordKeys X (recordOf X ht H A σ y), within X t q ℓ) ∧
    (∀ c ∈ recordArrays X (recordOf X ht H A σ y),
      ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1) := by
  have har : ∀ c ∈ recordArrays X (recordOf X ht H A σ y),
      ∃ a ∈ evenNbrs y, c.2 = X.g.evenType (X.p.J n) a.1 := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hc | hc
      · exact recordOf_obs_type X ht H A σ y c hc
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨a, ha, htype, hopt⟩ := recordOf_ref_type X ht H A σ y d hd
        exact ⟨a, ha, htype⟩
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
      have hd' : (recordOf X ht H A σ y).2.2.2 = some d := by simpa using hd
      exact recordOf_mask_type X ht H A σ y (d.1, d.2.1) d.2.2 hd'
  refine ⟨?_, har⟩
  intro ℓ hℓ
  rcases Finset.mem_insert.mp hℓ with hℓ | hℓ
  · exact hℓ ▸ htarget
  · rcases Finset.mem_union.mp hℓ with hℓ | hℓ
    · obtain ⟨c, hc, hℓ⟩ := Finset.mem_biUnion.mp hℓ
      obtain ⟨a, ha, he⟩ := har c hc
      exact htypes a ha ℓ (he ▸ hℓ)
    · obtain ⟨c, hc, hℓ⟩ := Finset.mem_biUnion.mp hℓ
      obtain ⟨a, ha, htype, hopt⟩ := recordOf_ref_type X ht H A σ y c hc
      exact hopts a ha ℓ (hopt ▸ hℓ)

theorem incident_sign (v : EvenRole5 n) (b : X.St.Site)
    (hv : X.St.stateOf v.1 ∈ X.St.neighbors b) (y : OddRole5 n) (hy : X.St.stateOf y.1 = b) :
    _root_.hammingDist (X.g.sign y.1) (X.g.sign v.1) ≤ 1 := by
  obtain ⟨x, z, hx, hz, hadj⟩ := (X.St.mem_neighbors b (X.St.stateOf v.1)).mp hv
  have hxs := (X.St.state_determines x y.1 (hx.trans hy.symm)).2.1
  have hzs := (X.St.state_determines z v.1 hz).2.1
  have h := adjacent_sign X z x hadj.symm
  simpa only [hxs, hzs] using h

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

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

theorem singleton_congr (H H' : X.KeyHist) (A A' : X.ArraysOn (hp X ht).Loc)
    (v : EvenRole5 n) (l : (hp X ht).Loc) (hb : H.1 = H'.1)
    (hc : ∀ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, H.2 ℓ = H'.2 ℓ)
    (ho : ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) v.1).toFinset, H.2 ℓ = H'.2 ℓ)
    (ha : A (l, X.g.evenType (X.p.J n) v.1) = A' (l, X.g.evenType (X.p.J n) v.1)) :
    singletonOK X ht H A v l = singletonOK X ht H' A' v l := by
  have hlaw : X.blockLaw H (X.g.evenType (X.p.J n) v.1) =
      X.blockLaw H' (X.g.evenType (X.p.J n) v.1) := blockLawOn_ext X H H' _ _ hb hc
  have havg (x) : avgMarg X H (X.g.evenType (X.p.J n) v.1) x =
      avgMarg X H' (X.g.evenType (X.p.J n) v.1) x := by simp only [avgMarg, hlaw]
  have hsub := refSubset_ext X H H' A A' (l, X.g.evenType (X.p.J n) v.1)
    (X.g.optionalKey (X.p.J n) v.1) ha ho
  have hh : heavyCountOn X ht H A v (l, X.refSubsetOn H A
      (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)) =
      heavyCountOn X ht H' A' v (l, X.refSubsetOn H' A'
      (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1)) := by
    simp only [heavyCountOn, hsub, ha, PriorHeavy, havg]
    rfl
  have hhit (k) (hk : X.g.optionalKey (X.p.J n) v.1 = some (.inl k)) :
      X.hitSet A (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H.2 k) =
      X.hitSet A' (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H'.2 k) := by
    have he := ho (.inl k) (by simp [hk])
    simp only [Setup5.hitSet, Setup5.lowCol, ha, he]
    rfl
  dsimp only [singletonOK]
  rw [hh, hsub]
  congr 1
  apply propext
  constructor <;> intro h k hk
  · simpa only [hhit k hk] using h k hk
  · simpa only [hhit k hk] using h k hk

theorem neighbor_sign_bound (y : OddRole5 n) (v : EvenRole5 n) (hv : v ∈ evenNbrs y)
    (t : CubeVertex (X.p.m n)) (q : ℕ) (hy : _root_.hammingDist (X.g.sign y.1) t ≤ q) :
    _root_.hammingDist (X.g.sign v.1) t ≤ q + 1 := by
  have h1 := adjacent_sign X y.1 v.1 ((Finset.mem_filter.mp hv).2.symm)
  have h2 := _root_.hammingDist_triangle (X.g.sign v.1) (X.g.sign y.1) t
  omega

theorem failSets_congr (H H' : X.KeyHist) (P : (hp X ht).Loc → Bool)
    (A A' : X.ArraysOn (hp X ht).Loc) (b : X.St.Site) (j : ℕ)
    (v : EvenRole5 n) (hv : X.St.stateOf v.1 ∈ X.St.neighbors b)
    {t : CubeVertex (X.p.m n)} {q₀ q : ℕ}
    (hnear : _root_.hammingDist (X.g.sign v.1) t ≤ q₀) (hq : q₀ + 3 ≤ q)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X t q ℓ → H.2 ℓ = H'.2 ℓ)
    (ha : ∀ c, c.2 ∈ localTypes X t q → A c = A' c) :
    failSets X ht H P A b j = failSets X ht H' P A' b j := by
  have hynear (y : OddRole5 n) (hy : X.St.stateOf y.1 = b) :
      _root_.hammingDist (X.g.sign y.1) t ≤ q₀ + 1 := by
    have h1 := incident_sign X v b hv y hy
    have h2 := _root_.hammingDist_triangle (X.g.sign y.1) (X.g.sign v.1) t
    omega
  have hfail (μ : X.St.Site → (hp X ht).Loc) (y : OddRole5 n) (hy : X.St.stateOf y.1 = b) :
      X.step3FailOn H (recordOf X ht H A (fun a => some (μ (X.St.stateOf a.1))) y) A =
      X.step3FailOn H' (recordOf X ht H' A' (fun a => some (μ (X.St.stateOf a.1))) y) A' := by
    have hty (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        X.g.evenType (X.p.J n) a.1 ∈ localTypes X t q := by
      simp only [localTypes, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ℓ hℓ
      have h := type_keys_within X a.1 t (q₀ + 2)
        (neighbor_sign_bound X y a ha t (q₀ + 1) (hynear y hy)) ℓ hℓ
      exact within_mono X (by omega) h
    have htarg : within X t q (X.g.roleKey (X.p.J n) y.1) := by
      have h := role_key_within X y.1 t (q₀ + 1) (hynear y hy)
      exact within_mono X (by omega) h
    have hop (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
        ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) a.1).toFinset, within X t q ℓ := by
      intro ℓ hℓ
      have h := optional_key_within X a.1 t (q₀ + 2)
        (neighbor_sign_bound X y a ha t (q₀ + 1) (hynear y hy)) ℓ hℓ
      exact within_mono X (by omega) h
    have hr := recordOf_congr X ht H H' A A'
      (fun a => some (μ (X.St.stateOf a.1))) (fun a => some (μ (X.St.stateOf a.1))) y (fun _ _ => rfl)
      (fun a ha' l => ha _ (hty a ha')) (hc _ htarg)
    rw [← hr]
    have hd := recordOf_data X ht H A (fun a => some (μ (X.St.stateOf a.1))) y
      htarg (fun a ha' ℓ hℓ => (Finset.mem_filter.mp (hty a ha')).2 ℓ hℓ) hop
    exact (record_tests_ext X H H' _ A A' hb (fun ℓ hℓ => hc ℓ (hd.1 ℓ hℓ))
      (fun c hc' => by
        obtain ⟨a, ha', he⟩ := hd.2 c hc'
        exact ha c (he.symm ▸ hty a ha'))).1
  unfold failSets
  congr 1
  apply Finset.filter_congr
  intro μ hμ
  apply and_congr_right
  intro hμ'
  apply and_congr_right
  intro hcard
  exact exists_congr fun y => and_congr_right (fun hy => by rw [hfail μ y hy])

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

theorem eligOf_congr (H H' : X.KeyHist) (P : (hp X ht).Loc → Bool)
    (A A' : X.ArraysOn (hp X ht).Loc) (v : EvenRole5 n)
    {t : CubeVertex (X.p.m n)} {q₀ q : ℕ}
    (hnear : _root_.hammingDist (X.g.sign v.1) t ≤ q₀) (hq : q₀ + 3 ≤ q)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X t q ℓ → H.2 ℓ = H'.2 ℓ)
    (ha : ∀ c, c.2 ∈ localTypes X t q → A c = A' c) :
    eligOf X ht H P A (siteOf X v) = eligOf X ht H' P A' (siteOf X v) := by
  have hsame (w : EvenRole5 n) (hw : siteOf X w = siteOf X v) :
      _root_.hammingDist (X.g.sign w.1) t ≤ q₀ := by
    have he : X.St.stateOf w.1 = X.St.stateOf v.1 := X.St.oneHot_injective hw
    rw [(X.St.state_determines w.1 v.1 he).2.1]
    exact hnear
  have hs (w : EvenRole5 n) (hw : siteOf X w = siteOf X v) (l) :
      singletonOK X ht H A w l = singletonOK X ht H' A' w l := by
    have hk := type_keys_within X w.1 t q₀ (hsame w hw)
    have hm : X.g.evenType (X.p.J n) w.1 ∈ localTypes X t q := by
      simp only [localTypes, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun ℓ hℓ => within_mono X (by omega) (hk ℓ hℓ)
    exact singleton_congr X ht H H' A A' w l hb
      (fun ℓ hℓ => hc ℓ (within_mono X (by omega) (hk ℓ hℓ)))
      (fun ℓ hℓ => hc ℓ (within_mono X (by omega)
        (optional_key_within X w.1 t q₀ (hsame w hw) ℓ hℓ))) (ha _ hm)
  have hmark (j : ℕ) : marks X ht H P A (siteOf X v) j = marks X ht H' P A' (siteOf X v) j := by
    unfold marks
    apply congrArg (fun S : Finset (hp X ht).Loc => S.filter (fun l => (l.2 : ℕ) = j))
    apply Finset.biUnion_congr rfl
    intro b hb'
    obtain ⟨u, hu, he⟩ := (Finset.mem_filter.mp hb').2
    have he' : u = X.St.stateOf v.1 := X.St.oneHot_injective he
    have hv : X.St.stateOf v.1 ∈ X.St.neighbors b := he' ▸ hu
    apply Finset.biUnion_congr rfl
    intro j' hj'
    exact congrArg (fun F : Finset (Finset (hp X ht).Loc) =>
      (Lane_sol_s05_centres.markingFamily F).biUnion id)
        (failSets_congr X ht H H' P A A' b j' v hv hnear hq hb hc ha)
  funext j
  unfold eligOf
  apply Finset.filter_congr
  intro l hl
  rw [hmark]
  apply and_congr_left
  intro hnot
  exact forall_congr' fun w => imp_congr_right (fun hw => by rw [hs w hw l])

def maskArrays (U : Finset X.Ty) (A : ∀ K : X.Ty, X.Array K) : ∀ K : X.Ty, X.Array K :=
  fun K => if K ∈ U then A K else fun _ => X.fallbackBlock K

def maskTie (U : Finset X.Ty) (v : (hp X ht).TiePerm × (∀ K : X.Ty, X.Array K)) :=
  (v.1, maskArrays X U v.2)

def maskAct (U : Finset X.Ty) (v : Bool × (hp X ht).TiePerm × (∀ K : X.Ty, X.Array K)) :=
  (v.1, maskTie X ht U v.2)

def maskVal (U : Finset X.Ty) (v : CVal X ht) : CVal X ht :=
  (v.1, maskAct X ht U v.2)

def maskΩ (U : Finset X.Ty) (ω : CΩ X ht) : CΩ X ht := fun l => maskVal X ht U (ω l)

theorem masked_law (H H' : X.KeyHist) (t : CubeVertex (X.p.m n)) (q : ℕ)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X t q ℓ → H.2 ℓ = H'.2 ℓ) :
    FinProb.map (centreLaw X ht H) (maskΩ X ht (localTypes X t q)) =
    FinProb.map (centreLaw X ht H') (maskΩ X ht (localTypes X t q)) := by
  unfold centreLaw maskΩ
  rw [map_pi, map_pi]
  congr 1
  funext l
  unfold maskVal
  rw [map_prod_snd, map_prod_snd]
  congr 1
  unfold maskAct
  rw [map_prod_snd, map_prod_snd]
  congr 1
  unfold maskTie
  rw [map_prod_snd, map_prod_snd]
  congr 1
  unfold maskArrays
  rw [map_pi _ (fun K (A : X.Array K) => if K ∈ localTypes X t q then A else fun _ => X.fallbackBlock K),
    map_pi _ (fun K (A : X.Array K) => if K ∈ localTypes X t q then A else fun _ => X.fallbackBlock K)]
  congr 1
  funext K
  by_cases hK : K ∈ localTypes X t q
  · simp only [hK, if_true]
    have hcol : ∀ ℓ ∈ K.2.1, H.2 ℓ = H'.2 ℓ :=
      fun ℓ hℓ => hc ℓ ((Finset.mem_filter.mp hK).2 ℓ hℓ)
    have hlaw : X.blockLaw H K = X.blockLaw H' K := blockLawOn_ext X H H' K K.2.1 hb hcol
    rw [hlaw]
  · simp only [hK, if_false]
    exact map_const _ _ _

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

theorem selections_congr (H H' : X.KeyHist) (ω ω' : CΩ X ht) (y : OddRole5 n) (R q : ℕ)
    (hq : R + 4 ≤ q) (hb : H.1 = H'.1)
    (hc : ∀ ℓ, within X (X.g.sign y.1) q ℓ → H.2 ℓ = H'.2 ℓ)
    (hp' : pos ω = pos ω') (ha' : act ω = act ω') (ht' : tie ω = tie ω')
    (hA : ∀ c, c.2 ∈ localTypes X (X.g.sign y.1) q → arraysOf ω c = arraysOf ω' c) :
    ∀ a ∈ evenNbrs y, selAt X (markElig X ht H) ω R a = selAt X (markElig X ht H') ω' R a := by
  intro a ha
  unfold selAt
  rw [hp', ha', ht']
  apply selection_congr
  · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  · intro u hu hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    simp only [siteOf] at hd
    have hs : _root_.hammingDist (X.g.sign v.1) (X.g.sign a.1) ≤ R :=
      (X.St.sign_distance v.1 a.1).trans hd
    have hadj := neighbor_sign_bound X y a ha (X.g.sign y.1) 0 (by simp)
    have htriangle := _root_.hammingDist_triangle (X.g.sign v.1) (X.g.sign a.1) (X.g.sign y.1)
    have hnear : _root_.hammingDist (X.g.sign v.1) (X.g.sign y.1) ≤ R + 1 := by omega
    change eligOf X ht H (pos ω) (arraysOf ω) (siteOf X v) =
      eligOf X ht H' (pos ω') (arraysOf ω') (siteOf X v)
    rw [hp']
    exact eligOf_congr X ht H H' (pos ω') _ _ v hnear (by omega) hb hc hA

theorem heavyCount_congr (H H' : X.KeyHist) (ω ω' : CΩ X ht) (v : EvenRole5 n)
    (l : (hp X ht).Loc) (hb : H.1 = H'.1)
    (hc : ∀ ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1, H.2 ℓ = H'.2 ℓ)
    (ho : ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) v.1).toFinset, H.2 ℓ = H'.2 ℓ)
    (ha : arraysOf ω (l, X.g.evenType (X.p.J n) v.1) =
      arraysOf ω' (l, X.g.evenType (X.p.J n) v.1)) :
    refSubset X H ω v l = refSubset X H' ω' v l ∧
      heavyCount X H ω v (l, refSubset X H ω v l) =
        heavyCount X H' ω' v (l, refSubset X H' ω' v l) := by
  have hsub := refSubset_ext X H H' (arraysOf ω) (arraysOf ω')
    (l, X.g.evenType (X.p.J n) v.1) (X.g.optionalKey (X.p.J n) v.1) ha ho
  refine ⟨hsub, ?_⟩
  have hlaw : X.blockLaw H (X.g.evenType (X.p.J n) v.1) =
      X.blockLaw H' (X.g.evenType (X.p.J n) v.1) :=
    blockLawOn_ext X H H' (X.g.evenType (X.p.J n) v.1) _ hb hc
  have havg (x) : avgMarg X H (X.g.evenType (X.p.J n) v.1) x =
      avgMarg X H' (X.g.evenType (X.p.J n) v.1) x := by simp only [avgMarg, hlaw]
  change heavyCountOn X ht H (arraysOf ω) v _ = heavyCountOn X ht H' (arraysOf ω') v _
  simp only [heavyCountOn, refSubset, hsub, ha, PriorHeavy, havg]
  rfl

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

theorem presentation_event_congr (H H' : X.KeyHist) (ω ω' : CΩ X ht)
    (y : OddRole5 n) (R q : ℕ) (r : X.RecordOn (hp X ht).Loc) (A : X.ArraysOn (hp X ht).Loc)
    (hq : R + 4 ≤ q) (hb : H.1 = H'.1)
    (hc : ∀ ℓ, within X (X.g.sign y.1) q ℓ → H.2 ℓ = H'.2 ℓ)
    (hpos : pos ω = pos ω') (hact : act ω = act ω') (htie : tie ω = tie ω')
    (hA : ∀ c, c.2 ∈ localTypes X (X.g.sign y.1) q → arraysOf ω c = arraysOf ω' c) :
    (LocalValidAt X ht (markElig X ht) H ω R y ∧
      actualRecordAt X (markElig X ht H) H ω R y = r ∧ ∀ c ∈ r.2.1, arraysOf ω c = A c) =
    (LocalValidAt X ht (markElig X ht) H' ω' R y ∧
      actualRecordAt X (markElig X ht H') H' ω' R y = r ∧ ∀ c ∈ r.2.1, arraysOf ω' c = A c) := by
  let σ := fun a => selAt X (markElig X ht H) ω R a
  let σ' := fun a => selAt X (markElig X ht H') ω' R a
  let r₀ := recordOf X ht H (arraysOf ω) σ y
  let r₁ := recordOf X ht H' (arraysOf ω') σ' y
  have hσ : ∀ a ∈ evenNbrs y, σ a = σ' a := selections_congr X ht H H' ω ω' y R q hq hb hc hpos hact htie hA
  have hnear (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      _root_.hammingDist (X.g.sign a.1) (X.g.sign y.1) ≤ 1 :=
    neighbor_sign_bound X y a ha _ 0 (by simp)
  have htypes (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      ∀ ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1, within X (X.g.sign y.1) q ℓ :=
    fun ℓ hℓ => within_mono X (by omega) (type_keys_within X a.1 _ 1 (hnear a ha) ℓ hℓ)
  have hopts (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      ∀ ℓ ∈ (X.g.optionalKey (X.p.J n) a.1).toFinset, within X (X.g.sign y.1) q ℓ :=
    fun ℓ hℓ => within_mono X (by omega) (optional_key_within X a.1 _ 1 (hnear a ha) ℓ hℓ)
  have htarg : within X (X.g.sign y.1) q (X.g.roleKey (X.p.J n) y.1) :=
    role_key_within X y.1 _ q (by simp)
  have hty (a : EvenRole5 n) (ha : a ∈ evenNbrs y) :
      X.g.evenType (X.p.J n) a.1 ∈ localTypes X (X.g.sign y.1) q := by
    simp only [localTypes, Finset.mem_filter, Finset.mem_univ, true_and]
    exact htypes a ha
  have harole (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l) :
      arraysOf ω (l, X.g.evenType (X.p.J n) a.1) =
      arraysOf ω' (l, X.g.evenType (X.p.J n) a.1) := hA _ (hty a ha)
  have hr : r₀ = r₁ := recordOf_congr X ht H H' _ _ σ σ' y hσ harole (hc _ htarg)
  have hd := recordOf_data X ht H (arraysOf ω) σ y htarg htypes hopts
  have harr : ∀ c ∈ recordArrays X r₀, arraysOf ω c = arraysOf ω' c := by
    intro c hc'
    obtain ⟨a, ha, he⟩ := hd.2 c hc'
    exact hA c (he.symm ▸ hty a ha)
  have htests := record_tests_ext X H H' r₀ (arraysOf ω) (arraysOf ω') hb
    (fun ℓ hℓ => hc ℓ (hd.1 ℓ hℓ)) harr
  have hchoose : (∀ a ∈ evenNbrs y, (σ a).isSome) = (∀ a ∈ evenNbrs y, (σ' a).isSome) := by
    apply propext
    exact forall_congr' fun a => imp_congr_right (fun ha => by rw [hσ a ha])
  have hcard : ((evenNbrs y).image σ).card = ((evenNbrs y).image σ').card := by
    congr 1
    exact Finset.image_congr hσ
  have hhit (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l k)
      (hk : X.g.optionalKey (X.p.J n) a.1 = some (.inl k)) :
      X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k) =
      X.hitSet (arraysOf ω') (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H'.2 k) := by
    have he := hc (.inl k) (hopts a ha _ (by simp [hk]))
    simp only [Setup5.hitSet, harole a ha l, Setup5.lowCol, he]
    rfl
  have hhits :
      (∀ a ∈ evenNbrs y, ∀ l k, σ a = some l → X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
        X.p.usedBlocks n ≤ (X.hitSet (arraysOf ω) (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H.2 k)).card) =
      (∀ a ∈ evenNbrs y, ∀ l k, σ' a = some l → X.g.optionalKey (X.p.J n) a.1 = some (.inl k) →
        X.p.usedBlocks n ≤ (X.hitSet (arraysOf ω') (l, X.g.evenType (X.p.J n) a.1) (X.lowCol H'.2 k)).card) := by
    apply propext
    exact forall_congr' fun a => imp_congr_right fun ha => forall_congr' fun l => forall_congr' fun k => by
      rw [hσ a ha]
      exact imp_congr_right fun hs => imp_congr_right fun hk => by rw [hhit a ha l k hk]
  have hheavy (a : EvenRole5 n) (ha : a ∈ evenNbrs y) (l) :=
    heavyCount_congr X ht H H' ω ω' a l hb
      (fun ℓ hℓ => hc ℓ (htypes a ha ℓ hℓ)) (fun ℓ hℓ => hc ℓ (hopts a ha ℓ hℓ)) (harole a ha l)
  have hheavies :
      (∀ a ∈ evenNbrs y, ∀ l, σ a = some l →
        (heavyCount X H ω a (l, refSubset X H ω a l) : ℝ) ≤
          X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) (refSubset X H ω a l) : ℝ)) =
      (∀ a ∈ evenNbrs y, ∀ l, σ' a = some l →
        (heavyCount X H' ω' a (l, refSubset X H' ω' a l) : ℝ) ≤
          X.p.nu0 * (X.refLen (X.g.evenType (X.p.J n) a.1) (refSubset X H' ω' a l) : ℝ)) := by
    apply propext
    exact forall_congr' fun a => imp_congr_right fun ha => forall_congr' fun l => by
      rw [hσ a ha, (hheavy a ha l).2, (hheavy a ha l).1]
  have hobsarr : ∀ c ∈ r₀.2.1, arraysOf ω c = arraysOf ω' c := by
    intro c hc'
    apply harr c
    simp only [recordArrays, Finset.mem_union]
    exact Or.inl (Or.inl hc')
  have hraw : (∀ c ∈ r₀.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) =
      (∀ c ∈ r₀.2.1, ∀ i, X.blockWeight H' c.2 c.2.2.1 (arraysOf ω' c i) ≠ 0) := by
    apply propext
    apply forall_congr'
    intro c
    apply imp_congr_right
    intro hco
    apply forall_congr'
    intro i
    have hk : ∀ ℓ ∈ c.2.2.1, H.2 ℓ = H'.2 ℓ := by
      intro ℓ hℓ
      apply hc
      obtain ⟨a, ha, he⟩ := recordOf_obs_type X ht H (arraysOf ω) σ y c hco
      exact htypes a ha ℓ (he ▸ hℓ)
    have hw : X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) =
        X.blockWeight H' c.2 c.2.2.1 (arraysOf ω' c i) := by
      unfold Setup5.blockWeight
      rw [hb, hobsarr c hco]
      congr 1
      exact Finset.prod_congr rfl (fun ℓ hℓ => by rw [hk ℓ hℓ])
    rw [hw]
  have hvalid : LocalValidAt X ht (markElig X ht) H ω R y = LocalValidAt X ht (markElig X ht) H' ω' R y := by
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) = _
    change (X.baseLaw.w H.1 ≠ 0 ∧ X.Step1Pass H.1 ∧
      (∀ a ∈ evenNbrs y, (σ a).isSome) ∧ _ ∧ ((evenNbrs y).image σ).card ≤ X.p.T n ∧
      _ ∧ _ ∧ (∀ c ∈ r₀.2.1, ∀ i, X.blockWeight H c.2 c.2.2.1 (arraysOf ω c i) ≠ 0) ∧
      0 < X.step3PostOn H r₀ (arraysOf ω) none (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      X.candGateOn H r₀ (arraysOf ω) (H.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      ¬ X.step3FailOn H r₀ (arraysOf ω)) = _
    rw [hb, hchoose, hpos, hcard, hhits, hheavies, hraw, htests.1, htests.2.1 none (H.2 (X.g.roleKey (X.p.J n) y.1)),
      htests.2.2 (H.2 (X.g.roleKey (X.p.J n) y.1)), hc _ htarg]
    let tail (d : Finset ((hp X ht).Loc × X.Ty) ×
        Finset ((hp X ht).Loc × X.Ty × Option X.Key) ×
        Option ((hp X ht).Loc × X.Ty × Finset (Fin X.blockBound))) : Prop :=
      (∀ c ∈ d.1, ∀ i, X.blockWeight H' c.2 c.2.2.1 (arraysOf ω' c i) ≠ 0) ∧
      0 < X.step3PostOn H' (X.g.roleKey (X.p.J n) y.1, d) (arraysOf ω') none
        (H'.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      X.candGateOn H' (X.g.roleKey (X.p.J n) y.1, d) (arraysOf ω')
        (H'.2 (X.g.roleKey (X.p.J n) y.1)) ∧
      ¬ X.step3FailOn H' (X.g.roleKey (X.p.J n) y.1, d) (arraysOf ω')
    have htail : tail r₀.2 = tail r₁.2 := congrArg tail (congrArg Prod.snd hr)
    change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ tail r₀.2) =
      (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ tail r₁.2)
    rw [htail]
  change (LocalValidAt X ht (markElig X ht) H ω R y ∧ r₀ = r ∧ _) =
    (LocalValidAt X ht (markElig X ht) H' ω' R y ∧ r₁ = r ∧ _)
  rw [hvalid, ← hr]
  apply propext
  apply and_congr_right
  intro hv
  apply and_congr_right
  intro he
  subst r
  exact forall_congr' fun c => imp_congr_right (fun hco => by rw [hobsarr c hco])

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12.Model
open Classical OAI.HypercubeRamsey Setup5
open scoped BigOperators
noncomputable section
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) (ht : HDParams)

def presentationMass (H : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn (hp X ht).Loc) (A : X.ArraysOn (hp X ht).Loc) : ℝ :=
  (centreLaw X ht H).pr fun ω =>
    LocalValidAt X ht (markElig X ht) H ω ((hp X ht).Rshort (X.p.m n)) y ∧
    actualRecordAt X (markElig X ht H) H ω ((hp X ht).Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = A c

theorem mass_congr (H H' : X.KeyHist) (y : OddRole5 n)
    (r : X.RecordOn (hp X ht).Loc) (A : X.ArraysOn (hp X ht).Loc)
    (q : ℕ) (hq : (hp X ht).Rshort (X.p.m n) + 4 ≤ q)
    (hb : H.1 = H'.1) (hc : ∀ ℓ, within X (X.g.sign y.1) q ℓ → H.2 ℓ = H'.2 ℓ) :
    presentationMass X ht H y r A = presentationMass X ht H' y r A := by
  let U := localTypes X (X.g.sign y.1) q
  let F := fun H ω => LocalValidAt X ht (markElig X ht) H ω ((hp X ht).Rshort (X.p.m n)) y ∧
    actualRecordAt X (markElig X ht H) H ω ((hp X ht).Rshort (X.p.m n)) y = r ∧
    ∀ c ∈ r.2.1, arraysOf ω c = A c
  have hm (H : X.KeyHist) (ω : CΩ X ht) : F H ω = F H (maskΩ X ht U ω) := by
    apply presentation_event_congr X ht H H ω (maskΩ X ht U ω) y _ q r A hq rfl (fun _ _ => rfl)
    · rfl
    · rfl
    · rfl
    · intro c hc
      change arraysOf ω c = if c.2 ∈ U then arraysOf ω c else fun _ => X.fallbackBlock c.2
      rw [if_pos hc]
  have hF : F H = F H' := by
    funext ω
    exact presentation_event_congr X ht H H' ω ω y _ q r A hq hb hc rfl rfl rfl (fun _ _ => rfl)
  change (centreLaw X ht H).pr (F H) = (centreLaw X ht H').pr (F H')
  calc
    (centreLaw X ht H).pr (F H) = (FinProb.map (centreLaw X ht H) (maskΩ X ht U)).pr (F H) := by
      rw [pr_map]
      exact congrArg (fun B : CΩ X ht → Prop => (centreLaw X ht H).pr B) (funext (hm H))
    _ = (FinProb.map (centreLaw X ht H') (maskΩ X ht U)).pr (F H') := by
      rw [masked_law X ht H H' _ q hb hc, hF]
    _ = (centreLaw X ht H').pr (F H') := by
      rw [pr_map]
      exact congrArg (fun B : CΩ X ht → Prop => (centreLaw X ht H').pr B)
        (funext fun ω => (hm H' ω).symm)

theorem mass_local (hD : ht.D = 8) (hm : 1 ≤ X.p.m n)
    (b : X.Base) (hi : X.HighHid) (y : OddRole5 n)
    (r : X.RecordOn (hp X ht).Loc) (A : X.ArraysOn (hp X ht).Loc) :
    FinProb.DependsOn (fun lo => presentationMass X ht (b, X.joinHidden hi lo) y r A)
      (Finset.univ.filter fun k : X.LowIdx =>
        _root_.hammingDist k.2.1 (X.g.sign y.1) ≤ 16 * Nat.sqrt (X.p.m n)) := by
  intro lo lo' hlo
  have hs : 1 ≤ Nat.sqrt (X.p.m n) := by
    exact Nat.succ_le_of_lt (Nat.sqrt_pos.mpr (by omega))
  apply mass_congr X ht _ _ y r A (16 * Nat.sqrt (X.p.m n))
  · simp only [HDParams.Rshort, hp, hD]
    omega
  · rfl
  · intro ℓ hℓ
    cases ℓ with
    | inr i => rfl
    | inl k => exact hlo k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓ⟩)

end
end HypercubeRamsey.Lane_sol_s05_j12.Model

namespace HypercubeRamsey.Lane_sol_s05_j12

open Lean Elab Tactic

/-- Expose the frozen height-parameter wrapper while elaborating the bridge, then restore
its original reducibility settings. Kernel checking still uses the original definition. -/
elab "j12_reduce_height" t:tacticSeq : tactic => do
  let saved ← getEnv
  let aliases : Array String := #[
    "HypercubeRamsey.Setup5.HeightChoice5.hp",
    "HypercubeRamsey.Setup5.CΩ",
    "HypercubeRamsey.Setup5.CVal",
    "HypercubeRamsey.Setup5.arraysOf",
    "HypercubeRamsey.Setup5.arr",
    "HypercubeRamsey.Setup5.pos",
    "HypercubeRamsey.Setup5.act",
    "HypercubeRamsey.Setup5.tie",
    "HypercubeRamsey.Setup5.centreLaw",
    "HypercubeRamsey.Setup5.LocalValidAt",
    "HypercubeRamsey.Setup5.actualRecordAt",
    "HypercubeRamsey.Setup5.refSubset",
    "HypercubeRamsey.Setup5.heavyCount",
    "HypercubeRamsey.Setup5.avgMarg",
    "HypercubeRamsey.Setup5.PriorHeavy",
    "HypercubeRamsey.Setup5.selAt",
    "HypercubeRamsey.Setup5.sites",
    "HypercubeRamsey.Setup5.siteOf",
    "HypercubeRamsey.Setup5.Lane_opus_s05.recordOf",
    "HypercubeRamsey.Setup5.Lane_opus_s05.heavyCountOn",
    "HypercubeRamsey.Setup5.Lane_opus_s05.singletonOK",
    "HypercubeRamsey.Setup5.Lane_opus_s05.prosp",
    "HypercubeRamsey.Setup5.Lane_opus_s05.failSets",
    "HypercubeRamsey.Setup5.Lane_opus_s05.marks",
    "HypercubeRamsey.Setup5.Lane_opus_s05.eligOf",
    "HypercubeRamsey.Setup5.Lane_opus_s05.markElig",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.CΩ",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.CVal",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.arraysOf",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.arr",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.pos",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.act",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.tie",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.centreLaw",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.LocalValidAt",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.actualRecordAt",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.refSubset",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.heavyCount",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.avgMarg",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.PriorHeavy",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.selAt",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.sites",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.siteOf",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.recordOf",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.heavyCountOn",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.singletonOK",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.prosp",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.failSets",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.marks",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.eligOf",
    "HypercubeRamsey.Lane_sol_s05_j12.Model.markElig"]
  for aliasName in aliases do
    let n := aliasName.toName
    if (← getEnv).contains n then
      if (← Lean.getReducibilityStatus n) == .semireducible then
        modifyEnv fun env => Lean.reducibilityExtraExt.addCore env (n, .implicitReducible) .local .anonymous
  Lean.Meta.resetCache
  try
    evalTactic t
  finally
    setEnv saved
    Lean.Meta.resetCache

end HypercubeRamsey.Lane_sol_s05_j12
