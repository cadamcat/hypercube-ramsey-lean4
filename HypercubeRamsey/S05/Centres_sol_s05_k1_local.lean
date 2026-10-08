import HypercubeRamsey.S05.Centres_sol_s05_k1_lookup
import HypercubeRamsey.S05.Centres_sol_s05_k1_height

namespace HypercubeRamsey.Lane_sol_s05_k1

open Classical OAI.HypercubeRamsey

noncomputable section
set_option maxHeartbeats 400000

theorem cube_hamming_eq {d : ℕ} (u v : CubeVertex d) :
    HypercubeRamsey.hammingDist u v = _root_.hammingDist u v := by
  unfold HypercubeRamsey.hammingDist _root_.hammingDist
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]

theorem cube_hamming_eq_with {d : ℕ} (inst : Fintype (Fin d))
    (e : ∀ _i : Fin d, DecidableEq Bool) (u v : CubeVertex d) :
    HypercubeRamsey.hammingDist u v = @ _root_.hammingDist (Fin d) (fun _ => Bool) inst e u v := by
  unfold HypercubeRamsey.hammingDist _root_.hammingDist
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem selectionAt_local (p : HDParams) (Sites : p.Sites)
    (P A P' A' : p.Loc → Bool) (E E' : p.EligMap) (τ τ' : p.Ties)
    (v : CubeVertex p.d) (R : ℕ)
    (hE : ∀ s, _root_.hammingDist s v ≤ R → ∀ j, E s j = E' s j)
    (hshape : ∀ s, _root_.hammingDist s v ≤ R → ∀ j l, l ∈ E s j →
      _root_.hammingDist l.1 s ≤ p.r)
    (hP : ∀ l, _root_.hammingDist l.1 v ≤ R + p.r + p.D → P l = P' l)
    (hA : ∀ l, _root_.hammingDist l.1 v ≤ R + p.r + p.D → A l = A' l)
    (hτ : ∀ j, τ (v, j) = τ' (v, j)) :
    p.selectionAt Sites P A E τ R v = p.selectionAt Sites P' A' E' τ' R v := by
  have hbad : ∀ s, _root_.hammingDist s v ≤ R → ∀ j,
      p.Bad P A E s j ↔ p.Bad P' A' E' s j := by
    intro s hs j
    have he := hE s hs j
    have ha : ∀ l ∈ E s j, A l = A' l := by
      intro l hl
      apply hA l
      have hd := (_root_.hammingDist_triangle l.1 s v).trans
        (Nat.add_le_add (hshape s hs j l hl) hs)
      omega
    have hactive : (∀ l ∈ E s j, A l = false) ↔ (∀ l ∈ E' s j, A' l = false) := by
      rw [← he]
      constructor
      · intro h l hl
        rw [← ha l hl]
        exact h l hl
      · intro h l hl
        rw [ha l hl]
        exact h l hl
    have hcount : (Finset.univ.filter (fun u : CubeVertex p.d =>
        P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u s ≤ p.r + p.D)) =
        Finset.univ.filter (fun u : CubeVertex p.d =>
          P' (u, j) = true ∧ A' (u, j) = true ∧ _root_.hammingDist u s ≤ p.r + p.D) := by
      ext u
      by_cases hd : _root_.hammingDist u s ≤ p.r + p.D
      · have hv : _root_.hammingDist u v ≤ R + p.r + p.D := by
          have ht := (_root_.hammingDist_triangle u s v).trans (Nat.add_le_add hd hs)
          omega
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP (u, j) hv, hA (u, j) hv]
      · simp only [Finset.mem_filter, hd, and_false]
    unfold HDParams.Bad
    rw [hactive, hcount]
  apply selectionAt_of_bad_congr p Sites P A P' A' E E' v R τ τ' hbad
  · exact hE v (by simp)
  · intro j l hl
    apply hA l
    have hd := hshape v (by simp) j l hl
    omega
  · exact hτ

theorem choose_ext {α : Sort*} {P Q : α → Prop} (hp : ∃ a, P a) (hq : ∃ a, Q a)
    (h : ∀ a, P a ↔ Q a) : Classical.choose hp = Classical.choose hq := by
  have he : P = Q := funext fun a => propext (h a)
  subst Q
  rfl

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G) {Id : Type} [DecidableEq Id]

def recordForChoices (H : X.KeyHist) (a : X.ArraysOn Id) (y : OddRole5 n)
    (s : EvenRole5 n → Option Id) : X.RecordOn Id :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs := (Setup5.evenNbrs y).biUnion (fun v => match s v with
    | some l => {(l, X.g.evenType (X.p.J n) v.1)} | none => ∅)
  let refs := (Setup5.evenNbrs y).biUnion (fun v => match s v with
    | some l => if ℓ ∈ (X.g.evenType (X.p.J n) v.1).2.1 ∧
        ℓ.isLeft = (X.g.evenType (X.p.J n) v.1).2.2.isSome then
        {(l, X.g.evenType (X.p.J n) v.1, X.g.optionalKey (X.p.J n) v.1)} else ∅
    | none => ∅)
  let mask := match ℓ with
    | .inl k => if hex : ∃ v ∈ Setup5.evenNbrs y,
        (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (s v).isSome then
      let v := Classical.choose hex
      match s v with
      | some l => some (l, X.g.evenType (X.p.J n) v.1,
          X.firstK (X.hitSet a (l, X.g.evenType (X.p.J n) v.1) (X.lowCol H.2 k)) (X.p.usedBlocks n))
      | none => none
      else none
    | .inr _ => none
  (ℓ, obs, refs, mask)

theorem recordForChoices_congr (H : X.KeyHist) (a b : X.ArraysOn Id) (y : OddRole5 n)
    (s t : EvenRole5 n → Option Id) (hs : ∀ v ∈ Setup5.evenNbrs y, s v = t v)
    (hab : ∀ v ∈ Setup5.evenNbrs y, ∀ l, s v = some l →
      a (l, X.g.evenType (X.p.J n) v.1) = b (l, X.g.evenType (X.p.J n) v.1)) :
    recordForChoices X H a y s = recordForChoices X H b y t := by
  unfold recordForChoices
  dsimp only
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply Finset.biUnion_congr rfl
    intro v hv
    rw [hs v hv]
  apply Prod.ext
  · apply Finset.biUnion_congr rfl
    intro v hv
    rw [hs v hv]
  by_cases hy : X.g.severity y.1 ≤ X.p.J n
  · simp only [ChunkGeometry5.roleKey, dite_eq_left hy]
    have hp (v : EvenRole5 n) :
        (v ∈ Setup5.evenNbrs y ∧ (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (s v).isSome) ↔
        (v ∈ Setup5.evenNbrs y ∧ (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (t v).isSome) := by
      by_cases hv : v ∈ Setup5.evenNbrs y
      · simp only [hv, true_and, hs v hv]
      · simp only [hv, false_and]
    have he : (∃ v ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (s v).isSome) ↔
        (∃ v ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (t v).isSome) := exists_congr hp
    by_cases hex : ∃ v ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (s v).isSome
    · have hex' := he.mp hex
      rw [dite_eq_left hex, dite_eq_left hex']
      have hchoose := choose_ext hex hex' hp
      rw [← hchoose]
      let v := Classical.choose hex
      have hv : v ∈ Setup5.evenNbrs y := (Classical.choose_spec hex).1
      rw [← hs v hv]
      cases hsel : s v with
      | none => rfl
      | some l =>
        have ha := hab v hv l hsel
        dsimp only [v] at ha
        simp only [Setup5.hitSet]
        rw [ha]
    · have hn : ¬ ∃ v ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) v.1).2.2 = none ∧ (t v).isSome :=
        fun h => hex (he.mpr h)
      rw [dite_eq_right hex, dite_eq_right hn]
  · simp only [ChunkGeometry5.roleKey, dite_eq_right hy]

theorem renamed_refs {Id' : Type} [DecidableEq Id'] (f : Id → Id') (r : X.RecordOn Id) :
    (renameRecord X f r).2.2.1 = r.2.2.1.image (fun d : Id × X.Ty × Option X.Key => (f d.1, d.2)) := by
  ext c
  simp only [renameRecord, Finset.mem_image]

theorem low_column_eval (H : X.KeyHist) (ℓ : X.Key) (k : X.LowIdx) (hk : ℓ = .inl k)
    (h : Fin (colLen5 (X.p.s n) ℓ)) : H.2 ℓ h = X.lowCol H.2 k := by
  subst ℓ
  change H.2 (.inl k) h = H.2 (.inl k) (0 : Fin 1)
  have hh : (h : Fin 1) = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance h (0 : Fin 1)
  exact congrArg (fun h : Fin 1 => H.2 (.inl k) h) hh

theorem record_ref_mode (r : X.RecordOn Id) (y : OddRole5 n) (μ : X.St.Site → Id)
    (hr : X.RecordFrom r y μ) (hl : r.1.isLeft) (hT : 0 < X.p.T n)
    (d : Id × X.Ty × Option X.Key) (hd : d ∈ r.2.2.1) : d.2.1.2.2.isSome := by
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  let i0 : Fin (X.p.T n) := ⟨0, hT⟩
  let f : Id → Fin (X.p.T n) := fun _ => i0
  let r' := renameRecord X f r
  have hr' : X.RecOccurs r' := ⟨y, f ∘ μ, recordFrom_rename X f r y μ hr⟩
  have hd' : (i0, d.2.1, d.2.2) ∈ r'.2.2.1 := by
    rw [renamed_refs X f r]
    apply (Finset.mem_image (f := fun d : Id × X.Ty × Option X.Key => (f d.1, d.2))).mpr
    exact ⟨d, hd, rfl⟩
  exact Lane_sol_s05_hist1b.low_record_ref_mode X r' hr' hl _ hd'

theorem record_refs_length_lower (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (y : OddRole5 n) (μ : X.St.Site → Id) (hr : X.RecordFrom r y μ) (hl : r.1.isLeft)
    (hT : 0 < X.p.T n) (c : Id × X.Ty × Finset (Fin X.blockBound)) (hc : c ∈ X.refsOn H r a) :
    X.p.kPrime n r.1.level ≤ X.refLen c.2.1 c.2.2 := by
  letI : DecidableEq (Fin (X.p.T n)) := Classical.decEq _
  let i0 : Fin (X.p.T n) := ⟨0, hT⟩
  let f : Id → Fin (X.p.T n) := fun _ => i0
  let r' := renameRecord X f r
  have hr' : X.RecOccurs r' := ⟨y, f ∘ μ, recordFrom_rename X f r y μ hr⟩
  have href : X.refsOn H r a = r.2.2.1.image (fun d : Id × X.Ty × Option X.Key =>
      (d.1, d.2.1, X.refSubsetOn H a (d.1, d.2.1) d.2.2)) := by
    ext c
    simp only [Setup5.refsOn, Finset.mem_image]
  rw [href] at hc
  obtain ⟨d, hd, he⟩ := (Finset.mem_image (f := fun d : Id × X.Ty × Option X.Key =>
    (d.1, d.2.1, X.refSubsetOn H a (d.1, d.2.1) d.2.2))).mp hc
  have hmode := record_ref_mode X r y μ hr hl hT d hd
  have hfull : X.refSubsetOn H a (d.1, d.2.1) d.2.2 =
      Finset.univ.filter (fun i : Fin X.blockBound => (i : ℕ) < X.p.typeBlocks n d.2.1) := by
    cases ht : d.2.1.2.2 with
    | none => simp [ht] at hmode
    | some j => simp only [Setup5.refSubsetOn, ht]
  have hd' : (i0, d.2.1, d.2.2) ∈ r'.2.2.1 := by
    rw [renamed_refs X f r]
    apply (Finset.mem_image (f := fun d : Id × X.Ty × Option X.Key => (f d.1, d.2))).mpr
    exact ⟨d, hd, rfl⟩
  have hc' : (i0, c.2.1, c.2.2) ∈ Lane_sol_s05_hist1b.lowRefs X r' := by
    have heq : Lane_sol_s05_hist1b.lowRefs X r' = r'.2.2.1.image
        (fun d : Fin (X.p.T n) × X.Ty × Option X.Key =>
          (d.1, d.2.1, Finset.univ.filter (fun i : Fin X.blockBound => (i : ℕ) < X.p.typeBlocks n d.2.1))) := by
      ext c
      simp only [Lane_sol_s05_hist1b.lowRefs, Finset.mem_image]
    rw [heq]
    apply (Finset.mem_image (f := fun d : Fin (X.p.T n) × X.Ty × Option X.Key =>
      (d.1, d.2.1, Finset.univ.filter (fun i : Fin X.blockBound => (i : ℕ) < X.p.typeBlocks n d.2.1)))).mpr
    refine ⟨(i0, d.2.1, d.2.2), hd', ?_⟩
    have hK := congrArg (fun c : Id × X.Ty × Finset (Fin X.blockBound) => c.2.1) he
    have hM := congrArg (fun c : Id × X.Ty × Finset (Fin X.blockBound) => c.2.2) he
    dsimp only at hK hM
    rw [← hfull, hM, hK]
  exact Lane_sol_s05_hist1b.lowRefs_length_lower X r' hr' hl _ hc'

end
end HypercubeRamsey.Lane_sol_s05_k1
