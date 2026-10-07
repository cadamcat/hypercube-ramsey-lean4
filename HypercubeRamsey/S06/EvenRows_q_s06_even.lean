import HypercubeRamsey.S06.Defs
import HypercubeRamsey.S06.Centres

namespace HypercubeRamsey.S06.Lane_q_s06_even

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

private theorem pi_weight_split_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
        (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  let f : ι → ℝ := fun i => (P i).w (ω i)
  have hs : (∏ i : {i // i ∈ s}, f i.1) = ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 :=
        Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) := by
      exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) * (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]

/-- Split a product-law weight at one distinguished coordinate. -/
theorem pi_weight_split_coord_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (j : ι) (ω : ∀ i, Ω i) :
      (∏ i, (P i).w (ω i)) = (P j).w (ω j) *
      (∏ i : {i // i ≠ j}, (P i.1).w (ω i.1)) := by
  have hsingle :
      (∏ i : {i // i ∈ ({j} : Finset ι)}, (P i.1).w (ω i.1)) = (P j).w (ω j) := by
    simp
  let ecomp : {i // i ∉ ({j} : Finset ι)} ≃ {i // i ≠ j} := {
    toFun := fun i => ⟨i.1, by simpa using i.2⟩
    invFun := fun i => ⟨i.1, by simpa using i.2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl }
  have hcomp :
      (∏ i : {i // i ∉ ({j} : Finset ι)}, (P i.1).w (ω i.1)) =
        ∏ i : {i // i ≠ j}, (P i.1).w (ω i.1) := by
    exact Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
  rw [pi_weight_split_even P {j} ω, hsingle, hcomp]

/-- Split the expectation of a product law into coordinates in a finite set and its complement. -/
theorem pi_expect_split_even {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
              f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split_even P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

/-- Expand an event under a product law by conditioning on its first coordinate. -/
theorem pr_prod_eq_sum_even {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α × β → Prop) :
    (FinProb.prod P Q).pr A = ∑ a, P.w a * Q.pr (fun b => A (a, b)) := by
  classical
  unfold FinProb.pr
  change (∑ ab, if A ab then P.w ab.1 * Q.w ab.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : A (a, b) <;> simp [h]

/-- Transfer a bound on each projected atom to any event of the projection. -/
theorem pr_event_le_sum_atoms {Ω α : Type*} [Fintype Ω] [Fintype α]
    (P : FinProb Ω) (f : Ω → α) (B : α → Prop) (b : α → ℝ)
    (h : ∀ a, P.pr (fun ω => f ω = a) ≤ b a) :
    P.pr (fun ω => B (f ω)) ≤ ∑ a ∈ Finset.univ.filter B, b a := by
  classical
  calc
    P.pr (fun ω => B (f ω)) =
        ∑ ω, ∑ a, if f ω = a ∧ B a then P.w ω else 0 := by
      unfold FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hB : B (f ω)
      · rw [if_pos hB]
        have hsum : (∑ a, if f ω = a ∧ B a then P.w ω else 0) = P.w ω := by
          calc
            (∑ a, if f ω = a ∧ B a then P.w ω else 0) =
                ∑ a, if f ω = a then P.w ω else 0 := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  by_cases hEq : f ω = a
                  · subst a
                    simp [hB]
                  · simp [hEq]
            _ = P.w ω := by simp
        exact hsum.symm
      · rw [if_neg hB]
        symm
        apply Finset.sum_eq_zero
        intro a ha
        by_cases hEq : f ω = a
        · have hBa : ¬ B a := by simpa [hEq] using hB
          simp [hEq, hBa]
        · simp [hEq]
    _ = ∑ a, if B a then P.pr (fun ω => f ω = a) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hB : B a <;> simp [hB, FinProb.pr]
    _ ≤ ∑ a, if B a then b a else 0 := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hB : B a <;> simp [hB, h a]
    _ = ∑ a ∈ Finset.univ.filter B, b a := by
      rw [Finset.sum_filter]

/-- Each law in a nonempty finite family is dominated by its unnormalized sum, after normalization. -/
theorem law_le_card_normalized_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (P : ι → FinProb Ω) (D : Finset ι) (hD : D.Nonempty) (i : ι) (hi : i ∈ D)
    (ω₀ y : Ω) :
    (P i).w y ≤ (D.card : ℝ) * (normalize6 (fun y => ∑ i ∈ D, (P i).w y) ω₀).w y := by
  classical
  let f : Ω → ℝ := fun y => ∑ i ∈ D, (P i).w y
  have hf : ∀ y, 0 ≤ f y := by
    intro y
    exact Finset.sum_nonneg fun i hi => (P i).nonneg y
  have htotal : ∑ y, f y = (D.card : ℝ) := by
    calc
      ∑ y, f y = ∑ i ∈ D, ∑ y, (P i).w y := by
        simp only [f]
        rw [Finset.sum_comm]
      _ = ∑ i ∈ D, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (P i).sum_eq_one
      _ = (D.card : ℝ) := by simp
  have hmass : ∑ y, max 0 (f y) = (D.card : ℝ) := by
    calc
      ∑ y, max 0 (f y) = ∑ y, f y := by
        apply Finset.sum_congr rfl
        intro y hy
        exact max_eq_right (hf y)
      _ = (D.card : ℝ) := htotal
  have hpos : 0 < ∑ y, max 0 (f y) := by
    rw [hmass]
    exact_mod_cast (Finset.card_pos.mpr hD)
  have hnorm (y : Ω) : (normalize6 f ω₀).w y = f y / (D.card : ℝ) := by
    simp [normalize6, hpos, hf y, hmass, hD]
  have hle : (P i).w y ≤ f y := by
    dsimp [f]
    exact Finset.single_le_sum (fun j hj => (P j).nonneg y) hi
  rw [hnorm]
  have hcard : (D.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hD).ne'
  calc
    (P i).w y ≤ f y := hle
    _ = (D.card : ℝ) * (f y / (D.card : ℝ)) := by field_simp [hcard]

/-- Multiply pointwise exponential comparisons over a finite set. -/
theorem prod_le_exp_sum_mul_prod {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p q c : ι → ℝ) (hp : ∀ i ∈ S, 0 ≤ p i) (hq : ∀ i ∈ S, 0 ≤ q i)
    (h : ∀ i ∈ S, p i ≤ Real.exp (c i) * q i) :
    ∏ i ∈ S, p i ≤ Real.exp (∑ i ∈ S, c i) * ∏ i ∈ S, q i := by
  calc
    ∏ i ∈ S, p i ≤ ∏ i ∈ S, Real.exp (c i) * q i := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hp i hi
      · intro i hi
        exact h i hi
    _ = (∏ i ∈ S, Real.exp (c i)) * ∏ i ∈ S, q i := by rw [Finset.prod_mul_distrib]
    _ = Real.exp (∑ i ∈ S, c i) * ∏ i ∈ S, q i := by rw [← Real.exp_sum]

/-- A residual-coordinate edge preserves the even type data used by `Matching`. -/
theorem matching_of_residual_flip {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (v : CubeVertex n) (a : Fin n) (ha : a ∈ X.g.L.residual) :
    X.Matching (X.g.L.stateOf (flipVertex6 v a)) (X.evenType v) := by
  classical
  have hset : Finset.univ.filter (fun b : Fin n => v b ≠ flipVertex6 v a b) = {a} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hb : b = a
    · subst b
      cases hv : v a <;> simp [flipVertex6, hv]
    · have hupdate : Function.update v a (!v a) b = v b := by
        exact Function.update_of_ne (f := v) (a := b) (a' := a) hb (!v a)
      simp [flipVertex6, hupdate, hb]
  have hdist : hammingDist v (flipVertex6 v a) = 1 := by
    simp [hammingDist, hset]
  have hadj : (cube n).Adj v (flipVertex6 v a) := hdist
  have hcoarseDisj : ∀ i, Disjoint (X.g.L.coarseChunks i) X.g.L.residual :=
    X.g.L.chunks_disjoint.2.2.2.1
  have hfineDisj : ∀ i, Disjoint (X.g.L.fineChunks i) X.g.L.residual :=
    X.g.L.chunks_disjoint.2.2.2.2
  have hkey : X.g.L.key (flipVertex6 v a) = X.g.L.key v := by
    symm
    apply X.g.flips.noncoarse_flip_key v (flipVertex6 v a) hadj
    intro i b hb
    have hnot : a ∉ X.g.L.coarseChunks i := by
      intro hamem
      exact (Finset.disjoint_left.mp (hcoarseDisj i)) hamem ha
    have hba : b ≠ a := ne_of_mem_of_not_mem hb hnot
    simp [flipVertex6, hba]
  have hfine : ∀ i b, b ∈ X.g.L.fineChunks i →
      v b = (flipVertex6 v a) b := by
    intro i b hb
    have hnot : a ∉ X.g.L.fineChunks i := by
      intro hamem
      exact (Finset.disjoint_left.mp (hfineDisj i)) hamem ha
    have hba : b ≠ a := ne_of_mem_of_not_mem hb hnot
    simp [flipVertex6, hba]
  have hflipFacts := X.g.flips.nonfine_flip_fine v (flipVertex6 v a) hadj (by
    intro i b hb
    exact hfine i b hb)
  have hsign : X.g.L.sign (flipVertex6 v a) = X.g.L.sign v := hflipFacts.1.symm
  have hsev : X.g.L.severity (flipVertex6 v a) = X.g.L.severity v := hflipFacts.2.2.symm
  have hstateKey := X.facts.key_eq (flipVertex6 v a)
  have hstateSev := X.facts.severity_eq (flipVertex6 v a)
  have hmode : (X.evenType v).mode = X.stMode (X.g.L.stateOf (flipVertex6 v a)) := by
    have hsev' : X.g.L.stSeverity (X.g.L.stateOf (flipVertex6 v a)) = X.g.L.severity v :=
      hstateSev.trans hsev
    have hmodeType : (X.evenType v).mode = modeOf6 X.J (X.g.L.severity v) := by
      simp only [Ctx6.evenType, Type6.mode, makeType6]
      split_ifs with h
      · simp [modeOf6, h]
      · simp [modeOf6, h]
    have hmodeState : X.stMode (X.g.L.stateOf (flipVertex6 v a)) =
        modeOf6 X.J (X.g.L.stSeverity (X.g.L.stateOf (flipVertex6 v a))) := rfl
    calc
      (X.evenType v).mode = modeOf6 X.J (X.g.L.severity v) := hmodeType
      _ = modeOf6 X.J (X.g.L.stSeverity (X.g.L.stateOf (flipVertex6 v a))) :=
        congrArg (modeOf6 X.J) hsev'.symm
      _ = X.stMode (X.g.L.stateOf (flipVertex6 v a)) := hmodeState.symm
  have htypeKey : (X.evenType v).key = X.g.L.stKey (X.g.L.stateOf (flipVertex6 v a)) := by
    calc
      (X.evenType v).key = X.g.L.key v := by
        simp only [Ctx6.evenType, Type6.key, makeType6]
        split_ifs <;> rfl
      _ = X.g.L.key (flipVertex6 v a) := hkey.symm
      _ = X.g.L.stKey (X.g.L.stateOf (flipVertex6 v a)) := hstateKey.symm
  constructor
  · exact hmode
  · exact congrArg primaryName6 htypeKey

/-- A selected center lies in the active eligibility set at the selected height. -/
theorem choice_mem_elig {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (C : X.Centre) (R : ℕ) (s : X.State) (ℓ : X.Loc)
    (hchoice : X.choice H C R s = some ℓ) :
    ∃ j : Fin (X.hp.H + 1), ℓ ∈ X.elig H C (X.site s) j ∧ X.act C ℓ = true := by
  classical
  unfold Ctx6.choice at hchoice
  dsimp only [HDParams.selectionAt] at hchoice
  split_ifs at hchoice with hj hbad hne
  all_goals try cases hchoice
  let height := X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) R (X.site s)
  let level : Fin (X.hp.H + 1) := ⟨height, by omega⟩
  let active := (X.elig H C (X.site s) level).filter (fun x => X.act C x = true)
  let priorities := active.image (fun x => X.hp.priority (X.ties C) (X.site s, level) x)
  have hmin : priorities.min' hne ∈ priorities := Finset.min'_mem priorities hne
  have hmem := Finset.mem_image.mp hmin
  refine ⟨level, ?_, ?_⟩
  · have hactive : Classical.choose hmem ∈ active := (Classical.choose_spec hmem).1
    exact (Finset.mem_filter.mp hactive).1
  · have hactive : Classical.choose hmem ∈ active := (Classical.choose_spec hmem).1
    exact (Finset.mem_filter.mp hactive).2

/-- A valid odd descriptor is among the descriptors generated by its actual level pair. -/
theorem valid_desc_mem_descsIn {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (C : X.Centre) (b : X.State)
    (hvalid : X.OddValid H C X.Rlong b) :
    ∃ j : Fin X.hp.H,
      X.actDesc H C X.Rlong b ∈ X.descsIn b (X.permAt (X.pos C) b j) := by
  classical
  obtain ⟨j, hlevels⟩ := hvalid.2.2.1
  let φ : X.g.L.stNbr b → X.Loc := fun a => (X.choice H C X.Rlong a.1).getD X.defaultLoc
  have hchoice : ∀ a : X.g.L.stNbr b, X.choice H C X.Rlong a.1 = some (φ a) := by
    intro a
    have hsome := hvalid.1 a.1 a.2
    cases hc : X.choice H C X.Rlong a.1 with
    | none => simp [hc] at hsome
    | some ℓ => simp [φ, hc]
  have hperm : ∀ a : X.g.L.stNbr b, φ a ∈ X.permAt (X.pos C) b j a := by
    intro a
    obtain ⟨l, hElig, hAct⟩ :=
      choice_mem_elig X H C X.Rlong a.1 (φ a) (hchoice a)
    have hprosp := (Finset.mem_sdiff.mp (by simpa [Ctx6.elig] using hElig)).1
    simp only [Ctx6.prosp, Finset.mem_filter, Finset.mem_univ, true_and] at hprosp
    rcases hprosp with ⟨hpos, hlevel, hdist⟩
    have hpair := hlevels a.1 a.2 (φ a) (hchoice a)
    have hown : φ a ∈ X.prosp (X.pos C) (X.site a.1) (φ a).2 := by
      simp [Ctx6.prosp, hpos, hdist]
    unfold Ctx6.permAt
    exact Finset.mem_biUnion.mpr ⟨(φ a).2, hpair, hown⟩
  have hcard : (Finset.univ.image φ).card ≤ X.T := by
    simpa [Ctx6.actDesc, φ, Finset.image_image, Function.comp_def] using hvalid.2.2.2.1
  refine ⟨j, ?_⟩
  unfold Ctx6.descsIn
  apply Finset.mem_image.mpr
  refine ⟨φ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · exact ⟨hperm, hcard⟩
  · rfl

set_option maxHeartbeats 1000000
/-- The selected even pair occurs in the actual descriptor of each adjacent odd role. -/
theorem selected_pair_mem_actDesc {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (C : X.Centre) (v u : CubeVertex n)
    (hv : IsEvenRole v) (hu : ¬ IsEvenRole u) (hadj : (cube n).Adj u v) :
    ((X.choice H C X.Rlong (X.g.L.stateOf v)).getD X.defaultLoc,
      X.stType (X.g.L.stateOf v)) ∈
        X.actDesc H C X.Rlong (X.g.L.stateOf u) := by
  have hNbr : X.g.L.stateOf v ∈ X.g.L.stNbr (X.g.L.stateOf u) := by
    simp only [ChunkLayout6.stNbr, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨u, v, hu, hv, rfl, rfl, hadj⟩
  change ((X.choice H C X.Rlong (X.g.L.stateOf v)).getD X.defaultLoc,
      X.stType (X.g.L.stateOf v)) ∈
    Finset.univ.image (fun a : {q // q ∈ X.g.L.stNbr (X.g.L.stateOf u)} =>
      ((X.choice H C X.Rlong a.1).getD X.defaultLoc, X.stType a.1))
  apply Finset.mem_image.mpr
  refine ⟨⟨X.g.L.stateOf v, hNbr⟩, Finset.mem_univ _, ?_⟩
  rfl
set_option maxHeartbeats 200000

/-- A selected even pair lies in some permitted descriptor at an adjacent valid odd state. -/
theorem selected_pair_in_descsIn_of_valid_neighbor {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (C : X.Centre)
    (v u : CubeVertex n) (hv : IsEvenRole v) (hu : ¬ IsEvenRole u)
    (hadj : (cube n).Adj u v) (c : X.Loc)
    (hc : X.choice H C X.Rlong (X.g.L.stateOf v) = some c)
    (hvalid : X.OddValid H C X.Rlong (X.g.L.stateOf u)) :
    ∃ j : Fin X.hp.H,
      X.actDesc H C X.Rlong (X.g.L.stateOf u) ∈
          X.descsIn (X.g.L.stateOf u) (X.permAt (X.pos C) (X.g.L.stateOf u) j) ∧
        (c, X.stType (X.g.L.stateOf v)) ∈ X.actDesc H C X.Rlong (X.g.L.stateOf u) := by
  obtain ⟨j, hdesc⟩ := valid_desc_mem_descsIn X H C (X.g.L.stateOf u) hvalid
  have hpair := selected_pair_mem_actDesc X H C v u hv hu hadj
  have hpair' : (c, X.stType (X.g.L.stateOf v)) ∈ X.actDesc H C X.Rlong (X.g.L.stateOf u) := by
    simpa [hc] using hpair
  exact ⟨j, hdesc, hpair'⟩

/-- Insert a descriptor containing a fixed pair into the union over level-pair descriptors. -/
theorem mem_descUnion_of_level_pair {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {G : Colour} {M : TagMix N} (X : Ctx6 γ p₀ K n N E G M)
    (H : X.Hist) (C : X.Centre) (b : X.State) (c : X.Loc × X.Ty)
    (D : Finset (X.Loc × X.Ty)) (j : Fin X.hp.H)
    (hD : D ∈ X.descsIn b (X.permAt (X.pos C) b j)) (hc : c ∈ D) :
    D ∈ (Finset.univ : Finset (Fin X.hp.H)).biUnion
      (fun j => (X.descsIn b (X.permAt (X.pos C) b j)).filter (fun D => c ∈ D)) := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hD, hc⟩⟩

private theorem exists_flipVertex6_of_adj {n : ℕ} (v u : CubeVertex n)
    (hadj : (cube n).Adj v u) : ∃ a : Fin n, u = flipVertex6 v a := by
  have hcard : (Finset.univ.filter fun a : Fin n => v a ≠ u a).card = 1 := by
    simpa [cube, hammingDist] using hadj
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ?_⟩
  funext b
  by_cases hb : b = a
  · subst b
    have hmem : a ∈ Finset.univ.filter (fun i : Fin n => v i ≠ u i) := by
      rw [ha]
      simp
    have hdiff : v a ≠ u a := (Finset.mem_filter.mp hmem).2
    cases hv : v a <;> cases hu : u a <;> simp_all [flipVertex6]
  · have hnot : b ∉ Finset.univ.filter (fun i : Fin n => v i ≠ u i) := by
      rw [ha]
      simp [hb]
    have hsame : v b = u b := by
      by_contra hneq
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩)
    have hupdate : Function.update v a (!v a) b = v b :=
      Function.update_of_ne (f := v) (a := b) (a' := a) hb (!v a)
    calc
      u b = v b := hsame.symm
      _ = Function.update v a (!v a) b := hupdate.symm

/-- A cube vertex has at most one adjacent vertex for each flipped coordinate. -/
theorem adjacent_card_le_dimension_even {n : ℕ} (v : CubeVertex n) (hn : 0 < n) :
    (Finset.univ.filter fun u : CubeVertex n => (cube n).Adj v u).card ≤ n := by
  classical
  let adj : Finset (CubeVertex n) := Finset.univ.filter fun u => (cube n).Adj v u
  let coord : CubeVertex n → Fin n := fun u =>
    if h : (cube n).Adj v u then Classical.choose (exists_flipVertex6_of_adj v u h) else ⟨0, by omega⟩
  have hcoord : ∀ u ∈ adj, u = flipVertex6 v (coord u) := by
    intro u hu
    have hadj : (cube n).Adj v u := (Finset.mem_filter.mp hu).2
    simp only [coord, dif_pos hadj]
    exact Classical.choose_spec (exists_flipVertex6_of_adj v u hadj)
  have hinj : (adj : Set (CubeVertex n)).InjOn coord := by
    intro u hu w hw heq
    rw [hcoord u hu, hcoord w hw, heq]
  calc
    (Finset.univ.filter fun u : CubeVertex n => (cube n).Adj v u).card = adj.card := by rfl
    _ ≤ Finset.univ.card := Finset.card_le_card_of_injOn coord (by
      intro u hu
      exact Finset.mem_univ _) hinj
    _ = n := by simp

/-- Only occupied chunk coordinates can give a neighboring state that fails `Matching`. -/
theorem nonmatching_adjacent_card_le_occupied {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (v : CubeVertex n) (hn : 0 < n) :
    (Finset.univ.filter fun u : CubeVertex n =>
      (cube n).Adj v u ∧ ¬ X.Matching (X.g.L.stateOf u) (X.evenType v)).card ≤
      ((Finset.univ.biUnion X.g.L.coarseChunks) ∪
        (Finset.univ.biUnion X.g.L.fineChunks)).card := by
  classical
  let bad : Finset (CubeVertex n) := Finset.univ.filter fun u =>
    (cube n).Adj v u ∧ ¬ X.Matching (X.g.L.stateOf u) (X.evenType v)
  let occupied : Finset (Fin n) :=
    (Finset.univ.biUnion X.g.L.coarseChunks) ∪ (Finset.univ.biUnion X.g.L.fineChunks)
  let coord : CubeVertex n → Fin n := fun u =>
    if h : (cube n).Adj v u then Classical.choose (exists_flipVertex6_of_adj v u h) else ⟨0, hn⟩
  have hcoord : ∀ u ∈ bad, u = flipVertex6 v (coord u) := by
    intro u hu
    have hadj : (cube n).Adj v u := (Finset.mem_filter.mp hu).2.1
    simp only [coord, dif_pos hadj]
    exact Classical.choose_spec (exists_flipVertex6_of_adj v u hadj)
  have hmaps : ∀ u ∈ bad, coord u ∈ occupied := by
    intro u hu
    by_contra hocc
    have hres : coord u ∈ X.g.L.residual := by
      have hmem : coord u ∈ occupied ∪ X.g.L.residual := by
        have hmem := Finset.mem_univ (coord u)
        rw [← X.g.L.chunks_cover] at hmem
        simpa [occupied] using hmem
      rcases Finset.mem_union.mp hmem with hmem | hres
      · exact False.elim (hocc hmem)
      · exact hres
    have hmatch := matching_of_residual_flip X v (coord u) hres
    have heq := hcoord u hu
    rw [← heq] at hmatch
    exact (Finset.mem_filter.mp hu).2.2 hmatch
  have hinj : (bad : Set (CubeVertex n)).InjOn coord := by
    intro u hu w hw hEq
    rw [hcoord u hu, hcoord w hw, hEq]
  exact Finset.card_le_card_of_injOn coord (by
    intro u hu
    exact hmaps u hu) hinj

end HypercubeRamsey.S06.Lane_q_s06_even
