import HypercubeRamsey.S09.Core.Experiment
import HypercubeRamsey.Framework.Minimax

namespace HypercubeRamsey.Lane_q_s09_tag

open Classical Filter OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 0

private theorem finProb_ext_q_s09_tag {Ω : Type*} [Fintype Ω]
    {P Q : FinProb Ω} (h : ∀ ω, P.w ω = Q.w ω) : P = Q := by
  cases P with
  | mk pw pn ps =>
    cases Q with
    | mk qw qn qs =>
      have hpw : pw = qw := funext h
      subst qw
      have hpn : pn = qn := Subsingleton.elim _ _
      have hps : ps = qs := Subsingleton.elim _ _
      cases hpn
      cases hps
      rfl

private theorem finProb_nonempty_q_s09_tag {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) : Nonempty Ω := by
  classical
  by_contra h
  letI : IsEmpty Ω := ⟨fun ω => h ⟨ω⟩⟩
  have hzero : (∑ ω, P.w ω) = 0 := by simp
  rw [P.sum_eq_one] at hzero
  norm_num at hzero

theorem pi_expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (f : ∀ i, α i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).expect (f i) := by
  classical
  simp only [FinProb.expect, FinProb.pi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [← Finset.prod_mul_distrib]

private theorem pi_weight_split_q_s09_tag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter (fun i => i ∉ s)
  have hs : (∏ i : {i // i ∈ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl
  }
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
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) *
          (∏ i : {i // i ∉ s}, f i.1) := by rw [← hs, ← hnot]

theorem pi_expect_split_q_s09_tag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
            f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [pi_weight_split_q_s09_tag P s (e.symm (a, b))]
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

def maskMass {N : ℕ} (ν : Law N) (A : Finset (Fin N)) : ℝ :=
  ∑ y ∈ A, ν.w y

theorem restrictOr9_zero {N : ℕ} (μ : Law N) (A : Finset (Fin N)) (y : Fin N)
    (hy : μ.w y = 0) : (restrictOr9 μ A).w y = 0 := by
  classical
  unfold restrictOr9
  split_ifs with h
  · by_cases hyA : y ∈ A <;> simp [Law.restrict, hyA, hy]
  · exact hy

theorem restrictOr9_outside {N : ℕ} (μ : Law N) (A : Finset (Fin N)) (y : Fin N)
    (hA : 0 < ∑ x ∈ A, μ.w x) (hy : y ∉ A) : (restrictOr9 μ A).w y = 0 := by
  classical
  unfold restrictOr9
  rw [dif_pos hA]
  simp [Law.restrict, hy]

private theorem pr_mono_of_imp {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

private theorem pr_event_compl {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A + P.pr (fun ω => ¬ A ω) = 1 := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  letI : DecidablePred (fun ω => ¬ A ω) := fun ω => Classical.propDecidable (¬ A ω)
  unfold FinProb.pr
  calc
    (∑ ω, if A ω then P.w ω else 0) +
        (∑ ω, if ¬ A ω then P.w ω else 0) = ∑ ω, P.w ω := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : A ω <;> simp [h]
    _ = 1 := P.sum_eq_one

theorem finite_mask_minimax {N : ℕ} [Nonempty (Fin N)] (ν : Law N) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : Finset (Fin N) → Law N)
    (hR : ∀ A, 0 < maskMass ν A → ∀ y, y ∉ A → (R A).w y = 0) :
    ∃ p : FinProb {A : Finset (Fin N) // δ / 2 ≤ maskMass ν A},
      ∀ y, ∑ A, p.w A * (R A.1).w y ≤ (1 + δ) * ν.w y := by
  classical
  let A := {A : Finset (Fin N) // δ / 2 ≤ maskMass ν A}
  have hAne : Nonempty A := by
    refine ⟨⟨Finset.univ, ?_⟩⟩
    have hmass : maskMass ν Finset.univ = 1 := by simp [maskMass, ν.sum_eq_one]
    rw [hmass]
    linarith
  have hsolve : ∀ q : FinProb (Fin N), ∃ a : A,
      ∑ y, q.w y * ((R a.1).w y - (1 + δ) * ν.w y) ≤ 0 := by
    intro q
    let μ : ℝ := ∑ y, ν.w y * q.w y
    let t : ℝ := (1 + δ) * μ
    have hμ_nonneg : 0 ≤ μ := by
      dsimp [μ]
      exact Finset.sum_nonneg fun y _ => mul_nonneg (ν.nonneg y) (q.nonneg y)
    have htpos : 0 < 1 + δ := by linarith
    have hqnonneg : ∀ y, 0 ≤ q.w y := q.nonneg
    let good : Finset (Fin N) := Finset.univ.filter (fun y => q.w y ≤ t)
    have hgoodmass : δ / 2 ≤ maskMass ν good := by
      by_cases hμ : μ = 0
      · have hterm (y : Fin N) : ν.w y * q.w y = 0 := by
          have hle : ν.w y * q.w y ≤ μ := by
            dsimp [μ]
            exact Finset.single_le_sum
              (fun z _ => mul_nonneg (ν.nonneg z) (q.nonneg z)) (Finset.mem_univ y)
          have hnonneg := mul_nonneg (ν.nonneg y) (q.nonneg y)
          rw [hμ] at hle
          exact le_antisymm (le_trans hle (by rfl)) hnonneg
        have hbadzero : ν.pr (fun y => y ∉ good) = 0 := by
          unfold FinProb.pr
          apply Finset.sum_eq_zero
          intro y _
          by_cases hy : y ∉ good
          · have hqpos : 0 < q.w y := by
              have : ¬ q.w y ≤ t := by simpa [good] using hy
              have ht0 : t = 0 := by simp [t, μ, hμ]
              rw [ht0] at this
              exact lt_of_not_ge this
            have hνzero : ν.w y = 0 := (mul_eq_zero.mp (hterm y)).resolve_right (ne_of_gt hqpos)
            simp [hy, hνzero]
          · simp [hy]
        have hcompl := pr_event_compl ν (fun y => y ∈ good)
        have hgoodpr : ν.pr (fun y => y ∈ good) = 1 := by
          have hnot : (fun y => ¬ y ∈ good) = (fun y => y ∉ good) := rfl
          rw [hnot, hbadzero] at hcompl
          linarith
        have hmasspr : ν.pr (fun y => y ∈ good) = maskMass ν good := by
          unfold FinProb.pr maskMass
          have hEq : good = Finset.univ.filter (fun y : Fin N => y ∈ good) := by
            ext y
            simp
          rw [hEq]
          simp [Finset.sum_filter]
        rw [← hmasspr, hgoodpr]
        linarith
      · have hμpos : 0 < μ := lt_of_le_of_ne hμ_nonneg (Ne.symm hμ)
        have ht : 0 < t := mul_pos htpos hμpos
        have hmarkov := FinProb.markov ν q.w t hqnonneg ht
        have hmean : ν.expect q.w = μ := by simp [FinProb.expect, μ]
        have hbad : ν.pr (fun y => y ∉ good) ≤ 1 / (1 + δ) := by
          have hsub : ∀ y, y ∉ good → t ≤ q.w y := by
            intro y hy
            have hlt : ¬ q.w y ≤ t := by simpa [good] using hy
            exact le_of_lt (lt_of_not_ge hlt)
          have hle := pr_mono_of_imp ν hsub
          have hratio : μ / t = 1 / (1 + δ) := by
            dsimp [t]
            field_simp [ne_of_gt hμpos, ne_of_gt htpos]
          calc
            ν.pr (fun y => y ∉ good) ≤ ν.pr (fun y => t ≤ q.w y) := hle
            _ ≤ ν.expect q.w / t := hmarkov
            _ = 1 / (1 + δ) := by rw [hmean, hratio]
        have hcompl := pr_event_compl ν (fun y => y ∈ good)
        have hgoodpr : δ / (1 + δ) ≤ ν.pr (fun y => y ∈ good) := by
          have hnot : (fun y => ¬ y ∈ good) = (fun y => y ∉ good) := rfl
          rw [hnot] at hcompl
          have hidentity : 1 - 1 / (1 + δ) = δ / (1 + δ) := by
            field_simp [ne_of_gt htpos]
            ring
          have hbound : 1 - 1 / (1 + δ) ≤ ν.pr (fun y => y ∈ good) := by
            linarith
          rw [hidentity] at hbound
          exact hbound
        have hmasspr : ν.pr (fun y => y ∈ good) = maskMass ν good := by
          unfold FinProb.pr maskMass
          have hEq : good = Finset.univ.filter (fun y : Fin N => y ∈ good) := by
            ext y
            simp
          rw [hEq]
          simp [Finset.sum_filter]
        rw [← hmasspr]
        have hδratio : δ / 2 ≤ δ / (1 + δ) := by
          apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) htpos).2
          nlinarith [hδ, hδ1]
        exact hδratio.trans hgoodpr
    let a : A := ⟨good, hgoodmass⟩
    have hprice : ∀ y ∈ good, q.w y ≤ t := by
      intro y hy
      exact (Finset.mem_filter.mp hy).2
    have hmeanR : (R a.1).expect q.w ≤ t := by
      have hpoint : ∀ y, q.w y ≤ if y ∈ good then t else q.w y := by
        intro y
        by_cases hy : y ∈ good
        · simp [hy, hprice y hy]
        · simp [hy]
      have hmono := (R a.1).expect_mono hpoint
      have hsupport : ∀ y, y ∉ good → (R a.1).w y = 0 :=
        hR good (lt_of_lt_of_le (by positivity) hgoodmass)
      have hpiece : (R a.1).expect (fun y => if y ∈ good then t else q.w y) = t := by
        unfold FinProb.expect
        have hpointEq (y : Fin N) :
            (R a.1).w y * (if y ∈ good then t else q.w y) = (R a.1).w y * t := by
          by_cases hy : y ∈ good
          · simp [hy]
          · simp [hy, hsupport y hy]
        calc
          (∑ y, (R a.1).w y * (if y ∈ good then t else q.w y)) =
              ∑ y, (R a.1).w y * t := by
            apply Finset.sum_congr rfl
            intro y _
            exact hpointEq y
          _ = t := by rw [← Finset.sum_mul]; simp [(R a.1).sum_eq_one]
      exact hmono.trans_eq hpiece
    have hmatrix :
        ∑ y, q.w y * ((R a.1).w y - (1 + δ) * ν.w y) =
          (R a.1).expect q.w - (1 + δ) * μ := by
      calc
        ∑ y, q.w y * ((R a.1).w y - (1 + δ) * ν.w y) =
            ∑ y, (q.w y * (R a.1).w y - (1 + δ) * (ν.w y * q.w y)) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = (∑ y, q.w y * (R a.1).w y) -
            (1 + δ) * (∑ y, ν.w y * q.w y) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        _ = (R a.1).expect q.w - (1 + δ) * μ := by
          simp [FinProb.expect, μ, mul_comm]
    refine ⟨a, ?_⟩
    have hmeanR' : (R a.1).expect q.w ≤ (1 + δ) * μ := by simpa [t] using hmeanR
    rw [hmatrix]
    linarith
  obtain ⟨p, hp⟩ := finite_minimax
    (fun (a : A) (y : Fin N) => (R a.1).w y - (1 + δ) * ν.w y) hsolve
  refine ⟨p, ?_⟩
  intro y
  have h := hp y
  have hrewrite :
      (∑ a, p.w a * ((R a.1).w y - (1 + δ) * ν.w y)) =
        (∑ a, p.w a * (R a.1).w y) - (1 + δ) * ν.w y := by
    calc
      ∑ a, p.w a * ((R a.1).w y - (1 + δ) * ν.w y) =
          ∑ a, (p.w a * (R a.1).w y - (1 + δ) * ν.w y * p.w a) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ a, p.w a * (R a.1).w y) -
          (1 + δ) * ν.w y * (∑ a, p.w a) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (∑ a, p.w a * (R a.1).w y) - (1 + δ) * ν.w y := by
        rw [p.sum_eq_one]
        ring
  rw [hrewrite] at h
  linarith

noncomputable def tagAnchorSites_q_s09_tag {P : Params9} {n : ℕ}
    (I : IDMap9 P n) : Finset (I.ID ⊕ OddSites9 n) :=
  Finset.univ.image Sum.inl

noncomputable def tagAnchorOutcome_q_s09_tag {P : Params9} {n N : ℕ}
    {I : IDMap9 P n} (a : ∀ v : tagAnchorSites_q_s09_tag I, Val9 I N v.1)
    (b : OddSites9 n) (A : Finset (Fin N)) : Outcome9 I N :=
  fun v => match v with
    | .inl c => a ⟨Sum.inl c,
        Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
    | .inr b' => if b' = b then A else (∅ : Finset (Fin N))

theorem rowLaw9_ext_q_s09_tag {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (b : OddSites9 n) {ω ω' : Outcome9 I N}
    (hanc : ∀ c, anc9 ω c = anc9 ω' c) (hmask : msk9 ω b = msk9 ω' b) :
    rowLaw9 S E G ω b = rowLaw9 S E G ω' b := by
  have hhit : hitSet9 E G ω (IDMap9.seen I b.1) = hitSet9 E G ω' (IDMap9.seen I b.1) := by
    unfold hitSet9
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h c hc
      rw [← hanc c]
      exact h c hc
    · intro h c hc
      rw [hanc c]
      exact h c hc
  have hmasked : maskedLaw9 S ω b = maskedLaw9 S ω' b := by
    simp [maskedLaw9, hmask]
  unfold rowLaw9
  rw [hmasked, hhit]

noncomputable def tagActionLaw_q_s09_tag {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (b : OddSites9 n) (A : Finset (Fin N)) : Law N :=
  Law.mix (FinProb.pi (fun v : tagAnchorSites_q_s09_tag I => inputLaw9 S I v.1))
    (fun a => rowLaw9 S E G (tagAnchorOutcome_q_s09_tag a b A) b)

theorem tagActionLaw_eq_of_tag_eq_q_s09_tag {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S S' : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (b : OddSites9 n) (A : Finset (Fin N)) (hTag : S.tag = S'.tag) :
    tagActionLaw_q_s09_tag (I := I) S E G b A =
      tagActionLaw_q_s09_tag (I := I) S' E G b A := by
  classical
  have hinput (i : tagAnchorSites_q_s09_tag I) :
      inputLaw9 S I i.1 = inputLaw9 S' I i.1 := by
    obtain ⟨c, _, hci⟩ := Finset.mem_image.mp i.2
    rw [← hci]
    simp [inputLaw9, hTag]
    rfl
  have hinputFun :
      (fun i : tagAnchorSites_q_s09_tag I => inputLaw9 S I i.1) =
        (fun i : tagAnchorSites_q_s09_tag I => inputLaw9 S' I i.1) := funext hinput
  have hrow (a : ∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1) :
      rowLaw9 S E G (tagAnchorOutcome_q_s09_tag a b A) b =
        rowLaw9 S' E G (tagAnchorOutcome_q_s09_tag a b A) b := by
    simp [rowLaw9, maskedLaw9, siteSecond9, hTag]
  apply finProb_ext_q_s09_tag
  intro y
  simp only [tagActionLaw_q_s09_tag, Law.mix]
  rw [hinputFun]
  apply Finset.sum_congr rfl
  intro a _
  rw [hrow a]

theorem flipWord_involutive {m : ℕ} (z : CubeVertex m) (j : Fin m) :
    flipWord9 (flipWord9 z j) j = z := by
  funext k
  by_cases h : k = j
  · subst k
    simp [flipWord9]
  · simp [flipWord9, h]

theorem tagScope_card_le (P : Params9) (n : ℕ) (z : CubeVertex (P.m n)) :
    (tagScope9 z).card ≤ P.m n + 1 := by
  classical
  unfold tagScope9
  calc
    (insert z (Finset.univ.image (flipWord9 z))).card ≤
        (Finset.univ.image (flipWord9 z)).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin (P.m n))).card + 1 := by
      gcongr
      exact Finset.card_image_le
    _ = P.m n + 1 := by simp

theorem tagScope_fiber_card_le (P : Params9) (n : ℕ) (a : CubeVertex (P.m n)) :
    (Finset.univ.filter (fun z : CubeVertex (P.m n) => a ∈ tagScope9 z)).card ≤ P.m n + 1 := by
  classical
  let S := insert a (Finset.univ.image (flipWord9 a))
  have hsub : Finset.univ.filter (fun z : CubeVertex (P.m n) => a ∈ tagScope9 z) ⊆ S := by
    intro z hz
    have hz' : a ∈ insert z (Finset.univ.image (flipWord9 z)) := by
      simpa [tagScope9] using (Finset.mem_filter.mp hz).2
    rcases Finset.mem_insert.mp hz' with hza | hflip
    · subst z
      exact Finset.mem_insert_self _ _
    · obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp hflip
      have hzEq : z = flipWord9 a j := by
        have h := congrArg (fun x => flipWord9 x j) hja
        rw [flipWord_involutive] at h
        exact h
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hzEq.symm⟩
  have hcard : S.card ≤ P.m n + 1 := by
    simpa [S, tagScope9] using tagScope_card_le P n a
  exact (Finset.card_le_card hsub).trans hcard

theorem one_sub_mul_le_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (d : ℕ) :
    1 - (d : ℝ) * x ≤ (1 - x) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        1 - ((d + 1 : ℕ) : ℝ) * x ≤ (1 - (d : ℝ) * x) * (1 - x) := by
          push_cast
          nlinarith [sq_nonneg x]
        _ ≤ (1 - x) ^ d * (1 - x) :=
          mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hx1)
        _ = (1 - x) ^ (d + 1) := by rw [pow_succ]

theorem expTail_square_tendsto (P : Params9) (hP : P.Valid) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * P.tail c n) atTop (nhds 0) := by
  have hu : 0 < P.u := by
    have hxs : (0 : ℝ) < (P.xS : ℝ) := by exact_mod_cast hP.1.1
    rw [Params9.u]
    linarith
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ P.u) atTop atTop :=
    (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (2 / P.u) c hc).comp ht
  have heq :
      (fun n : ℕ => ((n : ℝ) ^ P.u) ^ (2 / P.u) *
        Real.exp (-c * (n : ℝ) ^ P.u)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2 * P.tail c n) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnNat : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnNat
    have hp : ((n : ℝ) ^ P.u) ^ (2 / P.u) = (n : ℝ) ^ 2 := by
      calc
        ((n : ℝ) ^ P.u) ^ (2 / P.u) = (n : ℝ) ^ (P.u * (2 / P.u)) := by
          rw [← Real.rpow_mul hnpos.le]
        _ = (n : ℝ) ^ (2 : ℝ) := by
          congr 1
          field_simp [ne_of_gt hu] <;> ring
        _ = (n : ℝ) ^ 2 := Real.rpow_natCast (n : ℝ) 2
    simp [Params9.tail, hp]
  exact h.congr' heq

theorem pi_expect_glue {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : ∀ i, FinProb (α i)) (U : Finset ι) (f : (∀ i, α i) → ℝ)
    (ω₀ : ∀ i, α i) (hf : FinProb.DependsOn f U) :
    ∑ a : (∀ i : U, α i.1),
      (∏ i : U, (P i.1).w (a i)) * f (S07.glue U ω₀ a) =
      (FinProb.pi P).expect f := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ U) α
  have hglue (a : ∀ i : U, α i.1) :
      S07.glue U ω₀ a = e.symm (a, fun i : {i // i ∉ U} => ω₀ i.1) := by
    funext i
    by_cases hi : i ∈ U
    · simp [S07.glue, e, hi, Equiv.piEquivPiSubtypeProd]
    · simp [S07.glue, e, hi, Equiv.piEquivPiSubtypeProd]
  calc
    (∑ a : (∀ i : U, α i.1),
        (∏ i : U, (P i.1).w (a i)) * f (S07.glue U ω₀ a)) =
      (FinProb.pi (fun i : {i // i ∈ U} => P i.1)).expect
        (fun a => f (e.symm (a, fun i : {i // i ∉ U} => ω₀ i.1))) := by
      simp only [FinProb.expect, FinProb.pi]
      apply Finset.sum_congr rfl
      intro a ha
      rw [hglue]
    _ = (FinProb.pi P).expect f :=
      (FinProb.pi_expect_depends P U f ω₀ hf).symm

theorem tagLaw_pos_coord (P : Params9) (n N : ℕ) (M : TagMix N)
    (E : Fin N → Fin N → Prop) (G : Colour) (c : ℝ)
    (havoid : 0 < (FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)).pr
      (fun tag => ∀ z, ¬ tagBad9 (P := P) E G c tag z))
    (tag : CubeVertex (P.m n) → M.ι)
    (htag : 0 < (tagLaw9 P n M E G c).w tag) (z : CubeVertex (P.m n)) :
    0 < M.Λ (tag z) := by
  classical
  let raw : FinProb (CubeVertex (P.m n) → M.ι) :=
    FinProb.pi (fun _ : CubeVertex (P.m n) => tagMixLaw9 M)
  let good : (CubeVertex (P.m n) → M.ι) → Prop :=
    fun t => ∀ z, ¬ tagBad9 (P := P) E G c t z
  have hqeq : tagLaw9 P n M E G c = raw.cond good havoid := by
    change S07.condOr raw good = raw.cond good havoid
    unfold S07.condOr
    rw [dif_pos havoid]
  have hgood : good tag := by
    rw [hqeq, FinProb.cond] at htag
    by_contra hnot
    simp [FinProb.cond, hnot] at htag
  have hrawpos : 0 < raw.w tag := by
    rw [hqeq, FinProb.cond] at htag
    have hquot : 0 < raw.w tag / raw.pr good := by simpa [hgood] using htag
    exact (div_pos_iff_of_pos_right havoid).mp hquot
  have hcoord : 0 < (tagMixLaw9 M).w (tag z) := by
    by_contra hnot
    have hz : (tagMixLaw9 M).w (tag z) = 0 :=
      le_antisymm (not_lt.mp hnot) ((tagMixLaw9 M).nonneg _)
    have hzero : raw.w tag = 0 := by
      dsimp [raw, FinProb.pi]
      exact Finset.prod_eq_zero (Finset.mem_univ z) (by simpa [tagMixLaw9] using hz)
    exact (ne_of_gt hrawpos) hzero
  simpa [tagMixLaw9] using hcoord

theorem rpow_ratio_tendsto (a b : ℝ) (hab : a < b) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  have heq : (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(b - a))) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
    calc
      (n : ℝ) ^ a / (n : ℝ) ^ b = (n : ℝ) ^ (a - b) := (Real.rpow_sub hnpos a b).symm
      _ = (n : ℝ) ^ (-(b - a)) := by congr 1 <;> ring
  exact h.congr' heq.symm

theorem inv_rpow_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  have heq : (fun n : ℕ => 1 / (n : ℝ) ^ a) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-a)) := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
    simp [one_div, Real.rpow_neg hnpos.le]
  exact h.congr' heq.symm

theorem basic_m_le_n_eventually_q_s09_tag (P : Params9) (hP : P.Valid) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 ≤ n ∧ P.m n ≤ n := by
  classical
  refine ⟨1, ?_⟩
  intro n hn
  refine ⟨hn, ?_⟩
  cases hcase : P.case with
  | sub yS yD yM =>
      have hsub : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
          1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      have hσ : (0 : ℝ) < (P.σ : ℝ) := by exact_mod_cast hP.2.2.2.1.1
      have hyM : (yM : ℝ) ≤ 1 := by
        have hlt : yM < 1 - P.σ := hsub.2.2.1
        have hcast : (yM : ℝ) < 1 - (P.σ : ℝ) := by exact_mod_cast hlt
        linarith
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpow : (n : ℝ) ^ (yM : ℝ) ≤ (n : ℝ) := by
        calc
          (n : ℝ) ^ (yM : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hnR hyM
          _ = (n : ℝ) := by simp
      have hfloor : (P.m n : ℝ) ≤ (n : ℝ) := by
        rw [Params9.m, hcase]
        exact (Nat.floor_le (by positivity)).trans hpow
      exact_mod_cast hfloor
  | lin αS αD hB yB =>
      have hlin : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
          P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      have hαD : (αD : ℝ) / 10 ≤ 1 := by
        have hcast : (αD : ℝ) < (((1 : ℚ) / 100 : ℚ) : ℝ) :=
          Rat.cast_lt.mpr hlin.2.2.1
        have hcast' : (((1 : ℚ) / 100 : ℚ) : ℝ) = (1 : ℝ) / 100 := by norm_num
        rw [hcast'] at hcast
        linarith
      have hαDpos : 0 < (αD : ℝ) := by
        have h100 : (0 : ℝ) < ((100 * αS : ℚ) : ℝ) := by exact_mod_cast hlin.1
        have hnext : ((100 * αS : ℚ) : ℝ) < (αD : ℝ) := by exact_mod_cast hlin.2.1
        exact lt_trans h100 hnext
      have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have harg : (αD : ℝ) * (n : ℝ) / 10 ≤ (n : ℝ) := by
        calc
          (αD : ℝ) * (n : ℝ) / 10 = ((αD : ℝ) / 10) * (n : ℝ) := by ring
          _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hαD hnR
          _ = (n : ℝ) := by ring
      have hfloor : (P.m n : ℝ) ≤ (n : ℝ) := by
        rw [Params9.m, hcase]
        exact (Nat.floor_le (by positivity [hαDpos])).trans harg
      exact_mod_cast hfloor

theorem tagWidth_over_rpow_tendsto (P : Params9) (a : ℝ) (ha : 0 < a)
    (hxa : (P.xS : ℝ) < a) :
    Tendsto
      (fun n : ℕ =>
        ((n : ℝ) ^ (P.xS : ℝ) + ((P.hPlus : ℝ) + 1) * Real.log (n : ℝ) + 1) /
          (n : ℝ) ^ a) atTop (nhds 0) := by
  have hpow := rpow_ratio_tendsto (P.xS : ℝ) a hxa
  have hlog :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hone := inv_rpow_tendsto a ha
  have hsum : Tendsto (fun n : ℕ =>
      (n : ℝ) ^ (P.xS : ℝ) / (n : ℝ) ^ a +
        ((P.hPlus : ℝ) + 1) *
          (Real.log (n : ℝ) / (n : ℝ) ^ a) + 1 / (n : ℝ) ^ a) atTop (nhds 0) := by
    simpa [add_assoc] using
      Tendsto.add hpow (Tendsto.add (Tendsto.const_mul ((P.hPlus : ℝ) + 1) hlog) hone)
  have heq :
      (fun n : ℕ =>
        ((n : ℝ) ^ (P.xS : ℝ) + ((P.hPlus : ℝ) + 1) * Real.log (n : ℝ) + 1) /
          (n : ℝ) ^ a) =ᶠ[atTop]
      (fun n : ℕ =>
        (n : ℝ) ^ (P.xS : ℝ) / (n : ℝ) ^ a +
          ((P.hPlus : ℝ) + 1) *
            (Real.log (n : ℝ) / (n : ℝ) ^ a) + 1 / (n : ℝ) ^ a) := by
    filter_upwards with n
    ring
  exact hsum.congr' heq.symm

set_option maxHeartbeats 0 in
theorem tag_first_width_budget (P : Params9) (hP : P.Valid) (hA : P.CoreAdmissible) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) * Real.log (n : ℝ) + 1 + Real.log (n : ℝ) ≤
        (P.m n : ℝ) * Real.log 2 := by
  classical
  have hxSlt1 : (P.xS : ℝ) < 1 := by
    have hxsxD : (P.xS : ℝ) < (P.xD : ℝ) := by exact_mod_cast hP.1.2.1
    have hxD : (P.xD : ℝ) < (1 : ℝ) / 10 := by
      have hq : P.xD < (1 : ℚ) / 10 := hP.1.2.2
      calc
        (P.xD : ℝ) < (((1 : ℚ) / 10 : ℚ) : ℝ) := Rat.cast_lt.mpr hq
        _ = (1 : ℝ) / 10 := by norm_num
    linarith
  let W : ℕ → ℝ := fun n =>
    (n : ℝ) ^ (P.xS : ℝ) + ((P.hPlus : ℝ) + 1) * Real.log (n : ℝ) + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  cases hcase : P.case with
  | sub yS yD yM =>
      have hsub : 0 < yS ∧ yS < yM ∧ yM < 1 - P.σ ∧
          1 - P.σ < yD ∧ yD < 1 ∧ P.χ < P.σ / 10 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      have hxyQ : P.xS < yM := by
        simpa [Params9.CoreAdmissible, hcase] using hA
      have hxy : (P.xS : ℝ) < (yM : ℝ) := by exact_mod_cast hxyQ
      have hy : 0 < (yM : ℝ) := by
        exact_mod_cast (lt_trans hsub.1 hsub.2.1)
      have hWlim := tagWidth_over_rpow_tendsto P (yM : ℝ) hy hxy
      have hInv := inv_rpow_tendsto (yM : ℝ) hy
      have hWsmall : ∀ᶠ n : ℕ in Filter.atTop,
          W n / (n : ℝ) ^ (yM : ℝ) < Real.log 2 / 2 :=
        hWlim.eventually (Iio_mem_nhds (by positivity))
      have hInvsmall : ∀ᶠ n : ℕ in Filter.atTop,
          1 / (n : ℝ) ^ (yM : ℝ) < 1 / 2 :=
        hInv.eventually (Iio_mem_nhds (by norm_num))
      obtain ⟨nW, hW⟩ := Filter.eventually_atTop.mp hWsmall
      obtain ⟨nI, hI⟩ := Filter.eventually_atTop.mp hInvsmall
      refine ⟨max nW (max nI 1), ?_⟩
      intro n hn
      have hnW : nW ≤ n := le_trans (le_max_left _ _) hn
      have hnI : nI ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
      have hWn := hW n hnW
      have hIn := hI n hnI
      have hBpos : 0 < (n : ℝ) ^ (yM : ℝ) :=
        Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn1)) _
      have hWscaled : W n < (Real.log 2 / 2) * (n : ℝ) ^ (yM : ℝ) :=
        (div_lt_iff₀ hBpos).mp hWn
      have hBgt2 : 2 < (n : ℝ) ^ (yM : ℝ) := by
        have h := (div_lt_iff₀ hBpos).mp hIn
        nlinarith
      have hmargin : Real.log 2 < (Real.log 2 / 2) * (n : ℝ) ^ (yM : ℝ) := by
        nlinarith [mul_pos hlog2 (sub_pos.mpr hBgt2)]
      have hWfloor : W n + Real.log 2 < (n : ℝ) ^ (yM : ℝ) * Real.log 2 := by
        nlinarith
      have hfloorCast : (n : ℝ) ^ (yM : ℝ) - 1 < (P.m n : ℝ) := by
        have hf : (n : ℝ) ^ (yM : ℝ) < (P.m n : ℝ) + 1 := by
          simpa [Params9.m, hcase] using (Nat.lt_floor_add_one ((n : ℝ) ^ (yM : ℝ)))
        linarith
      have hfinal : W n < (P.m n : ℝ) * Real.log 2 := by
        have hfloorLog := mul_lt_mul_of_pos_right hfloorCast hlog2
        nlinarith [hWfloor, hfloorLog]
      have hWunfold : W n = (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) *
          Real.log (n : ℝ) + 1 + Real.log (n : ℝ) := by
        dsimp [W]
        ring
      rw [← hWunfold]
      exact hfinal.le
  | lin αS αD hB yB =>
      have hlin : 0 < 100 * αS ∧ 100 * αS < αD ∧ αD < 1 / 100 ∧
          P.σ < P.χ / 10 ∧ P.hPlus < hB ∧ hB < 1 ∧ 0 < yB ∧ yB < 1 := by
        simpa [hcase] using hP.2.2.2.2.2.2
      have hαD : 0 < (αD : ℝ) := by
        have hαS_q : (0 : ℚ) < αS := by nlinarith [hlin.1]
        have hαS : (0 : ℝ) < (αS : ℝ) := by exact_mod_cast hαS_q
        have h2 : (100 * αS : ℝ) < (αD : ℝ) := by exact_mod_cast hlin.2.1
        exact lt_trans (mul_pos (by norm_num : (0 : ℝ) < 100) hαS) h2
      let cD : ℝ := (αD : ℝ) / 10
      have hcD : 0 < cD := by dsimp [cD]; positivity
      have hWlim := tagWidth_over_rpow_tendsto P 1 one_pos hxSlt1
      have hWsmall : ∀ᶠ n : ℕ in Filter.atTop,
          W n / (n : ℝ) < cD * Real.log 2 / 2 :=
        by
          simpa only [Real.rpow_one] using
            hWlim.eventually (Iio_mem_nhds (by positivity))
      have hInvsmall : ∀ᶠ n : ℕ in Filter.atTop,
          1 / (n : ℝ) < cD / 2 := by
        have hInv := inv_rpow_tendsto 1 one_pos
        have hInv' : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
          simpa only [Real.rpow_one] using hInv
        exact hInv'.eventually (Iio_mem_nhds (by positivity))
      obtain ⟨nW, hW⟩ := Filter.eventually_atTop.mp hWsmall
      obtain ⟨nI, hI⟩ := Filter.eventually_atTop.mp hInvsmall
      refine ⟨max nW (max nI 1), ?_⟩
      intro n hn
      have hnW : nW ≤ n := le_trans (le_max_left _ _) hn
      have hnI : nI ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
      have hn1 : 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
      have hWn := hW n hnW
      have hIn := hI n hnI
      have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn1)
      have hBpos : 0 < (n : ℝ) * cD := mul_pos hnR hcD
      have hWscaled : W n < (cD * Real.log 2 / 2) * (n : ℝ) :=
        (div_lt_iff₀ hnR).mp hWn
      have hBgt2 : 2 < (n : ℝ) * cD := by
        have h := (div_lt_iff₀ hnR).mp hIn
        nlinarith
      have hmargin : Real.log 2 < (Real.log 2 / 2) * ((n : ℝ) * cD) := by
        nlinarith [mul_pos hlog2 (sub_pos.mpr hBgt2)]
      have hWfloor : W n + Real.log 2 < ((n : ℝ) * cD) * Real.log 2 := by
        nlinarith
      have hfloorCast : (n : ℝ) * cD - 1 < (P.m n : ℝ) := by
        have hf : (n : ℝ) * cD < (P.m n : ℝ) + 1 := by
          rw [Params9.m, hcase]
          calc
            (n : ℝ) * cD = (αD : ℝ) * (n : ℝ) / 10 := by
              dsimp [cD]
              ring
            _ < (⌊(αD : ℝ) * (n : ℝ) / 10⌋₊ : ℝ) + 1 :=
              Nat.lt_floor_add_one _
        linarith
      have hfloorLog := mul_lt_mul_of_pos_right hfloorCast hlog2
      have hfinal : W n < (P.m n : ℝ) * Real.log 2 := by
        nlinarith [hWfloor, hfloorLog]
      have hWunfold : W n = (n : ℝ) ^ (P.xS : ℝ) + (P.hPlus : ℝ) *
          Real.log (n : ℝ) + 1 + Real.log (n : ℝ) := by
        dsimp [W]
        ring
      rw [← hWunfold]
      exact hfinal.le

noncomputable def tagRowCoords_q_s09_tag {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n) : Finset (I.ID ⊕ OddSites9 n) :=
  insert (Sum.inr b) (tagAnchorSites_q_s09_tag I)

private theorem tagRowCoords_anchor_mem {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n) (c : I.ID) :
    Sum.inl c ∈ tagRowCoords_q_s09_tag I b := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩

private theorem tagRowCoords_mask_mem {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n) : Sum.inr b ∈ tagRowCoords_q_s09_tag I b :=
  Finset.mem_insert_self _ _

private def tagRowCoordsToPair_q_s09_tag {P : Params9} {n N : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n)
    (x : ∀ i : tagRowCoords_q_s09_tag I b, Val9 I N i.1) :
    (∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1) × Finset (Fin N) :=
  (fun i => x ⟨i.1, Finset.mem_insert_of_mem i.2⟩,
    x ⟨Sum.inr b, tagRowCoords_mask_mem I b⟩)

private def tagRowCoordsFromPair_q_s09_tag {P : Params9} {n N : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n)
    (q : (∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1) × Finset (Fin N)) :
    ∀ i : tagRowCoords_q_s09_tag I b, Val9 I N i.1 := fun i =>
  match i.1 with
  | Sum.inl c => q.1 ⟨Sum.inl c,
      Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
  | Sum.inr b' => if b' = b then q.2 else (∅ : Finset (Fin N))

noncomputable def tagRowCoordsEquiv_q_s09_tag {P : Params9} {n N : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n) :
    (∀ i : tagRowCoords_q_s09_tag I b, Val9 I N i.1) ≃
      ((∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1) × Finset (Fin N)) where
  toFun := tagRowCoordsToPair_q_s09_tag I b
  invFun := tagRowCoordsFromPair_q_s09_tag I b
  left_inv := by
    intro x
    funext i
    rcases i with ⟨v, hv⟩
    cases v with
    | inl c => simp [tagRowCoordsToPair_q_s09_tag, tagRowCoordsFromPair_q_s09_tag]
    | inr b' =>
        have hb : b' = b := by
          rcases Finset.mem_insert.mp hv with heq | hanc
          · exact Sum.inr.inj heq
          · rcases Finset.mem_image.mp hanc with ⟨c, _, hc⟩
            cases hc
        subst b'
        simp [tagRowCoordsToPair_q_s09_tag, tagRowCoordsFromPair_q_s09_tag]
  right_inv := by
    rintro ⟨a, A⟩
    apply Prod.ext
    · funext i
      rcases i with ⟨v, hv⟩
      cases v with
      | inl c => simp [tagRowCoordsToPair_q_s09_tag, tagRowCoordsFromPair_q_s09_tag]
      | inr b' =>
          rcases Finset.mem_image.mp hv with ⟨c, _, hc⟩
          cases hc
    · simp [tagRowCoordsToPair_q_s09_tag, tagRowCoordsFromPair_q_s09_tag]

noncomputable def tagRowIndexEquiv_q_s09_tag {P : Params9} {n : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n) :
    tagRowCoords_q_s09_tag I b ≃ I.ID ⊕ PUnit.{1} where
  toFun i :=
    match i.1 with
    | Sum.inl c => Sum.inl c
    | Sum.inr _ => Sum.inr PUnit.unit
  invFun j :=
    match j with
    | Sum.inl c => ⟨Sum.inl c, tagRowCoords_anchor_mem I b c⟩
    | Sum.inr _ => ⟨Sum.inr b, tagRowCoords_mask_mem I b⟩
  left_inv := by
    intro i
    rcases i with ⟨v, hv⟩
    cases v with
    | inl c => rfl
    | inr b' =>
        have hb : b' = b := by
          rcases Finset.mem_insert.mp hv with heq | hanc
          · exact Sum.inr.inj heq
          · rcases Finset.mem_image.mp hanc with ⟨c, _, hc⟩
            cases hc
        subst b'
        rfl
  right_inv := by
    intro j
    cases j with
    | inl c => rfl
    | inr u => rfl

private noncomputable def tagAnchorIndexEquiv_q_s09_tag {P : Params9} {n : ℕ}
    (I : IDMap9 P n) : I.ID ≃ tagAnchorSites_q_s09_tag I where
  toFun c := ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
  invFun i := Classical.choose (Finset.mem_image.mp i.2)
  left_inv c := by
    have hmem : Sum.inl c ∈ tagAnchorSites_q_s09_tag I :=
      Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
    have heq := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    exact Sum.inl.inj heq
  right_inv i := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp i.2)).2

@[simp] theorem tagRowCoordsEquiv_symm_anchor_q_s09_tag {P : Params9} {n N : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n)
    (a : ∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1) (A : Finset (Fin N))
    (c : I.ID) :
    (tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A)
        ⟨Sum.inl c, tagRowCoords_anchor_mem I b c⟩ =
      a ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩ := by
  change tagRowCoordsFromPair_q_s09_tag I b (a, A)
      ⟨Sum.inl c, tagRowCoords_anchor_mem I b c⟩ = _
  simp [tagRowCoordsFromPair_q_s09_tag]

@[simp] theorem tagRowCoordsEquiv_symm_mask_q_s09_tag {P : Params9} {n N : ℕ}
    (I : IDMap9 P n) (b : OddSites9 n)
    (a : ∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1) (A : Finset (Fin N)) :
    (tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A)
        ⟨Sum.inr b, tagRowCoords_mask_mem I b⟩ = A := by
  change tagRowCoordsFromPair_q_s09_tag I b (a, A)
      ⟨Sum.inr b, tagRowCoords_mask_mem I b⟩ = _
  simp [tagRowCoordsFromPair_q_s09_tag]
  rfl

theorem rawRowLaw_eq_mask_mix_q_s09_tag {P : Params9} {n N : ℕ} {M : TagMix N}
    {I : IDMap9 P n} (S : Setup9 P n N M) (E : Fin N → Fin N → Prop) (G : Colour)
    (b : OddSites9 n) :
    rawRowLaw9 S I E G b =
      Law.mix (S.maskLaw b) (fun A => tagActionLaw_q_s09_tag (I := I) S E G b A) := by
  classical
  apply finProb_ext_q_s09_tag
  intro y
  let U := tagRowCoords_q_s09_tag I b
  let anchorP := FinProb.pi
    (fun i : tagAnchorSites_q_s09_tag I => inputLaw9 S I i.1)
  let f : Outcome9 I N → ℝ := fun ω => (rowLaw9 S E G ω b).w y
  let ω₀ : Outcome9 I N := Classical.choice
    (finProb_nonempty_q_s09_tag (FinProb.pi (inputLaw9 S I)))
  have hf : FinProb.DependsOn f U := by
    intro ω ω' hagree
    apply congrArg (fun μ : Law N => μ.w y)
    apply rowLaw9_ext_q_s09_tag S E G b
    · intro c
      exact hagree (Sum.inl c) (tagRowCoords_anchor_mem I b c)
    · exact hagree (Sum.inr b) (tagRowCoords_mask_mem I b)
  have hglue := pi_expect_glue (inputLaw9 S I) U f ω₀ hf
  have hleft : (rawRowLaw9 S I E G b).w y = (FinProb.pi (inputLaw9 S I)).expect f := by
    simp [rawRowLaw9, Law.mix, rawLaw9, FinProb.expect, f]
  rw [hleft, ← hglue]
  change (∑ x : (∀ i : U, Val9 I N i.1),
      (∏ i : U, (inputLaw9 S I i.1).w (x i)) * f (S07.glue U ω₀ x)) = _
  rw [← Equiv.sum_comp (tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm
      (fun x => (∏ i : U, (inputLaw9 S I i.1).w (x i)) * f (S07.glue U ω₀ x))]
  rw [Fintype.sum_prod_type]
  change (∑ a : (∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1),
      ∑ A : Finset (Fin N),
        (∏ i : U, (inputLaw9 S I i.1).w
          ((tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A) i)) *
          f (S07.glue U ω₀ ((tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A)))) = _
  simp only [FinProb.expect, anchorP, tagActionLaw_q_s09_tag, Law.mix, f]
  have hright :
      (∑ A : Finset (Fin N), (S.maskLaw b).w A *
        ∑ a : (∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1),
          anchorP.w a * (rowLaw9 S E G (tagAnchorOutcome_q_s09_tag a b A) b).w y) =
      ∑ a : (∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1),
        ∑ A : Finset (Fin N),
          ((S.maskLaw b).w A * anchorP.w a) *
            (rowLaw9 S E G (tagAnchorOutcome_q_s09_tag a b A) b).w y := by
    calc
      _ = ∑ A : Finset (Fin N),
          ∑ a : (∀ i : tagAnchorSites_q_s09_tag I, Val9 I N i.1),
            ((S.maskLaw b).w A * anchorP.w a) *
              (rowLaw9 S E G (tagAnchorOutcome_q_s09_tag a b A) b).w y := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [Finset.sum_comm]
  rw [hright]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro A
  have hweight :
      (∏ i : U, (inputLaw9 S I i.1).w
          ((tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A) i)) =
        (S.maskLaw b).w A * anchorP.w a := by
    let ei := tagRowIndexEquiv_q_s09_tag I b
    let qa := (tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A)
    let g : I.ID ⊕ PUnit.{1} → ℝ := fun j =>
      let i := ei.symm j
      (inputLaw9 S I i.1).w (qa i)
    have hanchor :
        anchorP.w a = ∏ c : I.ID,
          (M.μ (S.tag c.slice)).w
            (a ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩) := by
      symm
      calc
        (∏ c : I.ID, (M.μ (S.tag c.slice)).w
            (a ⟨Sum.inl c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩)) =
            ∏ i : tagAnchorSites_q_s09_tag I, (inputLaw9 S I i.1).w (a i) := by
          exact Fintype.prod_equiv (tagAnchorIndexEquiv_q_s09_tag I) _ _ (by
            intro c
            simp [tagAnchorIndexEquiv_q_s09_tag, inputLaw9])
        _ = anchorP.w a := by simp [anchorP, FinProb.pi]
    calc
      (∏ i : U, (inputLaw9 S I i.1).w (qa i)) =
          ∏ j : I.ID ⊕ PUnit.{1}, g j :=
        Fintype.prod_equiv ei _ _ (by
          intro j
          dsimp [g]
          rw [ei.symm_apply_apply])
      _ = (S.maskLaw b).w A * anchorP.w a := by
        rw [Fintype.prod_sum_type]
        simp [g, ei, tagRowIndexEquiv_q_s09_tag, qa,
          tagRowCoordsEquiv_symm_anchor_q_s09_tag, tagRowCoordsEquiv_symm_mask_q_s09_tag,
          inputLaw9, hanchor, mul_comm]
  have hrowLaw :
      rowLaw9 S E G (S07.glue U ω₀ ((tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A))) b =
        rowLaw9 S E G (tagAnchorOutcome_q_s09_tag a b A) b := by
    apply rowLaw9_ext_q_s09_tag S E G b
    · intro c
      dsimp [anc9]
      change (S07.glue (tagRowCoords_q_s09_tag I b) ω₀
          ((tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A))) (Sum.inl c) = _
      rw [S07.glue]
      simp only [dif_pos (tagRowCoords_anchor_mem I b c)]
      exact tagRowCoordsEquiv_symm_anchor_q_s09_tag I b a A c
    · dsimp [msk9]
      change (S07.glue (tagRowCoords_q_s09_tag I b) ω₀
          ((tagRowCoordsEquiv_q_s09_tag (N := N) I b).symm (a, A))) (Sum.inr b) = _
      rw [S07.glue]
      simp only [dif_pos (tagRowCoords_mask_mem I b)]
      rw [tagRowCoordsEquiv_symm_mask_q_s09_tag]
      simp [tagAnchorOutcome_q_s09_tag]
      rfl
  rw [hweight, hrowLaw]

end HypercubeRamsey.Lane_q_s09_tag
