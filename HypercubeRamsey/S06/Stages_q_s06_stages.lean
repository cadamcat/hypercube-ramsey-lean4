import HypercubeRamsey.S06.Defs
import HypercubeRamsey.S06.Experiment
import HypercubeRamsey.S06.Step3Defs
import HypercubeRamsey.S03.ConditionalAvoidance
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_q_s06_stages

open Classical
open HypercubeRamsey.S06

theorem tagWeight_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (S : Finset X.HKey)
    (i : X.ι) (Z Z' : X.Hid) (hS : S ⊆ β.obs)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tagWeight (base, Z) β S i = X.tagWeight (base, Z') β S i := by
  unfold Ctx6.tagWeight
  have hprod : (∏ ℓ ∈ S,
      safeRatio6 ((X.hidPostRep base ℓ.1 β.key i).w (Z ℓ))
        ((X.hidPostDel base ℓ.1 β.key).w (Z ℓ))) =
      ∏ ℓ ∈ S,
        safeRatio6 ((X.hidPostRep base ℓ.1 β.key i).w (Z' ℓ))
          ((X.hidPostDel base ℓ.1 β.key).w (Z' ℓ)) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hZ ℓ (hS hℓ)]
  rw [hprod]

theorem tagMass_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (S : Finset X.HKey)
    (Z Z' : X.Hid) (hS : S ⊆ β.obs) (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tagMass (base, Z) β S = X.tagMass (base, Z') β S := by
  unfold Ctx6.tagMass
  apply Finset.sum_congr rfl
  intro i hi
  exact tagWeight_eq_of_agree X base β S i Z Z' hS hZ

theorem step2Tests_iff_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (Z Z' : X.Hid)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.Step2Tests (base, Z) β ↔ X.Step2Tests (base, Z') β := by
  have hfull : X.tagMass (base, Z) β β.obs = X.tagMass (base, Z') β β.obs :=
    tagMass_eq_of_agree X base β β.obs Z Z' (by intro ℓ hℓ; exact hℓ) hZ
  have hdel : ∀ ℓ ∈ β.obs,
      X.tagMass (base, Z) β (β.obs.erase ℓ) =
        X.tagMass (base, Z') β (β.obs.erase ℓ) := by
    intro ℓ hℓ
    apply tagMass_eq_of_agree X base β (β.obs.erase ℓ) Z Z'
    · intro j hj
      exact (Finset.mem_erase.mp hj).2
    · exact hZ
  unfold Ctx6.Step2Tests
  rw [hfull]
  constructor
  · rintro ⟨hpos, hthr, hdel'⟩
    refine ⟨hpos, hthr, ?_⟩
    intro ℓ hℓ
    rw [← hdel ℓ hℓ]
    exact hdel' ℓ hℓ
  · rintro ⟨hpos, hthr, hdel'⟩
    refine ⟨hpos, hthr, ?_⟩
    intro ℓ hℓ
    rw [hdel ℓ hℓ]
    exact hdel' ℓ hℓ

theorem step2Fail_iff_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (Z Z' : X.Hid)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.Step2Fail (base, Z) β ↔ X.Step2Fail (base, Z') β := by
  have htests := step2Tests_iff_of_agree X base β Z Z' hZ
  have hprop : X.Step2Tests (base, Z) β = X.Step2Tests (base, Z') β := propext htests
  simp only [Ctx6.Step2Fail, hprop]

private theorem finprob_eq_of_weights_eq {Ω : Type*} [Fintype Ω]
    {P Q : FinProb Ω} (hw : ∀ ω, P.w ω = Q.w ω) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq ht =>
      have hpw : pw = qw := funext hw
      subst qw
      have hproof : hp = hq := Subsingleton.elim _ _
      have hsum : hs = ht := Subsingleton.elim _ _
      cases hproof
      cases hsum
      rfl

theorem tagPost_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (S : Finset X.HKey)
    (Z Z' : X.Hid) (hS : S ⊆ β.obs) (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tagPost (base, Z) β S = X.tagPost (base, Z') β S := by
  apply finprob_eq_of_weights_eq
  intro i
  change (normalize6 (X.tagWeight (base, Z) β S) X.i₀).w i =
    (normalize6 (X.tagWeight (base, Z') β S) X.i₀).w i
  have hfun : X.tagWeight (base, Z) β S = X.tagWeight (base, Z') β S := by
    funext i
    exact tagWeight_eq_of_agree X base β S i Z Z' hS hZ
  rw [hfun]

theorem labelLaw_eq_of_name_values
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (S : Finset X.Name) (i : X.ι)
    (Z Z' : X.Hid)
    (hval : ∀ nm ∈ S, X.varVal (base, Z) nm = X.varVal (base, Z') nm) :
    X.labelLaw (base, Z) S i = X.labelLaw (base, Z') S i := by
  have hreq : X.reqNbhd (base, Z) S = X.reqNbhd (base, Z') S := by
    ext x
    unfold Ctx6.reqNbhd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h nm hnm
    · rw [← hval nm hnm]
      exact h nm hnm
    · rw [hval nm hnm]
      exact h nm hnm
  unfold Ctx6.labelLaw
  rw [hreq]

theorem labelLaw_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (i : X.ι)
    (Z Z' : X.Hid) (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.labelLaw (base, Z) (reqNames6 β) i = X.labelLaw (base, Z') (reqNames6 β) i := by
  apply labelLaw_eq_of_name_values X base (reqNames6 β) i Z Z'
  intro nm hnm
  cases nm with
  | par p => rfl
  | hid ℓ =>
    have hℓ : ℓ ∈ β.obs := by
      by_cases hm : β.mode = .high
      · simpa [reqNames6, hm] using hnm
      · simpa [reqNames6, hm] using hnm
    exact hZ ℓ hℓ

theorem tupleLaw_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (β : X.Ty) (Z Z' : X.Hid)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.tupleLaw (base, Z) β = X.tupleLaw (base, Z') β := by
  have htag := tagPost_eq_of_agree X base β β.obs Z Z' (by intro ℓ hℓ; exact hℓ) hZ
  have hlabel : ∀ i,
      X.labelLaw (base, Z) (reqNames6 β) i = X.labelLaw (base, Z') (reqNames6 β) i := by
    intro i
    exact labelLaw_eq_of_agree X base β i Z Z' hZ
  apply finprob_eq_of_weights_eq
  intro tup
  simp [Ctx6.tupleLaw, Ctx6.tupleLawOn, Ctx6.Tβ, FinProb.bind, FinProb.pi, htag, hlabel]

theorem tupleRatio_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (baseA baseB : X.Base) (β : X.Ty)
    (Zξ Zξ' Z Z' : X.Hid) (hξ : ∀ ℓ ∈ β.obs, Zξ ℓ = Zξ' ℓ)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) (refTag refTag' : FinProb X.ι)
    (href : refTag = refTag') (drop : X.Name) (o : X.Tuple) :
    X.tupleRatio (baseA, Zξ) (baseB, Z) β refTag drop o =
      X.tupleRatio (baseA, Zξ') (baseB, Z') β refTag' drop o := by
  have htag := tagPost_eq_of_agree X baseA β β.obs Zξ Zξ'
    (by intro ℓ hℓ; exact hℓ) hξ
  have hvalξ : ∀ nm ∈ reqNames6 β,
      X.varVal (baseA, Zξ) nm = X.varVal (baseA, Zξ') nm := by
    intro nm hnm
    cases nm with
    | par p => rfl
    | hid ℓ =>
      have hℓ : ℓ ∈ β.obs := by
        by_cases hm : β.mode = .high
        · simpa [reqNames6, hm] using hnm
        · simpa [reqNames6, hm] using hnm
      exact hξ ℓ hℓ
  have hlabelξ : X.labelLaw (baseA, Zξ) (reqNames6 β) o.1 =
      X.labelLaw (baseA, Zξ') (reqNames6 β) o.1 :=
    labelLaw_eq_of_name_values X baseA (reqNames6 β) o.1 Zξ Zξ' hvalξ
  have hval : ∀ nm ∈ reqNames6 β,
      X.varVal (baseB, Z) nm = X.varVal (baseB, Z') nm := by
    intro nm hnm
    cases nm with
    | par p => rfl
    | hid ℓ =>
      have hℓ : ℓ ∈ β.obs := by
        by_cases hm : β.mode = .high
        · simpa [reqNames6, hm] using hnm
        · simpa [reqNames6, hm] using hnm
      exact hZ ℓ hℓ
  have hlabelDel : X.labelLaw (baseB, Z) ((reqNames6 β).erase drop) o.1 =
      X.labelLaw (baseB, Z') ((reqNames6 β).erase drop) o.1 := by
    apply labelLaw_eq_of_name_values X baseB ((reqNames6 β).erase drop) o.1 Z Z'
    intro nm hnm
    exact hval nm (Finset.mem_erase.mp hnm).2
  have htagW : (X.Tβ (baseA, Zξ) β).w o.1 =
      (X.Tβ (baseA, Zξ') β).w o.1 := by
    exact congrArg (fun P : FinProb X.ι => P.w o.1) (by simpa [Ctx6.Tβ] using htag)
  have hrefW : refTag.w o.1 = refTag'.w o.1 := congrArg (fun P : FinProb X.ι => P.w o.1) href
  unfold Ctx6.tupleRatio
  rw [htagW, hrefW, hlabelξ, hlabelDel]

theorem lowLik_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (b : X.State) (ξ : Fin N)
    (β : X.Ty) (o : X.Tuple) (Z Z' : X.Hid)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.lowLik (base, Z) b ξ β o = X.lowLik (base, Z') b ξ β o := by
  have hξ : ∀ ℓ ∈ β.obs,
      (Function.update Z (X.tgt b) ξ) ℓ = (Function.update Z' (X.tgt b) ξ) ℓ := by
    intro ℓ hℓ
    by_cases hℓt : ℓ = X.tgt b <;> simp [hℓt, hZ ℓ hℓ]
  have htag : X.TβDel (base, Z) β (X.tgt b) = X.TβDel (base, Z') β (X.tgt b) := by
    simpa [Ctx6.TβDel] using tagPost_eq_of_agree X base β (β.obs.erase (X.tgt b))
      Z Z' (Finset.erase_subset _ _) hZ
  unfold Ctx6.lowLik
  change X.tupleRatio (base, Function.update Z (X.tgt b) ξ) (base, Z) β
      (X.TβDel (base, Z) β (X.tgt b)) (.hid (X.tgt b)) o =
    X.tupleRatio (base, Function.update Z' (X.tgt b) ξ) (base, Z') β
      (X.TβDel (base, Z') β (X.tgt b)) (.hid (X.tgt b)) o
  exact tupleRatio_eq_of_agree X base base β
    (Function.update Z (X.tgt b) ξ) (Function.update Z' (X.tgt b) ξ) Z Z'
    hξ hZ _ _ htag (.hid (X.tgt b)) o

theorem highLik_eq_of_agree
    {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (base : X.Base) (b : X.State) (ξ : Fin N)
    (β : X.Ty) (o : X.Tuple) (Z Z' : X.Hid)
    (hZ : ∀ ℓ ∈ β.obs, Z ℓ = Z' ℓ) :
    X.highLik (base, Z) b ξ β o = X.highLik (base, Z') b ξ β o := by
  unfold Ctx6.highLik
  change X.tupleRatio (X.withPar base (X.tgtName b) ξ, Z) (base, Z) β
      (tagLaw6 M) (.par (X.tgtName b)) o =
    X.tupleRatio (X.withPar base (X.tgtName b) ξ, Z') (base, Z') β
      (tagLaw6 M) (.par (X.tgtName b)) o
  exact tupleRatio_eq_of_agree X (X.withPar base (X.tgtName b) ξ) base β
    Z Z' Z Z' hZ hZ (tagLaw6 M) (tagLaw6 M) rfl (.par (X.tgtName b)) o

theorem finprob_pr_eq_expect_indicator {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω => if A ω then 1 else 0) := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω <;> simp [hA]

theorem pi_pr_and_of_disjoint_depends
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (A B : (∀ i, Ω i) → Prop) (s t : Finset ι)
    (hA : FinProb.DependsOn A s) (hB : FinProb.DependsOn B t)
    (hst : Disjoint s t) :
    (FinProb.pi P).pr (fun ω => A ω ∧ B ω) =
      (FinProb.pi P).pr A * (FinProb.pi P).pr B := by
  classical
  letI : DecidablePred A := fun ω => Classical.propDecidable (A ω)
  letI : DecidablePred B := fun ω => Classical.propDecidable (B ω)
  letI : DecidablePred (fun ω => A ω ∧ B ω) :=
    fun ω => Classical.propDecidable (A ω ∧ B ω)
  let f : (∀ i, Ω i) → ℝ := fun ω => if A ω then 1 else 0
  let g : (∀ i, Ω i) → ℝ := fun ω => if B ω then 1 else 0
  have hf : FinProb.DependsOn f s := by
    intro ω ω' hω
    have hprop := hA ω ω' hω
    simpa [f] using congrArg (fun p : Prop => if p then (1 : ℝ) else 0) hprop
  have hg : FinProb.DependsOn g t := by
    intro ω ω' hω
    have hprop := hB ω ω' hω
    simpa [g] using congrArg (fun p : Prop => if p then (1 : ℝ) else 0) hprop
  have hAB : ∀ ω, (if A ω ∧ B ω then 1 else 0) = f ω * g ω := by
    intro ω
    by_cases hAω : A ω <;> by_cases hBω : B ω <;> simp [f, g, hAω, hBω]
  calc
    (FinProb.pi P).pr (fun ω => A ω ∧ B ω) =
        (FinProb.pi P).expect (fun ω => f ω * g ω) := by
          rw [finprob_pr_eq_expect_indicator]
          apply congrArg
          funext ω
          exact hAB ω
    _ = (FinProb.pi P).expect f * (FinProb.pi P).expect g :=
      FinProb.pi_expect_mul_of_disjoint P f g s t hf hg hst
    _ = (FinProb.pi P).pr A * (FinProb.pi P).pr B := by
      rw [← finprob_pr_eq_expect_indicator (FinProb.pi P) A,
        ← finprob_pr_eq_expect_indicator (FinProb.pi P) B]

theorem finprob_pr_finset_mass {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinProb Ω) (A : Finset Ω) :
    LocalLemma.mass P.w A = P.pr (fun ω => ω ∈ A) := by
  classical
  unfold LocalLemma.mass FinProb.pr
  have hfilter : Finset.univ.filter (fun ω : Ω => ω ∈ A) = A := by
    ext ω
    simp
  rw [← hfilter, Finset.sum_filter]
  simp [hfilter]

private theorem finprob_pr_congr_local {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω
  · simp [hA, (hAB ω).mp hA]
  · have hB : ¬ B ω := fun h => hA ((hAB ω).mpr h)
    simp [hA, hB]

theorem pi_local_mass_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (I : Type*) [Fintype I] [DecidableEq I]
    (scope : I → Finset ι) (E : I → Finset (∀ i, Ω i)) (i : I) (S : Finset I)
    (hdep : ∀ j, FinProb.DependsOn (fun ω => ω ∈ E j) (scope j))
    (hremote : ∀ j ∈ S, Disjoint (scope i) (scope j)) :
    LocalLemma.mass (FinProb.pi P).w (E i ∩ LocalLemma.avoid E S) =
      (FinProb.pi P).pr (fun ω => ω ∈ E i) *
        LocalLemma.mass (FinProb.pi P).w (LocalLemma.avoid E S) := by
  classical
  let U : Finset ι := S.biUnion scope
  have hscopeDisj : Disjoint (scope i) U := by
    apply Finset.disjoint_left.mpr
    intro a hai haU
    rcases Finset.mem_biUnion.mp haU with ⟨j, hjS, haj⟩
    exact (Finset.disjoint_left.mp (hremote j hjS)) hai haj
  have havoidDep : FinProb.DependsOn
      (fun ω : ∀ i, Ω i => ∀ j ∈ S, ω ∉ E j) U := by
    intro ω ω' hω
    apply propext
    constructor <;> intro h j hjS
    · intro hmem
      have hEq : (ω ∈ E j) = (ω' ∈ E j) := hdep j ω ω' (by
        intro k hk
        exact hω k (Finset.mem_biUnion.mpr ⟨j, hjS, hk⟩))
      exact h j hjS (hEq.symm ▸ hmem)
    · intro hmem
      have hEq : (ω' ∈ E j) = (ω ∈ E j) := hdep j ω' ω (by
        intro k hk
        exact (hω k (Finset.mem_biUnion.mpr ⟨j, hjS, hk⟩)).symm)
      exact h j hjS (hEq ▸ hmem)
  have hmassAB : LocalLemma.mass (FinProb.pi P).w (E i ∩ LocalLemma.avoid E S) =
      (FinProb.pi P).pr (fun ω => ω ∈ E i ∧ ω ∈ LocalLemma.avoid E S) := by
    rw [finprob_pr_finset_mass]
    apply finprob_pr_congr_local
    intro ω
    simp
  have hmassAvoid : LocalLemma.mass (FinProb.pi P).w (LocalLemma.avoid E S) =
      (FinProb.pi P).pr (fun ω => ω ∈ LocalLemma.avoid E S) :=
    finprob_pr_finset_mass (FinProb.pi P) _
  rw [hmassAB, hmassAvoid]
  calc
    (FinProb.pi P).pr (fun ω => ω ∈ E i ∧ ω ∈ LocalLemma.avoid E S) =
        (FinProb.pi P).pr (fun ω => ω ∈ E i) *
          (FinProb.pi P).pr (fun ω => ∀ j ∈ S, ω ∉ E j) := by
            have hpi := pi_pr_and_of_disjoint_depends P
              (fun ω => ω ∈ E i) (fun ω => ∀ j ∈ S, ω ∉ E j) (scope i) U
              (hdep i) havoidDep hscopeDisj
            simpa [LocalLemma.avoid] using hpi
    _ = (FinProb.pi P).pr (fun ω => ω ∈ E i) *
          (FinProb.pi P).pr (fun ω => ω ∈ LocalLemma.avoid E S) := by
        congr 1
        apply finprob_pr_congr_local
        intro ω
        simp [LocalLemma.avoid]

theorem restrictOr6_weight_of_pos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω₀ ω : Ω) (hA : 0 < P.pr A) :
    (restrictOr6 P A ω₀).w ω = (if A ω then P.w ω else 0) / P.pr A := by
  classical
  have hsum : (∑ ω, max 0 (if A ω then P.w ω else 0)) = P.pr A := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : A x
    · simp [h, max_eq_right (P.nonneg x)]
    · simp [h]
  have hmax : ∀ x, max 0 (if A x then P.w x else 0) = if A x then P.w x else 0 := by
    intro x
    split_ifs <;> simp [P.nonneg]
  unfold restrictOr6
  have hpos : 0 < ∑ x, max 0 (if A x then P.w x else 0) := by
    rw [hsum]
    exact hA
  rw [normalize6, dif_pos hpos]
  change max 0 (if A ω then P.w ω else 0) /
      (∑ x, max 0 (if A x then P.w x else 0)) =
    (if A ω then P.w ω else 0) / P.pr A
  rw [hmax ω, hsum]

theorem restrictOr6_support_of_pos {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) (ω₀ ω : Ω) (hA : 0 < P.pr A)
    (hω : (restrictOr6 P A ω₀).w ω ≠ 0) : A ω ∧ P.w ω ≠ 0 := by
  rw [restrictOr6_weight_of_pos P A ω₀ ω hA] at hω
  constructor
  · by_contra h
    simp [h] at hω
  · by_contra h
    have hnum : (if A ω then P.w ω else 0) = 0 := by
      split_ifs with hAω
      · exact h
      · rfl
    rw [hnum] at hω
    simp at hω

theorem pi_support_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (ω : ∀ i, Ω i) (hω : (FinProb.pi P).w ω ≠ 0) :
    ∀ i, (P i).w (ω i) ≠ 0 := by
  classical
  have hprod : (∏ i, (P i).w (ω i)) ≠ 0 := by
    simpa [FinProb.pi] using hω
  intro i
  exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)

theorem bind_support_factors {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (ab : α × β)
    (hab : (FinProb.bind P K).w ab ≠ 0) : P.w ab.1 ≠ 0 ∧ (K ab.1).w ab.2 ≠ 0 := by
  exact mul_ne_zero_iff.mp (by simpa [FinProb.bind] using hab)

theorem pr_congr {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω
  · have hB := (hAB ω).mp hA
    simp [hA, hB]
  · have hB : ¬ B ω := fun h => hA ((hAB ω).mpr h)
    simp [hA, hB]

theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact P.nonneg ω
  · exact le_rfl

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simpa [hA, hB] using P.nonneg ω
    · simp [hA, hB]

private noncomputable def avoidEventFilter {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I]
    (E : I → Finset Ω) : Finset Ω :=
  @Finset.filter Ω (fun ω => ∀ i ∈ (Finset.univ : Finset I), ω ∉ E i)
    (fun ω => Classical.propDecidable _) Finset.univ

theorem avoid_mass_eq_pr {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I] (P : FinProb Ω) (E : I → Finset Ω) :
    LocalLemma.mass P.w (LocalLemma.avoid E Finset.univ) =
      P.pr (fun ω => ∀ i ∈ (Finset.univ : Finset I), ω ∉ E i) := by
  classical
  let A : Ω → Prop := fun ω => ∀ i ∈ (Finset.univ : Finset I), ω ∉ E i
  have hfilter : LocalLemma.avoid E Finset.univ = avoidEventFilter E := by
    unfold LocalLemma.avoid avoidEventFilter
    exact (Finset.filter_congr_decidable Finset.univ A
      (fun ω => Classical.propDecidable (A ω))).symm
  calc
    LocalLemma.mass P.w (LocalLemma.avoid E Finset.univ) =
        (avoidEventFilter E).sum P.w := by
          unfold LocalLemma.mass
          rw [hfilter]
    _ = P.pr A := by
      symm
      simp [FinProb.pr, A, avoidEventFilter, Finset.sum_filter]

theorem bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1 ab.2) =
      P.expect (fun a => (K a).pr (A a)) := by
  classical
  simp only [FinProb.pr, FinProb.bind, FinProb.expect, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : A a b <;> simp [h, mul_comm]

theorem pr_exists_finset_le {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] (P : FinProb Ω) (S : Finset ι) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, P.pr (A i) := by
  classical
  letI : DecidablePred (fun ω => ∃ i ∈ S, A i ω) :=
    fun ω => Classical.propDecidable (∃ i ∈ S, A i ω)
  have hpr : P.pr (fun ω => ∃ i ∈ S, A i ω) =
      ∑ ω, if (∃ i ∈ S, A i ω) then P.w ω else 0 := rfl
  rw [hpr]
  calc
    (∑ ω, if ∃ i ∈ S, A i ω then P.w ω else 0) ≤
        ∑ ω, ∑ i ∈ S, if A i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i ∈ S, A i ω
      · obtain ⟨i, hiS, hiA⟩ := hex
        calc
          (if ∃ i ∈ S, A i ω then P.w ω else 0) = P.w ω := if_pos ⟨i, hiS, hiA⟩
          _ ≤ ∑ i ∈ S, if A i ω then P.w ω else 0 :=
            calc
              P.w ω = (if A i ω then P.w ω else 0) := (if_pos hiA).symm
              _ ≤ ∑ j ∈ S, if A j ω then P.w ω else 0 :=
                Finset.single_le_sum (f := fun j : ι => if A j ω then P.w ω else 0) (a := i)
                  (fun j hj => by
                    split_ifs
                    · exact P.nonneg ω
                    · exact le_rfl) hiS
      · simp only [if_neg hex]
        exact Finset.sum_nonneg fun i hi => by
          split_ifs
          · exact P.nonneg ω
          · exact le_rfl
    _ = ∑ i ∈ S, (∑ ω, if A i ω then P.w ω else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ S, P.pr (A i) := by simp [FinProb.pr]

theorem pr_exists_shape_le {Ω I Sh : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype Sh] [DecidableEq Sh] (P : FinProb Ω) (S : Finset I) (shape : I → Sh)
    (F : Ω → I → ℝ) (t : ℝ)
    (hshape : ∀ i j, shape i = shape j → ∀ ω, F ω i = F ω j) :
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
      ∑ s : {s // s ∈ S.image shape}, P.pr (fun ω => t ≤ F ω (Classical.choose (Finset.mem_image.mp s.2))) := by
  classical
  let rep : {s // s ∈ S.image shape} → I := fun s => Classical.choose (Finset.mem_image.mp s.2)
  have hrep : ∀ s : {s // s ∈ S.image shape}, rep s ∈ S ∧ shape (rep s) = s.1 := by
    intro s
    exact Classical.choose_spec (Finset.mem_image.mp s.2)
  have hsub : ∀ ω, (∃ i ∈ S, t ≤ F ω i) →
      ∃ s : {s // s ∈ S.image shape}, t ≤ F ω (rep s) := by
    intro ω hω
    obtain ⟨i, hiS, hiF⟩ := hω
    let s : {s // s ∈ S.image shape} := ⟨shape i, Finset.mem_image.mpr ⟨i, hiS, rfl⟩⟩
    refine ⟨s, ?_⟩
    have hs : shape i = shape (rep s) := by
      calc
        shape i = s.1 := rfl
        _ = shape (rep s) := (hrep s).2.symm
    have hF := hshape i (rep s) hs ω
    exact hiF.trans_eq hF
  calc
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
        P.pr (fun ω => ∃ s : {s // s ∈ S.image shape}, t ≤ F ω (rep s)) :=
      pr_mono P hsub
    _ ≤ ∑ s : {s // s ∈ S.image shape}, P.pr (fun ω => t ≤ F ω (rep s)) := by
      simpa using pr_exists_finset_le P (Finset.univ : Finset {s // s ∈ S.image shape})
        (fun s ω => t ≤ F ω (rep s))

noncomputable def chooseImageRep {I Sh : Type*} [DecidableEq Sh] [Inhabited I]
    (S : Finset I) (shape : I → Sh) (s : Sh) : I :=
  if hs : s ∈ S.image shape then Classical.choose (Finset.mem_image.mp hs) else default

theorem chooseImageRep_spec {I Sh : Type*} [DecidableEq Sh] [Inhabited I]
    (S : Finset I) (shape : I → Sh) {s : Sh} (hs : s ∈ S.image shape) :
    chooseImageRep S shape s ∈ S ∧ shape (chooseImageRep S shape s) = s := by
  classical
  unfold chooseImageRep
  rw [dif_pos hs]
  exact Classical.choose_spec (Finset.mem_image.mp hs)

theorem pr_exists_shape_sum {Ω I Sh : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [Fintype Sh] [DecidableEq Sh] [Inhabited I]
    (P : FinProb Ω) (S : Finset I) (shape : I → Sh) (F : Ω → I → ℝ) (t : ℝ)
    (hshape : ∀ i j, shape i = shape j → ∀ ω, F ω i = F ω j) :
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
      ∑ s ∈ S.image shape, P.pr (fun ω => t ≤ F ω (chooseImageRep S shape s)) := by
  classical
  have hsub : ∀ ω, (∃ i ∈ S, t ≤ F ω i) →
      ∃ s ∈ S.image shape, t ≤ F ω (chooseImageRep S shape s) := by
    intro ω hω
    obtain ⟨i, hiS, hiF⟩ := hω
    have hmem : shape i ∈ S.image shape := Finset.mem_image.mpr ⟨i, hiS, rfl⟩
    have hrep := chooseImageRep_spec S shape hmem
    have heq : shape i = shape (chooseImageRep S shape (shape i)) := hrep.2.symm
    have hF := hshape i (chooseImageRep S shape (shape i)) heq ω
    exact ⟨shape i, hmem, hiF.trans_eq hF⟩
  calc
    P.pr (fun ω => ∃ i ∈ S, t ≤ F ω i) ≤
        P.pr (fun ω => ∃ s ∈ S.image shape, t ≤ F ω (chooseImageRep S shape s)) :=
      pr_mono P hsub
    _ ≤ ∑ s ∈ S.image shape, P.pr (fun ω => t ≤ F ω (chooseImageRep S shape s)) :=
      pr_exists_finset_le P (S.image shape)
        (fun s ω => t ≤ F ω (chooseImageRep S shape s))

open Filter

theorem eventually_const_mul_nat_rpow_neg_lt {a c b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ n : ℕ in Filter.atTop, c * (n : ℝ) ^ (-a) < b := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) := tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ => c * (n : ℝ) ^ (-a)) Filter.atTop (nhds 0) :=
    by simpa using hconst.mul hpow
  filter_upwards [Metric.tendsto_nhds.1 hlim b hb] with n hn
  have habs : |c * (n : ℝ) ^ (-a)| < b := by simpa [Real.dist_eq] using hn
  exact (abs_lt.mp habs).2

theorem eventually_nat_ceil_rpow_add_two_le_double {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((⌈(n : ℝ) ^ a⌉₊ : ℝ) + 2) ≤ (n : ℝ) ^ (2 * a) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ a) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ (n : ℝ) ^ a :=
    hpow.eventually_ge_atTop 4
  filter_upwards [hlarge] with n hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hceil := (Nat.ceil_lt_add_one (Real.rpow_nonneg hn0 a)).le
  have hquad : (n : ℝ) ^ a + 3 ≤ ((n : ℝ) ^ a) ^ 2 := by nlinarith
  have hpowEq : (n : ℝ) ^ (2 * a) = ((n : ℝ) ^ a) ^ 2 := by
    rw [show 2 * a = a * 2 by ring, Real.rpow_mul hn0 a 2]
    exact Real.rpow_natCast ((n : ℝ) ^ a) 2
  calc
    ((⌈(n : ℝ) ^ a⌉₊ : ℝ) + 2) ≤ (n : ℝ) ^ a + 3 := by linarith
    _ ≤ ((n : ℝ) ^ a) ^ 2 := hquad
    _ = (n : ℝ) ^ (2 * a) := hpowEq.symm

theorem eventually_T₆_le_J₆ :
    ∀ᶠ m : ℕ in Filter.atTop, T₆ m ≤ J₆ m := by
  have hpow : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 1000 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually_ge_atTop 2] with m hm
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  let x : ℝ := (m : ℝ) ^ (1 / 1000 : ℝ)
  have hpow40 : (m : ℝ) ^ (1 / 25 : ℝ) = x ^ 40 := by
    calc
      (m : ℝ) ^ (1 / 25 : ℝ) = (m : ℝ) ^ ((1 / 1000 : ℝ) * 40) := by congr 1 <;> norm_num
      _ = ((m : ℝ) ^ (1 / 1000 : ℝ)) ^ (40 : ℝ) :=
        Real.rpow_mul hm0 (1 / 1000 : ℝ) 40
      _ = x ^ 40 := by
        simpa [x] using Real.rpow_natCast ((m : ℝ) ^ (1 / 1000 : ℝ)) 40
  have hx2 : x + 1 ≤ x ^ 2 := by dsimp [x] at *; nlinarith
  have hx40 : x ^ 2 ≤ x ^ 40 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) (by norm_num : 2 ≤ 40)
  have hT : (T₆ m : ℝ) ≤ x + 1 := by
    dsimp [T₆, x]
    exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hm0 _)).le
  have hTy : (T₆ m : ℝ) ≤ (m : ℝ) ^ (1 / 25 : ℝ) := by
    rw [hpow40]
    exact hT.trans (hx2.trans hx40)
  have hfloor : T₆ m ≤ ⌊(m : ℝ) ^ (1 / 25 : ℝ)⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg hm0 _)).2 hTy
  simpa [J₆] using hfloor

theorem m₆_nat_tendsto_atTop (p₀ : ℝ) (hp₀ : 0 < p₀) :
    Tendsto (fun n : ℕ => m₆ p₀ n) Filter.atTop Filter.atTop := by
  have hα : 0 < α₆ p₀ := lt_min (by norm_num) (by linarith)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ α₆ p₀) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hceil : Tendsto (fun x : ℝ => Nat.ceil x) Filter.atTop Filter.atTop :=
    (Nat.ceil_mono (R := ℝ)).tendsto_atTop_atTop
      (fun b : ℕ => ⟨(b : ℝ), by simp⟩)
  have hceilPow : Tendsto (fun n : ℕ => Nat.ceil ((n : ℝ) ^ α₆ p₀))
      Filter.atTop Filter.atTop := hceil.comp hpow
  simpa [m₆] using hceilPow

theorem m₆_tendsto_atTop (p₀ : ℝ) (hp₀ : 0 < p₀) :
    Tendsto (fun n : ℕ => (m₆ p₀ n : ℝ)) Filter.atTop Filter.atTop := by
  exact (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop).comp
      (m₆_nat_tendsto_atTop p₀ hp₀)

end HypercubeRamsey.Lane_q_s06_stages
