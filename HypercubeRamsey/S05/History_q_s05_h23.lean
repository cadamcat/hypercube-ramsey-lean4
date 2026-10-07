import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.History_q_s05_hist2

/-!
# Helpers for the Stage 2 and Stage 3 history restrictions
-/

namespace HypercubeRamsey.Lane_q_s05_h23

open Classical OAI.HypercubeRamsey
open scoped BigOperators

set_option synthInstance.maxSize 1024

noncomputable section

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}

noncomputable def blockLocalBins5 (X : Setup5 γ K' χ n N E G) (K : X.Ty) (S : Finset X.Key) :
    Finset (BinVector5 n) :=
  insert K.1.1 ((S ∪ X.gateKeys K).biUnion fun ℓ => binList5 ℓ.coarse)

theorem binList_subset_blockLocalBins5 (X : Setup5 γ K' χ n N E G)
    (K : X.Ty) (S : Finset X.Key) (ℓ : X.Key)
    (hℓ : ℓ ∈ S ∨ ℓ ∈ X.gateKeys K) :
    binList5 ℓ.coarse ⊆ blockLocalBins5 X K S := by
  intro w hw
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr
    ⟨ℓ, Finset.mem_union.mpr hℓ, hw⟩

theorem blockLocalBins_mono5 (X : Setup5 γ K' χ n N E G) (K : X.Ty)
    {S T : Finset X.Key} (hST : S ⊆ T) :
    blockLocalBins5 X K S ⊆ blockLocalBins5 X K T := by
  intro w hw
  simp only [blockLocalBins5, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_union] at hw ⊢
  rcases hw with hw | ⟨ℓ, hℓ, hbin⟩
  · exact Or.inl hw
  · refine Or.inr ⟨ℓ, ?_, hbin⟩
    rcases hℓ with hS | hgate
    · exact Or.inl (hST hS)
    · exact Or.inr hgate

noncomputable abbrev CoarsePairLaw5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (w : BinVector5 n) : FinProb (Fin N × X.Stream) :=
  FinProb.bind (X.P.prior.partner v w) fun a =>
    FinProb.pi fun _s : Fin (X.p.streamSegs n) => X.segLaw v a

noncomputable def coarsePairEquiv5 (X : Setup5 γ K' χ n N E G) :
    (BinVector5 n → Fin N × X.Stream) ≃ X.Coarse where
  toFun z := (fun w => (z w).1, fun w => (z w).2)
  invFun c := fun w => (c.1 w, c.2 w)
  left_inv := by
    intro z
    funext w
    change ((z w).1, (z w).2) = z w
    exact Prod.ext rfl rfl
  right_inv := by
    intro c
    cases c with
    | mk a W =>
      apply Prod.ext
      · funext w
        rfl
      · funext w
        funext s
        funext x
        rfl

set_option maxHeartbeats 0 in
theorem coarseLaw_eq_map_pi5 (X : Setup5 γ K' χ n N E G) (v : Fin N) :
    X.coarseLaw v = FinProb.map (FinProb.pi (CoarsePairLaw5 X v)) (coarsePairEquiv5 X) := by
  classical
  let e := coarsePairEquiv5 X
  apply FinProb.ext
  intro c
  simp only [FinProb.map]
  rw [Finset.sum_eq_single (e.symm c)]
  · have he : coarsePairEquiv5 X (e.symm c) = c := by
      simpa [e] using e.apply_symm_apply c
    have hleft : (X.coarseLaw v).w c =
        (∏ w, (X.P.prior.partner v w).w (c.1 w)) *
          ∏ w, ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s) := by
      rfl
    have hright : (FinProb.pi (CoarsePairLaw5 X v)).w (e.symm c) =
        ∏ w, ((X.P.prior.partner v w).w (c.1 w) *
          ∏ s, (X.segLaw v (c.1 w)).w (c.2 w s)) := by
      rfl
    rw [if_pos he]
    rw [hleft, hright]
    apply (Finset.prod_mul_distrib).symm
  · intro z hz hne
    have hz' : coarsePairEquiv5 X z ≠ c := by
      intro heq
      apply hne
      exact e.injective (by simpa [e] using heq)
    simp [hz']
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem pi_pr_ext_depends5 {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P Q : ∀ i, FinProb (Ω i)) (A : (∀ i, Ω i) → Prop)
    (s : Finset I) (ω₀ : ∀ i, Ω i)
    (hA : FinProb.DependsOn A s)
    (hPQ : ∀ i ∈ s, P i = Q i) :
    (FinProb.pi P).pr A = (FinProb.pi Q).pr A := by
  classical
  let f : (∀ i, Ω i) → ℝ := fun ω => if A ω then 1 else 0
  have hf : FinProb.DependsOn f s := by
    intro ω ω' hω
    simp [f, hA ω ω' hω]
  have hpr (R : ∀ i, FinProb (Ω i)) :
      (FinProb.pi R).pr A = (FinProb.pi R).expect f := by
    simp [FinProb.pr, FinProb.expect, FinProb.pi, f]
  have hPi : FinProb.pi (fun i : {i // i ∈ s} => P i.1) =
      FinProb.pi (fun i : {i // i ∈ s} => Q i.1) := by
    apply FinProb.ext
    intro a
    simp only [FinProb.pi]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (fun R : FinProb (Ω i.1) => R.w (a i)) (hPQ i.1 i.2)
  calc
    (FinProb.pi P).pr A = (FinProb.pi P).expect f := hpr P
    _ = (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
        (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => ω₀ i.1))) := FinProb.pi_expect_depends P s f ω₀ hf
    _ = (FinProb.pi (fun i : {i // i ∈ s} => Q i.1)).expect
        (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => ω₀ i.1))) := by rw [hPi]
    _ = (FinProb.pi Q).expect f := (FinProb.pi_expect_depends Q s f ω₀ hf).symm
    _ = (FinProb.pi Q).pr A := (hpr Q).symm

theorem bind_pr5 {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (A : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => A ab.1 ab.2) =
      P.expect (fun a => (K a).pr (A a)) := by
  classical
  unfold FinProb.pr FinProb.expect
  change (∑ ab : α × β,
      if A ab.1 ab.2 then P.w ab.1 * (K ab.1).w ab.2 else 0) =
    ∑ a, P.w a * (∑ b, if A a b then (K a).w b else 0)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hA : A a b <;> simp [hA]

theorem pr_mono5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

theorem pr_nonneg5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs <;> simp [P.nonneg ω]

theorem colWeight_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base)
    (ℓ : X.Key) (W W' : BinVector5 n → X.Stream)
    (keep : BinVector5 n → Fin (X.p.streamSegs n) → Prop)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ binList5 ℓ.coarse, W w = W' w) :
    X.colWeight b ℓ W keep = X.colWeight b' ℓ W' keep := by
  classical
  funext y
  by_cases hboundary : ℓ.coarse.2 = true
  · have hprod :
        (∏ w ∈ binList5 ℓ.coarse,
          (X.P.prior.partner y w).w (b.2.1 w) *
            ∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < X.p.uSeg n (ℓ.level + 1) ∧ keep w s then
              (X.segLaw y (b.2.1 w)).w (W w s) else 1) =
        (∏ w ∈ binList5 ℓ.coarse,
          (X.P.prior.partner y w).w (b'.2.1 w) *
            ∏ s : Fin (X.p.streamSegs n), if (s : ℕ) < X.p.uSeg n (ℓ.level + 1) ∧ keep w s then
              (X.segLaw y (b'.2.1 w)).w (W' w s) else 1) := by
      apply Finset.prod_congr rfl
      intro w hw
      rw [hpartner w hw, hstream w hw]
    simp only [Setup5.colWeight, hboundary]
    rw [hprod]
    simp only [if_true]
  · have hcenter : ℓ.coarse.1 ∈ binList5 ℓ.coarse := by
      simp [binList5, hboundary]
    simp [Setup5.colWeight, hboundary, hparent, hstream ℓ.coarse.1 hcenter]

theorem prior_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base) (ℓ : X.Key)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ binList5 ℓ.coarse, b.2.2 w = b'.2.2 w) :
    X.prior b ℓ = X.prior b' ℓ := by
  change normalize5 (X.colWeight b ℓ b.2.2 (fun _ _ => True)) X.y₀ =
    normalize5 (X.colWeight b' ℓ b'.2.2 (fun _ _ => True)) X.y₀
  exact congrArg (fun f : Fin N → ℝ => normalize5 f X.y₀)
    (colWeight_ext_bins5 X b b' ℓ b.2.2 b'.2.2 (fun _ _ => True)
      hparent hpartner hstream)

theorem priorDel_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base) (ℓ : X.Key)
    (w : BinVector5 n) (k : ℕ)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ binList5 ℓ.coarse, b.2.2 w = b'.2.2 w) :
    X.priorDel b ℓ w k = X.priorDel b' ℓ w k := by
  change normalize5 (X.colWeight b ℓ b.2.2 (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k))) X.y₀ =
    normalize5 (X.colWeight b' ℓ b'.2.2 (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k))) X.y₀
  exact congrArg (fun f : Fin N → ℝ => normalize5 f X.y₀)
    (colWeight_ext_bins5 X b b' ℓ b.2.2 b'.2.2
      (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) hparent hpartner hstream)

theorem priorRep_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base) (ℓ : X.Key)
    (w : BinVector5 n) {k : ℕ} (z : Fin k → Word5 N X.p.q0)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ v ∈ binList5 ℓ.coarse, b.2.1 v = b'.2.1 v)
    (hstream : ∀ v ∈ binList5 ℓ.coarse, b.2.2 v = b'.2.2 v) :
    X.priorRep b ℓ w z = X.priorRep b' ℓ w z := by
  have hreplace : ∀ v ∈ binList5 ℓ.coarse,
      X.replaceStream b.2.2 w z v = X.replaceStream b'.2.2 w z v := by
    intro v hv
    by_cases hvw : v = w
    · subst v
      simp [Setup5.replaceStream, hstream w hv]
    · simp [Setup5.replaceStream, hvw, hstream v hv]
  change normalize5 (X.colWeight b ℓ (X.replaceStream b.2.2 w z) (fun _ _ => True)) X.y₀ =
    normalize5 (X.colWeight b' ℓ (X.replaceStream b'.2.2 w z) (fun _ _ => True)) X.y₀
  exact congrArg (fun f : Fin N → ℝ => normalize5 f X.y₀)
    (colWeight_ext_bins5 X b b' ℓ (X.replaceStream b.2.2 w z)
      (X.replaceStream b'.2.2 w z) (fun _ _ => True) hparent hpartner hreplace)

theorem blockBase_ext5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base) (K : X.Ty)
    (z : X.Block K) (hparent : b.1 = b'.1)
    (hcenter : b.2.1 K.1.1 = b'.2.1 K.1.1) :
    X.blockBase b K z = X.blockBase b' K z := by
  simp [Setup5.blockBase, hparent, hcenter]

theorem blockGate_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base)
    (K : X.Ty) (S : Finset X.Key) (z : X.Block K)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K S, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K S, b.2.2 w = b'.2.2 w) :
    X.blockGate b K z ↔ X.blockGate b' K z := by
  simp only [Setup5.blockGate]
  constructor
  · intro hgate ℓ hℓ y
    have hlocal : binList5 ℓ.coarse ⊆ blockLocalBins5 X K S :=
      binList_subset_blockLocalBins5 X K S ℓ (Or.inr hℓ)
    have hP : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w :=
      fun w hw => hpartner w (hlocal hw)
    have hW : ∀ w ∈ binList5 ℓ.coarse, b.2.2 w = b'.2.2 w :=
      fun w hw => hstream w (hlocal hw)
    have hrep := priorRep_ext_bins5 X b b' ℓ K.1.1 z hparent hP hW
    have hdel := priorDel_ext_bins5 X b b' ℓ K.1.1 (X.p.typeSegs n K)
      hparent hP hW
    have h := hgate ℓ hℓ y
    rw [hrep, hdel] at h
    exact h
  · intro hgate ℓ hℓ y
    have hlocal : binList5 ℓ.coarse ⊆ blockLocalBins5 X K S :=
      binList_subset_blockLocalBins5 X K S ℓ (Or.inr hℓ)
    have hP : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w :=
      fun w hw => hpartner w (hlocal hw)
    have hW : ∀ w ∈ binList5 ℓ.coarse, b.2.2 w = b'.2.2 w :=
      fun w hw => hstream w (hlocal hw)
    have hrep := priorRep_ext_bins5 X b b' ℓ K.1.1 z hparent hP hW
    have hdel := priorDel_ext_bins5 X b b' ℓ K.1.1 (X.p.typeSegs n K)
      hparent hP hW
    have h := hgate ℓ hℓ y
    rw [← hrep, ← hdel] at h
    exact h

theorem blockWeight_ext_bins5 (X : Setup5 γ K' χ n N E G)
    (H H' : X.KeyHist) (K : X.Ty) (S : Finset X.Key) (z : X.Block K)
    (hparent : H.1.1 = H'.1.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K S, H.1.2.1 w = H'.1.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K S, H.1.2.2 w = H'.1.2.2 w)
    (hcols : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    X.blockWeight H K S z = X.blockWeight H' K S z := by
  have hlocalCenter : K.1.1 ∈ blockLocalBins5 X K S := by
    simp [blockLocalBins5]
  have hbase := blockBase_ext5 X H.1 H'.1 K z hparent
    (hpartner K.1.1 hlocalCenter)
  have hgate : X.blockGate H.1 K z = X.blockGate H'.1 K z :=
    propext (blockGate_ext_bins5 X H.1 H'.1 K S z hparent hpartner hstream)
  have hlik : ∀ ℓ ∈ S, X.colLik H.1 K ℓ z (H.2 ℓ) =
      X.colLik H'.1 K ℓ z (H'.2 ℓ) := by
    intro ℓ hℓ
    have hlocal : binList5 ℓ.coarse ⊆ blockLocalBins5 X K S :=
      binList_subset_blockLocalBins5 X K S ℓ (Or.inl hℓ)
    have hP : ∀ w ∈ binList5 ℓ.coarse, H.1.2.1 w = H'.1.2.1 w :=
      fun w hw => hpartner w (hlocal hw)
    have hW : ∀ w ∈ binList5 ℓ.coarse, H.1.2.2 w = H'.1.2.2 w :=
      fun w hw => hstream w (hlocal hw)
    have hrep := priorRep_ext_bins5 X H.1 H'.1 ℓ K.1.1 z hparent hP hW
    have hdel := priorDel_ext_bins5 X H.1 H'.1 ℓ K.1.1
      (X.p.typeSegs n K) hparent hP hW
    rw [Setup5.colLik, Setup5.colLik, hrep, hdel, hcols ℓ hℓ]
  unfold Setup5.blockWeight
  rw [hbase, hgate]
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  exact hlik ℓ hℓ

theorem blockMass_ext_bins5 (X : Setup5 γ K' χ n N E G)
    (H H' : X.KeyHist) (K : X.Ty) (S : Finset X.Key)
    (hparent : H.1.1 = H'.1.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K S, H.1.2.1 w = H'.1.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K S, H.1.2.2 w = H'.1.2.2 w)
    (hcols : ∀ ℓ ∈ S, H.2 ℓ = H'.2 ℓ) :
    X.blockMass H K S = X.blockMass H' K S := by
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z hz
  exact blockWeight_ext_bins5 X H H' K S z hparent hpartner hstream hcols

theorem step2Fail_ext_bins5 (X : Setup5 γ K' χ n N E G)
    (H H' : X.KeyHist) (K : X.Ty)
    (hparent : H.1.1 = H'.1.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K K.2.1, H.1.2.1 w = H'.1.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K K.2.1, H.1.2.2 w = H'.1.2.2 w)
    (hcols : ∀ ℓ ∈ K.2.1, H.2 ℓ = H'.2 ℓ) :
    X.step2Fail H K ↔ X.step2Fail H' K := by
  have hcenter : K.1.1 ∈ blockLocalBins5 X K K.2.1 := by
    change K.1.1 ∈ insert K.1.1 _
    exact Finset.mem_insert_self _ _
  have htrue : X.trueBlock H.1 K = X.trueBlock H'.1 K := by
    funext s
    by_cases hs : (s : ℕ) < X.p.streamSegs n
    · simp [Setup5.trueBlock, hs, hstream K.1.1 hcenter]
    · simp [Setup5.trueBlock, hs]
  have hgate0 := blockGate_ext_bins5 X H.1 H'.1 K K.2.1 (X.trueBlock H.1 K)
    hparent hpartner hstream
  have hgate : X.blockGate H.1 K (X.trueBlock H.1 K) ↔
      X.blockGate H'.1 K (X.trueBlock H'.1 K) := by
    simpa only [htrue] using hgate0
  have hmass : X.blockMass H K K.2.1 = X.blockMass H' K K.2.1 :=
    blockMass_ext_bins5 X H H' K K.2.1 hparent hpartner hstream hcols
  have hmassErase : ∀ ℓ ∈ K.2.1,
      X.blockMass H K (K.2.1.erase ℓ) = X.blockMass H' K (K.2.1.erase ℓ) := by
    intro ℓ hℓ
    have hscope : blockLocalBins5 X K (K.2.1.erase ℓ) ⊆
        blockLocalBins5 X K K.2.1 :=
      blockLocalBins_mono5 X K (Finset.erase_subset _ _)
    have hP : ∀ w ∈ blockLocalBins5 X K (K.2.1.erase ℓ),
        H.1.2.1 w = H'.1.2.1 w := fun w hw => hpartner w (hscope hw)
    have hW : ∀ w ∈ blockLocalBins5 X K (K.2.1.erase ℓ),
        H.1.2.2 w = H'.1.2.2 w := fun w hw => hstream w (hscope hw)
    have hC : ∀ j ∈ K.2.1.erase ℓ, H.2 j = H'.2 j := by
      intro j hj
      exact hcols j (Finset.mem_of_mem_erase hj)
    exact blockMass_ext_bins5 X H H' K (K.2.1.erase ℓ) hparent hP hW hC
  unfold Setup5.step2Fail
  constructor
  · rintro ⟨hg, hbad⟩
    refine ⟨hgate.mp hg, ?_⟩
    rcases hbad with hden | ⟨ℓ, hℓ, hratio⟩
    · exact Or.inl (by rw [hmass] at hden; exact hden)
    · exact Or.inr ⟨ℓ, hℓ, by rw [hmass, hmassErase ℓ hℓ] at hratio; exact hratio⟩
  · rintro ⟨hg, hbad⟩
    refine ⟨hgate.mpr hg, ?_⟩
    rcases hbad with hden | ⟨ℓ, hℓ, hratio⟩
    · exact Or.inl (by rw [← hmass] at hden; exact hden)
    · exact Or.inr ⟨ℓ, hℓ, by rw [← hmass, ← hmassErase ℓ hℓ] at hratio; exact hratio⟩

theorem step2FailPr_ext_bins5 (X : Setup5 γ K' χ n N E G)
    (b b' : X.Base) (K : X.Ty)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K K.2.1, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K K.2.1, b.2.2 w = b'.2.2 w) :
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) =
      (X.hiddenLaw b').pr (fun U => X.step2Fail (b', U) K) := by
  classical
  let P : ∀ ℓ : X.Key, FinProb (Fin (colLen5 (X.p.s n) ℓ) → Fin N) :=
    fun ℓ => FinProb.pi fun _ => X.prior b ℓ
  let Q : ∀ ℓ : X.Key, FinProb (Fin (colLen5 (X.p.s n) ℓ) → Fin N) :=
    fun ℓ => FinProb.pi fun _ => X.prior b' ℓ
  let A : X.Hidden → Prop := fun U => X.step2Fail (b, U) K
  let A' : X.Hidden → Prop := fun U => X.step2Fail (b', U) K
  have hdep : FinProb.DependsOn A K.2.1 := by
    intro U U' hU
    exact propext (step2Fail_ext_bins5 X (b, U) (b, U') K rfl
      (by intro w hw; rfl) (by intro w hw; rfl) (fun ℓ hℓ => hU ℓ hℓ))
  have hPQ : ∀ ℓ ∈ K.2.1, P ℓ = Q ℓ := by
    intro ℓ hℓ
    have hlocal : binList5 ℓ.coarse ⊆ blockLocalBins5 X K K.2.1 :=
      binList_subset_blockLocalBins5 X K K.2.1 ℓ (Or.inl hℓ)
    have hprior := prior_ext_bins5 X b b' ℓ hparent
      (fun w hw => hpartner w (hlocal hw))
      (fun w hw => hstream w (hlocal hw))
    exact congrArg (fun π : Law N => FinProb.pi (fun _ => π)) hprior
  have hAeq : ∀ U, A U ↔ A' U := by
    intro U
    exact step2Fail_ext_bins5 X (b, U) (b', U) K hparent hpartner hstream
      (fun _ _ => rfl)
  have hAfun : A = A' := by
    funext U
    exact propext (hAeq U)
  change (FinProb.pi P).pr A = (FinProb.pi Q).pr A'
  calc
    (FinProb.pi P).pr A = (FinProb.pi Q).pr A :=
      pi_pr_ext_depends5 P Q A K.2.1 (fun _ => fun _ => X.y₀) hdep hPQ
    _ = (FinProb.pi Q).pr A' := by rw [hAfun]

theorem optFail_ext_bins5 (X : Setup5 γ K' χ n N E G)
    (H H' : X.KeyHist) (K : X.Ty) (t : CubeVertex (X.p.m n))
    (hparent : H.1.1 = H'.1.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K (insert (X.optKeyOf K t) K.2.1),
      H.1.2.1 w = H'.1.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K (insert (X.optKeyOf K t) K.2.1),
      H.1.2.2 w = H'.1.2.2 w)
    (hcols : ∀ ℓ ∈ insert (X.optKeyOf K t) K.2.1, H.2 ℓ = H'.2 ℓ) :
    X.optFail H K t ↔ X.optFail H' K t := by
  let S := insert (X.optKeyOf K t) K.2.1
  have hcenter : K.1.1 ∈ blockLocalBins5 X K S := by
    change K.1.1 ∈ insert K.1.1 _
    exact Finset.mem_insert_self _ _
  have htrue : X.trueBlock H.1 K = X.trueBlock H'.1 K := by
    funext s
    by_cases hs : (s : ℕ) < X.p.streamSegs n
    · simp [Setup5.trueBlock, hs, hstream K.1.1 hcenter]
    · simp [Setup5.trueBlock, hs]
  have hgate0 := blockGate_ext_bins5 X H.1 H'.1 K S (X.trueBlock H.1 K)
    hparent hpartner hstream
  have hgate : X.blockGate H.1 K (X.trueBlock H.1 K) ↔
      X.blockGate H'.1 K (X.trueBlock H'.1 K) := by
    simpa only [htrue] using hgate0
  have hmassInsert : X.blockMass H K S = X.blockMass H' K S :=
    blockMass_ext_bins5 X H H' K S hparent hpartner hstream hcols
  have hscope : blockLocalBins5 X K K.2.1 ⊆ blockLocalBins5 X K S := by
    apply blockLocalBins_mono5
    intro ℓ hℓ
    exact Finset.mem_insert_of_mem hℓ
  have hP : ∀ w ∈ blockLocalBins5 X K K.2.1, H.1.2.1 w = H'.1.2.1 w :=
    fun w hw => hpartner w (hscope hw)
  have hW : ∀ w ∈ blockLocalBins5 X K K.2.1, H.1.2.2 w = H'.1.2.2 w :=
    fun w hw => hstream w (hscope hw)
  have hC : ∀ ℓ ∈ K.2.1, H.2 ℓ = H'.2 ℓ := by
    intro ℓ hℓ
    exact hcols ℓ (Finset.mem_insert_of_mem hℓ)
  have hmassKeys : X.blockMass H K K.2.1 = X.blockMass H' K K.2.1 :=
    blockMass_ext_bins5 X H H' K K.2.1 hparent hP hW hC
  unfold Setup5.optFail
  constructor
  · rintro ⟨hg, hbad⟩
    refine ⟨hgate.mp hg, ?_⟩
    rw [hmassInsert, hmassKeys] at hbad
    exact hbad
  · rintro ⟨hg, hbad⟩
    refine ⟨hgate.mpr hg, ?_⟩
    rw [← hmassInsert, ← hmassKeys] at hbad
    exact hbad

theorem optFailPr_ext_bins5 (X : Setup5 γ K' χ n N E G)
    (b b' : X.Base) (K : X.Ty) (t : CubeVertex (X.p.m n))
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ blockLocalBins5 X K (insert (X.optKeyOf K t) K.2.1),
      b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ blockLocalBins5 X K (insert (X.optKeyOf K t) K.2.1),
      b.2.2 w = b'.2.2 w) :
    (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) =
      (X.hiddenLaw b').pr (fun U => X.optFail (b', U) K t) := by
  classical
  let S := insert (X.optKeyOf K t) K.2.1
  let P : ∀ ℓ : X.Key, FinProb (Fin (colLen5 (X.p.s n) ℓ) → Fin N) :=
    fun ℓ => FinProb.pi fun _ => X.prior b ℓ
  let Q : ∀ ℓ : X.Key, FinProb (Fin (colLen5 (X.p.s n) ℓ) → Fin N) :=
    fun ℓ => FinProb.pi fun _ => X.prior b' ℓ
  let A : X.Hidden → Prop := fun U => X.optFail (b, U) K t
  let A' : X.Hidden → Prop := fun U => X.optFail (b', U) K t
  have hdep : FinProb.DependsOn A S := by
    intro U U' hU
    exact propext (optFail_ext_bins5 X (b, U) (b, U') K t rfl
      (by intro w hw; rfl) (by intro w hw; rfl) (fun ℓ hℓ => hU ℓ hℓ))
  have hPQ : ∀ ℓ ∈ S, P ℓ = Q ℓ := by
    intro ℓ hℓ
    have hlocal : binList5 ℓ.coarse ⊆ blockLocalBins5 X K S :=
      binList_subset_blockLocalBins5 X K S ℓ (Or.inl hℓ)
    have hprior := prior_ext_bins5 X b b' ℓ hparent
      (fun w hw => hpartner w (hlocal hw))
      (fun w hw => hstream w (hlocal hw))
    exact congrArg (fun π : Law N => FinProb.pi (fun _ => π)) hprior
  have hAeq : ∀ U, A U ↔ A' U := by
    intro U
    exact optFail_ext_bins5 X (b, U) (b', U) K t hparent hpartner hstream
      (fun _ _ => rfl)
  have hAfun : A = A' := by
    funext U
    exact propext (hAeq U)
  change (FinProb.pi P).pr A = (FinProb.pi Q).pr A'
  calc
    (FinProb.pi P).pr A = (FinProb.pi Q).pr A :=
      pi_pr_ext_depends5 P Q A S (fun _ => fun _ => X.y₀) hdep hPQ
    _ = (FinProb.pi Q).pr A' := by rw [hAfun]

theorem step1Fail_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base)
    (ℓ : X.Key) (w : BinVector5 n) (k : ℕ)
    (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ binList5 ℓ.coarse, b.2.2 w = b'.2.2 w) :
    X.step1Fail b ℓ w k ↔ X.step1Fail b' ℓ w k := by
  simp only [Setup5.step1Fail]
  simp_rw [prior_ext_bins5 X b b' ℓ hparent hpartner hstream,
    priorDel_ext_bins5 X b b' ℓ w k hparent hpartner hstream]

theorem capFail_ext_bins5 (X : Setup5 γ K' χ n N E G) (b b' : X.Base)
    (ℓ : X.Key) (hparent : b.1 = b'.1)
    (hpartner : ∀ w ∈ binList5 ℓ.coarse, b.2.1 w = b'.2.1 w)
    (hstream : ∀ w ∈ binList5 ℓ.coarse, b.2.2 w = b'.2.2 w) :
    X.capFail b ℓ ↔ X.capFail b' ℓ := by
  simp only [Setup5.capFail]
  simp_rw [prior_ext_bins5 X b b' ℓ hparent hpartner hstream]

abbrev Stage2TypeOcc5 (X : Setup5 γ K' χ n N E G) :=
  {K : X.Ty // X.TypeOccurs K}

abbrev Stage2Step1Alarm5 (X : Setup5 γ K' χ n N E G) :=
  Σ K : Stage2TypeOcc5 X, {ℓ : X.Key // ℓ ∈ X.gateKeys K.1}

abbrev Stage2CapAlarm5 (X : Setup5 γ K' χ n N E G) :=
  {ℓ : X.Key // X.KeyOccurs ℓ}

abbrev Stage2OptAlarm5 (X : Setup5 γ K' χ n N E G) :=
  {q : X.Ty × CubeVertex (X.p.m n) // X.TypeOccurs q.1 ∧ X.OptOccurs q.1 q.2}

abbrev Stage2AlarmIndex5 (X : Setup5 γ K' χ n N E G) :=
  Stage2Step1Alarm5 X ⊕
    (Stage2CapAlarm5 X ⊕ (Stage2TypeOcc5 X ⊕ Stage2OptAlarm5 X))

noncomputable instance stage2TypeOccFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2TypeOcc5 X) := by
  classical
  infer_instance

noncomputable instance stage2Step1AlarmFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2Step1Alarm5 X) := by
  classical
  infer_instance

noncomputable instance stage2CapAlarmFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2CapAlarm5 X) := by
  classical
  infer_instance

noncomputable instance stage2OptAlarmFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2OptAlarm5 X) := by
  classical
  infer_instance

noncomputable instance stage2AlarmIndexFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2AlarmIndex5 X) := by
  classical
  infer_instance

noncomputable def stage2AlarmBad5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (i : Stage2AlarmIndex5 X) (c : X.Coarse) : Prop :=
  match i with
  | Sum.inl a =>
      X.step1Fail (v, c) a.2.1 a.1.1.1.1 (X.p.typeSegs n a.1.1)
  | Sum.inr (Sum.inl a) => X.capFail (v, c) a.1
  | Sum.inr (Sum.inr (Sum.inl a)) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) a.1)
  | Sum.inr (Sum.inr (Sum.inr a)) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) a.1.1 a.1.2)

noncomputable def stage2AlarmScope5 (X : Setup5 γ K' χ n N E G)
    (i : Stage2AlarmIndex5 X) : Finset (BinVector5 n) :=
  match i with
  | Sum.inl a => binList5 a.2.1.coarse
  | Sum.inr (Sum.inl a) => binList5 a.1.coarse
  | Sum.inr (Sum.inr (Sum.inl a)) => blockLocalBins5 X a.1 a.1.2.1
  | Sum.inr (Sum.inr (Sum.inr a)) =>
      blockLocalBins5 X a.1.1 (insert (X.optKeyOf a.1.1 a.1.2) a.1.1.2.1)

structure Stage2RawBounds5 (X : Setup5 γ K' χ n N E G) (v : Fin N) : Prop where
  step1 : ∀ K, X.TypeOccurs K → ∀ ℓ, ℓ ∈ X.gateKeys K →
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K)) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)
  cap : ∀ ℓ, X.KeyOccurs ℓ →
    (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) / 2)
  step2 : ∀ K, X.TypeOccurs K →
    (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)
  optional : ∀ K t, X.OptOccurs K t →
    (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)

noncomputable def stage2AlarmBudget5 (X : Setup5 γ K' χ n N E G)
    (i : Stage2AlarmIndex5 X) : ℝ :=
  match i with
  | Sum.inl a => Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1.1)) / 2)
  | Sum.inr (Sum.inl a) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (a.1.level + 1))) / 2)
  | Sum.inr (Sum.inr (Sum.inl a)) =>
      ((a.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1)) / 4)
  | Sum.inr (Sum.inr (Sum.inr _)) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)

noncomputable def stage2AlarmBadOnPairs5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (i : Stage2AlarmIndex5 X) (ω : BinVector5 n → Fin N × X.Stream) : Prop :=
  stage2AlarmBad5 X v i (coarsePairEquiv5 X ω)

theorem step2AlarmProb_bound5 (X : Setup5 γ K' χ n N E G) (v : Fin N) (K : X.Ty)
    (hraw : (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) ≤
      ((K.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 2)) :
    (X.coarseLaw v).pr (fun c =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K)) ≤
      ((K.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
  classical
  let A : X.Coarse → X.Hidden → Prop := fun c U => X.step2Fail ((v, c), U) K
  let f : X.Coarse → ℝ := fun c => (X.hiddenLaw (v, c)).pr (A c)
  let u : ℝ := X.p.delta * (X.p.q0 * X.p.typeSegs n K)
  let t : ℝ := Real.exp (-u / 4)
  have ht : 0 < t := Real.exp_pos _
  have hbind : (X.keyLawAt v).pr (fun cu => A cu.1 cu.2) =
      (X.coarseLaw v).expect f := by
    simpa [Setup5.keyLawAt, A, f] using
      (bind_pr5 (X.coarseLaw v) (fun c => X.hiddenLaw (v, c)) A)
  have hmean : (X.coarseLaw v).expect f ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-u / 2) := by
    rw [← hbind]
    simpa [u] using hraw
  have hnonneg : ∀ c, 0 ≤ f c := fun c => pr_nonneg5 (X.hiddenLaw (v, c)) (A c)
  have hMarkov := FinProb.markov (X.coarseLaw v) f t hnonneg ht
  have hsubset : (X.coarseLaw v).pr (fun c => t < f c) ≤
      (X.coarseLaw v).pr (fun c => t ≤ f c) := by
    apply pr_mono5
    intro c hc
    exact le_of_lt hc
  have hexp : Real.exp (-u / 2) / Real.exp (-u / 4) = Real.exp (-u / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    (X.coarseLaw v).pr (fun c => Real.exp (-u / 4) < f c) ≤
        (X.coarseLaw v).pr (fun c => t ≤ f c) := by
          simpa [t] using hsubset
    _ ≤ (X.coarseLaw v).expect f / t := hMarkov
    _ ≤ (((K.2.1.card : ℝ) + 1) * Real.exp (-u / 2)) / t :=
      div_le_div_of_nonneg_right hmean ht.le
    _ = ((K.2.1.card : ℝ) + 1) * Real.exp (-u / 4) := by
      dsimp [t]
      calc
        (((K.2.1.card : ℝ) + 1) * Real.exp (-u / 2)) / Real.exp (-u / 4) =
            ((K.2.1.card : ℝ) + 1) *
              (Real.exp (-u / 2) / Real.exp (-u / 4)) := by ring
        _ = ((K.2.1.card : ℝ) + 1) * Real.exp (-u / 4) := by rw [hexp]
    _ = ((K.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by rfl

theorem optAlarmProb_bound5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (K : X.Ty) (t : CubeVertex (X.p.m n))
    (hraw : (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)) :
    (X.coarseLaw v).pr (fun c =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t)) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
  classical
  let A : X.Coarse → X.Hidden → Prop := fun c U => X.optFail ((v, c), U) K t
  let f : X.Coarse → ℝ := fun c => (X.hiddenLaw (v, c)).pr (A c)
  let u : ℝ := X.p.delta * (X.p.q0 * X.p.uStarSeg n)
  let r : ℝ := Real.exp (-u / 4)
  have hr : 0 < r := Real.exp_pos _
  have hbind : (X.keyLawAt v).pr (fun cu => A cu.1 cu.2) =
      (X.coarseLaw v).expect f := by
    simpa [Setup5.keyLawAt, A, f] using
      (bind_pr5 (X.coarseLaw v) (fun c => X.hiddenLaw (v, c)) A)
  have hmean : (X.coarseLaw v).expect f ≤ Real.exp (-u / 2) := by
    rw [← hbind]
    simpa [u] using hraw
  have hnonneg : ∀ c, 0 ≤ f c := fun c => pr_nonneg5 (X.hiddenLaw (v, c)) (A c)
  have hMarkov := FinProb.markov (X.coarseLaw v) f r hnonneg hr
  have hsubset : (X.coarseLaw v).pr (fun c => r < f c) ≤
      (X.coarseLaw v).pr (fun c => r ≤ f c) := by
    apply pr_mono5
    intro c hc
    exact le_of_lt hc
  have hexp : Real.exp (-u / 2) / Real.exp (-u / 4) = Real.exp (-u / 4) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  calc
    (X.coarseLaw v).pr (fun c => Real.exp (-u / 4) < f c) ≤
        (X.coarseLaw v).pr (fun c => r ≤ f c) := by
          simpa [r] using hsubset
    _ ≤ (X.coarseLaw v).expect f / r := hMarkov
    _ ≤ Real.exp (-u / 2) / r := div_le_div_of_nonneg_right hmean hr.le
    _ = Real.exp (-u / 4) := by
      dsimp [r]
      exact hexp
    _ = Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by rfl

theorem stage2AlarmPr_bound5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (hraw : Stage2RawBounds5 X v) (i : Stage2AlarmIndex5 X) :
    (X.coarseLaw v).pr (stage2AlarmBad5 X v i) ≤ stage2AlarmBudget5 X i := by
  classical
  cases i with
  | inl a =>
      change (X.coarseLaw v).pr
          (fun c => X.step1Fail (v, c) a.2.1 a.1.1.1.1 (X.p.typeSegs n a.1.1)) ≤
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1.1)) / 2)
      exact hraw.step1 a.1.1 a.1.2 a.2.1 a.2.2
  | inr rest =>
    cases rest with
    | inl a =>
        change (X.coarseLaw v).pr (fun c => X.capFail (v, c) a.1) ≤
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (a.1.level + 1))) / 2)
        exact hraw.cap a.1 a.2
    | inr tail =>
      cases tail with
      | inl a =>
          change (X.coarseLaw v).pr (fun c =>
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1)) / 4) <
              (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) a.1)) ≤
            ((a.1.2.1.card : ℝ) + 1) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1)) / 4)
          exact step2AlarmProb_bound5 X v a.1 (hraw.step2 a.1 a.2)
      | inr a =>
          change (X.coarseLaw v).pr (fun c =>
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
              (X.hiddenLaw (v, c)).pr
                (fun U => X.optFail ((v, c), U) a.1.1 a.1.2)) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)
          exact optAlarmProb_bound5 X v a.1.1 a.1.2
            (hraw.optional a.1.1 a.1.2 a.2.2)

theorem stage2AlarmBad_depends_bins5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (i : Stage2AlarmIndex5 X) :
    FinProb.DependsOn (stage2AlarmBadOnPairs5 X v i) (stage2AlarmScope5 X i) := by
  classical
  intro ω ω' hω
  let c := coarsePairEquiv5 X ω
  let c' := coarsePairEquiv5 X ω'
  have hA : ∀ w ∈ stage2AlarmScope5 X i, c.1 w = c'.1 w := by
    intro w hw
    change (ω w).1 = (ω' w).1
    exact congrArg Prod.fst (hω w hw)
  have hW : ∀ w ∈ stage2AlarmScope5 X i, c.2 w = c'.2 w := by
    intro w hw
    change (ω w).2 = (ω' w).2
    exact congrArg Prod.snd (hω w hw)
  cases i with
  | inl a =>
    have hlocal : ∀ w ∈ binList5 a.2.1.coarse, c.1 w = c'.1 w := by
      intro w hw
      exact hA w (by simpa [stage2AlarmScope5] using hw)
    have hstream : ∀ w ∈ binList5 a.2.1.coarse, c.2 w = c'.2 w := by
      intro w hw
      exact hW w (by simpa [stage2AlarmScope5] using hw)
    change X.step1Fail (v, c) a.2.1 a.1.1.1.1 (X.p.typeSegs n a.1.1) =
      X.step1Fail (v, c') a.2.1 a.1.1.1.1 (X.p.typeSegs n a.1.1)
    exact propext (step1Fail_ext_bins5 X (v, c) (v, c') a.2.1 a.1.1.1.1
      (X.p.typeSegs n a.1.1) rfl hlocal hstream)
  | inr rest =>
    cases rest with
    | inl a =>
      have hlocal : ∀ w ∈ binList5 a.1.coarse, c.1 w = c'.1 w := by
        intro w hw
        exact hA w (by simpa [stage2AlarmScope5] using hw)
      have hstream : ∀ w ∈ binList5 a.1.coarse, c.2 w = c'.2 w := by
        intro w hw
        exact hW w (by simpa [stage2AlarmScope5] using hw)
      change X.capFail (v, c) a.1 = X.capFail (v, c') a.1
      exact propext (capFail_ext_bins5 X (v, c) (v, c') a.1 rfl hlocal hstream)
    | inr tail =>
      cases tail with
      | inl a =>
        have hlocal : ∀ w ∈ blockLocalBins5 X a.1 a.1.2.1,
            c.1 w = c'.1 w := by
          intro w hw
          exact hA w (by simpa [stage2AlarmScope5] using hw)
        have hstream : ∀ w ∈ blockLocalBins5 X a.1 a.1.2.1,
            c.2 w = c'.2 w := by
          intro w hw
          exact hW w (by simpa [stage2AlarmScope5] using hw)
        have hprob := step2FailPr_ext_bins5 X (v, c) (v, c') a.1 rfl hlocal hstream
        change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n a.1)) / 4) <
            (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) a.1)) =
          (Real.exp (-(X.p.delta * (X.p.q0 * (X.p.typeSegs n a.1))) / 4) <
            (X.hiddenLaw (v, c')).pr (fun U => X.step2Fail ((v, c'), U) a.1))
        rw [hprob]
      | inr a =>
        have hlocal : ∀ w ∈ blockLocalBins5 X a.1.1
            (insert (X.optKeyOf a.1.1 a.1.2) a.1.1.2.1), c.1 w = c'.1 w := by
          intro w hw
          exact hA w (by simpa [stage2AlarmScope5] using hw)
        have hstream : ∀ w ∈ blockLocalBins5 X a.1.1
            (insert (X.optKeyOf a.1.1 a.1.2) a.1.1.2.1), c.2 w = c'.2 w := by
          intro w hw
          exact hW w (by simpa [stage2AlarmScope5] using hw)
        have hprob := optFailPr_ext_bins5 X (v, c) (v, c') a.1.1 a.1.2 rfl hlocal hstream
        change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
            (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) a.1.1 a.1.2)) =
          (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
            (X.hiddenLaw (v, c')).pr (fun U => X.optFail ((v, c'), U) a.1.1 a.1.2))
        rw [hprob]

end

end HypercubeRamsey.Lane_q_s05_h23
