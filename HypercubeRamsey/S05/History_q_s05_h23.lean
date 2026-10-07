import HypercubeRamsey.S05.Experiment
import HypercubeRamsey.S05.History_q_s05_hist2
import HypercubeRamsey.S03.ConditionalAvoidance

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

theorem map_equiv_weight5 {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinProb α) (e : α ≃ β) (b : β) :
    (FinProb.map P e).w b = P.w (e.symm b) := by
  classical
  change (∑ a, if e a = b then P.w a else 0) = P.w (e.symm b)
  rw [Finset.sum_eq_single (e.symm b)]
  · simp [e.apply_symm_apply]
  · intro a ha hne
    have hne' : e a ≠ b := by
      intro heq
      apply hne
      exact e.injective (by simpa using heq)
    simp [hne']
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

def LocalAdj5 {I V : Type*} (sc : I → Finset V) (i j : I) : Prop :=
  i ≠ j ∧ ¬ Disjoint (sc i) (sc j)

structure ProductLLLData5 {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (P : ∀ v, FinProb (α v)) {I : Type*} [Fintype I] [DecidableEq I]
    (Bad : I → (∀ v, α v) → Prop) (sc : I → Finset V) (x : I → ℝ) : Prop where
  x_nonneg : ∀ i, 0 ≤ x i
  x_lt_one : ∀ i, x i < 1
  scope : ∀ i, FinProb.DependsOn (Bad i) (sc i)
  charge : ∀ i, (FinProb.pi P).pr (Bad i) ≤
    x i * ∏ j ∈ Finset.univ.filter (LocalAdj5 sc i), (1 - x j)

theorem prod_one_sub_lower5 {I : Type*} [Fintype I] (S : Finset I) (x : I → ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ x i) (h1 : ∀ i ∈ S, x i ≤ 1) :
    1 - ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 - x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have h0S : ∀ j ∈ S, 0 ≤ x j := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
      have h1S : ∀ j ∈ S, x j ≤ 1 := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ S, x j := Finset.sum_nonneg fun j hj => h0S j hj
      have hi0 : 0 ≤ x i := h0 i (Finset.mem_insert_self i S)
      have hi1 : x i ≤ 1 := h1 i (Finset.mem_insert_self i S)
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 - (x i + ∑ j ∈ S, x j) ≤ (1 - x i) * (1 - ∑ j ∈ S, x j) := by
          nlinarith [mul_nonneg hi0 hsum0]
        _ ≤ (1 - x i) * ∏ j ∈ S, (1 - x j) :=
          mul_le_mul_of_nonneg_left (ih h0S h1S) (sub_nonneg.mpr hi1)

theorem productLLLData_of_budget5 {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (P : ∀ v, FinProb (α v)) {I : Type*} [Fintype I] [DecidableEq I]
    (Bad : I → (∀ v, α v) → Prop) (sc : I → Finset V) (budget : I → ℝ)
    (hscope : ∀ i, FinProb.DependsOn (Bad i) (sc i))
    (hbudget0 : ∀ i, 0 ≤ budget i) (hbudgetHalf : ∀ i, budget i < 1 / 2)
    (hprob : ∀ i, (FinProb.pi P).pr (Bad i) ≤ budget i)
    (hneighbors : ∀ i,
      (∑ j ∈ Finset.univ.filter (LocalAdj5 sc i), budget j) ≤ 1 / 4) :
    ProductLLLData5 P Bad sc (fun i => 2 * budget i) := by
  classical
  refine ⟨?_, ?_, hscope, ?_⟩
  · intro i
    exact mul_nonneg (by norm_num) (hbudget0 i)
  · intro i
    have h := hbudgetHalf i
    nlinarith [hbudget0 i]
  · intro i
    let N := Finset.univ.filter (LocalAdj5 sc i)
    have hbudgetN : (∑ j ∈ N, budget j) ≤ 1 / 4 := by
      simpa [N] using hneighbors i
    have hx0 : ∀ j ∈ N, 0 ≤ 2 * budget j := by
      intro j hj
      exact mul_nonneg (by norm_num) (hbudget0 j)
    have hx1 : ∀ j ∈ N, 2 * budget j ≤ 1 := by
      intro j hj
      have h := hbudgetHalf j
      nlinarith
    have hprod : 1 / 2 ≤ ∏ j ∈ N, (1 - 2 * budget j) := by
      have hsum : (∑ j ∈ N, 2 * budget j) = 2 * ∑ j ∈ N, budget j := by
        rw [Finset.mul_sum]
      have hlower := prod_one_sub_lower5 N (fun j => 2 * budget j) hx0 hx1
      rw [hsum] at hlower
      linarith
    calc
      (FinProb.pi P).pr (Bad i) ≤ budget i := hprob i
      _ = (2 * budget i) * (1 / 2 : ℝ) := by ring
      _ ≤ (2 * budget i) * ∏ j ∈ N, (1 - 2 * budget j) := by
        exact mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) (hbudget0 i))

theorem expect_filter5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Finset Ω) (f : Ω → ℝ)
    [DecidablePred (fun ω => ω ∈ A)] :
    P.expect (fun ω => (if ω ∈ A then 1 else 0) * f ω) =
      ∑ ω ∈ A, P.w ω * f ω := by
  simp only [FinProb.expect]
  have hfilter : Finset.univ.filter (fun ω => ω ∈ A) = A := by
    ext ω
    simp
  calc
    (∑ ω, P.w ω * ((if ω ∈ A then 1 else 0) * f ω)) =
        ∑ ω, if ω ∈ A then P.w ω * f ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hA : ω ∈ A <;> simp [hA] <;> ring
    _ = ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ A), P.w ω * f ω := by
      rw [← Finset.sum_filter]
    _ = ∑ ω ∈ A, P.w ω * f ω := by rw [hfilter]

theorem pr_indicator5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω => if A ω then 1 else 0) := by
  simp [FinProb.pr, FinProb.expect]

theorem map_pr_equiv5 {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinProb α) (e : α ≃ β) (A : β → Prop) :
    (FinProb.map P e).pr A = P.pr (fun a => A (e a)) := by
  classical
  rw [pr_indicator5, FinProb.map_expect]
  exact (pr_indicator5 P (fun a => A (e a))).symm

theorem pr_congr5 {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω ↔ B ω) : P.pr A = P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω
  · have hB := (hAB ω).mp hA
    simp [hA, hB]
  · have hB : ¬ B ω := fun h => hA ((hAB ω).mpr h)
    simp [hA, hB]

theorem pr_exists_le_sum5 {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinProb Ω) (A : I → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  change (∑ ω, if (∃ i, A i ω) then P.w ω else 0) ≤
    ∑ i, ∑ ω, if A i ω then P.w ω else 0
  calc
    (∑ ω, if (∃ i, A i ω) then P.w ω else 0) ≤
        ∑ ω, P.w ω * ∑ i, if A i ω then 1 else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hex : ∃ i, A i ω
      · obtain ⟨i, hi⟩ := hex
        have hsum : (1 : ℝ) ≤ ∑ i', if A i' ω then 1 else 0 := by
          have hs := Finset.single_le_sum
            (s := (Finset.univ : Finset I))
            (fun j hj => by split_ifs <;> positivity) (Finset.mem_univ i)
          simpa [hi] using hs
        have hweight := P.nonneg ω
        simp [hex]
        nlinarith [mul_nonneg hweight (hsum - 1)]
      · simp [hex]
    _ = ∑ i, ∑ ω, if A i ω then P.w ω else 0 := by
      calc
        (∑ ω, P.w ω * ∑ i, if A i ω then 1 else 0) =
            ∑ ω, ∑ i, P.w ω * (if A i ω then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [Finset.mul_sum]
        _ = ∑ i, ∑ ω, P.w ω * (if A i ω then 1 else 0) := Finset.sum_comm
        _ = ∑ i, ∑ ω, if A i ω then P.w ω else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hA : A i ω <;> simp [hA]
    _ = ∑ i, P.pr (A i) := by simp [FinProb.pr]

theorem productAvoidanceLocalCompare5 {V : Type*} [Fintype V] [DecidableEq V]
    {α : V → Type*} [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (P : ∀ v, FinProb (α v)) {I : Type*} [Fintype I] [DecidableEq I]
    (Bad : I → (∀ v, α v) → Prop) (sc : I → Finset V) (x : I → ℝ)
    (hL : ProductLLLData5 P Bad sc x) :
    ∃ Q : FinProb (∀ v, α v),
      (∀ ω, Q.w ω ≠ 0 → ∀ i, ¬ Bad i ω) ∧
      (∀ ω, Q.w ω ≠ 0 → (FinProb.pi P).w ω ≠ 0) ∧
      ∀ (U : Finset V) (Φ : (∀ v, α v) → ℝ),
        (∀ ω, 0 ≤ Φ ω) → FinProb.DependsOn Φ U →
      Q.expect Φ ≤
        (∏ i ∈ Finset.univ.filter (fun i => ¬ Disjoint (sc i) U), (1 - x i))⁻¹ *
          (FinProb.pi P).expect Φ := by
  classical
  let Ω := ∀ v, α v
  letI : DecidableEq Ω := Fintype.decidablePiFintype
  let Pfull : FinProb Ω := FinProb.pi P
  let w : Ω → ℝ := Pfull.w
  let E : I → Finset Ω := fun i => Finset.univ.filter (Bad i)
  let Adj : I → I → Prop := LocalAdj5 sc
  let p : I → ℝ := fun i => Pfull.pr (Bad i)
  have hw : ∀ ω, 0 ≤ w ω := by
    intro ω
    exact Pfull.nonneg ω
  have hw1 : ∑ ω, w ω = 1 := by
    exact Pfull.sum_eq_one
  have hmassPr (A : Ω → Prop) :
      LocalLemma.mass w (Finset.univ.filter A) = Pfull.pr A := by
    simp [LocalLemma.mass, FinProb.pr, Pfull, w, FinProb.pi, Finset.sum_filter]
  have hEProb (i : I) : LocalLemma.mass w (E i) = p i := by
    dsimp [E, p]
    exact hmassPr (Bad i)
  have hscopeE : ∀ i ω ω', (∀ v ∈ sc i, ω v = ω' v) →
      (ω ∈ E i ↔ ω' ∈ E i) := by
    intro i ω ω' heq
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.of_eq (hL.scope i ω ω' heq)
  have hsymm : ∀ i j, Adj i j → Adj j i := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    exact fun hdis => hij.2 hdis.symm
  have hirr : ∀ i, ¬ Adj i i := by
    intro i hi
    exact hi.1 rfl
  have hcond : ∀ i (S : Finset I), i ∉ S → (∀ j ∈ S, ¬ Adj i j) →
      LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) ≤
        p i * LocalLemma.mass w (LocalLemma.avoid E S) := by
    intro i S hiS hsep
    have hdis : ∀ j ∈ S, Disjoint (sc i) (sc j) := by
      intro j hj
      have hne : i ≠ j := by
        intro hEq
        exact hiS (hEq ▸ hj)
      by_contra hnot
      exact hsep j hj ⟨hne, hnot⟩
    have hind := LocalLemma.mass_inter_avoid_of_disjoint_scopes
      (fun v a => (P v).w a) (fun v a => (P v).nonneg a) (fun v => (P v).sum_eq_one)
      E sc hscopeE i S hdis
    have hind' : LocalLemma.mass w (E i ∩ LocalLemma.avoid E S) =
        LocalLemma.mass w (E i) * LocalLemma.mass w (LocalLemma.avoid E S) := by
      simpa [w, Pfull, FinProb.pi] using hind
    rw [hind', hEProb]
  have hpx : ∀ i, p i ≤ x i * ∏ j ∈ Finset.univ.filter (Adj i), (1 - x j) := by
    intro i
    exact hL.charge i
  have hca := LocalLemma.conditional_avoidance w hw hw1 E Adj hsymm hirr p x
    hcond hL.x_nonneg hL.x_lt_one hpx
  let allGood := LocalLemma.avoid E Finset.univ
  let goodAll : Ω → Prop := fun ω => ∀ i, ω ∉ E i
  have hallSet : allGood = Finset.univ.filter goodAll := by
    ext ω
    simp [allGood, goodAll, LocalLemma.avoid]
  have hfilterGoodSet : Finset.univ.filter (fun ω => ω ∈ allGood) = allGood := by
    ext ω
    simp
  let massAll : ℝ := LocalLemma.mass w allGood
  have hmassAllpos : 0 < massAll := by
    exact hca.1
  have hsumGood : (∑ ω, if ω ∈ allGood then w ω else 0) = massAll := by
    calc
      (∑ ω, if ω ∈ allGood then w ω else 0) =
          ∑ ω ∈ allGood, w ω := by rw [← Finset.sum_filter, hfilterGoodSet]
      _ = massAll := by simp [massAll, LocalLemma.mass]
  let Q : FinProb Ω := {
    w := fun ω => (if ω ∈ allGood then w ω else 0) / massAll
    nonneg := by
      intro ω
      apply div_nonneg
      · split_ifs <;> simp [hw ω]
      · exact hmassAllpos.le
    sum_eq_one := by
      rw [← Finset.sum_div, hsumGood]
      exact div_self (ne_of_gt hmassAllpos)
  }
  have hQsupport : ∀ ω, Q.w ω ≠ 0 → ∀ i, ¬ Bad i ω := by
    intro ω hω i hbad
    have hnot : ω ∉ allGood := by
      intro hmem
      have hgood := (show ω ∈ allGood ↔ goodAll ω by rw [hallSet]; simp).mp hmem
      exact hgood i (by simp [E, hbad])
    have hzero : Q.w ω = 0 := by simp [Q, hnot]
    exact hω hzero
  have hQraw : ∀ ω, Q.w ω ≠ 0 → Pfull.w ω ≠ 0 := by
    intro ω hω
    by_contra hzero
    have hz : Q.w ω = 0 := by
      by_cases hgood : ω ∈ allGood
      · have hweight : w ω = 0 := hzero
        simp [Q, hgood, hweight]
      · simp [Q, hgood]
    exact hω hz
  refine ⟨Q, hQsupport, hQraw, ?_⟩
  intro U Φ hΦ hΦdep
  let S : Finset I := Finset.univ.filter fun i => Disjoint (sc i) U
  let T : Finset I := Finset.univ.filter fun i => ¬ Disjoint (sc i) U
  have hST : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro i hiS hiT
    exact (Finset.mem_filter.mp hiT).2 (Finset.mem_filter.mp hiS).2
  have hcover : S ∪ T = Finset.univ := by
    ext i
    by_cases hdis : Disjoint (sc i) U <;> simp [S, T, hdis]
  have hAvoidST : LocalLemma.avoid E (S ∪ T) = LocalLemma.avoid E Finset.univ := by
    rw [hcover]
  have hsubAvoid : LocalLemma.avoid E Finset.univ ⊆ LocalLemma.avoid E S := by
    intro ω hω
    simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    intro i hi
    exact hω i trivial
  have hmassSpos : 0 < LocalLemma.mass w (LocalLemma.avoid E S) := by
    have hmono : LocalLemma.mass w (LocalLemma.avoid E Finset.univ) ≤
        LocalLemma.mass w (LocalLemma.avoid E S) := by
      unfold LocalLemma.mass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubAvoid (fun ω _ _ => hw ω)
    exact lt_of_lt_of_le hca.1 hmono
  let IndS : Ω → ℝ := fun ω => if ω ∈ LocalLemma.avoid E S then 1 else 0
  have hnum (R : Finset I) :
      (∑ ω ∈ LocalLemma.avoid E R, w ω * Φ ω) =
        Pfull.expect (fun ω => (if ω ∈ LocalLemma.avoid E R then 1 else 0) * Φ ω) := by
    simpa [w] using (expect_filter5 Pfull (LocalLemma.avoid E R) Φ).symm
  have hdepIndS : FinProb.DependsOn IndS (S.biUnion sc) := by
    intro ω ω' heq
    have havoids : ω ∈ LocalLemma.avoid E S ↔ ω' ∈ LocalLemma.avoid E S := by
      simp only [LocalLemma.avoid, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hgood i hiS
        have heqE := hscopeE i ω ω'
          (fun v hv => heq v (Finset.mem_biUnion.mpr ⟨i, hiS, hv⟩))
        exact fun hmem => hgood i hiS (heqE.mpr hmem)
      · intro hgood i hiS
        have heqE := hscopeE i ω ω'
          (fun v hv => heq v (Finset.mem_biUnion.mpr ⟨i, hiS, hv⟩))
        exact fun hmem => hgood i hiS (heqE.mp hmem)
    simp [IndS, havoids]
  have hdis : Disjoint (S.biUnion sc) U := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvU
    obtain ⟨i, hiS, hvi⟩ := Finset.mem_biUnion.mp hvS
    exact (Finset.disjoint_left.mp (Finset.mem_filter.mp hiS).2) hvi hvU
  have hIndPr : Pfull.expect IndS = LocalLemma.mass w (LocalLemma.avoid E S) := by
    simpa [IndS, w, LocalLemma.mass] using
      (expect_filter5 Pfull (LocalLemma.avoid E S) (fun _ => 1))
  have hIndependence := FinProb.pi_expect_mul_of_disjoint P IndS Φ
    (S.biUnion sc) U hdepIndS hΦdep hdis
  have hratioS :
      (∑ ω ∈ LocalLemma.avoid E S, w ω * Φ ω) /
          LocalLemma.mass w (LocalLemma.avoid E S) = Pfull.expect Φ := by
    rw [hnum S, hIndependence, hIndPr]
    field_simp [ne_of_gt hmassSpos]
    ring
  have hQexp : Q.expect Φ =
      (∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω) /
        LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
    have hnumAll : Pfull.expect (fun ω => (if ω ∈ allGood then 1 else 0) * Φ ω) =
        ∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω := by
      simpa [w] using (expect_filter5 Pfull allGood Φ)
    calc
      Q.expect Φ =
          (Pfull.expect (fun ω => (if ω ∈ allGood then 1 else 0) * Φ ω)) / massAll := by
            change (∑ ω, ((if ω ∈ allGood then w ω else 0) / massAll) * Φ ω) = _
            calc
              (∑ ω, ((if ω ∈ allGood then w ω else 0) / massAll) * Φ ω) =
                  ∑ ω, (w ω * ((if ω ∈ allGood then 1 else 0) * Φ ω)) / massAll := by
                apply Finset.sum_congr rfl
                intro ω hω
                by_cases hgood : ω ∈ allGood <;> simp [hgood] <;> ring
              _ = (∑ ω, w ω * ((if ω ∈ allGood then 1 else 0) * Φ ω)) / massAll :=
                (Finset.sum_div _ _ _).symm
              _ = Pfull.expect (fun ω => (if ω ∈ allGood then 1 else 0) * Φ ω) / massAll := by
                rfl
      _ = (∑ ω ∈ LocalLemma.avoid E Finset.univ, w ω * Φ ω) /
          LocalLemma.mass w (LocalLemma.avoid E Finset.univ) := by
        rw [hnumAll]
  have hcompare := hca.2.2.1 S T hST Φ hΦ
  rw [hAvoidST] at hcompare
  rw [← hQexp, hratioS] at hcompare
  simpa [T] using hcompare

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

theorem prior_irrel_sign5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (ℓ ℓ' : X.Key) (hcoarse : ℓ.coarse = ℓ'.coarse) (hlevel : ℓ.level = ℓ'.level) :
    X.prior b ℓ = X.prior b ℓ' := by
  have hweight : ∀ y, X.colWeight b ℓ b.2.2 (fun _ _ => True) y =
      X.colWeight b ℓ' b.2.2 (fun _ _ => True) y := by
    intro y
    simp [Setup5.colWeight, hcoarse, hlevel]
  change normalize5 (X.colWeight b ℓ b.2.2 (fun _ _ => True)) X.y₀ =
      normalize5 (X.colWeight b ℓ' b.2.2 (fun _ _ => True)) X.y₀
  exact congrArg (fun f : Fin N → ℝ => normalize5 f X.y₀) (funext hweight)

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

theorem priorDel_irrel_sign5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (ℓ ℓ' : X.Key) (w : BinVector5 n) (k : ℕ)
    (hcoarse : ℓ.coarse = ℓ'.coarse) (hlevel : ℓ.level = ℓ'.level) :
    X.priorDel b ℓ w k = X.priorDel b ℓ' w k := by
  have hweight : ∀ y, X.colWeight b ℓ b.2.2
      (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) y =
        X.colWeight b ℓ' b.2.2 (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k)) y := by
    intro y
    simp [Setup5.colWeight, hcoarse, hlevel]
  change normalize5 (X.colWeight b ℓ b.2.2
      (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k))) X.y₀ =
    normalize5 (X.colWeight b ℓ' b.2.2
      (fun w' s => ¬ (w' = w ∧ (s : ℕ) < k))) X.y₀
  exact congrArg (fun f : Fin N → ℝ => normalize5 f X.y₀) (funext hweight)

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

theorem priorRep_irrel_sign5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (ℓ ℓ' : X.Key) (w : BinVector5 n) {k : ℕ} (z : Fin k → Word5 N X.p.q0)
    (hcoarse : ℓ.coarse = ℓ'.coarse) (hlevel : ℓ.level = ℓ'.level) :
    X.priorRep b ℓ w z = X.priorRep b ℓ' w z := by
  have hweight : ∀ y, X.colWeight b ℓ (X.replaceStream b.2.2 w z) (fun _ _ => True) y =
      X.colWeight b ℓ' (X.replaceStream b.2.2 w z) (fun _ _ => True) y := by
    intro y
    simp [Setup5.colWeight, hcoarse, hlevel]
  change normalize5 (X.colWeight b ℓ (X.replaceStream b.2.2 w z) (fun _ _ => True)) X.y₀ =
      normalize5 (X.colWeight b ℓ' (X.replaceStream b.2.2 w z) (fun _ _ => True)) X.y₀
  exact congrArg (fun f : Fin N → ℝ => normalize5 f X.y₀) (funext hweight)

def shiftSignVector5 {m : ℕ} (t s : CubeVertex m) : CubeVertex m :=
  fun h => if t h then !s h else s h

theorem shiftSignVector_self5 {m : ℕ} (t : CubeVertex m) :
    shiftSignVector5 t t = default := by
  funext h
  by_cases ht : t h <;> simp [shiftSignVector5, ht]

theorem shiftSignVector_update5 {m : ℕ} (t : CubeVertex m) (h : Fin m) :
    shiftSignVector5 t (Function.update t h (!t h)) =
      Function.update (default : CubeVertex m) h true := by
  funext k
  by_cases hk : k = h
  · subst k
    cases ht : t h <;> simp [shiftSignVector5, Function.update, ht]
  · simp [shiftSignVector5, Function.update_of_ne hk]

theorem shiftSignVector_involutive5 {m : ℕ} (t s : CubeVertex m) :
    shiftSignVector5 t (shiftSignVector5 t s) = s := by
  funext h
  by_cases ht : t h <;> simp [shiftSignVector5, ht]

noncomputable def signShiftKey5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) : X.Key ≃ X.Key where
  toFun := fun ℓ =>
    match ℓ with
    | .inl q => .inl (q.1, shiftSignVector5 t q.2.1, q.2.2)
    | .inr i => .inr i
  invFun := fun ℓ =>
    match ℓ with
    | .inl q => .inl (q.1, shiftSignVector5 t q.2.1, q.2.2)
    | .inr i => .inr i
  left_inv := by
    intro ℓ
    cases ℓ with
    | inl q =>
        rcases q with ⟨i, s, j⟩
        change Sum.inl (i, shiftSignVector5 t (shiftSignVector5 t s), j) = Sum.inl (i, s, j)
        apply congrArg Sum.inl
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact shiftSignVector_involutive5 t s
          · rfl
    | inr i => rfl
  right_inv := by
    intro ℓ
    cases ℓ with
    | inl q =>
        rcases q with ⟨i, s, j⟩
        change Sum.inl (i, shiftSignVector5 t (shiftSignVector5 t s), j) = Sum.inl (i, s, j)
        apply congrArg Sum.inl
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact shiftSignVector_involutive5 t s
          · rfl
    | inr i => rfl

theorem signShiftKey5_apply_apply (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    signShiftKey5 X t (signShiftKey5 X t ℓ) = ℓ :=
  (signShiftKey5 X t).left_inv ℓ

theorem signShiftKey5_keyAt5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (i : CoarseKey5 n) (s : CubeVertex (X.p.m n))
    (k : ℕ) :
    signShiftKey5 X t (keyAt5 (X.p.J n) i s k) =
      keyAt5 (X.p.J n) i (shiftSignVector5 t s) k := by
  by_cases hk : k ≤ X.p.J n <;> simp [keyAt5, hk, signShiftKey5]

theorem signShiftKey5_coarse (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    (signShiftKey5 X t ℓ).coarse = ℓ.coarse := by
  cases ℓ <;> rfl

theorem signShiftKey5_level (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    (signShiftKey5 X t ℓ).level = ℓ.level := by
  cases ℓ <;> rfl

theorem signShiftKey5_colLen (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    colLen5 (X.p.s n) (signShiftKey5 X t ℓ) = colLen5 (X.p.s n) ℓ := by
  cases ℓ <;> rfl

theorem prior_signShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    X.prior b (signShiftKey5 X t ℓ) = X.prior b ℓ := by
  exact prior_irrel_sign5 X b (signShiftKey5 X t ℓ) ℓ
    (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)

abbrev LowKey5 (X : Setup5 γ K' χ n N E G) :=
  CoarseKey5 n × CubeVertex (X.p.m n) × Fin (X.p.J n + 1)

noncomputable def signShiftLowKey5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) : LowKey5 X ≃ LowKey5 X where
  toFun q := (q.1, shiftSignVector5 t q.2.1, q.2.2)
  invFun q := (q.1, shiftSignVector5 t q.2.1, q.2.2)
  left_inv := by
    intro q
    rcases q with ⟨i, s, j⟩
    change (i, shiftSignVector5 t (shiftSignVector5 t s), j) = (i, s, j)
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact shiftSignVector_involutive5 t s
      · rfl
  right_inv := by
    intro q
    rcases q with ⟨i, s, j⟩
    change (i, shiftSignVector5 t (shiftSignVector5 t s), j) = (i, s, j)
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact shiftSignVector_involutive5 t s
      · rfl

theorem signShiftLowKey5_apply_apply (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (q : LowKey5 X) :
    signShiftLowKey5 X t (signShiftLowKey5 X t q) = q :=
  (signShiftLowKey5 X t).left_inv q

abbrev HiddenLow5 (X : Setup5 γ K' χ n N E G) := LowKey5 X → Fin 1 → Fin N
abbrev HiddenHigh5 (X : Setup5 γ K' χ n N E G) :=
  CoarseKey5 n → Fin (X.p.s n) → Fin N
abbrev HiddenSplit5 (X : Setup5 γ K' χ n N E G) := HiddenLow5 X × HiddenHigh5 X

noncomputable def hiddenSplitEquiv5 (X : Setup5 γ K' χ n N E G) :
    X.Hidden ≃ HiddenSplit5 X where
  toFun U := (fun k h => U (.inl k) h, fun i h => U (.inr i) h)
  invFun q := fun ℓ =>
    match ℓ with
    | .inl k => q.1 k
    | .inr i => q.2 i
  left_inv := by
    intro U
    funext ℓ
    cases ℓ <;> funext h <;> rfl
  right_inv := by
    intro q
    apply Prod.ext
    · funext k
      funext h
      rfl
    · funext i
      funext h
      rfl

noncomputable def hiddenLowShift5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) : HiddenLow5 X ≃ HiddenLow5 X where
  toFun U := fun k h => U (signShiftLowKey5 X t k) h
  invFun U := fun k h => U (signShiftLowKey5 X t k) h
  left_inv := by
    intro U
    funext k
    funext h
    change U (signShiftLowKey5 X t (signShiftLowKey5 X t k)) h = U k h
    rw [signShiftLowKey5_apply_apply]
  right_inv := by
    intro U
    funext k
    funext h
    change U (signShiftLowKey5 X t (signShiftLowKey5 X t k)) h = U k h
    rw [signShiftLowKey5_apply_apply]

noncomputable def hiddenSignShift5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) : X.Hidden ≃ X.Hidden :=
  (hiddenSplitEquiv5 X).trans
    ((Equiv.prodCongr (hiddenLowShift5 X t) (Equiv.refl _)).trans (hiddenSplitEquiv5 X).symm)

theorem hiddenSignShift5_apply_low (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (U : X.Hidden) (k : LowKey5 X) (h : Fin 1) :
    hiddenSignShift5 X t U (.inl k) h = U (.inl (signShiftLowKey5 X t k)) h := rfl

theorem hiddenSignShift5_apply_high (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (U : X.Hidden) (i : CoarseKey5 n)
    (h : Fin (X.p.s n)) :
    hiddenSignShift5 X t U (.inr i) h = U (.inr i) h := rfl

noncomputable def finCastEquiv5 {a b : ℕ} (h : a = b) : Fin a ≃ Fin b where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv := by intro i; simp
  right_inv := by intro i; simp

theorem hiddenSignShift5_apply_signShiftKey (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (U : X.Hidden) (ℓ : X.Key)
    (h : Fin (colLen5 (X.p.s n) (signShiftKey5 X t ℓ))) :
    hiddenSignShift5 X t U (signShiftKey5 X t ℓ) h =
      U ℓ (Fin.cast (signShiftKey5_colLen X t ℓ) h) := by
  cases ℓ with
  | inl q =>
      rcases q with ⟨i, s, j⟩
      have hcast : Fin.cast (signShiftKey5_colLen X t (.inl (i, s, j))) h = h := by
        apply Fin.ext
        rfl
      calc
        hiddenSignShift5 X t U (signShiftKey5 X t (.inl (i, s, j))) h =
            U (.inl (signShiftLowKey5 X t (signShiftLowKey5 X t (i, s, j)))) h := by
              simpa [signShiftKey5, signShiftLowKey5] using
                (hiddenSignShift5_apply_low X t U (signShiftLowKey5 X t (i, s, j)) h)
        _ = U (.inl (i, s, j)) h := by rw [signShiftLowKey5_apply_apply]
        _ = U (.inl (i, s, j)) (Fin.cast (signShiftKey5_colLen X t (.inl (i, s, j))) h) :=
          by rw [hcast]
  | inr i =>
      have hcast : Fin.cast (signShiftKey5_colLen X t (.inr i)) h = h := by
        apply Fin.ext
        rfl
      calc
        hiddenSignShift5 X t U (.inr i) h = U (.inr i) h := hiddenSignShift5_apply_high X t U i h
        _ = U (.inr i) (Fin.cast (signShiftKey5_colLen X t (.inr i)) h) := by rw [hcast]

noncomputable def signShiftHistory5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (H : X.KeyHist) : X.KeyHist :=
  (H.1, hiddenSignShift5 X t H.2)

theorem hiddenLaw_weight_signShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (U : X.Hidden) :
    (X.hiddenLaw b).w (hiddenSignShift5 X t U) = (X.hiddenLaw b).w U := by
  classical
  let e := signShiftLowKey5 X t
  have hLowPi (V : X.Hidden) :
      (∏ k : LowKey5 X,
        (FinProb.pi (fun _ : Fin 1 => X.prior b (.inl k))).w (V (.inl k))) *
      (∏ i : CoarseKey5 n,
        (FinProb.pi (fun _ : Fin (X.p.s n) => X.prior b (.inr i))).w (V (.inr i)) ) =
        (X.hiddenLaw b).w V := by
    change (∏ k : LowKey5 X,
        (FinProb.pi (fun _ : Fin 1 => X.prior b (.inl k))).w (V (.inl k))) *
      (∏ i : CoarseKey5 n,
        (FinProb.pi (fun _ : Fin (X.p.s n) => X.prior b (.inr i))).w (V (.inr i))) =
      ∏ ℓ : X.Key,
        (FinProb.pi (fun _ : Fin (colLen5 (X.p.s n) ℓ) => X.prior b ℓ)).w (V ℓ)
    rw [Fintype.prod_sum_type]
    rfl
  have hLow (V : X.Hidden) :
      (∏ k : LowKey5 X, ∏ h : Fin 1,
        (X.prior b (.inl k)).w (V (.inl k) h)) *
      (∏ i : CoarseKey5 n, ∏ h : Fin (X.p.s n),
        (X.prior b (.inr i)).w (V (.inr i) h)) = (X.hiddenLaw b).w V := by
    simpa only [FinProb.pi] using hLowPi V
  have hlowInvariant :
      ∏ k : LowKey5 X, ∏ h : Fin 1,
        (X.prior b (.inl k)).w (U (.inl (e k)) h) =
      ∏ k : LowKey5 X, ∏ h : Fin 1,
        (X.prior b (.inl k)).w (U (.inl k) h) := by
    calc
      (∏ k : LowKey5 X, ∏ h : Fin 1,
          (X.prior b (.inl k)).w (U (.inl (e k)) h)) =
        ∏ k : LowKey5 X, ∏ h : Fin 1,
          (X.prior b (.inl (e.symm k))).w (U (.inl k) h) := by
            exact Fintype.prod_equiv e
              (fun k => ∏ h : Fin 1, (X.prior b (.inl k)).w (U (.inl (e k)) h))
              (fun k => ∏ h : Fin 1, (X.prior b (.inl (e.symm k))).w (U (.inl k) h))
              (by
                intro k
                have hprior : X.prior b (.inl k) = X.prior b (.inl (e (e k))) := by
                  apply prior_irrel_sign5 <;> rfl
                apply Finset.prod_congr rfl
                intro h hh
                exact congrArg (fun L : Law N => L.w (U (.inl (e k)) h)) hprior)
      _ = ∏ k : LowKey5 X, ∏ h : Fin 1,
          (X.prior b (.inl k)).w (U (.inl k) h) := by
            apply Finset.prod_congr rfl
            intro k hk
            apply Finset.prod_congr rfl
            intro h hh
            have hprior : X.prior b (.inl (e.symm k)) = X.prior b (.inl k) := by
              apply prior_irrel_sign5
              · rfl
              · rfl
            exact congrArg (fun L : Law N => L.w (U (.inl k) h)) hprior
  calc
    (X.hiddenLaw b).w (hiddenSignShift5 X t U) =
        (∏ k : LowKey5 X, ∏ h : Fin 1,
          (X.prior b (.inl k)).w (U (.inl (e k)) h)) *
          (∏ i : CoarseKey5 n, ∏ h : Fin (X.p.s n),
            (X.prior b (.inr i)).w (U (.inr i) h)) := by
          simpa [hiddenSignShift5, hiddenSplitEquiv5, hiddenLowShift5, e,
            signShiftLowKey5] using (hLow (hiddenSignShift5 X t U)).symm
    _ = (∏ k : LowKey5 X, ∏ h : Fin 1,
          (X.prior b (.inl k)).w (U (.inl k) h)) *
          (∏ i : CoarseKey5 n, ∏ h : Fin (X.p.s n),
            (X.prior b (.inr i)).w (U (.inr i) h)) := by rw [hlowInvariant]
    _ = (X.hiddenLaw b).w U := hLow U

theorem hiddenLaw_map_signShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) :
    FinProb.map (X.hiddenLaw b) (hiddenSignShift5 X t) = X.hiddenLaw b := by
  classical
  apply FinProb.ext
  intro U
  rw [map_equiv_weight5]
  have h := hiddenLaw_weight_signShift5 X b t ((hiddenSignShift5 X t).symm U)
  have he : hiddenSignShift5 X t ((hiddenSignShift5 X t).symm U) = U :=
    (hiddenSignShift5 X t).apply_symm_apply U
  rw [he] at h
  exact h.symm

noncomputable def signShiftType5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) : X.Ty :=
  (K.1, K.2.1.image (signShiftKey5 X t), K.2.2)

theorem signShiftType5_eq_of_highKeys (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    signShiftType5 X t K = K := by
  classical
  let e := signShiftKey5 X t
  have hS : K.2.1.image e = K.2.1 := by
    ext ℓ
    constructor
    · intro h
      obtain ⟨ℓ₀, hℓ₀, heq⟩ := Finset.mem_image.mp h
      rcases hHigh ℓ₀ hℓ₀ with ⟨i, rfl⟩
      have heq' : (Sum.inr i : X.Key) = ℓ := by simpa [e, signShiftKey5] using heq
      simpa [heq'] using hℓ₀
    · intro hℓ
      rcases hHigh ℓ hℓ with ⟨i, rfl⟩
      exact Finset.mem_image.mpr ⟨.inr i, hℓ, rfl⟩
  change (K.1, K.2.1.image e, K.2.2) = K
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hS
    · rfl

theorem signShiftType5_center (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    (signShiftType5 X t K).1.1 = K.1.1 := rfl

theorem signShiftType5_level (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    (signShiftType5 X t K).2.2 = K.2.2 := rfl

theorem signShiftType5_keys_card (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    (signShiftType5 X t K).2.1.card = K.2.1.card := by
  change (K.2.1.image (signShiftKey5 X t)).card = K.2.1.card
  exact Finset.card_image_of_injective _ (signShiftKey5 X t).injective

theorem gateKeys_signShiftLow5 (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    X.gateKeys (signShiftType5 X t K) =
      (X.gateKeys K).image (signShiftKey5 X t) := by
  simp [Setup5.gateKeys, signShiftType5, hlevel]

theorem signShiftType5_segs (X : Setup5 γ K' χ n N E G)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) :
    X.p.typeSegs n (signShiftType5 X t K) = X.p.typeSegs n K := by
  simp [Params5.typeSegs, signShiftType5]

theorem typeOccurs_highKeys5 (X : Setup5 γ K' χ n N E G) (K : X.Ty)
    (hK : X.TypeOccurs K) (hnone : K.2.2 = none) :
    ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i := by
  classical
  rcases hK with ⟨x, hx, htype⟩
  have hnone' : (X.g.evenType (X.p.J n) x).2.2 = none := by rw [htype, hnone]
  have hsev : X.g.severity x > X.p.J n := by
    by_contra hnot
    have hle : X.g.severity x ≤ X.p.J n := Nat.not_lt.mp hnot
    have hfalse : (some (⟨X.g.severity x, Nat.lt_succ_of_le hle⟩ :
        Fin (X.p.J n + 1)) : Option (Fin (X.p.J n + 1))) = none := by
      simpa [ChunkGeometry5.evenType, hle] using hnone'
    cases hfalse
  have htypeKeys : X.g.typeKeys (X.p.J n) x =
      (X.g.coarseRange x).image (fun i => (.inr i : X.Key)) := by
    simp [ChunkGeometry5.typeKeys, not_le_of_gt hsev]
  have hkeys : K.2.1 = (X.g.coarseRange x).image (fun i => (.inr i : X.Key)) := by
    calc
      K.2.1 = (X.g.evenType (X.p.J n) x).2.1 := by rw [htype]
      _ = X.g.typeKeys (X.p.J n) x := rfl
      _ = _ := htypeKeys
  intro ℓ hℓ
  rw [hkeys] at hℓ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
  exact ⟨i, rfl⟩

theorem optOccurs_high5 (X : Setup5 γ K' χ n N E G) (K : X.Ty)
    (t : CubeVertex (X.p.m n)) (hOpt : X.OptOccurs K t) : K.2.2 = none := by
  classical
  rcases hOpt with ⟨x, hx, htype, hoptional⟩
  have hsev : X.g.severity x = X.p.J n + 1 := by
    by_cases h : X.g.severity x = X.p.J n + 1
    · exact h
    · have hnone : X.g.optionalKey (X.p.J n) x = none := by
        simp [ChunkGeometry5.optionalKey, h]
      rw [hnone] at hoptional
      cases hoptional
  have hthird := congrArg (fun T : X.Ty => T.2.2) htype
  have hthird' : (X.g.evenType (X.p.J n) x).2.2 = none := by
    simp [ChunkGeometry5.evenType, hsev]
  calc
    K.2.2 = (X.g.evenType (X.p.J n) x).2.2 := hthird.symm
    _ = none := hthird'

theorem flippable_card_le_severity5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) : (X.g.flippable x).card ≤ X.g.severity x := by
  classical
  unfold ChunkGeometry5.flippable ChunkGeometry5.severity
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

theorem typeKeys_card_le_severity5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) :
    (X.g.typeKeys (X.p.J n) x).card ≤
      coarseChunkCount5 * 4 + 1 + X.g.severity x + 2 := by
  classical
  unfold ChunkGeometry5.typeKeys
  by_cases hlow : X.g.severity x ≤ X.p.J n
  · rw [if_pos hlow]
    calc
      _ ≤ (X.g.coarseRange x).card + (X.g.flippable x).card + 2 := by
        have hlast : (({X.g.severity x + 1} : Finset ℕ) ∪
            (if 0 < X.g.severity x then {X.g.severity x - 1} else ∅)).card ≤ 2 := by
          split_ifs
          · exact (Finset.card_union_le _ _).trans (by simp)
          · simp
        have h1 := Finset.card_union_le
          ((X.g.coarseRange x).image (fun i => keyAt5 (X.p.J n) i
            (X.g.sign x) (X.g.severity x)))
          ((X.g.flippable x).image (fun h => keyAt5 (X.p.J n) (X.g.key x)
            (Function.update (X.g.sign x) h (!X.g.sign x h)) (X.g.severity x)))
        have h2 := Finset.card_union_le
          (((X.g.coarseRange x).image (fun i => keyAt5 (X.p.J n) i
            (X.g.sign x) (X.g.severity x))) ∪
            ((X.g.flippable x).image (fun h => keyAt5 (X.p.J n) (X.g.key x)
              (Function.update (X.g.sign x) h (!X.g.sign x h)) (X.g.severity x))))
          (Finset.image (fun j' => keyAt5 (X.p.J n) (X.g.key x) (X.g.sign x) j')
            (({X.g.severity x + 1} : Finset ℕ) ∪
              (if 0 < X.g.severity x then {X.g.severity x - 1} else ∅)))
        have h3 := Finset.card_image_le
          (s := X.g.coarseRange x)
          (f := fun i => keyAt5 (X.p.J n) i (X.g.sign x) (X.g.severity x))
        have h4 := Finset.card_image_le
          (s := X.g.flippable x)
          (f := fun h => keyAt5 (X.p.J n) (X.g.key x)
            (Function.update (X.g.sign x) h (!X.g.sign x h)) (X.g.severity x))
        have h5 := Finset.card_image_le
          (s := ({X.g.severity x + 1} : Finset ℕ) ∪
            (if 0 < X.g.severity x then {X.g.severity x - 1} else ∅))
          (f := fun j' => keyAt5 (X.p.J n) (X.g.key x) (X.g.sign x) j')
        omega
      _ ≤ coarseChunkCount5 * 4 + 1 + X.g.severity x + 2 := by
        have hc := X.g.coarseRange_card_le x
        have hf := flippable_card_le_severity5 X x
        omega
  · rw [if_neg hlow]
    have hc := X.g.coarseRange_card_le x
    have hi := Finset.card_image_le (s := X.g.coarseRange x)
      (f := fun i => (Sum.inr i : X.Key))
    omega

theorem card_smallSubsets_le5 {α : Type*} [Fintype α] [DecidableEq α]
    (j : ℕ) (hj : j ≤ Fintype.card α) (hα : 0 < Fintype.card α) :
    (Finset.univ.filter fun S : Finset α => S.card ≤ j).card ≤
      (j + 1) * (Fintype.card α) ^ j := by
  classical
  let I : Finset ℕ := Finset.range (j + 1)
  let F : Finset (Finset α) := I.biUnion fun k => (Finset.univ : Finset α).powersetCard k
  have hF : F = Finset.univ.filter fun S : Finset α => S.card ≤ j := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hS
      obtain ⟨k, hk, hpow⟩ := Finset.mem_biUnion.mp hS
      have hmem := Finset.mem_powersetCard.mp hpow
      rw [hmem.2]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (by simpa [I] using hk))
    · intro hS
      have hk : S.card ∈ I := by
        simpa [I, Nat.lt_succ_iff] using hS
      apply Finset.mem_biUnion.mpr
      refine ⟨S.card, hk, ?_⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  calc
    (Finset.univ.filter fun S : Finset α => S.card ≤ j).card = F.card := by rw [← hF]
    _ ≤ ∑ k ∈ I, ((Finset.univ : Finset α).powersetCard k).card := by
      exact Finset.card_biUnion_le
    _ = ∑ k ∈ I, Nat.choose (Fintype.card α) k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.card_powersetCard]
    _ ≤ ∑ k ∈ I, (Fintype.card α) ^ j := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp (by simpa [I] using hk))
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hα hk')
    _ = (j + 1) * (Fintype.card α) ^ j := by simp [I]

def smallSubsets5 (m j : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.range (j + 1)).biUnion fun k => (Finset.univ : Finset (Fin m)).powersetCard k

theorem mem_smallSubsets5 {m j : ℕ} (F : Finset (Fin m)) :
    F ∈ smallSubsets5 m j ↔ F.card ≤ j := by
  simp only [smallSubsets5, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  constructor
  · rintro ⟨k, hk, hcard⟩
    omega
  · intro hF
    exact ⟨F.card, by omega, rfl⟩

def lowTypeFromData5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1))
    (C : Finset (CoarseKey5 n)) (F : Finset (Fin (X.p.m n))) : X.Ty :=
  (q, C.image (fun i => keyAt5 (X.p.J n) i t j.val) ∪
    F.image (fun h => keyAt5 (X.p.J n) q (Function.update t h (!t h)) j.val) ∪
    (({j.val + 1} : Finset ℕ) ∪
      (if 0 < j.val then {j.val - 1} else ∅)).image
        (fun k => keyAt5 (X.p.J n) q t k), some j)

def lowTypeCandidates5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1)) : Finset X.Ty :=
  ((nearCoarseKeys5 q.1).powerset.product (smallSubsets5 (X.p.m n) j.val)).image
    (fun d => lowTypeFromData5 X q t j d.1 d.2)

theorem lowTypeCandidates_card5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1))
    (hJ : j.val ≤ X.p.m n) (hm : 0 < X.p.m n) (D : ℕ)
    (hD : (nearCoarseKeys5 q.1).card ≤ D) :
    (lowTypeCandidates5 X q t j).card ≤
      2 ^ D * (j.val + 1) * (X.p.m n) ^ j.val := by
  classical
  have hj' : j.val ≤ Fintype.card (Fin (X.p.m n)) := by simpa using hJ
  have hm' : 0 < Fintype.card (Fin (X.p.m n)) := by simpa using hm
  have hsmall0 := card_smallSubsets_le5 (α := Fin (X.p.m n)) j.val hj' hm'
  have hsmallSet : smallSubsets5 (X.p.m n) j.val =
      Finset.univ.filter fun F : Finset (Fin (X.p.m n)) => F.card ≤ j.val := by
    ext F
    simp [mem_smallSubsets5]
  have hsmall : (smallSubsets5 (X.p.m n) j.val).card ≤
      (j.val + 1) * (X.p.m n) ^ j.val := by
    rw [hsmallSet]
    simpa using hsmall0
  calc
    (lowTypeCandidates5 X q t j).card ≤
        ((nearCoarseKeys5 q.1).powerset.product (smallSubsets5 (X.p.m n) j.val)).card :=
      Finset.card_image_le
    _ = ((nearCoarseKeys5 q.1).powerset.card) * (smallSubsets5 (X.p.m n) j.val).card :=
      Finset.card_product _ _
    _ ≤ 2 ^ D * ((j.val + 1) * (X.p.m n) ^ j.val) := by
      apply Nat.mul_le_mul
      · simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hD
      · exact hsmall
    _ = 2 ^ D * (j.val + 1) * (X.p.m n) ^ j.val := by ring

theorem normalizedEvenType_mem_candidates5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (j : Fin (X.p.J n + 1)) (hj : X.g.severity x = j.val) :
    signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x) ∈
      lowTypeCandidates5 X (X.g.key x) default j := by
  classical
  have hlow : X.g.severity x ≤ X.p.J n := by have := j.isLt; omega
  have hjle : j.val ≤ X.p.J n := by rw [← hj]; exact hlow
  let t := X.g.sign x
  let C := X.g.coarseRange x
  let F := X.g.flippable x
  let D : Finset ℕ := ({j.val + 1} : Finset ℕ) ∪
    (if 0 < j.val then {j.val - 1} else ∅)
  have hA : (C.image (fun i => keyAt5 (X.p.J n) i t j.val)).image
      (signShiftKey5 X t) =
      C.image (fun i => keyAt5 (X.p.J n) i default j.val) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i hi
    have h := signShiftKey5_keyAt5 X t i t j.val
    simpa [t, shiftSignVector_self5] using h
  have hB : (F.image (fun h => keyAt5 (X.p.J n) (X.g.key x)
      (Function.update t h (!t h)) j.val)).image (signShiftKey5 X t) =
      F.image (fun h => keyAt5 (X.p.J n) (X.g.key x)
        (Function.update (default : CubeVertex (X.p.m n)) h true) j.val) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro h hh
    have hEq := signShiftKey5_keyAt5 X t (X.g.key x)
      (Function.update t h (!t h)) j.val
    simpa [t, shiftSignVector_update5] using hEq
  have hD : (D.image (fun k => keyAt5 (X.p.J n) (X.g.key x) t k)).image
      (signShiftKey5 X t) =
      D.image (fun k => keyAt5 (X.p.J n) (X.g.key x) default k) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro k hk
    have h := signShiftKey5_keyAt5 X t (X.g.key x) t k
    simpa [t, shiftSignVector_self5] using h
  have htypeKeysEq : X.g.typeKeys (X.p.J n) x =
      (C.image (fun i => keyAt5 (X.p.J n) i t j.val) ∪
        F.image (fun h => keyAt5 (X.p.J n) (X.g.key x)
          (Function.update t h (!t h)) j.val)) ∪
        D.image (fun k => keyAt5 (X.p.J n) (X.g.key x) t k) := by
    unfold ChunkGeometry5.typeKeys
    rw [if_pos hlow]
    rw [hj]
  have hS : (X.g.typeKeys (X.p.J n) x).image (signShiftKey5 X t) =
      C.image (fun i => keyAt5 (X.p.J n) i default j.val) ∪
        F.image (fun h => keyAt5 (X.p.J n) (X.g.key x)
          (Function.update (default : CubeVertex (X.p.m n)) h true) j.val) ∪
        D.image (fun k => keyAt5 (X.p.J n) (X.g.key x) default k) := by
    rw [htypeKeysEq, Finset.image_union, Finset.image_union, hA, hB, hD]
  have hkeyEq : signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x) =
      lowTypeFromData5 X (X.g.key x) default j C F := by
    dsimp [signShiftType5, ChunkGeometry5.evenType, lowTypeFromData5]
    rw [dif_pos hlow]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact hS
      · exact congrArg some (Fin.ext hj)
  refine Finset.mem_image.mpr ⟨(X.g.coarseRange x, X.g.flippable x), ?_, hkeyEq.symm⟩
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_powerset.mpr (X.g.coarseRange_subset_nearKeys5 x)
  · rw [mem_smallSubsets5]
    simpa [hj] using flippable_card_le_severity5 X x

def highTypeFromData5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (C : Finset (CoarseKey5 n)) : X.Ty :=
  (q, C.image (fun i => (Sum.inr i : X.Key)), none)

def highTypeCandidates5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) : Finset X.Ty :=
  (nearCoarseKeys5 q.1).powerset.image (highTypeFromData5 X q)

theorem coarseKey_mem_nearKeys5 {n : ℕ} (q : CoarseKey5 n) :
    q ∈ nearCoarseKeys5 q.1 := by
  apply Finset.mem_product.mpr
  exact ⟨binVector_self_mem_near5 q.1, Finset.mem_univ q.2⟩

theorem keyAt5_coarse {n m J : ℕ} (q : CoarseKey5 n) (t : CubeVertex m) (k : ℕ) :
    (keyAt5 J q t k).coarse = q := by
  by_cases hk : k ≤ J <;> simp [keyAt5, hk, HiddenKey5.coarse]

theorem binNeighborVal5_dist_le {n : ℕ} (w : Fin (n + 1)) (d : Fin 3) :
    Nat.dist w.val (binNeighborVal5 w d).val ≤ 1 := by
  by_cases h0 : d.val = 0
  · simp [binNeighborVal5, h0]
    rw [Nat.dist_eq_sub_of_le_right (Nat.sub_le _ _)]
    omega
  · by_cases h1 : d.val = 1
    · simp [binNeighborVal5, h0, h1]
    · have h2 : d.val = 2 := by omega
      have hw : w.val ≤ n := by omega
      by_cases htop : w.val = n
      · simp [binNeighborVal5, h0, h1, h2, htop]
      · have hplus : w.val + 1 ≤ n := by omega
        have hmin : min n (w.val + 1) = w.val + 1 := Nat.min_eq_right hplus
        simp [binNeighborVal5, h0, h1, h2, hmin]
        rw [Nat.dist_eq_sub_of_le (by omega)]
        omega

theorem binAdjacent_mem_nearBinVectors5 {n : ℕ} (w z : BinVector5 n)
    (h : binAdjacent5 w z) : z ∈ nearBinVectors5 w := by
  apply mem_nearBinVectors5_of_coords
  intro i
  have hd : Nat.dist (w i).val (z i).val ≤ 1 := h.2 i
  have hb : (w i).val ≤ (z i).val + 1 ∧ (z i).val ≤ (w i).val + 1 := by
    rcases Nat.le_total (w i).val (z i).val with hle | hge
    · rw [Nat.dist_eq_sub_of_le hle] at hd
      omega
    · rw [Nat.dist_eq_sub_of_le_right hge] at hd
      omega
  obtain ⟨d, hEq⟩ := exists_binNeighborVal5 (w i) (z i) hb.1 hb.2
  unfold binNeighborVals5
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hEq.symm⟩

theorem binList_mem_nearBinVectors5 {n : ℕ} (q : CoarseKey5 n) (w : BinVector5 n)
    (hw : w ∈ binList5 q) : w ∈ nearBinVectors5 q.1 := by
  by_cases hb : q.2
  · simp only [binList5, if_pos hb, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with rfl | hadj
    · exact binVector_self_mem_near5 q.1
    · exact binAdjacent_mem_nearBinVectors5 q.1 w hadj
  · simp [binList5, hb] at hw
    subst w
    exact binVector_self_mem_near5 q.1

theorem nearBinVectors_coord_dist5 {n : ℕ} (w z : BinVector5 n)
    (hz : z ∈ nearBinVectors5 w) :
    ∀ i, Nat.dist (w i).val (z i).val ≤ 1 := by
  classical
  unfold nearBinVectors5 at hz
  obtain ⟨f, hf, hEq⟩ := Finset.mem_image.mp hz
  intro i
  have hpi : f i (Finset.mem_univ i) ∈ binNeighborVals5 w i :=
    (Finset.mem_pi.mp hf) i (Finset.mem_univ i)
  obtain ⟨d, hd, hval⟩ := Finset.mem_image.mp hpi
  have hval' : binNeighborVal5 (w i) d = z i := by
    calc
      binNeighborVal5 (w i) d = f i (Finset.mem_univ i) := hval
      _ = z i := congrFun hEq i
  rw [← hval']
  exact binNeighborVal5_dist_le (w i) d

theorem nearBinVectors_mem_symm5 {n : ℕ} (w z : BinVector5 n)
    (hz : z ∈ nearBinVectors5 w) : w ∈ nearBinVectors5 z := by
  apply mem_nearBinVectors5_of_coords
  intro i
  have hd := nearBinVectors_coord_dist5 w z hz i
  have hb : (z i).val ≤ (w i).val + 1 ∧ (w i).val ≤ (z i).val + 1 := by
    rcases Nat.le_total (w i).val (z i).val with hle | hge
    · rw [Nat.dist_eq_sub_of_le hle] at hd
      omega
    · rw [Nat.dist_eq_sub_of_le_right hge] at hd
      omega
  obtain ⟨d, hEq⟩ := exists_binNeighborVal5 (z i) (w i) hb.1 hb.2
  unfold binNeighborVals5
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, hEq.symm⟩

def nearBinVectors2_5 {n : ℕ} (w : BinVector5 n) : Finset (BinVector5 n) :=
  (nearBinVectors5 w).biUnion nearBinVectors5

def nearCoarseKeys2_5 {n : ℕ} (w : BinVector5 n) : Finset (CoarseKey5 n) :=
  (nearBinVectors2_5 w).product (Finset.univ : Finset Bool)

theorem nearBinVectors2_card_le5 {n : ℕ} (w : BinVector5 n) :
    (nearBinVectors2_5 w).card ≤ (3 ^ coarseChunkCount5) ^ 2 := by
  classical
  calc
    (nearBinVectors2_5 w).card ≤
        ∑ z ∈ nearBinVectors5 w, (nearBinVectors5 z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ nearBinVectors5 w, 3 ^ coarseChunkCount5 := by
      apply Finset.sum_le_sum
      intro z hz
      exact nearBinVectors5_card_le z
    _ = (nearBinVectors5 w).card * 3 ^ coarseChunkCount5 := by simp
    _ ≤ 3 ^ coarseChunkCount5 * 3 ^ coarseChunkCount5 :=
      Nat.mul_le_mul_right _ (nearBinVectors5_card_le w)
    _ = (3 ^ coarseChunkCount5) ^ 2 := by ring

theorem nearCoarseKeys2_card_le5 {n : ℕ} (w : BinVector5 n) :
    (nearCoarseKeys2_5 w).card ≤ 2 * (3 ^ coarseChunkCount5) ^ 2 := by
  classical
  calc
    (nearCoarseKeys2_5 w).card =
        (nearBinVectors2_5 w).card * (Finset.univ : Finset Bool).card :=
      Finset.card_product _ _
    _ ≤ (3 ^ coarseChunkCount5) ^ 2 * 2 :=
      Nat.mul_le_mul_right _ (nearBinVectors2_card_le5 w)
    _ = 2 * (3 ^ coarseChunkCount5) ^ 2 := by omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem nearBinVectors2_mem_symm5 {n : ℕ} (w z : BinVector5 n)
    (hz : z ∈ nearBinVectors2_5 w) : w ∈ nearBinVectors2_5 z := by
  obtain ⟨u, huw, hzu⟩ := Finset.mem_biUnion.mp hz
  change w ∈ (nearBinVectors5 z).biUnion nearBinVectors5
  apply Finset.mem_biUnion.mpr
  refine ⟨u, ?_, ?_⟩
  · exact nearBinVectors_mem_symm5 u z hzu
  · exact nearBinVectors_mem_symm5 u w huw

theorem nearBinVectors2_self5 {n : ℕ} (w : BinVector5 n) : w ∈ nearBinVectors2_5 w := by
  apply Finset.mem_biUnion.mpr
  exact ⟨w, binVector_self_mem_near5 w, binVector_self_mem_near5 w⟩

theorem lowTypeCandidates_keys_coarse5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1))
    (K : X.Ty) (hK : K ∈ lowTypeCandidates5 X q t j) :
    ∀ ℓ ∈ K.2.1, ℓ.coarse ∈ nearCoarseKeys5 q.1 := by
  classical
  obtain ⟨d, hd, hEq⟩ := Finset.mem_image.mp hK
  rcases Finset.mem_product.mp hd with ⟨hC, hF⟩
  have hCsubset : d.1 ⊆ nearCoarseKeys5 q.1 := Finset.mem_powerset.mp hC
  intro ℓ hℓ
  rw [← hEq] at hℓ
  dsimp [lowTypeFromData5] at hℓ
  rcases Finset.mem_union.mp hℓ with hAB | hD
  · rcases Finset.mem_union.mp hAB with hA | hB
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      simpa [keyAt5_coarse] using hCsubset hi
    · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hB
      rw [keyAt5_coarse]
      exact coarseKey_mem_nearKeys5 q
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hD
    rw [keyAt5_coarse]
    exact coarseKey_mem_nearKeys5 q

theorem highTypeCandidates_keys_coarse5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hK : K ∈ highTypeCandidates5 X q) :
    ∀ ℓ ∈ K.2.1, ℓ.coarse ∈ nearCoarseKeys5 q.1 := by
  classical
  obtain ⟨C, hC, hEq⟩ := Finset.mem_image.mp hK
  have hCsubset : C ⊆ nearCoarseKeys5 q.1 := Finset.mem_powerset.mp hC
  intro ℓ hℓ
  rw [← hEq] at hℓ
  dsimp [highTypeFromData5] at hℓ
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hℓ
  exact hCsubset hi

theorem highTypeCandidates_card5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n)
    (D : ℕ) (hD : (nearCoarseKeys5 q.1).card ≤ D) :
    (highTypeCandidates5 X q).card ≤ 2 ^ D := by
  classical
  calc
    (highTypeCandidates5 X q).card ≤ (nearCoarseKeys5 q.1).powerset.card :=
      Finset.card_image_le
    _ = 2 ^ (nearCoarseKeys5 q.1).card := Finset.card_powerset _
    _ ≤ 2 ^ D := Nat.pow_le_pow_right (by omega : 0 < 2) hD

theorem highEvenType_mem_candidates5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (hhigh : ¬ X.g.severity x ≤ X.p.J n) :
    X.g.evenType (X.p.J n) x ∈ highTypeCandidates5 X (X.g.key x) := by
  classical
  have hType : X.g.typeKeys (X.p.J n) x =
      (X.g.coarseRange x).image (fun i => (Sum.inr i : X.Key)) := by
    unfold ChunkGeometry5.typeKeys
    rw [if_neg hhigh]
  have hC : X.g.coarseRange x ⊆ nearCoarseKeys5 (X.g.key x).1 :=
    X.g.coarseRange_subset_nearKeys5 x
  have hmem : X.g.coarseRange x ∈ (nearCoarseKeys5 (X.g.key x).1).powerset :=
    Finset.mem_powerset.mpr hC
  apply Finset.mem_image.mpr
  refine ⟨X.g.coarseRange x, hmem, ?_⟩
  dsimp [highTypeCandidates5, highTypeFromData5, ChunkGeometry5.evenType]
  rw [dif_neg hhigh, hType]

abbrev Stage2LowPattern5 (X : Setup5 γ K' χ n N E G) :=
  Σ q : CoarseKey5 n, Σ j : Fin (X.p.J n + 1),
    {K : X.Ty // K ∈ lowTypeCandidates5 X q default j ∧
      K.1 = q ∧ K.2.2 = some j ∧
      ∃ x : CubeVertex n, IsEvenRole x ∧
        K = signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x)}

noncomputable instance stage2LowPatternFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2LowPattern5 X) := by
  classical
  infer_instance

abbrev Stage2HighPattern5 (X : Setup5 γ K' χ n N E G) :=
  Σ q : CoarseKey5 n,
    {K : X.Ty // K ∈ highTypeCandidates5 X q ∧
      K.1 = q ∧ K.2.2 = none ∧
      ∃ x : CubeVertex n, IsEvenRole x ∧ K = X.g.evenType (X.p.J n) x}

noncomputable instance stage2HighPatternFintype5 (X : Setup5 γ K' χ n N E G) :
    Fintype (Stage2HighPattern5 X) := by
  classical
  infer_instance

abbrev Stage2LowPatternAt5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :=
  {K : X.Ty // K ∈ lowTypeCandidates5 X q default j ∧ K.1 = q ∧ K.2.2 = some j ∧
    ∃ x : CubeVertex n, IsEvenRole x ∧
      K = signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x)}

noncomputable instance stage2LowPatternAtFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :
    Fintype (Stage2LowPatternAt5 X q j) := by
  classical
  infer_instance

abbrev Stage2HighPatternAt5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {K : X.Ty // K ∈ highTypeCandidates5 X q ∧ K.1 = q ∧ K.2.2 = none ∧
    ∃ x : CubeVertex n, IsEvenRole x ∧ K = X.g.evenType (X.p.J n) x}

noncomputable instance stage2HighPatternAtFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighPatternAt5 X q) := by
  classical
  infer_instance

theorem stage2LowPatternAt_gateKeys_coarse5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j) :
    ∀ ℓ ∈ X.gateKeys p.1, ℓ.coarse ∈ nearCoarseKeys5 q.1 := by
  have hgate : X.gateKeys p.1 = p.1.2.1 := by
    simp [Setup5.gateKeys, p.2.2.2.1]
  rw [hgate]
  exact lowTypeCandidates_keys_coarse5 X q default j p.1 p.2.1

theorem stage2HighPatternAt_gateKeys_coarse5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (p : Stage2HighPatternAt5 X q) :
    ∀ ℓ ∈ X.gateKeys p.1, ℓ.coarse ∈ nearCoarseKeys5 q.1 := by
  have hkeys := highTypeCandidates_keys_coarse5 X q p.1 p.2.1
  have hlevel : p.1.2.2 = none := p.2.2.2.1
  intro ℓ hℓ
  simp only [Setup5.gateKeys, hlevel, if_pos, Finset.mem_union, Finset.mem_singleton] at hℓ
  rcases hℓ with hmem | heq
  · exact hkeys ℓ hmem
  · subst ℓ
    simpa [Setup5.optKeyOf, p.2.2.1] using coarseKey_mem_nearKeys5 q

def lowKeysBase5 : ℕ := coarseChunkCount5 * 4 + 3
def stage2TypeCountBase5 : ℕ := 2 ^ (2 * 3 ^ coarseChunkCount5)

theorem Params5.tendsto_m_atTop_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ) :
    Tendsto (fun n : ℕ => (p.m n : ℝ)) atTop atTop := by
  have hmle (n : ℕ) : (n : ℝ) ^ p.alpha ≤ (p.m n : ℝ) := by
    dsimp [Params5.m]
    exact Nat.le_ceil _
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
    (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono hmle hpow

theorem Params5.J_le_m_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ) (n : ℕ)
    (hm : 1 ≤ p.m n) : p.J n ≤ p.m n := by
  have hmreal : 1 ≤ (p.m n : ℝ) := by exact_mod_cast hm
  have hrpow : (p.m n : ℝ) ^ (1 / 20 : ℝ) ≤ (p.m n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmreal (by norm_num)
  have hfloor : (Nat.floor ((p.m n : ℝ) ^ (1 / 20 : ℝ)) : ℝ) ≤
      (p.m n : ℝ) ^ (1 / 20 : ℝ) := Nat.floor_le (by positivity)
  have hcast : (p.J n : ℝ) ≤ (p.m n : ℝ) := by
    simpa [Params5.J] using hfloor.trans hrpow
  exact_mod_cast hcast

theorem Params5.q0_uSeg_lower_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) :
    p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) ≤
      (p.q0 : ℝ) * (p.uSeg n j : ℝ) := by
  have hq : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
  have hceil :
      p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤
        (p.uSeg n j : ℝ) := by
    dsimp [Params5.uSeg]
    exact Nat.le_ceil _
  calc
    p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) =
        (p.q0 : ℝ) *
          (p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by
            field_simp [ne_of_gt hq]
    _ ≤ (p.q0 : ℝ) * (p.uSeg n j : ℝ) :=
      mul_le_mul_of_nonneg_left hceil hq.le

theorem Params5.q0_uStarSeg_lower_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n : ℕ) :
    p.eta * Real.log (p.m n : ℝ) ≤ (p.q0 : ℝ) * (p.uStarSeg n : ℝ) := by
  have hq : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
  have hceil : p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ) ≤
      (p.uStarSeg n : ℝ) := by
    dsimp [Params5.uStarSeg]
    exact Nat.le_ceil _
  calc
    p.eta * Real.log (p.m n : ℝ) =
        (p.q0 : ℝ) * (p.eta * Real.log (p.m n : ℝ) / (p.q0 : ℝ)) := by
          field_simp [ne_of_gt hq]
    _ ≤ (p.q0 : ℝ) * (p.uStarSeg n : ℝ) :=
      mul_le_mul_of_nonneg_left hceil hq.le

theorem Params5.capBudget_le_mpow_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n k : ℕ) (hm : 1 ≤ p.m n) (hK1 : 8 / p.delta ≤ p.K1) :
    Real.exp (-(p.delta * (p.q0 * p.uSeg n (k + 1))) / 2) ≤
      Real.exp (-20 * Real.log (p.m n : ℝ)) := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have ht : 0 ≤ ((k : ℝ) + 5) * Real.log (p.m n : ℝ) :=
    mul_nonneg (by positivity) hlog
  have hseg := p.q0_uSeg_lower_h23 n (k + 1)
  have hk : 8 ≤ p.delta * p.K1 := (div_le_iff₀ p.hdelta.1).mp hK1
  have hcoef : 4 ≤ p.delta * p.K1 / 2 := by nlinarith [hk]
  have hlow : 20 * Real.log (p.m n : ℝ) ≤
      (p.delta * p.K1 / 2) * (((k : ℝ) + 5) * Real.log (p.m n : ℝ)) := by
    have hj : (5 : ℝ) ≤ (k : ℝ) + 5 := by exact_mod_cast Nat.le_add_left 5 k
    nlinarith [mul_le_mul_of_nonneg_right hj hlog]
  have hscale :
      (p.delta * p.K1 / 2) * (((k : ℝ) + 5) * Real.log (p.m n : ℝ)) ≤
        p.delta * ((p.q0 : ℝ) * p.uSeg n (k + 1) : ℝ) / 2 := by
    have hs := mul_le_mul_of_nonneg_left hseg (div_nonneg p.hdelta.1.le (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith [hs]
  apply Real.exp_le_exp.mpr
  nlinarith [hlow.trans hscale]

theorem Params5.lowAlarmExp_le5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) (hK1 : 8 / p.delta ≤ p.K1) :
    Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 4) ≤
      Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by
  have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have ht : 0 ≤ ((j : ℝ) + 4) * Real.log (p.m n : ℝ) := mul_nonneg (by positivity) hlog
  have hseg := p.q0_uSeg_lower_h23 n j
  have hk : 8 ≤ p.delta * p.K1 := by
    have h := (div_le_iff₀ p.hdelta.1).mp hK1
    nlinarith [h]
  have hcoef : 2 ≤ p.delta * p.K1 / 4 := by nlinarith [hk]
  have hscaled :
      (p.delta / 4) * (p.K1 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ))) ≤
        (p.delta / 4) * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) :=
    mul_le_mul_of_nonneg_left hseg (by positivity)
  have hrate : 2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
      p.delta * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) / 4 := by
    calc
      2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
          (p.delta * p.K1 / 4) * (((j : ℝ) + 4) * Real.log (p.m n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef ht
      _ = (p.delta / 4) *
            (p.K1 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ))) := by ring
      _ ≤ (p.delta / 4) * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) := hscaled
      _ = p.delta * ((p.q0 : ℝ) * (p.uSeg n j : ℝ)) / 4 := by ring
  exact Real.exp_le_exp.mpr (by nlinarith [hrate])

theorem Params5.lowAlarmExpStep1_le5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) (hK1 : 8 / p.delta ≤ p.K1) :
    Real.exp (-(p.delta * (p.q0 * p.uSeg n j)) / 2) ≤
      Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by
  refine le_trans ?_ (p.lowAlarmExp_le5 n j hm hK1)
  apply Real.exp_le_exp.mpr
  have hpos : 0 ≤ p.delta * (p.q0 * p.uSeg n j : ℝ) := by positivity
  nlinarith [hpos]

theorem Params5.highAlarmExp_le5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n : ℕ) :
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) ≤
      Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ)) := by
  have hseg := p.q0_uStarSeg_lower_h23 n
  have hscaled := mul_le_mul_of_nonneg_left hseg
    (div_nonneg p.hdelta.1.le (by norm_num : (0 : ℝ) ≤ 4))
  apply Real.exp_le_exp.mpr
  nlinarith [hscaled]

theorem natPow_mul_exp_decay5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ j : ℝ) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
      Real.exp (-8 * Real.log (p.m n : ℝ)) := by
  have hmpos : 0 < (p.m n : ℝ) := by exact_mod_cast (by omega : 0 < p.m n)
  have hpow : ((p.m n) ^ j : ℝ) =
      Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) := by
    calc
      ((p.m n) ^ j : ℝ) = (p.m n : ℝ) ^ j := by norm_cast
      _ = (p.m n : ℝ) ^ (j : ℝ) := by rw [← Real.rpow_natCast]
      _ = Real.exp (Real.log (p.m n : ℝ) * (j : ℝ)) :=
        Real.rpow_def_of_pos hmpos _
      _ = Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) := by congr 1; ring
  calc
    ((p.m n) ^ j : ℝ) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) =
      Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by rw [hpow]
    _ = Real.exp (-((j : ℝ) + 8) * Real.log (p.m n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-8 * Real.log (p.m n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
      nlinarith [hlog]

theorem Params5.natPow_eq_exp_log_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n k : ℕ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ k : ℝ) = Real.exp ((k : ℝ) * Real.log (p.m n : ℝ)) := by
  have hmpos : 0 < (p.m n : ℝ) := by exact_mod_cast (by omega : 0 < p.m n)
  calc
    ((p.m n) ^ k : ℝ) = (p.m n : ℝ) ^ k := by norm_cast
    _ = (p.m n : ℝ) ^ (k : ℝ) := by rw [← Real.rpow_natCast]
    _ = Real.exp (Real.log (p.m n : ℝ) * (k : ℝ)) :=
      Real.rpow_def_of_pos hmpos _
    _ = Real.exp ((k : ℝ) * Real.log (p.m n : ℝ)) := by congr 1; ring

theorem Params5.natPow_exp_cancel_h23 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n k : ℕ) (a : ℝ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ k : ℝ) * Real.exp (-a * Real.log (p.m n : ℝ)) =
      Real.exp (((k : ℝ) - a) * Real.log (p.m n : ℝ)) := by
  rw [p.natPow_eq_exp_log_h23 n k hm, ← Real.exp_add]
  congr 1
  ring

theorem stage2LowPatternAt_keys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j) :
    p.1.2.1.card ≤ lowKeysBase5 + j.val := by
  rcases p.2.2.2.2 with ⟨x, hx, hK⟩
  let K0 := X.g.evenType (X.p.J n) x
  have hlevel0 : K0.2.2 = some j := by
    have h := p.2.2.2.1
    rw [hK, signShiftType5_level] at h
    exact h
  have hlow : X.g.severity x ≤ X.p.J n := by
    by_contra hnot
    have hnone : K0.2.2 = none := by
      simp [K0, ChunkGeometry5.evenType, hnot]
    rw [hnone] at hlevel0
    cases hlevel0
  have hfin : (⟨X.g.severity x, Nat.lt_succ_of_le hlow⟩ : Fin (X.p.J n + 1)) = j := by
    have hsome : some (⟨X.g.severity x, Nat.lt_succ_of_le hlow⟩ : Fin (X.p.J n + 1)) = some j := by
      simpa [K0, ChunkGeometry5.evenType, hlow] using hlevel0
    exact Option.some.inj hsome
  have hseverity : X.g.severity x = j.val := congrArg Fin.val hfin
  have hcard := typeKeys_card_le_severity5 X x
  calc
    p.1.2.1.card = (X.g.typeKeys (X.p.J n) x).card := by
      rw [hK, signShiftType5_keys_card]
      simp [K0, ChunkGeometry5.evenType]
    _ ≤ coarseChunkCount5 * 4 + 1 + X.g.severity x + 2 := hcard
    _ = lowKeysBase5 + j.val := by rw [hseverity, lowKeysBase5]; omega

theorem stage2LowPatternAt_gateKeys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j) :
    (X.gateKeys p.1).card ≤ lowKeysBase5 + j.val := by
  have hgate : X.gateKeys p.1 = p.1.2.1 := by
    simp [Setup5.gateKeys, p.2.2.2.1]
  rw [hgate]
  exact stage2LowPatternAt_keys_card_le5 X q j p

theorem highTypeCandidates_keys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hK : K ∈ highTypeCandidates5 X q) :
    K.2.1.card ≤ (nearCoarseKeys5 q.1).card := by
  classical
  obtain ⟨C, hC, hEq⟩ := Finset.mem_image.mp hK
  rw [← hEq]
  dsimp [highTypeFromData5]
  calc
    (C.image fun i => (Sum.inr i : X.Key)).card ≤ C.card := Finset.card_image_le
    _ ≤ (nearCoarseKeys5 q.1).card := Finset.card_le_card (Finset.mem_powerset.mp hC)

theorem stage2HighPatternAt_gateKeys_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (p : Stage2HighPatternAt5 X q) (D : ℕ)
    (hD : (nearCoarseKeys5 q.1).card ≤ D) :
    (X.gateKeys p.1).card ≤ D + 1 := by
  have hkeys : p.1.2.1.card ≤ D :=
    (highTypeCandidates_keys_card_le5 X q p.1 p.2.1).trans hD
  have hlevel : p.1.2.2 = none := p.2.2.2.1
  have hgate : X.gateKeys p.1 = p.1.2.1 ∪ {X.optKeyOf p.1 default} := by
    simp [Setup5.gateKeys, hlevel]
  rw [hgate]
  calc
    (p.1.2.1 ∪ {X.optKeyOf p.1 default}).card ≤ p.1.2.1.card + 1 := by
      exact (Finset.card_union_le _ _).trans (by simp)
    _ ≤ D + 1 := Nat.add_le_add_right hkeys 1

abbrev Stage2LowStep1Data5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :=
  Σ p : Stage2LowPatternAt5 X q j, {ℓ : X.Key // ℓ ∈ X.gateKeys p.1}

noncomputable instance stage2LowStep1DataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) : Fintype (Stage2LowStep1Data5 X q j) := by
  classical
  infer_instance

theorem stage2LowStep1Data_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :
    Fintype.card (Stage2LowStep1Data5 X q j) ≤
      (lowTypeCandidates5 X q default j).card * (lowKeysBase5 + j.val) := by
  classical
  calc
    Fintype.card (Stage2LowStep1Data5 X q j) =
        ∑ p : Stage2LowPatternAt5 X q j,
          Fintype.card {ℓ : X.Key // ℓ ∈ X.gateKeys p.1} := Fintype.card_sigma
    _ ≤ ∑ _p : Stage2LowPatternAt5 X q j, lowKeysBase5 + j.val := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Fintype.card_coe]
      exact stage2LowPatternAt_gateKeys_card_le5 X q j p
    _ = Fintype.card (Stage2LowPatternAt5 X q j) * (lowKeysBase5 + j.val) := by simp
    _ ≤ (lowTypeCandidates5 X q default j).card * (lowKeysBase5 + j.val) := by
      exact Nat.mul_le_mul_right _ (stage2LowPatternAt_card_le5 X q j)

abbrev Stage2HighStep1Data5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  Σ p : Stage2HighPatternAt5 X q, {ℓ : X.Key // ℓ ∈ X.gateKeys p.1}

noncomputable instance stage2HighStep1DataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighStep1Data5 X q) := by
  classical
  infer_instance

theorem stage2HighStep1Data_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (D : ℕ) (hD : (nearCoarseKeys5 q.1).card ≤ D) :
    Fintype.card (Stage2HighStep1Data5 X q) ≤ 2 ^ D * (D + 1) := by
  classical
  calc
    Fintype.card (Stage2HighStep1Data5 X q) =
        ∑ p : Stage2HighPatternAt5 X q,
          Fintype.card {ℓ : X.Key // ℓ ∈ X.gateKeys p.1} := Fintype.card_sigma
    _ ≤ ∑ _p : Stage2HighPatternAt5 X q, D + 1 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Fintype.card_coe]
      exact stage2HighPatternAt_gateKeys_card_le5 X q p D hD
    _ = Fintype.card (Stage2HighPatternAt5 X q) * (D + 1) := by simp
    _ ≤ (highTypeCandidates5 X q).card * (D + 1) :=
      Nat.mul_le_mul_right _ (stage2HighPatternAt_card_le5 X q)
    _ ≤ 2 ^ D * (D + 1) := Nat.mul_le_mul_right _ (highTypeCandidates_card5 X q D hD)

def stage2LowCapOccurs5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) : Prop :=
  ∃ ℓ : X.Key, X.KeyOccurs ℓ ∧
    ∃ t : CubeVertex (X.p.m n),
      signShiftKey5 X t ℓ = .inl (q, default, j)

noncomputable instance stage2LowCapOccursDecidable5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) : Decidable (stage2LowCapOccurs5 X q j) :=
  Classical.propDecidable _

abbrev Stage2LowCapData5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {j : Fin (X.p.J n + 1) // stage2LowCapOccurs5 X q j}

noncomputable instance stage2LowCapDataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2LowCapData5 X q) := by
  classical
  infer_instance

theorem stage2LowCapData_card_le5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    Fintype.card (Stage2LowCapData5 X q) ≤ X.p.J n + 1 := by
  classical
  calc
    Fintype.card (Stage2LowCapData5 X q) ≤ Fintype.card (Fin (X.p.J n + 1)) :=
      Fintype.card_le_of_injective (fun j : Stage2LowCapData5 X q => j.1) (by
        intro a b h
        exact Subtype.ext h)
    _ = X.p.J n + 1 := Fintype.card_fin _

abbrev Stage2HighOptPatternAt5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {p : Stage2HighPatternAt5 X q // ∃ t, X.OptOccurs p.1 t}

noncomputable instance stage2HighOptPatternAtFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighOptPatternAt5 X q) := by
  classical
  infer_instance

theorem stage2HighOptPatternAt_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    Fintype.card (Stage2HighOptPatternAt5 X q) ≤ (highTypeCandidates5 X q).card := by
  classical
  apply le_trans (Fintype.card_le_of_injective
    (fun p : Stage2HighOptPatternAt5 X q => p.1) (by
      intro a b h
      exact Subtype.ext h))
  exact stage2HighPatternAt_card_le5 X q

abbrev Stage2HighCapData5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  {u : Unit // X.KeyOccurs (.inr q)}

noncomputable instance stage2HighCapDataFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2HighCapData5 X q) := by
  classical
  infer_instance

theorem stage2HighCapData_card_le5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    Fintype.card (Stage2HighCapData5 X q) ≤ 1 := by
  classical
  calc
    Fintype.card (Stage2HighCapData5 X q) ≤ Fintype.card Unit :=
      Fintype.card_le_of_injective (fun u : Stage2HighCapData5 X q => u.1) (by
        intro a b h
        exact Subtype.ext h)
    _ = 1 := Fintype.card_unit

inductive Stage2GroupAlarm5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) where
  | lowStep1 (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j)
      (ℓ : {ℓ : X.Key // ℓ ∈ X.gateKeys p.1})
  | highStep1 (p : Stage2HighPatternAt5 X q)
      (ℓ : {ℓ : X.Key // ℓ ∈ X.gateKeys p.1})
  | lowCap (j : Fin (X.p.J n + 1)) (h : stage2LowCapOccurs5 X q j)
  | highCap (h : X.KeyOccurs (.inr q))
  | lowStep2 (j : Fin (X.p.J n + 1)) (p : Stage2LowPatternAt5 X q j)
  | highStep2 (p : Stage2HighPatternAt5 X q)
  | highOptional (p : Stage2HighOptPatternAt5 X q)

noncomputable instance stage2GroupAlarmFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2GroupAlarm5 X q) := by
  classical
  infer_instance

abbrev Stage2LowStep2Data5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  Σ j : Fin (X.p.J n + 1), Stage2LowPatternAt5 X q j

abbrev Stage2GroupAlarmFlat5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :=
  (Σ j : Fin (X.p.J n + 1), Stage2LowStep1Data5 X q j) ⊕
    (Stage2HighStep1Data5 X q ⊕
      (Stage2LowCapData5 X q ⊕
        (Stage2HighCapData5 X q ⊕
          (Stage2LowStep2Data5 X q ⊕
            (Stage2HighPatternAt5 X q ⊕ Stage2HighOptPatternAt5 X q))))

noncomputable instance stage2GroupAlarmFlatFintype5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Fintype (Stage2GroupAlarmFlat5 X q) := by
  classical
  infer_instance

noncomputable def stage2GroupAlarmEquiv5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) : Stage2GroupAlarm5 X q ≃ Stage2GroupAlarmFlat5 X q where
  toFun := fun i => match i with
    | .lowStep1 j p ℓ => Sum.inl ⟨j, ⟨p, ℓ⟩⟩
    | .highStep1 p ℓ => Sum.inr (Sum.inl ⟨p, ℓ⟩)
    | .lowCap j h => Sum.inr (Sum.inr (Sum.inl ⟨j, h⟩))
    | .highCap h => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨(), h⟩)))
    | .lowStep2 j p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩))))
    | .highStep2 p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))
    | .highOptional p => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p)))))
  invFun := fun a => match a with
    | Sum.inl ⟨j, ⟨p, ℓ⟩⟩ => .lowStep1 j p ℓ
    | Sum.inr (Sum.inl ⟨p, ℓ⟩) => .highStep1 p ℓ
    | Sum.inr (Sum.inr (Sum.inl ⟨j, h⟩)) => .lowCap j h
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨u, h⟩))) => .highCap h
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))) => .lowStep2 j p
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) => .highStep2 p
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) => .highOptional p
  left_inv := by intro i; cases i <;> rfl
  right_inv := by
    intro a
    cases a with
    | inl a => cases a with | mk j d => cases d with | mk p ℓ => rfl
    | inr r =>
      cases r with
      | inl d => cases d with | mk p ℓ => rfl
      | inr r =>
        cases r with
        | inl d => cases d with | mk j h => rfl
        | inr r =>
          cases r with
          | inl d => cases d with | mk u h => rfl
          | inr r =>
          cases r with
          | inl d => cases d with | mk j p => rfl
          | inr r =>
            cases r with
            | inl p => rfl
            | inr p => rfl

noncomputable def stage2GroupAlarmBad5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) (c : X.Coarse) : Prop :=
  match i with
  | .lowStep1 _ p ℓ =>
      X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
  | .highStep1 p ℓ =>
      X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
  | .lowCap j _ => X.capFail (v, c) (.inl (q, default, j))
  | .highCap _ => X.capFail (v, c) (.inr q)
  | .lowStep2 _ p =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)
  | .highStep2 p =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)
  | .highOptional p =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U =>
          X.optFail ((v, c), U) p.1.1 (default : CubeVertex (X.p.m n)))

noncomputable def stage2GroupAlarmScope5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) : Finset (BinVector5 n) :=
  match i with
  | .lowStep1 _ _ ℓ => binList5 ℓ.1.coarse
  | .highStep1 _ ℓ => binList5 ℓ.1.coarse
  | .lowCap _ _ => binList5 q
  | .highCap _ => binList5 q
  | .lowStep2 _ p => blockLocalBins5 X p.1 p.1.2.1
  | .highStep2 p => blockLocalBins5 X p.1 p.1.2.1
  | .highOptional p =>
      blockLocalBins5 X p.1.1 (insert (X.optKeyOf p.1.1 default) p.1.1.2.1)

noncomputable def stage2GroupAlarmBudget5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) : ℝ :=
  match i with
  | .lowStep1 _ p _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | .highStep1 p _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | .lowCap j _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (j.val + 1))) / 2)
  | .highCap _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (X.p.J n + 1))) / 2)
  | .lowStep2 _ p =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | .highStep2 p =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | .highOptional _ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)

noncomputable def stage2GroupAlarmFlatBudget5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (a : Stage2GroupAlarmFlat5 X q) : ℝ :=
  match a with
  | Sum.inl ⟨j, ⟨p, ℓ⟩⟩ =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | Sum.inr (Sum.inl ⟨p, ℓ⟩) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2)
  | Sum.inr (Sum.inr (Sum.inl ⟨j, h⟩)) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (j.val + 1))) / 2)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨u, h⟩))) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (X.p.J n + 1))) / 2)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))) =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) =>
      ((p.1.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) =>
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)

theorem stage2GroupAlarmBudget_sum_eq_flat5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    (∑ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBudget5 X q i) =
      ∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a := by
  calc
    (∑ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBudget5 X q i) =
        ∑ i : Stage2GroupAlarm5 X q,
          stage2GroupAlarmFlatBudget5 X q (stage2GroupAlarmEquiv5 X q i) := by
            apply Finset.sum_congr rfl
            intro i hi
            cases i <;> rfl
    _ = ∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a :=
      Equiv.sum_comp (stage2GroupAlarmEquiv5 X q) _

noncomputable def stage2GroupBudgetParam5 (p : Params5 γ K' χ) (n D : ℕ) : ℝ :=
  (∑ j : Fin (p.J n + 1),
      ((((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2)) +
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4))) +
  ((p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (p.m n : ℝ)) +
  (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2)) +
  (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4)) +
  (stage2TypeCountBase5 : ℝ) *
    Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) +
  Real.exp (-20 * Real.log (p.m n : ℝ))

noncomputable def stage2GroupBudgetBound5 (X : Setup5 γ K' χ n N E G) (D : ℕ) : ℝ :=
  stage2GroupBudgetParam5 X.p n D

noncomputable def stage2GroupBudgetVanishing5 {γ K' χ : ℝ}
    (p : Params5 γ K' χ) (n : ℕ) : ℝ :=
  8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
      Real.exp (-5 * Real.log (p.m n : ℝ)) +
    3 * Real.exp (-19 * Real.log (p.m n : ℝ)) +
    (((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) *
      Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ)))

theorem stage2GroupAlarmFlatBudget_decomp5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    (∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a) =
      (∑ j : Fin (X.p.J n + 1),
        ∑ a : Stage2LowStep1Data5 X q j,
          stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) +
      (∑ a : Stage2HighStep1Data5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inl a))) +
      (∑ a : Stage2LowCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inl a)))) +
      (∑ a : Stage2HighCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))) +
      (∑ j : Fin (X.p.J n + 1),
        ∑ p : Stage2LowPatternAt5 X q j,
          stage2GroupAlarmFlatBudget5 X q
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) +
      (∑ p : Stage2HighPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))) +
      ∑ p : Stage2HighOptPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))))) := by
  classical
  simp [Stage2GroupAlarmFlat5, Fintype.sum_sum_type, Fintype.sum_sigma]

theorem stage2GroupAlarmFlatBudget_sum_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (hm : 1 ≤ X.p.m n) (hJ : X.p.J n ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1) :
    (∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a) ≤
      stage2GroupBudgetBound5 X (2 * 3 ^ coarseChunkCount5) := by
  classical
  let D0 : ℕ := 2 * 3 ^ coarseChunkCount5
  have hD0 : (nearCoarseKeys5 q.1).card ≤ D0 := by
    simpa [D0] using nearCoarseKeys5_card_le5 q.1
  let D : ℕ := D0
  have hD : (nearCoarseKeys5 q.1).card ≤ D := by simpa [D] using hD0
  have hmPos : 0 < X.p.m n := by omega
  have hCandidate (j : Fin (X.p.J n + 1)) :
      (lowTypeCandidates5 X q default j).card ≤
        stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val := by
    have hjJ : j.val ≤ X.p.J n := Nat.le_of_lt_succ j.isLt
    have hjm : j.val ≤ X.p.m n := le_trans hjJ hJ
    simpa [stage2TypeCountBase5, D0] using
      lowTypeCandidates_card5 X q default j hjm hmPos D0 hD0
  have hS1const (j : Fin (X.p.J n + 1)) (a : Stage2LowStep1Data5 X q j) :
      stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩) =
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2) := by
    rcases a with ⟨p, ℓ⟩
    simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
  have hS1j (j : Fin (X.p.J n + 1)) :
      (∑ a : Stage2LowStep1Data5 X q j,
        stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) ≤
      (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2)) := by
    have hsum : (∑ a : Stage2LowStep1Data5 X q j,
        stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) =
        (Fintype.card (Stage2LowStep1Data5 X q j) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2) := by
      simp [hS1const]
    rw [hsum]
    apply mul_le_mul_of_nonneg_right
    · have hcard := stage2LowStep1Data_card_le5 X q j
      have hcount : Fintype.card (Stage2LowStep1Data5 X q j) ≤
          stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
            (lowKeysBase5 + j.val) := by
        calc
          Fintype.card (Stage2LowStep1Data5 X q j) ≤
              (lowTypeCandidates5 X q default j).card * (lowKeysBase5 + j.val) := hcard
          _ ≤ (stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val) *
                (lowKeysBase5 + j.val) := Nat.mul_le_mul_right _ (hCandidate j)
      exact_mod_cast hcount
    · exact (Real.exp_pos _).le
  have hS1all :
      (∑ j : Fin (X.p.J n + 1),
        ∑ a : Stage2LowStep1Data5 X q j,
          stage2GroupAlarmFlatBudget5 X q (Sum.inl ⟨j, a⟩)) ≤
      ∑ j : Fin (X.p.J n + 1),
        (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 2)) := by
    exact Finset.sum_le_sum fun j hj => hS1j j
  have hS2j (j : Fin (X.p.J n + 1)) :
      (∑ p : Stage2LowPatternAt5 X q j,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) ≤
      (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by
    have hterm (p : Stage2LowPatternAt5 X q j) :
        stage2GroupAlarmFlatBudget5 X q
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩))))) ≤
          ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4) := by
      have hkeys := stage2LowPatternAt_keys_card_le5 X q j p
      have hkeys' : (p.1.2.1.card : ℝ) + 1 ≤
          ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hkeys 1
      have hbudget : stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩))))) =
          ((p.1.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4) := by
        simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
      rw [hbudget]
      exact mul_le_mul_of_nonneg_right hkeys' (Real.exp_pos _).le
    have hsum : (∑ p : Stage2LowPatternAt5 X q j,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) ≤
        (Fintype.card (Stage2LowPatternAt5 X q j) : ℝ) *
          (((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by
      calc
        _ ≤ ∑ _p : Stage2LowPatternAt5 X q j,
              ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
                Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4) :=
          Finset.sum_le_sum fun p hp => hterm p
        _ = _ := by simp
    calc
      _ ≤ (Fintype.card (Stage2LowPatternAt5 X q j) : ℝ) *
            (((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := hsum
      _ ≤ ((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val : ℕ) : ℝ) *
            (((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast (stage2LowPatternAt_card_le5 X q j).trans (hCandidate j)
          · exact mul_nonneg (by positivity) (Real.exp_pos _).le
      _ = (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
            (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) := by push_cast; ring
  have hS2all :
      (∑ j : Fin (X.p.J n + 1),
        ∑ p : Stage2LowPatternAt5 X q j,
          stage2GroupAlarmFlatBudget5 X q
            (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨j, p⟩)))))) ≤
      ∑ j : Fin (X.p.J n + 1),
        (((stage2TypeCountBase5 * (j.val + 1) * (X.p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n j.val)) / 4)) :=
    Finset.sum_le_sum fun j hj => hS2j j
  have hcapTerm (a : Stage2LowCapData5 X q) :
      stage2GroupAlarmFlatBudget5 X q
        (Sum.inr (Sum.inr (Sum.inl a))) ≤ Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    simpa [stage2GroupAlarmFlatBudget5] using
      X.p.capBudget_le_mpow_h23 n a.1.val hm hK1
  have hcap :
      (∑ a : Stage2LowCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inl a)))) ≤
        ((X.p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    calc
      _ ≤ (Fintype.card (Stage2LowCapData5 X q) : ℝ) *
          Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
        calc
          _ ≤ ∑ _a : Stage2LowCapData5 X q, Real.exp (-20 * Real.log (X.p.m n : ℝ)) :=
            Finset.sum_le_sum fun a ha => hcapTerm a
          _ = _ := by simp
      _ ≤ ((X.p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (X.p.m n : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast stage2LowCapData_card_le5 X q)
          (Real.exp_pos _).le
  have hhigh1const (a : Stage2HighStep1Data5 X q) :
      stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inl a)) =
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2) := by
    rcases a with ⟨p, ℓ⟩
    simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
  have hhigh1 :
      (∑ a : Stage2HighStep1Data5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inl a))) ≤
        (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)) := by
    calc
      _ = (Fintype.card (Stage2HighStep1Data5 X q) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2) := by simp [hhigh1const]
      _ ≤ (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast stage2HighStep1Data_card_le5 X q D hD
        · exact (Real.exp_pos _).le
  have hhighKeys (p : Stage2HighPatternAt5 X q) : p.1.2.1.card ≤ D :=
    (highTypeCandidates_keys_card_le5 X q p.1 p.2.1).trans hD
  have hhigh2term (p : Stage2HighPatternAt5 X q) :
      stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))) ≤
        ((D + 1 : ℕ) : ℝ) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
    have hplus : (p.1.2.1.card : ℝ) + 1 ≤ ((D + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (hhighKeys p) 1
    have hbud : stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))))) =
        ((p.1.2.1.card : ℝ) + 1) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
      simp [stage2GroupAlarmFlatBudget5, Params5.typeSegs, p.2.2.2.1]
    rw [hbud]
    exact mul_le_mul_of_nonneg_right hplus (Real.exp_pos _).le
  have hhigh2 :
      (∑ p : Stage2HighPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))))) ≤
        (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by
    calc
      _ ≤ ∑ _p : Stage2HighPatternAt5 X q,
          ((D + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) :=
        Finset.sum_le_sum fun p hp => hhigh2term p
      _ = (Fintype.card (Stage2HighPatternAt5 X q) : ℝ) *
          (((D + 1 : ℕ) : ℝ) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by simp
      _ ≤ (((stage2TypeCountBase5 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by
        have hc : Fintype.card (Stage2HighPatternAt5 X q) ≤ stage2TypeCountBase5 := by
          calc
            Fintype.card (Stage2HighPatternAt5 X q) ≤ (highTypeCandidates5 X q).card :=
              stage2HighPatternAt_card_le5 X q
            _ ≤ stage2TypeCountBase5 := by
              simpa [stage2TypeCountBase5, D] using highTypeCandidates_card5 X q D hD
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity))
          (Real.exp_pos _).le
      _ = (((stage2TypeCountBase5 * (D + 1) : ℕ) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) := by push_cast; ring
  have hhighOpt :
      (∑ p : Stage2HighOptPatternAt5 X q,
        stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))))) ≤
        (stage2TypeCountBase5 : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
    calc
      _ = (Fintype.card (Stage2HighOptPatternAt5 X q) : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by simp [stage2GroupAlarmFlatBudget5]
      _ ≤ (stage2TypeCountBase5 : ℝ) *
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (stage2HighOptPatternAt_card_le5 X q).trans (by
            calc
              (highTypeCandidates5 X q).card ≤ 2 ^ D := highTypeCandidates_card5 X q D hD
              _ = stage2TypeCountBase5 := by simp [stage2TypeCountBase5, D])
        · exact (Real.exp_pos _).le
  have hhighCapTerm (a : Stage2HighCapData5 X q) :
      stage2GroupAlarmFlatBudget5 X q
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) ≤
        Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    simpa [stage2GroupAlarmFlatBudget5] using
      X.p.capBudget_le_mpow_h23 n (X.p.J n) hm hK1
  have hhighCap :
      (∑ a : Stage2HighCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inr (Sum.inl a)))) ) ≤
        Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    calc
      _ ≤ ∑ _a : Stage2HighCapData5 X q, Real.exp (-20 * Real.log (X.p.m n : ℝ)) :=
        Finset.sum_le_sum fun a ha => hhighCapTerm a
      _ = (Fintype.card (Stage2HighCapData5 X q) : ℝ) *
          Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by simp
      _ ≤ 1 * Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast stage2HighCapData_card_le5 X q)
          (Real.exp_pos _).le
      _ = Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by ring
  have hcapAll :
      (∑ a : Stage2LowCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inl a)))) +
      (∑ a : Stage2HighCapData5 X q,
        stage2GroupAlarmFlatBudget5 X q (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))) ≤
      ((X.p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * Real.log (X.p.m n : ℝ)) +
        Real.exp (-20 * Real.log (X.p.m n : ℝ)) := by
    exact add_le_add hcap hhighCap
  rw [stage2GroupAlarmFlatBudget_decomp5]
  dsimp [stage2GroupBudgetBound5, D0]
  nlinarith [hS1all, hS2all, hhigh1, hhigh2, hhighOpt, hcapAll]

theorem lowPatternPolyBound5 (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ m) :
    ((j + 1 : ℕ) : ℝ) * ((lowKeysBase5 + j + 1 : ℕ) : ℝ) ≤
      2 * (lowKeysBase5 + 2 : ℕ) * (m : ℝ) ^ 2 := by
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hjR : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
  have hL : 0 ≤ (lowKeysBase5 : ℝ) := by positivity
  have hLprod : 0 ≤ (lowKeysBase5 : ℝ) * ((m : ℝ) - 1) :=
    mul_nonneg hL (by linarith)
  have hA : (j : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
  have hB : (lowKeysBase5 : ℝ) + j + 1 ≤
      (lowKeysBase5 + 2 : ℝ) * (m : ℝ) := by nlinarith [hLprod, hjR, hmR]
  calc
    ((j + 1 : ℕ) : ℝ) * ((lowKeysBase5 + j + 1 : ℕ) : ℝ) ≤
        (2 * (m : ℝ)) * ((lowKeysBase5 + 2 : ℝ) * (m : ℝ)) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    _ = 2 * (lowKeysBase5 + 2 : ℕ) * (m : ℝ) ^ 2 := by push_cast; ring

theorem natPow_mul_exp_decay5 {γ K' χ : ℝ} (p : Params5 γ K' χ)
    (n j : ℕ) (hm : 1 ≤ p.m n) :
    ((p.m n) ^ j : ℝ) * Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) ≤
      Real.exp (-8 * Real.log (p.m n : ℝ)) := by
  have hmpos : 0 < (p.m n : ℝ) := by exact_mod_cast (by omega : 0 < p.m n)
  have hpow : ((p.m n) ^ j : ℝ) =
      Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) := by
    calc
      ((p.m n) ^ j : ℝ) = (p.m n : ℝ) ^ j := by norm_cast
      _ = (p.m n : ℝ) ^ (j : ℝ) := by rw [← Real.rpow_natCast]
      _ = Real.exp (Real.log (p.m n : ℝ) * (j : ℝ)) :=
        Real.rpow_def_of_pos hmpos _
      _ = Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) := by congr 1; ring
  calc
    ((p.m n) ^ j : ℝ) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) =
      Real.exp ((j : ℝ) * Real.log (p.m n : ℝ)) *
        Real.exp (-2 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ)) := by rw [hpow]
    _ = Real.exp (-((j : ℝ) + 8) * Real.log (p.m n : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-8 * Real.log (p.m n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : 0 ≤ Real.log (p.m n : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
      nlinarith [hlog]

theorem stage2GroupBudgetBound_le_vanishing5 (X : Setup5 γ K' χ n N E G)
    (hm : 1 ≤ X.p.m n) (hJ : X.p.J n ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1) :
    stage2GroupBudgetBound5 X (2 * 3 ^ coarseChunkCount5) ≤
      stage2GroupBudgetVanishing5 X.p n := by
  classical
  let p := X.p
  let m : ℝ := p.m n
  let L : ℝ := Real.log m
  have hmPos : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < p.m n)
  have hlog : 0 ≤ L := by dsimp [L, m]; exact Real.log_nonneg (by exact_mod_cast hm)
  have hscale6 : m * Real.exp (-6 * L) = Real.exp (-5 * L) := by
    dsimp [m, L]
    simpa using p.natPow_exp_cancel_h23 n 1 6 hm
  have hscale20 : m * Real.exp (-20 * L) = Real.exp (-19 * L) := by
    dsimp [m, L]
    simpa using p.natPow_exp_cancel_h23 n 1 20 hm
  have hlowPer (j : Fin (p.J n + 1)) :
      (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2)) +
      (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4)) ≤
      4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
        Real.exp (-6 * L) := by
    have hjJ : j.val ≤ p.J n := Nat.le_of_lt_succ j.isLt
    have hjm : j.val ≤ p.m n := le_trans hjJ hJ
    have hpoly := lowPatternPolyBound5 (p.m n) j.val (by omega) hjm
    have hdecay := p.natPow_mul_exp_decay5 n j.val hm
    have hExp1 := p.lowAlarmExpStep1_le5 n j.val hm hK1
    have hExp2 := p.lowAlarmExp_le5 n j.val hm hK1
    have hcoeff1 :
        ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) ≤
        ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left
        (stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val) (Nat.le_succ _)
    have hpolyExp :
        ((j.val + 1 : ℕ) : ℝ) *
          ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ) *
          (((p.m n) ^ j.val : ℕ) : ℝ) *
          Real.exp (-2 * ((j.val : ℝ) + 4) * L) ≤
        2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2 *
          Real.exp (-8 * L) := by
      calc
        _ = (((j.val + 1 : ℕ) : ℝ) *
              ((lowKeysBase5 + j.val + 1 : ℕ) : ℝ)) *
              ((((p.m n) ^ j.val : ℕ) : ℝ) *
                Real.exp (-2 * ((j.val : ℝ) + 4) * L)) := by ring
        _ ≤ (2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2) *
              Real.exp (-8 * L) := by
          exact mul_le_mul (lowPatternPolyBound5 (p.m n) j.val (by omega) hjm)
            hdecay (by positivity) (by positivity)
    have hterm1 :
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2)) ≤
        2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-6 * L) := by
      calc
        _ ≤ (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
            (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
            Real.exp (-2 * ((j.val : ℝ) + 4) * L) :=
              mul_le_mul hcoeff1 hExp1 (by positivity) (by positivity)
        _ ≤ (stage2TypeCountBase5 : ℝ) *
              (2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2) *
              Real.exp (-8 * L) := by
          simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
            (mul_le_mul_of_nonneg_left hpolyExp (by positivity))
        _ = 2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              Real.exp (-6 * L) := by
          calc
            2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                (p.m n : ℝ) ^ 2 * Real.exp (-8 * L) =
              2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                ((p.m n) ^ 2 : ℝ) * Real.exp (-8 * L) := by ring
            _ = 2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                  Real.exp (-6 * L) := by
              dsimp [L]
              rw [p.natPow_exp_cancel_h23 n 2 8 hm]
              ring
    have hterm2 :
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4)) ≤
        2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-6 * L) := by
      calc
        _ ≤ (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
            (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
            Real.exp (-2 * ((j.val : ℝ) + 4) * L) :=
              mul_le_mul_of_nonneg_left hExp2 (by positivity)
        _ ≤ (stage2TypeCountBase5 : ℝ) *
              (2 * (lowKeysBase5 + 2 : ℝ) * (p.m n : ℝ) ^ 2) *
              Real.exp (-8 * L) := by
          simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
            (mul_le_mul_of_nonneg_left hpolyExp (by positivity))
        _ = 2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              Real.exp (-6 * L) := by
          calc
            2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                (p.m n : ℝ) ^ 2 * Real.exp (-8 * L) =
              2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                ((p.m n) ^ 2 : ℝ) * Real.exp (-8 * L) := by ring
            _ = 2 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                  Real.exp (-6 * L) := by
              dsimp [L]
              rw [p.natPow_exp_cancel_h23 n 2 8 hm]
              ring
    linarith
  have hlowSum :
      (∑ j : Fin (p.J n + 1),
        (((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 2) +
        ((stage2TypeCountBase5 * (j.val + 1) * (p.m n) ^ j.val *
          (lowKeysBase5 + j.val + 1) : ℕ) : ℝ) *
          Real.exp (-(p.delta * (p.q0 * p.uSeg n j.val)) / 4))) ≤
      8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
        Real.exp (-5 * L) := by
    calc
      _ ≤ ∑ _j : Fin (p.J n + 1),
          4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
            Real.exp (-6 * L) := Finset.sum_le_sum fun j hj => hlowPer j
      _ = ((p.J n + 1 : ℕ) : ℝ) *
          (4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
            Real.exp (-6 * L)) := by simp
      _ ≤ (2 * (p.m n : ℝ)) *
          (4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
            Real.exp (-6 * L)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hNat : p.J n + 1 ≤ 2 * p.m n := by omega
        exact_mod_cast hNat
      _ = 8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-5 * L) := by
        calc
          (2 * (p.m n : ℝ)) *
              (4 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
                Real.exp (-6 * L)) =
            8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              ((p.m n) ^ 1 : ℝ) * Real.exp (-6 * L) := by simp [pow_one]; ring
          _ = 8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
              Real.exp (-5 * L) := by
            dsimp [L]
            rw [p.natPow_exp_cancel_h23 n 1 6 hm]
            ring
  have hcapAll : ((p.J n + 1 : ℕ) : ℝ) * Real.exp (-20 * L) +
      Real.exp (-20 * L) ≤ 3 * Real.exp (-19 * L) := by
    have hNat : p.J n + 2 ≤ 3 * p.m n := by omega
    have hCast : ((p.J n + 1 : ℕ) : ℝ) + 1 ≤ 3 * (p.m n : ℝ) := by
      exact_mod_cast hNat
    calc
      _ = (((p.J n + 1 : ℕ) : ℝ) + 1) * Real.exp (-20 * L) := by ring
      _ ≤ (3 * (p.m n : ℝ)) * Real.exp (-20 * L) :=
        mul_le_mul_of_nonneg_right hCast (Real.exp_pos _).le
      _ = 3 * Real.exp (-19 * L) := by
        calc
          (3 * (p.m n : ℝ)) * Real.exp (-20 * L) =
              3 * ((p.m n) ^ 1 : ℝ) * Real.exp (-20 * L) := by simp [pow_one]
          _ = 3 * Real.exp (-19 * L) := by
            dsimp [L]
            rw [p.natPow_exp_cancel_h23 n 1 20 hm]
            ring
  have hstar := p.highAlarmExp_le5 n
  have hstarHalf :
      Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) ≤
        Real.exp (-(p.delta * p.eta / 4) * L) := by
    have hpos : 0 ≤ p.delta * ((p.q0 : ℝ) * p.uStarSeg n) := by positivity
    calc
      Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) ≤
          Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) := by
            apply Real.exp_le_exp.mpr
            nlinarith [hpos]
      _ ≤ Real.exp (-(p.delta * p.eta / 4) * L) := by
            simpa [L, m] using hstar
  have hhigh :
      (((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2)) +
      (((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4)) +
      (stage2TypeCountBase5 : ℝ) *
        Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) ≤
      (((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) *
        Real.exp (-(p.delta * p.eta / 4) * L) := by
    have hRate := p.highAlarmExp_le5 n
    have hCoef :
        (stage2TypeCountBase5 : ℝ) * (2 * (2 * 3 ^ coarseChunkCount5) + 3 : ℕ) =
          ((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [← hCoef]
    have h1 : Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 2) ≤
        Real.exp (-(p.delta * p.eta / 4) * L) := hstarHalf
    have h2 : Real.exp (-(p.delta * (p.q0 * p.uStarSeg n)) / 4) ≤
        Real.exp (-(p.delta * p.eta / 4) * L) := by simpa [L, m] using hRate
    have hC : 0 ≤ (stage2TypeCountBase5 : ℝ) *
        (2 * (2 * 3 ^ coarseChunkCount5) + 3 : ℕ) := by positivity
    nlinarith [h1, h2, hC]
  have hparam : stage2GroupBudgetParam5 p n (2 * 3 ^ coarseChunkCount5) ≤
      8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-5 * Real.log (p.m n : ℝ)) +
        3 * Real.exp (-19 * Real.log (p.m n : ℝ)) +
        (((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) *
          Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ)) := by
    unfold stage2GroupBudgetParam5
    dsimp [p, L, m] at hlowSum hcapAll hhigh ⊢
    nlinarith [hlowSum, hcapAll, hhigh]
  calc
    stage2GroupBudgetBound5 X (2 * 3 ^ coarseChunkCount5) =
        stage2GroupBudgetParam5 p n (2 * 3 ^ coarseChunkCount5) := rfl
    _ ≤ 8 * (stage2TypeCountBase5 : ℝ) * (lowKeysBase5 + 2 : ℝ) *
          Real.exp (-5 * Real.log (p.m n : ℝ)) +
        3 * Real.exp (-19 * Real.log (p.m n : ℝ)) +
        (((stage2TypeCountBase5 * (2 * (2 * 3 ^ coarseChunkCount5) + 3) : ℕ) : ℝ) *
          Real.exp (-(p.delta * p.eta / 4) * Real.log (p.m n : ℝ)) := hparam
    _ = stage2GroupBudgetVanishing5 p n := by rfl

theorem stage2GroupAlarmBad_ext5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) (c c' : X.Coarse)
    (h : ∀ w ∈ stage2GroupAlarmScope5 X q i,
      c.1 w = c'.1 w ∧ c.2 w = c'.2 w) :
    stage2GroupAlarmBad5 X v q i c ↔ stage2GroupAlarmBad5 X v q i c' := by
  cases i with
  | lowStep1 j p ℓ =>
      have hp : ∀ w ∈ binList5 ℓ.1.coarse, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 ℓ.1.coarse, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1) ↔
        X.step1Fail (v, c') ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
      exact step1Fail_ext_bins5 X (v, c) (v, c') ℓ.1 p.1.1.1
        (X.p.typeSegs n p.1) rfl hp hW
  | highStep1 p ℓ =>
      have hp : ∀ w ∈ binList5 ℓ.1.coarse, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 ℓ.1.coarse, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.step1Fail (v, c) ℓ.1 p.1.1.1 (X.p.typeSegs n p.1) ↔
        X.step1Fail (v, c') ℓ.1 p.1.1.1 (X.p.typeSegs n p.1)
      exact step1Fail_ext_bins5 X (v, c) (v, c') ℓ.1 p.1.1.1
        (X.p.typeSegs n p.1) rfl hp hW
  | lowCap j hKey =>
      have hp : ∀ w ∈ binList5 q, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 q, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.capFail (v, c) (.inl (q, default, j)) ↔
        X.capFail (v, c') (.inl (q, default, j))
      exact capFail_ext_bins5 X (v, c) (v, c') (.inl (q, default, j)) rfl hp hW
  | highCap hKey =>
      have hp : ∀ w ∈ binList5 q, c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ binList5 q, c.2 w = c'.2 w := fun w hw => (h w hw).2
      change X.capFail (v, c) (.inr q) ↔ X.capFail (v, c') (.inr q)
      exact capFail_ext_bins5 X (v, c) (v, c') (.inr q) rfl hp hW
  | lowStep2 j p =>
      have hp : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.1 w = c'.1 w :=
        fun w hw => (h w hw).1
      have hW : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.2 w = c'.2 w :=
        fun w hw => (h w hw).2
      have hprob := step2FailPr_ext_bins5 X (v, c) (v, c') p.1 rfl hp hW
      change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) ↔
        (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c')).pr (fun U => X.step2Fail ((v, c'), U) p.1))
      rw [hprob]
  | highStep2 p =>
      have hp : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.1 w = c'.1 w :=
        fun w hw => (h w hw).1
      have hW : ∀ w ∈ blockLocalBins5 X p.1 p.1.2.1, c.2 w = c'.2 w :=
        fun w hw => (h w hw).2
      have hprob := step2FailPr_ext_bins5 X (v, c) (v, c') p.1 rfl hp hW
      change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) ↔
        (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c')).pr (fun U => X.step2Fail ((v, c'), U) p.1))
      rw [hprob]
  | highOptional p =>
      have hp : ∀ w ∈ blockLocalBins5 X p.1.1 (insert (X.optKeyOf p.1.1 default) p.1.1.2.1),
          c.1 w = c'.1 w := fun w hw => (h w hw).1
      have hW : ∀ w ∈ blockLocalBins5 X p.1.1 (insert (X.optKeyOf p.1.1 default) p.1.1.2.1),
          c.2 w = c'.2 w := fun w hw => (h w hw).2
      have hprob := optFailPr_ext_bins5 X (v, c) (v, c') p.1.1 default rfl hp hW
      change (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) p.1.1 default)) ↔
        (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
          (X.hiddenLaw (v, c')).pr (fun U => X.optFail ((v, c'), U) p.1.1 default))
      rw [hprob]

noncomputable def stage2GroupBad5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (c : X.Coarse) : Prop :=
  ∃ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBad5 X v q i c

theorem stage2GroupGood_conclusions5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (c : X.Coarse) (hgood : ∀ q : CoarseKey5 n, ¬ stage2GroupBad5 X v q c) :
    (∀ K, X.TypeOccurs K → ∀ ℓ ∈ X.gateKeys K,
      ¬ X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K)) ∧
    (∀ ℓ, X.KeyOccurs ℓ → ¬ X.capFail (v, c) ℓ) ∧
    (∀ K, X.TypeOccurs K →
      (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
        ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)) ∧
    ∀ K t, X.OptOccurs K t →
      (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) ≤
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK ℓ hℓ
    obtain ⟨x, hx, htype⟩ := hK
    by_cases hlow : X.g.severity x ≤ X.p.J n
    · obtain ⟨j, p, hpK⟩ := stage2LowPatternAt_of_role5 X x hx hlow
      let t := X.g.sign x
      have hgate : X.gateKeys p.1 = (X.gateKeys K).image (signShiftKey5 X t) := by
        rw [htype]
        exact gateKeys_signShiftLow5 X t K (by
          simpa [ChunkGeometry5.evenType, hlow] using (show K.2.2 = some ⟨X.g.severity x, Nat.lt_succ_of_le hlow⟩ from by
            rw [htype]
            simp [ChunkGeometry5.evenType, hlow]))
      have hℓmem : signShiftKey5 X t ℓ ∈ X.gateKeys p.1 := by
        rw [hgate]
        exact Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
      have hnot : ¬ stage2GroupAlarmBad5 X v (X.g.key x)
          (.lowStep1 j p ⟨signShiftKey5 X t ℓ, hℓmem⟩) c := by
        intro hbad
        exact hgood (X.g.key x) ⟨.lowStep1 j p ⟨signShiftKey5 X t ℓ, hℓmem⟩, hbad⟩
      intro hfail
      exact hnot ((step1Fail_signShift5 X (v, c) t K ℓ).mpr hfail)
    · obtain ⟨p, hpK⟩ := stage2HighPatternAt_of_role5 X x hx hlow
      have hnot : ¬ stage2GroupAlarmBad5 X v (X.g.key x)
          (.highStep1 p ⟨ℓ, by simpa [htype] using hℓ⟩) c := by
        intro hbad
        exact hgood (X.g.key x) ⟨.highStep1 p ⟨ℓ, by simpa [htype] using hℓ⟩, hbad⟩
      simpa [htype] using hnot
  · intro ℓ hℓ
    cases ℓ with
    | inl low =>
        rcases low with ⟨q, t, j⟩
        let ℓ₀ : X.Key := .inl (q, default, j)
        have hshift : signShiftKey5 X t (.inl (q, t, j)) = ℓ₀ := by
          simp [signShiftKey5, shiftSignVector_self5]
        have hocc : stage2LowCapOccurs5 X q j := ⟨.inl (q, t, j), hℓ, t, hshift⟩
        have hnot : ¬ stage2GroupAlarmBad5 X v q (.lowCap j hocc) c := by
          intro hbad
          exact hgood q ⟨.lowCap j hocc, hbad⟩
        intro hfail
        exact hnot ((capFail_signShift5 X (v, c) t (.inl (q, t, j))).mpr hfail)
    | inr q =>
        have hnot : ¬ stage2GroupAlarmBad5 X v q (.highCap hℓ) c := by
          intro hbad
          exact hgood q ⟨.highCap hℓ, hbad⟩
        exact hnot
  · intro K hK
    obtain ⟨x, hx, htype⟩ := hK
    by_cases hlow : X.g.severity x ≤ X.p.J n
    · obtain ⟨j, p, hpK⟩ := stage2LowPatternAt_of_role5 X x hx hlow
      let t := X.g.sign x
      have hnot : ¬ stage2GroupAlarmBad5 X v (X.g.key x) (.lowStep2 j p) c := by
        intro hbad
        exact hgood (X.g.key x) ⟨.lowStep2 j p, hbad⟩
      have hcanonical : (X.hiddenLaw (v, c)).pr
          (fun U => X.step2Fail ((v, c), U) p.1) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) := by
        have hle := le_of_not_gt hnot
        change ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) p.1)) at hnot
        exact le_of_not_gt hnot
      have hpr : (X.hiddenLaw (v, c)).pr
          (fun U => X.step2Fail ((v, c), U) p.1) =
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) := by
        have hlevel : K.2.2 = some j := by
          rw [htype]
          simp [ChunkGeometry5.evenType, hlow]
        simpa [hpK, htype, t] using step2FailPr_signShiftLowSimple5 X (v, c) t K hlevel
      rw [hpr] at hcanonical
      have hfactor : (1 : ℝ) ≤ (K.2.1.card : ℝ) + 1 := by positivity
      calc
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
              simpa [htype] using hcanonical
        _ ≤ ((K.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
              exact mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
    · have hnot : ¬ stage2GroupAlarmBad5 X v (X.g.key x) (.highStep2
          (stage2HighPatternAt_of_role5 X x hx hlow).choose) c := by
        intro hbad
        exact hgood (X.g.key x) ⟨.highStep2 (stage2HighPatternAt_of_role5 X x hx hlow).choose, hbad⟩
      have hle : (X.hiddenLaw (v, c)).pr
          (fun U => X.step2Fail ((v, c), U) K) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
        have hKnone : K.2.2 = none := by
          rw [htype]
          simp [ChunkGeometry5.evenType, hlow]
        have htypeOccurs : X.TypeOccurs K := hK
        have hp := stage2HighPatternAt_of_role5 X x hx hlow
        have hpEq : hp.choose.1 = K := by simpa [htype] using hp.choose_spec.2
        have hnot' : ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) <
            (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K)) := by
          simpa [hpEq] using hnot
        exact le_of_not_gt hnot'
      calc
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := hle
        _ ≤ ((K.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
              have hc : (1 : ℝ) ≤ (K.2.1.card : ℝ) + 1 := by positivity
              exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
  · intro K t hOpt
    have hnone : K.2.2 = none := optOccurs_high5 X K t hOpt
    have hType : X.TypeOccurs K := by
      rcases hOpt with ⟨x, hx, hK, hoptional⟩
      exact ⟨x, hx, hK.symm⟩
    have hHigh := typeOccurs_highKeys5 X K hType hnone
    rcases hOpt with ⟨x, hx, hK, hoptional⟩
    have hp := stage2HighPatternAt_of_role5 X x hx (by
      rw [← hK]
      have hn := hnone
      simpa [ChunkGeometry5.evenType] using hn)
    have hpEq : hp.choose.1 = K := by simpa [hK] using hp.choose_spec.2
    have hnot : ¬ stage2GroupAlarmBad5 X v (X.g.key x)
        (.highOptional ⟨hp.choose, ⟨t, hOpt⟩⟩) c := by
      intro hbad
      exact hgood (X.g.key x) ⟨.highOptional ⟨hp.choose, ⟨t, hOpt⟩⟩, hbad⟩
    have hcanonical : (X.hiddenLaw (v, c)).pr
        (fun U => X.optFail ((v, c), U) K (default : CubeVertex (X.p.m n))) ≤
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) := by
      have hnot' : ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K default)) := by
        simpa [hpEq] using hnot
      exact le_of_not_gt hnot'
    have hpr : (X.hiddenLaw (v, c)).pr
        (fun U => X.optFail ((v, c), U) K default) =
      (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) := by
      simpa [shiftSignVector_self5, signShiftType5_eq_of_highKeys X t K hHigh] using
        optFailPr_signShiftHighSimple5 X (v, c) t t K hnone hHigh
    rw [hpr] at hcanonical
    exact hcanonical

noncomputable def stage2GroupBadOnPairs5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) (ω : BinVector5 n → Fin N × X.Stream) : Prop :=
  stage2GroupBad5 X v q (coarsePairEquiv5 X ω)

theorem stage2GroupBadOnPairs_depends5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) :
    FinProb.DependsOn (stage2GroupBadOnPairs5 X v q) (stage2GroupScope5 X q) := by
  classical
  intro ω ω' hω
  let e := coarsePairEquiv5 X
  let c := e ω
  let c' := e ω'
  have hpair : ∀ w ∈ stage2GroupScope5 X q,
      c.1 w = c'.1 w ∧ c.2 w = c'.2 w := by
    intro w hw
    change (ω w).1 = (ω' w).1 ∧ (ω w).2 = (ω' w).2
    have hp := hω w hw
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  have hbad (i : Stage2GroupAlarm5 X q) :
      stage2GroupAlarmBad5 X v q i c ↔ stage2GroupAlarmBad5 X v q i c' := by
    apply stage2GroupAlarmBad_ext5
    intro w hw
    exact hpair w (stage2GroupAlarmScope_subset5 X q i hw)
  change (∃ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBad5 X v q i c) ↔
    (∃ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBad5 X v q i c')
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hbad i).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hbad i).mpr hi⟩

theorem stage2LowPatternAt_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (j : Fin (X.p.J n + 1)) :
    Fintype.card (Stage2LowPatternAt5 X q j) ≤ (lowTypeCandidates5 X q default j).card := by
  classical
  let f : Stage2LowPatternAt5 X q j → {K : X.Ty // K ∈ lowTypeCandidates5 X q default j} :=
    fun K => ⟨K.1, K.2.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    change a.1 = b.1
    exact congrArg (fun z : {K : X.Ty // K ∈ lowTypeCandidates5 X q default j} => z.1) hab
  calc
    Fintype.card (Stage2LowPatternAt5 X q j) ≤
        Fintype.card {K : X.Ty // K ∈ lowTypeCandidates5 X q default j} :=
      Fintype.card_le_of_injective f hf
    _ = (lowTypeCandidates5 X q default j).card := by rw [Fintype.card_coe]

theorem stage2HighPatternAt_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    Fintype.card (Stage2HighPatternAt5 X q) ≤ (highTypeCandidates5 X q).card := by
  classical
  let f : Stage2HighPatternAt5 X q → {K : X.Ty // K ∈ highTypeCandidates5 X q} :=
    fun K => ⟨K.1, K.2.1⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    change a.1 = b.1
    exact congrArg (fun z : {K : X.Ty // K ∈ highTypeCandidates5 X q} => z.1) hab
  calc
    Fintype.card (Stage2HighPatternAt5 X q) ≤
        Fintype.card {K : X.Ty // K ∈ highTypeCandidates5 X q} :=
      Fintype.card_le_of_injective f hf
    _ = (highTypeCandidates5 X q).card := by rw [Fintype.card_coe]

theorem stage2LowPattern_exists5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (heven : IsEvenRole x) (hlow : X.g.severity x ≤ X.p.J n) :
    ∃ p : Stage2LowPattern5 X,
      p.1 = X.g.key x ∧ p.2.1.val = X.g.severity x ∧
        p.2.2.1 = signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x) := by
  classical
  let j : Fin (X.p.J n + 1) := ⟨X.g.severity x, by omega⟩
  let K : X.Ty := signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x)
  have hmem : K ∈ lowTypeCandidates5 X (X.g.key x) default j := by
    exact normalizedEvenType_mem_candidates5 X x j rfl
  have hlevel : K.2.2 = some j := by
    dsimp [K]
    rw [signShiftType5_level]
    have hfin : (⟨X.g.severity x, Nat.lt_succ_of_le hlow⟩ : Fin (X.p.J n + 1)) = j := by
      apply Fin.ext
      rfl
    simpa [ChunkGeometry5.evenType, hlow] using congrArg some hfin
  refine ⟨⟨X.g.key x, j, ⟨K, hmem, rfl, hlevel, ⟨x, heven, rfl⟩⟩⟩, rfl, ?_, ?_⟩
  · rfl
  · rfl

theorem stage2HighPattern_exists5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (heven : IsEvenRole x) (hhigh : ¬ X.g.severity x ≤ X.p.J n) :
    ∃ p : Stage2HighPattern5 X,
      p.1 = X.g.key x ∧ p.2.1 = X.g.evenType (X.p.J n) x := by
  classical
  have hlevel : (X.g.evenType (X.p.J n) x).2.2 = none := by
    simp [ChunkGeometry5.evenType, hhigh]
  refine ⟨⟨X.g.key x, ⟨X.g.evenType (X.p.J n) x,
    highEvenType_mem_candidates5 X x hhigh, rfl, hlevel, ⟨x, heven, rfl⟩⟩⟩, rfl, rfl⟩

theorem stage2LowPatternAt_of_role5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (heven : IsEvenRole x) (hlow : X.g.severity x ≤ X.p.J n) :
    ∃ j : Fin (X.p.J n + 1), ∃ p : Stage2LowPatternAt5 X (X.g.key x) j,
      p.1 = signShiftType5 X (X.g.sign x) (X.g.evenType (X.p.J n) x) := by
  classical
  obtain ⟨p, hq, hj, hK⟩ := stage2LowPattern_exists5 X x heven hlow
  let j := p.2.1
  let pAt : Stage2LowPatternAt5 X (X.g.key x) j := by
    refine ⟨p.2.2.1, ?_⟩
    simpa [j, hq] using p.2.2.2
  refine ⟨j, pAt, ?_⟩
  simpa [pAt] using hK

theorem stage2HighPatternAt_of_role5 (X : Setup5 γ K' χ n N E G)
    (x : CubeVertex n) (heven : IsEvenRole x) (hhigh : ¬ X.g.severity x ≤ X.p.J n) :
    ∃ p : Stage2HighPatternAt5 X (X.g.key x),
      p.1 = X.g.evenType (X.p.J n) x := by
  classical
  obtain ⟨p, hq, hK⟩ := stage2HighPattern_exists5 X x heven hhigh
  let pAt : Stage2HighPatternAt5 X (X.g.key x) := by
    refine ⟨p.2.1, ?_⟩
    simpa [hq] using p.2.2
  exact ⟨pAt, by simpa [pAt] using hK⟩

theorem blockGate_signShiftLow5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) (z : X.Block K) :
    X.blockGate b (signShiftType5 X t K) z ↔ X.blockGate b K z := by
  classical
  let e := signShiftKey5 X t
  let K' := signShiftType5 X t K
  have hGateSet : X.gateKeys K' = (X.gateKeys K).image e := by
    simp [Setup5.gateKeys, e, K', signShiftType5, hlevel]
  have hcenter : K'.1.1 = K.1.1 := by rfl
  have hsegs : X.p.typeSegs n K' = X.p.typeSegs n K :=
    signShiftType5_segs X t K
  constructor
  · intro h ℓ hℓ y
    have hmem : e ℓ ∈ X.gateKeys K' := by
      rw [hGateSet]
      exact Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩
    have hrep : X.priorRep b (e ℓ) K.1.1 z = X.priorRep b ℓ K.1.1 z := by
      exact priorRep_irrel_sign5 X b (e ℓ) ℓ K.1.1 z
        (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)
    have hdel : X.priorDel b (e ℓ) K.1.1 (X.p.typeSegs n K) =
        X.priorDel b ℓ K.1.1 (X.p.typeSegs n K) := by
      exact priorDel_irrel_sign5 X b (e ℓ) ℓ K.1.1 (X.p.typeSegs n K)
        (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)
    have h0 := h (e ℓ) hmem y
    change (X.priorRep b (e ℓ) K.1.1 z).w y ≤
      Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n K)) *
        (X.priorDel b (e ℓ) K.1.1 (X.p.typeSegs n K)).w y at h0
    rw [hrep, hdel] at h0
    exact h0
  · intro h ℓ hℓ y
    have hmem : ℓ ∈ (X.gateKeys K).image e := by
      rw [← hGateSet]
      exact hℓ
    obtain ⟨ℓ₀, hℓ₀, heq⟩ := Finset.mem_image.mp hmem
    subst ℓ
    have hrep : X.priorRep b (e ℓ₀) K.1.1 z = X.priorRep b ℓ₀ K.1.1 z := by
      exact priorRep_irrel_sign5 X b (e ℓ₀) ℓ₀ K.1.1 z
        (signShiftKey5_coarse X t ℓ₀) (signShiftKey5_level X t ℓ₀)
    have hdel : X.priorDel b (e ℓ₀) K.1.1 (X.p.typeSegs n K) =
        X.priorDel b ℓ₀ K.1.1 (X.p.typeSegs n K) := by
      exact priorDel_irrel_sign5 X b (e ℓ₀) ℓ₀ K.1.1 (X.p.typeSegs n K)
        (signShiftKey5_coarse X t ℓ₀) (signShiftKey5_level X t ℓ₀)
    have h0 := h ℓ₀ hℓ₀ y
    change (X.priorRep b ℓ₀ K.1.1 z).w y ≤
      Real.exp (X.p.a 1 * (X.p.q0 * X.p.typeSegs n K)) *
        (X.priorDel b ℓ₀ K.1.1 (X.p.typeSegs n K)).w y at h0
    rw [← hrep, ← hdel] at h0
    exact h0

theorem colLik_signShiftLow5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (z : X.Block K) (ℓ : X.Key) :
    X.colLik (signShiftHistory5 X t H).1 (signShiftType5 X t K)
        (signShiftKey5 X t ℓ) z
        ((signShiftHistory5 X t H).2 (signShiftKey5 X t ℓ)) =
      X.colLik H.1 K ℓ z (H.2 ℓ) := by
  classical
  let e := signShiftKey5 X t
  let K' := signShiftType5 X t K
  let H' := signShiftHistory5 X t H
  have hlen := signShiftKey5_colLen X t ℓ
  have hrep : X.priorRep H.1 (e ℓ) K.1.1 z = X.priorRep H.1 ℓ K.1.1 z := by
    exact priorRep_irrel_sign5 X H.1 (e ℓ) ℓ K.1.1 z
      (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)
  have hdel : X.priorDel H.1 (e ℓ) K.1.1 (X.p.typeSegs n K) =
      X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K) := by
    exact priorDel_irrel_sign5 X H.1 (e ℓ) ℓ K.1.1 (X.p.typeSegs n K)
      (signShiftKey5_coarse X t ℓ) (signShiftKey5_level X t ℓ)
  have hcol (h : Fin (colLen5 (X.p.s n) (e ℓ))) :
      H'.2 (e ℓ) h = H.2 ℓ (Fin.cast hlen h) := by
    exact hiddenSignShift5_apply_signShiftKey X t H.2 ℓ h
  change (∏ h : Fin (colLen5 (X.p.s n) (e ℓ)),
      ratio5 ((X.priorRep H.1 (e ℓ) K.1.1 z).w (H'.2 (e ℓ) h))
        ((X.priorDel H.1 (e ℓ) K.1.1 (X.p.typeSegs n K)).w (H'.2 (e ℓ) h))) =
    ∏ h : Fin (colLen5 (X.p.s n) ℓ),
      ratio5 ((X.priorRep H.1 ℓ K.1.1 z).w (H.2 ℓ h))
        ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (H.2 ℓ h))
  exact Fintype.prod_equiv (finCastEquiv5 hlen)
    (fun h => ratio5 ((X.priorRep H.1 (e ℓ) K.1.1 z).w (H'.2 (e ℓ) h))
      ((X.priorDel H.1 (e ℓ) K.1.1 (X.p.typeSegs n K)).w (H'.2 (e ℓ) h)))
    (fun h => ratio5 ((X.priorRep H.1 ℓ K.1.1 z).w (H.2 ℓ h))
      ((X.priorDel H.1 ℓ K.1.1 (X.p.typeSegs n K)).w (H.2 ℓ h)))
    (by
      intro h
      rw [hcol h, hrep, hdel]
      rfl)

theorem blockWeight_signShiftLow5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) (S : Finset X.Key) (z : X.Block K) :
    X.blockWeight (signShiftHistory5 X t H) (signShiftType5 X t K)
        (S.image (signShiftKey5 X t)) z = X.blockWeight H K S z := by
  classical
  let e := signShiftKey5 X t
  let K' := signShiftType5 X t K
  let H' := signShiftHistory5 X t H
  have hbase : X.blockBase H'.1 K' z = X.blockBase H.1 K z := by
    change X.blockBase H.1 K z = X.blockBase H.1 K z
    rfl
  have hgate : X.blockGate H'.1 K' z = X.blockGate H.1 K z :=
    by
      change X.blockGate H.1 (signShiftType5 X t K) z = X.blockGate H.1 K z
      exact propext (blockGate_signShiftLow5 X H.1 t K hlevel z)
  have hlik : ∀ ℓ ∈ S,
      X.colLik H'.1 K' (e ℓ) z (H'.2 (e ℓ)) = X.colLik H.1 K ℓ z (H.2 ℓ) := by
    intro ℓ hℓ
    exact colLik_signShiftLow5 X H t K z ℓ
  have hprod :
      (∏ ℓ ∈ S.image e, X.colLik H'.1 K' ℓ z (H'.2 ℓ)) =
        ∏ ℓ ∈ S, X.colLik H.1 K ℓ z (H.2 ℓ) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro ℓ hℓ
      exact hlik ℓ hℓ
    · intro ℓ hℓ ℓ' hℓ' heq
      exact e.injective heq
  unfold Setup5.blockWeight
  rw [hbase, hgate, hprod]

theorem blockMass_signShiftLow5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) (S : Finset X.Key) :
    X.blockMass (signShiftHistory5 X t H) (signShiftType5 X t K)
        (S.image (signShiftKey5 X t)) = X.blockMass H K S := by
  classical
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z hz
  exact blockWeight_signShiftLow5 X H t K hlevel S z

theorem blockWeight_signShiftCore5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (S : Finset X.Key) (z : X.Block K)
    (hgate : X.blockGate (signShiftHistory5 X t H).1 (signShiftType5 X t K) z =
      X.blockGate H.1 K z) :
    X.blockWeight (signShiftHistory5 X t H) (signShiftType5 X t K)
        (S.image (signShiftKey5 X t)) z = X.blockWeight H K S z := by
  classical
  let e := signShiftKey5 X t
  let K' := signShiftType5 X t K
  let H' := signShiftHistory5 X t H
  have hbase : X.blockBase H'.1 K' z = X.blockBase H.1 K z := by
    change X.blockBase H.1 K z = X.blockBase H.1 K z
    rfl
  have hlik : ∀ ℓ ∈ S,
      X.colLik H'.1 K' (e ℓ) z (H'.2 (e ℓ)) = X.colLik H.1 K ℓ z (H.2 ℓ) := by
    intro ℓ hℓ
    exact colLik_signShiftLow5 X H t K z ℓ
  have hprod :
      (∏ ℓ ∈ S.image e, X.colLik H'.1 K' ℓ z (H'.2 ℓ)) =
        ∏ ℓ ∈ S, X.colLik H.1 K ℓ z (H.2 ℓ) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro ℓ hℓ
      exact hlik ℓ hℓ
    · intro ℓ hℓ ℓ' hℓ' heq
      exact e.injective heq
  unfold Setup5.blockWeight
  rw [hbase, hgate, hprod]

theorem blockMass_signShiftCore5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (S : Finset X.Key)
    (hgate : ∀ z : X.Block K,
      X.blockGate (signShiftHistory5 X t H).1 (signShiftType5 X t K) z =
        X.blockGate H.1 K z) :
    X.blockMass (signShiftHistory5 X t H) (signShiftType5 X t K)
        (S.image (signShiftKey5 X t)) = X.blockMass H K S := by
  classical
  unfold Setup5.blockMass
  apply Finset.sum_congr rfl
  intro z hz
  exact blockWeight_signShiftCore5 X H t K S z (hgate z)

theorem step2Fail_signShiftLow5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    X.step2Fail (signShiftHistory5 X t H) (signShiftType5 X t K) ↔ X.step2Fail H K := by
  classical
  let e := signShiftKey5 X t
  let K' := signShiftType5 X t K
  let H' := signShiftHistory5 X t H
  have hsegs : X.p.typeSegs n K' = X.p.typeSegs n K := signShiftType5_segs X t K
  have hsum : (∑ ℓ ∈ K'.2.1, (colLen5 (X.p.s n) ℓ : ℝ)) =
      ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ) := by
    change (∑ ℓ ∈ K.2.1.image e, (colLen5 (X.p.s n) ℓ : ℝ)) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro ℓ hℓ
      rw [signShiftKey5_colLen]
    · exact e.injective.injOn
  have hMass : X.blockMass H' K' K'.2.1 = X.blockMass H K K.2.1 := by
    change X.blockMass H' K' (K.2.1.image e) = _
    exact blockMass_signShiftLow5 X H t K hlevel K.2.1
  have hErase (ℓ : X.Key) : K'.2.1.erase (e ℓ) = (K.2.1.erase ℓ).image e := by
    change (K.2.1.image e).erase (e ℓ) = (K.2.1.erase ℓ).image e
    exact (K.2.1.image_erase e.injective ℓ).symm
  have hMassErase (ℓ : X.Key) :
      X.blockMass H' K' (K'.2.1.erase (e ℓ)) =
        X.blockMass H K (K.2.1.erase ℓ) := by
    rw [hErase ℓ]
    exact blockMass_signShiftLow5 X H t K hlevel (K.2.1.erase ℓ)
  have hTrue : X.trueBlock H'.1 K' = X.trueBlock H.1 K := by
    change X.trueBlock H.1 (signShiftType5 X t K) = X.trueBlock H.1 K
    rfl
  have hGate : X.blockGate H'.1 K' (X.trueBlock H'.1 K') ↔
      X.blockGate H.1 K (X.trueBlock H.1 K) := by
    rw [hTrue]
    exact blockGate_signShiftLow5 X H.1 t K hlevel (X.trueBlock H.1 K)
  unfold Setup5.step2Fail
  constructor
  · rintro ⟨hgate, hfail⟩
    refine ⟨hGate.mp hgate, ?_⟩
    rcases hfail with hmass | ⟨ℓ, hℓ, hmass⟩
    · left
      simpa [H', K', hMass, hsum, hsegs] using hmass
    · right
      have hmem : ℓ ∈ K.2.1.image e := by
        change ℓ ∈ K'.2.1 at hℓ
        simpa [K', signShiftType5] using hℓ
      obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Finset.mem_image.mp hmem
      refine ⟨ℓ₀, hℓ₀, ?_⟩
      rw [signShiftKey5_colLen X t ℓ₀] at hmass
      simpa [H', K', hMass, hMassErase ℓ₀, hsegs] using hmass
  · rintro ⟨hgate, hfail⟩
    refine ⟨hGate.mpr hgate, ?_⟩
    rcases hfail with hmass | ⟨ℓ', hℓ', hmass⟩
    · left
      simpa [H', K', hMass, hsum, hsegs] using hmass
    · have hℓshift : e ℓ' ∈ K'.2.1 := by
        change e ℓ' ∈ K.2.1.image e
        exact Finset.mem_image.mpr ⟨ℓ', hℓ', rfl⟩
      right
      refine ⟨e ℓ', hℓshift, ?_⟩
      rw [← signShiftKey5_colLen X t ℓ'] at hmass
      simpa [H', K', hMass, hMassErase ℓ', hsegs] using hmass

theorem step2FailPr_signShiftLow5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    (X.hiddenLaw b).pr (fun U =>
      X.step2Fail (b, hiddenSignShift5 X t U) (signShiftType5 X t K)) =
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) := by
  classical
  let P := X.hiddenLaw b
  let A : X.Hidden → Prop := fun U => X.step2Fail (b, U) (signShiftType5 X t K)
  have hMap := map_pr_equiv5 P (hiddenSignShift5 X t) A
  rw [hiddenLaw_map_signShift5 X b t] at hMap
  have hEvent (U : X.Hidden) : A (hiddenSignShift5 X t U) ↔ X.step2Fail (b, U) K := by
    simpa [A, signShiftHistory5] using step2Fail_signShiftLow5 X (b, U) t K hlevel
  calc
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, hiddenSignShift5 X t U)
        (signShiftType5 X t K)) = P.pr A := hMap.symm
    _ = P.pr (fun U => A (hiddenSignShift5 X t U)) := hMap
    _ = (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) :=
      pr_congr5 P _ _ hEvent

theorem optFail_signShiftHigh5 (X : Setup5 γ K' χ n N E G) (H : X.KeyHist)
    (t₀ t : CubeVertex (X.p.m n)) (K : X.Ty)
    (hnone : K.2.2 = none)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    X.optFail (signShiftHistory5 X t₀ H) (signShiftType5 X t₀ K)
        (shiftSignVector5 t₀ t) ↔ X.optFail H K t := by
  classical
  let e := signShiftKey5 X t₀
  let K' := signShiftType5 X t₀ K
  let H' := signShiftHistory5 X t₀ H
  have hK : K' = K := signShiftType5_eq_of_highKeys X t₀ K hHigh
  have hS : K'.2.1 = K.2.1 := congrArg (fun T : X.Ty => T.2.1) hK
  have hImage : K.2.1.image e = K.2.1 := by
    change K'.2.1 = K.2.1
    exact hS
  have hopt : e (X.optKeyOf K t) = X.optKeyOf K (shiftSignVector5 t₀ t) := by
    rfl
  have hGateSet : X.gateKeys K' = X.gateKeys K := by
    rw [hK]
  have hPlus : insert (X.optKeyOf K' (shiftSignVector5 t₀ t)) K'.2.1 =
      (insert (X.optKeyOf K t) K.2.1).image e := by
    calc
      insert (X.optKeyOf K' (shiftSignVector5 t₀ t)) K'.2.1 =
          insert (X.optKeyOf K (shiftSignVector5 t₀ t)) K.2.1 := by rw [hK]
      _ = (insert (X.optKeyOf K t) K.2.1).image e := by
        rw [Finset.image_insert, hopt, hImage]
  have hgate (z : X.Block K) : X.blockGate H'.1 K' z = X.blockGate H.1 K z := by
    change X.blockGate H.1 K' z = X.blockGate H.1 K z
    unfold Setup5.blockGate
    rw [hGateSet]
    rfl
  have hMass : X.blockMass H' K' K'.2.1 = X.blockMass H K K.2.1 := by
    exact blockMass_signShiftCore5 X H t₀ K K.2.1 (hgate ·)
  have hMassPlus :
      X.blockMass H' K' (insert (X.optKeyOf K' (shiftSignVector5 t₀ t)) K'.2.1) =
        X.blockMass H K (insert (X.optKeyOf K t) K.2.1) := by
    calc
      X.blockMass H' K' (insert (X.optKeyOf K' (shiftSignVector5 t₀ t)) K'.2.1) =
          X.blockMass H' K' ((insert (X.optKeyOf K t) K.2.1).image e) := by rw [hPlus]
      _ = X.blockMass H K (insert (X.optKeyOf K t) K.2.1) :=
        blockMass_signShiftCore5 X H t₀ K (insert (X.optKeyOf K t) K.2.1) (hgate ·)
  have hTrue : X.trueBlock H'.1 K' = X.trueBlock H.1 K := by
    change X.trueBlock H.1 K' = X.trueBlock H.1 K
    rfl
  have hGate : X.blockGate H'.1 K' (X.trueBlock H'.1 K') ↔
      X.blockGate H.1 K (X.trueBlock H.1 K) := by
    rw [hTrue]
    exact Iff.of_eq (hgate (X.trueBlock H.1 K))
  unfold Setup5.optFail
  constructor
  · rintro ⟨hg, hm⟩
    refine ⟨hGate.mp hg, ?_⟩
    rw [hMassPlus, hMass] at hm
    exact hm
  · rintro ⟨hg, hm⟩
    refine ⟨hGate.mpr hg, ?_⟩
    rw [← hMassPlus, ← hMass] at hm
    exact hm

theorem optFailPr_signShiftHigh5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t₀ t : CubeVertex (X.p.m n)) (K : X.Ty)
    (hnone : K.2.2 = none)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    (X.hiddenLaw b).pr (fun U => X.optFail (b, hiddenSignShift5 X t₀ U)
      (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) =
    (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) := by
  classical
  let P := X.hiddenLaw b
  let A : X.Hidden → Prop := fun U =>
    X.optFail (b, U) (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)
  have hMap := map_pr_equiv5 P (hiddenSignShift5 X t₀) A
  rw [hiddenLaw_map_signShift5 X b t₀] at hMap
  have hEvent (U : X.Hidden) : A (hiddenSignShift5 X t₀ U) ↔ X.optFail (b, U) K t := by
    simpa [A, signShiftHistory5] using optFail_signShiftHigh5 X (b, U) t₀ t K hnone hHigh
  calc
    (X.hiddenLaw b).pr (fun U => X.optFail (b, hiddenSignShift5 X t₀ U)
        (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) = P.pr A := hMap.symm
    _ = P.pr (fun U => A (hiddenSignShift5 X t₀ U)) := hMap
    _ = (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) := pr_congr5 P _ _ hEvent

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

theorem step1Fail_signShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (ℓ : X.Key) :
    X.step1Fail b (signShiftKey5 X t ℓ)
        (signShiftType5 X t K).1.1
        (X.p.typeSegs n (signShiftType5 X t K)) ↔
      X.step1Fail b ℓ K.1.1 (X.p.typeSegs n K) := by
  rw [signShiftType5_center, signShiftType5_segs]
  exact (Setup5.step1Fail_irrel_sign5 X b ℓ (signShiftKey5 X t ℓ) K.1.1
    (X.p.typeSegs n K) (signShiftKey5_coarse X t ℓ).symm
    (signShiftKey5_level X t ℓ).symm).symm

theorem capFail_signShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    X.capFail b (signShiftKey5 X t ℓ) ↔ X.capFail b ℓ := by
  exact (Setup5.capFail_irrel_sign5 X b ℓ (signShiftKey5 X t ℓ)
    (signShiftKey5_coarse X t ℓ).symm (signShiftKey5_level X t ℓ).symm).symm

theorem step1AlarmPr_signShift5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) (ℓ : X.Key) :
    (X.coarseLaw v).pr (fun c =>
      X.step1Fail (v, c) (signShiftKey5 X t ℓ)
        (signShiftType5 X t K).1.1
        (X.p.typeSegs n (signShiftType5 X t K))) =
    (X.coarseLaw v).pr (fun c => X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K)) := by
  apply pr_congr5
  intro c
  exact step1Fail_signShift5 X (v, c) t K ℓ

theorem capAlarmPr_signShift5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t : CubeVertex (X.p.m n)) (ℓ : X.Key) :
    (X.coarseLaw v).pr (fun c => X.capFail (v, c) (signShiftKey5 X t ℓ)) =
    (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := by
  apply pr_congr5
  intro c
  exact capFail_signShift5 X (v, c) t ℓ

theorem step2KeyLawPr_signShiftLow5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    (X.keyLawAt v).pr (fun cu =>
      X.step2Fail ((v, cu.1), hiddenSignShift5 X t cu.2) (signShiftType5 X t K)) =
    (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) := by
  classical
  have hleft : (X.keyLawAt v).pr (fun cu =>
      X.step2Fail ((v, cu.1), hiddenSignShift5 X t cu.2) (signShiftType5 X t K)) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr (fun U =>
        X.step2Fail ((v, c), hiddenSignShift5 X t U) (signShiftType5 X t K))) := by
    simpa [Setup5.keyLawAt] using bind_pr5 (X.coarseLaw v)
      (fun c => X.hiddenLaw (v, c))
      (fun c U => X.step2Fail ((v, c), hiddenSignShift5 X t U) (signShiftType5 X t K))
  have hright : (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr
        (fun U => X.step2Fail ((v, c), U) K)) := by
    simpa [Setup5.keyLawAt] using bind_pr5 (X.coarseLaw v)
      (fun c => X.hiddenLaw (v, c)) (fun c U => X.step2Fail ((v, c), U) K)
  have hfun : (fun c => (X.hiddenLaw (v, c)).pr (fun U =>
      X.step2Fail ((v, c), hiddenSignShift5 X t U) (signShiftType5 X t K))) =
      (fun c => (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K)) := by
    funext c
    exact step2FailPr_signShiftLow5 X (v, c) t K hlevel
  calc
    (X.keyLawAt v).pr (fun cu =>
        X.step2Fail ((v, cu.1), hiddenSignShift5 X t cu.2) (signShiftType5 X t K)) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr (fun U =>
        X.step2Fail ((v, c), hiddenSignShift5 X t U) (signShiftType5 X t K))) := hleft
    _ = (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr
        (fun U => X.step2Fail ((v, c), U) K)) := by rw [hfun]
    _ = (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) := hright.symm

theorem optKeyLawPr_signShiftHigh5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t₀ t : CubeVertex (X.p.m n)) (K : X.Ty) (hnone : K.2.2 = none)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    (X.keyLawAt v).pr (fun cu =>
      X.optFail ((v, cu.1), hiddenSignShift5 X t₀ cu.2)
        (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) =
    (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) := by
  classical
  have hleft : (X.keyLawAt v).pr (fun cu =>
      X.optFail ((v, cu.1), hiddenSignShift5 X t₀ cu.2)
        (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr (fun U =>
        X.optFail ((v, c), hiddenSignShift5 X t₀ U)
          (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t))) := by
    simpa [Setup5.keyLawAt] using bind_pr5 (X.coarseLaw v)
      (fun c => X.hiddenLaw (v, c))
      (fun c U => X.optFail ((v, c), hiddenSignShift5 X t₀ U)
        (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t))
  have hright : (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr
        (fun U => X.optFail ((v, c), U) K t)) := by
    simpa [Setup5.keyLawAt] using bind_pr5 (X.coarseLaw v)
      (fun c => X.hiddenLaw (v, c)) (fun c U => X.optFail ((v, c), U) K t)
  have hfun : (fun c => (X.hiddenLaw (v, c)).pr (fun U =>
      X.optFail ((v, c), hiddenSignShift5 X t₀ U) (signShiftType5 X t₀ K)
        (shiftSignVector5 t₀ t))) =
      (fun c => (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t)) := by
    funext c
    exact optFailPr_signShiftHigh5 X (v, c) t₀ t K hnone hHigh
  calc
    (X.keyLawAt v).pr (fun cu =>
        X.optFail ((v, cu.1), hiddenSignShift5 X t₀ cu.2)
          (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr (fun U =>
        X.optFail ((v, c), hiddenSignShift5 X t₀ U)
          (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t))) := hleft
    _ = (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr
        (fun U => X.optFail ((v, c), U) K t)) := by rw [hfun]
    _ = (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) := hright.symm

theorem keyLawPr_hiddenSignShift5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t : CubeVertex (X.p.m n)) (A : X.Coarse → X.Hidden → Prop) :
    (X.keyLawAt v).pr (fun cu => A cu.1 (hiddenSignShift5 X t cu.2)) =
      (X.keyLawAt v).pr (fun cu => A cu.1 cu.2) := by
  classical
  have hleft : (X.keyLawAt v).pr (fun cu => A cu.1 (hiddenSignShift5 X t cu.2)) =
      (X.coarseLaw v).expect (fun c =>
        (X.hiddenLaw (v, c)).pr (fun U => A c (hiddenSignShift5 X t U))) := by
    simpa [Setup5.keyLawAt] using bind_pr5 (X.coarseLaw v)
      (fun c => X.hiddenLaw (v, c)) (fun c U => A c (hiddenSignShift5 X t U))
  have hright : (X.keyLawAt v).pr (fun cu => A cu.1 cu.2) =
      (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr (A c)) := by
    simpa [Setup5.keyLawAt] using bind_pr5 (X.coarseLaw v)
      (fun c => X.hiddenLaw (v, c)) (fun c U => A c U)
  have hfun : (fun c => (X.hiddenLaw (v, c)).pr (fun U => A c (hiddenSignShift5 X t U))) =
      (fun c => (X.hiddenLaw (v, c)).pr (A c)) := by
    funext c
    let P := X.hiddenLaw (v, c)
    have hmap := map_pr_equiv5 P (hiddenSignShift5 X t) (A c)
    rw [hiddenLaw_map_signShift5 X (v, c) t] at hmap
    exact hmap.symm
  calc
    (X.keyLawAt v).pr (fun cu => A cu.1 (hiddenSignShift5 X t cu.2)) =
      (X.coarseLaw v).expect (fun c =>
        (X.hiddenLaw (v, c)).pr (fun U => A c (hiddenSignShift5 X t U))) := hleft
    _ = (X.coarseLaw v).expect (fun c => (X.hiddenLaw (v, c)).pr (A c)) := by rw [hfun]
    _ = (X.keyLawAt v).pr (fun cu => A cu.1 cu.2) := hright.symm

theorem hiddenLawPr_hiddenSignShift5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (A : X.Hidden → Prop) :
    (X.hiddenLaw b).pr (fun U => A (hiddenSignShift5 X t U)) =
      (X.hiddenLaw b).pr A := by
  classical
  let P := X.hiddenLaw b
  have hmap := map_pr_equiv5 P (hiddenSignShift5 X t) A
  rw [hiddenLaw_map_signShift5 X b t] at hmap
  exact hmap.symm

theorem step2FailPr_signShiftLowSimple5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) (signShiftType5 X t K)) =
      (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) := by
  calc
    (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) (signShiftType5 X t K)) =
      (X.hiddenLaw b).pr (fun U => X.step2Fail (b, hiddenSignShift5 X t U)
        (signShiftType5 X t K)) := by
          symm
          exact hiddenLawPr_hiddenSignShift5 X b t
            (fun U => X.step2Fail (b, U) (signShiftType5 X t K))
    _ = (X.hiddenLaw b).pr (fun U => X.step2Fail (b, U) K) :=
      step2FailPr_signShiftLow5 X b t K hlevel

theorem optFailPr_signShiftHighSimple5 (X : Setup5 γ K' χ n N E G) (b : X.Base)
    (t₀ t : CubeVertex (X.p.m n)) (K : X.Ty) (hnone : K.2.2 = none)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    (X.hiddenLaw b).pr (fun U => X.optFail (b, U) (signShiftType5 X t₀ K)
      (shiftSignVector5 t₀ t)) =
      (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) := by
  calc
    (X.hiddenLaw b).pr (fun U => X.optFail (b, U) (signShiftType5 X t₀ K)
        (shiftSignVector5 t₀ t)) =
      (X.hiddenLaw b).pr (fun U => X.optFail (b, hiddenSignShift5 X t₀ U)
        (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) := by
          symm
          exact hiddenLawPr_hiddenSignShift5 X b t₀
            (fun U => X.optFail (b, U) (signShiftType5 X t₀ K)
              (shiftSignVector5 t₀ t))
    _ = (X.hiddenLaw b).pr (fun U => X.optFail (b, U) K t) :=
      optFailPr_signShiftHigh5 X b t₀ t K hnone hHigh

theorem step2KeyLawPr_signShiftLowSimple5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t : CubeVertex (X.p.m n)) (K : X.Ty) {j : Fin (X.p.J n + 1)}
    (hlevel : K.2.2 = some j) :
    (X.keyLawAt v).pr (fun cu =>
      X.step2Fail ((v, cu.1), cu.2) (signShiftType5 X t K)) =
      (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) := by
  calc
    (X.keyLawAt v).pr (fun cu =>
        X.step2Fail ((v, cu.1), cu.2) (signShiftType5 X t K)) =
      (X.keyLawAt v).pr (fun cu =>
        X.step2Fail ((v, cu.1), hiddenSignShift5 X t cu.2) (signShiftType5 X t K)) := by
          symm
          exact keyLawPr_hiddenSignShift5 X v t
            (fun c U => X.step2Fail ((v, c), U) (signShiftType5 X t K))
    _ = (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K) :=
      step2KeyLawPr_signShiftLow5 X v t K hlevel

theorem optKeyLawPr_signShiftHighSimple5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (t₀ t : CubeVertex (X.p.m n)) (K : X.Ty) (hnone : K.2.2 = none)
    (hHigh : ∀ ℓ ∈ K.2.1, ∃ i : CoarseKey5 n, ℓ = .inr i) :
    (X.keyLawAt v).pr (fun cu =>
      X.optFail ((v, cu.1), cu.2) (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) =
      (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) := by
  calc
    (X.keyLawAt v).pr (fun cu =>
        X.optFail ((v, cu.1), cu.2) (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) =
      (X.keyLawAt v).pr (fun cu =>
        X.optFail ((v, cu.1), hiddenSignShift5 X t₀ cu.2)
          (signShiftType5 X t₀ K) (shiftSignVector5 t₀ t)) := by
          symm
          exact keyLawPr_hiddenSignShift5 X v t₀
            (fun c U => X.optFail ((v, c), U) (signShiftType5 X t₀ K)
              (shiftSignVector5 t₀ t))
    _ = (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K t) :=
      optKeyLawPr_signShiftHigh5 X v t₀ t K hnone hHigh

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

def stage2GroupScope5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    Finset (BinVector5 n) :=
  nearBinVectors2_5 q.1

def stage2GroupIndicesTouching5 (X : Setup5 γ K' χ n N E G)
    (B : Finset (BinVector5 n)) : Finset (CoarseKey5 n) :=
  Finset.univ.filter fun q => ¬ Disjoint (stage2GroupScope5 X q) B

theorem stage2GroupIndicesTouching_card_le5 (X : Setup5 γ K' χ n N E G)
    (B : Finset (BinVector5 n)) :
    (stage2GroupIndicesTouching5 X B).card ≤
      B.card * (2 * (3 ^ coarseChunkCount5) ^ 2) := by
  classical
  let F : BinVector5 n → Finset (CoarseKey5 n) := nearCoarseKeys2_5
  have hsubset : stage2GroupIndicesTouching5 X B ⊆ B.biUnion F := by
    intro q hq
    have hnot : ¬ Disjoint (stage2GroupScope5 X q) B :=
      (Finset.mem_filter.mp hq).2
    rw [Finset.disjoint_left] at hnot
    push_neg at hnot
    obtain ⟨w, hwq, hwB⟩ := hnot
    have hcenter : q.1 ∈ nearCoarseKeys2_5 w := by
      exact Finset.mem_product.mpr
        ⟨nearBinVectors2_mem_symm5 q.1 w (by simpa [stage2GroupScope5] using hwq),
          Finset.mem_univ _⟩
    exact Finset.mem_biUnion.mpr ⟨w, hwB, by simpa [F] using hcenter⟩
  calc
    (stage2GroupIndicesTouching5 X B).card ≤ (B.biUnion F).card := Finset.card_le_card hsubset
    _ ≤ ∑ w ∈ B, (F w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ B, 2 * (3 ^ coarseChunkCount5) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      exact nearCoarseKeys2_card_le5 w
    _ = B.card * (2 * (3 ^ coarseChunkCount5) ^ 2) := by simp

def stage2GroupScopeCardBound5 : ℕ := (3 ^ coarseChunkCount5) ^ 2
def stage2GroupTouchPerBin5 : ℕ := 2 * stage2GroupScopeCardBound5
def stage2GroupDegreeBound5 : ℕ := stage2GroupScopeCardBound5 * stage2GroupTouchPerBin5

theorem stage2GroupScope_card_le5 (X : Setup5 γ K' χ n N E G) (q : CoarseKey5 n) :
    (stage2GroupScope5 X q).card ≤ stage2GroupScopeCardBound5 := by
  simpa [stage2GroupScope5, stage2GroupScopeCardBound5] using nearBinVectors2_card_le5 q.1

theorem stage2GroupNeighbors_card_le5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) :
    (Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q)).card ≤
      stage2GroupDegreeBound5 := by
  classical
  let B := stage2GroupScope5 X q
  have hsubset : Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q) ⊆
      stage2GroupIndicesTouching5 X B := by
    intro q' hq'
    have hAdj := (Finset.mem_filter.mp hq').2
    have htouch : ¬ Disjoint (stage2GroupScope5 X q') B := by
      intro hd
      exact hAdj.2 hd.symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htouch⟩
  calc
    (Finset.univ.filter (LocalAdj5 (stage2GroupScope5 X) q)).card ≤
        (stage2GroupIndicesTouching5 X B).card := Finset.card_le_card hsubset
    _ ≤ B.card * stage2GroupTouchPerBin5 := by
      simpa [B, stage2GroupTouchPerBin5] using stage2GroupIndicesTouching_card_le5 X B
    _ ≤ stage2GroupDegreeBound5 := by
      exact Nat.mul_le_mul_right _ (stage2GroupScope_card_le5 X q)

theorem exp_neg_two_mul_le_one_sub5 (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hden : 0 < 1 + 2 * x := by positivity
  have hExp : 1 + 2 * x ≤ Real.exp (2 * x) := Real.add_one_le_exp _
  have hInv : (Real.exp (2 * x))⁻¹ ≤ (1 + 2 * x)⁻¹ :=
    one_div_le_one_div_of_le hden hExp
  have hpoly : 1 ≤ (1 - x) * (1 + 2 * x) := by nlinarith
  have hfrac : (1 + 2 * x)⁻¹ ≤ 1 - x := by
    apply (div_le_iff₀ hden).2
    nlinarith [hpoly]
  calc
    Real.exp (-2 * x) = (Real.exp (2 * x))⁻¹ := by rw [Real.exp_neg]
    _ ≤ (1 + 2 * x)⁻¹ := hInv
    _ ≤ 1 - x := hfrac

theorem stage2GroupFactor_le5 (X : Setup5 γ K' χ n N E G)
    (B : Finset (BinVector5 n)) (b : ℝ) (hb0 : 0 ≤ b)
    (hbsmall : 2 * b ≤ Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ))) :
    (∏ q ∈ Finset.univ.filter (fun q : CoarseKey5 n =>
      ¬ Disjoint (stage2GroupScope5 X q) B), (1 - 2 * b))⁻¹ ≤ (2 : ℝ) ^ B.card := by
  classical
  let S := Finset.univ.filter (fun q : CoarseKey5 n =>
    ¬ Disjoint (stage2GroupScope5 X q) B)
  let x := 2 * b
  have hCpos : 0 < (stage2GroupTouchPerBin5 : ℝ) := by
    dsimp [stage2GroupTouchPerBin5]
    positivity
  have hCge : (2 : ℝ) ≤ (stage2GroupTouchPerBin5 : ℝ) := by
    dsimp [stage2GroupTouchPerBin5]
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hmaxhalf : Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (stage2GroupTouchPerBin5 : ℝ))).2
    nlinarith [hlog2le, hCge]
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    linarith [hbsmall, hmaxhalf]
  have htouch : S.card ≤ B.card * stage2GroupTouchPerBin5 := by
    simpa [S] using stage2GroupIndicesTouching_card_le5 X B
  have htouchR : (S.card : ℝ) ≤ (B.card * stage2GroupTouchPerBin5 : ℕ) := by
    exact_mod_cast htouch
  have hlogbound : 2 * x ≤ Real.log 2 / (stage2GroupTouchPerBin5 : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hbsmall (by norm_num : (0 : ℝ) ≤ 2)
    dsimp [x] at hmul ⊢
    calc
      2 * (2 * b) ≤ 2 * (Real.log 2 / (2 * (stage2GroupTouchPerBin5 : ℝ))) := hmul
      _ = Real.log 2 / (stage2GroupTouchPerBin5 : ℝ) := by
        field_simp [ne_of_gt hCpos]
        ring
  have hsumx : 2 * x * (S.card : ℝ) ≤ Real.log 2 * (B.card : ℝ) := by
    have hfirst := mul_le_mul_of_nonneg_right hlogbound (Nat.cast_nonneg S.card)
    have hsecond := mul_le_mul_of_nonneg_left htouchR
      (div_nonneg hlog2.le hCpos.le)
    calc
      2 * x * (S.card : ℝ) ≤
          (Real.log 2 / (stage2GroupTouchPerBin5 : ℝ)) * (S.card : ℝ) := hfirst
      _ ≤ (Real.log 2 / (stage2GroupTouchPerBin5 : ℝ)) *
            (B.card * stage2GroupTouchPerBin5 : ℕ) := hsecond
      _ = Real.log 2 * (B.card : ℝ) := by field_simp [ne_of_gt hCpos]
  have hsingle : Real.exp (-2 * x) ≤ 1 - x := exp_neg_two_mul_le_one_sub5 x hx0 hxhalf
  have hpow : (Real.exp (-2 * x)) ^ S.card ≤ (1 - x) ^ S.card :=
    pow_le_pow_left₀ (Real.exp_nonneg _) hsingle _
  have hexpPow : (Real.exp (-2 * x)) ^ S.card =
      Real.exp (-2 * x * (S.card : ℝ)) := by
    calc
      (Real.exp (-2 * x)) ^ S.card = (Real.exp (-2 * x)) ^ (S.card : ℝ) := by
        rw [Real.rpow_natCast]
      _ = Real.exp ((-2 * x) * (S.card : ℝ)) := (Real.exp_mul _ _).symm
  have hprod : Real.exp (-2 * x * (S.card : ℝ)) ≤
      ∏ q ∈ S, (1 - 2 * b) := by
    calc
      Real.exp (-2 * x * (S.card : ℝ)) = (Real.exp (-2 * x)) ^ S.card := hexpPow.symm
      _ ≤ (1 - x) ^ S.card := hpow
      _ = ∏ q ∈ S, (1 - 2 * b) := by simp [S, x]
  have hExpPow : Real.exp (-Real.log 2 * (B.card : ℝ)) =
      1 / (2 : ℝ) ^ B.card := by
    calc
      Real.exp (-Real.log 2 * (B.card : ℝ)) =
          Real.exp ((B.card : ℝ) * (-Real.log 2)) := by congr 1; ring
      _ = (Real.exp (-Real.log 2)) ^ B.card := by
        simpa only [Real.rpow_natCast] using (Real.exp_mul (-Real.log 2) (B.card : ℝ)).symm
      _ = 1 / (2 : ℝ) ^ B.card := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        simp [one_div, inv_pow]
  have hProdLower : 1 / (2 : ℝ) ^ B.card ≤ ∏ q ∈ S, (1 - 2 * b) := by
    calc
      1 / (2 : ℝ) ^ B.card = Real.exp (-Real.log 2 * (B.card : ℝ)) := hExpPow.symm
      _ ≤ Real.exp (-2 * x * (S.card : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [hsumx])
      _ ≤ ∏ q ∈ S, (1 - 2 * b) := hprod
  have hprodPos : 0 < ∏ q ∈ S, (1 - 2 * b) :=
    lt_of_lt_of_le (by positivity) hProdLower
  have hmul : 1 ≤ (∏ q ∈ S, (1 - 2 * b)) * (2 : ℝ) ^ B.card := by
    calc
      1 = (1 / (2 : ℝ) ^ B.card) * (2 : ℝ) ^ B.card := by field_simp
      _ ≤ (∏ q ∈ S, (1 - 2 * b)) * (2 : ℝ) ^ B.card :=
        mul_le_mul_of_nonneg_right hProdLower (by positivity)
  have hinv : (∏ q ∈ S, (1 - 2 * b))⁻¹ ≤ (2 : ℝ) ^ B.card :=
    (inv_le_iff_one_le_mul₀' hprodPos).2 hmul
  simpa [S] using hinv

theorem binList_subset_stage2GroupScope5 (X : Setup5 γ K' χ n N E G)
    (q i : CoarseKey5 n) (hi : i ∈ nearCoarseKeys5 q.1) :
    binList5 i ⊆ stage2GroupScope5 X q := by
  intro w hw
  have hvec : i.1 ∈ nearBinVectors5 q.1 := by
    have hi' : i ∈ (nearBinVectors5 q.1).product Finset.univ := by
      simpa [nearCoarseKeys5] using hi
    exact (Finset.mem_product.mp hi').1
  exact Finset.mem_biUnion.mpr ⟨i.1, hvec, binList_mem_nearBinVectors5 i w hw⟩

theorem blockLocalBins_subset_stage2GroupScope5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hcenter : K.1 = q)
    (hkeys : ∀ ℓ ∈ K.2.1 ∪ X.gateKeys K, ℓ.coarse ∈ nearCoarseKeys5 q.1) :
    blockLocalBins5 X K K.2.1 ⊆ stage2GroupScope5 X q := by
  intro w hw
  simp only [blockLocalBins5, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_union] at hw
  rcases hw with hw | ⟨ℓ, hℓ, hw⟩
  · have hW : w = q.1 := by simpa [hcenter] using hw
    simpa [stage2GroupScope5, hW] using nearBinVectors2_self5 q.1
  · exact binList_subset_stage2GroupScope5 X q ℓ.coarse
      (hkeys ℓ (Finset.mem_union.mpr hℓ)) hw

theorem blockLocalBinsInsert_subset_stage2GroupScope5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (K : X.Ty) (hcenter : K.1 = q)
    (S : Finset X.Key)
    (hkeys : ∀ ℓ ∈ S ∪ X.gateKeys K, ℓ.coarse ∈ nearCoarseKeys5 q.1) :
    blockLocalBins5 X K S ⊆ stage2GroupScope5 X q := by
  intro w hw
  simp only [blockLocalBins5, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_union] at hw
  rcases hw with hw | ⟨ℓ, hℓ, hw⟩
  · have hW : w = q.1 := by simpa [hcenter] using hw
    simpa [stage2GroupScope5, hW] using nearBinVectors2_self5 q.1
  · exact binList_subset_stage2GroupScope5 X q ℓ.coarse
      (hkeys ℓ (Finset.mem_union.mpr hℓ)) hw

theorem stage2GroupAlarmScope_subset5 (X : Setup5 γ K' χ n N E G)
    (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) :
    stage2GroupAlarmScope5 X q i ⊆ stage2GroupScope5 X q := by
  cases i with
  | lowStep1 j p ℓ =>
      exact binList_subset_stage2GroupScope5 X q ℓ.1.coarse
        (stage2LowPatternAt_gateKeys_coarse5 X q j p ℓ.1 ℓ.2)
  | highStep1 p ℓ =>
      exact binList_subset_stage2GroupScope5 X q ℓ.1.coarse
        (stage2HighPatternAt_gateKeys_coarse5 X q p ℓ.1 ℓ.2)
  | lowCap j h =>
      exact binList_subset_stage2GroupScope5 X q q (coarseKey_mem_nearKeys5 q)
  | highCap h =>
      exact binList_subset_stage2GroupScope5 X q q (coarseKey_mem_nearKeys5 q)
  | lowStep2 j p =>
      apply blockLocalBins_subset_stage2GroupScope5 X q p.1 p.2.2.1
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hkey | hgate
      · exact lowTypeCandidates_keys_coarse5 X q default j p.1 p.2.1 ℓ hkey
      · exact stage2LowPatternAt_gateKeys_coarse5 X q j p ℓ hgate
  | highStep2 p =>
      apply blockLocalBins_subset_stage2GroupScope5 X q p.1 p.2.2.1
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hkey | hgate
      · exact highTypeCandidates_keys_coarse5 X q p.1 p.2.1 ℓ hkey
      · exact stage2HighPatternAt_gateKeys_coarse5 X q p ℓ hgate
  | highOptional p =>
      apply blockLocalBinsInsert_subset_stage2GroupScope5 X q p.1.1 p.1.2.2.1
        (insert (X.optKeyOf p.1.1 default) p.1.1.2.1)
      intro ℓ hℓ
      rcases Finset.mem_union.mp hℓ with hS | hgate
      · rcases Finset.mem_insert.mp hS with hopt | hkey
        · subst ℓ
          simpa [Setup5.optKeyOf, p.1.2.2.1] using coarseKey_mem_nearKeys5 q
        · exact highTypeCandidates_keys_coarse5 X q p.1.1 p.1.2.1 ℓ hkey
      · exact stage2HighPatternAt_gateKeys_coarse5 X q p.1 ℓ hgate

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

theorem stage2GroupAlarmPr_bound5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (hraw : Stage2RawBounds5 X v) (q : CoarseKey5 n) (i : Stage2GroupAlarm5 X q) :
    (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q i) ≤ stage2GroupAlarmBudget5 X q i := by
  classical
  cases i with
  | lowStep1 j p a =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      let K0 : X.Ty := X.g.evenType (X.p.J n) x
      let t : CubeVertex (X.p.m n) := X.g.sign x
      have hlevel0 : K0.2.2 = some j := by
        have h := p.2.2.2.1
        rw [hK, signShiftType5_level] at h
        exact h
      have hType : X.TypeOccurs K0 := ⟨x, hx, rfl⟩
      have hmemCanon : a.1 ∈ X.gateKeys (signShiftType5 X t K0) := by
        simpa [hK, K0, t] using a.2
      have hGate := gateKeys_signShiftLow5 X t K0 hlevel0
      rw [hGate] at hmemCanon
      obtain ⟨ℓ0, hℓ0, hℓ⟩ := Finset.mem_image.mp hmemCanon
      have hpr : (X.coarseLaw v).pr (fun c =>
          X.step1Fail (v, c) a.1 p.1.1.1 (X.p.typeSegs n p.1)) =
          (X.coarseLaw v).pr (fun c =>
            X.step1Fail (v, c) ℓ0 K0.1.1 (X.p.typeSegs n K0)) := by
        simpa [hK, K0, t, hℓ.symm, signShiftType5_segs] using
          step1AlarmPr_signShift5 X v t K0 ℓ0
      calc
        (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q (.lowStep1 j p a)) =
            (X.coarseLaw v).pr (fun c =>
              X.step1Fail (v, c) a.1 p.1.1.1 (X.p.typeSegs n p.1)) := rfl
        _ = (X.coarseLaw v).pr (fun c =>
              X.step1Fail (v, c) ℓ0 K0.1.1 (X.p.typeSegs n K0)) := hpr
        _ ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K0)) / 2) :=
          hraw.step1 K0 hType ℓ0 hℓ0
        _ = stage2GroupAlarmBudget5 X q (.lowStep1 j p a) := by
          simp [stage2GroupAlarmBudget5, hK, K0, signShiftType5_segs]
  | highStep1 p a =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      have hType : X.TypeOccurs p.1 := ⟨x, hx, hK.symm⟩
      exact hraw.step1 p.1 hType a.1 a.2
  | lowCap j hocc =>
      rcases hocc with ⟨ℓ, hℓ, t, hKey⟩
      have hlevel : ℓ.level = j.val := by
        calc
          ℓ.level = (signShiftKey5 X t ℓ).level := (signShiftKey5_level X t ℓ).symm
          _ = ((.inl (q, default, j) : X.Key)).level := congrArg (fun k : X.Key => k.level) hKey
          _ = j.val := rfl
      have hpr : (X.coarseLaw v).pr (fun c => X.capFail (v, c) (.inl (q, default, j))) =
          (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := by
        simpa [hKey.symm] using capAlarmPr_signShift5 X v t ℓ
      calc
        (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q (.lowCap j hocc)) =
            (X.coarseLaw v).pr (fun c => X.capFail (v, c) (.inl (q, default, j))) := rfl
        _ = (X.coarseLaw v).pr (fun c => X.capFail (v, c) ℓ) := hpr
        _ ≤ Real.exp (-(X.p.delta * (X.p.q0 * X.p.uSeg n (ℓ.level + 1))) / 2) :=
          hraw.cap ℓ hℓ
        _ = stage2GroupAlarmBudget5 X q (.lowCap j hocc) := by
          simp [stage2GroupAlarmBudget5, hlevel]
  | highCap hKey =>
      exact hraw.cap (.inr q) hKey
  | lowStep2 j p =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      let K0 : X.Ty := X.g.evenType (X.p.J n) x
      let t : CubeVertex (X.p.m n) := X.g.sign x
      have hlevel0 : K0.2.2 = some j := by
        have h := p.2.2.2.1
        rw [hK, signShiftType5_level] at h
        exact h
      have hType : X.TypeOccurs K0 := ⟨x, hx, rfl⟩
      have hEqPr := step2KeyLawPr_signShiftLowSimple5 X v t K0 hlevel0
      have hRawCanon : (X.keyLawAt v).pr (fun cu =>
          X.step2Fail ((v, cu.1), cu.2) p.1) ≤
          ((p.1.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2) := by
        calc
          (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) p.1) =
              (X.keyLawAt v).pr (fun cu => X.step2Fail ((v, cu.1), cu.2) K0) := by
                simpa [hK, K0, t] using hEqPr
          _ ≤ ((K0.2.1.card : ℝ) + 1) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K0)) / 2) :=
                hraw.step2 K0 hType
          _ = ((p.1.2.1.card : ℝ) + 1) *
              Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n p.1)) / 2) := by
                simp [hK, K0, signShiftType5_keys_card, signShiftType5_segs]
      exact step2AlarmProb_bound5 X v p.1 hRawCanon
  | highStep2 p =>
      rcases p.2.2.2.2 with ⟨x, hx, hK⟩
      have hType : X.TypeOccurs p.1 := ⟨x, hx, hK.symm⟩
      exact step2AlarmProb_bound5 X p.1 (hraw.step2 p.1 hType)
  | highOptional p =>
      rcases p.1.2.2.2.2 with ⟨x, hx, hK⟩
      rcases p.2 with ⟨t₀, hOpt⟩
      let K0 : X.Ty := p.1.1
      have hType : X.TypeOccurs K0 := ⟨x, hx, hK.symm⟩
      have hnone : K0.2.2 = none := optOccurs_high5 X K0 t₀ hOpt
      have hHigh := typeOccurs_highKeys5 X K0 hType hnone
      have hRawCanon : (X.keyLawAt v).pr (fun cu =>
          X.optFail ((v, cu.1), cu.2) K0 (default : CubeVertex (X.p.m n))) ≤
          Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 2) := by
        have hKfixed : signShiftType5 X t₀ K0 = K0 :=
          signShiftType5_eq_of_highKeys X t₀ K0 hHigh
        have hEqPr : (X.keyLawAt v).pr (fun cu =>
            X.optFail ((v, cu.1), cu.2) K0 (default : CubeVertex (X.p.m n))) =
            (X.keyLawAt v).pr (fun cu => X.optFail ((v, cu.1), cu.2) K0 t₀) := by
          simpa [hKfixed, shiftSignVector_self5] using
            optKeyLawPr_signShiftHighSimple5 X v t₀ t₀ K0 hnone hHigh
        rw [hEqPr]
        exact hraw.optional K0 t₀ hOpt
      exact optAlarmProb_bound5 X v K0 default hRawCanon

theorem stage2GroupBad_pr_le_budget5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (hraw : Stage2RawBounds5 X v) (q : CoarseKey5 n)
    (hm : 1 ≤ X.p.m n) (hJ : X.p.J n ≤ X.p.m n)
    (hK1 : 8 / X.p.delta ≤ X.p.K1) :
    (X.coarseLaw v).pr (stage2GroupBad5 X v q) ≤
      stage2GroupBudgetBound5 X (2 * 3 ^ coarseChunkCount5) := by
  classical
  calc
    (X.coarseLaw v).pr (stage2GroupBad5 X v q) ≤
        ∑ i : Stage2GroupAlarm5 X q,
          (X.coarseLaw v).pr (stage2GroupAlarmBad5 X v q i) := by
      simpa [stage2GroupBad5] using
        pr_exists_le_sum5 (X.coarseLaw v) (stage2GroupAlarmBad5 X v q)
    _ ≤ ∑ i : Stage2GroupAlarm5 X q, stage2GroupAlarmBudget5 X q i := by
      apply Finset.sum_le_sum
      intro i hi
      exact stage2GroupAlarmPr_bound5 X v hraw q i
    _ = ∑ a : Stage2GroupAlarmFlat5 X q, stage2GroupAlarmFlatBudget5 X q a :=
      stage2GroupAlarmBudget_sum_eq_flat5 X q
    _ ≤ stage2GroupBudgetBound5 X (2 * 3 ^ coarseChunkCount5) :=
      stage2GroupAlarmFlatBudget_sum_le5 X q hm hJ hK1

theorem stage2GroupBadOnPairs_pr5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (q : CoarseKey5 n) :
    (FinProb.pi (CoarsePairLaw5 X v)).pr (stage2GroupBadOnPairs5 X v q) =
      (X.coarseLaw v).pr (stage2GroupBad5 X v q) := by
  classical
  let P := FinProb.pi (CoarsePairLaw5 X v)
  let e := coarsePairEquiv5 X
  have hmap := map_pr_equiv5 P e (stage2GroupBad5 X v q)
  have hcoarse : X.coarseLaw v = FinProb.map P e := by
    simpa [P, e] using coarseLaw_eq_map_pi5 X v
  calc
    P.pr (stage2GroupBadOnPairs5 X v q) = (FinProb.map P e).pr (stage2GroupBad5 X v q) := by
      simpa [stage2GroupBadOnPairs5, e] using hmap.symm
    _ = (X.coarseLaw v).pr (stage2GroupBad5 X v q) := by rw [← hcoarse]

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

def stage2AlarmConclusion5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (ν : FinProb X.Coarse) : Prop :=
  (∀ c, ν.w c ≠ 0 → X.Step1Pass (v, c)) ∧
  (∀ c, ν.w c ≠ 0 → ∀ K, X.TypeOccurs K →
    (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
      ((K.2.1.card : ℝ) + 1) *
        Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4)) ∧
  (∀ c, ν.w c ≠ 0 → ∀ K t, X.OptOccurs K t →
    (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4)) ∧
  (∀ (B : Finset (BinVector5 n)) (f : X.Coarse → ℝ), (∀ c, 0 ≤ f c) →
    (∀ c c', (∀ w ∈ B, c.1 w = c'.1 w ∧ c.2 w = c'.2 w) → f c = f c') →
      ν.expect f ≤ 2 ^ B.card * (X.coarseLaw v).expect f) ∧
  ∀ c, ν.w c ≠ 0 → (X.coarseLaw v).w c ≠ 0

theorem stage2AlarmLLL_to_conclusion5 (X : Setup5 γ K' χ n N E G) (v : Fin N)
    (x : Stage2AlarmIndex5 X → ℝ)
    (hL : ProductLLLData5 (CoarsePairLaw5 X v) (stage2AlarmBadOnPairs5 X v)
      (stage2AlarmScope5 X) x)
    (hfactor : ∀ B : Finset (BinVector5 n),
      (∏ i ∈ Finset.univ.filter (fun i : Stage2AlarmIndex5 X =>
        ¬ Disjoint (stage2AlarmScope5 X i) B), (1 - x i))⁻¹ ≤ (2 : ℝ) ^ B.card) :
    ∃ ν : FinProb X.Coarse, stage2AlarmConclusion5 X v ν := by
  classical
  let e := coarsePairEquiv5 X
  let P := CoarsePairLaw5 X v
  obtain ⟨Q, hQbad, hQraw, hQexpect⟩ :=
    productAvoidanceLocalCompare5 P (stage2AlarmBadOnPairs5 X v)
      (stage2AlarmScope5 X) x hL
  let ν : FinProb X.Coarse := FinProb.map Q e
  have hsource (c : X.Coarse) (hc : ν.w c ≠ 0) : Q.w (e.symm c) ≠ 0 := by
    change (FinProb.map Q e).w c ≠ 0 at hc
    rw [map_equiv_weight5 Q e c] at hc
    exact hc
  have hgood (c : X.Coarse) (hc : ν.w c ≠ 0) (i : Stage2AlarmIndex5 X) :
      ¬ stage2AlarmBad5 X v i c := by
    have h := hQbad (e.symm c) (hsource c hc) i
    simpa [stage2AlarmBadOnPairs5, e] using h
  have hrawSupport : ∀ c, ν.w c ≠ 0 → (X.coarseLaw v).w c ≠ 0 := by
    intro c hc
    have hprod : (FinProb.pi P).w (e.symm c) ≠ 0 := hQraw (e.symm c) (hsource c hc)
    have heq : (X.coarseLaw v).w c = (FinProb.pi P).w (e.symm c) := by
      calc
        (X.coarseLaw v).w c = (FinProb.map (FinProb.pi P) e).w c := by
          rw [coarseLaw_eq_map_pi5 X v]
        _ = (FinProb.pi P).w (e.symm c) := map_equiv_weight5 (FinProb.pi P) e c
    rw [heq]
    exact hprod
  refine ⟨ν, ?_⟩
  unfold stage2AlarmConclusion5
  refine ⟨?_, ?_⟩
  · intro c hc
    constructor
    · intro K hK ℓ hℓ
      let a : Stage2Step1Alarm5 X := ⟨⟨K, hK⟩, ⟨ℓ, hℓ⟩⟩
      have h := hgood c hc (Sum.inl a)
      change ¬ X.step1Fail (v, c) ℓ K.1.1 (X.p.typeSegs n K) at h
      exact h
    · intro ℓ hℓ
      let a : Stage2CapAlarm5 X := ⟨ℓ, hℓ⟩
      have h := hgood c hc (Sum.inr (Sum.inl a))
      change ¬ X.capFail (v, c) ℓ at h
      exact h
  · refine ⟨?_, ?_⟩
    · intro c hc K hK
      let a : Stage2TypeOcc5 X := ⟨K, hK⟩
      have h := hgood c hc (Sum.inr (Sum.inr (Sum.inl a)))
      change ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) <
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K)) at h
      calc
        (X.hiddenLaw (v, c)).pr (fun U => X.step2Fail ((v, c), U) K) ≤
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := le_of_not_gt h
        _ = 1 * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by ring
        _ ≤ ((K.2.1.card : ℝ) + 1) *
            Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K)) / 4) := by
          have hcard0 : (0 : ℝ) ≤ (K.2.1.card : ℝ) := by positivity
          have hcard : (1 : ℝ) ≤ (K.2.1.card : ℝ) + 1 := by linarith
          exact mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    · refine ⟨?_, ?_⟩
      · intro c hc K t hKt
        have hK : X.TypeOccurs K := by
          rcases hKt with ⟨z, hz, htype, hopt⟩
          exact ⟨z, hz, htype⟩
        let a : Stage2OptAlarm5 X := ⟨(K, t), ⟨hK, hKt⟩⟩
        have h := hgood c hc (Sum.inr (Sum.inr (Sum.inr a)))
        change ¬ (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)) / 4) <
          (X.hiddenLaw (v, c)).pr (fun U => X.optFail ((v, c), U) K t)) at h
        exact le_of_not_gt h
      · refine ⟨?_, hrawSupport⟩
        intro B f hf hdep
        let Φ : (BinVector5 n → Fin N × X.Stream) → ℝ := fun ω => f (e ω)
        have hΦ : ∀ ω, 0 ≤ Φ ω := fun ω => hf (e ω)
        have hΦdep : FinProb.DependsOn Φ B := by
          intro ω ω' heq
          apply hdep (e ω) (e ω')
          intro w hw
          have hp := heq w hw
          exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
        have hmapν : ν.expect f = Q.expect Φ := by
          simpa [ν, Φ, e] using (FinProb.map_expect Q e f)
        have hmapCoarse : X.coarseLaw v = FinProb.map (FinProb.pi P) e := by
          simpa [P, e] using coarseLaw_eq_map_pi5 X v
        have hmapRaw : (X.coarseLaw v).expect f = (FinProb.pi P).expect Φ := by
          rw [hmapCoarse]
          simpa [Φ] using (FinProb.map_expect (FinProb.pi P) e f)
        have hRawNonneg : 0 ≤ (FinProb.pi P).expect Φ := by
          unfold FinProb.expect
          apply Finset.sum_nonneg
          intro ω hω
          exact mul_nonneg ((FinProb.pi P).nonneg ω) (hΦ ω)
        calc
          ν.expect f = Q.expect Φ := hmapν
          _ ≤ (∏ i ∈ Finset.univ.filter (fun i =>
                ¬ Disjoint (stage2AlarmScope5 X i) B), (1 - x i))⁻¹ *
                (FinProb.pi P).expect Φ := hQexpect B Φ hΦ hΦdep
          _ ≤ (2 : ℝ) ^ B.card * (FinProb.pi P).expect Φ :=
            mul_le_mul_of_nonneg_right (hfactor B) hRawNonneg
          _ = (2 : ℝ) ^ B.card * (X.coarseLaw v).expect f := by rw [← hmapRaw]

end

end HypercubeRamsey.Lane_q_s05_h23
