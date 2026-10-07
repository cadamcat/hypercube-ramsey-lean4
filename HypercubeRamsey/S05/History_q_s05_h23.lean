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
