import HypercubeRamsey.S05.Centres_sol_s05_centres_records

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical
open scoped BigOperators
set_option maxHeartbeats 400000
noncomputable section

def DisjointFamily {Id : Type*} [DecidableEq Id] (M : Finset (Finset Id)) : Prop :=
  ∀ A ∈ M, ∀ B ∈ M, A ≠ B → Disjoint A B

theorem maximal_disjoint_family {Id : Type*} [DecidableEq Id] (F : Finset (Finset Id)) :
    ∃ M : Finset (Finset Id), M ⊆ F ∧ DisjointFamily M ∧
      ∀ S ∈ F, S.Nonempty → (S ∩ M.biUnion id).Nonempty := by
  classical
  let candidates : Finset (Finset (Finset Id)) := F.powerset.filter DisjointFamily
  have hne : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset F), ?_⟩⟩
    simp [DisjointFamily]
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hsub : M ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
  have hpair : DisjointFamily M := (Finset.mem_filter.mp hM).2
  refine ⟨M, hsub, hpair, ?_⟩
  intro S hS hSnon
  by_contra hn
  have hdis : Disjoint S (M.biUnion id) := by
    apply Finset.disjoint_left.mpr
    intro i hi him
    exact hn ⟨i, Finset.mem_inter.mpr ⟨hi, him⟩⟩
  have hnot : S ∉ M := by
    intro hm
    obtain ⟨i, hi⟩ := hSnon
    exact Finset.disjoint_left.mp hdis hi (Finset.mem_biUnion.mpr ⟨S, hm, hi⟩)
  have hdisM (A : Finset Id) (hA : A ∈ M) : Disjoint S A := by
    apply Finset.disjoint_left.mpr
    intro i hi hiA
    exact Finset.disjoint_left.mp hdis hi (Finset.mem_biUnion.mpr ⟨A, hA, hiA⟩)
  have hpair' : DisjointFamily (insert S M) := by
    intro A hA0 B hB0 hAB
    rcases Finset.mem_insert.mp hA0 with hAS | hAM
    · subst A
      rcases Finset.mem_insert.mp hB0 with hBS | hBM
      · subst B
        exact (hAB rfl).elim
      · exact hdisM B hBM
    · rcases Finset.mem_insert.mp hB0 with hBS | hBM
      · subst B
        exact (hdisM A hAM).symm
      · exact hpair A hAM B hBM hAB
  have hnew : insert S M ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, hpair'⟩
    exact Finset.insert_subset hS hsub
  have hcard := hmax (insert S M) hnew
  rw [Finset.card_insert_of_notMem hnot] at hcard
  omega

def markingFamily {Id : Type*} [DecidableEq Id] (F : Finset (Finset Id)) : Finset (Finset Id) :=
  Classical.choose (maximal_disjoint_family F)

theorem markingFamily_spec {Id : Type*} [DecidableEq Id] (F : Finset (Finset Id)) :
    markingFamily F ⊆ F ∧ DisjointFamily (markingFamily F) ∧
      ∀ S ∈ F, S.Nonempty → (S ∩ (markingFamily F).biUnion id).Nonempty :=
  Classical.choose_spec (maximal_disjoint_family F)

theorem marking_card_bound {Id : Type*} [DecidableEq Id] (F : Finset (Finset Id))
    (k T : ℕ) (hsmall : (markingFamily F).card ≤ k)
    (hsize : ∀ S ∈ F, S.card ≤ T) : ((markingFamily F).biUnion id).card ≤ k * T := by
  calc
    _ ≤ ∑ S ∈ markingFamily F, S.card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ markingFamily F, T := Finset.sum_le_sum fun S hS =>
      hsize S ((markingFamily_spec F).1 hS)
    _ = (markingFamily F).card * T := by simp
    _ ≤ k * T := Nat.mul_le_mul_right T hsmall

theorem disjoint_failure_union
    {Id Rec : Type*} [Fintype Id] [DecidableEq Id] [Fintype Rec]
    {A : Id → Type*} [∀ i, Fintype (A i)]
    (P : ∀ i, FinProb (A i)) (ids : Rec → Finset Id) (fail : Rec → (∀ i, A i) → Prop)
    (hlocal : ∀ r, FinProb.DependsOn (fail r) (ids r)) (ε : ℝ) (hε : 0 ≤ ε)
    (hfail : ∀ r, (FinProb.pi P).pr (fail r) ≤ ε) (q : ℕ) :
    (FinProb.pi P).pr (fun ω => ∃ s : Fin q → Rec,
      (∀ i j, i ≠ j → Disjoint (ids (s i)) (ids (s j))) ∧ ∀ i, fail (s i) ω) ≤
      (Fintype.card Rec : ℝ) ^ q * ε ^ q := by
  classical
  let μ := FinProb.pi P
  let Z : Rec → (∀ i, A i) → ℝ := fun r ω => if fail r ω then 1 else 0
  have hZlocal : ∀ r, FinProb.DependsOn (Z r) (ids r) := by
    intro r ω ω' hω
    simp only [Z, hlocal r ω ω' hω]
  have hpr (r : Rec) : μ.expect (Z r) = μ.pr (fail r) := by
    simp [FinProb.expect, FinProb.pr, Z, mul_ite]
  have hnonneg (r : Rec) : 0 ≤ μ.expect (Z r) := by
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω)
      (by dsimp [Z]; split_ifs <;> norm_num)
  have hEach (s : Fin q → Rec) : μ.pr (fun ω =>
      (∀ i j, i ≠ j → Disjoint (ids (s i)) (ids (s j))) ∧ ∀ i, fail (s i) ω) ≤ ε ^ q := by
    by_cases hsep : ∀ i j, i ≠ j → Disjoint (ids (s i)) (ids (s j))
    · have hindicator (ω : ∀ i, A i) :
          (if ∀ i, fail (s i) ω then (1 : ℝ) else 0) = ∏ i, Z (s i) ω := by
        by_cases hall : ∀ i, fail (s i) ω
        · simp [Z, hall]
        · obtain ⟨i, hi⟩ := not_forall.mp hall
          have hz : (∏ j, Z (s j) ω) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Z, hi])
          simp [hall, hz]
      have heq : μ.pr (fun ω => ∀ i, fail (s i) ω) = μ.expect (fun ω => ∏ i, Z (s i) ω) := by
        unfold FinProb.pr FinProb.expect
        apply Finset.sum_congr rfl
        intro ω _
        dsimp only
        rw [← hindicator ω]
        split_ifs <;> simp
      have hj := Lane_sol_s05_h5l.pi_expect_prod_disjoint P Finset.univ
        (fun i : Fin q => ids (s i)) (fun i ω => Z (s i) ω)
        (fun i _ => hZlocal (s i)) (fun i _ j _ hij => hsep i j hij)
      calc
        _ = μ.pr (fun ω => ∀ i, fail (s i) ω) := by
          apply congrArg μ.pr
          funext ω
          exact propext ⟨And.right, fun h => ⟨hsep, h⟩⟩
        _ = μ.expect (fun ω => ∏ i, Z (s i) ω) := heq
        _ = ∏ i, μ.expect (Z (s i)) := hj
        _ ≤ ∏ _i : Fin q, ε := by
          apply Finset.prod_le_prod₀
          · intro i _; exact hnonneg (s i)
          · intro i _; rw [hpr]; exact hfail (s i)
        _ = ε ^ q := by simp
    · simp only [hsep, false_and, FinProb.pr, if_false, Finset.sum_const_zero]
      exact pow_nonneg hε q
  have hu := FinProb.pr_exists_le_sum5 μ (fun (s : Fin q → Rec) ω =>
    (∀ i j, i ≠ j → Disjoint (ids (s i)) (ids (s j))) ∧ ∀ i, fail (s i) ω)
  calc
    _ ≤ ∑ s : Fin q → Rec, μ.pr (fun ω =>
        (∀ i j, i ≠ j → Disjoint (ids (s i)) (ids (s j))) ∧ ∀ i, fail (s i) ω) := hu
    _ ≤ ∑ _s : Fin q → Rec, ε ^ q := Finset.sum_le_sum fun s _ => hEach s
    _ = (Fintype.card Rec : ℝ) ^ q * ε ^ q := by simp

theorem failure_count_union
    {Id Rec : Type*} [Fintype Id] [DecidableEq Id] [Fintype Rec]
    {A : Id → Type*} [∀ i, Fintype (A i)]
    (P : ∀ i, FinProb (A i)) (ids : Rec → Finset Id)
    (hsep : ∀ r r', r ≠ r' → Disjoint (ids r) (ids r'))
    (fail : Rec → (∀ i, A i) → Prop) (hlocal : ∀ r, FinProb.DependsOn (fail r) (ids r))
    (ε : ℝ) (hε : 0 ≤ ε) (hfail : ∀ r, (FinProb.pi P).pr (fail r) ≤ ε) (q : ℕ) :
    (FinProb.pi P).pr (fun ω => q ≤ (Finset.univ.filter fun r => fail r ω).card) ≤
      (Fintype.card Rec : ℝ) ^ q * ε ^ q := by
  classical
  apply le_trans (FinProb.pr_mono (FinProb.pi P) _ _ ?_)
    (disjoint_failure_union P ids fail hlocal ε hε hfail q)
  intro ω hω
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq hω
  let e : Fin q ≃ T := Fintype.equivOfCardEq (by simp [hc])
  let s : Fin q → Rec := fun i => (e i).1
  have hs : Function.Injective s := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  refine ⟨s, ?_, ?_⟩
  · intro i j hij
    exact hsep (s i) (s j) (fun h => hij (hs h))
  · intro i
    exact (Finset.mem_filter.mp (hT (e i).2)).2

end
end HypercubeRamsey.Lane_sol_s05_centres
