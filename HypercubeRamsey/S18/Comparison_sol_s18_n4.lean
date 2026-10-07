import HypercubeRamsey.S18.Nodes_q_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_n4
open Classical
open scoped BigOperators

private theorem finLawPr_eq_mass_filter
    {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = LocalLemma.mass P.w (Finset.univ.filter A) := by
  classical
  simp [FinLaw.pr, LocalLemma.mass, Finset.sum_filter]

private theorem prodOneSubLower
    {I : Type*} [DecidableEq I] (S : Finset I) (q : I → ℝ)
    (hq0 : ∀ i ∈ S, 0 ≤ q i) (hq1 : ∀ i ∈ S, q i ≤ 1) :
    1 - ∑ i ∈ S, q i ≤ ∏ i ∈ S, (1 - q i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      have hi0 := hq0 i (Finset.mem_insert_self i S)
      have hi1 := hq1 i (Finset.mem_insert_self i S)
      have hq0' : ∀ j ∈ S, 0 ≤ q j := fun j hj => hq0 j (Finset.mem_insert_of_mem hj)
      have hq1' : ∀ j ∈ S, q j ≤ 1 := fun j hj => hq1 j (Finset.mem_insert_of_mem hj)
      have hsum0 : 0 ≤ ∑ j ∈ S, q j := Finset.sum_nonneg fun j hj => hq0' j hj
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        1 - (q i + ∑ j ∈ S, q j) ≤ (1 - q i) * (1 - ∑ j ∈ S, q j) := by
          nlinarith [mul_nonneg hi0 hsum0]
        _ ≤ (1 - q i) * ∏ j ∈ S, (1 - q j) :=
          mul_le_mul_of_nonneg_left (ih hq0' hq1') (sub_nonneg.mpr hi1)

private theorem lawPrAvoidMass {Ω I : Type*} [Fintype Ω] [Fintype I]
    [DecidableEq Ω] [DecidableEq I] (P : FinLaw Ω) (leaves : I → Finset Ω)
    (S : Finset I) (F : Ω → Prop) :
    LocalLemma.mass P.w ((Finset.univ.filter F) ∩ LocalLemma.avoid leaves S) =
      P.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ leaves i) := by
  unfold LocalLemma.mass FinLaw.pr
  rw [← Finset.sum_ite_mem_eq]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hf : F x <;> by_cases ha : ∀ i ∈ S, x ∉ leaves i <;>
    simp [LocalLemma.avoid, hf, ha]

private theorem lawCondPr {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : FinLaw Ω) (A : Finset Ω) (hA : 0 < ∑ x ∈ A, P.w x) (F : Ω → Prop) :
    (FinLaw.cond P A hA).pr F = P.pr (fun x => x ∈ A ∧ F x) / (∑ x ∈ A, P.w x) := by
  unfold FinLaw.pr FinLaw.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hm : x ∈ A <;> by_cases hf : F x <;> simp [hm, hf]

set_option maxHeartbeats 400000 in
/-- The local lemma compares an additional test event through only its touching leaves. -/
theorem leafTestProbabilityBound
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2)
    (hpositive : 0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x)
    (F : D.encoding.InitInput → Prop) (touches : L.Leaf → Prop)
    (hF : ∀ S : Finset L.Leaf, (∀ i ∈ S, ¬ touches i) →
      D.encoding.permLaw.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
        D.encoding.permLaw.pr F * D.encoding.permLaw.pr (fun x => ∀ i ∈ S, x ∉ L.leaf i)) :
    (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).pr F ≤
      D.encoding.permLaw.pr F * ∏ i ∈ Finset.univ.filter touches,
        (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹ := by
  classical
  let p : L.Leaf → ℝ := fun i => D.encoding.permLaw.pr (fun x => x ∈ L.leaf i)
  let q : L.Leaf → ℝ := fun i => 2 * p i
  let adj : L.Leaf → L.Leaf → Prop := fun i j => j ≠ i ∧ L.adjacent i j
  letI : DecidableRel adj := Classical.decRel _
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    unfold p FinLaw.pr
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact D.encoding.permLaw.nonneg x
    · exact le_rfl
  have hq0 : ∀ i, 0 ≤ q i := fun i => mul_nonneg (by norm_num) (hp0 i)
  have hqLt : ∀ i, q i < 1 := by
    intro i
    have hi := hprob i
    dsimp [q, p] at hi ⊢
    linarith
  have hq1 : ∀ i, q i ≤ 1 := fun i => (hqLt i).le
  have hsymm : ∀ i j, adj i j → adj j i := by
    intro i j hij
    rcases hij with ⟨hne, hadj⟩
    refine ⟨hne.symm, ?_⟩
    apply (L.adjacent_eq j i).mpr
    rcases (L.adjacent_eq i j).mp hadj with hdom | himage | htape
    · exact Or.inl (by
        intro hdis
        exact hdom (disjoint_comm.mp hdis))
    · exact Or.inr (Or.inl (by
        intro hdis
        exact himage (disjoint_comm.mp hdis)))
    · exact Or.inr (Or.inr (by
        intro hdis
        exact htape (disjoint_comm.mp hdis)))
  have hirr : ∀ i, ¬ adj i i := by
    intro i hi
    exact hi.1 rfl
  have hcond : ∀ i (S : Finset L.Leaf), i ∉ S →
      (∀ j ∈ S, ¬ adj i j) →
      LocalLemma.mass D.encoding.permLaw.w
          (L.leaf i ∩ LocalLemma.avoid L.leaf S) ≤
        p i * LocalLemma.mass D.encoding.permLaw.w
          (LocalLemma.avoid L.leaf S) := by
    intro i S hiS hnon
    have hnon' : ∀ j ∈ S, ¬ L.adjacent i j := by
      intro j hj hadj
      have hji : j ≠ i := by
        intro hEq
        exact hiS (hEq ▸ hj)
      exact hnon j hj ⟨hji, hadj⟩
    have hraw := L.nonneighbor_bound i S hnon'
    have hnum : LocalLemma.mass D.encoding.permLaw.w
        (L.leaf i ∩ LocalLemma.avoid L.leaf S) =
        D.encoding.permLaw.pr (fun x => x ∈ L.leaf i ∧ ∀ j ∈ S, x ∉ L.leaf j) := by
      rw [finLawPr_eq_mass_filter]
      congr 1
      ext x
      simp [LocalLemma.avoid]
    have hden : LocalLemma.mass D.encoding.permLaw.w
        (LocalLemma.avoid L.leaf S) =
        D.encoding.permLaw.pr (fun x => ∀ j ∈ S, x ∉ L.leaf j) := by
      rw [finLawPr_eq_mass_filter]
      congr 1
      ext x
      simp [LocalLemma.avoid]
    rw [← hnum, ← hden] at hraw
    simpa [p] using hraw
  have hneighborCharge : ∀ i,
      (∑ j ∈ Finset.univ.filter (adj i), q j) ≤ 1 / 2 := by
    intro i
    have hcharge' :
        (∑ j ∈ Finset.univ.filter (fun j => L.adjacent i j), q j) ≤ 1 / 2 := by
      simpa [q, p, Finset.sum_filter] using hcharge i
    have hsub : Finset.univ.filter (adj i) ⊆
        Finset.univ.filter (fun j => L.adjacent i j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        (Finset.mem_filter.mp hj).2.2⟩
    calc
      (∑ j ∈ Finset.univ.filter (adj i), q j) ≤
          ∑ j ∈ Finset.univ.filter (fun j => L.adjacent i j), q j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hq0 j)
      _ ≤ 1 / 2 := hcharge'
  have hpx : ∀ i, p i ≤ q i *
      ∏ j ∈ Finset.univ.filter (adj i), (1 - q j) := by
    intro i
    have hprod := prodOneSubLower (Finset.univ.filter (adj i)) q
      (fun j hj => hq0 j) (fun j hj => hq1 j)
    have hsum : ∑ j ∈ Finset.univ.filter (adj i), q j ≤ 1 / 2 := hneighborCharge i
    have hprodHalf : 1 / 2 ≤ ∏ j ∈ Finset.univ.filter (adj i), (1 - q j) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hprodHalf (hq0 i)
    dsimp [q]
    nlinarith
  have hLLL := LocalLemma.conditional_avoidance
    D.encoding.permLaw.w D.encoding.permLaw.nonneg D.encoding.permLaw.sum_one
    L.leaf adj hsymm hirr p q hcond hq0 hqLt hpx
  let Fset := Finset.univ.filter F
  have hden (S : Finset L.Leaf) : LocalLemma.mass D.encoding.permLaw.w (LocalLemma.avoid L.leaf S) =
      D.encoding.permLaw.pr (fun x => ∀ i ∈ S, x ∉ L.leaf i) := by
    rw [finLawPr_eq_mass_filter]
    congr 1
    ext x
    simp only [LocalLemma.avoid, Finset.mem_filter]
  have htest : ∀ S : Finset L.Leaf, (∀ i ∈ S, ¬ touches i) →
      LocalLemma.mass D.encoding.permLaw.w (Fset ∩ LocalLemma.avoid L.leaf S) ≤
        D.encoding.permLaw.pr F * LocalLemma.mass D.encoding.permLaw.w (LocalLemma.avoid L.leaf S) := by
    intro S hS
    rw [lawPrAvoidMass, hden]
    exact hF S hS
  have hterminal : S18.terminalSet D δ = LocalLemma.avoid L.leaf Finset.univ := by
    ext x
    simp [Lane_q_s18_n4.terminalSetAvoidLeaves D δ L, LocalLemma.avoid]
  have hc : (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).pr F =
      LocalLemma.mass D.encoding.permLaw.w (Fset ∩ LocalLemma.avoid L.leaf Finset.univ) /
        LocalLemma.mass D.encoding.permLaw.w (LocalLemma.avoid L.leaf Finset.univ) := by
    rw [LateEncoding.terminalLaw, lawCondPr]
    have hevent : (fun x => x ∈ S18.terminalSet D δ ∧ F x) =
        (fun x => F x ∧ ∀ i ∈ (Finset.univ : Finset L.Leaf), x ∉ L.leaf i) := by
      funext x
      apply propext
      simp only [Lane_q_s18_n4.terminalSetAvoidLeaves D δ L, Finset.mem_univ,
        forall_const, and_comm]
    rw [hevent, ← lawPrAvoidMass]
    change _ / LocalLemma.mass D.encoding.permLaw.w (S18.terminalSet D δ) = _
    rw [hterminal]
  rw [hc]
  simpa [q, p] using hLLL.2.2.2 Fset (D.encoding.permLaw.pr F) touches htest Finset.univ

private theorem comparisonMapE {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

/-- Comparing every value fiber suffices for every nonnegative finite test. -/
theorem testComparisonFromFibers {Ω : Type*} [Fintype Ω]
    (J P : FinLaw Ω) (Ψ : Ω → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x) (c : ℝ)
    (hfiber : ∀ v, J.pr (fun x => Ψ x = v) ≤ c * P.pr (fun x => Ψ x = v)) :
    J.E Ψ ≤ c * P.E Ψ := by
  let values := Finset.univ.image Ψ
  let project : Ω → values := fun x => ⟨Ψ x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  have hweight (R : FinLaw Ω) (v : values) :
      (FinLaw.map R project).w v = R.pr (fun x => Ψ x = v.1) := by
    unfold FinLaw.map FinLaw.pr
    apply Finset.sum_congr rfl
    intro x hx
    have heq : project x = v ↔ Ψ x = v.1 := Subtype.ext_iff
    by_cases h : Ψ x = v.1 <;> simp [heq, h]
  have hv : ∀ v : values, 0 ≤ v.1 := by
    intro v
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp v.2
    exact heq ▸ hΨ x
  have hweights : ∀ v : values, (FinLaw.map J project).w v ≤ c * (FinLaw.map P project).w v := by
    intro v
    rw [hweight, hweight]
    exact hfiber v.1
  have hJ : (FinLaw.map J project).E (fun v => v.1) = J.E Ψ := comparisonMapE J project _
  have hP : (FinLaw.map P project).E (fun v => v.1) = P.E Ψ := comparisonMapE P project _
  rw [← hJ, ← hP]
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hmem
  have hh := mul_le_mul_of_nonneg_right (hweights v) (hv v)
  simpa only [mul_assoc] using hh

/-- Exact remaining sufficient condition for the local comparison field. -/
theorem terminalTestComparisonOfFibers
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ ε : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2)
    (hpositive : 0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x)
    (Ψ : D.encoding.InitInput → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x)
    (touches : ℝ → L.Leaf → Prop)
    (hnonneighbor : ∀ v (S : Finset L.Leaf), (∀ i ∈ S, ¬ touches v i) →
      D.encoding.permLaw.pr (fun x => Ψ x = v ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
        D.encoding.permLaw.pr (fun x => Ψ x = v) *
          D.encoding.permLaw.pr (fun x => ∀ i ∈ S, x ∉ L.leaf i))
    (hcost : ∀ v, (∏ i ∈ Finset.univ.filter (touches v),
      (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹) ≤ 1 + ε) :
    (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).E Ψ ≤
      (1 + ε) * D.encoding.permLaw.E Ψ := by
  apply testComparisonFromFibers _ _ Ψ hΨ (1 + ε)
  intro v
  have hp : 0 ≤ D.encoding.permLaw.pr (fun x => Ψ x = v) := by
    unfold FinLaw.pr
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : Ψ x = v <;> simp [h, D.encoding.permLaw.nonneg]
  exact (leafTestProbabilityBound D δ L hprob hcharge hpositive (fun x => Ψ x = v)
    (touches v) (hnonneighbor v)).trans (by
      calc
        _ ≤ D.encoding.permLaw.pr (fun x => Ψ x = v) * (1 + ε) :=
          mul_le_mul_of_nonneg_left (hcost v) hp
        _ = (1 + ε) * D.encoding.permLaw.pr (fun x => Ψ x = v) := mul_comm _ _)

end HypercubeRamsey.Lane_sol_s18_n4
