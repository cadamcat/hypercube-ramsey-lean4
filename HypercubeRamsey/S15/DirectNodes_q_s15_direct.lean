import HypercubeRamsey.S15.Defs
import HypercubeRamsey.S05.Clock_q_s05_even
import HypercubeRamsey.Framework.FinProbLemmas

/-! Geometric and locality adapters for the direct assignment proof lane. -/

namespace HypercubeRamsey.Lane_q_s15_direct

open HypercubeRamsey OAI.HypercubeRamsey
open Classical

noncomputable def star {T : Stage} {k : ℕ}
    (a : S15.EvenPosition T k) :
    Finset (S15.OddPosition T k) :=
  Finset.univ.filter fun b => S15.Adjacent a b

theorem star_card_le {T : Stage} {k : ℕ}
    (a : S15.EvenPosition T k) :
    (star a).card ≤ T.S.n k := by
  classical
  let S := star a
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj a.1 v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj a.1 v).card := Finset.card_le_card hsub
    _ ≤ T.S.n k := cube_adj_neighbors_card_le (T.S.n k) a.1

noncomputable def starIncidence {T : Stage} {k : ℕ}
    (b : S15.OddPosition T k) :
    Finset (S15.EvenPosition T k) :=
  Finset.univ.filter fun a => b ∈ star a

theorem star_incidence_card_le {T : Stage} {k : ℕ}
    (b : S15.OddPosition T k) :
    (starIncidence b).card ≤ T.S.n k := by
  classical
  let S := starIncidence b
  have himage : S.card = (S.image Subtype.val).card :=
    (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hsub : S.image Subtype.val ⊆
      Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj b.1 v := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
    have hb : b ∈ star a := (Finset.mem_filter.mp ha).2
    have hab : S15.Adjacent a b := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.symm⟩
  calc
    S.card = (S.image Subtype.val).card := himage
    _ ≤ (Finset.univ.filter fun v : CubeVertex (T.S.n k) =>
        (cube (T.S.n k)).Adj b.1 v).card := Finset.card_le_card hsub
    _ ≤ T.S.n k := cube_adj_neighbors_card_le (T.S.n k) b.1

theorem directRowMass_dependsOn {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : S15.EvenPosition T k)
    (ys ys' : S15.OddAssignment T k)
    (hys : ∀ b ∈ star a, ys b = ys' b) :
    S15.directRowMass PT hPT ys a = S15.directRowMass PT hPT ys' a := by
  classical
  have hcrossSubset : S15.crossingNeighbours PT hPT a ⊆ star a := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hbulkSubset : S15.bulkNeighbours PT hPT a ⊆ star a := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
  have hfactor (b : S15.OddPosition T k) (hb : b ∈ star a) (x : Fin (T.S.N k)) :
      S15.directFactor PT hPT a ys b x = S15.directFactor PT hPT a ys' b x := by
    simp [S15.directFactor, hys b hb]
  have hcross : S15.directCrossingMass PT hPT ys a =
      S15.directCrossingMass PT hPT ys' a := by
    unfold S15.directCrossingMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact hfactor b (hcrossSubset hb) x
  have hpost (x : Fin (T.S.N k)) :
      S15.directPostCrossingWeight PT hPT ys a x =
        S15.directPostCrossingWeight PT hPT ys' a x := by
    unfold S15.directPostCrossingWeight
    rw [hcross]
    by_cases hm : 0 < S15.directCrossingMass PT hPT ys' a
    · simp [hm]
      apply congrArg (fun z : ℝ => z / S15.directCrossingMass PT hPT ys' a)
      apply congrArg (fun z : ℝ => S15.directBaseWeight PT hPT a x * z)
      apply Finset.prod_congr rfl
      intro b hb
      exact hfactor b (hcrossSubset hb) x
    · simp [hm]
  have hbulk : S15.directBulkMass PT hPT ys a = S15.directBulkMass PT hPT ys' a := by
    unfold S15.directBulkMass
    apply Finset.sum_congr rfl
    intro x hx
    rw [hpost]
    congr 1
    apply Finset.prod_congr rfl
    intro b hb
    exact hfactor b (hbulkSubset hb) x
  simp [S15.directRowMass, hcross, hbulk]

theorem expect_le_of_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    [∀ i, Nonempty (Ω i)] (P : FinProb (∀ i, Ω i)) (laws : ∀ i, FinProb (Ω i))
    (S : Finset ι) (F : (∀ i, Ω i) → ℝ) (α : ℝ)
    (hF : ∀ ω, 0 ≤ F ω)
    (hdep : FinProb.DependsOn F S)
    (hbound : ∀ o : ∀ i, Ω i,
      P.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤ α * ∏ i ∈ S, (laws i).w (o i)) :
    P.expect F ≤ α * (FinProb.pi laws).expect F := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i : ι => i ∈ S) Ω
  let proj : (∀ i, Ω i) → (∀ i : {i // i ∈ S}, Ω i.1) := fun ω i => ω i.1
  let outside : ∀ i : {i // i ∉ S}, Ω i.1 := fun i => Classical.choice (inferInstance)
  let Fsub : (∀ i : {i // i ∈ S}, Ω i.1) → ℝ := fun a => F (e.symm (a, outside))
  let Psub : FinProb (∀ i : {i // i ∈ S}, Ω i.1) := FinProb.map P proj
  let Qsub : FinProb (∀ i : {i // i ∈ S}, Ω i.1) :=
    FinProb.pi (fun i : {i // i ∈ S} => laws i.1)
  have hFsub : ∀ a, 0 ≤ Fsub a := fun a => hF (e.symm (a, outside))
  have hproj (ω : ∀ i, Ω i) (i : {i // i ∈ S}) :
      e.symm (proj ω, outside) i.1 = ω i.1 := by
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2, proj]
  have hFfactor (ω : ∀ i, Ω i) : F ω = Fsub (proj ω) := by
    unfold Fsub
    apply hdep
    intro i hi
    exact (hproj ω ⟨i, hi⟩).symm
  have hPexpect : P.expect F = Psub.expect Fsub := by
    calc
      P.expect F = P.expect (fun ω => Fsub (proj ω)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro ω hω
        rw [hFfactor]
      _ = Psub.expect Fsub := (FinProb.map_expect P proj Fsub).symm
  have hrawexpect : (FinProb.pi laws).expect F = Qsub.expect Fsub := by
    exact FinProb.pi_expect_depends laws S F
      (fun i => Classical.choice (inferInstance)) hdep
  have hPsubWeight (a : ∀ i : {i // i ∈ S}, Ω i.1) :
      Psub.w a = P.pr (fun ω => ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩) := by
    unfold Psub FinProb.map FinProb.pr
    apply Finset.sum_congr rfl
    intro ω hω
    have hiff : proj ω = a ↔ ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩ := by
      constructor
      · intro h i hi
        exact congrFun h ⟨i, hi⟩
      · intro h
        funext i
        exact h i.1 i.2
    by_cases h : ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩ <;> simp [hiff, h]
  have htarget (a : ∀ i : {i // i ∈ S}, Ω i.1) :
      Psub.w a ≤ α * Qsub.w a := by
    rw [hPsubWeight]
    let o : ∀ i, Ω i := e.symm (a, outside)
    have ho (i : ι) (hi : i ∈ S) : o i = a ⟨i, hi⟩ := by
      simp [o, e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
    have hprob : P.pr (fun ω => ∀ i (hi : i ∈ S), ω i = a ⟨i, hi⟩) =
        P.pr (fun ω => ∀ i (hi : i ∈ S), ω i = o i) := by
      congr 1
      funext ω
      apply propext
      constructor
      · intro h i hi
        calc
          ω i = a ⟨i, hi⟩ := h i hi
          _ = o i := (ho i hi).symm
      · intro h i hi
        calc
          ω i = o i := h i hi
          _ = a ⟨i, hi⟩ := ho i hi
    rw [hprob]
    calc
      P.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤ α * ∏ i ∈ S, (laws i).w (o i) := hbound o
      _ = α * Qsub.w a := by
        congr 1
        have hattach (g : ι → ℝ) :
            (∏ i : {i // i ∈ S}, g i.1) = ∏ i ∈ S, g i := by
          rw [Finset.univ_eq_attach]
          exact Finset.prod_attach S g
        calc
          ∏ i ∈ S, (laws i).w (o i) =
              ∏ i : {i // i ∈ S}, (laws i.1).w (o i.1) :=
            (hattach (fun i => (laws i).w (o i))).symm
          _ = ∏ i : {i // i ∈ S}, (laws i.1).w (a i) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [ho i.1 i.2]
          _ = Qsub.w a := by simp [Qsub, FinProb.pi]
  calc
    P.expect F = Psub.expect Fsub := hPexpect
    _ = ∑ a, Psub.w a * Fsub a := rfl
    _ ≤ ∑ a, (α * Qsub.w a) * Fsub a := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (htarget a) (hFsub a)
    _ = α * Qsub.expect Fsub := by
      simp [FinProb.expect, Finset.mul_sum, mul_assoc]
    _ = α * (FinProb.pi laws).expect F := by rw [hrawexpect]

end HypercubeRamsey.Lane_q_s15_direct
