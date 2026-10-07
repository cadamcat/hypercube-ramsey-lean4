import HypercubeRamsey.S05.History_sol_s05_h5l_incidence

namespace HypercubeRamsey.Lane_sol_s05_h5l

open Classical OAI.HypercubeRamsey

noncomputable section
set_option maxHeartbeats 800000

theorem pr_finset_union_le {Ω I : Type*} [Fintype Ω] (P : FinProb Ω)
    (S : Finset I) (A : I → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, P.pr (A i) := by
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert i S hi ih =>
    have he : (fun ω => ∃ j ∈ insert i S, A j ω) =
        (fun ω => A i ω ∨ ∃ j ∈ S, A j ω) := by
      funext ω
      apply propext
      simp
    rw [he]
    calc
      _ ≤ P.pr (A i) + P.pr (fun ω => ∃ j ∈ S, A j ω) := FinProb.pr_union P _ _
      _ ≤ P.pr (A i) + ∑ j ∈ S, P.pr (A j) := add_le_add le_rfl ih
      _ = _ := (Finset.sum_insert (f := fun j => P.pr (A j)) hi).symm

def smallSubsets (m j : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.range (j + 1)).biUnion fun h => Finset.univ.powersetCard h

theorem mem_smallSubsets {m j : ℕ} (F : Finset (Fin m)) :
    F ∈ smallSubsets m j ↔ F.card ≤ j := by
  simp only [smallSubsets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨h, hh, he⟩
    omega
  · intro h
    exact ⟨F.card, by omega, rfl⟩

theorem smallSubsets_card (m j : ℕ) :
    (smallSubsets m j).card ≤ (j + 1) * (m + 1) ^ j := by
  calc
    _ ≤ ∑ h ∈ Finset.range (j + 1), (Finset.univ.powersetCard h : Finset (Finset (Fin m))).card :=
      Finset.card_biUnion_le
    _ = ∑ h ∈ Finset.range (j + 1), m.choose h := by simp
    _ ≤ ∑ _h ∈ Finset.range (j + 1), (m + 1) ^ j := by
      apply Finset.sum_le_sum
      intro h hh
      have hle : h ≤ j := by have := Finset.mem_range.mp hh; omega
      exact (Nat.choose_le_pow m h).trans ((Nat.pow_le_pow_left (Nat.le_succ m) h).trans
        (Nat.pow_le_pow_right (by omega : 0 < m + 1) hle))
    _ = _ := by simp

/-- Retain actual signs when counting types at a fixed entering history. -/
def lowTypeFromData {n m J : ℕ} (q : CoarseKey5 n) (t : CubeVertex m) (j : Fin (J + 1))
    (C : Finset (CoarseKey5 n)) (F : Finset (Fin m)) : EvenType5 n m J :=
  (q, C.image (fun i => keyAt5 J i t j.val) ∪
    F.image (fun h => keyAt5 J q (flipVertex5 t h) j.val) ∪
    (({j.val + 1} : Finset ℕ) ∪ (if 0 < j.val then {j.val - 1} else ∅)).image
      (fun h => keyAt5 J q t h), some j)

def lowTypeCandidates {n m J : ℕ} (q : CoarseKey5 n) (t : CubeVertex m) (j : Fin (J + 1)) :
    Finset (EvenType5 n m J) :=
  ((coarseBall 1 q).powerset.product (smallSubsets m j.val)).image
    (fun d => lowTypeFromData q t j d.1 d.2)

theorem lowTypeCandidates_card {n m J : ℕ} (q : CoarseKey5 n) (t : CubeVertex m) (j : Fin (J + 1))
    (D : ℕ) (hD : (coarseBall 1 q).card ≤ D) :
    (lowTypeCandidates q t j).card ≤ 2 ^ D * (j.val + 1) * (m + 1) ^ j.val := by
  calc
    _ ≤ ((coarseBall 1 q).powerset.product (smallSubsets m j.val)).card := Finset.card_image_le
    _ = 2 ^ (coarseBall 1 q).card * (smallSubsets m j.val).card := by simp
    _ ≤ 2 ^ D * ((j.val + 1) * (m + 1) ^ j.val) :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < 2) hD) (smallSubsets_card m j.val)
    _ = _ := (Nat.mul_assoc _ _ _).symm

theorem evenType_mem_candidates {n m : ℕ} (g : ChunkGeometry5 n m) (J : ℕ)
    (x : CubeVertex n) (j : Fin (J + 1)) (hj : g.severity x = j.val) :
    g.evenType J x ∈ lowTypeCandidates (g.key x) (g.sign x) j := by
  have hlo : g.severity x ≤ J := by have := j.isLt; omega
  refine Finset.mem_image.mpr ⟨(g.coarseRange x, g.flippable x), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, coarseRange_near g x q hq⟩
    · apply (mem_smallSubsets _).2
      rw [← hj]
      exact flippable_card_le_severity g x
  · simp only [lowTypeFromData, ChunkGeometry5.evenType, ChunkGeometry5.typeKeys,
      ite_eq_left hlo, dite_eq_left hlo]
    apply Prod.ext
    · rfl
    · dsimp only
      apply Prod.ext
      · dsimp only
        simp only [hj, flipVertex5]
      · dsimp only
        apply congrArg some
        apply Fin.ext
        exact hj.symm

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (X : Setup5 γ K' χ n N E G)

def lowTypeGroup (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1)) :
    Finset X.Ty :=
  @Finset.filter X.Ty (fun K => ∃ x : CubeVertex n,
    IsEvenRole x ∧ X.g.evenType (X.p.J n) x = K ∧
      X.g.key x = q ∧ X.g.sign x = t ∧ X.g.severity x = j.val)
    (fun _ => Classical.propDecidable _) Finset.univ

theorem mem_lowTypeGroup (q : CoarseKey5 n) (t : CubeVertex (X.p.m n))
    (j : Fin (X.p.J n + 1)) (K : X.Ty) :
    K ∈ lowTypeGroup X q t j ↔ ∃ x : CubeVertex n,
      IsEvenRole x ∧ X.g.evenType (X.p.J n) x = K ∧
        X.g.key x = q ∧ X.g.sign x = t ∧ X.g.severity x = j.val := by
  simp only [lowTypeGroup, Finset.mem_filter, Finset.mem_univ, true_and]

theorem lowTypeGroup_subset (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1)) :
    lowTypeGroup X q t j ⊆ lowTypeCandidates q t j := by
  intro K hK
  obtain ⟨x, hx, ht, hq, hs, hj⟩ := (mem_lowTypeGroup X q t j K).mp hK
  have hh := evenType_mem_candidates X.g (X.p.J n) x j hj
  simpa only [ht, hq, hs] using hh

theorem lowTypeGroup_card (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1))
    (D : ℕ) (hD : (coarseBall 1 q).card ≤ D) :
    (lowTypeGroup X q t j).card ≤ 2 ^ D * (j.val + 1) * (X.p.m n + 1) ^ j.val :=
  (Finset.card_le_card (lowTypeGroup_subset X q t j)).trans (lowTypeCandidates_card q t j D hD)

theorem lowTypeGroup_data (q : CoarseKey5 n) (t : CubeVertex (X.p.m n)) (j : Fin (X.p.J n + 1))
    (K : X.Ty) (hK : K ∈ lowTypeGroup X q t j) :
    X.TypeOccurs K ∧ K.1 = q ∧ K.2.2 = some j ∧
      K.2.1.card ≤ coarseChunkCount5 * 4 + 1 + j.val + 2 := by
  obtain ⟨x, hx, ht, hq, hs, hj⟩ := (mem_lowTypeGroup X q t j K).mp hK
  have hlo : X.g.severity x ≤ X.p.J n := by have := j.isLt; omega
  refine ⟨⟨x, hx, ht⟩, ?_, ?_, ?_⟩
  · rw [← ht]
    exact hq
  · rw [← ht]
    simp only [ChunkGeometry5.evenType, dite_eq_left hlo]
    congr 1
    apply Fin.ext
    exact hj
  · rw [← ht, ← hj]
    exact low_type_card X.g (X.p.J n) x hlo

end
end HypercubeRamsey.Lane_sol_s05_h5l
