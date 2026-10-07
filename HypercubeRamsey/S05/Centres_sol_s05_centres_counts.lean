import HypercubeRamsey.S05.Centres_sol_s05_centres_records

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
noncomputable section

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem fin_prefix_card (k t : ℕ) (h : k ≤ t) :
    (Finset.univ.filter (fun i : Fin t => (i : ℕ) < k)).card = k := by
  classical
  let S := Finset.univ.filter (fun i : Fin t => (i : ℕ) < k)
  let e : Fin k ≃ S := {
    toFun := fun i => ⟨Fin.castLE h i, by simp [S, i.isLt]⟩
    invFun := fun i => ⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; rfl
    right_inv := by intro i; rfl }
  simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr e).symm

theorem usedBlocks_le_pool : X.p.usedBlocks n ≤ X.p.poolBlocks n := by
  have hexp : 1 ≤ Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg X.p.hKh.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hmul := mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg (X.p.usedBlocks n) :
    (0 : ℝ) ≤ X.p.usedBlocks n)
  have hceil : Real.exp (X.p.Kh * ((X.p.q0 : ℝ) * X.p.uStarSeg n)) * X.p.usedBlocks n ≤
      (X.p.poolBlocks n : ℝ) := Nat.le_ceil _
  exact_mod_cast (show (X.p.usedBlocks n : ℝ) ≤ X.p.poolBlocks n by simpa only [one_mul] using hmul.trans hceil)

def usedIndices : Finset (Fin X.blockBound) :=
  Finset.univ.filter fun i => (i : ℕ) < X.p.usedBlocks n

theorem usedIndices_legit (K : X.Ty) (hK : K.2.2 = none) : X.LegitRef K (usedIndices X) := by
  have hb : X.p.usedBlocks n ≤ X.blockBound :=
    (usedBlocks_le_pool X).trans (Nat.le_max_left _ _)
  simp only [Setup5.LegitRef, hK]
  change (usedIndices X).card = X.p.usedBlocks n ∧ usedIndices X ⊆ X.poolIdx
  rw [show (usedIndices X).card = X.p.usedBlocks n from fin_prefix_card _ _ hb]
  refine ⟨rfl, ?_⟩
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (usedBlocks_le_pool X)⟩

def shapeRecord {Id : Type} (y : OddRole5 n) (μ : X.St.Site → Id) : X.RecordOn Id :=
  let ℓ := X.g.roleKey (X.p.J n) y.1
  let obs := (Setup5.evenNbrs y).image fun a => (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1)
  let refs := ((Setup5.evenNbrs y).filter fun a =>
    ℓ ∈ (X.g.evenType (X.p.J n) a.1).2.1 ∧
      ℓ.isLeft = (X.g.evenType (X.p.J n) a.1).2.2.isSome).image fun a =>
        (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, X.g.optionalKey (X.p.J n) a.1)
  let mask : Option (Id × X.Ty × Finset (Fin X.blockBound)) :=
    if ℓ.isLeft then
      if hex : ∃ a ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none then
        let a := Classical.choose hex
        some (μ (X.St.stateOf a.1), X.g.evenType (X.p.J n) a.1, usedIndices X)
      else none
    else none
  (ℓ, obs, refs, mask)

theorem shapeRecord_from {Id : Type} (y : OddRole5 n) (μ : X.St.Site → Id) :
    X.RecordFrom (shapeRecord X y μ) y μ := by
  classical
  refine ⟨rfl, ?_, ?_, ?_⟩
  · ext c
    simp [shapeRecord]
  · ext c
    simp [shapeRecord]
  · dsimp only [shapeRecord]
    by_cases hl : (X.g.roleKey (X.p.J n) y.1).isLeft
    · rw [if_pos hl]
      by_cases hex : ∃ a ∈ Setup5.evenNbrs y, (X.g.evenType (X.p.J n) a.1).2.2 = none
      · rw [dif_pos hex]
        let a := Classical.choose hex
        have ha := Classical.choose_spec hex
        exact ⟨hl, a, ha.1, rfl, ha.2, rfl, usedIndices_legit X _ ha.2⟩
      · rw [dif_neg hex]
        intro _ a ha
        cases hK : (X.g.evenType (X.p.J n) a.1).2.2 with
        | none => exact (hex ⟨a, ha, hK⟩).elim
        | some j => simp [hK]
    · rw [if_neg hl]
      intro h
      exact (hl h).elim

def siteType (s : X.St.Site) : X.Ty :=
  if hex : ∃ a : EvenRole5 n, X.St.stateOf a.1 = s then
    X.g.evenType (X.p.J n) (Classical.choose hex).1
  else X.g.evenType (X.p.J n) (fun _ => false)

theorem siteType_even (a : EvenRole5 n) : siteType X (X.St.stateOf a.1) = X.g.evenType (X.p.J n) a.1 := by
  have hex : ∃ b : EvenRole5 n, X.St.stateOf b.1 = X.St.stateOf a.1 := ⟨a, rfl⟩
  rw [siteType, dif_pos hex]
  exact (X.St.state_determines _ _ (Classical.choose_spec hex)).2.2.2.2.1

end
end HypercubeRamsey.Lane_sol_s05_centres
