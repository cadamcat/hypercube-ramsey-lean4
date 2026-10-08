import HypercubeRamsey.S05.Centres_sol_s05_centres_support

namespace HypercubeRamsey.Lane_sol_s05_centres

open Classical OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
noncomputable section

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def observedArrays {Id : Type} (r : X.RecordOn Id) (a : X.ArraysOn Id) : X.ArraysOn Id :=
  fun c => if c ∈ r.2.1 then a c else fun _ => X.fallbackBlock c.2

theorem observedArrays_eq {Id : Type} (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty) (hc : c ∈ r.2.1) : observedArrays X r a c = a c := by
  simp [observedArrays, hc]

theorem refsOn_arrays_congr {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) : X.refsOn H r a = X.refsOn H r b := by
  classical
  have hmap (c : Id × X.Ty × Option X.Key) (hc : c ∈ r.2.2.1) :
      (c.1, c.2.1, X.refSubsetOn H a (c.1, c.2.1) c.2.2) =
        (c.1, c.2.1, X.refSubsetOn H b (c.1, c.2.1) c.2.2) := by
    have ha := hab (c.1, c.2.1) (href c hc)
    have hhit : ∀ y, X.hitSet a (c.1, c.2.1) y = X.hitSet b (c.1, c.2.1) y := by
      intro y
      unfold Setup5.hitSet
      rw [ha]
    simp [Setup5.refSubsetOn, hhit]
  unfold Setup5.refsOn
  ext d
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨c, hc, (hmap c hc).symm.trans he⟩
  · rintro ⟨c, hc, he⟩
    exact ⟨c, hc, (hmap c hc).trans he⟩

theorem step3Post_arrays_congr {Id : Type} (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c)
    (excl : Option (Id × X.Ty × Finset (Fin X.blockBound)))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn H r a excl θ = X.step3PostOn H r b excl θ := by
  unfold Setup5.step3PostOn
  rw [Lane_sol_s05_hist1b.candGateOn_arrays_congr X H r a b hmask hab θ,
    Lane_sol_s05_hist1b.obsLikOn_arrays_congr X H r a b hab θ excl,
    Lane_sol_s05_hist1b.step3MassOn_arrays_congr X H r a b hmask hab excl]

theorem highSource_arrays_congr {Id : Type} (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highSource H r a h = X.highSource H r b h := by
  have hp : X.step3PostOn H r a none = X.step3PostOn H r b none :=
    funext (step3Post_arrays_congr X H r a b hmask hab none)
  simp only [Setup5.highSource, hp]

theorem highDeleted_arrays_congr {Id : Type} (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highDeleted H r a c h = X.highDeleted H r b c h := by
  have hp : X.step3PostOn H r a (some c) = X.step3PostOn H r b (some c) :=
    funext (step3Post_arrays_congr X H r a b hmask hab (some c))
  simp only [Setup5.highDeleted, hp]

theorem highCapped_arrays_congr {Id : Type} (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) : X.HighCapped H r a ↔ X.HighCapped H r b := by
  simp only [Setup5.HighCapped, highSource_arrays_congr X H r a b hmask hab]

theorem highPrice_arrays_congr {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a b : X.ArraysOn Id)
    (hmask : ∀ c M, r.2.2.2 = some (c.1, c.2, M) → c ∈ r.2.1)
    (href : ∀ c ∈ r.2.2.1, (c.1, c.2.1) ∈ r.2.1)
    (hab : ∀ c ∈ r.2.1, a c = b c) :
    X.HighPriceFeasible H r a ↔ X.HighPriceFeasible H r b := by
  classical
  unfold Setup5.HighPriceFeasible
  rw [refsOn_arrays_congr X H r a b href hab]
  simp only [
    highSource_arrays_congr X H r a b hmask hab,
    highDeleted_arrays_congr X H r a b hmask hab]

def indexRow {s N : ℕ} (R : FinProb (Fin s × Fin N)) (t : ℕ) (o : Fin (t + 1) × Fin N) : ℝ :=
  if h : (o.1 : ℕ) < s then R.w (⟨o.1, h⟩, o.2) else 0

theorem indexRow_nonneg {s N : ℕ} (R : FinProb (Fin s × Fin N)) (t : ℕ) (o : Fin (t + 1) × Fin N) :
    0 ≤ indexRow R t o := by
  unfold indexRow
  split_ifs
  · exact R.nonneg _
  · exact le_rfl

theorem indexRow_index {s N t : ℕ} (R : FinProb (Fin s × Fin N)) (he : s = t)
    (o : Fin (t + 1) × Fin N) (hi : t ≤ (o.1 : ℕ)) : indexRow R t o = 0 := by
  simp [indexRow, he, not_lt.mpr hi]

theorem indexRow_sum {s N t : ℕ} (R : FinProb (Fin s × Fin N)) (he : s = t) :
    ∑ o : Fin (t + 1) × Fin N, indexRow R t o = 1 := by
  subst t
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have hlast : (∑ y : Fin N, indexRow R s (Fin.last s, y)) = 0 := by simp [indexRow]
  rw [hlast, add_zero]
  have hi : ∀ h : Fin s, ∀ y : Fin N, indexRow R s (h.castSucc, y) = R.w (h, y) := by
    intro h y
    simp [indexRow, h.isLt]
  simp only [hi]
  rw [← Fintype.sum_prod_type]
  exact R.sum_eq_one

theorem indexRow_cap {s N t : ℕ} (R : FinProb (Fin s × Fin N)) (C : ℝ)
    (hC : 0 ≤ C) (hcap : ∀ h y, R.w (h, y) ≤ C) (o : Fin (t + 1) × Fin N) :
    indexRow R t o ≤ C := by
  unfold indexRow
  split_ifs
  · exact hcap _ _
  · exact hC

theorem indexRow_support {s N t : ℕ} (R : FinProb (Fin s × Fin N))
    (o : Fin (t + 1) × Fin N) (ho : indexRow R t o ≠ 0) :
    ∃ h : Fin s, (h : ℕ) = (o.1 : ℕ) ∧ R.w (h, o.2) ≠ 0 := by
  unfold indexRow at ho
  split_ifs at ho with hi
  · exact ⟨⟨o.1, hi⟩, rfl, ho⟩
  · exact (ho rfl).elim

def indexCost {s N : ℕ} {Ref : Type*} (R : FinProb (Fin s × Fin N))
    (Q : Ref → Fin s → Law N) (c : Ref) (t : ℕ) (o : Fin (t + 1) × Fin N) : ℝ :=
  if h : (o.1 : ℕ) < s then
    max 0 (Real.log (indexRow R t o / ((Q c ⟨o.1, h⟩).w o.2 / (s : ℝ)))) else 0

theorem indexCost_sum {s N t : ℕ} {Ref : Type*} (R : FinProb (Fin s × Fin N))
    (Q : Ref → Fin s → Law N) (c : Ref) (he : s = t) :
    (∑ o : Fin (t + 1) × Fin N, indexRow R t o * indexCost R Q c t o) =
      ∑ h, ∑ y, R.w (h, y) * highDeletionCost5 R Q c h y := by
  subst t
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have hlast : (∑ y : Fin N, indexRow R s (Fin.last s, y) * indexCost R Q c s (Fin.last s, y)) = 0 := by
    simp [indexRow]
  rw [hlast, add_zero]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro y _
  simp [indexRow, indexCost, highDeletionCost5, h.isLt]

end
end HypercubeRamsey.Lane_sol_s05_centres
