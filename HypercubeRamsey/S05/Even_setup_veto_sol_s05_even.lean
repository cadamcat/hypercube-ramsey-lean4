import HypercubeRamsey.S05.Even_setup_local_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def vetoCondition (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (ω : X.CΩ L.ht) (y : OddRole5 n) : Prop := y = b → Setup5.pos ω l = t

theorem vetoCondition_local (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (hl : l ∈ X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack)) (y : OddRole5 n) :
    FinProb.DependsOn (fun ω => vetoCondition X L b l t ω y)
      (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack)) := by
  intro ω ω' hagree
  dsimp only [vetoCondition]
  by_cases hy : y = b
  · subst y
    have heq := congrArg (fun u : X.CVal L.ht => u.1) (hagree l hl)
    change (b = b → (ω l).1 = t) = (b = b → (ω' l).1 = t)
    rw [heq]
  · simp [hy]

def vetoLayer (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (hl : l ∈ X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack)) : X.CentreLayer5 :=
  { L with
    valid := fun H ω y => L.valid H ω y ∧ vetoCondition X L b l t ω y
    success := fun H ω => L.success H ω ∧ Setup5.pos ω l = t
    valid_local := by
      intro H y ω ω' hagree
      have h1 := L.valid_local H y ω ω' hagree
      have h2 := vetoCondition_local X L b l t hl y ω ω' hagree
      dsimp only at h1 h2 ⊢
      rw [h1, h2]
    success_valid := by
      intro H ω h y
      exact ⟨L.success_valid H ω h.1 y, fun _ => h.2⟩
    success_legal := fun H ω h => L.success_legal H ω h.1
    success_select := fun H ω h => L.success_select H ω h.1
    valid_select := fun H ω y h => L.valid_select H ω y h.1
    valid_base_support := fun H ω y h => L.valid_base_support H ω y h.1
    valid_step1 := fun H ω y h => L.valid_step1 H ω y h.1
    valid_block_support := fun H ω y h => L.valid_block_support H ω y h.1
    valid_path_support := fun H ω y h => L.valid_path_support H ω y h.1
    valid_counts := fun H ω y h => L.valid_counts H ω y h.1
    valid_T := fun H ω y h => L.valid_T H ω y h.1
    valid_hits := fun H ω y h => L.valid_hits H ω y h.1
    valid_heavy := fun H ω y h => L.valid_heavy H ω y h.1
    valid_gate := fun H ω y h => L.valid_gate H ω y h.1
    valid_step3 := fun H ω y h => L.valid_step3 H ω y h.1 }

def vetoRow (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (R : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ)
    (H : X.KeyHist) (ω : X.CΩ L.ht) (y : OddRole5 n) : X.OddOut → ℝ :=
  if vetoCondition X L b l t ω y then R H ω y else fun _ => 0

theorem vetoRow_nonneg (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (R : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ)
    (hR : ∀ H ω y o, 0 ≤ R H ω y o) (H) (ω) (y) (o) :
    0 ≤ vetoRow X L b l t R H ω y o := by
  unfold vetoRow
  split_ifs
  · exact hR H ω y o
  · rfl

theorem vetoRow_le (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (R : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ)
    (hR : ∀ H ω y o, 0 ≤ R H ω y o) (H) (ω) (y) (o) :
    vetoRow X L b l t R H ω y o ≤ R H ω y o := by
  unfold vetoRow
  split_ifs
  · rfl
  · exact hR H ω y o

theorem vetoRow_local (L : X.CentreLayer5) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (hl : l ∈ X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack))
    (R : X.KeyHist → X.CΩ L.ht → OddRole5 n → X.OddOut → ℝ)
    (hR : ∀ H y, FinProb.DependsOn (fun ω => R H ω y)
      (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack))) (H) (y) :
    FinProb.DependsOn (fun ω => vetoRow X L b l t R H ω y)
      (X.scopeBall (h := L.ht) y.1 (L.ht.hp.r + L.slack)) := by
  intro ω ω' hagree
  dsimp only [vetoRow]
  have h1 := vetoCondition_local X L b l t hl y ω ω' hagree
  have h2 := hR H y ω ω' hagree
  dsimp only at h1 h2
  rw [h1, h2]

def vetoHighRows (L : X.CentreLayer5) (HR : X.HighRows5 L) (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (hl : l ∈ X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack)) : X.HighRows5 (vetoLayer X L b l t hl) where
  row := vetoRow X L b l t HR.row
  row_nonneg := vetoRow_nonneg X L b l t HR.row HR.row_nonneg
  row_low := by
    intro H ω y o hy
    unfold vetoRow
    split_ifs
    · exact HR.row_low H ω y o hy
    · rfl
  row_index := by
    intro H ω y o hi
    unfold vetoRow
    split_ifs
    · exact HR.row_index H ω y o hi
    · rfl
  row_invalid := by
    intro H ω y o hy
    unfold vetoRow
    split_ifs with hcond
    · exact HR.row_invalid H ω y o (fun hvalid => hy ⟨hvalid, hcond⟩)
    · rfl
  row_sum := by
    intro H ω y hy hhigh
    simp only [vetoLayer] at hy
    simp only [vetoRow, if_pos hy.2]
    exact HR.row_sum H ω y hy.1 hhigh
  row_cap := by
    intro H ω y o
    exact (vetoRow_le X L b l t HR.row HR.row_nonneg H ω y o).trans (HR.row_cap H ω y o)
  row_support := by
    intro H ω y o hne
    unfold vetoRow at hne
    split_ifs at hne with hcond
    · exact HR.row_support H ω y o hne
    · exact (hne rfl).elim
  row_cost := by
    intro H ω y hy hhigh
    simp only [vetoLayer] at hy
    simp only [vetoRow, if_pos hy.2]
    exact HR.row_cost H ω y hy.1 hhigh
  row_local := vetoRow_local X L b l t hl HR.row HR.row_local

def vetoLowRows (L : X.CentreLayer5) {cL cH : ℝ} (LR : X.LowRows5 L cL cH)
    (b : OddRole5 n) (l : L.ht.hp.Loc) (t : Bool)
    (hl : l ∈ X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack)) :
    X.LowRows5 (vetoLayer X L b l t hl) cL cH :=
  { LR with
    row := vetoRow X L b l t LR.row
    row_nonneg := vetoRow_nonneg X L b l t LR.row LR.row_nonneg
    row_high := by
      intro H ω y o hy
      unfold vetoRow
      split_ifs
      · exact LR.row_high H ω y o hy
      · rfl
    row_index := by
      intro H ω y o hi
      unfold vetoRow
      split_ifs
      · exact LR.row_index H ω y o hi
      · rfl
    row_invalid := by
      intro H ω y o hy
      unfold vetoRow
      split_ifs with hcond
      · exact LR.row_invalid H ω y o (fun hvalid => hy ⟨hvalid, hcond⟩)
      · rfl
    row_sum := by
      intro H ω y hy hlow
      simp only [vetoLayer] at hy
      simp only [vetoRow, if_pos hy.2]
      exact LR.row_sum H ω y hy.1 hlow
    row_cap := by
      intro H ω y o
      exact (mul_le_mul_of_nonneg_left
        (vetoRow_le X L b l t LR.row LR.row_nonneg H ω y o) (Nat.cast_nonneg N)).trans (LR.row_cap H ω y o)
    row_support := by
      intro H ω y o hne
      unfold vetoRow at hne
      split_ifs at hne with hcond
      · exact LR.row_support H ω y o hne
      · exact (hne rfl).elim
    row_deletion := by
      intro H ω y hy hlow
      simp only [vetoLayer] at hy
      simp only [vetoRow, if_pos hy.2]
      exact LR.row_deletion H ω y hy.1 hlow
    row_local := vetoRow_local X L b l t hl LR.row LR.row_local
    long_vs_proxy := by
      intro H hH y x hlow
      apply le_trans _ (LR.long_vs_proxy H hH y x hlow)
      unfold FinProb.expect
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ ((X.centreLaw L.ht H).nonneg ω)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact vetoRow_le X L b l t LR.row LR.row_nonneg H ω y (0, x) }

/-- The missing adjacent-state distance bound would supply precisely the required scope inclusion. -/
theorem adjacent_scope_inclusion (L : X.CentreLayer5) (v : EvenRole5 n) (b : OddRole5 n)
    (hd : _root_.hammingDist (X.St.oneHot (X.St.stateOf b.1)) (X.siteOf v) ≤ 8) :
    X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack) ⊆
      X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8) := by
  intro l hl
  have hb := (Finset.mem_filter.mp hl).2
  change _root_.hammingDist l.1 (X.St.oneHot (X.St.stateOf b.1)) ≤ L.ht.hp.r + L.slack at hb
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (_root_.hammingDist_triangle l.1 (X.St.oneHot (X.St.stateOf b.1)) (X.siteOf v)).trans
    (Nat.add_le_add hb hd)

end
end HypercubeRamsey.Lane_sol_s05_even
