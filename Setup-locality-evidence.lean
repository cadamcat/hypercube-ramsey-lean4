import HypercubeRamsey.S05.Even
import HypercubeRamsey.S05.Even_setup_veto_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

theorem evenSetup_forces_star_validity (L : X.CentreLayer5) {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L) (ES : X.EvenSetup5 LR HR)
    (H : X.KeyHist) (ω ω' : X.CΩ L.ht) (O : OddRole5 n → X.OddOut)
    (hs : L.success H ω) (hB : X.BudgetOK HR H ω O) (v : EvenRole5 n) (c : X.CRef L.ht)
    (hc : X.evenRefOf (L.elig H) H ω v = some c)
    (hag : ∀ l ∈ X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8), ω l = ω' l)
    (b : OddRole5 n) (hb : b ∈ Setup5.star v) : L.valid H ω' b := by
  have hgate := ES.gate_success H ω O hs hB v c hc
  have heq := ES.gate_local H v c O ω ω' hag
  dsimp only at heq
  have hgate' : ES.gate H v c ω' O := heq ▸ hgate
  exact ES.gate_valid H v c ω' O hgate' b hb

/-- A validity veto in an odd scope outside an adjacent even scope prevents a local even gate.
All modified layers and rows satisfy their frozen structure contracts (see vetoLayer/Rows). -/
theorem veto_obstructs_evenSetup (L : X.CentreLayer5) {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
    (H : X.KeyHist) (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut)
    (hs : L.success H ω) (hB : X.BudgetOK HR H ω O)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht)
    (hc : X.evenRefOf (L.elig H) H ω v = some c) (hb : b ∈ Setup5.star v)
    (l : L.ht.hp.Loc)
    (hl : l ∈ X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack))
    (hlout : l ∉ X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8))
    :
    ¬ Nonempty (X.EvenSetup5 (vetoLowRows X L LR b l (Setup5.pos ω l) hl) (vetoHighRows X L HR b l (Setup5.pos ω l) hl)) := by
  intro ⟨ES⟩
  let ω' : X.CΩ L.ht := Function.update ω l (!(Setup5.pos ω l), (ω l).2)
  have hcond (y : OddRole5 n) : vetoCondition X L b l (Setup5.pos ω l) ω y := fun _ => rfl
  have hbudget : X.BudgetOK (vetoHighRows X L HR b l (Setup5.pos ω l) hl) H ω O := by
    intro w
    have hcost (y : OddRole5 n) :
        X.budgetCost (vetoHighRows X L HR b l (Setup5.pos ω l) hl) H ω w y (O y) = X.budgetCost HR H ω w y (O y) := by
      unfold Setup5.budgetCost
      simp only [vetoHighRows, vetoLayer, vetoRow, if_pos (hcond y)]
      split_ifs <;> cases he : X.evenRefOf (L.elig H) H ω w <;> simp [he]
    change (∑ y, X.budgetCost (vetoHighRows X L HR b l (Setup5.pos ω l) hl) H ω w y (O y)) ≤ _
    simp_rw [hcost]
    exact hB w
  have hag : ∀ l' ∈ X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8), ω l' = ω' l' := by
    intro l' hl'
    have hne : l' ≠ l := by intro he; subst l'; exact hlout hl'
    exact (Function.update_of_ne hne _ _).symm
  have hvalid := evenSetup_forces_star_validity X (vetoLayer X L b l (Setup5.pos ω l) hl)
    (vetoLowRows X L LR b l (Setup5.pos ω l) hl) (vetoHighRows X L HR b l (Setup5.pos ω l) hl) ES H ω ω' O ⟨hs, rfl⟩ hbudget v c hc hag b hb
  have hbad := hvalid.2 rfl
  change Setup5.pos ω' l = Setup5.pos ω l at hbad
  simp [ω', Setup5.pos] at hbad

theorem universalEvenSetup_forces_scope_inclusion (L : X.CentreLayer5) {cL cH : ℝ}
    (LR : X.LowRows5 L cL cH) (HR : X.HighRows5 L)
    (hgen : ∀ (L' : X.CentreLayer5) (LR' : X.LowRows5 L' cL cH) (HR' : X.HighRows5 L'),
      Nonempty (X.EvenSetup5 LR' HR'))
    (H : X.KeyHist) (ω : X.CΩ L.ht) (O : OddRole5 n → X.OddOut)
    (hs : L.success H ω) (hB : X.BudgetOK HR H ω O)
    (v : EvenRole5 n) (b : OddRole5 n) (c : X.CRef L.ht)
    (hc : X.evenRefOf (L.elig H) H ω v = some c) (hb : b ∈ Setup5.star v) :
    X.scopeBall (h := L.ht) b.1 (L.ht.hp.r + L.slack) ⊆
      X.scopeBall (h := L.ht) v.1 (L.ht.hp.r + L.slack + 8) := by
  intro l hl
  by_contra hlout
  exact veto_obstructs_evenSetup X L LR HR H ω O hs hB v b c hc hb l hl hlout
    (hgen _ (vetoLowRows X L LR b l (Setup5.pos ω l) hl) (vetoHighRows X L HR b l (Setup5.pos ω l) hl))

#print axioms evenSetup_forces_star_validity
#print axioms veto_obstructs_evenSetup
#print axioms universalEvenSetup_forces_scope_inclusion
end
end HypercubeRamsey.Lane_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even
open OAI.HypercubeRamsey

def gapEvenImage : CubeVertex 20 := fun _ => false
def gapOddImage : CubeVertex 20 := fun i => decide (i.val < 9)
def gapLocation : CubeVertex 20 := fun i => decide (i.val < 14)

/-- With nine parity-tag coordinates, an odd radius-5 scope reaches beyond the even radius-13 scope. -/
theorem nine_coordinate_scope_gap :
    _root_.hammingDist gapLocation gapOddImage = 5 ∧
    _root_.hammingDist gapLocation gapEvenImage = 14 ∧
    ¬ _root_.hammingDist gapLocation gapEvenImage ≤ 5 + 8 := by
  decide

#print axioms nine_coordinate_scope_gap
end HypercubeRamsey.Lane_sol_s05_even
