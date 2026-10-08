import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_probability

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- A uniform one-slice estimate applies when its selector reads the other slices. -/
theorem uniform_slice_event_bound {Z Pos Act Aux El : Type}
    [Fintype Z] [DecidableEq Z] [Fintype Pos] [Fintype Act] [Fintype Aux]
    (P : FinProb Pos) (A : FinProb Act) (Q : FinProb Aux)
    (F : Pos → Act → El → Prop) (ε : ℝ)
    (hbound : ∀ (B : Type) [Fintype B] (R : FinProb B) (Esel : Pos → B → El),
      ((P.prod R).prod A).pr (fun ω => F ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) ≤ ε)
    (z : Z) (Esel : (Z → Pos) → Aux → El) :
    (((FinProb.pi (fun _ : Z => P)).prod Q).prod (FinProb.pi (fun _ : Z => A))).pr
      (fun ω => F (ω.1.1 z) (ω.2 z) (Esel ω.1.1 ω.1.2)) ≤ ε := by
  classical
  let R := (FinProb.pi (fun _ : {z' : Z // z' ≠ z} => P)).prod Q
  let E' : Pos → ({z' : Z // z' ≠ z} → Pos) × Aux → El :=
    fun pos rest => Esel (insertField z pos rest.1) rest.2
  have hb := hbound _ R E'
  have heq :
      (((FinProb.pi (fun _ : Z => P)).prod Q).prod (FinProb.pi (fun _ : Z => A))).pr
        (fun ω => F (ω.1.1 z) (ω.2 z) (Esel ω.1.1 ω.1.2)) =
      ((P.prod R).prod A).pr (fun ω => F ω.1.1 ω.2 (E' ω.1.1 ω.1.2)) := by
    rw [pr_indicator, prod_expect, prod_expect]
    dsimp only
    have hact (pos : Z → Pos) (aux : Aux) :
        (FinProb.pi (fun _ : Z => A)).expect
          (fun acts => if F (pos z) (acts z) (Esel pos aux) then (1 : ℝ) else 0) =
        A.expect (fun act => if F (pos z) act (Esel pos aux) then (1 : ℝ) else 0) :=
      pi_coordinate_expect (fun _ : Z => A) z
        (fun act => if F (pos z) act (Esel pos aux) then (1 : ℝ) else 0)
    simp_rw [hact]
    rw [pi_split_coordinate_expect (fun _ : Z => P) z]
    rw [pr_indicator, prod_expect, prod_expect]
    simp_rw [R, prod_expect]
    simp [E', insertField]
  exact heq.trans_le hb

end HypercubeRamsey.Lane_sol_s10_d2
