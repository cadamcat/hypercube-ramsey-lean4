import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_probability

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Curry position/activation fields and combine the independent tuple/mask auxiliary law. -/
theorem regroup_pair_fields_pr {Z Loc Pos Act Tu Ms : Type*}
    [Fintype Z] [DecidableEq Z] [Fintype Loc] [DecidableEq Loc]
    [Fintype Pos] [Fintype Act] [Fintype Tu] [Fintype Ms]
    (P : Z × Loc → FinProb Pos) (A : Z × Loc → FinProb Act)
    (T : FinProb Tu) (S : FinProb Ms)
    (F : (Z → Loc → Pos) → Tu × Ms → (Z → Loc → Act) → Prop) :
    ((((FinProb.pi P).prod T).prod S).prod (FinProb.pi A)).pr
      (fun ω => F (fun z loc => ω.1.1.1 (z, loc)) (ω.1.1.2, ω.1.2)
        (fun z loc => ω.2 (z, loc))) =
      (((FinProb.pi (fun z => FinProb.pi (fun loc => P (z, loc)))).prod (T.prod S)).prod
        (FinProb.pi (fun z => FinProb.pi (fun loc => A (z, loc))))).pr
          (fun ω => F ω.1.1 ω.1.2 ω.2) := by
  classical
  rw [pr_indicator, pr_indicator]
  simp_rw [prod_expect]
  have hA (W : Z × Loc → Pos) (tu : Tu) (ms : Ms) :
      (FinProb.pi A).expect (fun V => if F (fun z loc => W (z, loc)) (tu, ms)
        (fun z loc => V (z, loc)) then (1 : ℝ) else 0) =
      (FinProb.pi (fun z => FinProb.pi (fun loc => A (z, loc)))).expect
        (fun V => if F (fun z loc => W (z, loc)) (tu, ms) V then (1 : ℝ) else 0) :=
    pi_curry_expect A (fun V => if F (fun z loc => W (z, loc)) (tu, ms) V then (1 : ℝ) else 0)
  simp_rw [hA]
  exact pi_curry_expect P (fun W => T.expect (fun tu => S.expect (fun ms =>
    (FinProb.pi (fun z => FinProb.pi (fun loc => A (z, loc)))).expect
      (fun V => if F W (tu, ms) V then (1 : ℝ) else 0))))

end HypercubeRamsey.Lane_sol_s10_d2
