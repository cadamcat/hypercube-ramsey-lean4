import HypercubeRamsey.S10.Split_opus_s10_tagged_sol_s10_d2_probability

namespace HypercubeRamsey.Lane_sol_s10_d2

open Classical OAI.HypercubeRamsey HypercubeRamsey.S10 Filter
open scoped BigOperators

/-- Independent later coordinates do not change a position-only event. -/
theorem first_of_five_pr {α β γ ξ η : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype ξ] [Fintype η]
    (P : FinProb α) (Q : FinProb β) (R : FinProb γ) (S : FinProb ξ) (T : FinProb η)
    (A : α → Prop) :
    ((((P.prod Q).prod R).prod S).prod T).pr (fun x => A x.1.1.1.1) = P.pr A := by
  calc
    ((((P.prod Q).prod R).prod S).prod T).pr (fun x => A x.1.1.1.1) =
      (((P.prod Q).prod R).prod S).pr (fun x => A x.1.1.1) :=
        p10_1k_pr_prod_fst (((P.prod Q).prod R).prod S) T (fun x => A x.1.1.1)
    _ = ((P.prod Q).prod R).pr (fun x => A x.1.1) :=
      p10_1k_pr_prod_fst ((P.prod Q).prod R) S (fun x => A x.1.1)
    _ = (P.prod Q).pr (fun x => A x.1) :=
      p10_1k_pr_prod_fst (P.prod Q) R (fun x => A x.1)
    _ = P.pr A := p10_1k_pr_prod_fst P Q A

end HypercubeRamsey.Lane_sol_s10_d2
