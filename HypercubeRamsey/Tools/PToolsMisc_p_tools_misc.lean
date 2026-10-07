import Mathlib

namespace HypercubeRamsey
namespace PToolsMisc

theorem ite_decidable_irrel {α : Sort*} (p : Prop)
    (d₁ d₂ : Decidable p) (a b : α) : @ite α p d₁ a b = @ite α p d₂ a b := by
  cases d₁ <;> cases d₂ <;> simp_all

theorem sum_sub_univ {α : Type*} [Fintype α] (f g : α → ℝ) :
    (∑ x, (f x - g x)) = (∑ x, f x) - ∑ x, g x := by
  classical
  simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

end PToolsMisc
end HypercubeRamsey
