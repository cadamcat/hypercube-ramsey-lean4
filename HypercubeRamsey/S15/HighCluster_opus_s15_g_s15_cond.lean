import HypercubeRamsey.S15.ClusterNodes_q_s15_c2

namespace HypercubeRamsey.S15.Lane_q_s15_cond

theorem heq_of_dependent_apply {α : Sort*} {β : α → Sort*}
    (f : ∀ a, β a) {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

end HypercubeRamsey.S15.Lane_q_s15_cond
