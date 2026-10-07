import HypercubeRamsey.S05
import Lean

open HypercubeRamsey OAI.HypercubeRamsey
open Classical

namespace HypercubeRamsey.Lane_sol_fix2_s05

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

-- The fixed height family is feasible for every permitted alpha, independently of n.
theorem height_family_feasible (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 50) :
    HDAdmissible 10 (α / 10000) (α / 2000) (α / 1000000) (α / 100000)
      (1 - α / 100000) (α / 20000) (1 / 2) 2 8 := by
  constructor
  · norm_num
  · exact ⟨by linarith, by linarith, by linarith⟩
  · norm_num
  · exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith, by linarith⟩
  · norm_num

theorem fixed_slack_gap (h : X.HeightChoice5) : h.ζ - h.σ = 9 * X.p.alpha / 1000000 := by
  rcases h.fixed with ⟨_, _, hσ, hζ, _, _⟩
  rw [hσ, hζ]
  ring

theorem height_extra_constraints (α : ℝ) (hα : 0 < α) (hα' : α < 1 / 50) :
    9 / 10 < 1 - α / 100000 ∧ α / 2000 < α / 1000 := by
  constructor <;> linarith

-- A zero raw base, as in the identity-adjacency countermodel, cannot be locally valid.
theorem unsupported_base_invalid (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (y : OddRole5 n) (hzero : X.baseLaw.w H.1 = 0) : ¬ L.valid H ω y := by
  intro hv
  exact L.valid_base_support H ω y hv hzero

-- The same exclusion applies to zero-mass true paths, even at a supported base.
theorem unsupported_path_invalid (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (y : OddRole5 n)
    (hzero : X.step3PostOn H (X.actualRecord (L.elig H) H ω y) (Setup5.arraysOf ω) none
      (H.2 (X.g.roleKey (X.p.J n) y.1)) = 0) : ¬ L.valid H ω y := by
  intro hv
  have hp := L.valid_path_support H ω y hv
  rw [hzero] at hp
  exact (lt_irrefl (0 : ℝ)) hp

theorem unsupported_block_invalid (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (y : OddRole5 n) (c : L.ht.hp.Loc × X.Ty)
    (hc : c ∈ (X.actualRecord (L.elig H) H ω y).2.1)
    (i : Fin (X.p.typeBlocks n c.2))
    (hzero : X.blockWeight H c.2 c.2.2.1 (Setup5.arraysOf ω c i) = 0) : ¬ L.valid H ω y := by
  intro hv
  exact L.valid_block_support H ω y hv c hc i hzero

theorem overcrowded_star_invalid (L : X.CentreLayer5) (H : X.KeyHist) (ω : X.CΩ L.ht)
    (y : OddRole5 n) (a : EvenRole5 n) (ha : a ∈ Setup5.evenNbrs y) (j : Fin (L.ht.hp.H + 1))
    (hover : 2 * L.ht.hp.lam < ((Finset.univ.filter fun u : CubeVertex L.ht.hp.d =>
      Setup5.pos ω (u, j) = true ∧ hammingDist u (X.siteOf a) ≤ L.ht.hp.r).card : ℝ)) :
    ¬ L.valid H ω y := by
  intro hv
  exact (not_lt_of_ge (L.valid_counts H ω y hv a ha j)) hover

-- A fixed radius cannot cover the entire sign cube as m grows.
theorem fixed_radius_not_full (C m : ℕ) (hm : C < Nat.sqrt m) (hs : 0 < Nat.sqrt m) :
    C * Nat.sqrt m < m := by
  calc
    C * Nat.sqrt m < Nat.sqrt m * Nat.sqrt m := Nat.mul_lt_mul_of_pos_right hm hs
    _ ≤ m := Nat.sqrt_le m

-- A locality certificate identifies any two histories agreeing on its actual scope.
theorem proxy_scope_identity (C : ℕ) (b : X.Base) (hi : X.HighHid)
    (Z : X.LowHid → OddRole5 n → Fin N → ℝ) (hZ : X.ProxyMeanData5 C b hi Z)
    (r : OddRole5 n) (lo lo' : X.LowHid)
    (heq : ∀ k, hammingDist k.2.1 (X.g.sign r.1) ≤ C * Nat.sqrt (X.p.m n) → lo k = lo' k) :
    Z lo r = Z lo' r := by
  exact hZ.locality r lo lo' (fun k hk => heq k (Finset.mem_filter.mp hk).2)

end HypercubeRamsey.Lane_sol_fix2_s05

#print axioms HypercubeRamsey.Lane_sol_fix2_s05.height_family_feasible
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.fixed_slack_gap
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.height_extra_constraints
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.unsupported_base_invalid
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.unsupported_path_invalid
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.unsupported_block_invalid
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.overcrowded_star_invalid
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.fixed_radius_not_full
#print axioms HypercubeRamsey.Lane_sol_fix2_s05.proxy_scope_identity
#print axioms HypercubeRamsey.Setup5.L5_1g_rows
#print axioms HypercubeRamsey.Setup5.L5_1k_rows
#print axioms HypercubeRamsey.Setup5.L5_1l2
#print axioms HypercubeRamsey.L5_1_rows
#print axioms HypercubeRamsey.L5_1_consumed

-- Reuse the earlier audit's compiled type/value walk: all 28 assembly nodes must remain consumed.
#eval show Lean.MetaM Unit from do
  let nodes : Array Lean.Name := #[
    `HypercubeRamsey.D5_1_params, `HypercubeRamsey.L5_1a, `HypercubeRamsey.L5_1b,
    `HypercubeRamsey.L5_1e0, `HypercubeRamsey.L5_1e_cover,
    `HypercubeRamsey.Setup5.L5_1c, `HypercubeRamsey.Setup5.L5_1d,
    `HypercubeRamsey.Setup5.L5_1d_bounds, `HypercubeRamsey.Setup5.L5_1f,
    `HypercubeRamsey.Setup5.L5_1e_count, `HypercubeRamsey.Setup5.L5_1h1,
    `HypercubeRamsey.Setup5.L5_1h2, `HypercubeRamsey.Setup5.L5_1h3,
    `HypercubeRamsey.Setup5.L5_1h4, `HypercubeRamsey.Setup5.L5_1h5,
    `HypercubeRamsey.Setup5.L5_1l1, `HypercubeRamsey.Setup5.L5_1l2,
    `HypercubeRamsey.Setup5.L5_1j, `HypercubeRamsey.Setup5.L5_1g_rows,
    `HypercubeRamsey.L5_1g_common_high_law, `HypercubeRamsey.Setup5.L5_1k_rows,
    `HypercubeRamsey.Setup5.L5_1l3, `HypercubeRamsey.L5_1m,
    `HypercubeRamsey.Setup5.L5_1m_inputs, `HypercubeRamsey.Setup5.L5_1n_setup,
    `HypercubeRamsey.Setup5.L5_1n, `HypercubeRamsey.Setup5.L5_1n_rows,
    `HypercubeRamsey.Setup5.L5_1o]
  let mut seen : Std.HashSet Lean.Name := {}
  let mut todo : Array Lean.Name := #[`HypercubeRamsey.L5_1_consumed]
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let ci ← Lean.getConstInfo name
    let refs := ci.type.getUsedConstants ++
      (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
    for c in refs do
      if c.toString.startsWith "HypercubeRamsey." || c.toString.startsWith "_private.HypercubeRamsey." then
        todo := todo.push c
  for name in nodes do
    unless seen.contains name do throwError "Unused Section 5 node: {name}"
  Lean.logInfo m!"All {nodes.size} Section 5 nodes are consumed."
