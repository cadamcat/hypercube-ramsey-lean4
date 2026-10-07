import HypercubeRamsey.S09.Defs
import HypercubeRamsey.Tools.Finner

/-!
# Shared Section 9 tools requested by this lane

TS-B3's generalized height lemma is not present under `HypercubeRamsey/S03/Height/`
on this branch.  `height_general9` records the Section 9 instance needed from
that shared scale induction; `p92_map1` in `Nodes.lean` assembles directly
from it.  The witness exposes active eligibility, all three crowd regions,
the level window, and full-cube distance-two regularity.
-/

namespace HypercubeRamsey

open scoped BigOperators
open OAI.HypercubeRamsey Classical

/-- SHARED: X-Finner (PART-B.md §4). Finite Finner inequality for a product of independent finite laws. -/
theorem finner_product {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {Ω : κ → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (P : ∀ j, FinProb (Ω j)) (S : ι → Finset κ)
    (f : ι → (∀ j, Ω j) → ℝ) (d : ℕ) (hd : 0 < d)
    (hdep : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ d)
    (hdepends : ∀ i, FinProb.DependsOn (f i) (S i))
    (hnonneg : ∀ i ω, 0 ≤ f i ω) :
    FinProb.expect (FinProb.pi P) (fun ω => ∏ i, f i ω) ≤
      ∏ i, Real.rpow
        (FinProb.expect (FinProb.pi P) (fun ω => (f i ω) ^ d))
        (1 / (d : ℝ)) := by
  classical
  simpa [one_div] using xFinner P S d hd hdep f hnonneg hdepends

structure CenterID9 (m n H : ℕ) where
  slice : CubeVertex m
  location : CubeVertex n
  level : Fin (H + 1)
  deriving DecidableEq

def specialWord9 {n m : ℕ} (hmn : m ≤ n) (v : CubeVertex n) : CubeVertex m :=
  fun i => v (Fin.castLE hmn i)

def residualDistance9 {n : ℕ} (m : ℕ) (u v : CubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => m ≤ i.val ∧ u i ≠ v i)).card

def wordDistance9 {m : ℕ} (u v : CubeVertex m) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => u i ≠ v i)).card

def HeightGood9 {n m H : ℕ} (hmn : m ≤ n) (active : Finset (CenterID9 m n H))
    (r : ℕ) (χ σ ε : ℝ) (v : CubeVertex n) (ℓ : Fin (H + 1)) : Prop :=
  (∃ c ∈ active, c.slice = specialWord9 hmn v ∧
    residualDistance9 m c.location v ≤ r ∧ c.level = ℓ) ∧
  ((active.filter (fun c => c.slice = specialWord9 hmn v ∧
      residualDistance9 m c.location v ≤ r ∧ Nat.dist c.level.val ℓ.val ≤ 2)).card : ℝ) ≤
    (n : ℝ) ^ (χ / 2) ∧
  ((active.filter (fun c => wordDistance9 c.slice (specialWord9 hmn v) = 1 ∧
      residualDistance9 m c.location v ≤ r - 1 ∧ Nat.dist c.level.val ℓ.val ≤ 2)).card : ℝ) ≤
    (n : ℝ) ^ (χ / 2) ∧
  ((active.filter (fun c => c.slice = specialWord9 hmn v ∧
      residualDistance9 m c.location v ≤ r + 1 ∧ Nat.dist c.level.val ℓ.val ≤ 2)).card : ℝ) ≤
    (n : ℝ) ^ (1 - σ + ε)

structure HeightWitness9 (P : Params9) (n : ℕ) where
  specialBits : ℕ
  specialBits_le : specialBits ≤ n
  specialBudget : P.Ss (n : ℝ) < (specialBits : ℝ) * Real.log 2
  radius : ℕ
  levels : ℕ
  levels_pos : 0 < levels
  active : Finset (CenterID9 specialBits n levels)
  ε : ℝ
  ε_pos : 0 < ε
  ε_lt_σ : ε < (P.σ : ℝ)
  height : CubeVertex n → Fin (levels + 1)
  height_lt : ∀ v, (height v).val < levels
  height_good : ∀ v,
    HeightGood9 specialBits_le active radius P.χ P.σ ε v (height v)
  distance_two_regular : ∀ u v,
    (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card ≤ 2 →
      Nat.dist (height u).val (height v).val ≤ 1

noncomputable def seenIDs9 {n m H : ℕ}
    (c : CubeVertex n → CenterID9 m n H) (b : CubeVertex n) :
    Finset (CenterID9 m n H) :=
  (Finset.univ.filter (fun a : CubeVertex n => (cube n).Adj a b)).image c

/-- SHARED: F-HeightGeneral (TS-B3; PART-B.md §3.9, §5). The Section 9
instantiation needed here: under the base hole/crowd tails, cross-slice overlap
bound, and degraded threshold gaps, obtain active centres and good heights
for every cube site, with levels differing by at most one at full-cube
distance at most two. The `HeightWitness9` fields make the three crowd regions
and level window explicit. -/
theorem height_general9 (P : Params9) (hP : P.Valid) :
    ∃ n₀, ∀ n, n₀ ≤ n → Nonempty (HeightWitness9 P n) := by
  sorry

end HypercubeRamsey
