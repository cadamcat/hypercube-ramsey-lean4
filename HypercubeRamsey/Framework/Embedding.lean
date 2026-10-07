import HypercubeRamsey.Framework.Basic

/-!
# Embedding interface

A cube copy across the two host sides from injective maps of the even and the odd roles.
-/

namespace HypercubeRamsey

open OAI.HypercubeRamsey

/-- Even roles: an even number of coordinates equal to `true`. -/
def IsEvenRole {n : ℕ} (v : CubeVertex n) : Prop :=
  Even (Finset.univ.filter (fun i => v i = true)).card

/-- Even roles to the first side, odd roles to the second side. -/
theorem cube_copy_of_parts {n N : ℕ} {G : Fin N → Fin N → Prop}
    (fA : {v : CubeVertex n // IsEvenRole v} → Fin N)
    (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (hA : Function.Injective fA) (hB : Function.Injective fB)
    (hedge : ∀ a b, (cube n).Adj a.1 b.1 → G (fA a) (fB b)) :
    Nonempty ((cube n).Copy (crossGraph G)) := sorry

/-- Even roles to the second side, odd roles to the first side. -/
theorem cube_copy_of_parts_swap {n N : ℕ} {G : Fin N → Fin N → Prop}
    (fA : {v : CubeVertex n // IsEvenRole v} → Fin N)
    (fB : {v : CubeVertex n // ¬ IsEvenRole v} → Fin N)
    (hA : Function.Injective fA) (hB : Function.Injective fB)
    (hedge : ∀ a b, (cube n).Adj a.1 b.1 → G (fB b) (fA a)) :
    Nonempty ((cube n).Copy (crossGraph G)) := sorry

end HypercubeRamsey
