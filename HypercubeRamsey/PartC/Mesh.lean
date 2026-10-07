import HypercubeRamsey.PartC.Tiling

/-!
# F-Mesh: Kuhn grid and finite mesh interfaces

`KuhnSimplex` names the translated cube and coordinate ordering that define a
Kuhn simplex. `KuhnMesh` is the finite partition-of-unity interface consumed
by the internal solver; its local support clause fixes the required `D + 1`
active-vertex bound.
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- An integer grid vertex in `D` real coordinates. -/
abbrev KuhnGridVertex (D : ℕ) := Fin D → ℤ

/-- A Kuhn simplex is a grid cube together with an ordering of its axes. -/
structure KuhnSimplex (D : ℕ) where
  corner : KuhnGridVertex D
  order : Equiv.Perm (Fin D)

namespace KuhnSimplex

/-- The `t`th vertex along the ordered chain of a Kuhn simplex. -/
def vertex {D : ℕ} (S : KuhnSimplex D) (t : Fin (D + 1)) : KuhnGridVertex D :=
  fun j => S.corner j + if ∃ a : Fin D, a.val < t.val ∧ S.order a = j then 1 else 0

/-- All vertices in the ordered chain, before zero-weight vertices are removed. -/
def vertices {D : ℕ} (S : KuhnSimplex D) : Finset (KuhnGridVertex D) :=
  Finset.univ.image S.vertex

end KuhnSimplex

/-- X-Kuhn: barycentric coordinates on one Kuhn simplex. -/
structure KuhnBarycentric (D : ℕ) where
  simplex : KuhnSimplex D
  point : Fin D → ℝ
  spacing : ℝ
  spacing_pos : 0 < spacing
  weight : Fin (D + 1) → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  reconstruct : ∀ j,
    point j = spacing * ∑ i, weight i * ((simplex.vertex i j : ℤ) : ℝ)

/-- The nonzero local vertices of barycentric coordinates on a Kuhn simplex. -/
noncomputable def KuhnBarycentric.active {D : ℕ} (b : KuhnBarycentric D) : Finset (Fin (D + 1)) :=
  Finset.univ.filter fun i => 0 < b.weight i

/-- F-Mesh: finite, continuous Kuhn partition of unity with at most `D+1` active vertices. -/
structure KuhnMesh (D : ℕ) (K : Set (Fin D → ℝ)) (r : ℝ) where
  Vertex : Type
  [vertexFinite : Fintype Vertex]
  base : Vertex → K
  weight : Vertex → K → ℝ
  scale_pos : 0 < r
  continuous_weight : ∀ v, Continuous (weight v)
  nonneg : ∀ v p, 0 ≤ weight v p
  sum_one : ∀ p, ∑ v, weight v p = 1
  local_support : ∀ v p, 0 < weight v p →
    ∀ j, |p.1 j - (base v).1 j| ≤ r
  active_bound : ∀ p,
    (Finset.univ.filter fun v => 0 < weight v p).card ≤ D + 1

/-- The domain assumptions under which a Kuhn mesh is requested. -/
structure KuhnDomain (D : ℕ) (K : Set (Fin D → ℝ)) : Prop where
  nonempty : K.Nonempty
  compact : IsCompact K
  convex : Convex ℝ K

/-- D14.M: abstract mesh payload used for a tiling's cleaned corner supports. -/
structure Mesh {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) where
  V : Type
  [vFin : Fintype V]
  Param : Type
  dimension : ℕ
  base : V → Param
  wt : V → Param → ℝ
  corner : V → Fin 𝒯.m → Finset (Fin (T.S.N k))
  wt_nonneg : ∀ v p, 0 ≤ wt v p
  wt_sum_one : ∀ p, ∑ v, wt v p = 1
  active_bound : ∀ p,
    (Finset.univ.filter fun v => 0 < wt v p).card ≤ dimension + 1

end HypercubeRamsey
