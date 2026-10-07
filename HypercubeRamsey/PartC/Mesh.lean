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

/-- D14.M: mesh of the parameter polytope of a tiling, with the cleaned corner supports stored at its
vertices (sections/14 lines 9–14).

A parameter point carries one input law and one price vector per patch (`paramLaw`, `paramPrice`;
the input laws lie in the capped domain `Capᵢ`). Barycentric weights are continuous, a vertex with
positive weight at `p` has its base point within the L13.4 stability radius `n⁻³` (per-patch `ℓ¹`)
and within price distance `1/(n Mᵢ)` of `p`, and at most `D + 1 ≤ 2N + 1` vertices are active,
since the polytope has dimension `D = ∑ᵢ 2|Yᵢ| ≤ 2N` (blueprint §5.1(1); needed by L14.3). -/
structure Mesh {κ : CConsts} {T : Stage} {k : ℕ} (𝒯 : Tiling κ T k) where
  V : Type
  [vFin : Fintype V]
  Param : Type
  [paramTop : TopologicalSpace Param]
  paramLaw : Param → Fin 𝒯.m → Law (T.S.N k)
  paramPrice : Param → Fin 𝒯.m → Fin (T.S.N k) → ℝ
  paramLaw_supp : ∀ p i, (paramLaw p i).SupportedIn (𝒯.P i).Y
  paramLaw_cap : ∀ p i y,
    ((𝒯.P i).M : ℝ) * (paramLaw p i).w y ≤ Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
  paramPrice_simplex : ∀ p i, (∀ y, 0 ≤ paramPrice p i y) ∧ (∀ y, y ∉ (𝒯.P i).Y → paramPrice p i y = 0) ∧
    ∑ y, paramPrice p i y = 1
  base : V → Param
  wt : V → Param → ℝ
  corner : V → Fin 𝒯.m → Finset (Fin (T.S.N k))
  wt_cont : ∀ v, Continuous (wt v)
  wt_nonneg : ∀ v p, 0 ≤ wt v p
  wt_sum_one : ∀ p, ∑ v, wt v p = 1
  local_law : ∀ v p, 0 < wt v p → ∀ i,
    ∑ y, |(paramLaw p i).w y - (paramLaw (base v) i).w y| ≤ (T.S.n k : ℝ) ^ (-3 : ℝ)
  local_price : ∀ v p, 0 < wt v p → ∀ i y,
    |paramPrice p i y - paramPrice (base v) i y| ≤ 1 / ((T.S.n k : ℝ) * (𝒯.P i).M)
  active_bound : ∀ p,
    (Finset.univ.filter fun v => 0 < wt v p).card ≤ 2 * T.S.N k + 1

instance instMeshVFintype {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (mesh : Mesh 𝒯) :
    Fintype mesh.V := mesh.vFin

instance instMeshParamTop {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k} (mesh : Mesh 𝒯) :
    TopologicalSpace mesh.Param := mesh.paramTop

end HypercubeRamsey
