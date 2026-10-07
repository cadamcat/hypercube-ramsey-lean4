import HypercubeRamsey.S05.Parents

/-!
# D5.3 and D5.5: chunk/sign keys and one-hot state geometry

The chunk/sign certificate and state encoding are interfaces over their ambient finite sets.  They retain
the bounds and adjacency facts needed by Sections 5 and 6 without fixing the caller's parent prior.
-/

namespace HypercubeRamsey

open Classical OAI.HypercubeRamsey

/-- A hidden-column key: coarse key, majority-sign vector, and low severity (`none` is high severity). -/
structure ColumnKey5 (Coarse : Type*) (m : ℕ) where
  coarse : Coarse
  signs : Fin m → Bool
  severity : Option ℕ
  deriving DecidableEq

/-- A finite chunk/sign layout together with the geometric facts about its keys. -/
structure ChunkSignCertificate5 (Vertex Coarse : Type*) [Fintype Vertex] (m n : ℕ) where
  layout : ChunkSignData5 Vertex Coarse m
  measure : FinProb Vertex
  coarseBin : Vertex → Coarse
  coarseCandidates : Vertex → Finset Coarse
  columnKey : Vertex → ColumnKey5 Coarse m
  paddedKeys : Vertex → Finset (ColumnKey5 Coarse m)
  parity_mass : ∀ c, measure.pr (fun v => layout.parity v = c) = 1 / 2
  signs_uniform_on_parity : ∀ c t,
    measure.pr (fun v => layout.parity v = c ∧ layout.sign v = t) =
      measure.pr (fun v => layout.parity v = c) / 2 ^ m
  severity_tail : ∀ h, 1 ≤ h → h ≤ m →
    measure.pr (fun v => h ≤ layout.severity v) ≤ (n : ℝ) ^ (-(13 / 100 : ℝ) * h)
  boundary_small : measure.pr layout.boundary ≤ (n : ℝ) ^ (-(5 / 100 : ℝ))
  own_coarse_is_candidate : ∀ v, coarseBin v ∈ coarseCandidates v
  adjacent_coarse_is_candidate : ∀ v u, layout.adjacent v u →
    coarseBin u ∈ coarseCandidates v
  adjacent_key_is_padded : ∀ v u, layout.adjacent v u → columnKey u ∈ paddedKeys v

/-- Uniform law on the vertices of the Boolean cube. -/
noncomputable def uniformCube5 (n : ℕ) : FinProb (CubeVertex n) :=
  FinProb.uniform Finset.univ (Finset.univ_nonempty)

/-- L5.1b: the cube's coarse bins and majority signs have the rarity and neighbor-cover properties.

The construction keeps the 300 coarse chunks, the odd fine chunks, the `5.5` interface threshold, and the
padded hidden-key list used by each even type. -/
theorem L5_1b (γ K' χ : ℝ) (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ C : ChunkSignCertificate5 (CubeVertex n) (Fin 300) (p.m n) n,
        C.measure = uniformCube5 n := by
  sorry

/-- A state quotient with its one-hot embedding and the bounded odd/even neighborhood geometry. -/
structure CubeStateEncoding5 (n s d J : ℕ) where
  stateOf : CubeVertex n → Fin s
  oneHot : Fin s → Fin d → Bool
  evenState : Fin s → Prop
  stateKey : Fin s → ℕ
  severity : Fin s → ℕ
  neighbors : Fin s → Finset (Fin s)
  state_edge : ∀ u v, (cube n).Adj u v → stateOf v ∈ neighbors (stateOf u)
  parity_exact : ∀ v, evenState (stateOf v) ↔ IsEvenRole v
  degree_linear : ∃ C : ℝ, 0 ≤ C ∧ ∀ v, (neighbors v).card ≤ C * n
  two_even_distance : ∀ b u v, u ∈ neighbors b → v ∈ neighbors b →
    evenState u → evenState v →
      (Finset.univ.filter (fun i => oneHot u i ≠ oneHot v i)).card ≤ 8
  low_high_neighbors_coalesce : ∀ b, ∀ u v,
    u ∈ neighbors b → v ∈ neighbors b →
      severity u ≤ J → severity v ≤ J → stateKey u = stateKey v

/-- L5.1e0: the count-state quotient has dimension `(1+o(1))n`, exact parity, bounded degree, and
ambient distance at most eight between even neighbors of one odd state. -/
theorem L5_1e0 (γ K' χ : ℝ) (p : Params5 γ K' χ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ ε : ℝ, 0 < ε →
      ∃ s d : ℕ, ∃ C : CubeStateEncoding5 n s d (p.J n),
        (d : ℝ) ≤ (1 + ε) * n := by
  sorry

end HypercubeRamsey
