import HypercubeRamsey.S07.Experiment

/-!
# L7.1a: geometry facts

Source: `sections/07-…tex`, lines 55–82, 172, 183, 211–214, 233–237, 253, 273–274, 283, 341–345.  The four nodes
hold for every grid geometry; `geomFacts` bundles them for the later stages.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey

variable {d : ℝ} {n s ℓ q : ℕ}

/-- L7.1a(i)–(ii) (07:61–63, 79–82, 211–214, 235–237): a coordinate flip moves the cell by distance at most one
and the flipped vertex's cell is listed by the original cell (a special flip keeps the key or moves one bin, an
auxiliary flip changes one auxiliary bit, a residual flip changes neither); only the `sℓ` special coordinates
change the grid key; `|E(g)| ≤ 2s`; `q + 1` own words; the listed names are distinct. -/
theorem grid_local (Γ : GridGeom d n s ℓ q) : GeomLocal Γ := by
  sorry

/-- Ball sizes (07:172, 253, 283, 355): radius-`R` balls have at most `(2s+1)^R` keys, `(q+1)^R` auxiliary words
and `(2s+q+1)^R` cells. -/
theorem grid_balls (Γ : GridGeom d n s ℓ q) : GeomBalls Γ := by
  sorry

/-- L7.1a(iii) (07:65–68): with a residual coordinate, each parity class has `2^{n-1}` vertices, and the vertices
of one parity reading the cell `(g, t)` are the fraction `2^{-q} ∏_r Pr[Bin(ℓ,1/2) ∈ bin g_r]` of the class; the
key masses sum to one and are at most `(2n^{-d/4})^s`. -/
theorem grid_counts (Γ : GridGeom d n s ℓ q) : GeomCounts Γ := by
  sorry

/-- L7.1a(iv) (07:183, 273–274, 341–345): near fractions for the three moment estimates, from the exact counts
and the ball sizes. -/
theorem grid_near (Γ : GridGeom d n s ℓ q) (hB : GeomBalls Γ) (hC : GeomCounts Γ) : GeomNear Γ := by
  sorry

/-- L7.1a: all geometry facts. -/
theorem geomFacts (Γ : GridGeom d n s ℓ q) : GeomFacts Γ :=
  ⟨grid_local Γ, grid_balls Γ, grid_counts Γ, grid_near Γ (grid_balls Γ) (grid_counts Γ)⟩

end HypercubeRamsey.S07
