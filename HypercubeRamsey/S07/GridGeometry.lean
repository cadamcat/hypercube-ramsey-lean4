import HypercubeRamsey.Framework.Basic

/-!
# L7.1a: grid geometry

The geometry records disjoint special chunks, auxiliary coordinates, a residual coordinate, and monotone
binning maps whose binomial masses are small. The bin sizes and coordinate counts use the Section 7 exponents.
-/

namespace HypercubeRamsey.S07

open OAI.HypercubeRamsey

/-- A grid partition of cube coordinates with small binomial mass in every bin. -/
structure GridGeom (d : ℝ) (n s ℓ q : ℕ) where
  chunk : Fin s → Finset (Fin n)
  aux : Finset (Fin n)
  chunk_card : ∀ r, (chunk r).card = ℓ
  chunks_disjoint : Pairwise fun r r' => Disjoint (chunk r) (chunk r')
  aux_card : aux.card = q
  aux_disjoint : ∀ r, Disjoint aux (chunk r)
  residual_nonempty : ∃ j : Fin n, j ∉ aux ∧ ∀ r, j ∉ chunk r
  bins : Fin s → ℕ
  bin : ∀ r, Fin (ℓ + 1) → Fin (bins r)
  bin_monotone : ∀ r k k', k.val ≤ k'.val → (bin r k).val ≤ (bin r k').val
  bin_surjective : ∀ r, Function.Surjective (bin r)
  bin_mass : ∀ r b,
    (∑ k : Fin (ℓ + 1),
      if bin r k = b then ((Nat.choose ℓ k.val : ℕ) : ℝ) / (2 : ℝ) ^ ℓ else 0) ≤
        2 * (n : ℝ) ^ (-(d / 4))

/-- A key is one bin index for each special chunk. -/
abbrev GridGeom.Key {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  ∀ r, Fin (Γ.bins r)

/-- An auxiliary word records the bits on the auxiliary coordinate set. -/
abbrev GridGeom.AuxWord {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  Γ.aux → Bool

/-- A grid cell pairs a key with an auxiliary word. -/
abbrev GridGeom.Cell {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q) :=
  GridGeom.Key Γ × GridGeom.AuxWord Γ

/-- The grid key read by a cube vertex: one bin index per special chunk and the auxiliary bits. -/
noncomputable def GridGeom.key {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)
    (v : CubeVertex n) : (∀ r, Fin (Γ.bins r)) × (Γ.aux → Bool) := by
  classical
  let b : ∀ r, Fin (ℓ + 1) := fun r =>
    ⟨((Γ.chunk r).filter (fun j => v j = true)).card,
      Nat.lt_succ_of_le (by
        calc
          ((Γ.chunk r).filter (fun j => v j = true)).card ≤ (Γ.chunk r).card :=
            Finset.card_filter_le _ _
          _ = ℓ := Γ.chunk_card r)⟩
  exact (fun r => Γ.bin r (b r), fun j => v j)

/-- L7.1a (07:55–68, 77–82): for large `n`, the prescribed chunks and bins exist. -/
theorem gridGeom_exists (d : ℝ) (hd : 0 < d) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      Nonempty (GridGeom d n (Nat.ceil ((n : ℝ) ^ d)) ⌊(n : ℝ) ^ d⌋₊
        (Nat.ceil ((n : ℝ) ^ (4 * d)))) := by
  sorry

end HypercubeRamsey.S07
