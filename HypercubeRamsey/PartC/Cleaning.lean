import HypercubeRamsey.PartC.Tiling

/-!
# Stable cleaning vocabulary used by Sections 13–18 (L13.4)
-/

namespace HypercubeRamsey

open Classical
open scoped BigOperators

/-- No large correlation clique of the specified size is contained in `Sp`. -/
def NoClique {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (Sp : Finset (Fin N)) (π : Fin N → ℝ) (θ Q : ℝ) : Prop :=
  ¬ ∃ C ⊆ Sp, C.card = ⌈Real.exp Q⌉₊ ∧
    ∀ x ∈ C, ∀ z ∈ C, x ≠ z → 3 * θ < corr E c π x z

/-- Relaxed row-tail estimate supplied by L12.6b. -/
def RowTailRelaxed {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (X₀ : Finset (Fin N)) (n ξ : ℝ) (x : Fin N) : Prop :=
  (((X₀.filter fun z => Real.rpow n (-1.02) < |corr E c π x z|).card : ℝ) ≤
      Real.exp (-Real.rpow n 0.19) * X₀.card) ∧
    (∑ z ∈ X₀.filter (fun z => Real.rpow n (-1.02) < |corr E c π x z| ∧
        |corr E c π x z| ≤ 2 * ξ), Real.exp (100 * n * |corr E c π x z|)) ≤
      Real.exp (-Real.rpow n 0.19) * X₀.card

/-- Own-patch degree window for the three regimes in Section 13. -/
def OwnDegOK {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m) (π : Law (T.S.N k)) (x : Fin (T.S.N k)) : Prop :=
  match 𝒯.mode with
  | .bounded => |deg (T.S.E k) 𝒯.c π.w x - 1 / 2| ≤ κ.Kbd / T.S.n k
  | .lowDirect | .highDirect =>
      1 / 2 + (𝒯.P i).g / (4 * T.S.n k) ≤ deg (T.S.E k) 𝒯.c π.w x ∧
        deg (T.S.E k) 𝒯.c π.w x ≤ 1 / 2 + 4 * (𝒯.P i).g / T.S.n k
  | .lowCluster | .highSmall | .highLarge =>
      |deg (T.S.E k) 𝒯.c π.w x - 1 / 2| ≤ 10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb / T.S.n k

/-- Input laws for cleaning: uniform in direct/bounded modes, capped and supported in cluster modes. -/
def InputOK {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
    (π : Fin 𝒯.m → Law (T.S.N k)) : Prop :=
  ∀ i, (π i).SupportedIn (𝒯.P i).Y ∧
    (if 𝒯.mode.isCluster then
      ∀ y, (𝒯.P i).M * (π i).w y ≤ Real.exp (10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i)
    else π i = Law.unifCore (𝒯.P i).Y (h𝒯.patch_nonempty i).2)

/-- Per-patch first laws close in entrywise `ℓ¹` norm. -/
def NearInput {κ : CConsts} {T : Stage} {k : ℕ} {𝒯 : Tiling κ T k}
    (π π' : Fin 𝒯.m → Law (T.S.N k)) (ε : ℝ) : Prop :=
  ∀ i, ∑ y, |(π i).w y - (π' i).w y| ≤ ε

/-- Cleaned-support properties (P1)–(P5) from L13.4. -/
structure CleanProps {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m)
    (π : Fin 𝒯.m → Law (T.S.N k)) (C : Finset (Fin (T.S.N k))) : Prop where
  sub : C ⊆ (𝒯.P i).X
  nonempty : C.Nonempty
  /-- The cleaning loses less than half the patch (section 13, line 232). -/
  card_lower : (𝒯.P i).M / 2 ≤ (C.card : ℝ)
  /-- Stable cleaning removes less than the fraction `κ.a` of the original patch
  (sections/13, lines 226–232 and 270–278). -/
  card_lower_waste : (1 - κ.a) * ((𝒯.P i).M : ℝ) ≤ (C.card : ℝ)
  degOwn : ∀ x ∈ C, OwnDegOK 𝒯 i (π i) x
  noClique : NoClique (T.S.E k) 𝒯.c C (π i).w κ.θ (𝒯.Q i)
  degOther : ∀ j, j ≠ i → ∀ x ∈ C,
    |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2| ≤ 3 * bstar T k
  rowTail : ∀ j, ∀ x ∈ C,
    RowTailRelaxed (T.S.E k) 𝒯.c (π j).w (𝒯.P i).X (T.S.n k) κ.ξ x
  codeg : 𝒯.mode.isCluster → ∀ B ∈ (𝒯.P i).bins.parts, ∀ y ∈ B, ∀ y' ∈ B,
    1 / 4 + κ.a ≤
      (∑ x ∈ C, hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') / C.card

end HypercubeRamsey
