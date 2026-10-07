import HypercubeRamsey.S13.Allocation
import HypercubeRamsey.PartC.Cleaning

/-!
# Section 13.4: stable cleaning of extracted first supports
-/

namespace HypercubeRamsey.S13

open Filter
open Classical
open scoped BigOperators

/-- L13.4a: a law below a width budget has a large uniform approximant that
preserves every finite family of degree and correlation tests to `n⁻²`. -/
def UniformApproximantStatement : Prop :=
  ∀ (N J n : ℕ) (π : Law N) (B W : ℝ),
    B ≤ (n : ℝ) ^ (1 / 2 : ℝ) → W ≤ (n : ℝ) ^ (1 / 2 : ℝ) →
    W + 2 ≤ B → π.WidthLE W →
    (tests : Fin J → (Fin N → ℝ)) →
    (∀ j y, 0 ≤ tests j y ∧ tests j y ≤ 1) →
    J ≤ Nat.ceil (Real.exp (n : ℝ)) * n ^ 4 →
    ∃ V : Finset (Fin N), V.Nonempty ∧
      (N : ℝ) * Real.exp (-B) ≤ V.card ∧
      ∀ j, |(∑ y ∈ V, tests j y) / V.card - π.expect (tests j)| ≤
        (n : ℝ) ^ (-2 : ℝ)

theorem uniform_approximant (hSampling : LawSubsampleStatement) :
    UniformApproximantStatement := by
  sorry

/-- The degree-trimming output for L13.4b. -/
structure OwnDegreeData {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m)
    (π : Fin 𝒯.m → Law (T.S.N k)) where
  C : Finset (Fin (T.S.N k))
  sub : C ⊆ (𝒯.P i).X
  own : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    ∀ x ∈ C, OwnDegOK 𝒯 i (π' i) x

/-- The clique-trimming output for L13.4c, retaining the degree data. -/
structure OwnCliqueData {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    {π : Fin 𝒯.m → Law (T.S.N k)} (D : OwnDegreeData 𝒯 i π) where
  C : Finset (Fin (T.S.N k))
  sub : C ⊆ D.C
  noClique : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    NoClique (T.S.E k) 𝒯.c C (π' i).w κ.θ (𝒯.Q i)

/-- Other-patch degree and row-tail output for L13.4d. -/
structure OtherPatchData {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    {π : Fin 𝒯.m → Law (T.S.N k)}
    (D : OwnDegreeData 𝒯 i π) (C : OwnCliqueData D) where
  cleaned : Finset (Fin (T.S.N k))
  subset : cleaned ⊆ C.C
  loss : ((𝒯.P i).X \ cleaned).card < κ.a * (𝒯.P i).M
  nonempty : cleaned.Nonempty
  degOther : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    ∀ j, j ≠ i → ∀ x ∈ cleaned,
      |deg (T.S.E k) 𝒯.c (π' j).w x - 1 / 2| ≤ 3 * bstar T k
  rowTail : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    ∀ j, ∀ x ∈ cleaned,
      RowTailRelaxed (T.S.E k) 𝒯.c (π' j).w (𝒯.P i).X (T.S.n k) κ.ξ x

/-- L13.4e subnode: codegree survives deleting fewer than an `a` fraction of
the first support. -/
theorem cleaned_codegree_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} (h𝒯 : Tiling.Valid 𝒯)
    (i : Fin 𝒯.m) (C : Finset (Fin (T.S.N k)))
    (hC : C ⊆ (𝒯.P i).X)
    (hLoss : ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M) :
    𝒯.mode.isCluster → ∀ B ∈ (𝒯.P i).bins.parts, ∀ y ∈ B, ∀ y' ∈ B,
      (1 / 4 : ℝ) + κ.a ≤
        (∑ x ∈ C, hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') / C.card := by
  sorry

/-- L13.4e: assemble the four cleaned properties from the degree, clique,
other-patch, and codegree nodes. -/
theorem assemble_clean_props {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k}
    (i : Fin 𝒯.m) (π : Fin 𝒯.m → Law (T.S.N k))
    (D : OwnDegreeData 𝒯 i π) (C : OwnCliqueData D)
    (O : OtherPatchData D C)
    (hCodegree : 𝒯.mode.isCluster → ∀ B ∈ (𝒯.P i).bins.parts,
      ∀ y ∈ B, ∀ y' ∈ B,
        (1 / 4 : ℝ) + κ.a ≤
          (∑ x ∈ O.cleaned, hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y') /
            O.cleaned.card) :
    CleanProps 𝒯 i π O.cleaned ∧
      (𝒯.mode.isCluster → ∀ π',
        NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
        CleanProps 𝒯 i π' O.cleaned) := by
  constructor
  · have hself : NearInput π π ((T.S.n k : ℝ) ^ (-3 : ℝ)) := by
      intro j
      simp
    refine ⟨(O.subset.trans C.sub).trans D.sub, O.nonempty, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact D.own π hself x (O.subset.trans C.sub hx)
    · intro hClique
      apply C.noClique π hself
      rcases hClique with ⟨K, hK, hcard, hpair⟩
      exact ⟨K, hK.trans O.subset, hcard, hpair⟩
    · exact O.degOther π hself
    · exact O.rowTail π hself
    · intro hCluster
      exact hCodegree hCluster
  · intro hCluster π' hNear
    refine ⟨(O.subset.trans C.sub).trans D.sub, O.nonempty, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact D.own π' hNear x (O.subset.trans C.sub hx)
    · intro hClique
      apply C.noClique π' hNear
      rcases hClique with ⟨K, hK, hcard, hpair⟩
      exact ⟨K, hK.trans O.subset, hcard, hpair⟩
    · exact O.degOther π' hNear
    · exact O.rowTail π' hNear
    · intro _
      exact hCodegree hCluster

/-- L13.4b: own-patch degree trimming; the direct, cluster, and bounded
thresholds are exactly those in `OwnDegOK`. -/
theorem own_patch_degree_trim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hApprox : UniformApproximantStatement) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        Nonempty (OwnDegreeData 𝒯 i π) := by
  sorry

/-- L13.4c: remove large high-correlation cliques without destroying the own
degree margins. -/
theorem own_patch_clique_trim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∀ D : OwnDegreeData 𝒯 i π, Nonempty (OwnCliqueData D) := by
  sorry

/-- L13.4d: clean all other-patch degree outliers and enforce the relaxed row
tails on the fixed original first support. -/
theorem other_patch_degrees_and_tails (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∀ D : OwnDegreeData 𝒯 i π, ∀ C : OwnCliqueData D,
          Nonempty (OtherPatchData D C) := by
  sorry

/-- L13.4: stable cleaning at every valid tiling and every allowed input profile. -/
theorem stable_cleaning (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2)) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∃ C : Finset (Fin (T.S.N k)),
          ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧
          CleanProps 𝒯 i π C ∧
          (𝒯.mode.isCluster → ∀ π',
            NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C) := by
  have hD := own_patch_degree_trim κ hκ T hInit hDeep
    (uniform_approximant random_subset_lemma.2)
  have hC := own_patch_clique_trim κ hκ T hDeep
  have hO := other_patch_degrees_and_tails κ hκ T hInit hDeep
  filter_upwards [hD, hC, hO] with k hkD hkC hkO
  intro 𝒯 h𝒯 i π hInput
  obtain ⟨D⟩ := hkD 𝒯 h𝒯 i π hInput
  obtain ⟨C⟩ := hkC 𝒯 h𝒯 i π hInput D
  obtain ⟨O⟩ := hkO 𝒯 h𝒯 i π hInput D C
  let Cfinal := O.cleaned
  have hCsub : Cfinal ⊆ (𝒯.P i).X := (O.subset.trans C.sub).trans D.sub
  have hCodegree := cleaned_codegree_bound h𝒯 i Cfinal hCsub O.loss
  obtain ⟨hClean, hStable⟩ := assemble_clean_props i π D C O hCodegree
  exact ⟨Cfinal, O.loss, hClean, hStable⟩

end HypercubeRamsey.S13
