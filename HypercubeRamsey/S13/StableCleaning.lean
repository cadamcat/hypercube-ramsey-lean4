import HypercubeRamsey.S13.Allocation
import HypercubeRamsey.PartC.Cleaning
import HypercubeRamsey.S13.Needs

/-!
# Section 13.4: stable cleaning of extracted first supports
-/

namespace HypercubeRamsey.S13

open Filter
open Classical
open scoped BigOperators

/-- L13.4a (sections/13, lines 244–249): a capped law has a large uniform approximant that
preserves every finite family of degree and correlation tests to `n⁻²`. -/
def UniformApproximantStatement : Prop :=
  ∀ (N J n : ℕ) (π : Law N) (B W : ℝ),
    1 ≤ n →
    B ≤ (n : ℝ) ^ (1 / 2 : ℝ) → W ≤ (n : ℝ) ^ (1 / 2 : ℝ) →
    W + 2 ≤ B → π.WidthLE W →
    (n : ℝ) ^ 12 ≤ (N : ℝ) * Real.exp (-(B + W) / 2) →
    (tests : Fin J → (Fin N → ℝ)) →
    (∀ j y, 0 ≤ tests j y ∧ tests j y ≤ 1) →
    J ≤ Nat.ceil (Real.exp (2 * (n : ℝ))) * n ^ 4 →
    ∃ V : Finset (Fin N), V.Nonempty ∧
      (∀ y ∈ V, 0 < π.w y) ∧
      (N : ℝ) * Real.exp (-B) ≤ V.card ∧
      ∀ j, |(∑ y ∈ V, tests j y) / V.card - π.expect (tests j)| ≤
        (n : ℝ) ^ (-2 : ℝ)

theorem uniform_approximant (hSampling : LawSubsampleStatement) :
    UniformApproximantStatement := by
  sorry

/-- L13.4b (sections/13, lines 251–257): own-patch degree-trimming output. -/
structure OwnDegreeData {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m)
    (π : Fin 𝒯.m → Law (T.S.N k)) where
  C : Finset (Fin (T.S.N k))
  sub : C ⊆ (𝒯.P i).X
  loss : (((𝒯.P i).X \ C).card : ℝ) < (κ.a / 4) * (𝒯.P i).M
  own : ∀ x ∈ C, OwnDegOK 𝒯 i (π i) x
  own_near : 𝒯.mode.isCluster → ∀ π',
    NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    ∀ x ∈ C, OwnDegOK 𝒯 i (π' i) x

/-- L13.4c (sections/13, lines 259–265): clique-trimming output retaining degree data. -/
structure OwnCliqueData {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    {π : Fin 𝒯.m → Law (T.S.N k)} (D : OwnDegreeData 𝒯 i π) where
  C : Finset (Fin (T.S.N k))
  sub : C ⊆ D.C
  loss : ((D.C \ C).card : ℝ) < (κ.a / 4) * (𝒯.P i).M
  noClique : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    NoClique (T.S.E k) 𝒯.c C (π' i).w κ.θ (𝒯.Q i)

/-- L13.4d (sections/13, lines 267–276): other-patch degree and row-tail output. -/
structure OtherPatchData {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m}
    {π : Fin 𝒯.m → Law (T.S.N k)}
    (D : OwnDegreeData 𝒯 i π) (C : OwnCliqueData D) where
  cleaned : Finset (Fin (T.S.N k))
  subset : cleaned ⊆ C.C
  loss : ((𝒯.P i).X \ cleaned).card < κ.a * (𝒯.P i).M
  nonempty : cleaned.Nonempty
  /-- The cleaning loses less than half the patch (sections/13, line 232; shared `CleanProps.card_lower`). -/
  card_lower : (𝒯.P i).M / 2 ≤ (cleaned.card : ℝ)
  /-- The total waste is less than the fraction `κ.a` of the original patch
  (sections/13, lines 226–232 and 270–278; shared `CleanProps.card_lower_waste`). -/
  card_lower_waste : (1 - κ.a) * ((𝒯.P i).M : ℝ) ≤ (cleaned.card : ℝ)
  degOther : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    ∀ j, j ≠ i → ∀ x ∈ cleaned,
      |deg (T.S.E k) 𝒯.c (π' j).w x - 1 / 2| ≤ 3 * bstar T k
  rowTail : ∀ π', NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) →
    ∀ j, ∀ x ∈ cleaned,
      RowTailRelaxed (T.S.E k) 𝒯.c (π' j).w (𝒯.P i).X (T.S.n k) κ.ξ x

/-- L13.4e (sections/13, lines 273–278): codegree survives deleting fewer than an `a` fraction of
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

/-- L13.4e (sections/13, lines 273–278): assemble cleaned properties from degree, clique,
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
    refine ⟨(O.subset.trans C.sub).trans D.sub, O.nonempty, O.card_lower,
      O.card_lower_waste, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact D.own x (O.subset.trans C.sub hx)
    · intro hClique
      apply C.noClique π hself
      rcases hClique with ⟨K, hK, hcard, hpair⟩
      exact ⟨K, hK.trans O.subset, hcard, hpair⟩
    · exact O.degOther π hself
    · exact O.rowTail π hself
    · intro hCluster
      exact hCodegree hCluster
  · intro hCluster π' hNear
    refine ⟨(O.subset.trans C.sub).trans D.sub, O.nonempty, O.card_lower,
      O.card_lower_waste, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact D.own_near hCluster π' hNear x (O.subset.trans C.sub hx)
    · intro hClique
      apply C.noClique π' hNear
      rcases hClique with ⟨K, hK, hcard, hpair⟩
      exact ⟨K, hK.trans O.subset, hcard, hpair⟩
    · exact O.degOther π' hNear
    · exact O.rowTail π' hNear
    · intro _
      exact hCodegree hCluster

/-- L13.4b (sections/13, lines 251–257): own-patch degree trimming; direct, cluster, and bounded
thresholds are exactly those in `OwnDegOK`. -/
theorem own_patch_degree_trim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hApprox : UniformApproximantStatement) (hScales : ResidualScaleSpec) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        Nonempty (OwnDegreeData 𝒯 i π) := by
  sorry

/-- L13.4c (sections/13, lines 259–265): remove large high-correlation cliques without destroying own
degree margins. -/
theorem own_patch_clique_trim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hApprox : UniformApproximantStatement) (hScales : ResidualScaleSpec) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∀ D : OwnDegreeData 𝒯 i π, Nonempty (OwnCliqueData D) := by
  sorry

/-- L13.4d (sections/13, lines 267–276): clean other-patch outliers and enforce relaxed row
tails on the fixed original first support, retaining at least `(1 - κ.a) * M` labels. -/
theorem other_patch_degrees_and_tails (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : OtherPatchDiscrepancyInput κ T) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∀ D : OwnDegreeData 𝒯 i π, ∀ C : OwnCliqueData D,
          Nonempty (OtherPatchData D C) := by
  sorry

/-- L13.4 (sections/13, line 240): conflict and own-degree budgets carried
alongside the cleaned-support properties. -/
def CleaningScaleFacts {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) : Prop :=
  (∀ i, if 𝒯.mode = .bounded then
    Real.exp (Cstar κ.u κ.ξ * 𝒯.Q i) ≤ κ.Kbd
  else Real.exp (Cstar κ.u κ.ξ * 𝒯.Q i) ≤ Real.exp (𝒯.gain i)) ∧
  (𝒯.mode.isCluster → ∀ i,
    10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb < 𝒯.gain i / (100 * κ.u))

/-- L13.4 (sections/13, lines 240, 252–265): the fixed scale choices pay for
clique exclusion and the cluster degree window. -/
theorem cleaning_scale_bounds (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ 𝒯 : Tiling κ T k, Tiling.Valid 𝒯 → CleaningScaleFacts 𝒯 := by
  sorry

/-- L13.4 (sections/13, lines 218–281): stable cleaning with its conflict
and degree budgets, at every valid tiling and allowed input profile. -/
theorem stable_cleaning_with_facts (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hDeepOther : OtherPatchDiscrepancyInput κ T) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∃ C : Finset (Fin (T.S.N k)),
          ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧
          CleanProps 𝒯 i π C ∧
          (𝒯.mode.isCluster → ∀ π',
            NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C) ∧
          CleaningScaleFacts 𝒯 := by
  have hD := own_patch_degree_trim κ hκ T hInit hDeep
    (uniform_approximant random_subset_lemma.2) d13_1_residual_scale_specification
  have hC := own_patch_clique_trim κ hκ T hDeep
    (uniform_approximant random_subset_lemma.2) d13_1_residual_scale_specification
  have hO := other_patch_degrees_and_tails κ hκ T hInit hDeepOther
  have hScale := cleaning_scale_bounds κ hκ T
  filter_upwards [hD, hC, hO, hScale] with k hkD hkC hkO hkScale
  intro 𝒯 h𝒯 i π hInput
  obtain ⟨D⟩ := hkD 𝒯 h𝒯 i π hInput
  obtain ⟨C⟩ := hkC 𝒯 h𝒯 i π hInput D
  obtain ⟨O⟩ := hkO 𝒯 h𝒯 i π hInput D C
  let Cfinal := O.cleaned
  have hCsub : Cfinal ⊆ (𝒯.P i).X := (O.subset.trans C.sub).trans D.sub
  have hCodegree := cleaned_codegree_bound h𝒯 i Cfinal hCsub O.loss
  obtain ⟨hClean, hStable⟩ := assemble_clean_props i π D C O hCodegree
  exact ⟨Cfinal, O.loss, hClean, hStable, hkScale 𝒯 h𝒯⟩

/-- L13.4: cleaned-support export. The additional discrepancy input is the
shared contract in `Needs.lean`, required by the other-patch node. -/
theorem stable_cleaning (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hDeepOther : OtherPatchDiscrepancyInput κ T) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∃ C : Finset (Fin (T.S.N k)),
          ((𝒯.P i).X \ C).card < κ.a * (𝒯.P i).M ∧
          CleanProps 𝒯 i π C ∧
          (𝒯.mode.isCluster → ∀ π',
            NearInput π π' ((T.S.n k : ℝ) ^ (-3 : ℝ)) → CleanProps 𝒯 i π' C) := by
  filter_upwards [stable_cleaning_with_facts κ hκ T hInit hDeep hDeepOther]
    with k hk
  intro 𝒯 h𝒯 i π hInput
  obtain ⟨C, hLoss, hClean, hStable, hScale⟩ := hk 𝒯 h𝒯 i π hInput
  exact ⟨C, hLoss, hClean, hStable⟩

end HypercubeRamsey.S13
