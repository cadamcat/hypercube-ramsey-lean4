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
  intro N J n π B W hn hB hW hGap hWidth hSize tests htests hJ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNpos : (0 : ℝ) < N := by
    by_contra hN
    have hN' : (N : ℝ) = 0 := by exact le_antisymm (le_of_not_gt hN) (Nat.cast_nonneg _)
    rw [hN'] at hSize
    have hpow : 0 < (n : ℝ) ^ 12 := pow_pos hnpos 12
    nlinarith [hpow]
  have hshift : W + 1 ≤ (B + W) / 2 := by linarith
  have htsize : (n : ℝ) ^ 12 ≤ (N : ℝ) * Real.exp (-W) := by
    calc
      (n : ℝ) ^ 12 ≤ (N : ℝ) * Real.exp (-(B + W) / 2) := hSize
      _ ≤ (N : ℝ) * Real.exp (-W) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
        exact Real.exp_le_exp.mpr (by linarith)
  let t : ℝ := (N : ℝ) * Real.exp (-W)
  have hcap : ∀ y, t * π.w y ≤ 1 := by
    intro y
    unfold Law.WidthLE at hWidth
    have hy := hWidth y
    dsimp [t]
    calc
      (N : ℝ) * Real.exp (-W) * π.w y ≤
          (N : ℝ) * Real.exp (-W) * (Real.exp W / N) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      _ = 1 := by
        rw [Real.exp_neg]
        field_simp [ne_of_gt hNpos]
  have hcard : (N : ℝ) * Real.exp (-B) ≤ t / 2 := by
    have hexp2 : (2 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have hExp : Real.exp (-B) * 2 ≤ Real.exp (-W) := by
      have h := Real.exp_le_exp.mpr (show -B ≤ -(W + 2) by linarith)
      have hstrong : Real.exp (-(W + 2)) ≤ Real.exp (-W) / 2 := by
        rw [show -(W + 2) = -W + -2 by ring, Real.exp_add]
        have hfactor : 2 * Real.exp (-2) ≤ 1 := by
          rw [Real.exp_neg]
          have h' : 2 / Real.exp 2 ≤ 1 :=
            (div_le_one (Real.exp_pos _)).2 hexp2
          simpa [div_eq_mul_inv, mul_comm] using h'
        have hhalf : Real.exp (-2) ≤ (1 / 2 : ℝ) := by nlinarith [hfactor]
        calc
          Real.exp (-W) * Real.exp (-2) ≤ Real.exp (-W) * (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hhalf (le_of_lt (Real.exp_pos _))
          _ = Real.exp (-W) / 2 := by ring
      calc
        Real.exp (-B) * 2 ≤ Real.exp (-(W + 2)) * 2 :=
          mul_le_mul_of_nonneg_right h (by norm_num)
        _ ≤ Real.exp (-W) := by
          have h' := mul_le_mul_of_nonneg_right hstrong (by norm_num : (0 : ℝ) ≤ 2)
          nlinarith [h']
    dsimp [t]
    have h' := mul_le_mul_of_nonneg_left hExp (le_of_lt hNpos)
    nlinarith
  have hsample := hSampling N J n π t tests
    hn htsize hcap hJ htests
  rcases hsample with ⟨V, hVne, hVpos, hVcard, hVtests⟩
  refine ⟨V, hVne, hVpos, hcard.trans hVcard, hVtests⟩

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
  classical
  intro hCluster B hB y hy y' hy'
  have hModes : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
      𝒯.mode = .highLarge := by
    cases hmode : 𝒯.mode with
    | bounded =>
        have hFalse : False := by simpa [Mode.isCluster, hmode] using hCluster
        exact hFalse.elim
    | lowDirect =>
        have hFalse : False := by simpa [Mode.isCluster, hmode] using hCluster
        exact hFalse.elim
    | highDirect =>
        have hFalse : False := by simpa [Mode.isCluster, hmode] using hCluster
        exact hFalse.elim
    | lowCluster => exact Or.inl rfl
    | highSmall => exact Or.inr (Or.inl rfl)
    | highLarge => exact Or.inr (Or.inr rfl)
  have hData := h𝒯.cluster_data hModes i
  rcases hData with ⟨_, _, _, _, _, hPatchCodeg, _, _, _, _, _⟩
  have hMpos : (0 : ℝ) < (𝒯.P i).M := by
    have hcard := Finset.card_pos.mpr (h𝒯.patch_nonempty i).1
    rw [(𝒯.P i).cardX] at hcard
    exact_mod_cast hcard
  let f : Fin (T.S.N k) → ℝ := fun x =>
    hit (T.S.E k) 𝒯.c x y * hit (T.S.E k) 𝒯.c x y'
  have hHit01 (x z : Fin (T.S.N k)) :
      hit (T.S.E k) 𝒯.c x z = 0 ∨ hit (T.S.E k) 𝒯.c x z = 1 := by
    unfold hit
    split_ifs <;> simp
  have hfBounds (x : Fin (T.S.N k)) : 0 ≤ f x ∧ f x ≤ 1 := by
    dsimp [f]
    rcases hHit01 x y with hx | hx <;>
      rcases hHit01 x y' with hy' | hy' <;> simp [hx, hy']
  have hbase : (1 / 4 + 3 * κ.a) ≤
      (∑ x ∈ (𝒯.P i).X, f x) / (𝒯.P i).M := by
    simpa [f] using hPatchCodeg B hB y hy y' hy'
  have hbase' : (1 / 4 + 3 * κ.a) * (𝒯.P i).M ≤
      ∑ x ∈ (𝒯.P i).X, f x := (le_div_iff₀ hMpos).mp hbase
  have hdeleted : (∑ x ∈ (𝒯.P i).X \ C, f x) ≤
      ((𝒯.P i).X \ C).card := by
    calc
      (∑ x ∈ (𝒯.P i).X \ C, f x) ≤
          ∑ _x ∈ (𝒯.P i).X \ C, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro x hx
            exact (hfBounds x).2
      _ = ((𝒯.P i).X \ C).card := by simp
  have hdecomp : (∑ x ∈ (𝒯.P i).X, f x) =
      (∑ x ∈ C, f x) + (∑ x ∈ (𝒯.P i).X \ C, f x) := by
    rw [← Finset.sum_sdiff hC]
    ring
  have ha : 0 < κ.a := by
    by_contra h
    have hle : κ.a ≤ 0 := le_of_not_gt h
    have hLostNonneg : 0 ≤ (((𝒯.P i).X \ C).card : ℝ) := Nat.cast_nonneg _
    have hprod : κ.a * (𝒯.P i).M ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hMpos.le
    nlinarith [hLoss, hprod]
  have hsumC : (1 / 4 + 2 * κ.a) * (𝒯.P i).M ≤ ∑ x ∈ C, f x := by
    have hLoss' : (((𝒯.P i).X \ C).card : ℝ) < κ.a * (𝒯.P i).M := hLoss
    have hdeleted' : (∑ x ∈ (𝒯.P i).X \ C, f x) < κ.a * (𝒯.P i).M :=
      lt_of_le_of_lt hdeleted hLoss'
    have hbase'' := hbase'
    rw [hdecomp] at hbase''
    nlinarith
  have hCne : C.Nonempty := by
    by_contra hne
    have hempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty] at hsumC
    have hcoef : 0 < (1 / 4 + 2 * κ.a) := by positivity
    nlinarith [hMpos]
  have hCpos : (0 : ℝ) < C.card := by
    exact_mod_cast (Finset.card_pos.mpr hCne)
  have hcardCM : (C.card : ℝ) ≤ (𝒯.P i).M := by
    have hcard := Finset.card_le_card hC
    rw [(𝒯.P i).cardX] at hcard
    exact_mod_cast hcard
  have hnum : (1 / 4 + κ.a) * (C.card : ℝ) ≤ ∑ x ∈ C, f x := by
    calc
      (1 / 4 + κ.a) * (C.card : ℝ) ≤
          (1 / 4 + 2 * κ.a) * (C.card : ℝ) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (Nat.cast_nonneg _)
      _ ≤ (1 / 4 + 2 * κ.a) * (𝒯.P i).M :=
        mul_le_mul_of_nonneg_left hcardCM (by positivity)
      _ ≤ ∑ x ∈ C, f x := hsumC
  apply (le_div_iff₀ hCpos).2
  simpa [f] using hnum

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
  classical
  have hDirectArg {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
      (hMode : 𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) (i : Fin 𝒯.m) :
      Cstar κ.u κ.ξ * 𝒯.Q i ≤ (𝒯.P i).g / 1000 := by
    rcases (h𝒯.clique_scales i).2 hMode with ⟨_, _, hQ, _⟩
    have hM1 : 0 < κ.M1 := by linarith [hκ.M1_big.1]
    have hsqrt : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.2 hM1
    have hCstar : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
    calc
      Cstar κ.u κ.ξ * 𝒯.Q i ≤
          Cstar κ.u κ.ξ * (2 * (𝒯.P i).g / Real.sqrt κ.M1) :=
        mul_le_mul_of_nonneg_left hQ hCstar
      _ = (2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1) * (𝒯.P i).g := by ring
      _ ≤ (1e-4 : ℝ) * (𝒯.P i).g :=
        mul_le_mul_of_nonneg_right hκ.M1_big.2 (Nat.cast_nonneg _)
      _ = (1 / 10000) * (𝒯.P i).g := by norm_num
      _ ≤ (𝒯.P i).g / 1000 := by nlinarith
  have hClusterArgs {k : ℕ} (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯)
      (hMode : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
        𝒯.mode = .highLarge) (i : Fin 𝒯.m) :
      Cstar κ.u κ.ξ * 𝒯.Q i ≤ κ.a * (𝒯.P i).h / 10 ^ 6 ∧
        10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb <
          (κ.a * (𝒯.P i).h / 10 ^ 6) / (100 * (κ.u : ℝ)) := by
    rcases h𝒯.cluster_data hMode i with
      ⟨hmax, hg, _, _, _, _, _, hheight, _, _, _, _⟩
    have hM1 : 0 < κ.M1 := by linarith [hκ.M1_big.1]
    have hMqReal : max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) ≤
        κ.M1 * (𝒯.P i).q := by
      apply max_le hg
      have hfactor : 0 ≤ (κ.M1 - 1) * (𝒯.P i).q :=
        mul_nonneg (by linarith [hκ.M1_big.1]) (Nat.cast_nonneg _)
      nlinarith [hfactor]
    have hMq : ((max (𝒯.P i).g (𝒯.P i).q : ℕ) : ℝ) ≤
        κ.M1 * (𝒯.P i).q := by
      exact_mod_cast hMqReal
    have hQ0 : κ.Q0 ≤ (𝒯.P i).q := by
      have hprod : κ.Q0 * κ.M1 ≤ (𝒯.P i).q * κ.M1 := by
        calc
          κ.Q0 * κ.M1 = κ.M1 * κ.Q0 := by ring
          _ ≤ ((max (𝒯.P i).g (𝒯.P i).q : ℕ) : ℝ) := hmax
          _ ≤ κ.M1 * (𝒯.P i).q := hMq
          _ = (𝒯.P i).q * κ.M1 := by ring
      exact (mul_le_mul_iff_left₀ hM1).mp hprod
    rcases hκ.Q0_large (𝒯.P i).q hQ0 with
      ⟨_, _, _, _, _, _, hConflict, hDegree, _⟩
    rcases (h𝒯.clique_scales i).1 hMode with ⟨_, _, hQ, _⟩
    have hqNat : 1 ≤ (𝒯.P i).q := by
      rw [(h𝒯.measured_scales i).2]
      unfold qScale
      exact Nat.one_le_pow' _ 1
    have hq : (1 : ℝ) ≤ (𝒯.P i).q := by exact_mod_cast hqNat
    have hMloMhi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
      have hqpos : 0 < κ.cq := hκ.cq_rng.1
      have hterm : 0 ≤ 10 / κ.cq := by positivity
      have hstep : (κ.Mlo : ℝ) ≤ (κ.Mlo : ℝ) + 10 / κ.cq := by linarith
      exact le_trans hstep hκ.Mhi_big.1
    have hExponent : (κ.Mlo : ℝ) ≤
        (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) := by
      by_cases hLow : 𝒯.mode = .lowCluster
      · simp [hLow]
      · simpa [hLow] using hMloMhi
    have hPower : Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo ≤ (𝒯.P i).h := by
      have hmono := Real.rpow_le_rpow_of_exponent_le hq hExponent
      have hheight' : Real.rpow ((𝒯.P i).q : ℝ)
          (↑(if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi)) ≤ (𝒯.P i).h := by
        simpa only [Nat.cast_ite] using hheight
      exact le_trans hmono hheight'
    have hCstar : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
    have hConflict' : Cstar κ.u κ.ξ * 𝒯.Q i ≤
        (κ.a / 10 ^ 6) * Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo := by
      calc
        Cstar κ.u κ.ξ * 𝒯.Q i ≤
            Cstar κ.u κ.ξ * (2 * ((𝒯.P i).q : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hQ hCstar
        _ = 2 * Cstar κ.u κ.ξ * ((𝒯.P i).q : ℝ) ^ 2 := by ring
        _ ≤ (κ.a / 10 ^ 6) * Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo := by
          have hnonneg : 0 ≤ Cstar κ.u κ.ξ * ((𝒯.P i).q : ℝ) ^ 2 :=
            mul_nonneg hCstar (sq_nonneg _)
          nlinarith [hConflict, hnonneg]
    have hA : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
    have hU : 0 < (κ.u : ℝ) := by
      have hu := hκ.u_rng.2
      have hNat : 0 < κ.u := by omega
      exact_mod_cast hNat
    have hDen : 0 < (100 : ℝ) * κ.u := by positivity
    have hRpowPos : 0 < Real.rpow ((𝒯.P i).q : ℝ) κ.Cb :=
      Real.rpow_pos_of_pos (by positivity) _
    have hCpay : Cstar κ.u κ.ξ * 𝒯.Q i ≤ κ.a * (𝒯.P i).h / 10 ^ 6 := by
      calc
        Cstar κ.u κ.ξ * 𝒯.Q i ≤
            (κ.a / 10 ^ 6) * Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo := hConflict'
        _ ≤ (κ.a / 10 ^ 6) * (𝒯.P i).h :=
          mul_le_mul_of_nonneg_left hPower (by positivity)
        _ = κ.a * (𝒯.P i).h / 10 ^ 6 := by ring
    have hDpay : 40 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb ≤
        (κ.a * (𝒯.P i).h / 10 ^ 6) / (100 * (κ.u : ℝ)) := by
      calc
        40 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb ≤
            ((κ.a / 10 ^ 6) * Real.rpow ((𝒯.P i).q : ℝ) κ.Mlo) /
              (100 * (κ.u : ℝ)) := hDegree
        _ ≤ ((κ.a / 10 ^ 6) * (𝒯.P i).h) / (100 * (κ.u : ℝ)) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPower (by positivity)) hDen.le
        _ = (κ.a * (𝒯.P i).h / 10 ^ 6) / (100 * (κ.u : ℝ)) := by ring
    constructor
    · exact hCpay
    · have hStrict : 10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb <
          40 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb := by nlinarith [hRpowPos]
      exact lt_of_lt_of_le hStrict hDpay
  filter_upwards [] with k
  intro 𝒯 h𝒯
  cases hm : 𝒯.mode with
  | bounded =>
      simp [CleaningScaleFacts, hm, Mode.isCluster]
      intro i
      rcases hκ.bounded with ⟨_, _, _, _, hBound⟩
      rcases (h𝒯.bounded_data hm).2 i with ⟨_, _, _, _, hQ⟩
      simpa [hQ] using hBound
  | lowDirect =>
      simp [CleaningScaleFacts, hm, Mode.isCluster]
      intro i
      simpa [Tiling.gain, hm] using hDirectArg 𝒯 h𝒯 (Or.inl hm) i
  | highDirect =>
      simp [CleaningScaleFacts, hm, Mode.isCluster]
      intro i
      simpa [Tiling.gain, hm] using hDirectArg 𝒯 h𝒯 (Or.inr hm) i
  | lowCluster =>
      simp [CleaningScaleFacts, hm, Mode.isCluster]
      constructor
      · intro i
        simpa [Tiling.gain, hm] using (hClusterArgs 𝒯 h𝒯 (Or.inl hm) i).1
      · intro i
        simpa [Tiling.gain, hm] using (hClusterArgs 𝒯 h𝒯 (Or.inl hm) i).2
  | highSmall =>
      simp [CleaningScaleFacts, hm, Mode.isCluster]
      constructor
      · intro i
        simpa [Tiling.gain, hm] using (hClusterArgs 𝒯 h𝒯 (Or.inr (Or.inl hm)) i).1
      · intro i
        simpa [Tiling.gain, hm] using (hClusterArgs 𝒯 h𝒯 (Or.inr (Or.inl hm)) i).2
  | highLarge =>
      simp [CleaningScaleFacts, hm, Mode.isCluster]
      constructor
      · intro i
        simpa [Tiling.gain, hm] using (hClusterArgs 𝒯 h𝒯 (Or.inr (Or.inr hm)) i).1
      · intro i
        simpa [Tiling.gain, hm] using (hClusterArgs 𝒯 h𝒯 (Or.inr (Or.inr hm)) i).2

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
