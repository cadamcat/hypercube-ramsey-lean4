import HypercubeRamsey.S13.Allocation
import HypercubeRamsey.PartC.Cleaning
import HypercubeRamsey.S13.Needs
import HypercubeRamsey.S13.StableCleaning_q_s13_clean
import HypercubeRamsey.S13.StableCleaning_sol_s13_cleanB

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

set_option maxHeartbeats 2000000 in
/-- L13.4b (sections/13, lines 251–257): own-patch degree trimming; direct, cluster, and bounded
thresholds are exactly those in `OwnDegOK`. -/
theorem own_patch_degree_trim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hApprox : UniformApproximantStatement) (hScales : ResidualScaleSpec) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        Nonempty (OwnDegreeData 𝒯 i π) := by
  classical
  have hQbdDyadic : IsDyadic κ.Qbd := hκ.bounded.1
  have hQbdPos : 1 ≤ κ.Qbd := by
    rcases hQbdDyadic with ⟨j, hj⟩
    rw [hj]
    exact Nat.one_le_pow' _ 1
  have hnEvent : ∀ᶠ k in atTop, 1 ≤ (T.S.n k : ℝ) := by
    have htend : Tendsto (fun k : ℕ => (T.S.n k : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
    exact htend.eventually (eventually_ge_atTop (1 : ℝ))
  have hnLargeEvent : ∀ᶠ k in atTop, 8 * κ.Qbd ≤ T.S.n k :=
    T.S.n_tendsto.eventually (eventually_ge_atTop (8 * κ.Qbd))
  have hnHugeEvent : ∀ᶠ k in atTop, (1000000000000 : ℕ) ≤ T.S.n k :=
    T.S.n_tendsto.eventually_ge_atTop 1000000000000
  have hHostEvent : ∀ᶠ k in atTop, LargeHost 1 (T.S.n k) (T.S.N k) := by
    filter_upwards [T.S.eventually_large 1 1] with k hk
    exact hk.2
  have hPolyExpEvent :=
    HypercubeRamsey.S13.Lane_q_s13_clean.exp_quarter_dominates_pow12 T
  filter_upwards [hnEvent, hnLargeEvent, hnHugeEvent, hHostEvent, hPolyExpEvent]
    with k hk hkLarge hkHuge hHost hPoly
  have hn : 1 ≤ T.S.n k := by omega
  have hkR : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hn
  intro 𝒯 h𝒯 i π hInput
  have directCase (hMode : 𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) :
      Nonempty (OwnDegreeData 𝒯 i π) := by
    let X := (𝒯.P i).X
    let Y := (𝒯.P i).Y
    have hX : X.Nonempty := (h𝒯.patch_nonempty i).1
    have hY : Y.Nonempty := (h𝒯.patch_nonempty i).2
    have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    have hMpos : (0 : ℝ) < (𝒯.P i).M := by
      have hcard := Finset.card_pos.mpr hX
      rw [(𝒯.P i).cardX] at hcard
      exact_mod_cast hcard
    have hSupp : (Law.unifCore Y hY).SupportedIn Y := by
      intro y hy
      simp [Law.unifCore, hy]
    have hNotCluster : ¬ 𝒯.mode.isCluster := by
      rcases hMode with h | h <;> rw [h] <;> simp [Mode.isCluster]
    have hPi : π i = Law.unifCore Y hY := by
      have h := (hInput i).2
      rw [if_neg hNotCluster] at h
      exact h
    rcases h𝒯.direct_data hMode i with ⟨hMaxScale, hGq, hMass, hLower, _⟩
    rcases (h𝒯.clique_scales i).2 hMode with ⟨_, hQlo, hQhi, hqQ⟩
    have hM1 : 0 < κ.M1 := by linarith only [hκ.M1_big.1]
    have hsqrt : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.2 hM1
    have hsqrtge : 2 ≤ Real.sqrt κ.M1 := by
      have hsq : (2 : ℝ) ^ 2 ≤ κ.M1 := by exact_mod_cast hκ.M1_big.1
      have hsqrtsq : (Real.sqrt κ.M1) ^ 2 = κ.M1 := Real.sq_sqrt hM1.le
      nlinarith only [Real.sqrt_nonneg κ.M1, hsqrtsq, hsq]
    have hqBound : ((𝒯.P i).q : ℝ) < (𝒯.P i).g := by
      have hfactor : 2 / Real.sqrt κ.M1 ≤ 1 := (div_le_one hsqrt).2 hsqrtge
      have hQle : (𝒯.Q i : ℝ) ≤ (𝒯.P i).g := by
        calc
          (𝒯.Q i : ℝ) ≤ 2 * (𝒯.P i).g / Real.sqrt κ.M1 := hQhi
          _ = (𝒯.P i).g * (2 / Real.sqrt κ.M1) := by ring
          _ ≤ (𝒯.P i).g * 1 :=
            mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg _)
          _ = (𝒯.P i).g := by ring
      have hqQ' : ((𝒯.P i).q : ℝ) < (𝒯.Q i : ℝ) := by exact_mod_cast hqQ
      exact lt_of_lt_of_le hqQ' hQle
    have hgposR : (0 : ℝ) < (𝒯.P i).g := by
      by_contra h
      have hg0Real : ((𝒯.P i).g : ℝ) = 0 :=
        le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
      have hg0 : (𝒯.P i).g = 0 := Nat.cast_eq_zero.mp hg0Real
      rw [hg0Real] at hQlo hQhi
      have hQpos : (0 : ℝ) < (𝒯.Q i : ℝ) := by
        simpa using hQlo
      have hQle0 : (𝒯.Q i : ℝ) ≤ 0 := by
        calc
          (𝒯.Q i : ℝ) ≤ 2 * (0 : ℝ) / Real.sqrt κ.M1 := hQhi
          _ = 0 := by simp
      linarith
    have hgpos : 0 < (𝒯.P i).g := by exact_mod_cast hgposR
    have hscale : κ.M1 * κ.Q0 ≤ (𝒯.P i).g := by
      have hMaxReal : κ.M1 * κ.Q0 ≤ max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := by
        exact_mod_cast hMaxScale
      have hMaxLeReal : max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) ≤ (𝒯.P i).g :=
        max_le le_rfl hqBound.le
      exact le_trans hMaxReal hMaxLeReal
    have hscaleQ : κ.Q0 ≤ (𝒯.P i).g / κ.M1 := by
      apply (le_div_iff₀ hM1).2
      simpa [mul_comm] using hscale
    have hCond := hκ.Q0_large ((𝒯.P i).g / κ.M1) hscaleQ
    have hGap0 := hCond.1
    have hM1cancel : κ.M1 * ((𝒯.P i).g / κ.M1) = (𝒯.P i).g := by
      field_simp [ne_of_gt hM1]
    have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
    have hpowNeg : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (by positivity))
    have hξlt : κ.ξ < 1 := by
      have hξα : κ.ξ < κ.α := by
        calc
          κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
          _ ≤ κ.α := mul_le_of_le_one_right (le_of_lt hκ.α_rng.1) hpowNeg
      linarith only [hξα, hκ.α_rng.2]
    have hpow4 : (1 : ℝ) ≤ 4 ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
    have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith only [hpow4]
    have hdenpos : (0 : ℝ) < 3 * (4 : ℝ) ^ (κ.u + 3) := by positivity
    have hξsq : κ.ξ ^ 2 < 1 := by nlinarith only [hξlt, hκ.ξ_rng.1]
    have hθlt : κ.θ < 1 := by
      have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) < 1 :=
        (div_lt_one hdenpos).2 (by nlinarith only [hξsq, hden])
      exact lt_trans hκ.θ_rng.2 hfrac
    have haSmall : κ.a < 1 := by rw [hκ.a_eq]; nlinarith only [hθlt]
    have hLogEq : 800 / (κ.a * (1 / 400 : ℝ)) = 320000 / κ.a := by
      field_simp [ne_of_gt ha]
      norm_num
    have hGap : Real.log (320000 / κ.a) ≤
        (2 * (𝒯.P i).g : ℝ) ^ κ.aB - (𝒯.P i).g ^ κ.aB := by
      have hGap' : Real.log (320000 / κ.a) ≤
          ((2 : ℝ) ^ κ.aB - 1) * (𝒯.P i).g ^ κ.aB := by
        rw [hLogEq] at hGap0
        simpa [hM1cancel] using hGap0
      have hPow : (2 * (𝒯.P i).g : ℝ) ^ κ.aB =
          (2 : ℝ) ^ κ.aB * (𝒯.P i).g ^ κ.aB :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      rw [hPow]
      nlinarith only [hGap']
    have hbDyadic : IsDyadic (2 * (𝒯.P i).g) := by
      rcases hScales.g_dyadic κ T k (𝒯.P i).resX (𝒯.P i).resY with ⟨j, hj⟩
      refine ⟨j + 1, ?_⟩
      rw [← (h𝒯.measured_scales i).1] at hj
      rw [hj]
      simp [pow_succ, Nat.mul_comm]
    have hgScaleEq : gScale κ T k (𝒯.P i).resX (𝒯.P i).resY = (𝒯.P i).g :=
      (h𝒯.measured_scales i).1.symm
    have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    have hMpos : (0 : ℝ) < (𝒯.P i).M := by
      have hcard := Finset.card_pos.mpr hX
      rw [(𝒯.P i).cardX] at hcard
      exact_mod_cast hcard
    have hMassScaled : (T.S.N k : ℝ) * Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤
        κ.a / 800 * (𝒯.P i).M := by
      have hExp : Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤
          Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB) * (κ.a / 320000) := by
        calc
          Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤
              Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB - Real.log (320000 / κ.a)) :=
            Real.exp_le_exp.mpr (by linarith only [hGap])
          _ = Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB) /
              (320000 / κ.a) := by
            rw [Real.exp_sub, Real.exp_log (by positivity)]
          _ = Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB) * (κ.a / 320000) := by
            field_simp [ne_of_gt ha]
      have hMass' : (T.S.N k : ℝ) * Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB) ≤
          400 * (𝒯.P i).M := by
        calc
          (T.S.N k : ℝ) * Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB) =
              400 * ((1 / 400 : ℝ) * (T.S.N k : ℝ) *
                Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB)) := by ring
          _ ≤ 400 * (𝒯.P i).M := mul_le_mul_of_nonneg_left hMass (by norm_num)
      calc
        (T.S.N k : ℝ) * Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤
            (T.S.N k : ℝ) *
              (Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB) * (κ.a / 320000)) :=
          mul_le_mul_of_nonneg_left hExp (Nat.cast_nonneg _)
        _ = ((T.S.N k : ℝ) * Real.exp (-((𝒯.P i).g : ℝ) ^ κ.aB)) *
              (κ.a / 320000) := by ring
        _ ≤ (400 * (𝒯.P i).M) * (κ.a / 320000) :=
          mul_le_mul_of_nonneg_right hMass' (div_nonneg ha.le (by norm_num))
        _ = κ.a / 800 * (𝒯.P i).M := by ring
    have hCut : (T.S.N k : ℝ) *
        Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) <
          κ.a / 4 * (𝒯.P i).M := by
      calc
        (T.S.N k : ℝ) * Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤
            κ.a / 800 * (𝒯.P i).M := hMassScaled
        _ < κ.a / 4 * (𝒯.P i).M := by
          apply mul_lt_mul_of_pos_right _ hMpos
          nlinarith only [ha]
    have hYcard' : (T.S.N k : ℝ) *
        Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤ Y.card := by
      rw [(𝒯.P i).cardY]
      have hSmall : κ.a / 800 * (𝒯.P i).M ≤ (𝒯.P i).M := by
        calc
          κ.a / 800 * (𝒯.P i).M ≤ 1 * (𝒯.P i).M :=
            mul_le_mul_of_nonneg_right (by nlinarith only [haSmall]) hMpos.le
          _ = (𝒯.P i).M := by ring
      exact le_trans hMassScaled hSmall
    have hXres : X ⊆ (𝒯.P i).resX := (h𝒯.patch_supports i).1
    have hYres : Y ⊆ (𝒯.P i).resY := (h𝒯.patch_supports i).2.2.1
    have hIotaLe : κ.ι / 2 ≤ 1 := by
      have hmin : min κ.xs (min κ.η0 (0.01 : ℝ)) ≤ 0.01 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hιsmall : κ.ι < (0.01 : ℝ) / 1000 :=
        lt_of_lt_of_le hκ.ι_rng.2 (div_le_div_of_nonneg_right hmin (by norm_num))
      nlinarith
    have hScaleG := h𝒯.direct_scale_bound hMode i
    have hGleN : (𝒯.P i).g ≤ (T.S.n k : ℝ) := by
      calc
        (𝒯.P i).g ≤ (T.S.n k : ℝ) ^ (κ.ι / 2) := hScaleG
        _ ≤ (T.S.n k : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hkR hIotaLe
        _ = T.S.n k := by rw [Real.rpow_one]
    have hbgBound : 2 * (𝒯.P i).g ≤ 2 * T.S.n k + 1 := by
      exact_mod_cast (by nlinarith only [hGleN] :
        (2 * (𝒯.P i).g : ℝ) ≤ 2 * (T.S.n k : ℝ) + 1)
    have hNpow : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
        (2 * (𝒯.P i).g : ℝ) / T.S.n k := by
      have hnR : (0 : ℝ) < T.S.n k := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hInv : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ 1 / T.S.n k := by
        have hExp := Real.rpow_le_rpow_of_exponent_le hkR
          (by norm_num : (-2 : ℝ) ≤ -1)
        calc
          (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (T.S.n k : ℝ) ^ (-1 : ℝ) := hExp
          _ = 1 / T.S.n k := by
            rw [Real.rpow_neg hnR.le, Real.rpow_one]
            simp [one_div]
      have hbLower : (1 : ℝ) ≤ (2 * (𝒯.P i).g : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ 2 * (𝒯.P i).g)
      exact le_trans hInv (div_le_div_of_nonneg_right hbLower (Nat.cast_nonneg _))
    have hNoBias {U : Finset (Fin (T.S.N k))} (hUX : U ⊆ X)
        (hUcard : (T.S.N k : ℝ) * Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤ U.card)
        (hUn : U.Nonempty)
        (hRows : ∀ x ∈ U, 2 * ((2 * (𝒯.P i).g : ℝ)) / T.S.n k <
          deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2) : False := by
      have hApproxU (x : Fin (T.S.N k)) :
          |(∑ y ∈ Y, hit (T.S.E k) 𝒯.c x y) / Y.card -
              deg (T.S.E k) 𝒯.c (π i).w x| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ) := by
        rw [hPi, HypercubeRamsey.S13.Lane_q_s13_clean.deg_unifCore]
        simp
      have hUcardCast : (T.S.N k : ℝ) *
          Real.exp (-(((2 * (𝒯.P i).g : ℕ) : ℝ) ^ κ.aB)) ≤ U.card := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hUcard
      have hYcardCast : (T.S.N k : ℝ) *
          Real.exp (-(((2 * (𝒯.P i).g : ℕ) : ℝ) ^ κ.aB)) ≤ Y.card := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hYcard'
      have hRowsCast : ∀ x ∈ U,
          2 * ((2 * (𝒯.P i).g : ℕ) : ℝ) / T.S.n k <
            deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := by
        intro x hx
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hRows x hx
      have hNpowCast : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
          ((2 * (𝒯.P i).g : ℕ) : ℝ) / T.S.n k := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNpow
      have hW := HypercubeRamsey.S13.Lane_q_s13_clean.biasWitness_of_highRows
        κ T k (2 * (𝒯.P i).g) 𝒯.c (𝒯.P i).resX (𝒯.P i).resY U Y hUn hY
        (hUX.trans hXres) hYres hUcardCast hYcardCast (π i) hApproxU hRowsCast
        (lt_of_lt_of_le Nat.zero_lt_one hn) hNpowCast
      have hglt : gScale κ T k (𝒯.P i).resX (𝒯.P i).resY < 2 * (𝒯.P i).g := by
        rw [hgScaleEq]
        omega
      exact (hScales.bias_absent κ T k (𝒯.P i).resX (𝒯.P i).resY
        (2 * (𝒯.P i).g) hbDyadic hglt hbgBound) hW
    let Bad := X.filter (fun x =>
      4 * (𝒯.P i).g / T.S.n k < deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2)
    have hBadRows (x : Fin (T.S.N k)) (hx : x ∈ Bad) :
        2 * ((2 * (𝒯.P i).g : ℝ)) / T.S.n k <
          deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := by
      have hmem := (Finset.mem_filter.mp hx).2
      change (4 : ℝ) * (𝒯.P i).g / (T.S.n k : ℝ) < _ at hmem
      convert hmem using 1 <;> ring
    have hBadCard : (Bad.card : ℝ) <
        (T.S.N k : ℝ) * Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) := by
      by_contra h
      have hLarge : (T.S.N k : ℝ) *
          Real.exp (-((2 * (𝒯.P i).g : ℝ) ^ κ.aB)) ≤ Bad.card := le_of_not_gt h
      have hBadNe : Bad.Nonempty := by
        apply Finset.card_pos.mp
        exact_mod_cast lt_of_lt_of_le
          (mul_pos hNpos (Real.exp_pos _)) hLarge
      exact hNoBias (U := Bad) (Finset.filter_subset _ _) hLarge hBadNe hBadRows
    let C := X \ Bad
    have hCsub : C ⊆ X := by simp [C]
    have hXdiffSub : X \ C ⊆ Bad := by
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxX, hxNotC⟩
      by_contra hxNotBad
      apply hxNotC
      exact Finset.mem_sdiff.mpr ⟨hxX, hxNotBad⟩
    have hLoss : ((X \ C).card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
      have hcard : ((X \ C).card : ℝ) ≤ (Bad.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hXdiffSub
      exact lt_of_le_of_lt hcard (lt_trans hBadCard hCut)
    have hOwn : ∀ x ∈ C, OwnDegOK 𝒯 i (π i) x := by
      intro x hx
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
      have hUpper : deg (T.S.E k) 𝒯.c (π i).w x ≤
          1 / 2 + 4 * (𝒯.P i).g / T.S.n k := by
        by_contra hUpper
        have hStrict : 1 / 2 + 4 * (𝒯.P i).g / T.S.n k <
            deg (T.S.E k) 𝒯.c (π i).w x := lt_of_not_ge hUpper
        have hBad : x ∈ Bad := by
          apply Finset.mem_filter.mpr
          refine ⟨hxX, ?_⟩
          linarith
        exact hxNotBad hBad
      have hLowerPi : 1 / 2 + (𝒯.P i).g / (4 * T.S.n k) ≤
          deg (T.S.E k) 𝒯.c (π i).w x := by
        simpa [hPi, one_div] using hLower x hxX
      have hLowerPi' : (2 : ℝ)⁻¹ + (𝒯.P i).g / (4 * T.S.n k) ≤
          deg (T.S.E k) 𝒯.c (π i).w x := by
        convert hLowerPi using 1 <;> norm_num
      have hUpper' : deg (T.S.E k) 𝒯.c (π i).w x ≤
          (2 : ℝ)⁻¹ + 4 * (𝒯.P i).g / T.S.n k := by
        convert hUpper using 1 <;> norm_num
      rcases hMode with hLow | hHigh
      · simpa [OwnDegOK, hLow, one_div] using ⟨hLowerPi', hUpper'⟩
      · simpa [OwnDegOK, hHigh, one_div] using ⟨hLowerPi', hUpper'⟩
    refine ⟨⟨C, hCsub, hLoss, hOwn, ?_⟩⟩
    intro hCluster
    exact (hNotCluster hCluster).elim
  have boundedCase (hMode : 𝒯.mode = .bounded) :
      Nonempty (OwnDegreeData 𝒯 i π) := by
    let X := (𝒯.P i).X
    let Y := (𝒯.P i).Y
    let b : ℕ := 8 * κ.Qbd
    have hX : X.Nonempty := (h𝒯.patch_nonempty i).1
    have hY : Y.Nonempty := (h𝒯.patch_nonempty i).2
    have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
    have hMpos : (0 : ℝ) < (𝒯.P i).M := by
      have hcard := Finset.card_pos.mpr hX
      rw [(𝒯.P i).cardX] at hcard
      exact_mod_cast hcard
    have hNotCluster : ¬ 𝒯.mode.isCluster := by rw [hMode]; simp [Mode.isCluster]
    have hPi : π i = Law.unifCore Y hY := by
      have h := (hInput i).2
      rw [if_neg hNotCluster] at h
      exact h
    rcases h𝒯.bounded_data hMode with ⟨_, hAll⟩
    rcases hAll i with ⟨_, _, _, hMass, _⟩
    rcases hκ.bounded with ⟨_, hM1Qbd, _, _, hKbdExp⟩
    have hQbdLeB : (κ.Qbd : ℝ) ≤ b := by
      dsimp [b]
      exact_mod_cast (by omega : κ.Qbd ≤ 8 * κ.Qbd)
    have hM1 : 0 < κ.M1 := by linarith only [hκ.M1_big.1]
    have hM1Q0LeB : κ.M1 * κ.Q0 ≤ (b : ℝ) :=
      le_trans hM1Qbd.le hQbdLeB
    have hQ0 : κ.Q0 ≤ (b : ℝ) / κ.M1 := by
      apply (le_div_iff₀ hM1).2
      simpa [mul_comm] using hM1Q0LeB
    have hCond := hκ.Q0_large ((b : ℝ) / κ.M1) hQ0
    have hGap0 := hCond.1
    have hM1cancel : κ.M1 * ((b : ℝ) / κ.M1) = b := by
      field_simp [ne_of_gt hM1]
    have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
    have hpowNeg : Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (by positivity))
    have hξlt : κ.ξ < 1 := by
      have hξα : κ.ξ < κ.α := by
        calc
          κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100)) := hκ.ξ_rng.2
          _ ≤ κ.α := mul_le_of_le_one_right (le_of_lt hκ.α_rng.1) hpowNeg
      linarith only [hξα, hκ.α_rng.2]
    have hpow4 : (1 : ℝ) ≤ 4 ^ (κ.u + 3) := one_le_pow₀ (by norm_num)
    have hden : (3 : ℝ) ≤ 3 * (4 : ℝ) ^ (κ.u + 3) := by nlinarith only [hpow4]
    have hdenpos : (0 : ℝ) < 3 * (4 : ℝ) ^ (κ.u + 3) := by positivity
    have hξsq : κ.ξ ^ 2 < 1 := by nlinarith only [hξlt, hκ.ξ_rng.1]
    have hθlt : κ.θ < 1 := by
      have hfrac : κ.ξ ^ 2 / (3 * (4 : ℝ) ^ (κ.u + 3)) < 1 :=
        (div_lt_one hdenpos).2 (by nlinarith only [hξsq, hden])
      exact lt_trans hκ.θ_rng.2 hfrac
    have haSmall : κ.a < 1 := by rw [hκ.a_eq]; nlinarith only [hθlt]
    have hLogEq : 800 / (κ.a * (1 / 400 : ℝ)) = 320000 / κ.a := by
      field_simp [ne_of_gt ha]
      norm_num
    have haClt : κ.aC < 1 := by
      have hmin : min κ.η0 (1 : ℝ) ≤ 1 := min_le_right _ _
      have hsmall : min κ.η0 1 / (10 ^ 6 : ℝ) ≤ 1 / (10 ^ 6 : ℝ) :=
        div_le_div_of_nonneg_right hmin (by norm_num)
      have hsmall' : (1 / (10 ^ 6 : ℝ)) < 1 := by norm_num
      exact lt_trans hκ.aC_rng.2 (lt_of_le_of_lt hsmall hsmall')
    have haBlt : κ.aB < 1 := by
      have h := hκ.aB_rng.2.1
      nlinarith only [haClt, h]
    have hFactorLe : (Real.rpow 2 κ.aB - 1) ≤ 1 := by
      have hpow : Real.rpow 2 κ.aB ≤ 2 := by
        calc
          Real.rpow 2 κ.aB ≤ Real.rpow 2 1 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) haBlt.le
          _ = 2 := Real.rpow_one 2
      linarith
    have hbPowNonneg : 0 ≤ (b : ℝ) ^ κ.aB := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hBudget : Real.log (320000 / κ.a) ≤ (b : ℝ) ^ κ.aB := by
      have hGap' : Real.log (320000 / κ.a) ≤
          (Real.rpow 2 κ.aB - 1) * (b : ℝ) ^ κ.aB := by
        rw [hLogEq] at hGap0
        simpa [hM1cancel] using hGap0
      have hGap'' : (Real.rpow 2 κ.aB - 1) * (b : ℝ) ^ κ.aB ≤
          1 * (b : ℝ) ^ κ.aB :=
        mul_le_mul_of_nonneg_right hFactorLe hbPowNonneg
      have hGapFinal : (Real.rpow 2 κ.aB - 1) * (b : ℝ) ^ κ.aB ≤ (b : ℝ) ^ κ.aB := by
        calc
          (Real.rpow 2 κ.aB - 1) * (b : ℝ) ^ κ.aB ≤
              1 * (b : ℝ) ^ κ.aB := hGap''
          _ = (b : ℝ) ^ κ.aB := by ring
      exact le_trans hGap' hGapFinal
    have hRatio : Real.exp (-((b : ℝ) ^ κ.aB)) ≤ κ.a / 320000 := by
      calc
        Real.exp (-((b : ℝ) ^ κ.aB)) ≤ Real.exp (-Real.log (320000 / κ.a)) :=
          Real.exp_le_exp.mpr (by linarith only [hBudget])
        _ = κ.a / 320000 := by
          rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) ha)]
          field_simp [ne_of_gt ha]
    have hNmass : (T.S.N k : ℝ) ≤ 400 * (𝒯.P i).M := by
      have := hMass
      nlinarith
    have hMassScaled : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤
        κ.a / 800 * (𝒯.P i).M := by
      calc
        (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤
            (T.S.N k : ℝ) * (κ.a / 320000) :=
          mul_le_mul_of_nonneg_left hRatio (Nat.cast_nonneg _)
        _ ≤ (400 * (𝒯.P i).M) * (κ.a / 320000) :=
          mul_le_mul_of_nonneg_right hNmass (div_nonneg ha.le (by norm_num))
        _ = κ.a / 800 * (𝒯.P i).M := by ring
    have hCut : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) <
        κ.a / 4 * (𝒯.P i).M := by
      calc
        (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤
            κ.a / 800 * (𝒯.P i).M := hMassScaled
        _ < κ.a / 4 * (𝒯.P i).M := by
          have hcoef : κ.a / 800 < κ.a / 4 := by
            have h := mul_lt_mul_of_pos_left
              (by norm_num : (1 / 800 : ℝ) < 1 / 4) ha
            simpa [div_eq_mul_inv, mul_comm] using h
          exact mul_lt_mul_of_pos_right hcoef hMpos
    have hYcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ Y.card := by
      rw [(𝒯.P i).cardY]
      have hsmall : κ.a / 800 * (𝒯.P i).M ≤ (𝒯.P i).M := by
        have hMnonneg : (0 : ℝ) ≤ (𝒯.P i).M := Nat.cast_nonneg _
        have hcoef : κ.a / 800 ≤ 1 := by
          apply (div_le_one (by norm_num : (0 : ℝ) < 800)).2
          linarith only [haSmall]
        calc
          κ.a / 800 * (𝒯.P i).M ≤ 1 * (𝒯.P i).M :=
            mul_le_mul_of_nonneg_right hcoef hMnonneg
          _ = (𝒯.P i).M := by ring
      exact le_trans hMassScaled hsmall
    have hXres : X ⊆ (𝒯.P i).resX := (h𝒯.patch_supports i).1
    have hYres : Y ⊆ (𝒯.P i).resY := (h𝒯.patch_supports i).2.2.1
    have hQbdPowLarge : 16 * (κ.Qbd : ℝ) ≤ κ.Kbd := by
      have hP : 21000 ≤ κ.P := by
        have hp := hκ.P_big.2
        rw [hκ.Ac_eq] at hp
        norm_num at hp
        exact hp
      have hPpos : 0 < κ.P := by omega
      have hR : 1 ≤ κ.R := by
        rw [hκ.R_eq]
        have hp : 0 < κ.P ^ 2 := Nat.pow_pos hPpos
        omega
      have hL : 500 ≤ κ.L := by
        rw [hκ.L_eq]
        calc
          500 = 500 * 1 := by norm_num
          _ ≤ 500 * κ.R := Nat.mul_le_mul_left 500 hR
      have hLcast : (500 : ℝ) ≤ κ.L := by exact_mod_cast hL
      have hu : (16 : ℝ) ≤ κ.u := by
        have hu' : 10 * (κ.L : ℝ) ^ 2 < (κ.u : ℝ) := by
          exact_mod_cast hκ.u_rng.2
        have hLsq : (500 : ℝ) ^ 2 ≤ (κ.L : ℝ) ^ 2 := by
          nlinarith only [sq_nonneg ((κ.L : ℝ) - 500), hLcast]
        nlinarith only [hu', hLsq]
      have hCstar : 16 ≤ Cstar κ.u κ.ξ := by
        unfold Cstar
        have hfloor : 0 ≤ (⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊ : ℝ) := Nat.cast_nonneg _
        nlinarith only [hu, hfloor]
      have hQbdReal : (1 : ℝ) ≤ κ.Qbd := by exact_mod_cast hQbdPos
      have hmul : 16 * (κ.Qbd : ℝ) ≤ Cstar κ.u κ.ξ * κ.Qbd :=
        mul_le_mul_of_nonneg_right hCstar (Nat.cast_nonneg _)
      have hexp := Real.add_one_le_exp (Cstar κ.u κ.ξ * κ.Qbd)
      have hexp' : 16 * (κ.Qbd : ℝ) ≤
          Real.exp (Cstar κ.u κ.ξ * κ.Qbd) := by
        linarith only [hmul, hexp]
      exact le_trans hexp' hKbdExp
    have hKbdScale : 16 * (κ.Qbd : ℝ) ≤ κ.Kbd := hQbdPowLarge
    have hKbdWindow : 2 * (b : ℝ) ≤ κ.Kbd := by
      have hbCast : (b : ℝ) = 8 * (κ.Qbd : ℝ) := by simp [b, Nat.cast_mul]
      calc
        2 * (b : ℝ) = 16 * (κ.Qbd : ℝ) := by rw [hbCast]; ring
        _ ≤ κ.Kbd := hKbdScale
    have hFactorWindow : 2 * (b : ℝ) / T.S.n k ≤ κ.Kbd / T.S.n k :=
      div_le_div_of_nonneg_right hKbdWindow (Nat.cast_nonneg _)
    have hbDyadic : IsDyadic b := by
      rcases hQbdDyadic with ⟨j, hj⟩
      refine ⟨j + 3, ?_⟩
      dsimp [b]
      rw [hj]
      calc
        8 * 2 ^ j = 2 ^ 3 * 2 ^ j := by norm_num
        _ = 2 ^ (3 + j) := by rw [← pow_add]
        _ = 2 ^ (j + 3) := by congr 1 <;> omega
    have hbBound : b ≤ 2 * T.S.n k + 1 := by omega
    have hgScaleEq : gScale κ T k (𝒯.P i).resX (𝒯.P i).resY = (𝒯.P i).g :=
      (h𝒯.measured_scales i).1.symm
    have hgScaleLt : gScale κ T k (𝒯.P i).resX (𝒯.P i).resY < b := by
      rw [hgScaleEq]
      have hGleMaxReal : ((𝒯.P i).g : ℝ) ≤
          max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := le_max_left _ _
      have hCutoff : max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) < κ.M1 * κ.Q0 := by
        exact_mod_cast h𝒯.bounded_scale_cutoff hMode i
      have hGltB : ((𝒯.P i).g : ℝ) < (b : ℝ) := by
        calc
          (𝒯.P i).g ≤ max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := hGleMaxReal
          _ < κ.M1 * κ.Q0 := hCutoff
          _ < κ.Qbd := hM1Qbd
          _ ≤ b := hQbdLeB
      exact_mod_cast hGltB
    have hNoWitness : ¬ BiasWitness κ T k (𝒯.P i).resX (𝒯.P i).resY b :=
      hScales.bias_absent κ T k (𝒯.P i).resX (𝒯.P i).resY b hbDyadic hgScaleLt hbBound
    have hNpow : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (b : ℝ) / T.S.n k := by
      have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hInv : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ 1 / T.S.n k := by
        have hExp := Real.rpow_le_rpow_of_exponent_le hkR
          (by norm_num : (-2 : ℝ) ≤ -1)
        calc
          (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (T.S.n k : ℝ) ^ (-1 : ℝ) := hExp
          _ = 1 / T.S.n k := by rw [Real.rpow_neg hnR.le, Real.rpow_one]; simp [one_div]
      have hbOne : (1 : ℝ) ≤ b := by
        dsimp [b]
        exact_mod_cast (by omega : 1 ≤ 8 * κ.Qbd)
      exact le_trans hInv (div_le_div_of_nonneg_right hbOne (Nat.cast_nonneg _))
    have hApproxU (x : Fin (T.S.N k)) :
        |(∑ y ∈ Y, hit (T.S.E k) 𝒯.c x y) / Y.card -
            deg (T.S.E k) 𝒯.c (π i).w x| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ) := by
      rw [hPi, HypercubeRamsey.S13.Lane_q_s13_clean.deg_unifCore]
      simp
    have hNoHigh {U : Finset (Fin (T.S.N k))} (hUX : U ⊆ X)
        (hUcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ U.card)
        (hUn : U.Nonempty)
        (hRows : ∀ x ∈ U, 2 * (b : ℝ) / T.S.n k <
          deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2) : False := by
      have hW := HypercubeRamsey.S13.Lane_q_s13_clean.biasWitness_of_highRows
        κ T k b 𝒯.c (𝒯.P i).resX (𝒯.P i).resY U Y hUn hY
        (hUX.trans hXres) hYres hUcard hYcard (π i) hApproxU hRows
        (lt_of_lt_of_le Nat.zero_lt_one hn) hNpow
      exact hNoWitness hW
    have hNoLow {U : Finset (Fin (T.S.N k))} (hUX : U ⊆ X)
        (hUcard : (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) ≤ U.card)
        (hUn : U.Nonempty)
        (hRows : ∀ x ∈ U, 2 * (b : ℝ) / T.S.n k <
          1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x) : False := by
      have hW := HypercubeRamsey.S13.Lane_q_s13_clean.biasWitness_of_lowRows
        κ T k b 𝒯.c (𝒯.P i).resX (𝒯.P i).resY U Y hUn hY
        (hUX.trans hXres) hYres hUcard hYcard (π i) hApproxU hRows
        (lt_of_lt_of_le Nat.zero_lt_one hn) hNpow
      exact hNoWitness hW
    let BadHigh := X.filter (fun x =>
      κ.Kbd / T.S.n k < deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2)
    let BadLow := X.filter (fun x =>
      κ.Kbd / T.S.n k < 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x)
    have hHighRows (x : Fin (T.S.N k)) (hx : x ∈ BadHigh) :
        2 * (b : ℝ) / T.S.n k < deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := by
      have hxFilter : x ∈ X.filter (fun x =>
          κ.Kbd / T.S.n k < deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2) := by
        simpa [BadHigh] using hx
      have hbad := (Finset.mem_filter.mp hxFilter).2
      exact lt_of_le_of_lt hFactorWindow hbad
    have hLowRows (x : Fin (T.S.N k)) (hx : x ∈ BadLow) :
        2 * (b : ℝ) / T.S.n k < 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x := by
      have hxFilter : x ∈ X.filter (fun x =>
          κ.Kbd / T.S.n k < 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x) := by
        simpa [BadLow] using hx
      have hbad := (Finset.mem_filter.mp hxFilter).2
      exact lt_of_le_of_lt hFactorWindow hbad
    have hHighCard : (BadHigh.card : ℝ) <
        (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) := by
      by_contra h
      have hLarge := le_of_not_gt h
      have hNe : BadHigh.Nonempty := by
        apply Finset.card_pos.mp
        exact_mod_cast lt_of_lt_of_le (mul_pos hNpos (Real.exp_pos _)) hLarge
      exact hNoHigh (U := BadHigh) (by simpa [BadHigh] using Finset.filter_subset _ _)
        hLarge hNe hHighRows
    have hLowCard : (BadLow.card : ℝ) <
        (T.S.N k : ℝ) * Real.exp (-((b : ℝ) ^ κ.aB)) := by
      by_contra h
      have hLarge := le_of_not_gt h
      have hNe : BadLow.Nonempty := by
        apply Finset.card_pos.mp
        exact_mod_cast lt_of_lt_of_le (mul_pos hNpos (Real.exp_pos _)) hLarge
      exact hNoLow (U := BadLow) (by simpa [BadLow] using Finset.filter_subset _ _)
        hLarge hNe hLowRows
    let Bad := BadHigh ∪ BadLow
    have hBadCard : (Bad.card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
      have hUnion : (Bad.card : ℝ) ≤ (BadHigh.card : ℝ) + (BadLow.card : ℝ) := by
        exact_mod_cast Finset.card_union_le BadHigh BadLow
      have hHighSmall : (BadHigh.card : ℝ) < κ.a / 800 * (𝒯.P i).M :=
        lt_of_lt_of_le hHighCard hMassScaled
      have hLowSmall : (BadLow.card : ℝ) < κ.a / 800 * (𝒯.P i).M :=
        lt_of_lt_of_le hLowCard hMassScaled
      nlinarith only [hUnion, hHighSmall, hLowSmall, ha, hMpos]
    let C := X \ Bad
    have hCsub : C ⊆ X := by simp [C]
    have hXdiffSub : X \ C ⊆ Bad := by
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxX, hxNotC⟩
      by_contra hxNotBad
      exact hxNotC (Finset.mem_sdiff.mpr ⟨hxX, hxNotBad⟩)
    have hLoss : ((X \ C).card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
      exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hXdiffSub) hBadCard
    have hOwn : ∀ x ∈ C, OwnDegOK 𝒯 i (π i) x := by
      intro x hx
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
      have hxNotHigh : x ∉ BadHigh := fun h => hxNotBad (Finset.mem_union_left _ h)
      have hxNotLow : x ∉ BadLow := fun h => hxNotBad (Finset.mem_union_right _ h)
      have hUpper : deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 ≤ κ.Kbd / T.S.n k := by
        by_contra h
        push_neg at h
        exact hxNotHigh (Finset.mem_filter.mpr ⟨hxX, h⟩)
      have hLower : 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x ≤ κ.Kbd / T.S.n k := by
        by_contra h
        push_neg at h
        exact hxNotLow (Finset.mem_filter.mpr ⟨hxX, h⟩)
      have hAbs : |deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2| ≤ κ.Kbd / T.S.n k :=
        abs_le.mpr ⟨by linarith only [hLower], by linarith only [hUpper]⟩
      simpa [OwnDegOK, hMode] using hAbs
    refine ⟨⟨C, hCsub, hLoss, hOwn, ?_⟩⟩
    intro hCluster
    exact (hNotCluster hCluster).elim
  have clusterCase (hMode : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
      𝒯.mode = .highLarge) : Nonempty (OwnDegreeData 𝒯 i π) := by
    classical
    let X := (𝒯.P i).X
    let q := (𝒯.P i).q
    let xpow : ℝ := Real.rpow (q : ℝ) κ.Cb
    have hX : X.Nonempty := (h𝒯.patch_nonempty i).1
    have hqNat : 1 ≤ q := by
      change 1 ≤ (𝒯.P i).q
      rw [(h𝒯.measured_scales i).2]
      unfold qScale
      exact Nat.one_le_pow' _ 1
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqNat
    have hCbPos : 0 < κ.Cb := by
      have haB : 0 < κ.aB := hκ.aB_rng.1
      have haC : 0 < κ.aC := hκ.aC_rng.1
      have hCb := hκ.Cb_big
      have hterm : 0 < 100 * κ.aC / κ.aB := by positivity
      linarith
    have hxpow : 1 ≤ xpow := by
      dsimp [xpow]
      exact Real.one_le_rpow hq (le_of_lt hCbPos)
    obtain ⟨b, hbDyadic, hbx, hbxUpper⟩ :=
      HypercubeRamsey.S13.Lane_q_s13_clean.exists_dyadic_ceiling hxpow
    have hBpow : 0 ≤ (b : ℝ) ^ κ.aB := Real.rpow_nonneg (Nat.cast_nonneg _) _
    by_cases hTrivial : 2 * T.S.n k + 1 < b
    · let C := X
      have hMpos : (0 : ℝ) < (𝒯.P i).M := by
        have hcard := Finset.card_pos.mpr hX
        rw [(𝒯.P i).cardX] at hcard
        exact_mod_cast hcard
      have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
      have hxlarge : (T.S.n k : ℝ) < xpow := by
        have hbcast : (2 * T.S.n k + 1 : ℕ) < b := hTrivial
        have hbc : 2 * (T.S.n k : ℝ) + 1 < (b : ℝ) := by exact_mod_cast hbcast
        have hxlt : (b : ℝ) < 2 * xpow := hbxUpper
        nlinarith
      have hWindow : (1 / 2 : ℝ) ≤ 10 * xpow / T.S.n k := by
        have hnpos : (0 : ℝ) < T.S.n k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hdiv : (1 : ℝ) < xpow / T.S.n k := by
          apply (lt_div_iff₀ hnpos).2
          simpa using hxlarge
        calc
          (1 / 2 : ℝ) ≤ 10 * (xpow / T.S.n k) := by linarith
          _ = 10 * xpow / T.S.n k := by ring
      have hHalf (μ : Law (T.S.N k)) (x : Fin (T.S.N k)) :
          |deg (T.S.E k) 𝒯.c μ.w x - 1 / 2| ≤ 1 / 2 := by
        rcases HypercubeRamsey.S13.Lane_q_s13_clean.deg_bounds
          (T.S.E k) 𝒯.c μ x with ⟨h0, h1⟩
        rw [abs_le]
        constructor <;> linarith
      have hOwnAt (μ : Law (T.S.N k)) (x : Fin (T.S.N k)) :
          OwnDegOK 𝒯 i μ x := by
        have h := hHalf μ x
        have hWindow' : (1 / 2 : ℝ) ≤
            10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb / T.S.n k := by
          simpa [xpow, q] using hWindow
        have hOwnBound : |deg (T.S.E k) 𝒯.c μ.w x - 1 / 2| ≤
            10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb / T.S.n k :=
          le_trans h hWindow'
        rcases hMode with hLow | hSmall | hLarge
        · simpa [OwnDegOK, hLow] using hOwnBound
        · simpa [OwnDegOK, hSmall] using hOwnBound
        · simpa [OwnDegOK, hLarge] using hOwnBound
      have hLoss : ((X \ C).card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
        simp [C]
        positivity
      have hOwn : ∀ x ∈ C, OwnDegOK 𝒯 i (π i) x := by
        intro x hx
        exact hOwnAt (π i) x
      refine ⟨⟨C, ?_, hLoss, hOwn, ?_⟩⟩
      · exact Finset.Subset.rfl
      · intro _ π' _ x hx
        exact hOwnAt (π' i) x
    ·
      rcases h𝒯.cluster_data hMode i with
        ⟨hMaxScale, hGscale, hMass, _, _, _, _, hHeight, hHeightUpper, _, _, _⟩
      have hM1 : 0 < κ.M1 := by linarith only [hκ.M1_big.1]
      have hMqReal : max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) ≤
          κ.M1 * (𝒯.P i).q := by
        apply max_le hGscale
        have hfactor : 0 ≤ (κ.M1 - 1) * (𝒯.P i).q :=
          mul_nonneg (by linarith only [hκ.M1_big.1]) (Nat.cast_nonneg _)
        nlinarith only [hfactor]
      have hMaxReal : κ.M1 * κ.Q0 ≤
          max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := by
        exact_mod_cast hMaxScale
      have hQ0 : κ.Q0 ≤ (𝒯.P i).q := by
        have hprod : κ.Q0 * κ.M1 ≤ (𝒯.P i).q * κ.M1 := by
          calc
            κ.Q0 * κ.M1 = κ.M1 * κ.Q0 := by ring
            _ ≤ max ((𝒯.P i).g : ℝ) ((𝒯.P i).q : ℝ) := hMaxReal
            _ ≤ κ.M1 * (𝒯.P i).q := hMqReal
            _ = (𝒯.P i).q * κ.M1 := by ring
        exact (mul_le_mul_iff_left₀ hM1).mp hprod
      rcases hκ.Q0_large (𝒯.P i).q hQ0 with
        ⟨_, _, _, hScaleGap, hSamplerGap, hDegreeGap, _, _, _⟩
      have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
      have hLogEq : 800 / (κ.a * (1 / 400 : ℝ)) = 320000 / κ.a := by
        field_simp [ne_of_gt ha]
        norm_num
      have hRpowModeLe :
          Real.rpow ((𝒯.P i).q : ℝ)
            (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) ≤
          Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi := by
        have hMloMhi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
          have hcq : 0 < κ.cq := hκ.cq_rng.1
          have hterm : 0 ≤ 10 / κ.cq := by positivity
          have hstep : (κ.Mlo : ℝ) ≤ κ.Mlo + 10 / κ.cq := by linarith
          exact le_trans hstep hκ.Mhi_big.1
        have hExponent :
            (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) ≤ κ.Mhi := by
          by_cases hLow : 𝒯.mode = .lowCluster <;> simp [hLow, hMloMhi]
        exact Real.rpow_le_rpow_of_exponent_le hq hExponent
      have hHeightUpper' : (𝒯.P i).h <
          2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi := by
        have hHeightUpperCast : ((𝒯.P i).h : ℝ) <
            2 * Real.rpow ((𝒯.P i).q : ℝ)
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by
          simpa only [Nat.cast_ite] using hHeightUpper
        exact lt_of_lt_of_le hHeightUpperCast
          (mul_le_mul_of_nonneg_left hRpowModeLe (by norm_num))
      have hHeightOne : 1 ≤ (𝒯.P i).h := by
        have hqReal : (1 : ℝ) ≤ (𝒯.P i).q := by exact_mod_cast hqNat
        have hExponentPos :
            0 ≤ (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by positivity
        have hpow : 1 ≤ Real.rpow ((𝒯.P i).q : ℝ)
            (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by
          calc
            1 = Real.rpow 1
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) := by simp
            _ ≤ Real.rpow ((𝒯.P i).q : ℝ)
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else (κ.Mhi : ℝ)) :=
              Real.rpow_le_rpow (by norm_num) hqReal hExponentPos
        have hheight' : (1 : ℝ) ≤ (𝒯.P i).h := le_trans hpow hHeight
        exact_mod_cast hheight'
      have hKupper : (𝒯.kScale i : ℝ) <
          Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) + 1 := by
        change (sliceK κ (𝒯.P i).h : ℝ) < _
        unfold sliceK
        exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hTupper : (𝒯.tScale i : ℝ) <
          Real.rpow ((𝒯.P i).h : ℝ) κ.ω + 1 := by
        change (sliceT κ (𝒯.P i).h : ℝ) < _
        unfold sliceT
        exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hktBound : (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤
          4 * Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
        have hHone : (1 : ℝ) ≤ (𝒯.P i).h := by exact_mod_cast hHeightOne
        have hω : 0 < κ.ω := hκ.ω_rng.1
        have hpow1 : 1 ≤ Real.rpow ((𝒯.P i).h : ℝ) κ.ω :=
          Real.one_le_rpow hHone hω.le
        have hpow3 : Real.rpow ((𝒯.P i).h : ℝ) κ.ω ≤
            Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) := by
          apply Real.rpow_le_rpow_of_exponent_le hHone
          have hωnonneg : 0 ≤ κ.ω := hω.le
          linarith only [hωnonneg]
        have hprod :
            (Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) + 1) *
              (Real.rpow ((𝒯.P i).h : ℝ) κ.ω + 1) ≤
              4 * Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
          have hpow4 :
              Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) *
                Real.rpow ((𝒯.P i).h : ℝ) κ.ω =
                  Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
            calc
              Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) *
                  Real.rpow ((𝒯.P i).h : ℝ) κ.ω =
                Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω + κ.ω) := by
                  exact (Real.rpow_add
                    (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hHeightOne))
                    (3 * κ.ω) κ.ω).symm
              _ = Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by congr 1 <;> ring
          have hA : Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) ≤
              Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
            apply Real.rpow_le_rpow_of_exponent_le hHone
            have hωnonneg : 0 ≤ κ.ω := hω.le
            linarith only [hωnonneg]
          have hB : Real.rpow ((𝒯.P i).h : ℝ) κ.ω ≤
              Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
            apply Real.rpow_le_rpow_of_exponent_le hHone
            have hωnonneg : 0 ≤ κ.ω := hω.le
            linarith only [hωnonneg]
          have hOne : (1 : ℝ) ≤ Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
            apply Real.one_le_rpow hHone
            positivity
          calc
            (Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) + 1) *
                (Real.rpow ((𝒯.P i).h : ℝ) κ.ω + 1) =
              Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) *
                Real.rpow ((𝒯.P i).h : ℝ) κ.ω +
                Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) +
                Real.rpow ((𝒯.P i).h : ℝ) κ.ω + 1 := by ring
            _ ≤
                4 * Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
              calc
                Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) *
                    Real.rpow ((𝒯.P i).h : ℝ) κ.ω +
                    Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) +
                    Real.rpow ((𝒯.P i).h : ℝ) κ.ω + 1 ≤
                    Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) +
                    Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) +
                    Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) +
                    Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by
                  rw [hpow4]
                  exact add_le_add (add_le_add (add_le_add le_rfl hA) hB) hOne
                _ = 4 * Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := by ring
        have hscalePos : 0 ≤ (𝒯.kScale i : ℝ) := Nat.cast_nonneg _
        have htimePos : 0 ≤ (𝒯.tScale i : ℝ) := Nat.cast_nonneg _
        have hmul := mul_le_mul hKupper.le hTupper.le htimePos
          (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num))
        calc
          (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤
              (Real.rpow ((𝒯.P i).h : ℝ) (3 * κ.ω) + 1) *
                (Real.rpow ((𝒯.P i).h : ℝ) κ.ω + 1) := hmul
          _ ≤ 4 * Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := hprod
      have homegaSmall : 4 * κ.ω * κ.Mhi < κ.aC / 100 := by
        have hωM := hκ.ω_rng.2
        have hωMpos : 0 ≤ κ.ω * κ.Mhi :=
          mul_nonneg hκ.ω_rng.1.le (Nat.cast_nonneg _)
        have hfour : 4 * κ.ω * κ.Mhi ≤ 5 * κ.ω * κ.Mhi := by
          nlinarith only [hωMpos]
        exact lt_of_le_of_lt hfour hωM
      have hHpow : Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) ≤
          Real.rpow (2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi) (4 * κ.ω) := by
        have hHnonneg : 0 ≤ (𝒯.P i).h := Nat.cast_nonneg _
        have hHnonnegR : 0 ≤ ((𝒯.P i).h : ℝ) := Nat.cast_nonneg _
        have hBaseNonneg : 0 ≤ 2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have hexpNonneg : 0 ≤ 4 * κ.ω := mul_nonneg (by norm_num) hκ.ω_rng.1.le
        exact Real.rpow_le_rpow hHnonnegR hHeightUpper'.le hexpNonneg
      have hHpow' : Real.rpow (2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi)
          (4 * κ.ω) ≤ 2 * Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi) := by
        have htwo : Real.rpow 2 (4 * κ.ω) ≤ 2 := by
          have hAClt : κ.aC < 1 := by
            have hmin : min κ.η0 (1 : ℝ) ≤ 1 := min_le_right _ _
            have hsmall : min κ.η0 1 / (10 ^ 6 : ℝ) ≤ 1 / (10 ^ 6 : ℝ) :=
              div_le_div_of_nonneg_right hmin (by norm_num)
            have hsmall' : (1 / (10 ^ 6 : ℝ)) < 1 := by norm_num
            exact lt_trans hκ.aC_rng.2 (lt_of_le_of_lt hsmall hsmall')
          have hExp : 4 * κ.ω ≤ 1 := by
            have hMhi : (1 : ℝ) ≤ κ.Mhi := by
              have h := hκ.Mhi_big.1
              have hMlo : (0 : ℝ) ≤ κ.Mlo := Nat.cast_nonneg _
              have hterm : 0 < (10 : ℝ) / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
              have hpos : 0 < (κ.Mhi : ℝ) := by linarith only [h, hMlo, hterm]
              have hMhiNat : 0 < κ.Mhi := by exact_mod_cast hpos
              exact_mod_cast (show 1 ≤ κ.Mhi by omega)
            have hCoeff : (0 : ℝ) ≤ (5 : ℝ) * κ.ω :=
              mul_nonneg (by norm_num) hκ.ω_rng.1.le
            have hωMlo : 5 * κ.ω ≤ 5 * κ.ω * κ.Mhi := by
              calc
                5 * κ.ω = 5 * κ.ω * 1 := by ring
                _ ≤ 5 * κ.ω * κ.Mhi := mul_le_mul_of_nonneg_left hMhi hCoeff
            have hsmall : κ.aC / 100 < (1 / 100 : ℝ) := by nlinarith only [hAClt]
            have hωineq : 5 * κ.ω < (1 / 100 : ℝ) :=
              lt_of_le_of_lt hωMlo (lt_trans hκ.ω_rng.2 hsmall)
            have hωsmall : κ.ω < (1 / 500 : ℝ) := by nlinarith only [hωineq]
            nlinarith only [hωsmall]
          calc
            Real.rpow 2 (4 * κ.ω) ≤ Real.rpow 2 1 :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
            _ = 2 := Real.rpow_one 2
        have hqrpowNonneg : 0 ≤ Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hqnonneg : (0 : ℝ) ≤ (𝒯.P i).q := Nat.cast_nonneg _
        have hNested :
            Real.rpow (Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi) (4 * κ.ω) =
              Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi) := by
          have hmul := Real.rpow_mul hqnonneg κ.Mhi (4 * κ.ω)
          have hexpEq : κ.Mhi * (4 * κ.ω) = 4 * κ.ω * κ.Mhi := by ring
          rw [hexpEq] at hmul
          exact hmul.symm
        have htwoNonneg : (0 : ℝ) ≤ 2 := by norm_num
        calc
          Real.rpow (2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi) (4 * κ.ω) =
              Real.rpow 2 (4 * κ.ω) *
                Real.rpow (Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi) (4 * κ.ω) :=
            Real.mul_rpow htwoNonneg hqrpowNonneg
          _ = Real.rpow 2 (4 * κ.ω) *
                Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi) := by
            rw [hNested]
          _ ≤ 2 * Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi) :=
            mul_le_mul_of_nonneg_right htwo
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have hktWide : (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤
          8 * Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi) := by
        calc
          (𝒯.kScale i : ℝ) * 𝒯.tScale i ≤
              4 * Real.rpow ((𝒯.P i).h : ℝ) (4 * κ.ω) := hktBound
          _ ≤ 4 * Real.rpow (2 * Real.rpow ((𝒯.P i).q : ℝ) κ.Mhi) (4 * κ.ω) :=
            mul_le_mul_of_nonneg_left hHpow (by norm_num)
          _ ≤ 4 * (2 * Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi)) :=
            mul_le_mul_of_nonneg_left hHpow' (by norm_num)
          _ = 8 * Real.rpow ((𝒯.P i).q : ℝ) (4 * κ.ω * κ.Mhi) := by ring
      have hQtwo : Real.rpow ((𝒯.P i).q : ℝ) (2 * κ.aC) ≥
          2 * Real.rpow ((𝒯.P i).q : ℝ) κ.aC +
            2 * Real.rpow (2 * (𝒯.P i).q) (4 * κ.ω * κ.Mhi) +
            Real.log (320000 / κ.a) := by
        have hDegreeGap' := hDegreeGap
        rw [hLogEq] at hDegreeGap'
        exact hDegreeGap'
      let Bsampler : ℝ := Real.rpow ((𝒯.P i).q : ℝ) (κ.Cb * κ.aB)
      let cap : ℝ := 10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i
      let W : ℝ := Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + cap
      have hCbExp : 2 * κ.aC ≤ κ.Cb * κ.aB := by
        have h := mul_lt_mul_of_pos_right hκ.Cb_big hκ.aB_rng.1
        have h' : 100 * κ.aC + 100 * κ.aB < κ.Cb * κ.aB := by
          convert h using 1 <;> field_simp [ne_of_gt hκ.aB_rng.1] <;> ring
        have hleft : 2 * κ.aC ≤ 100 * κ.aC + 100 * κ.aB := by
          nlinarith only [hκ.aC_rng.1, hκ.aB_rng.1]
        exact le_of_lt (lt_of_le_of_lt hleft h')
      have hBsamplerLe : Bsampler ≤ Real.rpow (b : ℝ) κ.aB := by
        dsimp [Bsampler]
        calc
          Real.rpow ((𝒯.P i).q : ℝ) (κ.Cb * κ.aB) =
              Real.rpow (Real.rpow ((𝒯.P i).q : ℝ) κ.Cb) κ.aB :=
            Real.rpow_mul (x := (𝒯.P i).q) (Nat.cast_nonneg _) κ.Cb κ.aB
          _ ≤ Real.rpow (b : ℝ) κ.aB :=
            Real.rpow_le_rpow (by positivity) hbx (le_of_lt hκ.aB_rng.1)
      have hIsCluster : 𝒯.mode.isCluster := by
        rcases hMode with h | h | h
        · rw [h]
          simp [Mode.isCluster]
        · rw [h]
          simp [Mode.isCluster]
        · rw [h]
          simp [Mode.isCluster]
      have hInputi := hInput i
      have hPiSupport : (π i).SupportedIn (𝒯.P i).Y := hInputi.1
      have hNpos : (0 : ℝ) < T.S.N k := by exact_mod_cast T.S.N_pos k
      have hMpos : (0 : ℝ) < (𝒯.P i).M := by
        have hcard := Finset.card_pos.mpr (h𝒯.patch_nonempty i).1
        rw [(𝒯.P i).cardX] at hcard
        exact_mod_cast hcard
      have hPiCap : ∀ y, (𝒯.P i).M * (π i).w y ≤ Real.exp cap := by
        have h := hInputi.2
        rw [if_pos hIsCluster] at h
        simpa [cap] using h
      have hPiWidth : (π i).WidthLE W := by
        intro y
        by_cases hy : y ∈ (𝒯.P i).Y
        · have hcapy := hPiCap y
          have hcapy' : (π i).w y * (𝒯.P i).M ≤ Real.exp cap := by
            simpa [mul_comm] using hcapy
          have hatom : (π i).w y ≤ Real.exp cap / (𝒯.P i).M :=
            (le_div_iff₀ hMpos).2 hcapy'
          have hwidthEq : Real.exp cap / (𝒯.P i).M =
              Real.exp W / (T.S.N k : ℝ) := by
            dsimp [W]
            rw [Real.exp_add, Real.exp_log (div_pos hNpos hMpos)]
            field_simp [ne_of_gt hNpos, ne_of_gt hMpos]
            <;> ring
          rw [hwidthEq] at hatom
          exact hatom
        · have hzero := hPiSupport y hy
          rw [hzero]
          positivity
      have hSamplerParams :
          Bsampler ≤ Real.sqrt (T.S.n k) ∧
          W ≤ Real.sqrt (T.S.n k) ∧
          W + 2 ≤ Bsampler ∧
          (T.S.n k : ℝ) ^ 12 ≤ (T.S.N k : ℝ) * Real.exp (-(Bsampler + W) / 2) := by
        have hnR : (0 : ℝ) < T.S.n k := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have haCsmall : κ.aC < (1 / 1000000 : ℝ) := by
          have hmin : min κ.η0 (1 : ℝ) ≤ 1 := min_le_right _ _
          have hdiv : min κ.η0 (1 : ℝ) / (10 : ℝ) ^ 6 ≤
              1 / (10 : ℝ) ^ 6 :=
            div_le_div_of_nonneg_right hmin (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 6)
          have haCsmall' : κ.aC < min κ.η0 (1 : ℝ) / 1000000 := by
            have h := hκ.aC_rng.2
            rw [show (10 : ℝ) ^ 6 = 1000000 by norm_num] at h
            exact h
          have hdiv' : min κ.η0 (1 : ℝ) / 1000000 ≤ 1 / 1000000 := by
            rw [show (10 : ℝ) ^ 6 = 1000000 by norm_num] at hdiv
            exact hdiv
          exact lt_of_lt_of_le haCsmall' hdiv'
        have haBquarter : κ.aB ≤ (1 / 4 : ℝ) := by
          nlinarith only [hκ.aB_rng.2.1, haCsmall]
        have hbLe3n : b ≤ 3 * T.S.n k := by omega
        have hbLe3nR : (b : ℝ) ≤ 3 * (T.S.n k : ℝ) := by exact_mod_cast hbLe3n
        have hBupper : Bsampler ≤ Real.rpow (3 * (T.S.n k : ℝ)) κ.aB := by
          calc
            Bsampler ≤ Real.rpow (b : ℝ) κ.aB := hBsamplerLe
            _ ≤ Real.rpow (3 * (T.S.n k : ℝ)) κ.aB :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hbLe3nR hκ.aB_rng.1.le
        have h3pow : Real.rpow 3 κ.aB ≤ 3 := by
          calc
            Real.rpow 3 κ.aB ≤ Real.rpow 3 1 :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [haBquarter])
            _ = 3 := Real.rpow_one 3
        have hnPow : Real.rpow (T.S.n k : ℝ) κ.aB ≤
            Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hkR haBquarter
        have hMulR : Real.rpow (3 * (T.S.n k : ℝ)) κ.aB =
            Real.rpow 3 κ.aB * Real.rpow (T.S.n k : ℝ) κ.aB :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg (T.S.n k))
        have hBsmall' : Bsampler ≤ 3 * Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) := by
          calc
            Bsampler ≤ Real.rpow (3 * (T.S.n k : ℝ)) κ.aB := hBupper
            _ = Real.rpow 3 κ.aB * Real.rpow (T.S.n k : ℝ) κ.aB := hMulR
            _ ≤ 3 * Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) := by
              calc
                Real.rpow 3 κ.aB * Real.rpow (T.S.n k : ℝ) κ.aB ≤
                    3 * Real.rpow (T.S.n k : ℝ) κ.aB :=
                  mul_le_mul_of_nonneg_right h3pow
                    (Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.aB)
                _ ≤ 3 * Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) :=
                  mul_le_mul_of_nonneg_left hnPow (by norm_num)
        have hn1000 : (1000 : ℝ) ^ 4 ≤ (T.S.n k : ℝ) := by
          have hn1000' : (1000 : ℕ) ^ 4 ≤ T.S.n k := by
            have heq : (1000 : ℕ) ^ 4 = 1000000000000 := by norm_num
            rw [heq]
            exact hkHuge
          exact_mod_cast hn1000'
        have hlogN : Real.log 1000 ≤ (1 / 4 : ℝ) * Real.log (T.S.n k : ℝ) := by
          have h := Real.log_le_log (by norm_num : (0 : ℝ) < (1000 : ℝ) ^ 4) hn1000
          rw [Real.log_pow] at h
          have hdiv := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ (4 : ℝ))
          calc
            Real.log 1000 = (4 * Real.log 1000) / 4 := by ring
            _ ≤ Real.log (T.S.n k : ℝ) / 4 := hdiv
            _ = (1 / 4 : ℝ) * Real.log (T.S.n k : ℝ) := by ring
        have hQuarter : 1000 ≤ Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) :=
          Real.le_rpow_of_log_le hnR hlogN
        let v : ℝ := Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ)
        have hvNonneg : 0 ≤ v := by positivity
        have hv3 : 3 ≤ v := by
          dsimp [v]
          exact le_trans (by norm_num) hQuarter
        have hvMul : 3 * v ≤ v * v := by
          have hprod := mul_nonneg hvNonneg (sub_nonneg.mpr hv3)
          nlinarith only [hprod]
        have hSqrtEq : Real.sqrt (T.S.n k : ℝ) = v * v := by
          have hpow : Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) = v * v := by
            dsimp [v]
            calc
              Real.rpow (T.S.n k : ℝ) (1 / 2 : ℝ) =
                  Real.rpow (T.S.n k : ℝ) ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := by
                    congr 1 <;> norm_num
              _ = Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) *
                    Real.rpow (T.S.n k : ℝ) (1 / 4 : ℝ) :=
                Real.rpow_add hnR _ _
          simpa [Real.sqrt_eq_rpow] using hpow
        have hBsmall : Bsampler ≤ Real.sqrt (T.S.n k) := by
          rw [hSqrtEq]
          exact le_trans hBsmall' hvMul
        have hQpowBound : Real.rpow (q : ℝ) κ.aC ≤
            Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) := by
          have hCbExp : κ.aC ≤ κ.Cb / 4 := by
            have hCb : 100 ≤ κ.Cb := by
              have hterm : 0 < 100 * κ.aC / κ.aB :=
                div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
              linarith only [hκ.Cb_big, hterm]
            nlinarith only [haCsmall, hCb]
          have hbase : xpow ≤ 3 * (T.S.n k : ℝ) := le_trans hbx hbLe3nR
          have hmul := Real.rpow_mul (x := (q : ℝ)) (Nat.cast_nonneg _) κ.Cb (1 / 4 : ℝ)
          have hexpEq : κ.Cb * (1 / 4 : ℝ) = κ.Cb / 4 := by ring
          rw [hexpEq] at hmul
          calc
            Real.rpow (q : ℝ) κ.aC ≤ Real.rpow (q : ℝ) (κ.Cb / 4) :=
              Real.rpow_le_rpow_of_exponent_le hq hCbExp
            _ = Real.rpow xpow (1 / 4 : ℝ) := by simpa [xpow] using hmul
            _ ≤ Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) :=
              Real.rpow_le_rpow (by positivity) hbase (by norm_num)
        let e : ℝ := 4 * κ.ω * κ.Mhi
        have hePos : 0 < e := by
          dsimp [e]
          have hMhiPos : 0 < (κ.Mhi : ℝ) := by
            have hterm : 0 < 10 / κ.cq := div_pos (by norm_num) hκ.cq_rng.1
            linarith only [hκ.Mhi_big.1, hterm, show (0 : ℝ) ≤ κ.Mlo from Nat.cast_nonneg _]
          exact mul_pos (mul_pos (by norm_num) hκ.ω_rng.1) hMhiPos
        have heQuarter : e ≤ κ.Cb / 4 := by
          have hCb : 100 ≤ κ.Cb := by
            have hterm : 0 < 100 * κ.aC / κ.aB :=
              div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
            linarith only [hκ.Cb_big, hterm]
          have heSmall : e < κ.aC / 100 := homegaSmall
          nlinarith only [haCsmall, hCb, heSmall]
        have hQeBound : Real.rpow (q : ℝ) e ≤
            Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) := by
          have hbase : xpow ≤ 3 * (T.S.n k : ℝ) := le_trans hbx hbLe3nR
          have hmul := Real.rpow_mul (x := (q : ℝ)) (Nat.cast_nonneg _) κ.Cb (1 / 4 : ℝ)
          have hexpEq : κ.Cb * (1 / 4 : ℝ) = κ.Cb / 4 := by ring
          rw [hexpEq] at hmul
          calc
            Real.rpow (q : ℝ) e ≤ Real.rpow (q : ℝ) (κ.Cb / 4) :=
              Real.rpow_le_rpow_of_exponent_le hq heQuarter
            _ = Real.rpow xpow (1 / 4 : ℝ) := by simpa [xpow] using hmul
            _ ≤ Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) :=
              Real.rpow_le_rpow (by positivity) hbase (by norm_num)
        have hThreeQuarter : Real.rpow 3 (1 / 4 : ℝ) ≤ 2 := by
          have h16 : Real.rpow 16 (1 / 4 : ℝ) = 2 := by
            have hEq := (Real.rpow_inv_eq (by norm_num : (0 : ℝ) ≤ 16)
              (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (4 : ℝ) ≠ 0)).2
              (by norm_num : (16 : ℝ) = 2 ^ (4 : ℝ))
            simpa [one_div] using hEq
          exact le_trans (Real.rpow_le_rpow (by norm_num) (by norm_num : (3 : ℝ) ≤ 16)
            (by norm_num)) h16.le
        have hQuarterN : Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) ≤ 2 * v := by
          calc
            Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) =
                Real.rpow 3 (1 / 4 : ℝ) * v :=
              Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
            _ ≤ 2 * v := mul_le_mul_of_nonneg_right hThreeQuarter hvNonneg
        have hLogSlack :=
          HypercubeRamsey.S13.Lane_q_s13_clean.sampler_log_budget κ hκ
        have hLogEq' : Real.log (800 / (κ.a * (1 / 400 : ℝ))) =
            Real.log (320000 / κ.a) := congrArg Real.log hLogEq
        have hLogSlack' : 200 ≤ Real.log (800 / (κ.a * (1 / 400 : ℝ))) := by
          rw [hLogEq']
          exact hLogSlack
        have hLog400 : Real.log (400 : ℝ) ≤ 10 := by
          have hExp1 : 2 ≤ Real.exp (1 : ℝ) := by
            have h := Real.add_one_le_exp (1 : ℝ)
            nlinarith only [h]
          have hExp10 : Real.exp (1 : ℝ) ^ 10 = Real.exp (10 : ℝ) := by
            simpa using Real.exp_nat_mul (1 : ℝ) 10
          have hExp400 : 400 ≤ Real.exp (10 : ℝ) := by
            calc
              400 ≤ (2 : ℝ) ^ 10 := by norm_num
              _ ≤ Real.exp (1 : ℝ) ^ 10 := by gcongr
              _ = Real.exp (10 : ℝ) := hExp10
          exact (Real.log_le_iff_le_exp (by norm_num)).2 hExp400
        have hMass400 : (T.S.N k : ℝ) *
            Real.exp (-Real.rpow (q : ℝ) κ.aC) ≤ 400 * (𝒯.P i).M := by
          have hmul := mul_le_mul_of_nonneg_left hMass (by norm_num : (0 : ℝ) ≤ 400)
          calc
            (T.S.N k : ℝ) * Real.exp (-Real.rpow (q : ℝ) κ.aC) =
                400 * ((1 / 400 : ℝ) * (T.S.N k : ℝ) *
                  Real.exp (-Real.rpow (q : ℝ) κ.aC)) := by ring
            _ ≤ 400 * (𝒯.P i).M := hmul
        have hMassRatio : (T.S.N k : ℝ) / (𝒯.P i).M ≤
            400 * Real.exp (Real.rpow (q : ℝ) κ.aC) := by
          apply (div_le_iff₀ hMpos).2
          have hCancel : Real.exp (-Real.rpow (q : ℝ) κ.aC) *
              Real.exp (Real.rpow (q : ℝ) κ.aC) = 1 := by
            rw [← Real.exp_add]
            simp
          calc
            (T.S.N k : ℝ) =
                ((T.S.N k : ℝ) * Real.exp (-Real.rpow (q : ℝ) κ.aC)) *
                  Real.exp (Real.rpow (q : ℝ) κ.aC) := by
                    calc
                      (T.S.N k : ℝ) = (T.S.N k : ℝ) * 1 := by ring
                      _ = (T.S.N k : ℝ) *
                          (Real.exp (-Real.rpow (q : ℝ) κ.aC) *
                            Real.exp (Real.rpow (q : ℝ) κ.aC)) := by rw [hCancel]
                      _ = ((T.S.N k : ℝ) * Real.exp (-Real.rpow (q : ℝ) κ.aC)) *
                            Real.exp (Real.rpow (q : ℝ) κ.aC) := by ring
            _ ≤ (400 * (𝒯.P i).M) * Real.exp (Real.rpow (q : ℝ) κ.aC) :=
              mul_le_mul_of_nonneg_right hMass400 (Real.exp_nonneg _)
            _ = 400 * Real.exp (Real.rpow (q : ℝ) κ.aC) * (𝒯.P i).M := by ring
        have hLogMass : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
            Real.rpow (q : ℝ) κ.aC + Real.log (400 : ℝ) := by
          calc
            Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) ≤
                Real.log (400 * Real.exp (Real.rpow (q : ℝ) κ.aC)) :=
              Real.log_le_log (div_pos hNpos hMpos) hMassRatio
            _ = Real.log (400 : ℝ) + Real.log (Real.exp (Real.rpow (q : ℝ) κ.aC)) :=
              Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _))
            _ = Real.rpow (q : ℝ) κ.aC + Real.log (400 : ℝ) := by
              rw [Real.log_exp]
              ring
        have hCap : cap ≤ 80 * Real.rpow (q : ℝ) e := by
          dsimp [cap]
          calc
            10 * (𝒯.kScale i : ℝ) * 𝒯.tScale i =
                10 * ((𝒯.kScale i : ℝ) * 𝒯.tScale i) := by ring
            _ ≤ 10 * (8 * Real.rpow (q : ℝ) e) :=
              mul_le_mul_of_nonneg_left hktWide (by norm_num)
            _ = 80 * Real.rpow (q : ℝ) e := by ring
        let qPow : ℝ := Real.rpow (q : ℝ) κ.aC
        let qE : ℝ := Real.rpow (q : ℝ) e
        let qDouble : ℝ := Real.rpow (2 * (q : ℝ)) e
        have hqPowBound' : qPow ≤ Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) := by
          simpa [qPow] using hQpowBound
        have hqEBound' : qE ≤ Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) := by
          simpa [qE] using hQeBound
        have hqPowNonneg : 0 ≤ qPow := by dsimp [qPow]; positivity
        have hqENonneg : 0 ≤ qE := by dsimp [qE]; positivity
        have hqDoubleNonneg : 0 ≤ qDouble := by dsimp [qDouble]; positivity
        have hQDouble : qE ≤ qDouble := by
          dsimp [qE, qDouble]
          exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by nlinarith only [hqNat]) hePos.le
        have hCap' : cap ≤ 80 * qE := by simpa [qE] using hCap
        have hCapQuarter : cap ≤ 160 * v := by
          calc
            cap ≤ 80 * qE := hCap'
            _ ≤ 80 * Real.rpow (3 * (T.S.n k : ℝ)) (1 / 4 : ℝ) :=
              mul_le_mul_of_nonneg_left hqEBound' (by norm_num)
            _ ≤ 160 * v := by nlinarith only [hQuarterN]
        have hWupper : W ≤ 162 * v + 10 := by
          dsimp [W]
          calc
            Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + cap ≤
                (Real.rpow (q : ℝ) κ.aC + Real.log (400 : ℝ)) + cap :=
              add_le_add hLogMass le_rfl
            _ ≤ 162 * v + 10 := by
              have hqpv : qPow ≤ 2 * v := le_trans hqPowBound' hQuarterN
              have hlog400 : Real.log (400 : ℝ) ≤ 10 := hLog400
              have hcapv : cap ≤ 160 * v := hCapQuarter
              simpa [qPow] using (show qPow + Real.log (400 : ℝ) + cap ≤ 162 * v + 10 by
                linarith only [hqpv, hlog400, hcapv])
        have hWsmall : W ≤ Real.sqrt (T.S.n k) := by
          rw [hSqrtEq]
          have hLargePoly : 162 * v + 10 ≤ v * v := by
            have hv1000 : 1000 ≤ v := by dsimp [v]; exact hQuarter
            have hmargin : 162 * v + 10 ≤ 1000 * v := by linarith only [hv1000]
            have hprod := mul_nonneg hvNonneg (sub_nonneg.mpr hv1000)
            have hsquare : 1000 * v ≤ v * v := by nlinarith only [hprod]
            exact le_trans hmargin hsquare
          exact le_trans hWupper hLargePoly
        have hBWall : (Bsampler + W) / 2 ≤ Real.sqrt (T.S.n k) := by
          have hSum := add_le_add hBsmall hWsmall
          linarith only [hSum]
        have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
          have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
          norm_num at h ⊢
          exact h
        have hExpN : Real.exp ((T.S.n k : ℝ) / 2) ≤ (2 : ℝ) ^ T.S.n k := by
          calc
            Real.exp ((T.S.n k : ℝ) / 2) ≤
                Real.exp ((T.S.n k : ℝ) * Real.log 2) :=
              Real.exp_le_exp.mpr (by nlinarith only [hlog2])
            _ = Real.exp ((T.S.n k : ℝ) * Real.log 2) := by congr 1 <;> ring
            _ = Real.exp (Real.log 2) ^ T.S.n k :=
              Real.exp_nat_mul (Real.log 2) (T.S.n k)
            _ = (2 : ℝ) ^ T.S.n k := by rw [Real.exp_log (by norm_num)]
        have hNlower : (2 : ℝ) ^ T.S.n k ≤ T.S.N k := by
          dsimp [LargeHost] at hHost
          simpa using hHost.1
        have hExpNlower : Real.exp ((T.S.n k : ℝ) / 2) ≤ T.S.N k :=
          le_trans hExpN hNlower
        have hSqrtLe : Real.sqrt (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) / 4 := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · have hn16 : (16 : ℝ) ≤ T.S.n k := by
              exact_mod_cast (by omega : 16 ≤ T.S.n k)
            have hprod := mul_nonneg (le_of_lt hnR) (sub_nonneg.mpr hn16)
            have hsq : (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ 2 / 16 := by
              nlinarith only [hprod]
            calc
              (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ 2 / 16 := hsq
              _ = ((T.S.n k : ℝ) / 4) ^ 2 := by ring
        have hNexp : (T.S.n k : ℝ) ^ 12 ≤
            (T.S.N k : ℝ) * Real.exp (-Real.sqrt (T.S.n k : ℝ)) := by
          calc
            (T.S.n k : ℝ) ^ 12 ≤ Real.exp ((T.S.n k : ℝ) / 4) := hPoly
            _ ≤ Real.exp ((T.S.n k : ℝ) / 2) *
                Real.exp (-Real.sqrt (T.S.n k : ℝ)) := by
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              linarith only [hSqrtLe]
            _ ≤ (T.S.N k : ℝ) * Real.exp (-Real.sqrt (T.S.n k : ℝ)) :=
              mul_le_mul_of_nonneg_right hExpNlower (Real.exp_nonneg _)
        have hSampleSize : (T.S.n k : ℝ) ^ 12 ≤
            (T.S.N k : ℝ) * Real.exp (-(Bsampler + W) / 2) := by
          calc
            (T.S.n k : ℝ) ^ 12 ≤
                (T.S.N k : ℝ) * Real.exp (-Real.sqrt (T.S.n k : ℝ)) := hNexp
            _ ≤ (T.S.N k : ℝ) * Real.exp (-(Bsampler + W) / 2) :=
              mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (by linarith only [hBWall])) (Nat.cast_nonneg _)
        have hSamplerGap' : 2 * qPow + 2 * qDouble +
            Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤ Bsampler := by
          dsimp [Bsampler, qPow, qDouble]
          exact hSamplerGap
        have hBaseGap : qPow + 2 * qDouble +
            Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≥
              Real.log (400 : ℝ) + cap + 2 := by
          by_cases hBig : 78 * qE ≤ qPow
          · have hlarge : 80 * qE ≤ qPow + 2 * qDouble := by
              nlinarith only [hBig, hQDouble]
            nlinarith only [hlarge, hLogSlack', hLog400, hCap']
          · have hSmall : qPow < 78 * qE := lt_of_not_ge hBig
            have hqPos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNat)
            have hqLogNonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq
            have hqPowPos : 0 < qPow := by dsimp [qPow]; positivity
            have hqEPos : 0 < qE := by dsimp [qE]; positivity
            have hLogLeft : Real.log qPow < Real.log (78 * qE) :=
              Real.log_lt_log hqPowPos (by nlinarith only [hSmall])
            have hLogLeft' : κ.aC * Real.log (q : ℝ) <
                Real.log (78 : ℝ) + e * Real.log (q : ℝ) := by
              have hLhs : Real.log qPow = κ.aC * Real.log (q : ℝ) := by
                dsimp [qPow]
                exact Real.log_rpow hqPos κ.aC
              have hRhs : Real.log (78 * qE) =
                  Real.log (78 : ℝ) + e * Real.log (q : ℝ) := by
                rw [Real.log_mul (by norm_num) (ne_of_gt hqEPos)]
                dsimp [qE]
                rw [Real.log_rpow hqPos]
              rw [hLhs, hRhs] at hLogLeft
              exact hLogLeft
            have hDeltaPos : 0 < κ.aC - e := by nlinarith only [homegaSmall, hκ.aC_rng.1]
            have hDeltaLog : (κ.aC - e) * Real.log (q : ℝ) < Real.log 78 := by
              nlinarith only [hLogLeft']
            have heDelta : e ≤ (κ.aC - e) / 99 := by
              dsimp [e]
              nlinarith only [homegaSmall, hκ.aC_rng.1]
            have heLog : e * Real.log (q : ℝ) < Real.log 78 / 99 := by
              have hmul := mul_le_mul_of_nonneg_right heDelta hqLogNonneg
              nlinarith only [hmul, hDeltaLog]
            have hLog78 : Real.log (78 : ℝ) < 99 * Real.log 2 := by
              have hpow : (78 : ℝ) < (2 : ℝ) ^ 99 := by norm_num
              have h := Real.log_lt_log (by norm_num) hpow
              rw [Real.log_pow] at h
              exact h
            have heLog2 : e * Real.log (q : ℝ) < Real.log 2 := by
              nlinarith only [heLog, hLog78]
            have hLogQE : Real.log qE < Real.log 2 := by
              dsimp [qE]
              rw [Real.log_rpow hqPos]
              exact heLog2
            have hqElt2 : qE < 2 := by
              by_contra hnot
              have hle : 2 ≤ qE := le_of_not_gt hnot
              have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hle
              linarith only [hLogQE, hmono]
            have hcap160 : cap ≤ 160 := by
              calc
                cap ≤ 80 * qE := hCap'
                _ ≤ 80 * 2 := mul_le_mul_of_nonneg_left hqElt2.le (by norm_num)
                _ = 160 := by norm_num
            nlinarith only [hLogSlack', hLog400, hcap160, hqPowNonneg, hqDoubleNonneg]
        have hGapSampler : W + 2 ≤ Bsampler := by
          calc
            W + 2 = Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + cap + 2 := by
              dsimp [W]
              <;> ring
            _ ≤ qPow + Real.log (400 : ℝ) + cap + 2 := by
              have hMassCap : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) +
                  (cap + 2) ≤ (qPow + Real.log (400 : ℝ)) + (cap + 2) := by
                exact add_le_add (by simpa [qPow] using hLogMass) le_rfl
              calc
                Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + cap + 2 =
                    Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) + (cap + 2) := by ring
                _ ≤ (qPow + Real.log (400 : ℝ)) + (cap + 2) := hMassCap
                _ = qPow + Real.log (400 : ℝ) + cap + 2 := by ring
            _ ≤ 2 * qPow + 2 * qDouble +
                Real.log (800 / (κ.a * (1 / 400 : ℝ))) := by
              linarith only [hBaseGap]
            _ ≤ Bsampler := hSamplerGap'
        exact ⟨hBsmall, hWsmall, hGapSampler, hSampleSize⟩
      rcases hSamplerParams with ⟨hBsmall, hWsmall, hGapSampler, hSampleSize⟩
      have hBsmall' : Bsampler ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
        simpa [Real.sqrt_eq_rpow] using hBsmall
      have hWsmall' : W ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
        simpa [Real.sqrt_eq_rpow] using hWsmall
      let tests : Fin (T.S.N k) → Fin (T.S.N k) → ℝ :=
        fun x y => hit (T.S.E k) 𝒯.c x y
      have htests : ∀ x y, 0 ≤ tests x y ∧ tests x y ≤ 1 := by
        intro x y
        dsimp [tests]
        unfold hit
        split_ifs <;> norm_num
      have hTestCount :=
        HypercubeRamsey.S13.Lane_q_s13_clean.host_test_count hn (T.S.N_le k)
      obtain ⟨V, hVne, hVpos, hVcard, hVtests⟩ :=
        hApprox (T.S.N k) (T.S.N k) (T.S.n k) (π i) Bsampler W
          hn hBsmall' hWsmall' hGapSampler hPiWidth hSampleSize tests htests hTestCount
      have hVsubset : V ⊆ (𝒯.P i).Y := by
        intro y hy
        by_contra hyY
        have hzero := hPiSupport y hyY
        have hpositive := hVpos y hy
        rw [hzero] at hpositive
        linarith
      have hApproxDeg (x : Fin (T.S.N k)) :
          |(∑ y ∈ V, hit (T.S.E k) 𝒯.c x y) / V.card -
            deg (T.S.E k) 𝒯.c (π i).w x| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ) := by
        have h := hVtests x
        simpa [tests, FinProb.expect, deg] using h
      have hbPowCompare :
          Real.rpow ((𝒯.P i).q : ℝ) κ.aC +
            Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤
            Real.rpow (b : ℝ) κ.aB := by
        have hLower := hSamplerGap
        have hQtwoNonneg : 0 ≤ Real.rpow ((𝒯.P i).q : ℝ) κ.aC :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hXnonneg : 0 ≤ Real.rpow (2 * (𝒯.P i).q) (4 * κ.ω * κ.Mhi) :=
          Real.rpow_nonneg (by positivity) _
        have hLower' :
            2 * Real.rpow ((𝒯.P i).q : ℝ) κ.aC +
              2 * Real.rpow (2 * (𝒯.P i).q) (4 * κ.ω * κ.Mhi) +
              Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤ Bsampler := by
          dsimp [Bsampler]
          exact hLower
        calc
          Real.rpow ((𝒯.P i).q : ℝ) κ.aC +
              Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤
              2 * Real.rpow ((𝒯.P i).q : ℝ) κ.aC +
                2 * Real.rpow (2 * (𝒯.P i).q) (4 * κ.ω * κ.Mhi) +
                Real.log (800 / (κ.a * (1 / 400 : ℝ))) := by
            nlinarith only [hQtwoNonneg, hXnonneg]
          _ ≤ Bsampler := hLower'
          _ ≤ Real.rpow (b : ℝ) κ.aB := hBsamplerLe
      have hExpCompare : Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤
          Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) * (κ.a / 320000) := by
        have hGapB : Real.log (800 / (κ.a * (1 / 400 : ℝ))) ≤
            Real.rpow (b : ℝ) κ.aB -
              Real.rpow ((𝒯.P i).q : ℝ) κ.aC := by
          linarith only [hbPowCompare]
        have hlogpos : 0 < 320000 / κ.a := by positivity
        have hlogEq' : Real.log (800 / (κ.a * (1 / 400 : ℝ))) =
            Real.log (320000 / κ.a) := congrArg Real.log hLogEq
        calc
          Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤
              Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC -
                Real.log (320000 / κ.a)) :=
            Real.exp_le_exp.mpr (by
              rw [← hlogEq']
              linarith only [hGapB])
          _ = Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) * (κ.a / 320000) := by
            rw [Real.exp_sub, Real.exp_log hlogpos]
            field_simp [ne_of_gt ha]
      have hMscaled : (T.S.N k : ℝ) * Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤
          κ.a / 800 * (𝒯.P i).M := by
        have hMmass' : (T.S.N k : ℝ) *
            Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) ≤ 400 * (𝒯.P i).M := by
          have hmul := mul_le_mul_of_nonneg_left hMass (by norm_num : (0 : ℝ) ≤ 400)
          calc
            (T.S.N k : ℝ) * Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) =
                400 * ((1 / 400 : ℝ) * (T.S.N k : ℝ) *
                  Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC)) := by ring
            _ ≤ 400 * (𝒯.P i).M := hmul
        calc
          (T.S.N k : ℝ) * Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤
              (T.S.N k : ℝ) *
                (Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) * (κ.a / 320000)) :=
            mul_le_mul_of_nonneg_left hExpCompare (Nat.cast_nonneg _)
          _ ≤ (400 * (𝒯.P i).M) * (κ.a / 320000) :=
            calc
              (T.S.N k : ℝ) *
                  (Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC) *
                    (κ.a / 320000)) =
                  ((T.S.N k : ℝ) *
                    Real.exp (-Real.rpow ((𝒯.P i).q : ℝ) κ.aC)) *
                      (κ.a / 320000) := by ring
              _ ≤ (400 * (𝒯.P i).M) * (κ.a / 320000) :=
                mul_le_mul_of_nonneg_right hMmass'
                  (div_nonneg ha.le (by norm_num))
          _ = κ.a / 800 * (𝒯.P i).M := by ring
      have hbBound : b ≤ 2 * T.S.n k + 1 := by omega
      have hgScaleEq : gScale κ T k (𝒯.P i).resX (𝒯.P i).resY = (𝒯.P i).g :=
        (h𝒯.measured_scales i).1.symm
      have hgScaleLt : gScale κ T k (𝒯.P i).resX (𝒯.P i).resY < b := by
        rw [hgScaleEq]
        have hglt : ((𝒯.P i).g : ℝ) < b :=
          lt_of_le_of_lt hGscale (lt_of_lt_of_le hScaleGap hbx)
        exact_mod_cast hglt
      have hNoWitness : ¬ BiasWitness κ T k (𝒯.P i).resX (𝒯.P i).resY b :=
        hScales.bias_absent κ T k (𝒯.P i).resX (𝒯.P i).resY b hbDyadic hgScaleLt hbBound
      have hNpow : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (b : ℝ) / T.S.n k := by
        have hnR : 0 < (T.S.n k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hInv : (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ 1 / T.S.n k := by
          have hExp := Real.rpow_le_rpow_of_exponent_le hkR
            (by norm_num : (-2 : ℝ) ≤ -1)
          calc
            (T.S.n k : ℝ) ^ (-2 : ℝ) ≤ (T.S.n k : ℝ) ^ (-1 : ℝ) := hExp
            _ = 1 / T.S.n k := by rw [Real.rpow_neg hnR.le, Real.rpow_one]; simp [one_div]
        have hbOne : 1 ≤ (b : ℝ) := by exact_mod_cast (le_trans hxpow hbx)
        exact le_trans hInv (div_le_div_of_nonneg_right hbOne (Nat.cast_nonneg _))
      have hnR : 0 < (T.S.n k : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
      have hXres : X ⊆ (𝒯.P i).resX := (h𝒯.patch_supports i).1
      have hYres : (𝒯.P i).Y ⊆ (𝒯.P i).resY :=
        (h𝒯.patch_supports i).2.2.1
      have hVcardB : (T.S.N k : ℝ) *
          Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤ V.card := by
        calc
          (T.S.N k : ℝ) * Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤
              (T.S.N k : ℝ) * Real.exp (-Bsampler) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (neg_le_neg hBsamplerLe))
              (Nat.cast_nonneg _)
          _ ≤ V.card := hVcard
      have hNoBiasHigh {U : Finset (Fin (T.S.N k))} (hUX : U ⊆ X)
          (hUcard : (T.S.N k : ℝ) *
            Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤ U.card)
          (hUne : U.Nonempty)
          (hRows : ∀ x ∈ U, 2 * (b : ℝ) / T.S.n k <
            deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2) : False := by
        have hWitness := HypercubeRamsey.S13.Lane_q_s13_clean.biasWitness_of_highRows
          κ T k b 𝒯.c (𝒯.P i).resX (𝒯.P i).resY U V hUne hVne
          (hUX.trans hXres) (hVsubset.trans hYres) hUcard hVcardB (π i)
          hApproxDeg hRows (lt_of_lt_of_le Nat.zero_lt_one hn) hNpow
        exact hNoWitness hWitness
      have hNoBiasLow {U : Finset (Fin (T.S.N k))} (hUX : U ⊆ X)
          (hUcard : (T.S.N k : ℝ) *
            Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤ U.card)
          (hUne : U.Nonempty)
          (hRows : ∀ x ∈ U, 2 * (b : ℝ) / T.S.n k <
            1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x) : False := by
        have hWitness := HypercubeRamsey.S13.Lane_q_s13_clean.biasWitness_of_lowRows
          κ T k b 𝒯.c (𝒯.P i).resX (𝒯.P i).resY U V hUne hVne
          (hUX.trans hXres) (hVsubset.trans hYres) hUcard hVcardB (π i)
          hApproxDeg hRows (lt_of_lt_of_le Nat.zero_lt_one hn) hNpow
        exact hNoWitness hWitness
      let BadHigh := X.filter (fun x =>
        4 * xpow / T.S.n k < deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2)
      let BadLow := X.filter (fun x =>
        4 * xpow / T.S.n k < 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x)
      have hBadHighRows (x : Fin (T.S.N k)) (hx : x ∈ BadHigh) :
          2 * (b : ℝ) / T.S.n k <
            deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := by
        have hxmem := (Finset.mem_filter.mp hx).2
        have hnum : 2 * (b : ℝ) < 4 * xpow := by nlinarith only [hbxUpper]
        have hdiv := div_lt_div_of_pos_right hnum hnR
        have hxmem' : 4 * xpow / T.S.n k <
            deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := by
          simpa using hxmem
        exact lt_trans hdiv hxmem'
      have hBadLowRows (x : Fin (T.S.N k)) (hx : x ∈ BadLow) :
          2 * (b : ℝ) / T.S.n k <
            1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x := by
        have hxmem := (Finset.mem_filter.mp hx).2
        have hnum : 2 * (b : ℝ) < 4 * xpow := by nlinarith only [hbxUpper]
        have hdiv := div_lt_div_of_pos_right hnum hnR
        have hxmem' : 4 * xpow / T.S.n k <
            1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x := by
          simpa using hxmem
        exact lt_trans hdiv hxmem'
      have hBadHighCard : (BadHigh.card : ℝ) <
          (T.S.N k : ℝ) * Real.exp (-Real.rpow (b : ℝ) κ.aB) := by
        by_contra hnot
        have hLarge : (T.S.N k : ℝ) *
            Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤ BadHigh.card := le_of_not_gt hnot
        have hBadNe : BadHigh.Nonempty := by
          apply Finset.card_pos.mp
          exact_mod_cast lt_of_lt_of_le (mul_pos hNpos (Real.exp_pos _)) hLarge
        exact hNoBiasHigh (Finset.filter_subset _ _) hLarge hBadNe hBadHighRows
      have hBadLowCard : (BadLow.card : ℝ) <
          (T.S.N k : ℝ) * Real.exp (-Real.rpow (b : ℝ) κ.aB) := by
        by_contra hnot
        have hLarge : (T.S.N k : ℝ) *
            Real.exp (-Real.rpow (b : ℝ) κ.aB) ≤ BadLow.card := le_of_not_gt hnot
        have hBadNe : BadLow.Nonempty := by
          apply Finset.card_pos.mp
          exact_mod_cast lt_of_lt_of_le (mul_pos hNpos (Real.exp_pos _)) hLarge
        exact hNoBiasLow (Finset.filter_subset _ _) hLarge hBadNe hBadLowRows
      let Bad := BadHigh ∪ BadLow
      have hBadSmall : (Bad.card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
        have hUnion : (Bad.card : ℝ) ≤ (BadHigh.card : ℝ) + (BadLow.card : ℝ) := by
          exact_mod_cast Finset.card_union_le BadHigh BadLow
        have hHighSmall : (BadHigh.card : ℝ) < κ.a / 800 * (𝒯.P i).M :=
          lt_of_lt_of_le hBadHighCard hMscaled
        have hLowSmall : (BadLow.card : ℝ) < κ.a / 800 * (𝒯.P i).M :=
          lt_of_lt_of_le hBadLowCard hMscaled
        nlinarith only [hUnion, hHighSmall, hLowSmall, ha, hMpos]
      let C := X \ Bad
      have hCsub : C ⊆ X := by simp [C]
      have hXdiffSub : X \ C ⊆ Bad := by
        intro x hx
        rcases Finset.mem_sdiff.mp hx with ⟨hxX, hxNotC⟩
        by_contra hxNotBad
        exact hxNotC (Finset.mem_sdiff.mpr ⟨hxX, hxNotBad⟩)
      have hLoss : ((X \ C).card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
        have hcard : ((X \ C).card : ℝ) ≤ (Bad.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hXdiffSub
        exact lt_of_le_of_lt hcard hBadSmall
      have hOwn : ∀ x ∈ C, OwnDegOK 𝒯 i (π i) x := by
        intro x hx
        have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
        have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
        have hxNotHigh : x ∉ BadHigh := fun h => hxNotBad (Finset.mem_union_left _ h)
        have hxNotLow : x ∉ BadLow := fun h => hxNotBad (Finset.mem_union_right _ h)
        have htNonneg : 0 ≤ xpow / T.S.n k :=
          div_nonneg (by linarith only [hxpow]) (Nat.cast_nonneg _)
        have hUpper : deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 ≤
            4 * xpow / T.S.n k := by
          by_contra h
          have hStrict : 4 * xpow / T.S.n k <
              deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := lt_of_not_ge h
          exact hxNotHigh (Finset.mem_filter.mpr ⟨hxX, hStrict⟩)
        have hLower : 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x ≤
            4 * xpow / T.S.n k := by
          by_contra h
          have hStrict : 4 * xpow / T.S.n k <
              1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x := lt_of_not_ge h
          exact hxNotLow (Finset.mem_filter.mpr ⟨hxX, hStrict⟩)
        have hAbs : |deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2| ≤
            4 * xpow / T.S.n k :=
          abs_le.mpr ⟨by linarith only [hLower], hUpper⟩
        have hWide : 4 * xpow / T.S.n k ≤
            10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb / T.S.n k := by
          dsimp [xpow, q]
          have hpowNonneg : 0 ≤ Real.rpow ((𝒯.P i).q : ℝ) κ.Cb :=
            Real.rpow_nonneg (Nat.cast_nonneg _) _
          have hnum : 4 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb ≤
              10 * Real.rpow ((𝒯.P i).q : ℝ) κ.Cb := by nlinarith only [hpowNonneg]
          exact div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
        have hAbs' := hAbs.trans hWide
        rcases hMode with hLow | hSmall | hLarge
        · simpa [OwnDegOK, hLow] using hAbs'
        · simpa [OwnDegOK, hSmall] using hAbs'
        · simpa [OwnDegOK, hLarge] using hAbs'
      refine ⟨⟨C, hCsub, hLoss, hOwn, ?_⟩⟩
      intro _ π' hNear x hx
      have hxX : x ∈ X := (Finset.mem_sdiff.mp hx).1
      have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
      have hxNotHigh : x ∉ BadHigh := fun h => hxNotBad (Finset.mem_union_left _ h)
      have hxNotLow : x ∉ BadLow := fun h => hxNotBad (Finset.mem_union_right _ h)
      have hUpper : deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 ≤
          4 * xpow / T.S.n k := by
        by_contra h
        have hStrict : 4 * xpow / T.S.n k <
            deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2 := lt_of_not_ge h
        exact hxNotHigh (Finset.mem_filter.mpr ⟨hxX, hStrict⟩)
      have hLower : 1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x ≤
          4 * xpow / T.S.n k := by
        by_contra h
        have hStrict : 4 * xpow / T.S.n k <
            1 / 2 - deg (T.S.E k) 𝒯.c (π i).w x := lt_of_not_ge h
        exact hxNotLow (Finset.mem_filter.mpr ⟨hxX, hStrict⟩)
      have hCenter : |deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2| ≤
          4 * xpow / T.S.n k :=
        abs_le.mpr ⟨by linarith only [hLower], hUpper⟩
      have hNearDeg := HypercubeRamsey.S13.Lane_q_s13_clean.deg_l1
        (T.S.E k) 𝒯.c (π i) (π' i) x (hNear i)
      have hNearDeg' : |deg (T.S.E k) 𝒯.c (π' i).w x -
          deg (T.S.E k) 𝒯.c (π i).w x| ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by
        rw [abs_sub_comm]
        exact hNearDeg
      have hNinv : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ 1 / T.S.n k := by
        have hExp := Real.rpow_le_rpow_of_exponent_le hkR
          (by norm_num : (-3 : ℝ) ≤ -1)
        calc
          (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ (T.S.n k : ℝ) ^ (-1 : ℝ) := hExp
          _ = 1 / T.S.n k := by rw [Real.rpow_neg hnR.le, Real.rpow_one]; simp [one_div]
      have hErr : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ xpow / T.S.n k :=
        le_trans hNinv (div_le_div_of_nonneg_right hxpow (Nat.cast_nonneg _))
      have htNonneg : 0 ≤ xpow / T.S.n k :=
        div_nonneg (by linarith only [hxpow]) (Nat.cast_nonneg _)
      have hNearWide : (T.S.n k : ℝ) ^ (-3 : ℝ) + 4 * xpow / T.S.n k ≤
          10 * xpow / T.S.n k := by
        have hfour : 4 * xpow / T.S.n k = 4 * (xpow / T.S.n k) := by ring
        have hten : 10 * xpow / T.S.n k = 10 * (xpow / T.S.n k) := by ring
        rw [hfour, hten]
        have hsmall : (T.S.n k : ℝ) ^ (-3 : ℝ) + 4 * (xpow / T.S.n k) ≤
            (xpow / T.S.n k) + 4 * (xpow / T.S.n k) :=
          add_le_add hErr le_rfl
        have hlarge : (xpow / T.S.n k) + 4 * (xpow / T.S.n k) ≤
            10 * (xpow / T.S.n k) := by nlinarith only [htNonneg]
        exact le_trans hsmall hlarge
      have hNearAbs : |deg (T.S.E k) 𝒯.c (π' i).w x - 1 / 2| ≤
          10 * xpow / T.S.n k := by
        have hdecomp : deg (T.S.E k) 𝒯.c (π' i).w x - 1 / 2 =
            (deg (T.S.E k) 𝒯.c (π' i).w x - deg (T.S.E k) 𝒯.c (π i).w x) +
              (deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2) := by ring
        calc
          |deg (T.S.E k) 𝒯.c (π' i).w x - 1 / 2| =
              |(deg (T.S.E k) 𝒯.c (π' i).w x - deg (T.S.E k) 𝒯.c (π i).w x) +
                (deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2)| := by rw [hdecomp]
          _ ≤ |deg (T.S.E k) 𝒯.c (π' i).w x - deg (T.S.E k) 𝒯.c (π i).w x| +
                |deg (T.S.E k) 𝒯.c (π i).w x - 1 / 2| := abs_add_le _ _
          _ ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) + 4 * xpow / T.S.n k :=
            add_le_add hNearDeg' hCenter
          _ ≤ 10 * xpow / T.S.n k := hNearWide
      rcases hMode with hLow | hSmall | hLarge
      · simpa [OwnDegOK, hLow, xpow, q] using hNearAbs
      · simpa [OwnDegOK, hSmall, xpow, q] using hNearAbs
      · simpa [OwnDegOK, hLarge, xpow, q] using hNearAbs
  cases hm : 𝒯.mode with
  | lowDirect => exact directCase (Or.inl hm)
  | highDirect => exact directCase (Or.inr hm)
  | bounded => exact boundedCase hm
  | lowCluster => exact clusterCase (Or.inl hm)
  | highSmall => exact clusterCase (Or.inr (Or.inl hm))
  | highLarge => exact clusterCase (Or.inr (Or.inr hm))

/-- L13.4c (sections/13, lines 259–265): remove large high-correlation cliques without destroying own
degree margins. -/
theorem own_patch_clique_trim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xι κ.αι (κ.ι / 2))
    (hApprox : UniformApproximantStatement) (hScales : ResidualScaleSpec) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∀ D : OwnDegreeData 𝒯 i π, Nonempty (OwnCliqueData D) := by
  classical
  filter_upwards [Lane_sol_s13_cleanB.sampler_numeric κ hκ T] with k hk
  rcases hk with ⟨hn, herr, hnear, hcount, hsample⟩
  intro 𝒯 h𝒯 i π hInput D
  rcases Lane_sol_s13_cleanB.clique_budget κ hκ T k 𝒯 h𝒯 i π hInput with
    ⟨hdy, hqQ, hwidth, hloss⟩
  let m := Nat.ceil (Real.exp (𝒯.Q i : ℝ))
  have hm : 0 < m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hM : 0 < ((𝒯.P i).M : ℝ) := by
    have ht := Finset.card_pos.mpr (h𝒯.patch_nonempty i).1
    rw [(𝒯.P i).cardX] at ht
    exact_mod_cast ht
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  by_cases hbig : T.S.N k < m
  · refine ⟨⟨D.C, Finset.Subset.refl _, ?_, ?_⟩⟩
    · simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero]
      positivity
    · intro π' hNear
      rintro ⟨K, hK, hcard, _⟩
      have ht : K.card ≤ T.S.N k := by simpa using Finset.card_le_univ K
      rw [show K.card = m from hcard] at ht
      omega
  have hsmall : Real.exp (𝒯.Q i : ℝ) ≤ T.S.N k := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_of_not_gt hbig)
  rcases hsample (𝒯.Q i) hsmall with ⟨hrange, hB, hsize⟩
  let B := Real.rpow (𝒯.Q i : ℝ) κ.aC
  let W := B - 2
  let tests : Fin ((T.S.N k) * (T.S.N k)) → Fin (T.S.N k) → ℝ :=
    fun j y => (fv (T.S.E k) true (finProdFinEquiv.symm j).1 y *
      fv (T.S.E k) true (finProdFinEquiv.symm j).2 y + 1) / 2
  have htests : ∀ j y, 0 ≤ tests j y ∧ tests j y ≤ 1 := by
    intro j y
    dsimp [tests]
    unfold fv hit
    split_ifs <;> norm_num
  have hW : W ≤ (T.S.n k : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp [W, B]
    simp only [Real.rpow_eq_pow] at hB ⊢
    linarith only [hB]
  obtain ⟨U, hU, hUpos, hUcard, hUtests⟩ := hApprox (T.S.N k)
    ((T.S.N k) * (T.S.N k)) (T.S.n k) (π i) B W hn hB hW
    (by dsimp [W]; linarith) hwidth hsize tests htests (by simpa [pow_two] using hcount)
  have hUsub : U ⊆ (𝒯.P i).resY := by
    intro y hy
    have hyY : y ∈ (𝒯.P i).Y := by
      by_contra hnot
      have hz := (hInput i).1 y hnot
      linarith [hUpos y hy]
    exact (𝒯.P i).Y_res hyY
  let ν := Law.unifCore U hU
  have hCorr (x z : Fin (T.S.N k)) :
      corr (T.S.E k) true (π i).w x z - 2 * (T.S.n k : ℝ) ^ (-2 : ℝ) ≤
        corr (T.S.E k) true ν.w x z := by
    let f := fun y => (fv (T.S.E k) true x y * fv (T.S.E k) true z y + 1) / 2
    have ht := hUtests (finProdFinEquiv (x, z))
    have htf : tests (finProdFinEquiv (x, z)) = f := by
      have he : finProdFinEquiv.symm (finProdFinEquiv (x, z)) = (x, z) :=
        Equiv.symm_apply_apply _ _
      exact congrArg (fun p : Fin (T.S.N k) × Fin (T.S.N k) =>
        fun y => (fv (T.S.E k) true p.1 y * fv (T.S.E k) true p.2 y + 1) / 2) he
    rw [htf] at ht
    have ht' : |ν.expect f - (π i).expect f| ≤ (T.S.n k : ℝ) ^ (-2 : ℝ) := by
      simpa only [ν, Lane_q_s13_clean.unifCore_expect] using ht
    have hlo := (abs_le.mp ht').1
    have hp := Lane_q_s13_clean.corr_expect_shift (T.S.E k) (π i) x z
    have hu := Lane_q_s13_clean.corr_expect_shift (T.S.E k) ν x z
    change corr (T.S.E k) true (π i).w x z = 2 * (π i).expect f - 1 at hp
    change corr (T.S.E k) true ν.w x z = 2 * ν.expect f - 1 at hu
    linarith
  let R := fun x z => 2 * κ.θ < corr (T.S.E k) 𝒯.c (π i).w x z
  obtain ⟨P, hP, hDisjoint, hMax⟩ :=
    Lane_sol_s13_cleanB.clique_pack D.C m hm R
  let S := P.biUnion id
  let Bins : Fin P.card → Finset (Fin (T.S.N k)) :=
    fun j => (Lane_q_s13_clean.finsetEnum P j).val
  have hBins (j : Fin P.card) : Bins j ∈ P := (Lane_q_s13_clean.finsetEnum P j).property
  have hProps (A : Finset (Fin (T.S.N k))) (hA : A ∈ P) :
      A ⊆ D.C ∧ A.card = m ∧ ∀ x ∈ A, ∀ z ∈ A, x ≠ z → R x z := by
    exact hP A hA
  have hBinsUnion : Finset.univ.biUnion Bins = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, _, hj⟩
      exact Finset.mem_biUnion.mpr ⟨Bins j, hBins j, hj⟩
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨A, hA, hxA⟩
      let j := (Lane_q_s13_clean.finsetEnum P).symm ⟨A, hA⟩
      have hj : Bins j = A := by simp [Bins, j]
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by rwa [hj]⟩
  have hSSmall : (S.card : ℝ) < (T.S.N k : ℝ) * Real.exp (-B) := by
    by_contra hlarge
    have hlarge : (T.S.N k : ℝ) * Real.exp (-B) ≤ S.card := le_of_not_gt hlarge
    apply hScales.cluster_absent κ T k (𝒯.P i).resX (𝒯.P i).resY (𝒯.Q i)
      hdy (by rwa [← (h𝒯.measured_scales i).2]) hrange
    refine ⟨true, U, hU, P.card, Bins, hUsub, ?_, ?_, ?_, hUcard, ?_, ?_⟩
    · intro j
      exact ((hProps _ (hBins j)).1.trans D.sub).trans (𝒯.P i).X_res
    · intro j hj l hl hne
      apply hDisjoint (Bins j) (hBins j) (Bins l) (hBins l)
      intro hEq
      have ht : Lane_q_s13_clean.finsetEnum P j = Lane_q_s13_clean.finsetEnum P l :=
        Subtype.ext hEq
      exact hne ((Lane_q_s13_clean.finsetEnum P).injective ht)
    · intro j
      rw [(hProps _ (hBins j)).2.1]
      exact Nat.le_ceil _
    · rw [hBinsUnion]
      exact hlarge
    · intro j x hx z hz hne
      have ht := (hProps _ (hBins j)).2.2 x hx z hz hne
      have hc := Lane_q_s13_clean.corr_color_eq (T.S.E k) 𝒯.c (π i).w x z
      dsimp [R] at ht
      rw [hc] at ht
      have hu := hCorr x z
      change κ.θ < corr (T.S.E k) true ν.w x z
      linarith [ht, hu, herr]
  refine ⟨⟨D.C \ S, Finset.sdiff_subset, ?_, ?_⟩⟩
  · have hsub : D.C \ (D.C \ S) ⊆ S := by
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      by_contra hnot
      exact hx.2 ⟨hx.1, hnot⟩
    have hc : ((D.C \ (D.C \ S)).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hc.trans_lt (hSSmall.trans hloss)
  · intro π' hNear
    rintro ⟨K, hK, hcard, hpair⟩
    have hKR : ∀ x ∈ K, ∀ z ∈ K, x ≠ z → R x z := by
      intro x hx z hz hne
      have hn := Lane_q_s13_clean.corr_l1 (T.S.E k) 𝒯.c (π i) (π' i) x z (hNear i)
      have hl := (abs_le.mp hn).1
      have hp := hpair x hx z hz hne
      dsimp [R]
      linarith [hnear, hl, hp]
    exact hMax K (hK.trans Finset.sdiff_subset) hcard hKR hK

set_option maxHeartbeats 2000000 in
/-- L13.4d (sections/13, lines 267–276): clean other-patch outliers and enforce relaxed row
tails on the fixed original first support, retaining at least `(1 - κ.a) * M` labels. -/
theorem other_patch_degrees_and_tails (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hInit : InitDisc T κ.η0) (hDeep : OtherPatchDiscrepancyInput κ T) :
    ∀ᶠ k in atTop, ∀ (𝒯 : Tiling κ T k) (h𝒯 : Tiling.Valid 𝒯),
      ∀ i (π : Fin 𝒯.m → Law (T.S.N k)), InputOK 𝒯 h𝒯 π →
        ∀ D : OwnDegreeData 𝒯 i π, ∀ C : OwnCliqueData D,
          Nonempty (OtherPatchData D C) := by
  classical
  change DeepDisc T κ.xs κ.α (0.04 : ℝ) at hDeep
  have hTailsTrue := HypercubeRamsey.S12.row_trimming κ hκ T hDeep true
  have hTailsFalse := HypercubeRamsey.S12.row_trimming κ hκ T hDeep false
  have hRelaxedTrue := HypercubeRamsey.S12.rowTail_relax κ hκ T hDeep true
  have hRelaxedFalse := HypercubeRamsey.S12.rowTail_relax κ hκ T hDeep false
  have hNumeric := Lane_q_s13_clean.eventual_otherpatch_numeric κ hκ T
  have hNevent : ∀ᶠ k in atTop, 1 ≤ T.S.n k :=
    T.S.n_tendsto.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [hDeep, hTailsTrue, hTailsFalse, hRelaxedTrue, hRelaxedFalse,
    hNumeric, hNevent] with
    k hDisc hTailTrue hTailFalse hRelaxTrue hRelaxFalse hNum hk
  rcases hNum with ⟨hTailLoss, hLog400Xs, hXsLinear, hCountLog, hXsRoot,
    h01Root, hRootAlpha, hOutExp, hPowerGap, hLog400Iota⟩
  intro 𝒯 h𝒯 i π hInput D C
  have hTailEvent : ∀ (X₀ : Finset (Fin (T.S.N k))) (hX₀ : X₀.Nonempty),
      X₀ ⊆ T.X k → Real.log ((T.S.N k : ℝ) / X₀.card) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) →
      ∀ {α : Type} (J : Finset α) (laws : α → Law (T.S.N k)),
        (∀ j, (laws j).SupportedIn (T.Y k)) →
        (∀ j, (laws j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4))) →
        (J.card : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) →
        ∃ X₁ ⊆ X₀, ((X₀ \ X₁).card : ℝ) ≤
          Real.exp (-((T.S.n k : ℝ) ^ (0.3 : ℝ))) * X₀.card ∧
          ∀ j ∈ J, ∀ x ∈ X₁, HypercubeRamsey.S12.RowTail (T.S.E k) 𝒯.c (laws j).w X₀ (T.S.n k) κ.ξ x := by
    cases 𝒯.c <;> assumption
  have hRelaxEvent : ∀ (μ μ' : Law (T.S.N k)) (X₀ : Finset (Fin (T.S.N k)))
      (x : Fin (T.S.N k)), HypercubeRamsey.S12.RowTail (T.S.E k) 𝒯.c μ.w X₀ (T.S.n k) κ.ξ x →
      (∑ y, |μ.w y - μ'.w y|) ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) →
      RowTailRelaxed (T.S.E k) 𝒯.c μ'.w X₀ (T.S.n k) κ.ξ x := by
    cases 𝒯.c <;> assumption
  let X := (𝒯.P i).X
  have hNpos : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hnR : 1 ≤ (T.S.n k : ℝ) := by exact_mod_cast hk
  have hnPos : 0 < (T.S.n k : ℝ) := by linarith
  have hXne : X.Nonempty := by simpa [X] using (h𝒯.patch_nonempty i).1
  have hXsub : X ⊆ T.X k := by
    exact (((h𝒯.patch_supports i).1).trans ((h𝒯.patch_supports i).2.1)).trans Finset.sdiff_subset
  have hMpos : 0 < ((𝒯.P i).M : ℝ) := by
    have hcard := Finset.card_pos.mpr hXne
    rw [(𝒯.P i).cardX] at hcard
    exact_mod_cast hcard
  have hIotaNonneg : 0 ≤ κ.ι := hκ.ι_rng.1.le
  have hNPowerLe : (T.S.n k : ℝ) ^ κ.ι ≤
      (T.S.n k : ℝ) ^ (2 * κ.ι) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hκ.ι_rng.1])
  have hNPowerXs : (T.S.n k : ℝ) ^ κ.ι ≤
      (T.S.n k : ℝ) ^ (κ.xs / 4) := by
    calc
      (T.S.n k : ℝ) ^ κ.ι ≤ 12 * (T.S.n k : ℝ) ^ (2 * κ.ι) := by
        have hp : 0 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι) :=
          Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) _
        linarith only [hp, hNPowerLe]
      _ ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) := hPowerGap
  have hApos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hASmall := (Lane_sol_s13_cleanB.admissible_a_small κ hκ).2
  have hAone : κ.a < 1 := by linarith
  have hAhalf : κ.a < 1 / 2 := by linarith
  have hABleOne : κ.aB ≤ 1 := by
    have hACsmall : κ.aC < (1 : ℝ) := by
      have hmin : min κ.η0 (1 : ℝ) ≤ 1 := min_le_right _ _
      have hbound := hκ.aC_rng.2
      have hbound' : min κ.η0 1 / 10 ^ 6 ≤ 1 / 10 ^ 6 :=
        div_le_div_of_nonneg_right hmin (by norm_num)
      exact lt_trans hbound (lt_of_le_of_lt hbound' (by norm_num))
    exact le_trans hκ.aB_rng.2.1.le (by linarith)
  have hMloOne : (1 : ℝ) ≤ κ.Mlo := by
    have hRatio : 0 ≤ 100 * κ.aC / κ.aB :=
      div_nonneg (mul_nonneg (by norm_num) hκ.aC_rng.1.le) hκ.aB_rng.1.le
    have hCb : (100 : ℝ) < κ.Cb := by linarith [hκ.Cb_big]
    have hMlo : (200 : ℝ) < κ.Mlo := by linarith [hκ.Mlo_big]
    linarith
  have hMloLeMhi : (κ.Mlo : ℝ) ≤ κ.Mhi := by
    have hnonneg : 0 ≤ (10 : ℝ) / κ.cq := div_nonneg (by norm_num) hκ.cq_rng.1.le
    calc
      (κ.Mlo : ℝ) ≤ κ.Mlo + 10 / κ.cq := by linarith
      _ ≤ κ.Mhi := hκ.Mhi_big.1
  have hACLeMlo : κ.aC ≤ (κ.Mlo : ℝ) := by
    have hACsmall : κ.aC < 1 := by
      have hmin : min κ.η0 (1 : ℝ) ≤ 1 := min_le_right _ _
      have hbound' : min κ.η0 1 / 10 ^ 6 ≤ 1 / 10 ^ 6 :=
        div_le_div_of_nonneg_right hmin (by norm_num)
      exact lt_trans hκ.aC_rng.2 (lt_of_le_of_lt hbound' (by norm_num))
    linarith [hMloOne]
  have hPatchMass : ∀ j : Fin 𝒯.m,
      (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤ (𝒯.P j).M := by
    intro j
    cases hm : 𝒯.mode with
    | bounded =>
        rcases (h𝒯.bounded_data hm).2 j with ⟨_, _, _, hMass, _⟩
        have hExp : Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤ 1 := by
          calc
            Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤ Real.exp 0 :=
              Real.exp_le_exp.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.ι))
            _ = 1 := Real.exp_zero
        calc
          (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
              (T.S.N k : ℝ) / 400 :=
            by
              have ht := mul_le_mul_of_nonneg_left hExp (div_nonneg hNpos.le (by norm_num : (0 : ℝ) ≤ 400))
              simpa only [mul_one] using ht
          _ ≤ (𝒯.P j).M := by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hMass
    | lowDirect =>
        rcases h𝒯.direct_data (Or.inl hm) j with ⟨_, _, hMass, _, _, _, _⟩
        have hG := h𝒯.direct_scale_bound (Or.inl hm) j
        have hGpow : Real.rpow ((𝒯.P j).g : ℝ) κ.aB ≤
            Real.rpow ((T.S.n k : ℝ) ^ (κ.ι / 2)) κ.aB :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hG hκ.aB_rng.1.le
        have hNested : Real.rpow ((T.S.n k : ℝ) ^ (κ.ι / 2)) κ.aB =
            (T.S.n k : ℝ) ^ (κ.ι / 2 * κ.aB) := by
          exact (Real.rpow_mul (Nat.cast_nonneg (T.S.n k)) (κ.ι / 2) κ.aB).symm
        have hExpPow : Real.rpow ((𝒯.P j).g : ℝ) κ.aB ≤
            (T.S.n k : ℝ) ^ κ.ι := by
          calc
            Real.rpow ((𝒯.P j).g : ℝ) κ.aB ≤
                Real.rpow ((T.S.n k : ℝ) ^ (κ.ι / 2)) κ.aB := hGpow
            _ = (T.S.n k : ℝ) ^ (κ.ι / 2 * κ.aB) := hNested
            _ ≤ (T.S.n k : ℝ) ^ κ.ι :=
              Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hABleOne, hκ.ι_rng.1])
        have hExp : Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
            Real.exp (-Real.rpow ((𝒯.P j).g : ℝ) κ.aB) :=
          Real.exp_le_exp.mpr (neg_le_neg hExpPow)
        calc
          (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
              (T.S.N k : ℝ) / 400 * Real.exp (-Real.rpow ((𝒯.P j).g : ℝ) κ.aB) :=
            mul_le_mul_of_nonneg_left hExp (by positivity)
          _ ≤ (𝒯.P j).M := by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hMass
    | highDirect =>
        rcases h𝒯.direct_data (Or.inr hm) j with ⟨_, _, hMass, _, _, _, _⟩
        have hG := h𝒯.direct_scale_bound (Or.inr hm) j
        have hGpow : Real.rpow ((𝒯.P j).g : ℝ) κ.aB ≤
            Real.rpow ((T.S.n k : ℝ) ^ (κ.ι / 2)) κ.aB :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hG hκ.aB_rng.1.le
        have hNested : Real.rpow ((T.S.n k : ℝ) ^ (κ.ι / 2)) κ.aB =
            (T.S.n k : ℝ) ^ (κ.ι / 2 * κ.aB) :=
          (Real.rpow_mul (Nat.cast_nonneg (T.S.n k)) (κ.ι / 2) κ.aB).symm
        have hExpPow : Real.rpow ((𝒯.P j).g : ℝ) κ.aB ≤
            (T.S.n k : ℝ) ^ κ.ι := by
          calc
            Real.rpow ((𝒯.P j).g : ℝ) κ.aB ≤
                Real.rpow ((T.S.n k : ℝ) ^ (κ.ι / 2)) κ.aB := hGpow
            _ = (T.S.n k : ℝ) ^ (κ.ι / 2 * κ.aB) := hNested
            _ ≤ (T.S.n k : ℝ) ^ κ.ι :=
              Real.rpow_le_rpow_of_exponent_le hnR (by nlinarith [hABleOne, hκ.ι_rng.1])
        have hExp : Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
            Real.exp (-Real.rpow ((𝒯.P j).g : ℝ) κ.aB) :=
          Real.exp_le_exp.mpr (neg_le_neg hExpPow)
        calc
          (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
              (T.S.N k : ℝ) / 400 * Real.exp (-Real.rpow ((𝒯.P j).g : ℝ) κ.aB) :=
            mul_le_mul_of_nonneg_left hExp (by positivity)
          _ ≤ (𝒯.P j).M := by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hMass
    | lowCluster =>
        rcases h𝒯.cluster_data (Or.inl hm) j with
          ⟨_, _, hMass, _, _, _, _, hHeight, _, _, _, _⟩
        have hqNat : 1 ≤ (𝒯.P j).q := by
          rw [(h𝒯.measured_scales j).2]
          unfold qScale
          exact Nat.one_le_pow' _ 1
        have hq : (1 : ℝ) ≤ (𝒯.P j).q := by exact_mod_cast hqNat
        have hPower : Real.rpow ((𝒯.P j).q : ℝ) κ.aC ≤ (𝒯.P j).h := by
          have hheight : Real.rpow ((𝒯.P j).q : ℝ)
              (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ≤ (𝒯.P j).h := by
            simpa only [Nat.cast_ite] using hHeight
          have hexp : κ.aC ≤
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) := by
            by_cases hlow : 𝒯.mode = .lowCluster
            · simp [hlow, hACLeMlo]
            · simp [hlow, hACLeMlo.trans hMloLeMhi]
          exact le_trans (Real.rpow_le_rpow_of_exponent_le hq hexp) hheight
        have halloc := (h𝒯.allocation_bounds j).1
        have hHeightSmall : (𝒯.P j).h < (T.S.n k : ℝ) ^ κ.ι :=
          lt_of_le_of_lt (by exact_mod_cast (le_max_left _ _)) halloc
        have hExpPow : Real.rpow ((𝒯.P j).q : ℝ) κ.aC ≤
            (T.S.n k : ℝ) ^ κ.ι := lt_of_le_of_lt hPower hHeightSmall |>.le
        have hExp : Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
            Real.exp (-Real.rpow ((𝒯.P j).q : ℝ) κ.aC) :=
          Real.exp_le_exp.mpr (neg_le_neg hExpPow)
        calc
          (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
              (T.S.N k : ℝ) / 400 * Real.exp (-Real.rpow ((𝒯.P j).q : ℝ) κ.aC) :=
            mul_le_mul_of_nonneg_left hExp (by positivity)
          _ ≤ (𝒯.P j).M := by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hMass
    | highSmall =>
        rcases h𝒯.cluster_data (Or.inr (Or.inl hm)) j with
          ⟨_, _, hMass, _, _, _, _, hHeight, _, _, _, _⟩
        have hqNat : 1 ≤ (𝒯.P j).q := by
          rw [(h𝒯.measured_scales j).2]
          unfold qScale
          exact Nat.one_le_pow' _ 1
        have hq : (1 : ℝ) ≤ (𝒯.P j).q := by exact_mod_cast hqNat
        have hPower : Real.rpow ((𝒯.P j).q : ℝ) κ.aC ≤ (𝒯.P j).h := by
          have hheight : Real.rpow ((𝒯.P j).q : ℝ)
              (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ≤ (𝒯.P j).h := by
            simpa only [Nat.cast_ite] using hHeight
          have hexp : κ.aC ≤
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) := by
            by_cases hlow : 𝒯.mode = .lowCluster
            · simp [hlow, hACLeMlo]
            · simp [hlow, hACLeMlo.trans hMloLeMhi]
          exact le_trans (Real.rpow_le_rpow_of_exponent_le hq hexp) hheight
        have halloc := (h𝒯.allocation_bounds j).1
        have hHeightSmall : (𝒯.P j).h < (T.S.n k : ℝ) ^ κ.ι :=
          lt_of_le_of_lt (by exact_mod_cast (le_max_left _ _)) halloc
        have hExpPow : Real.rpow ((𝒯.P j).q : ℝ) κ.aC ≤
            (T.S.n k : ℝ) ^ κ.ι := (lt_of_le_of_lt hPower hHeightSmall).le
        have hExp : Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
            Real.exp (-Real.rpow ((𝒯.P j).q : ℝ) κ.aC) :=
          Real.exp_le_exp.mpr (neg_le_neg hExpPow)
        calc
          (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
              (T.S.N k : ℝ) / 400 * Real.exp (-Real.rpow ((𝒯.P j).q : ℝ) κ.aC) :=
            mul_le_mul_of_nonneg_left hExp (by positivity)
          _ ≤ (𝒯.P j).M := by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hMass
    | highLarge =>
        rcases h𝒯.cluster_data (Or.inr (Or.inr hm)) j with
          ⟨_, _, hMass, _, _, _, _, hHeight, _, _, _, _⟩
        have hqNat : 1 ≤ (𝒯.P j).q := by
          rw [(h𝒯.measured_scales j).2]
          unfold qScale
          exact Nat.one_le_pow' _ 1
        have hq : (1 : ℝ) ≤ (𝒯.P j).q := by exact_mod_cast hqNat
        have hPower : Real.rpow ((𝒯.P j).q : ℝ) κ.aC ≤ (𝒯.P j).h := by
          have hheight : Real.rpow ((𝒯.P j).q : ℝ)
              (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ≤ (𝒯.P j).h := by
            simpa only [Nat.cast_ite] using hHeight
          have hexp : κ.aC ≤
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) := by
            by_cases hlow : 𝒯.mode = .lowCluster
            · simp [hlow, hACLeMlo]
            · simp [hlow, hACLeMlo.trans hMloLeMhi]
          exact le_trans (Real.rpow_le_rpow_of_exponent_le hq hexp) hheight
        have halloc := (h𝒯.allocation_bounds j).1
        have hHeightSmall : (𝒯.P j).h < (T.S.n k : ℝ) ^ κ.ι :=
          lt_of_le_of_lt (by exact_mod_cast (le_max_left _ _)) halloc
        have hExpPow : Real.rpow ((𝒯.P j).q : ℝ) κ.aC ≤
            (T.S.n k : ℝ) ^ κ.ι := (lt_of_le_of_lt hPower hHeightSmall).le
        have hExp : Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
            Real.exp (-Real.rpow ((𝒯.P j).q : ℝ) κ.aC) :=
          Real.exp_le_exp.mpr (neg_le_neg hExpPow)
        calc
          (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) ≤
              (T.S.N k : ℝ) / 400 * Real.exp (-Real.rpow ((𝒯.P j).q : ℝ) κ.aC) :=
            mul_le_mul_of_nonneg_left hExp (by positivity)
          _ ≤ (𝒯.P j).M := by simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using hMass
  have hUnionDisjoint : ((Finset.univ : Finset (Fin 𝒯.m)) : Set (Fin 𝒯.m)).PairwiseDisjoint
      (fun j => (𝒯.P j).X) := by
    intro j hj l hl hjl
    exact h𝒯.patch_X_disjoint j l hjl
  let Xall := Finset.univ.biUnion (fun j : Fin 𝒯.m => (𝒯.P j).X)
  have hXallSub : Xall ⊆ T.X k := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    exact Finset.sdiff_subset (((h𝒯.patch_supports j).1.trans ((h𝒯.patch_supports j).2.1)) hxj)
  have hSumMass : (𝒯.m : ℝ) *
      ((T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι))) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin 𝒯.m)), ((𝒯.P j).M : ℝ) := by
    calc
      (𝒯.m : ℝ) *
          ((T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι))) =
          ∑ j ∈ (Finset.univ : Finset (Fin 𝒯.m)),
            ((T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι))) := by simp
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin 𝒯.m)), ((𝒯.P j).M : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hPatchMass j
  have hmNat : (𝒯.m : ℝ) ≤ 400 * Real.exp ((T.S.n k : ℝ) ^ κ.ι) := by
    have hUnionCard := Finset.card_biUnion hUnionDisjoint
    have hCardSum : (Xall.card : ℝ) =
        ∑ j ∈ (Finset.univ : Finset (Fin 𝒯.m)), ((𝒯.P j).M : ℝ) := by
      calc
        (Xall.card : ℝ) =
            ∑ j ∈ (Finset.univ : Finset (Fin 𝒯.m)), ((𝒯.P j).X.card : ℝ) := by
          exact_mod_cast hUnionCard
        _ = ∑ j ∈ (Finset.univ : Finset (Fin 𝒯.m)), ((𝒯.P j).M : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact_mod_cast (𝒯.P j).cardX
    have hUnionBound : (Xall.card : ℝ) ≤ T.S.N k := by
      have hcard := Finset.card_le_card hXallSub
      have hlt : (T.X k).card ≤ T.S.N k := by simpa using Finset.card_le_univ (T.X k)
      exact_mod_cast (le_trans hcard hlt)
    have hFactorPos : 0 <
        (T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι)) :=
      mul_pos (div_pos hNpos (by norm_num)) (Real.exp_pos _)
    have hProduct : (𝒯.m : ℝ) *
        ((T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι))) ≤ T.S.N k := by
      rw [← hCardSum] at hSumMass
      exact le_trans hSumMass hUnionBound
    have hQuot := (le_div_iff₀ hFactorPos).2 hProduct
    calc
      (𝒯.m : ℝ) ≤ (T.S.N k : ℝ) /
          ((T.S.N k : ℝ) / 400 * Real.exp (-((T.S.n k : ℝ) ^ κ.ι))) := hQuot
      _ = 400 * Real.exp ((T.S.n k : ℝ) ^ κ.ι) := by
        rw [Real.exp_neg]
        field_simp [ne_of_gt hNpos]
  have hmSmall : (𝒯.m : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) := by
    calc
      (𝒯.m : ℝ) ≤ 400 * Real.exp ((T.S.n k : ℝ) ^ κ.ι) := hmNat
      _ = Real.exp (Real.log (400 : ℝ) + (T.S.n k : ℝ) ^ κ.ι) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 400)]
      _ ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) :=
        Real.exp_le_exp.mpr hCountLog
  have huNat : 1 ≤ κ.u := by
    have ht := hκ.u_rng.2
    omega
  have huR : (1 : ℝ) ≤ κ.u := by exact_mod_cast huNat
  have hLogRatio : ∀ j : Fin 𝒯.m,
      Real.log ((T.S.N k : ℝ) / (𝒯.P j).M) ≤ (T.S.n k : ℝ) ^ κ.ι := by
    intro j
    have hMj : 0 < ((𝒯.P j).M : ℝ) :=
      lt_of_lt_of_le (mul_pos (div_pos hNpos (by norm_num)) (Real.exp_pos _)) (hPatchMass j)
    by_cases hb : 𝒯.mode = .bounded
    · rcases (h𝒯.bounded_data hb).2 j with ⟨_, _, _, hMass, _⟩
      have hMass' : (T.S.N k : ℝ) / 400 ≤ (𝒯.P j).M := by
        simpa only [div_eq_mul_inv, one_mul, mul_comm] using hMass
      have hratio : (T.S.N k : ℝ) / (𝒯.P j).M ≤ 400 := by
        apply (div_le_iff₀ hMj).mpr
        have hm := (div_le_iff₀ (by norm_num : (0 : ℝ) < 400)).mp hMass'
        linarith only [hm]
      exact (Real.log_le_log (div_pos hNpos hMj) hratio).trans hLog400Iota
    · have hall := (h𝒯.allocation_bounds j).2
      rcases hall with hbad | ⟨_, hlog⟩
      · exact (hb hbad).elim
      have hHeight : ((𝒯.P j).h : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by
        have hm := (h𝒯.allocation_bounds j).1
        have hmR : max ((𝒯.P j).h : ℝ) ((𝒯.P j).ℓ : ℝ) < (T.S.n k : ℝ) ^ κ.ι := by
          exact_mod_cast hm
        exact (le_max_left _ _).trans_lt hmR
      have direct (hd : 𝒯.mode = .lowDirect ∨ 𝒯.mode = .highDirect) :
          0 ≤ 𝒯.gain j ∧ 𝒯.gain j ≤ (T.S.n k : ℝ) ^ κ.ι := by
        have hg := h𝒯.direct_scale_bound hd j
        have hgn : 0 ≤ ((𝒯.P j).g : ℝ) := Nat.cast_nonneg _
        have hgle : ((𝒯.P j).g : ℝ) ≤ (T.S.n k : ℝ) ^ κ.ι :=
          hg.trans (Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [hκ.ι_rng.1]))
        have hdv : ((𝒯.P j).g : ℝ) / 1000 ≤ (𝒯.P j).g := div_le_self hgn (by norm_num)
        rcases hd with hd | hd <;> simpa only [Tiling.gain, hd] using
          (show 0 ≤ ((𝒯.P j).g : ℝ) / 1000 ∧ ((𝒯.P j).g : ℝ) / 1000 ≤ (T.S.n k : ℝ) ^ κ.ι from
            ⟨div_nonneg hgn (by norm_num), hdv.trans hgle⟩)
      have cluster (hc : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨ 𝒯.mode = .highLarge) :
          0 ≤ 𝒯.gain j ∧ 𝒯.gain j ≤ (T.S.n k : ℝ) ^ κ.ι := by
        have hhn : 0 ≤ ((𝒯.P j).h : ℝ) := Nat.cast_nonneg _
        have hprod := mul_le_mul_of_nonneg_right hAone.le hhn
        have hdv : κ.a * (𝒯.P j).h / 10 ^ 6 ≤ κ.a * (𝒯.P j).h :=
          div_le_self (mul_nonneg hApos.le hhn) (by norm_num)
        have hle : κ.a * (𝒯.P j).h / 10 ^ 6 ≤ (T.S.n k : ℝ) ^ κ.ι := by
          linarith only [hprod, hdv, hHeight]
        rcases hc with hc | hc | hc <;> simpa only [Tiling.gain, hc] using
          (show 0 ≤ κ.a * (𝒯.P j).h / 10 ^ 6 ∧ κ.a * (𝒯.P j).h / 10 ^ 6 ≤ (T.S.n k : ℝ) ^ κ.ι from
            ⟨div_nonneg (mul_nonneg hApos.le hhn) (by norm_num), hle⟩)
      have hg : 0 ≤ 𝒯.gain j ∧ 𝒯.gain j ≤ (T.S.n k : ℝ) ^ κ.ι := by
        cases hm : 𝒯.mode with
        | bounded => exact (hb hm).elim
        | lowDirect => exact direct (Or.inl hm)
        | highDirect => exact direct (Or.inr hm)
        | lowCluster => exact cluster (Or.inl hm)
        | highSmall => exact cluster (Or.inr (Or.inl hm))
        | highLarge => exact cluster (Or.inr (Or.inr hm))
      have hden : (1 : ℝ) ≤ 1000 * κ.u := by linarith only [huR]
      exact hlog.trans ((div_le_self hg.1 hden).trans hg.2)
  have hLogRatioXs : ∀ j : Fin 𝒯.m,
      Real.log ((T.S.N k : ℝ) / (𝒯.P j).M) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) := by
    intro j
    exact le_trans (hLogRatio j) hNPowerXs
  have hInputWidths : ∀ j : Fin 𝒯.m, (π j).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
    intro j
    have hMjPos : 0 < ((𝒯.P j).M : ℝ) := by
      exact lt_of_lt_of_le
        (mul_pos (div_pos hNpos (by norm_num)) (Real.exp_pos _)) (hPatchMass j)
    have hj := hInput j
    rcases hj with ⟨hSupport, hCapOrEq⟩
    by_cases hc : 𝒯.mode.isCluster
    · have hCap : ∀ y, (𝒯.P j).M * (π j).w y ≤
          Real.exp (10 * (𝒯.kScale j : ℝ) * 𝒯.tScale j) := by
        simpa [hc] using hCapOrEq
      have hModes : 𝒯.mode = .lowCluster ∨ 𝒯.mode = .highSmall ∨
          𝒯.mode = .highLarge := by
        cases hm : 𝒯.mode with
        | bounded => simp [Mode.isCluster, hm] at hc
        | lowDirect => simp [Mode.isCluster, hm] at hc
        | highDirect => simp [Mode.isCluster, hm] at hc
        | lowCluster => exact Or.inl rfl
        | highSmall => exact Or.inr (Or.inl rfl)
        | highLarge => exact Or.inr (Or.inr rfl)
      have hClusterData := h𝒯.cluster_data hModes j
      rcases hClusterData with ⟨_, _, _, _, _, _, _, hHeight, _, _, _, _⟩
      have hhNat : 1 ≤ (𝒯.P j).h := by
        have hqNat : 1 ≤ (𝒯.P j).q := by
          rw [(h𝒯.measured_scales j).2]
          unfold qScale
          exact Nat.one_le_pow' _ 1
        have hq : (1 : ℝ) ≤ (𝒯.P j).q := by exact_mod_cast hqNat
        have hMlo : (1 : ℝ) ≤ (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) := by
          by_cases hm : 𝒯.mode = .lowCluster
          · simp [hm, hMloOne]
          · have hMhi : (1 : ℝ) ≤ κ.Mhi := le_trans hMloOne hMloLeMhi
            simp [hm, hMhi]
        have hheight' : Real.rpow ((𝒯.P j).q : ℝ)
            (if 𝒯.mode = .lowCluster then κ.Mlo else κ.Mhi) ≤ (𝒯.P j).h := by
          simpa only [Nat.cast_ite] using hHeight
        have hOneHeight : (1 : ℝ) ≤ (𝒯.P j).h := by
          have he : 0 ≤ (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) := by
            simpa only [Nat.cast_ite] using (le_trans (by norm_num : (0 : ℝ) ≤ 1) hMlo)
          have hpow : 1 ≤ Real.rpow ((𝒯.P j).q : ℝ)
              (if 𝒯.mode = .lowCluster then (κ.Mlo : ℝ) else κ.Mhi) :=
            Real.one_le_rpow hq he
          exact le_trans hpow hheight'
        exact_mod_cast hOneHeight
      rcases Lane_q_s13_clean.slice_bounds_by_height κ hκ (𝒯.P j).h hhNat with
        ⟨hKNat, hTNat⟩
      have hKR : (𝒯.kScale j : ℝ) ≤ (𝒯.P j).h := by
        simpa [Tiling.kScale] using (show (sliceK κ (𝒯.P j).h : ℝ) ≤ (𝒯.P j).h by exact_mod_cast hKNat)
      have hTR : (𝒯.tScale j : ℝ) ≤ (𝒯.P j).h := by
        simpa [Tiling.tScale] using (show (sliceT κ (𝒯.P j).h : ℝ) ≤ (𝒯.P j).h by exact_mod_cast hTNat)
      have hHeightBound : (𝒯.P j).h < (T.S.n k : ℝ) ^ κ.ι :=
        lt_of_le_of_lt (by exact_mod_cast (le_max_left _ _)) (h𝒯.allocation_bounds j).1
      have hN2 : ((T.S.n k : ℝ) ^ κ.ι) ^ 2 =
          (T.S.n k : ℝ) ^ (2 * κ.ι) := by
        have hadd := Real.rpow_add hnPos κ.ι κ.ι
        have hexp : κ.ι + κ.ι = 2 * κ.ι := by ring
        simpa only [pow_two, hexp] using hadd.symm
      have hCapSize : 10 * (𝒯.kScale j : ℝ) * 𝒯.tScale j ≤
          10 * (T.S.n k : ℝ) ^ (2 * κ.ι) := by
        have hprod := mul_le_mul hKR hTR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hheightSq := mul_le_mul hHeightBound.le hHeightBound.le
          (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) κ.ι)
        nlinarith [hN2]
      have hWbudget : Real.log ((T.S.N k : ℝ) / (𝒯.P j).M) +
          10 * (𝒯.kScale j : ℝ) * 𝒯.tScale j ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) := by
        have hIotaToSquare := le_trans (hLogRatio j) hNPowerLe
        have htotal : Real.log ((T.S.N k : ℝ) / (𝒯.P j).M) +
            10 * (𝒯.kScale j : ℝ) * 𝒯.tScale j ≤
              12 * (T.S.n k : ℝ) ^ (2 * κ.ι) := by nlinarith [hIotaToSquare, hCapSize]
        exact le_trans htotal hPowerGap
      have hratioPos : 0 < (T.S.N k : ℝ) / (𝒯.P j).M := div_pos hNpos hMjPos
      intro y
      apply (le_div_iff₀ hNpos).mpr
      rw [mul_comm]
      calc
        (T.S.N k : ℝ) * (π j).w y =
            ((T.S.N k : ℝ) / (𝒯.P j).M) *
              ((𝒯.P j).M * (π j).w y) := by field_simp [ne_of_gt hMjPos]
        _ ≤ ((T.S.N k : ℝ) / (𝒯.P j).M) *
              Real.exp (10 * (𝒯.kScale j : ℝ) * 𝒯.tScale j) :=
          mul_le_mul_of_nonneg_left (hCap y) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ = Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P j).M) +
              10 * (𝒯.kScale j : ℝ) * 𝒯.tScale j) := by
          rw [Real.exp_add, Real.exp_log hratioPos]
        _ ≤ Real.exp ((T.S.n k : ℝ) ^ (κ.xs / 4)) :=
          Real.exp_le_exp.mpr hWbudget
    · have hPi : π j = Law.unifCore (𝒯.P j).Y (h𝒯.patch_nonempty j).2 := by
        simpa [hc] using hCapOrEq
      rw [hPi]
      have hCoreWidth := Lane_q_s13_clean.unifCore_width (𝒯.P j).Y
        (h𝒯.patch_nonempty j).2
      have hWidthBound : Real.log ((T.S.N k : ℝ) / (𝒯.P j).Y.card) ≤
          (T.S.n k : ℝ) ^ (κ.xs / 4) := by
        rw [(𝒯.P j).cardY]
        exact le_trans (hLogRatio j) hNPowerXs
      exact hCoreWidth.mono hWidthBound
  have hTauWidth : (Law.unifCore X hXne).WidthLE
      (Real.log ((T.S.N k : ℝ) / X.card)) :=
    Lane_q_s13_clean.unifCore_width X hXne
  have hLogX : Real.log ((T.S.N k : ℝ) / X.card) ≤ (T.S.n k : ℝ) ^ (κ.xs / 4) := by
    simpa [X, (𝒯.P i).cardX] using hLogRatioXs i
  have hInputSupports : ∀ j : Fin 𝒯.m, (π j).SupportedIn (T.Y k) := by
    intro j y hy
    have hYsub : (𝒯.P j).Y ⊆ T.Y k :=
      (((h𝒯.patch_supports j).2.2.1).trans
        ((h𝒯.patch_supports j).2.2.2)).trans Finset.sdiff_subset
    exact (hInput j).1 y (fun hyP => hy (hYsub hyP))
  have hTailOutput := hTailEvent X hXne hXsub hLogX
    (Finset.univ : Finset (Fin 𝒯.m)) π hInputSupports hInputWidths
    (by simpa only [Finset.card_univ, Fintype.card_fin] using hmSmall)
  rcases hTailOutput with ⟨Xtail, hXtailSub, hXtailLoss, hRowsTail⟩
  let τ := Law.unifCore X hXne
  have hTailLossSmall : ((X \ Xtail).card : ℝ) ≤ κ.a / 8 * (𝒯.P i).M := by
    have h := hXtailLoss
    rw [show X.card = (𝒯.P i).M by simp [X, (𝒯.P i).cardX]] at h
    have hmul := mul_le_mul_of_nonneg_right hTailLoss (Nat.cast_nonneg (𝒯.P i).M)
    exact le_trans h (by simpa [X, (𝒯.P i).cardX] using hmul)
  have hTauSupp : τ.SupportedIn (T.X k) := by
    intro x hx
    have hxNotX : x ∉ X := by
      intro hxX
      exact hx (hXsub hxX)
    simp [τ, Law.unifCore, hxNotX]
  have hTauWidth' : τ.WidthLE (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M)) := by
    have h := hTauWidth
    simpa [X, (𝒯.P i).cardX] using h
  have hBadFamily : ∀ j : Fin 𝒯.m,
      (X.filter fun x : Fin (T.S.N k) =>
        2 * bstar T k <
          |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|).card ≤
        2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) *
          (𝒯.P i).M := by
    intro j
    let Badj := X.filter fun x => 2 * bstar T k <
      |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|
    have hWidthPair : ((T.S.n k : ℝ) ^ (κ.xs / 4) ≤ (T.S.n k : ℝ) ^ κ.xs) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [hκ.xs_rng.1])
    have hAlphaHalf : κ.α * T.S.n k / 2 ≤ κ.α * T.S.n k := by
      have hp := mul_nonneg hκ.α_rng.1.le (Nat.cast_nonneg (T.S.n k))
      linarith
    have hbstar : 0 ≤ bstar T k := by unfold bstar; positivity
    have hOut := HypercubeRamsey.S12.exceptional_first hDisc 𝒯.c
      (w₁ := (T.S.n k : ℝ) ^ (κ.xs / 4)) (W₂ := κ.α * T.S.n k / 2)
      (w := Real.log ((T.S.N k : ℝ) / (𝒯.P i).M))
      (Or.inl ⟨hWidthPair, hAlphaHalf⟩) (π j) (hInputSupports j) (hInputWidths j)
      τ hTauSupp hTauWidth'
    have hBadSub : Badj ⊆ Finset.univ.filter fun x : Fin (T.S.N k) =>
        bstar T k < |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2| := by
      intro x hx
      have hmem := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
        lt_of_le_of_lt (by linarith only [hbstar] : bstar T k ≤ 2 * bstar T k) hmem.2⟩
    have hBadMass : (∑ x ∈ Badj, τ.w x) = (Badj.card : ℝ) / (𝒯.P i).M := by
      have hweight (x : Fin (T.S.N k)) (hx : x ∈ Badj) : τ.w x = ((𝒯.P i).M : ℝ)⁻¹ := by
        have hxX : x ∈ X := (Finset.mem_filter.mp hx).1
        simp [τ, Law.unifCore, hxX, X, (𝒯.P i).cardX]
      calc
        (∑ x ∈ Badj, τ.w x) = ∑ x ∈ Badj, ((𝒯.P i).M : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hweight x hx
        _ = (Badj.card : ℝ) / (𝒯.P i).M := by
          simp [div_eq_mul_inv]
    have hMassOut := HypercubeRamsey.S12.Exceptional_q_s12_exc.sum_subset_le
      Badj (Finset.univ.filter fun x : Fin (T.S.N k) =>
        bstar T k < |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|) τ.w hBadSub
      (fun x hx => τ.nonneg x)
    have hMassOut' : (Badj.card : ℝ) / (𝒯.P i).M ≤
        2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) := by
      rw [← hBadMass]
      exact le_trans hMassOut hOut
    have hBadCard : (Badj.card : ℝ) ≤
        2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) *
          (𝒯.P i).M := by
      exact (div_le_iff₀ hMpos).mp hMassOut'
    exact hBadCard
  let J := Finset.univ.filter fun j : Fin 𝒯.m => j ≠ i
  let Bad := J.biUnion fun j => X.filter fun x =>
    2 * bstar T k < |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|
  have hRootBud : (T.S.n k : ℝ) ^ (κ.xs / 4) +
      (T.S.n k : ℝ) ^ (0.1 : ℝ) ≤ κ.α * T.S.n k / 4 := by
    calc
      (T.S.n k : ℝ) ^ (κ.xs / 4) + (T.S.n k : ℝ) ^ (0.1 : ℝ) ≤
          Real.sqrt (T.S.n k : ℝ) + Real.sqrt (T.S.n k : ℝ) := add_le_add hXsRoot h01Root
      _ ≤ κ.α * T.S.n k / 4 := by linarith [hRootAlpha]
  have hBadBudget : (J.card : ℝ) *
      (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2)) ≤ κ.a / 8 := by
    have hJcard : (J.card : ℝ) ≤ (𝒯.m : ℝ) := by
      have ht : J.card ≤ 𝒯.m := by simpa only [Fintype.card_fin] using Finset.card_le_univ J
      exact_mod_cast ht
    have hJexp : (J.card : ℝ) ≤ Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) :=
      le_trans hJcard hmSmall
    have hExpCombo : Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) +
        (T.S.n k : ℝ) ^ (0.1 : ℝ) - κ.α * T.S.n k / 2 ≤
          -κ.α * T.S.n k / 4 := by linarith [hRootBud, hLogRatioXs i]
    calc
      (J.card : ℝ) *
          (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2)) ≤
          Real.exp ((T.S.n k : ℝ) ^ (0.1 : ℝ)) *
            (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2)) :=
        mul_le_mul_of_nonneg_right hJexp (by positivity)
      _ = 2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) +
            (T.S.n k : ℝ) ^ (0.1 : ℝ) - κ.α * T.S.n k / 2) := by
        rw [show Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) +
            (T.S.n k : ℝ) ^ (0.1 : ℝ) - κ.α * T.S.n k / 2 =
            (T.S.n k : ℝ) ^ (0.1 : ℝ) +
              (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) by ring,
          Real.exp_add]
        ring
      _ ≤ 2 * Real.exp (-κ.α * T.S.n k / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExpCombo) (by norm_num)
      _ ≤ κ.a / 8 := hOutExp
  have hBadCardSmall : (Bad.card : ℝ) ≤ κ.a / 8 * (𝒯.P i).M := by
    have hcard := Finset.card_biUnion_le (s := J) (t := fun j =>
      X.filter fun x => 2 * bstar T k <
        |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|)
    have hsum : (∑ j ∈ J, ((X.filter fun x => 2 * bstar T k <
        |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|).card : ℝ)) ≤
        (J.card : ℝ) *
          (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) *
            (𝒯.P i).M) := by
      calc
        _ ≤ ∑ j ∈ J,
            (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) *
              (𝒯.P i).M) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hBadFamily j
        _ = (J.card : ℝ) *
            (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) *
              (𝒯.P i).M) := by simp
    have hcardCast : (Bad.card : ℝ) ≤
        ∑ j ∈ J, ((X.filter fun x => 2 * bstar T k <
          |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2|).card : ℝ) := by
      exact_mod_cast hcard
    calc
      (Bad.card : ℝ) ≤ _ := hcardCast
      _ ≤ (J.card : ℝ) *
          (2 * Real.exp (Real.log ((T.S.N k : ℝ) / (𝒯.P i).M) - κ.α * T.S.n k / 2) *
            (𝒯.P i).M) := hsum
      _ ≤ κ.a / 8 * (𝒯.P i).M := by
        have h := mul_le_mul_of_nonneg_right hBadBudget hMpos.le
        nlinarith [h]
  have hBadSub : Bad ⊆ X := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, hj, hxj⟩
    exact (Finset.mem_filter.mp hxj).1
  let cleaned : Finset (Fin (T.S.N k)) := SDiff.sdiff (C.C ∩ Xtail) Bad
  have hCleanSub : cleaned ⊆ C.C := by
    intro x hx
    exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).1
  have hCleanX : cleaned ⊆ X := by
    intro x hx
    exact hXtailSub (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2
  have hDiffSub : X \ cleaned ⊆ (X \ C.C) ∪ (X \ Xtail) ∪ Bad := by
    intro x hx
    simp only [cleaned, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union] at hx ⊢
    tauto
  have hLossSplit : ((X \ cleaned).card : ℝ) ≤
      ((X \ C.C).card : ℝ) + ((X \ Xtail).card : ℝ) + (Bad.card : ℝ) := by
    have hCardSub := Finset.card_le_card hDiffSub
    have hUnion : ((X \ C.C ∪ (X \ Xtail) ∪ Bad).card : ℝ) ≤
        ((X \ C.C).card : ℝ) + ((X \ Xtail).card : ℝ) + (Bad.card : ℝ) := by
      have h1 := Finset.card_union_le (X \ C.C) (X \ Xtail)
      have h2 := Finset.card_union_le (X \ C.C ∪ (X \ Xtail)) Bad
      exact_mod_cast (by omega : ((X \ C.C ∪ (X \ Xtail) ∪ Bad).card : ℕ) ≤
        (X \ C.C).card + (X \ Xtail).card + Bad.card)
    exact le_trans (by exact_mod_cast hCardSub) hUnion
  have hDCLoss : ((X \ C.C).card : ℝ) < κ.a / 2 * (𝒯.P i).M := by
    have hSub : X \ C.C ⊆ (X \ D.C) ∪ (D.C \ C.C) := by
      intro x hx
      have hxX := (Finset.mem_sdiff.mp hx).1
      have hxnotC := (Finset.mem_sdiff.mp hx).2
      by_cases hxd : x ∈ D.C
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxd, hxnotC⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxX, hxd⟩)
    have hcard := Finset.card_le_card hSub
    have hUnionCard : ((X \ D.C ∪ (D.C \ C.C)).card : ℝ) ≤
        ((X \ D.C).card : ℝ) + ((D.C \ C.C).card : ℝ) := by
      exact_mod_cast Finset.card_union_le (X \ D.C) (D.C \ C.C)
    have hDloss : ((X \ D.C).card : ℝ) < κ.a / 4 * (𝒯.P i).M := by
      have heq : X \ D.C = (𝒯.P i).X \ D.C := by simp [X]
      rw [heq]
      exact D.loss
    have hCloss := C.loss
    exact lt_of_le_of_lt (le_trans (by exact_mod_cast hcard) hUnionCard) (by nlinarith [hDloss, hCloss])
  have hTotalLoss : ((X \ cleaned).card : ℝ) < κ.a * (𝒯.P i).M := by
    nlinarith [hLossSplit, hDCLoss, hTailLossSmall, hBadCardSmall, hAhalf]
  have hCleanNonempty : cleaned.Nonempty := by
    by_contra hne
    have hEmpty : cleaned = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have he : ((X \ cleaned).card : ℝ) = (𝒯.P i).M := by
      simp only [hEmpty, Finset.sdiff_empty, X, (𝒯.P i).cardX]
    have hbad : ((𝒯.P i).M : ℝ) < κ.a * (𝒯.P i).M := by
      rwa [he] at hTotalLoss
    have hlt : κ.a * (𝒯.P i).M < (𝒯.P i).M := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hAone hMpos
    exact (lt_asymm hlt) hbad
  have hCardLower : (𝒯.P i).M / 2 ≤ (cleaned.card : ℝ) := by
    have hEq := Finset.card_sdiff_add_card_eq_card hCleanX
    have hM : (X.card : ℝ) = (cleaned.card : ℝ) + ((X \ cleaned).card : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_comm] using hEq.symm)
    have hXcard : (X.card : ℝ) = (𝒯.P i).M := by simp [X, (𝒯.P i).cardX]
    rw [hXcard] at hM
    nlinarith [hTotalLoss, hM]
  have hCardWaste : (1 - κ.a) * ((𝒯.P i).M : ℝ) ≤ (cleaned.card : ℝ) := by
    have hEq := Finset.card_sdiff_add_card_eq_card hCleanX
    have hM : (X.card : ℝ) = (cleaned.card : ℝ) + ((X \ cleaned).card : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_comm] using hEq.symm)
    have hXcard : (X.card : ℝ) = (𝒯.P i).M := by simp [X, (𝒯.P i).cardX]
    rw [hXcard] at hM
    linarith [hTotalLoss, hM]
  refine ⟨⟨cleaned, ?_, hTotalLoss, hCleanNonempty, hCardLower, hCardWaste, ?_, ?_⟩⟩
  · intro x hx
    exact hCleanSub hx
  · intro π' hNear j hji x hx
    have hxNotBad : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
    have hxNotBadj : x ∉ X.filter fun z =>
        2 * bstar T k < |deg (T.S.E k) 𝒯.c (π j).w z - 1 / 2| := by
      intro hmem
      have hmemUnion : x ∈ Bad := by
        apply Finset.mem_biUnion.mpr
        refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩, hmem⟩
      exact hxNotBad hmemUnion
    have hxbase : |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2| ≤ 2 * bstar T k := by
      by_contra hlt
      exact hxNotBadj (Finset.mem_filter.mpr ⟨hCleanX hx, lt_of_not_ge hlt⟩)
    have hNearDeg := Lane_q_s13_clean.deg_l1
      (T.S.E k) 𝒯.c (π j) (π' j) x (hNear j)
    have hNearAbs : |deg (T.S.E k) 𝒯.c (π' j).w x -
        deg (T.S.E k) 𝒯.c (π j).w x| ≤ (T.S.n k : ℝ) ^ (-3 : ℝ) := by
      rw [abs_sub_comm]
      exact hNearDeg
    have hNminus : (T.S.n k : ℝ) ^ (-3 : ℝ) ≤ bstar T k := by
      unfold bstar
      exact Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    have hdecomp : deg (T.S.E k) 𝒯.c (π' j).w x - 1 / 2 =
        (deg (T.S.E k) 𝒯.c (π' j).w x - deg (T.S.E k) 𝒯.c (π j).w x) +
          (deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2) := by ring
    calc
      |deg (T.S.E k) 𝒯.c (π' j).w x - 1 / 2| =
          |(deg (T.S.E k) 𝒯.c (π' j).w x - deg (T.S.E k) 𝒯.c (π j).w x) +
            (deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2)| := by rw [hdecomp]
      _ ≤ |deg (T.S.E k) 𝒯.c (π' j).w x - deg (T.S.E k) 𝒯.c (π j).w x| +
            |deg (T.S.E k) 𝒯.c (π j).w x - 1 / 2| := abs_add_le _ _
      _ ≤ 3 * bstar T k := by nlinarith [hNearAbs, hxbase, hNminus, hApos]
  · intro π' hNear j x hx
    have hbase := hRowsTail j (Finset.mem_univ j) x
      ((Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2)
    exact hRelaxEvent (π j) (π' j) X x hbase (hNear j)

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
