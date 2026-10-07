import HypercubeRamsey.S12.ModerateMoment
import HypercubeRamsey.S12.CenteredMoment

/-!
# Section 12 homogeneous extension counts and peeling
-/

namespace HypercubeRamsey.S12

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

/-- L12.5: the homogeneous support, clique exclusion, and peeling budget. -/
structure HomogeneousInput (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (k : ℕ) (c : Colour) (C0 : ℝ) where
  S : InterSetting T k (κ.xs / 4)
  π : Law (T.S.N k)
  homogeneous : ∀ l, S.π l = π
  Sp : Finset (Fin (T.S.N k))
  Sp_nonempty : Sp.Nonempty
  Sp_subset : Sp ⊆ T.X k
  τ_supported : S.τ.SupportedIn Sp
  π_supported : π.SupportedIn (T.Y k)
  degree_gate : ∀ x ∈ Sp, DegGate (T.S.E k) c π.w C0 (bstar T k) x
  degree_positive : ∀ x ∈ Sp, 0 < deg (T.S.E k) c π.w x
  Q : ℝ
  Q_large : Real.log
      (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ Q ∧ 1 ≤ Q
  noClique : NoClique (T.S.E k) c Sp π.w κ.θ Q
  gamma : ℝ
  gamma_eq : gamma = Real.exp (Cstar κ.u κ.ξ * Q) *
    Sp.sup' Sp_nonempty (fun x => S.τ.w x *
      Real.rpow (deg (T.S.E k) c π.w x) (-(S.d : ℝ)))
  gamma_nonneg : 0 ≤ gamma
  gamma_lt_one : gamma < 1

/-- L12.5(iii): the peeling bound for every valid homogeneous setting at the stage. -/
def HomogeneousPeelingClaim (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (c : Colour) (C0 : ℝ) : Prop :=
  ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0,
      ∑ I : Finset (Fin κ.u),
        ∑ xs : Fin κ.u → Fin (T.S.N k),
          (if ¬ Moderate (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) κ.ξ xs
           then prodW H.S.τ.w xs *
             posTerm (T.S.E k) c (fun _ : Fin H.S.d => H.π.w) I xs else 0) ≤
            4 ^ (κ.u + 1) * H.gamma

/-- L12.5(i): the number of exceptional one-label extensions is bounded by Ramsey. -/
theorem homogeneous_extension_count (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0,
        ∀ i₀ : Fin κ.u, ∀ xs : Fin κ.u → Fin (T.S.N k),
          (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
          ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
            i₀ ∈ J ∧ 2 ≤ J.card ∧
              κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
              Real.exp (Cstar κ.u κ.ξ * H.Q) := by
  sorry

/-- L12.5(ii): every label has few large-correlation partners in the support. -/
theorem homogeneous_conflict_count (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0, ∀ x : Fin (T.S.N k),
        ((H.Sp.filter (fun z =>
          κ.ξ < |corr (T.S.E k) c H.π.w x z|)).card : ℝ) ≤
            Real.exp (Cstar κ.u κ.ξ * H.Q) := by
  sorry

/-- L12.5(iii): large-interaction tuples have bounded total positive-term mass. -/
theorem homogeneous_peeling (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0) :
    HomogeneousPeelingClaim κ hκ T c C0 := by
  sorry

/-- L12.5(iv): even-moment and peeling bounds give the homogeneous lower-tail estimate. -/
theorem homogeneous_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hModerate : ModerateMomentClaim κ T c C0)
    (hPeeling : HomogeneousPeelingClaim κ hκ T c C0) :
    ∀ᶠ k in atTop,
      ∀ H : HomogeneousInput κ hκ T k c C0, ∀ t : ℝ, 0 ≤ t → t < 1 →
        (∑ ys : Fin H.S.d → Fin (T.S.N k),
          if Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys < t
          then ∏ l, H.π.w (ys l) else 0) ≤
            (1 - t) ^ (-(κ.u : ℝ)) *
              ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
                4 ^ (κ.u + 1) * H.gamma) := by
  sorry

/-- L12.5: package the extension, conflict, peeling, and lower-tail nodes. -/
structure HomogeneousPeelingResults (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) : Prop where
  extension_count : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0,
      ∀ i₀ : Fin κ.u, ∀ xs : Fin κ.u → Fin (T.S.N k),
        (∀ i, i ≠ i₀ → xs i ∈ H.Sp) →
        ((H.Sp.filter (fun z => ∃ J : Finset (Fin κ.u),
          i₀ ∈ J ∧ 2 ≤ J.card ∧
            κ.ξ < |inter (T.S.E k) c H.π.w J (Function.update xs i₀ z)|)).card : ℝ) ≤
            Real.exp (Cstar κ.u κ.ξ * H.Q)
  conflict_count : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0, ∀ x : Fin (T.S.N k),
      ((H.Sp.filter (fun z => κ.ξ < |corr (T.S.E k) c H.π.w x z|)).card : ℝ) ≤
        Real.exp (Cstar κ.u κ.ξ * H.Q)
  peeling : HomogeneousPeelingClaim κ hκ T c C0
  lower_tail : ∀ᶠ k in atTop,
    ∀ H : HomogeneousInput κ hκ T k c C0, ∀ t : ℝ, 0 ≤ t → t < 1 →
      (∑ ys : Fin H.S.d → Fin (T.S.N k),
        if Zmass (T.S.E k) c H.S.τ.w (fun _ : Fin H.S.d => H.π.w) ys < t
        then ∏ l, H.π.w (ys l) else 0) ≤
          (1 - t) ^ (-(κ.u : ℝ)) *
            ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
              4 ^ (κ.u + 1) * H.gamma)

/-- L12.5: the public package assembled from its four theorem nodes. -/
theorem homogeneous_peeling_export (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    HomogeneousPeelingResults κ hκ T hDeep c C0 hC0 := by
  have hm := moderate_moment κ hκ T hDeep c C0 hC0
  have hp := homogeneous_peeling κ hκ T hDeep c C0 hC0 hm
  exact ⟨homogeneous_extension_count κ hκ T hDeep c C0 hC0,
    homogeneous_conflict_count κ hκ T hDeep c C0 hC0, hp,
    homogeneous_lower_tail κ hκ T hDeep c C0 hC0 hm hp⟩

end HypercubeRamsey.S12
