import HypercubeRamsey.S16.Geometry
import HypercubeRamsey.S03.NearProductInjection

/-!
# Section 16 calibrated bins and role labels

Both calibrations use the finite-dimensional separation lemma from the
Section 3 injection work. The sorry-bearing sampler contracts stop before
exact marginal calibration; the exported theorems assemble exact marginals
from price witnesses and compact convex marginal images.
-/

namespace HypercubeRamsey.S16

open Classical
open scoped BigOperators

/-- P16.3a/P16.4c: finite assignment marginals as a vector. -/
noncomputable def assignmentMarginalVector {I O : Type*} [Fintype I]
    [DecidableEq I] [Fintype O] (Q : FinLaw (I → O)) : I × O → ℝ :=
  fun io => Q.pr (fun x => x io.1 = io.2)

/-- P16.3a/P16.4c: feasible marginal vectors for a set of assignment laws. -/
noncomputable def assignmentMarginalImage {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] (feasible : Set (FinLaw (I → O))) :
    Set ((I × O) → ℝ) :=
  {v | ∃ Q ∈ feasible, ∀ i o, v (i, o) = assignmentMarginalVector Q (i, o)}

def marginalTargetVector {I O : Type*} [Fintype I] [Fintype O]
    (target : I → O → ℝ) : (I × O) → ℝ := fun io => target io.1 io.2

def targetMarginalPrice {I O : Type*} [Fintype I] [Fintype O]
    (target : I → O → ℝ) (price : (I × O) → ℝ) : ℝ :=
  ∑ io, price io * target io.1 io.2

noncomputable def assignmentMarginalPrice {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] (Q : FinLaw (I → O)) (price : (I × O) → ℝ) : ℝ :=
  ∑ io, price io * assignmentMarginalVector Q io

/-- P16.3a/P16.4c: reusable price-separation calibration from S03/Injection. -/
theorem exact_marginals_by_separation {I O : Type*} [Fintype I]
    [DecidableEq I] [Fintype O]
    (feasible : Set (FinLaw (I → O))) (target : I → O → ℝ)
    (hcompact : IsCompact (assignmentMarginalImage feasible))
    (hconvex : Convex ℝ (assignmentMarginalImage feasible))
    (hprice : ∀ price : (I × O) → ℝ,
      ∃ Q ∈ feasible,
        targetMarginalPrice target price ≤ assignmentMarginalPrice Q price) :
    ∃ Q ∈ feasible, ∀ i o, Q.pr (fun x => x i = o) = target i o := by
  classical
  let image := assignmentMarginalImage feasible
  let p := marginalTargetVector target
  have hp : p ∈ image := by
    apply HypercubeRamsey.calibration_by_separation image p hcompact hconvex
    intro price
    obtain ⟨Q, hQ, hPrice⟩ := hprice price
    refine ⟨assignmentMarginalVector Q, ⟨Q, hQ, fun _ _ => rfl⟩, ?_⟩
    simpa [p, targetMarginalPrice, assignmentMarginalPrice,
      marginalTargetVector, assignmentMarginalVector] using hPrice
  rcases hp with ⟨Q, hQ, hMarg⟩
  refine ⟨Q, hQ, ?_⟩
  intro i o
  have h := hMarg i o
  simpa [p, marginalTargetVector, assignmentMarginalVector] using h.symm

/-- P16.3 input: one typical pool and one passing slice history.
The `target` laws are the pool-restricted `q̃_g`; failure probabilities and
column loads are the conditional reference quantities in the paper. -/
structure GroupBinProblem (Group Bin Star Column : Type*)
    [Fintype Group] [DecidableEq Group] [Fintype Bin]
    [Fintype Star] [Fintype Column] where
  group_nonempty : Nonempty Group
  star_nonempty : Nonempty Star
  target : Group → FinLaw Bin
  participants : Star → Finset Group
  failureMass : Star → (Group → Bin) → ℝ
  columnLoad : (Group → Bin) → Column → ℝ
  d : ℕ
  ε : ℝ

namespace GroupBinProblem

variable {Group Bin Star Column : Type*}
variable [Fintype Group] [DecidableEq Group] [Fintype Bin]
variable [Fintype Star] [Fintype Column]

noncomputable def independentLaw (P : GroupBinProblem Group Bin Star Column) :
    FinLaw (Group → Bin) := FinLaw.pi P.target

noncomputable def independentFailure (P : GroupBinProblem Group Bin Star Column) (s : Star) : ℝ :=
  (P.independentLaw).E (P.failureMass s)

noncomputable def nominalColumnLoad (P : GroupBinProblem Group Bin Star Column)
    (y : Column) : ℝ := (P.independentLaw).E (fun a => P.columnLoad a y)

noncomputable def pinnedFailure (P : GroupBinProblem Group Bin Star Column)
    (s : Star) (g : Group) (b : Bin) : ℝ := by
  classical
  let mass := (P.independentLaw).pr (fun a => a g = b)
  exact if hmass : mass = 0 then 0 else
    (P.independentLaw).E (fun a => if a g = b then P.failureMass s a else 0) / mass

noncomputable def feasible (P : GroupBinProblem Group Bin Star Column)
    (Q : FinLaw (Group → Bin)) : Prop :=
  (∀ a, Q.w a ≠ 0 →
    (∀ s g g', g ∈ P.participants s → g' ∈ P.participants s → g ≠ g' → a g ≠ a g') ∧
    (∀ s, P.failureMass s a ≤ Real.rpow P.ε (1 / 8 : ℝ)) ∧
    (∀ y, P.columnLoad a y ≤ 1 / 5)) ∧
  ∀ (S : Finset Group) (a : Group → Bin),
    Q.pr (fun x => ∀ g ∈ S, x g = a g) ≤
      Real.exp (Real.rpow (P.d : ℝ) (-0.05) * S.card) *
        ∏ g ∈ S, (P.target g).w (a g)

noncomputable def feasibleSet (P : GroupBinProblem Group Bin Star Column) :
    Set (FinLaw (Group → Bin)) := {Q | P.feasible Q}

def targetPrice (P : GroupBinProblem Group Bin Star Column)
    (price : (Group × Bin) → ℝ) : ℝ :=
  ∑ gb, price gb * (P.target gb.1).w gb.2

noncomputable def lawPrice (Q : FinLaw (Group → Bin)) (price : (Group × Bin) → ℝ) : ℝ :=
  ∑ gb, price gb * Q.pr (fun a => a gb.1 = gb.2)

noncomputable def image (P : GroupBinProblem Group Bin Star Column) :=
  assignmentMarginalImage P.feasibleSet

def targetVector (P : GroupBinProblem Group Bin Star Column) :=
  marginalTargetVector (fun g b => (P.target g).w b)

end GroupBinProblem

/-- P16.3b hypotheses are the calibrated inputs furnished by L16.2, P15.3b,
and the slice solver. They state base atom, column, and pinned-star margins,
not the existence of an avoiding bin law. -/
structure GroupBinHypotheses {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Star Column : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) : Prop where
  scale_large : κ.d0 ≤ P.d
  epsilon_pos : 0 < P.ε ∧ P.ε ≤ 1
  atom_small : ∀ g b, (P.target g).w b ≤ Real.rpow (P.d : ℝ) (-0.95)
  column_slack : ∀ y, P.nominalColumnLoad y ≤ 1 / 10
  star_mean_small : ∀ s, P.independentFailure s ≤ 2 * Real.sqrt P.ε
  pinned_star_mean_small : ∀ s g b, P.pinnedFailure s g b ≤ 2 * Real.sqrt P.ε
  star_degree_small : ∀ g,
    ((Finset.univ.filter fun s => g ∈ P.participants s).card : ℝ) ≤
      Real.rpow (P.d : ℝ) (0.01)

/-- P16.3b: price-directed perturbed avoidance supplies feasible witnesses for
every price. The estimates include the group-bin pin bound from L16.2. -/
theorem perturbed_group_bin_price_witness {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Star Column : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column)
    (hP : GroupBinHypotheses hκ P) :
    ∀ price : (Group × Bin) → ℝ,
      ∃ Q ∈ P.feasibleSet,
        GroupBinProblem.targetPrice P price ≤ GroupBinProblem.lawPrice Q price := by
  sorry

/-- P16.3c: finite feasibility image. The support, star, capacity, and joint
conditions defining `feasible` are closed linear constraints on a finite law.-/
theorem group_bin_image_compact_convex {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin]
    [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) :
    IsCompact P.image ∧ Convex ℝ P.image := by
  sorry

/-- P16.3: exact calibrated group bins assembled using S03 separation. -/
theorem calibrated_group_bins {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Star Column : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column)
    (hP : GroupBinHypotheses hκ P) :
    ∃ Q : FinLaw (Group → Bin), P.feasible Q ∧
      ∀ g b, Q.pr (fun a => a g = b) = (P.target g).w b := by
  obtain ⟨hcompact, hconvex⟩ := group_bin_image_compact_convex P
  have hprice : ∀ price : (Group × Bin) → ℝ,
      ∃ Q ∈ P.feasibleSet,
        GroupBinProblem.targetPrice P price ≤ GroupBinProblem.lawPrice Q price :=
    perturbed_group_bin_price_witness hκ P hP
  have hprice' : ∀ price : (Group × Bin) → ℝ,
      ∃ Q ∈ P.feasibleSet,
        targetMarginalPrice (fun g b => (P.target g).w b) price ≤
          assignmentMarginalPrice Q price := by
    intro price
    obtain ⟨Q, hQ, hPrice⟩ := hprice price
    refine ⟨Q, hQ, ?_⟩
    simpa [GroupBinProblem.targetPrice, GroupBinProblem.lawPrice,
      targetMarginalPrice, assignmentMarginalPrice, assignmentMarginalVector] using hPrice
  obtain ⟨Q, hQ, hMarg⟩ := exact_marginals_by_separation
    P.feasibleSet (fun g b => (P.target g).w b) hcompact hconvex hprice'
  exact ⟨Q, hQ, hMarg⟩

/-- L16.4 input: within-bin role laws. Cluster safety tests are the
internal events; direct mode has no such tests. -/
structure RoleLabelProblem (Role : Type) (Star : Type*) (d : ℕ)
    [Fintype Role] [DecidableEq Role] [Fintype Star] where
  role_nonempty : Nonempty Role
  star_nonempty : Nonempty Star
  target : Role → FinLaw (Fin d)
  starBad : Star → (Role → Fin d) → Prop
  jointExponent : ℝ
  queryExponent : ℝ

namespace RoleLabelProblem

variable {Role : Type} {Star : Type*} {d : ℕ}
variable [Fintype Role] [DecidableEq Role] [Fintype Star]

noncomputable def productLaw (P : RoleLabelProblem Role Star d) : FinLaw (Role → Fin d) :=
  FinLaw.pi P.target

noncomputable def independentStarFailure (P : RoleLabelProblem Role Star d) (s : Star) : ℝ :=
  (P.productLaw).pr (P.starBad s)

noncomputable def pinnedStarFailure (P : RoleLabelProblem Role Star d)
    (s : Star) (r : Role) (y : Fin d) : ℝ := by
  classical
  let mass := (P.productLaw).pr (fun x => x r = y)
  exact if hmass : mass = 0 then 0 else
    (P.productLaw).pr (fun x => x r = y ∧ P.starBad s x) / mass

noncomputable def feasible (P : RoleLabelProblem Role Star d) (Q : FinLaw (Role → Fin d)) : Prop :=
  (∀ x, Q.w x ≠ 0 → Function.Injective x ∧ ∀ s, ¬ P.starBad s x) ∧
  ∀ (S : Finset Role) (y : Role → Fin d),
    (S.card : ℝ) ≤ Real.rpow (d : ℝ) P.queryExponent →
    Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
      Real.exp (Real.rpow (d : ℝ) P.jointExponent * S.card) *
        ∏ r ∈ S, (P.target r).w (y r)

noncomputable def feasibleSet (P : RoleLabelProblem Role Star d) :
    Set (FinLaw (Role → Fin d)) := {Q | P.feasible Q}

noncomputable def image (P : RoleLabelProblem Role Star d) := assignmentMarginalImage P.feasibleSet

end RoleLabelProblem

/-- Convert a Part C finite law to the Part A API used by Lemma 3.9. -/
noncomputable def finLawToFramework {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : FinProb Ω where
  w := P.w
  nonneg := P.nonneg
  sum_eq_one := P.sum_one

noncomputable def finProbToFinLaw {Ω : Type*} [Fintype Ω] (P : FinProb Ω) : FinLaw Ω where
  w := P.w
  nonneg := P.nonneg
  sum_one := P.sum_eq_one

@[simp] theorem finProbToFinLaw_pr {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    (finProbToFinLaw P).pr A = P.pr A := rfl

/-- P16.4 seed: Lemma 3.9 supplies injective role labels with exact input
marginals and near-product bounds before internal-event avoidance. -/
theorem role_near_product_seed {κ : CConsts} (hκ : κ.Admissible)
    {Role : Type} {Star : Type*} [Fintype Role] [DecidableEq Role] [Fintype Star]
    {d : ℕ} (P : RoleLabelProblem Role Star d) (hd : κ.d0 ≤ d)
    (hatom : ∀ r y, (P.target r).w y ≤ Real.rpow (d : ℝ) (-0.95))
    (hload : ∀ y, ∑ r, (P.target r).w y ≤ 0.4) :
    ∃ Q : FinLaw (Role → Fin d),
      (∀ x, Q.w x ≠ 0 → Function.Injective x) ∧
      (∀ r y, Q.pr (fun x => x r = y) = (P.target r).w y) ∧
      ∀ (S : Finset Role) (y : Role → Fin d),
        (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
          Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (P.target r).w (y r) := by
  classical
  let lab : ∀ r : Role, Fin d → Fin d := fun _ => id
  let laws : ∀ r : Role, FinProb (Fin d) := fun r => finLawToFramework (P.target r)
  have hAtom : ∀ r y, labMarg (laws r) (lab r) y ≤ (d : ℝ) ^ (-0.95 : ℝ) := by
    intro r y
    simpa [lab, laws, labMarg, finLawToFramework] using hatom r y
  have hLoad : ∀ y, ∑ r, labMarg (laws r) (lab r) y ≤ 0.4 := by
    intro y
    simpa [lab, laws, labMarg, finLawToFramework] using hload y
  obtain ⟨Q, hInjective, hMarginal, hJoint⟩ :=
    hκ.nearProduct d hd (R := Role) (Ω := fun _ => Fin d) lab laws hAtom hLoad
  let J : FinLaw (Role → Fin d) := finProbToFinLaw Q
  refine ⟨J, ?_, ?_, ?_⟩
  · intro x hx
    exact hInjective x hx
  · intro r y
    calc
      J.pr (fun x => x r = y) = Q.pr (fun x => x r = y) :=
        finProbToFinLaw_pr Q (fun x => x r = y)
      _ = (P.target r).w y := by simpa [laws, finLawToFramework] using hMarginal r y
  · intro S y hS
    calc
      J.pr (fun x => ∀ r ∈ S, x r = y r) =
          Q.pr (fun x => ∀ r ∈ S, x r = y r) :=
        finProbToFinLaw_pr Q (fun x => ∀ r ∈ S, x r = y r)
      _ ≤ Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) *
          ∏ r ∈ S, (P.target r).w (y r) := by
        simpa [laws, finLawToFramework] using hJoint S y hS

/-- P16.4b hypotheses give the small atoms, low columns, fixed-scale exponents,
and pinned-star bounds used by local avoidance. -/
structure RoleLabelHypotheses {κ : CConsts} (hκ : κ.Admissible)
    {Role : Type} {Star : Type*} [Fintype Role] [DecidableEq Role] [Fintype Star]
    {d : ℕ} (P : RoleLabelProblem Role Star d) : Prop where
  scale_large : κ.d0 ≤ d
  d_pos : 1 ≤ d
  atom_small : ∀ r y, (P.target r).w y ≤ Real.rpow (d : ℝ) (-0.95)
  column_load : ∀ y, ∑ r, (P.target r).w y ≤ 0.4
  output_exponent : -0.04 ≤ P.jointExponent
  query_exponent : P.queryExponent ≤ 0.025
  star_failure_small : ∀ s,
    P.independentStarFailure s ≤ Real.rpow (d : ℝ) (-10)
  pinned_star_failure_small : ∀ s r y,
    P.pinnedStarFailure s r y ≤ Real.rpow (d : ℝ) (-10)

/-- P16.4b: local avoidance and price perturbation produce feasible witnesses
for every price. The seed is the L3.9 sampler above. -/
theorem perturbed_role_label_price_witness {κ : CConsts} (hκ : κ.Admissible)
    {Role : Type} {Star : Type*} [Fintype Role] [DecidableEq Role] [Fintype Star]
    {d : ℕ} (P : RoleLabelProblem Role Star d)
    (hP : RoleLabelHypotheses hκ P)
    (hSeed : ∃ Q : FinLaw (Role → Fin d),
      (∀ x, Q.w x ≠ 0 → Function.Injective x) ∧
      (∀ r y, Q.pr (fun x => x r = y) = (P.target r).w y) ∧
      (∀ (S : Finset Role) (y : Role → Fin d),
        (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
          Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (P.target r).w (y r))) :
    ∀ price : (Role × Fin d) → ℝ,
      ∃ Q ∈ P.feasibleSet,
        targetMarginalPrice (fun r y => (P.target r).w y) price ≤
          assignmentMarginalPrice Q price := by
  sorry

/-- P16.4c: compact convex feasible marginal image after internal avoidance. -/
theorem role_label_image_compact_convex {Role : Type} {Star : Type*}
    [Fintype Role] [DecidableEq Role] [Fintype Star] {d : ℕ}
    (P : RoleLabelProblem Role Star d) :
    IsCompact P.image ∧ Convex ℝ P.image := by
  sorry

/-- P16.4: exact calibrated role labels, with every star failure avoided. -/
theorem calibrated_role_labels {κ : CConsts} (hκ : κ.Admissible)
    {Role : Type} {Star : Type*} [Fintype Role] [DecidableEq Role] [Fintype Star]
    {d : ℕ} (P : RoleLabelProblem Role Star d)
    (hP : RoleLabelHypotheses hκ P) :
    ∃ Q : FinLaw (Role → Fin d), P.feasible Q ∧
      ∀ r y, Q.pr (fun x => x r = y) = (P.target r).w y := by
  obtain ⟨seed, hInjective, hMarginal, hJoint⟩ := role_near_product_seed hκ P
    hP.scale_large hP.atom_small hP.column_load
  have hSeed : ∃ Q : FinLaw (Role → Fin d),
      (∀ x, Q.w x ≠ 0 → Function.Injective x) ∧
      (∀ r y, Q.pr (fun x => x r = y) = (P.target r).w y) ∧
      (∀ (S : Finset Role) (y : Role → Fin d),
        (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
          Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (P.target r).w (y r)) :=
    ⟨seed, hInjective, hMarginal, hJoint⟩
  obtain ⟨hcompact, hconvex⟩ := role_label_image_compact_convex P
  have hprice : ∀ price : (Role × Fin d) → ℝ,
      ∃ Q ∈ P.feasibleSet,
        targetMarginalPrice (fun r y => (P.target r).w y) price ≤
          assignmentMarginalPrice Q price :=
    perturbed_role_label_price_witness hκ P hP hSeed
  obtain ⟨Q, hQ, hMarg⟩ := exact_marginals_by_separation
    P.feasibleSet (fun r y => (P.target r).w y) hcompact hconvex hprice
  exact ⟨Q, hQ, hMarg⟩

end HypercubeRamsey.S16
