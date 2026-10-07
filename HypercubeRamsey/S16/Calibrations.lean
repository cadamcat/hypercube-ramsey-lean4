import HypercubeRamsey.S16.Avoidance
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

/-- The price step is separate from avoidance. Centering removes each row's
constant price; the two-sided error costs at most 2η times the centered L1 norm. -/
theorem relative_singletons_price_gain {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] (p q : I → FinLaw O) (Q : FinLaw (I → O))
    (ρ η : ℝ) (c : I × O → ℝ)
    (hη : 0 ≤ η) (hgap : 4 * η < ρ)
    (hupper : ∀ i o, (q i).w o ≤ 2 * (p i).w o)
    (hgain : (∑ io : I × O, centeredPrice p c io.1 io.2 * (q io.1).w io.2) ≥
      ρ / 2 * ∑ io : I × O, |centeredPrice p c io.1 io.2| * (p io.1).w io.2)
    (hrelative : ∀ i o, |Q.pr (fun x => x i = o) - (q i).w o| ≤ η * (q i).w o) :
    targetMarginalPrice (fun i o => (p i).w o) c ≤ assignmentMarginalPrice Q c := by
  sorry

/-- Successful cluster-cell primitive data. Failure masses are conditional
reference-label probabilities; column loads are sums of actual group contributions. -/
structure GroupBinProblem (Group Bin Star Column : Type*)
    [Fintype Group] [DecidableEq Group] [Fintype Bin]
    [Fintype Star] [Fintype Column] where
  target : Group → FinLaw Bin
  participants : Star → Finset Group
  failureMass : Star → (Group → Bin) → ℝ
  contribution : Group → Bin → Column → ℝ
  d : ℕ
  ε : ℝ

namespace GroupBinProblem

variable {Group Bin Star Column : Type*}
variable [Fintype Group] [DecidableEq Group] [Fintype Bin]
variable [Fintype Star] [Fintype Column]

noncomputable def independentLaw (P : GroupBinProblem Group Bin Star Column) := FinLaw.pi P.target
noncomputable def independentFailure (P : GroupBinProblem Group Bin Star Column) (s : Star) :=
  P.independentLaw.E (P.failureMass s)
def columnLoad (P : GroupBinProblem Group Bin Star Column) (a : Group → Bin) (y : Column) : ℝ :=
  ∑ g, P.contribution g (a g) y
noncomputable def nominalColumnLoad (P : GroupBinProblem Group Bin Star Column) (y : Column) :=
  P.independentLaw.E (fun a => P.columnLoad a y)
noncomputable def pinnedFailure (P : GroupBinProblem Group Bin Star Column)
    (s : Star) (g : Group) (b : Bin) : ℝ :=
  P.independentLaw.E (fun a => if a g = b then P.failureMass s a else 0) /
    P.independentLaw.pr (fun a => a g = b)

def safe (P : GroupBinProblem Group Bin Star Column) (a : Group → Bin) : Prop :=
  (∀ s g g', g ∈ P.participants s → g' ∈ P.participants s → g ≠ g' → a g ≠ a g') ∧
  (∀ s, P.failureMass s a ≤ Real.rpow P.ε (1 / 8 : ℝ)) ∧
  (∀ y, P.columnLoad a y ≤ 1 / 5)

noncomputable def feasible (P : GroupBinProblem Group Bin Star Column) (Q : FinLaw (Group → Bin)) : Prop :=
  (∀ a, Q.w a ≠ 0 → P.safe a) ∧
  ∀ (S : Finset Group) (a : Group → Bin),
    Q.pr (fun x => ∀ g ∈ S, x g = a g) ≤
      Real.exp (Real.rpow (P.d : ℝ) (-0.05) * S.card) * ∏ g ∈ S, (P.target g).w (a g)
noncomputable def feasibleSet (P : GroupBinProblem Group Bin Star Column) : Set (FinLaw (Group → Bin)) :=
  {Q | P.feasible Q}
def targetPrice (P : GroupBinProblem Group Bin Star Column) (price : Group × Bin → ℝ) :=
  targetMarginalPrice (fun g b => (P.target g).w b) price
noncomputable def lawPrice (Q : FinLaw (Group → Bin)) (price : Group × Bin → ℝ) :=
  assignmentMarginalPrice Q price
noncomputable def image (P : GroupBinProblem Group Bin Star Column) := assignmentMarginalImage P.feasibleSet

end GroupBinProblem

/-- The capacity producer supplies finite bad-event certificates for every
permitted perturbation, with base law exactly the independent group law.
This is the missing P15.3b input, not a feasible-law existence assumption. -/
structure GroupBinHypotheses {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Star Column : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [DecidableEq Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) : Prop where
  scale_large : κ.d0 ≤ P.d
  d_pos : 2 ≤ P.d
  perturbation_range : Real.rpow (P.d : ℝ) (-0.1) ≤ 1 / 3
  price_gap : 4 * Real.rpow (P.d : ℝ) (-2) < Real.rpow (P.d : ℝ) (-0.1)
  epsilon_pos : 0 < P.ε ∧ P.ε ≤ 1
  failure_range : ∀ s a, 0 ≤ P.failureMass s a ∧ P.failureMass s a ≤ 1
  failure_local : ∀ s, DependsOn (P.failureMass s) (P.participants s : Set Group)
  contribution_range : ∀ g b y, 0 ≤ P.contribution g b y ∧
    P.contribution g b y ≤ Real.rpow (P.d : ℝ) (-0.5)
  atom_small : ∀ g b, (P.target g).w b ≤ Real.rpow (P.d : ℝ) (-0.95)
  column_slack : ∀ y, P.nominalColumnLoad y ≤ 1 / 10
  star_mean_small : ∀ s, P.independentFailure s ≤ Real.rpow P.ε (1 / 4 : ℝ)
  pinned_star_mean_small : ∀ s g b, P.pinnedFailure s g b ≤ Real.rpow P.ε (1 / 4 : ℝ)
  star_size_small : ∀ s, (P.participants s).card ≤ Real.rpow (P.d : ℝ) 0.01
  star_degree_small : ∀ g,
    ((Finset.univ.filter fun s => g ∈ P.participants s).card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.01
  certificates : ∀ q : Group → FinLaw Bin,
    RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.1)) →
    ∃ A : AvoidanceData (fun a : Group → Bin => a) (fun g : Group => g) P.safe,
      A.base = FinLaw.pi q ∧
      AvoidanceHypotheses A P.target q (fun _ => True)
        (Real.rpow (P.d : ℝ) (-0.1)) (Real.rpow (P.d : ℝ) (-2))
        (Real.rpow (P.d : ℝ) (-0.05))

/-- P16.3b assembly: tilt, avoid, control singleton error, then pay the price. -/
theorem perturbed_group_bin_price_witness {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Star Column : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [DecidableEq Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) (hP : GroupBinHypotheses hκ P) :
    ∀ price : Group × Bin → ℝ, ∃ Q ∈ P.feasibleSet,
      P.targetPrice price ≤ GroupBinProblem.lawPrice Q price := by
  intro price
  let ρ := Real.rpow (P.d : ℝ) (-0.1)
  let η := Real.rpow (P.d : ℝ) (-2)
  let rate := Real.rpow (P.d : ℝ) (-0.05)
  have hρ : 0 < ρ ∧ ρ ≤ 1 / 3 := ⟨by
    dsimp [ρ]
    apply Real.rpow_pos_of_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hP.d_pos), hP.perturbation_range⟩
  obtain ⟨q, hq, hupper, hgain⟩ := centered_price_perturbation P.target ρ hρ price
  obtain ⟨A, _hbase, hA⟩ := hP.certificates q hq
  have hpos := avoidance_positive A P.target q (fun _ => True) ρ η rate hA
  let Q := A.avoidingLaw hpos
  have hs := avoidance_support A P.target q (fun _ => True) ρ η rate hA hpos
  have hj := avoidance_joint A P.target q (fun _ => True) ρ η rate hA hpos
  have hm := avoidance_relative_singletons A P.target q (fun _ => True) ρ η rate hA hpos
  have hp := relative_singletons_price_gain P.target q Q ρ η price (by dsimp [η]; positivity)
    hP.price_gap hupper hgain hm
  exact ⟨Q, ⟨hs, fun S a => hj S a trivial⟩, hp⟩

/-- Closed finite linear constraints have a compact convex marginal image. -/
theorem group_bin_image_compact_convex {Group Bin Star Column : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) : IsCompact P.image ∧ Convex ℝ P.image := by
  sorry

/-- P16.3: exact calibration after all four quantitative avoidance steps. -/
theorem calibrated_group_bins {κ : CConsts} (hκ : κ.Admissible)
    {Group Bin Star Column : Type*} [Fintype Group] [DecidableEq Group]
    [Fintype Bin] [DecidableEq Bin] [Fintype Star] [Fintype Column]
    (P : GroupBinProblem Group Bin Star Column) (hP : GroupBinHypotheses hκ P) :
    ∃ Q : FinLaw (Group → Bin), P.feasible Q ∧
      ∀ g b, Q.pr (fun a => a g = b) = (P.target g).w b := by
  obtain ⟨hc, hv⟩ := group_bin_image_compact_convex P
  exact exact_marginals_by_separation P.feasibleSet (fun g b => (P.target g).w b) hc hv
    (perturbed_group_bin_price_witness hκ P hP)

/-- Cluster blocks are physical bins; the direct-mode block is the entire
cell pool. Thus `d` is d_i in cluster mode and L_slot in direct mode. -/
inductive RoleLabelRegime | cluster | direct
  deriving DecidableEq

structure RoleLabelProblem (Role Label Star Block : Type)
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block] where
  regime : RoleLabelRegime
  d : ℕ
  h : ℕ
  target : Role → FinLaw Label
  blockOf : Role → Block
  blockLabels : Block → Finset Label
  block_card : ∀ b, (blockLabels b).card = d
  blocks_disjoint : ∀ b b', b ≠ b' → Disjoint (blockLabels b) (blockLabels b')
  target_support : ∀ r y, (target r).w y ≠ 0 → y ∈ blockLabels (blockOf r)
  participants : Star → Finset Role
  starBad : Star → (Role → Label) → Prop
  star_local : ∀ s x x', (∀ r ∈ participants s, x r = x' r) → (starBad s x ↔ starBad s x')

namespace RoleLabelProblem

variable {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
variable [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]

noncomputable def productLaw (P : RoleLabelProblem Role Label Star Block) := FinLaw.pi P.target
noncomputable def independentStarFailure (P : RoleLabelProblem Role Label Star Block) (s : Star) :=
  P.productLaw.pr (P.starBad s)
noncomputable def pinnedStarFailure (P : RoleLabelProblem Role Label Star Block)
    (s : Star) (r : Role) (y : Label) :=
  P.productLaw.pr (fun x => x r = y ∧ P.starBad s x) / P.productLaw.pr (fun x => x r = y)

def safe (P : RoleLabelProblem Role Label Star Block) (x : Role → Label) : Prop :=
  Function.Injective x ∧ ∀ s, ¬ P.starBad s x

def queries (P : RoleLabelProblem Role Label Star Block) (S : Finset Role) : Prop :=
  match P.regime with
  | .cluster => ∀ b, (S.filter fun r => P.blockOf r = b).card ≤ P.h
  | .direct => (S.card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025

noncomputable def rate (P : RoleLabelProblem Role Label Star Block) : ℝ :=
  Real.rpow (P.d : ℝ) (match P.regime with | .cluster => -0.01 | .direct => -0.04)

noncomputable def feasible (P : RoleLabelProblem Role Label Star Block) (Q : FinLaw (Role → Label)) : Prop :=
  (∀ x, Q.w x ≠ 0 → P.safe x) ∧ ∀ (S : Finset Role) (y : Role → Label), P.queries S →
    Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤ Real.exp (P.rate * S.card) * ∏ r ∈ S, (P.target r).w (y r)
noncomputable def feasibleSet (P : RoleLabelProblem Role Label Star Block) : Set (FinLaw (Role → Label)) :=
  {Q | P.feasible Q}
noncomputable def image (P : RoleLabelProblem Role Label Star Block) := assignmentMarginalImage P.feasibleSet

abbrev BlockState (P : RoleLabelProblem Role Label Star Block) (b : Block) :=
  {r : Role // P.blockOf r = b} → {y : Label // y ∈ P.blockLabels b}
abbrev SeedState (P : RoleLabelProblem Role Label Star Block) := ∀ b, P.BlockState b

def readout (P : RoleLabelProblem Role Label Star Block) (ω : P.SeedState) (r : Role) : Label :=
  (ω (P.blockOf r) ⟨r, rfl⟩).1

end RoleLabelProblem

/-- Per-bin injection seeds are independent whole-bin variables. -/
structure RoleBlockSeed {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (q : Role → FinLaw Label) where
  laws : ∀ b, FinLaw (P.BlockState b)
  injective : ∀ b ω, (laws b).w ω ≠ 0 → Function.Injective ω
  marginal : ∀ r y,
    (FinLaw.pi laws).pr (fun ω => P.readout ω r = y) = (q r).w y
  joint : ∀ (S : Finset Role) (y : Role → Label),
    (∀ b, ((S.filter fun r => P.blockOf r = b).card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025) →
    (FinLaw.pi laws).pr (fun ω => ∀ r ∈ S, P.readout ω r = y r) ≤
      Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) * ∏ r ∈ S, (q r).w (y r)

/-- Cluster certificates are on the actual independent block seed, and are
robust under all allowed perturbations. The direct branch has no tests. -/
structure RoleLabelHypotheses {κ : CConsts} (hκ : κ.Admissible)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) : Prop where
  scale_large : κ.d0 ≤ P.d
  d_pos : 2 ≤ P.d
  h_query : (P.h : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025
  cluster_range : P.regime = .cluster → Real.rpow (P.d : ℝ) (-0.02) ≤ 1 / 3
  price_gap : P.regime = .cluster → 4 * Real.rpow (P.d : ℝ) (-2) < Real.rpow (P.d : ℝ) (-0.02)
  atom_small : ∀ r y, (P.target r).w y ≤ Real.rpow (P.d : ℝ) (-0.95)
  column_load : ∀ y, ∑ r, (P.target r).w y ≤ 0.4
  robust_atoms : P.regime = .cluster → ∀ r y, 2 * (P.target r).w y ≤ Real.rpow (P.d : ℝ) (-0.95)
  cluster_columns : P.regime = .cluster → ∀ y, ∑ r, (P.target r).w y ≤ 0.2
  bin_roles : P.regime = .cluster → ∀ b,
    (Finset.univ.filter fun r => P.blockOf r = b).card ≤ P.d
  bin_star_degree : P.regime = .cluster → ∀ b,
    (Finset.univ.filter fun s => ∃ r ∈ P.participants s, P.blockOf r = b).card ≤ P.d * P.h
  direct_no_tests : P.regime = .direct → ∀ s x, ¬ P.starBad s x
  certificates : P.regime = .cluster → ∀ q : Role → FinLaw Label,
    RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.02)) →
    ∀ seed : RoleBlockSeed P q,
    ∃ A : AvoidanceData P.readout P.blockOf P.safe,
      A.base = FinLaw.pi seed.laws ∧
      AvoidanceHypotheses A P.target q P.queries (Real.rpow (P.d : ℝ) (-0.02))
        (Real.rpow (P.d : ℝ) (-2)) P.rate

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
    {Role : Type} [Fintype Role] [DecidableEq Role]
    {d : ℕ} (target : Role → FinLaw (Fin d)) (hd : κ.d0 ≤ d)
    (hatom : ∀ r y, (target r).w y ≤ Real.rpow (d : ℝ) (-0.95))
    (hload : ∀ y, ∑ r, (target r).w y ≤ 0.4) :
    ∃ Q : FinLaw (Role → Fin d),
      (∀ x, Q.w x ≠ 0 → Function.Injective x) ∧
      (∀ r y, Q.pr (fun x => x r = y) = (target r).w y) ∧
      ∀ (S : Finset Role) (y : Role → Fin d),
        (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
          Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (target r).w (y r) := by
  classical
  let lab : ∀ r : Role, Fin d → Fin d := fun _ => id
  let laws : ∀ r : Role, FinProb (Fin d) := fun r => finLawToFramework (target r)
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
      _ = (target r).w y := by simpa [laws, finLawToFramework] using hMarginal r y
  · intro S y hS
    calc
      J.pr (fun x => ∀ r ∈ S, x r = y r) =
          Q.pr (fun x => ∀ r ∈ S, x r = y r) :=
        finProbToFinLaw_pr Q (fun x => ∀ r ∈ S, x r = y r)
      _ ≤ Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) *
          ∏ r ∈ S, (target r).w (y r) := by
        simpa [laws, finLawToFramework] using hJoint S y hS

/-- Uniform provider obtained from the proved L3.9 wrapper, not an assumed seed. -/
def LabelSeedProvider (d₀ : ℕ) : Prop :=
  ∀ d ≥ d₀, ∀ {R : Type} [Fintype R] [DecidableEq R] (p : R → FinLaw (Fin d)),
    (∀ r y, (p r).w y ≤ Real.rpow (d : ℝ) (-0.95)) →
    (∀ y, ∑ r, (p r).w y ≤ 0.4) →
    ∃ Q : FinLaw (R → Fin d),
      (∀ x, Q.w x ≠ 0 → Function.Injective x) ∧
      (∀ r y, Q.pr (fun x => x r = y) = (p r).w y) ∧
      ∀ (S : Finset R) (y : R → Fin d), (S.card : ℝ) ≤ Real.rpow (d : ℝ) 0.025 →
        Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
          Real.exp (Real.rpow (d : ℝ) (-0.04) * S.card) * ∏ r ∈ S, (p r).w (y r)

/-- Reindex L3.9 in every actual block and take their independent product.
The input is a perturbed supported row law, with the lemma's atom/column slack. -/
theorem role_block_seed {κ : CConsts} (hκ : κ.Admissible)
    (provider : LabelSeedProvider κ.d0)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hd : κ.d0 ≤ P.d)
    (q : Role → FinLaw Label)
    (hsupport : ∀ r y, (q r).w y ≠ 0 → y ∈ P.blockLabels (P.blockOf r))
    (hatom : ∀ r y, (q r).w y ≤ Real.rpow (P.d : ℝ) (-0.95))
    (hload : ∀ y, ∑ r, (q r).w y ≤ 0.4) : Nonempty (RoleBlockSeed P q) := by
  sorry

/-- The robust input slack is retained by every centered-price perturbation. -/
theorem role_perturbation_slack {κ : CConsts} (hκ : κ.Admissible)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hP : RoleLabelHypotheses hκ P)
    (hc : P.regime = .cluster) (q : Role → FinLaw Label)
    (hq : RelativePerturbation P.target q (Real.rpow (P.d : ℝ) (-0.02))) :
    (∀ r y, (q r).w y ≠ 0 → y ∈ P.blockLabels (P.blockOf r)) ∧
    (∀ r y, (q r).w y ≤ Real.rpow (P.d : ℝ) (-0.95)) ∧
    (∀ y, ∑ r, (q r).w y ≤ 0.4) := by
  sorry

/-- Direct-mode calibration is just the block seed, with no internal tests. -/
theorem direct_role_seed_feasible {κ : CConsts} (hκ : κ.Admissible)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hP : RoleLabelHypotheses hκ P)
    (hd : P.regime = .direct) (seed : RoleBlockSeed P P.target) :
    P.feasible (FinLaw.map (FinLaw.pi seed.laws) P.readout) ∧
      ∀ r y, (FinLaw.map (FinLaw.pi seed.laws) P.readout).pr (fun x => x r = y) = (P.target r).w y := by
  sorry

/-- Cluster P16.4b assembly, on independent bin variables. -/
theorem perturbed_role_label_price_witness {κ : CConsts} (hκ : κ.Admissible)
    (provider : LabelSeedProvider κ.d0)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hP : RoleLabelHypotheses hκ P)
    (hc : P.regime = .cluster) :
    ∀ price : Role × Label → ℝ, ∃ Q ∈ P.feasibleSet,
      targetMarginalPrice (fun r y => (P.target r).w y) price ≤ assignmentMarginalPrice Q price := by
  intro price
  let ρ := Real.rpow (P.d : ℝ) (-0.02)
  let η := Real.rpow (P.d : ℝ) (-2)
  have hρ : 0 < ρ ∧ ρ ≤ 1 / 3 := ⟨by
    dsimp [ρ]
    apply Real.rpow_pos_of_pos
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hP.d_pos), hP.cluster_range hc⟩
  obtain ⟨q, hq, hu, hg⟩ := centered_price_perturbation P.target ρ hρ price
  obtain ⟨hs, ha, hl⟩ := role_perturbation_slack hκ P hP hc q hq
  obtain ⟨seed⟩ := role_block_seed hκ provider P hP.scale_large q hs ha hl
  obtain ⟨A, _hbase, hA⟩ := hP.certificates hc q hq seed
  have hpos := avoidance_positive A P.target q P.queries ρ η P.rate hA
  let Q := A.avoidingLaw hpos
  have hs := avoidance_support A P.target q P.queries ρ η P.rate hA hpos
  have hj := avoidance_joint A P.target q P.queries ρ η P.rate hA hpos
  have hm := avoidance_relative_singletons A P.target q P.queries ρ η P.rate hA hpos
  have hp := relative_singletons_price_gain P.target q Q ρ η price (by dsimp [η]; positivity)
    (hP.price_gap hc) hu hg hm
  exact ⟨Q, ⟨hs, hj⟩, hp⟩

/-- Compact convexity is independent of whether there are any feasible laws. -/
theorem role_label_image_compact_convex {Role Label Star Block : Type}
    [Fintype Role] [DecidableEq Role] [Fintype Label] [DecidableEq Label]
    [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) : IsCompact P.image ∧ Convex ℝ P.image := by
  sorry

/-- P16.4, with the paper's separate cluster and direct query domains. -/
theorem calibrated_role_labels {κ : CConsts} (hκ : κ.Admissible)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hP : RoleLabelHypotheses hκ P) :
    ∃ Q : FinLaw (Role → Label), P.feasible Q ∧
      ∀ r y, Q.pr (fun x => x r = y) = (P.target r).w y := by
  have provider : LabelSeedProvider κ.d0 := by
    intro d hd R _ _ target ha hl
    exact role_near_product_seed hκ target hd ha hl
  cases hr : P.regime with
  | direct =>
    obtain ⟨seed⟩ := role_block_seed hκ provider P hP.scale_large P.target P.target_support hP.atom_small hP.column_load
    exact ⟨_, direct_role_seed_feasible hκ P hP hr seed⟩
  | cluster =>
    obtain ⟨hc, hv⟩ := role_label_image_compact_convex P
    exact exact_marginals_by_separation P.feasibleSet (fun r y => (P.target r).w y) hc hv
      (perturbed_role_label_price_witness hκ provider P hP hr)

end HypercubeRamsey.S16
