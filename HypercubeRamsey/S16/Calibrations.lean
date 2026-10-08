import HypercubeRamsey.S16.Avoidance
import HypercubeRamsey.S03.NearProductInjection
import HypercubeRamsey.S16.Calibrations_q_s16_calib

/-!
# Section 16 calibrated bins and role labels

Both calibrations use the finite-dimensional separation lemma from the
Section 3 injection work. The sampler contracts stop before
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
  classical
  let center : I × O → ℝ := fun io => centeredPrice p c io.1 io.2
  let qm : I × O → ℝ := fun io => (q io.1).w io.2
  let Qm : I × O → ℝ := fun io => Q.pr (fun x => x io.1 = io.2)
  let pm : I × O → ℝ := fun io => (p io.1).w io.2
  let mean : I → ℝ := fun i => ∑ o, c (i, o) * (p i).w o
  have hpRow : ∀ i, ∑ o, (p i).w o = 1 := fun i => (p i).sum_one
  have hQRow : ∀ i, ∑ o, Qm (i, o) = 1 := by
    intro i
    calc
      ∑ o, Qm (i, o) = ∑ x, Q.w x := by
        simp [Qm, FinLaw.pr, Finset.sum_comm]
      _ = 1 := Q.sum_one
  have hpriceP : targetMarginalPrice (fun i o => (p i).w o) c = ∑ i, mean i := by
    simp [targetMarginalPrice, mean, Fintype.sum_prod_type]
  have hmeanQ : (∑ io : I × O, mean io.1 * Qm io) = ∑ i, mean i := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ i, ∑ o, mean i * Qm (i, o) =
          ∑ i, mean i * (∑ o, Qm (i, o)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ i, mean i := by simp [hQRow]
  have hpriceQ : assignmentMarginalPrice Q c =
      (∑ io : I × O, center io * Qm io) + ∑ i, mean i := by
    calc
      assignmentMarginalPrice Q c = ∑ io : I × O, c io * Qm io := by
        simp [assignmentMarginalPrice, assignmentMarginalVector, Qm]
      _ = ∑ io : I × O, (center io + mean io.1) * Qm io := by
        apply Finset.sum_congr rfl
        intro io hio
        simp [center, centeredPrice, mean]
      _ = (∑ io : I × O, center io * Qm io) +
          ∑ io : I × O, mean io.1 * Qm io := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro io hio
        ring
      _ = (∑ io : I × O, center io * Qm io) + ∑ i, mean i := by rw [hmeanQ]
  have hLnonneg : 0 ≤ ∑ io : I × O, |center io| * pm io :=
    Finset.sum_nonneg fun io _ => mul_nonneg (abs_nonneg _) ((p io.1).nonneg _)
  have hqLe : ∑ io : I × O, |center io| * qm io ≤
      2 * ∑ io : I × O, |center io| * pm io := by
    calc
      ∑ io : I × O, |center io| * qm io ≤
          ∑ io : I × O, |center io| * (2 * pm io) :=
        Finset.sum_le_sum fun io _ => mul_le_mul_of_nonneg_left
          (hupper io.1 io.2) (abs_nonneg _)
      _ = 2 * ∑ io : I × O, |center io| * pm io := by
        calc
          ∑ io : I × O, |center io| * (2 * pm io) =
              ∑ io : I × O, 2 * (|center io| * pm io) := by
            apply Finset.sum_congr rfl
            intro io hio
            ring
          _ = 2 * ∑ io : I × O, |center io| * pm io := (Finset.mul_sum _ _ _).symm
  have herr : |∑ io : I × O, center io * (Qm io - qm io)| ≤
      η * ∑ io : I × O, |center io| * qm io := by
    calc
      |∑ io : I × O, center io * (Qm io - qm io)| ≤
          ∑ io : I × O, |center io * (Qm io - qm io)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ io : I × O, |center io| * (η * qm io) :=
        Finset.sum_le_sum fun io _ => by
          have hdiff := hrelative io.1 io.2
          have hqnon : 0 ≤ qm io := (q io.1).nonneg io.2
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
      _ = η * ∑ io : I × O, |center io| * qm io := by
        calc
          ∑ io : I × O, |center io| * (η * qm io) =
              ∑ io : I × O, η * (|center io| * qm io) := by
            apply Finset.sum_congr rfl
            intro io hio
            ring
          _ = η * ∑ io : I × O, |center io| * qm io := (Finset.mul_sum _ _ _).symm
  have herrorLower : - (2 * η * ∑ io : I × O, |center io| * pm io) ≤
      ∑ io : I × O, center io * (Qm io - qm io) := by
    have hscale : η * ∑ io : I × O, |center io| * qm io ≤
        2 * η * ∑ io : I × O, |center io| * pm io := by
      calc
        η * ∑ io : I × O, |center io| * qm io ≤
            η * (2 * ∑ io : I × O, |center io| * pm io) :=
          mul_le_mul_of_nonneg_left hqLe hη
        _ = 2 * η * ∑ io : I × O, |center io| * pm io := by ring
    have herrLower' := (abs_le.mp herr).1
    linarith
  have hsplit : (∑ io : I × O, center io * Qm io) =
      (∑ io : I × O, center io * qm io) +
        ∑ io : I × O, center io * (Qm io - qm io) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro io hio
    ring
  have hhalf : 2 * η ≤ ρ / 2 := by linarith [hgap]
  have hcenterQ : 0 ≤ ∑ io : I × O, center io * Qm io := by
    rw [hsplit]
    calc
      (∑ io : I × O, center io * qm io) +
          ∑ io : I × O, center io * (Qm io - qm io) ≥
        ρ / 2 * ∑ io : I × O, |center io| * pm io -
          2 * η * ∑ io : I × O, |center io| * pm io :=
        add_le_add hgain herrorLower
      _ ≥ 0 := by nlinarith [hLnonneg, hhalf]
  rw [hpriceP, hpriceQ]
  linarith

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
  classical
  let X := Group → Bin
  let J := Finset Group × X
  let event : J → X → Prop := fun j a => ∀ g ∈ j.1, a g = j.2 g
  let bound : J → ℝ := fun j =>
    Real.exp (Real.rpow (P.d : ℝ) (-0.05) * j.1.card) *
      ∏ g ∈ j.1, (P.target g).w (j.2 g)
  let G := Lane_q_s16_calib.feasibleWeights P.safe event bound
  let image := Lane_q_s16_calib.weightMarginalImage G
  have hcv := Lane_q_s16_calib.feasibleWeights_weightMarginalImage_compact_convex
    P.safe event bound
  have hprSum (Q : FinLaw X) (A : X → Prop) :
      Q.pr A = Lane_q_s16_calib.eventWeightSum A Q.w := by
    simp [FinLaw.pr, Lane_q_s16_calib.eventWeightSum, Finset.sum_filter]
  have hImage : P.image = image := by
    ext v
    constructor
    · rintro ⟨Q, hQ, hv⟩
      change P.feasible Q at hQ
      rcases hQ with ⟨hsafe, hjoint⟩
      refine ⟨Q.w, ?_, ?_⟩
      · refine ⟨Q.nonneg, Q.sum_one, ?_, ?_⟩
        · intro a
          by_contra hzero
          exact a.2 (hsafe a.1 hzero)
        · intro j
          have hj := hjoint j.1 j.2
          change Q.pr (event j) ≤ bound j at hj
          rw [hprSum Q (event j)] at hj
          exact hj
      · intro g b
        calc
          v (g, b) = assignmentMarginalVector Q (g, b) := hv g b
          _ = Q.pr (fun a => a g = b) := rfl
          _ = Lane_q_s16_calib.eventWeightSum (fun a : X => a g = b) Q.w :=
            hprSum Q _
          _ = Lane_q_s16_calib.eventWeightSum (fun a : Group → Bin => a g = b) Q.w := rfl
    · rintro ⟨w, hw, hv⟩
      let Q : FinLaw X := ⟨w, hw.1, hw.2.1⟩
      refine ⟨Q, ?_, ?_⟩
      · constructor
        · intro a ha
          by_contra hnot
          have hwzero := hw.2.2.1 ⟨a, hnot⟩
          exact ha (by simpa [Q] using hwzero)
        · intro S a
          have hupper := hw.2.2.2 (S, a)
          have hupper' : Lane_q_s16_calib.eventWeightSum
              (fun x : X => ∀ g ∈ S, x g = a g) w ≤
                Real.exp (Real.rpow (P.d : ℝ) (-0.05) * S.card) *
                  ∏ g ∈ S, (P.target g).w (a g) := by
            simpa [event, bound] using hupper
          rw [hprSum Q (fun x : X => ∀ g ∈ S, x g = a g)]
          simpa [Q] using hupper'
      · intro g b
        calc
          v (g, b) = Lane_q_s16_calib.eventWeightSum (fun a : X => a g = b) w := hv g b
          _ = Q.pr (fun a => a g = b) := by
            simpa [Q] using (hprSum Q (fun a : X => a g = b)).symm
          _ = assignmentMarginalVector Q (g, b) := rfl
  rw [hImage]
  exact hcv

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
  classical
  have hdpos : 0 < P.d := lt_of_lt_of_le hκ.d0_pos hd
  let R : Block → Type := fun b => {r : Role // P.blockOf r = b}
  let e : ∀ b, {y : Label // y ∈ P.blockLabels b} ≃ Fin P.d :=
    fun b => Finset.equivFinOfCardEq (P.block_card b)
  let encode : ∀ b, Label → Fin P.d := fun b y =>
    if hy : y ∈ P.blockLabels b then e b ⟨y, hy⟩ else ⟨0, hdpos⟩
  have hencode : ∀ b y hy, encode b y = e b ⟨y, hy⟩ := by
    intro b y hy
    simp [encode, hy]
  let qFin : ∀ b, R b → FinLaw (Fin P.d) := fun b r =>
    FinLaw.map (q r.1) (encode b)
  have hmapWeight : ∀ b (r : R b) z,
      (qFin b r).w z = (q r.1).w ((e b).symm z).1 := by
    intro b r z
    let y := (e b).symm z
    have h := Lane_q_s16_calib.finLaw_map_weight_supported
      (q r.1) (fun y : Label => y ∈ P.blockLabels b) (e b) (encode b)
      (by intro y hy; exact hencode b y hy)
      (by intro y hy; simpa [r.2] using hsupport r.1 y hy)
      (e b).injective
    simpa [qFin, y] using h y
  have hAtomFin : ∀ b (r : R b) z,
      (qFin b r).w z ≤ Real.rpow (P.d : ℝ) (-0.95) := by
    intro b r z
    rw [hmapWeight]
    exact hatom r.1 ((e b).symm z).1
  have hloadFin : ∀ b z, ∑ r : R b, (qFin b r).w z ≤ 0.4 := by
    intro b z
    let y := (e b).symm z
    have hsubtypeSum (f : Role → ℝ) :
        (∑ r : R b, f r.1) =
          ∑ r ∈ Finset.univ.filter (fun r : Role => P.blockOf r = b), f r := by
      simpa [R] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset Role))
          (p := fun r : Role => P.blockOf r = b) (f := f))
    calc
      ∑ r : R b, (qFin b r).w z =
          ∑ r : R b, (q r.1).w y.1 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hmapWeight]
      _ = ∑ r ∈ Finset.univ.filter (fun r : Role => P.blockOf r = b),
            (q r).w y.1 := by
          simpa [y] using hsubtypeSum (fun r => (q r).w y.1)
      _ ≤ ∑ r, (q r).w y.1 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro r hr hnot
        exact (q r).nonneg y.1
      _ ≤ 0.4 := hload y.1
  have hprovider : ∀ b, ∃ Q : FinLaw (R b → Fin P.d),
      (∀ x, Q.w x ≠ 0 → Function.Injective x) ∧
      (∀ r z, Q.pr (fun x => x r = z) = (qFin b r).w z) ∧
      ∀ (S : Finset (R b)) (z : R b → Fin P.d),
        (S.card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025 →
        Q.pr (fun x => ∀ r ∈ S, x r = z r) ≤
          Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (qFin b r).w (z r) := by
    intro b
    exact provider P.d hd (qFin b) (hAtomFin b) (hloadFin b)
  choose Q hQinj hQmarg hQjoint using hprovider
  let decode : ∀ b, (R b → Fin P.d) → P.BlockState b := fun b z r =>
    (e b).symm (z r)
  let laws : ∀ b, FinLaw (P.BlockState b) := fun b => FinLaw.map (Q b) (decode b)
  have hlocalMapWeight : ∀ b (r : R b) z,
      (qFin b r).w z = (q r.1).w ((e b).symm z).1 := hmapWeight
  have hreadoutBlock (ω : P.SeedState) (r : Role) (b : Block)
      (hb : P.blockOf r = b) : P.readout ω r = (ω b ⟨r, hb⟩).1 := by
    cases hb
    rfl
  refine ⟨⟨laws, ?_, ?_, ?_⟩⟩
  · intro b ω hω r r' hrr'
    obtain ⟨z, hdecode, hz⟩ := Lane_q_s16_calib.finLaw_map_support (Q b) (decode b) ω hω
    have hFin : z r = z r' := by
      have h' := congrArg (e b) (congrArg (fun st : P.BlockState b => st r) hdecode)
      have h'' := congrArg (e b) (congrArg (fun st : P.BlockState b => st r') hdecode)
      have hval : (ω r).1 = (ω r').1 := congrArg Subtype.val hrr'
      have hω : ω r = ω r' := Subtype.ext hval
      calc
        z r = e b (ω r) := by simpa [decode] using h'
        _ = e b (ω r') := by rw [hω]
        _ = z r' := by simpa [decode] using h''.symm
    exact hQinj b z hz hFin
  · intro r y
    let b := P.blockOf r
    let rb : R b := ⟨r, rfl⟩
    by_cases hy : y ∈ P.blockLabels b
    · have hblockMarg : (FinLaw.pi laws).pr (fun ω => P.readout ω r = y) =
          (laws b).pr (fun st => (st rb).1 = y) := by
        exact Lane_q_s16_calib.finLaw_pi_pr_coordinate laws b
          (fun st => (st rb).1 = y)
      have hmapMarg : (laws b).pr (fun st => (st rb).1 = y) =
          (Q b).pr (fun z => z rb = e b ⟨y, hy⟩) := by
        dsimp [laws]
        rw [Lane_q_s16_calib.finLaw_map_pr]
        have hevent : (fun z : R b → Fin P.d => (decode b z rb).1 = y) =
            (fun z => z rb = e b ⟨y, hy⟩) := by
          funext z
          apply propext
          constructor
          · intro h
            have hsub : (e b).symm (z rb) = ⟨y, hy⟩ := Subtype.ext h
            simpa using congrArg (e b) hsub
          · intro h
            have hsub := congrArg (e b).symm h
            simpa using congrArg Subtype.val hsub
        rw [hevent]
      calc
        (FinLaw.pi laws).pr (fun ω => P.readout ω r = y) =
            (laws b).pr (fun st => (st rb).1 = y) := hblockMarg
        _ = (Q b).pr (fun z => z rb = e b ⟨y, hy⟩) := hmapMarg
        _ = (qFin b rb).w (e b ⟨y, hy⟩) := hQmarg b rb _
        _ = (q r).w y := by
          rw [hlocalMapWeight]
          simp [rb, b]
    · have htargetZero : (q r).w y = 0 := by
        by_contra hne
        exact hy (hsupport r y hne)
      have hblockMarg : (FinLaw.pi laws).pr (fun ω => P.readout ω r = y) = 0 := by
        have hcoord := Lane_q_s16_calib.finLaw_pi_pr_coordinate laws b
          (fun st => (st rb).1 = y)
        have hfalse : ∀ st : P.BlockState b, ¬ ((st rb).1 = y) := by
          intro st heq
          exact hy (by rw [← heq]; exact (st rb).2)
        calc
          (FinLaw.pi laws).pr (fun ω => P.readout ω r = y) =
              (laws b).pr (fun st => (st rb).1 = y) := hcoord
          _ = 0 := by
            unfold FinLaw.pr
            apply Finset.sum_eq_zero
            intro st hst
            rw [if_neg (hfalse st)]
      simpa [htargetZero] using hblockMarg
  · intro S y hS
    let lift : ∀ b, {r : Role // r ∈ S.filter (fun g => P.blockOf g = b)} ↪ R b :=
      fun b => {
        toFun := fun r => ⟨r.1, (Finset.mem_filter.mp r.2).2⟩
        inj' := by
          intro r r' h
          have hv : r.1 = r'.1 := congrArg (fun x : R b => x.1) h
          exact Subtype.ext hv }
    let T : ∀ b, Finset (R b) := fun b =>
      (S.filter (fun r => P.blockOf r = b)).attach.map (lift b)
    have hTcard (b : Block) : (T b).card = (S.filter (fun r => P.blockOf r = b)).card := by
      simp [T]
    have hTsmall (b : Block) : ((T b).card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025 := by
      rw [hTcard]
      exact hS b
    let yFin : ∀ b, R b → Fin P.d := fun b r => encode b (y r.1)
    let localEvent : ∀ b, P.BlockState b → Prop := fun b st =>
      ∀ r ∈ T b, (st r).1 = y r.1
    let globalEvent : (∀ b, P.BlockState b) → Prop := fun ω =>
      ∀ r ∈ S, P.readout ω r = y r
    have hfactorEvent : ∀ ω, globalEvent ω ↔ ∀ b, localEvent b (ω b) := by
      intro ω
      constructor
      · intro hall b r hr
        have hmem : r.1 ∈ S.filter (fun g => P.blockOf g = b) := by
          rcases Finset.mem_map.mp hr with ⟨r0, hr0, heq⟩
          have hval : r.1 = r0.1 := (congrArg Subtype.val heq).symm
          rw [hval]
          exact r0.2
        have hrole : r.1 ∈ S := (Finset.mem_filter.mp hmem).1
        have hblock : P.blockOf r.1 = b := (Finset.mem_filter.mp hmem).2
        have hread := hreadoutBlock ω r.1 b hblock
        calc
          (ω b r).1 = P.readout ω r.1 := hread.symm
          _ = y r.1 := hall r.1 hrole
      · intro hall r hr
        let b := P.blockOf r
        let rb : R b := ⟨r, rfl⟩
        have hrfilter : r ∈ S.filter (fun g => P.blockOf g = b) :=
          Finset.mem_filter.mpr ⟨hr, rfl⟩
        have hrmap : rb ∈ T b := by
          apply Finset.mem_map.mpr
          refine ⟨⟨r, hrfilter⟩, Finset.mem_attach _ _, ?_⟩
          apply Subtype.ext
          rfl
        simpa [globalEvent, localEvent, RoleLabelProblem.readout, b, rb] using
          hall b rb hrmap
    have hprobFactor :
        (FinLaw.pi laws).pr globalEvent = ∏ b, (laws b).pr (localEvent b) := by
      rw [show globalEvent = (fun ω => ∀ b, localEvent b (ω b)) by
        funext ω
        exact propext (hfactorEvent ω)]
      exact Lane_q_s16_calib.finLaw_pi_pr_forall laws localEvent
    have hlocalBound (b : Block) :
        (laws b).pr (localEvent b) ≤
          Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) *
            ∏ r ∈ T b, (q r.1).w (y r.1) := by
      by_cases hall : ∀ r ∈ T b, y r.1 ∈ P.blockLabels b
      · have hmapEvent : (laws b).pr (localEvent b) =
            (Q b).pr (fun z => ∀ r ∈ T b, z r = yFin b r) := by
          dsimp [laws]
          rw [Lane_q_s16_calib.finLaw_map_pr]
          have hevent : (fun z : R b → Fin P.d =>
              ∀ r ∈ T b, (decode b z r).1 = y r.1) =
                (fun z => ∀ r ∈ T b, z r = yFin b r) := by
            funext z
            apply propext
            constructor
            · intro hz r hr
              have hsub : (e b).symm (z r) = ⟨y r.1, hall r hr⟩ :=
                Subtype.ext (hz r hr)
              simpa [yFin, encode, hall r hr] using congrArg (e b) hsub
            · intro hz r hr
              have hsub := congrArg (e b).symm (hz r hr)
              simpa [decode, yFin, encode, hall r hr] using congrArg Subtype.val hsub
          rw [hevent]
        have hq := hQjoint b (T b) (yFin b) (hTsmall b)
        rw [hmapEvent]
        calc
          (Q b).pr (fun z => ∀ r ∈ T b, z r = yFin b r) ≤
              Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) *
                ∏ r ∈ T b, (qFin b r).w (yFin b r) := hq
          _ = Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) *
                ∏ r ∈ T b, (q r.1).w (y r.1) := by
            congr 1
            apply Finset.prod_congr rfl
            intro r hr
            rw [hmapWeight]
            simp [yFin, encode, hall r hr]
      · push_neg at hall
        obtain ⟨r, hr, hnot⟩ := hall
        have hprobZero : (laws b).pr (localEvent b) = 0 := by
          unfold FinLaw.pr localEvent
          apply Finset.sum_eq_zero
          intro st hst
          have hfalse : ¬ (∀ r ∈ T b, (st r).1 = y r.1) := by
            intro h
            exact hnot (by rw [← h r hr]; exact (st r).2)
          simp [hfalse]
        have htargetZero : (q r.1).w (y r.1) = 0 := by
          by_contra hne
          exact hnot (by simpa [r.2] using hsupport r.1 (y r.1) hne)
        have hprodZero : (∏ r ∈ T b, (q r.1).w (y r.1)) = 0 :=
          Finset.prod_eq_zero hr htargetZero
        simp [hprobZero, hprodZero]
    have hglobalNonneg : ∀ b, 0 ≤ (laws b).pr (localEvent b) := by
      intro b
      exact Finset.sum_nonneg fun st _ => by
        split_ifs
        · exact (laws b).nonneg st
        · exact le_rfl
    have hprodBound :
        ∏ b : Block, (laws b).pr (localEvent b) ≤
          ∏ b : Block,
            (Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) *
              ∏ r ∈ T b, (q r.1).w (y r.1)) :=
      Finset.prod_le_prod₀ (fun b hb => hglobalNonneg b)
        (fun b hb => hlocalBound b)
    have hcardSum : ∑ b : Block, (T b).card = S.card := by
      calc
        ∑ b : Block, (T b).card =
            ∑ b : Block, (S.filter (fun r => P.blockOf r = b)).card := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hTcard b
        _ = S.card := by
          simpa using (Finset.sum_card_fiberwise_eq_card_filter S
            (Finset.univ : Finset Block) P.blockOf)
    have hcardSumR :
        ∑ b : Block, ((T b).card : ℝ) = (S.card : ℝ) := by
      exact_mod_cast hcardSum
    have hprodQueries :
        ∏ b : Block, (∏ r ∈ T b, (q r.1).w (y r.1)) =
          ∏ r ∈ S, (q r).w (y r) := by
      have hTprod (b : Block) :
          (∏ r ∈ T b, (q r.1).w (y r.1)) =
            ∏ r ∈ S with P.blockOf r = b, (q r).w (y r) := by
        dsimp only [T]
        rw [Finset.prod_map]
        change (∏ r ∈ (S.filter (fun g => P.blockOf g = b)).attach,
            (q r.1).w (y r.1)) =
          ∏ r ∈ S with P.blockOf r = b, (q r).w (y r)
        exact Finset.prod_attach (S.filter (fun g => P.blockOf g = b))
          (fun g : Role => (q g).w (y g))
      calc
        ∏ b : Block, (∏ r ∈ T b, (q r.1).w (y r.1)) =
            ∏ b : Block, (∏ r ∈ S with P.blockOf r = b, (q r).w (y r)) := by
          apply Finset.prod_congr rfl
          intro b hb
          exact hTprod b
        _ = ∏ r ∈ S with P.blockOf r ∈ (Finset.univ : Finset Block),
              (q r).w (y r) := by
          exact Finset.prod_fiberwise_eq_prod_filter S Finset.univ P.blockOf
            (fun r => (q r).w (y r))
        _ = ∏ r ∈ S, (q r).w (y r) := by simp
    have hexp : ∏ b : Block,
        Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) =
          Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.mul_sum, hcardSumR]
    have hprodFinal :
        ∏ b : Block,
          (Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) *
            ∏ r ∈ T b, (q r.1).w (y r.1)) =
          Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (q r).w (y r) := by
      rw [Finset.prod_mul_distrib, hexp, hprodQueries]
    calc
      (FinLaw.pi laws).pr globalEvent = ∏ b, (laws b).pr (localEvent b) := hprobFactor
      _ ≤ ∏ b,
          (Real.exp (Real.rpow (P.d : ℝ) (-0.04) * (T b).card) *
            ∏ r ∈ T b, (q r.1).w (y r.1)) := hprodBound
      _ = Real.exp (Real.rpow (P.d : ℝ) (-0.04) * S.card) *
            ∏ r ∈ S, (q r).w (y r) := hprodFinal

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
  classical
  let ρ := Real.rpow (P.d : ℝ) (-0.02)
  have hdreal : 0 < (P.d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hP.d_pos)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact Real.rpow_pos_of_pos hdreal _
  have hρle : ρ ≤ 1 / 3 := hP.cluster_range hc
  have hden : 0 < 1 - ρ := by linarith
  have hfactor : (1 + ρ) / (1 - ρ) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hsupport : ∀ r y, (q r).w y ≠ 0 → y ∈ P.blockLabels (P.blockOf r) := by
    intro r y hqy
    have htarget : (P.target r).w y ≠ 0 := by
      intro hzero
      have hupper := (hq r y).2
      rw [hzero] at hupper
      have hqnon := (q r).nonneg y
      exact hqy (le_antisymm (by simpa using hupper) hqnon)
    exact P.target_support r y htarget
  have hatom : ∀ r y, (q r).w y ≤ Real.rpow (P.d : ℝ) (-0.95) := by
    intro r y
    calc
      (q r).w y ≤ (1 + ρ) / (1 - ρ) * (P.target r).w y := (hq r y).2
      _ ≤ 2 * (P.target r).w y :=
        mul_le_mul_of_nonneg_right hfactor ((P.target r).nonneg y)
      _ ≤ Real.rpow (P.d : ℝ) (-0.95) := hP.robust_atoms hc r y
  have hload : ∀ y, ∑ r, (q r).w y ≤ 0.4 := by
    intro y
    calc
      ∑ r, (q r).w y ≤ ∑ r, 2 * (P.target r).w y :=
        Finset.sum_le_sum fun r hr => by
          calc
            (q r).w y ≤ (1 + ρ) / (1 - ρ) * (P.target r).w y := (hq r y).2
            _ ≤ 2 * (P.target r).w y :=
              mul_le_mul_of_nonneg_right hfactor ((P.target r).nonneg y)
      _ = 2 * ∑ r, (P.target r).w y := by rw [Finset.mul_sum]
      _ ≤ 2 * (1 / 5) :=
        mul_le_mul_of_nonneg_left (by
          have hcol := hP.cluster_columns hc y
          norm_num at hcol
          exact hcol) (by norm_num)
      _ = 0.4 := by norm_num
  exact ⟨hsupport, hatom, hload⟩

/-- Direct-mode calibration is just the block seed, with no internal tests. -/
theorem direct_role_seed_feasible {κ : CConsts} (hκ : κ.Admissible)
    {Role Label Star Block : Type} [Fintype Role] [DecidableEq Role]
    [Fintype Label] [DecidableEq Label] [Fintype Star] [Fintype Block] [DecidableEq Block]
    (P : RoleLabelProblem Role Label Star Block) (hP : RoleLabelHypotheses hκ P)
    (hd : P.regime = .direct) (seed : RoleBlockSeed P P.target) :
    P.feasible (FinLaw.map (FinLaw.pi seed.laws) P.readout) ∧
      ∀ r y, (FinLaw.map (FinLaw.pi seed.laws) P.readout).pr (fun x => x r = y) = (P.target r).w y := by
  classical
  let base := FinLaw.pi seed.laws
  let Q := FinLaw.map base P.readout
  let R : Block → Type := fun b => {r : Role // P.blockOf r = b}
  have hreadoutBlock (ω : P.SeedState) (r : Role) (b : Block)
      (hb : P.blockOf r = b) : P.readout ω r = (ω b ⟨r, hb⟩).1 := by
    cases hb
    rfl
  have hreadoutInjective : ∀ ω, base.w ω ≠ 0 → Function.Injective (P.readout ω) := by
    intro ω hω r r' hrr'
    have hblock : P.blockOf r = P.blockOf r' := by
      by_contra hne
      have hrmem : P.readout ω r ∈ P.blockLabels (P.blockOf r) := by
        simp [RoleLabelProblem.readout]
      have hr'mem : P.readout ω r' ∈ P.blockLabels (P.blockOf r') := by
        simp [RoleLabelProblem.readout]
      have hdisj := P.blocks_disjoint (P.blockOf r) (P.blockOf r') hne
      have hnot : P.readout ω r ∉ P.blockLabels (P.blockOf r') :=
        (Finset.disjoint_left.mp hdisj) hrmem
      exact hnot (by simpa [hrr'] using hr'mem)
    obtain ⟨b, hbr, hbr'⟩ : ∃ b : Block, P.blockOf r = b ∧ P.blockOf r' = b :=
      ⟨P.blockOf r, rfl, hblock.symm⟩
    have hcoord := Lane_q_s16_calib.finLaw_pi_support seed.laws ω hω b
    have hinj := seed.injective b (ω b) hcoord
    let sr : R b := ⟨r, hbr⟩
    let sr' : R b := ⟨r', hbr'⟩
    have hval : (ω b sr).1 = (ω b sr').1 := by
      calc
        (ω b sr).1 = P.readout ω r := (hreadoutBlock ω r b hbr).symm
        _ = P.readout ω r' := hrr'
        _ = (ω b sr').1 := hreadoutBlock ω r' b hbr'
    have hstate : ω b sr = ω b sr' := Subtype.ext hval
    have hrole := hinj hstate
    exact congrArg Subtype.val hrole
  have hqueries (S : Finset Role) (y : Role → Label) (hS : P.queries S) :
      Q.pr (fun x => ∀ r ∈ S, x r = y r) ≤
        Real.exp (P.rate * S.card) * ∏ r ∈ S, (P.target r).w (y r) := by
    have hcard : (S.card : ℝ) ≤ Real.rpow (P.d : ℝ) 0.025 := by
      simpa [RoleLabelProblem.queries, hd] using hS
    have hsmall : ∀ b, ((S.filter fun r => P.blockOf r = b).card : ℝ) ≤
        Real.rpow (P.d : ℝ) 0.025 := by
      intro b
      calc
        ((S.filter fun r => P.blockOf r = b).card : ℝ) ≤ (S.card : ℝ) := by
          exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _))
        _ ≤ Real.rpow (P.d : ℝ) 0.025 := hcard
    have hj := seed.joint S y hsmall
    rw [Lane_q_s16_calib.finLaw_map_pr]
    simpa [Q, base, RoleLabelProblem.rate, hd] using hj
  have hfeasible : P.feasible Q := by
    constructor
    · intro x hx
      obtain ⟨ω, hread, hω⟩ := Lane_q_s16_calib.finLaw_map_support base P.readout x hx
      refine ⟨?_, ?_⟩
      · intro r r' hrr
        apply hreadoutInjective ω hω
        simpa [hread] using hrr
      intro s
      simpa [hread] using hP.direct_no_tests hd s (P.readout ω)
    · intro S y hS
      exact hqueries S y hS
  refine ⟨hfeasible, ?_⟩
  intro r y
  rw [Lane_q_s16_calib.finLaw_map_pr]
  exact seed.marginal r y

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
  classical
  let X := Role → Label
  let J := {S : Finset Role // P.queries S} × X
  let event : J → X → Prop := fun j x => ∀ r ∈ j.1.1, x r = j.2 r
  let bound : J → ℝ := fun j =>
    Real.exp (P.rate * j.1.1.card) * ∏ r ∈ j.1.1, (P.target r).w (j.2 r)
  let G := Lane_q_s16_calib.feasibleWeights P.safe event bound
  let image := Lane_q_s16_calib.weightMarginalImage G
  have hcv := Lane_q_s16_calib.feasibleWeights_weightMarginalImage_compact_convex
    P.safe event bound
  have hprSum (Q : FinLaw X) (A : X → Prop) :
      Q.pr A = Lane_q_s16_calib.eventWeightSum A Q.w := by
    simp [FinLaw.pr, Lane_q_s16_calib.eventWeightSum, Finset.sum_filter]
  have hImage : P.image = image := by
    ext v
    constructor
    · rintro ⟨Q, hQ, hv⟩
      change P.feasible Q at hQ
      rcases hQ with ⟨hsafe, hjoint⟩
      refine ⟨Q.w, ?_, ?_⟩
      · refine ⟨Q.nonneg, Q.sum_one, ?_, ?_⟩
        · intro x
          by_contra hzero
          exact x.2 (hsafe x.1 hzero)
        · intro j
          have hj := hjoint j.1.1 j.2 j.1.2
          change Q.pr (event j) ≤ bound j at hj
          rw [hprSum Q (event j)] at hj
          exact hj
      · intro r y
        calc
          v (r, y) = assignmentMarginalVector Q (r, y) := hv r y
          _ = Q.pr (fun x => x r = y) := rfl
          _ = Lane_q_s16_calib.eventWeightSum (fun x : X => x r = y) Q.w :=
            hprSum Q _
          _ = Lane_q_s16_calib.eventWeightSum (fun x : Role → Label => x r = y) Q.w := rfl
    · rintro ⟨w, hw, hv⟩
      let Q : FinLaw X := ⟨w, hw.1, hw.2.1⟩
      refine ⟨Q, ?_, ?_⟩
      · constructor
        · intro x hx
          by_contra hnot
          have hwzero := hw.2.2.1 ⟨x, hnot⟩
          exact hx (by simpa [Q] using hwzero)
        · intro S y hS
          have hupper := hw.2.2.2 (⟨⟨S, hS⟩, y⟩)
          have hupper' : Lane_q_s16_calib.eventWeightSum
              (fun x : X => ∀ r ∈ S, x r = y r) w ≤
                Real.exp (P.rate * S.card) * ∏ r ∈ S, (P.target r).w (y r) := by
            simpa [event, bound] using hupper
          rw [hprSum Q (fun x : X => ∀ r ∈ S, x r = y r)]
          simpa [Q] using hupper'
      · intro r y
        calc
          v (r, y) = Lane_q_s16_calib.eventWeightSum (fun x : X => x r = y) w := hv r y
          _ = Q.pr (fun x => x r = y) := by
            simpa [Q] using (hprSum Q (fun x : X => x r = y)).symm
          _ = assignmentMarginalVector Q (r, y) := rfl
  rw [hImage]
  exact hcv

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
