import HypercubeRamsey.PartC.Core
import HypercubeRamsey.S03.NearProductInjection

/-!
# Part C constant bundle

`QCond` records the fixed-threshold inequalities used by Sections 13–18.
The auxiliary constants `c5`, `c14`, `h0`, `d0`, and `cChernoff` stand for
the fixed outputs of the cited estimates. A node may use such a constant as
"the" constant of its estimate only if `Admissible` ties it to that estimate:
`c5` is bounded by an explicit absolute value (`c5_le`), `d0` carries the L3.9
contract (`nearProduct`), and the clock constants carry the L3.10 contract
(`clock`). `c14` and `h0` (L3.8 at the Section 14 exponents) and `cChernoff`
(P15.3b) are not yet tied: the node producing each must add the bound it needs
(an upper bound for `c14`, `cChernoff`; a lower bound for `h0`) before a
statement may read them as that estimate's constant.
-/

namespace HypercubeRamsey

open Filter
open scoped BigOperators

/-- L12.5: conflict-count exponent from the centered-moment argument. -/
noncomputable def Cstar (u : ℕ) (ξ : ℝ) : ℝ :=
  2 * ((⌊(4 : ℝ) ^ (u + 3) / ξ ^ 2⌋₊ : ℝ) + 1) + u + 1

/-- Binary entropy, with its continuous endpoint values. -/
noncomputable def binEntropy (x : ℝ) : ℝ :=
  if x = 0 then 0 else if x = 1 then 0 else -x * Real.log x - (1 - x) * Real.log (1 - x)

/-- F-CConsts: L3.10 sampler contract at scope exponent `B`, label-range constant `Cg` and integer
exponents `A`, `P`.

It records the hypotheses and the two outputs consumed by Part C (injectivity plus avoidance, and an
upper cylinder comparison with a vanishing error) in exactly the quantifier order of Part A's
`clock_sampling`, where the exponents may depend on `Cg`; `Cg` is therefore fixed here, not
universally quantified. Part C applies the lemma only with `log g ≤ 2 n` (`g = N ≤ n 2^n` with the
cube dimension as size parameter in L15.1d and P15.3, and `g ≤ N` with `n_clock = ⌊exp n^{δ'}⌋` in
P18.4b). `A` and `P` may be rounded upward from the real exponents returned by the framework theorem. -/
def ClockConstants (B Cg : ℝ) (A P : ℕ) (θ0 : ℝ) : Prop :=
  1 ≤ B ∧ θ0 = 1e-8 ∧
  ∃ A' P' : ℝ, ∃ n₀ : ℕ, ∃ ε : ℕ → ℝ,
    0 < A' ∧ 0 < P' ∧ A' ≤ A ∧ P' ≤ P ∧ 1 ≤ n₀ ∧
    Tendsto ε atTop (nhds 0) ∧
    ∀ n ≥ n₀, ∀ g : ℕ, Real.log g ≤ Cg * n →
      ∀ {R K : Type} [Fintype R] [DecidableEq R] [Fintype K]
        {Ω : R → Type} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
        (lab : ∀ a, Ω a → Fin g) (laws : ∀ a, FinProb (Ω a))
        (F : K → (∀ a, Ω a) → Prop) (sc : K → Finset R),
        (∀ y, ∑ a, labMarg (laws a) (lab a) y ≤ θ0) →
        (∀ a y, labMarg (laws a) (lab a) y ≤ (n : ℝ) ^ (-A')) →
        (∀ k, FinProb.DependsOn (F k) (sc k)) →
        (∀ k, ((sc k).card : ℝ) ≤ (n : ℝ) ^ B) →
        (∀ a, ((Finset.univ.filter fun k => a ∈ sc k).card : ℝ) ≤ (n : ℝ) ^ B) →
        (∀ k, (FinProb.pi laws).pr (F k) ≤ (n : ℝ) ^ (-P')) →
        ∃ J : FinProb (∀ a, Ω a),
          (∀ ω, J.w ω ≠ 0 → Function.Injective (fun a => lab a (ω a)) ∧
            ∀ k, ¬ F k ω) ∧
          (∀ (S : Finset R) (o : ∀ a, Ω a), ((S.card : ℝ) ≤ (n : ℝ) ^ B) →
            J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤
              (1 + ε n) * ∏ a ∈ S, (laws a).w (o a))

/-- F-CConsts: L3.9 contract. `d0` is a valid threshold for Part A's `near_product_injection`
(the same statement, for every bin size `d ≥ d0`). -/
def NearProductConstants (d0 : ℕ) : Prop :=
  ∀ d ≥ d0, ∀ {R : Type} [Fintype R] [DecidableEq R]
    {Ω : R → Type} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (lab : ∀ i, Ω i → Fin d) (p : ∀ i, FinProb (Ω i)),
    (∀ i y, labMarg (p i) (lab i) y ≤ (d : ℝ) ^ (-(0.95 : ℝ))) →
    (∀ y, ∑ i, labMarg (p i) (lab i) y ≤ 0.4) →
    ∃ J : FinProb (∀ i, Ω i),
      (∀ ω, J.w ω ≠ 0 → Function.Injective (fun i => lab i (ω i))) ∧
      (∀ i o, J.pr (fun ω => ω i = o) = (p i).w o) ∧
      (∀ (S : Finset R) (o : ∀ i, Ω i), (S.card : ℝ) ≤ (d : ℝ) ^ (0.025 : ℝ) →
        J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
          Real.exp ((d : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ i ∈ S, (p i).w (o i))

/-- Dyadic scale predicate used in the extraction and clique interfaces. -/
def IsDyadic (b : ℕ) : Prop := ∃ j : ℕ, b = 2 ^ j

/-- Constants shared by the definitions and the proof nodes of Sections 12–18. -/
structure CConsts where
  η0 : ℝ
  xs : ℝ
  α : ℝ
  ι : ℝ
  xι : ℝ
  αι : ℝ
  Ac : ℕ
  P : ℕ
  R : ℕ
  L : ℕ
  u : ℕ
  ξ : ℝ
  θ : ℝ
  Astar : ℕ
  Pstar : ℕ
  θ0 : ℝ
  aC : ℝ
  aB : ℝ
  M1 : ℝ
  Cb : ℝ
  Mlo : ℕ
  Mhi : ℕ
  cq : ℝ
  ω : ℝ
  a : ℝ
  ρ : ℝ
  KB : ℝ
  A0 : ℝ
  Q0 : ℝ
  Kbd : ℝ
  Qbd : ℕ
  θstar : ℝ
  Kp : ℕ
  cp : ℝ
  Kcell : ℝ
  cperm : ℝ
  β : ℝ
  c5 : ℝ
  c14 : ℝ
  cChernoff : ℝ
  h0 : ℕ
  d0 : ℕ

/-- Slice-scale helpers used in `QCond`. -/
noncomputable def sliceK (κ : CConsts) (h : ℕ) : ℕ :=
  ⌈Real.rpow (h : ℝ) (3 * κ.ω)⌉₊

/-- Height-round helper used in `QCond`. -/
noncomputable def sliceT (κ : CConsts) (h : ℕ) : ℕ :=
  ⌈Real.rpow (h : ℝ) κ.ω⌉₊

/-- Internal-error helper used in `QCond`. -/
noncomputable def sliceEps (κ : CConsts) (h : ℕ) : ℝ :=
  Real.exp (-0.001 * κ.a * (sliceK κ h : ℝ) * h)

/-- Uniform row-mean constant in the S4 estimate (P14.1j). -/
noncomputable def rowMeanConstant (κ : CConsts) : ℝ :=
  (4 * 200 / κ.a) * (3 + 1)

/-- The finite list of large-scale inequalities required at a threshold `q`.

The `h`-dependent conjuncts cover every integer internal dimension in the
specified range; `d` is the bin scale `⌊exp(q/2)⌋`. -/
def QCond (κ : CConsts) (q : ℝ) : Prop :=
  (Real.rpow 2 κ.aB - 1) * Real.rpow (κ.M1 * q) κ.aB ≥ Real.log (800 / (κ.a * (1 / 400 : ℝ))) ∧
  (Real.rpow q κ.aC + 10 ≤ (κ.a / 10 ^ 6) * Real.rpow q κ.Mlo / (1000 * κ.u)) ∧
  (Real.rpow (κ.M1 * q) κ.aB + 10 ≤ κ.M1 * q / (10 ^ 6 * κ.u)) ∧
  (κ.M1 * q < Real.rpow q κ.Cb) ∧
  (Real.rpow q (κ.Cb * κ.aB) ≥ 2 * Real.rpow q κ.aC +
    2 * Real.rpow (2 * q) (4 * κ.ω * κ.Mhi) + Real.log (800 / (κ.a * (1 / 400 : ℝ)))) ∧
  (Real.rpow q (2 * κ.aC) ≥ 2 * Real.rpow q κ.aC +
    2 * Real.rpow (2 * q) (4 * κ.ω * κ.Mhi) + Real.log (800 / (κ.a * (1 / 400 : ℝ)))) ∧
  (4 * Cstar κ.u κ.ξ * q ^ 2 ≤ (κ.a / 10 ^ 6) * Real.rpow q κ.Mlo) ∧
  (40 * Real.rpow q κ.Cb ≤ (κ.a / 10 ^ 6) * Real.rpow q κ.Mlo / (100 * κ.u)) ∧
  (∀ h : ℕ, Real.rpow q κ.Mlo ≤ (h : ℝ) → (h : ℝ) < 2 * Real.rpow q κ.Mhi →
    (κ.h0 ≤ h) ∧
    ((sliceT κ h : ℝ) * Real.log h ≤ κ.c5 * κ.a ^ 2 * (sliceK κ h : ℝ) / 10) ∧
    (0.02 * κ.a * h - Real.log (200 / κ.a) ≥ 0.0005 * κ.a * h) ∧
    ((2 : ℝ) ^ sliceK κ h * Real.exp (-0.013 * κ.a * (sliceK κ h : ℝ) * h) ≤ 1 / 2) ∧
    (Real.exp ((κ.a / 10 ^ 9) * h) * (h + 1) *
      Real.exp (-0.01 * κ.a * (sliceK κ h : ℝ) * h) ≤
      Real.exp (-0.009 * κ.a * (sliceK κ h : ℝ) * h)) ∧
    ((h : ℝ) ^ 6 * Real.sqrt (sliceEps κ h) ≤ Real.rpow 10 (-3)) ∧
    (Real.exp (-(Real.rpow (h : ℝ) (1 + κ.c14))) +
      2 * h ^ 2 * Real.sqrt (sliceEps κ h) ≤ Real.rpow 10 (-5)) ∧
    (⌊Real.exp (q / 2)⌋₊ ≥ κ.d0) ∧
    (Real.rpow (⌊Real.exp (q / 2)⌋₊ : ℝ) (-0.05) +
      Real.rpow (⌊Real.exp (q / 2)⌋₊ : ℝ) (-0.01) ≤ Real.rpow 10 (-3)) ∧
    ((h : ℝ) ≤ Real.rpow (⌊Real.exp (q / 2)⌋₊ : ℝ) 0.01) ∧
    ((⌊Real.exp (q / 2)⌋₊ : ℝ) *
      Real.exp (-κ.cChernoff * (⌊Real.exp (q / 2)⌋₊ : ℝ) ^ (0.4 : ℝ)) ≤
      ((⌊Real.exp (q / 2)⌋₊ : ℝ) ^ (-10 : ℝ)) / 2))

/-- The fixed bounded-mode threshold requirements. -/
def BoundedCond (κ : CConsts) : Prop :=
  IsDyadic κ.Qbd ∧
  κ.M1 * κ.Q0 < (κ.Qbd : ℝ) ∧
  Real.exp (-Real.rpow (κ.Qbd : ℝ) κ.aC) ≤ κ.a / 4000 ∧
  1 ≤ κ.Kbd ∧
  Real.exp (Cstar κ.u κ.ξ * κ.Qbd) ≤ κ.Kbd

/-- F-CConsts: named admissibility hypotheses for all fixed inequalities cited in §6. -/
structure CConsts.Admissible (κ : CConsts) : Prop where
  η0_pos : 0 < κ.η0
  xs_rng : 0 < κ.xs ∧ κ.xs < 0.01
  α_rng : 0 < κ.α ∧ κ.α < 0.01
  ι_rng : 0 < κ.ι ∧ κ.ι < min κ.xs (min κ.η0 0.01) / 1000
  xι_pos : 0 < κ.xι
  αι_pos : 0 < κ.αι
  Ac_eq : κ.Ac = 200
  P_big : κ.Pstar ≤ κ.P ∧ 100 * (κ.Ac + 10) ≤ κ.P
  R_eq : κ.R = κ.P ^ 2
  L_eq : κ.L = 500 * κ.R
  u_rng : Even κ.u ∧ 10 * κ.L ^ 2 < κ.u
  ξ_rng : 0 < κ.ξ ∧ κ.ξ < κ.α * Real.rpow 2 (-(10 * (κ.u : ℝ) + 100))
  θ_rng : 0 < κ.θ ∧ κ.θ < κ.ξ ^ 2 / (3 * 4 ^ (κ.u + 3))
  clock : ClockConstants 5 2 κ.Astar κ.Pstar κ.θ0
  aC_rng : 0 < κ.aC ∧ κ.aC < min κ.η0 1 / 10 ^ 6
  aB_rng : 0 < κ.aB ∧ κ.aB < κ.aC / 1000 ∧ κ.aB ≤ κ.xι
  M1_big : 4 ≤ κ.M1 ∧ 2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1 ≤ 1e-4
  Cb_big : 100 * κ.aC / κ.aB + 100 < κ.Cb
  Mlo_big : (κ.Cb + 100 : ℝ) < κ.Mlo
  cq_rng : 0 < κ.cq ∧ κ.cq < 1 / (20 * κ.Mlo)
  Mhi_big : (κ.Mlo : ℝ) + 10 / κ.cq ≤ κ.Mhi ∧ 5 < κ.cq * κ.Mhi
  ω_rng : 0 < κ.ω ∧ 5 * κ.ω * κ.Mhi < κ.aC / 100
  a_eq : κ.a = κ.θ / 100
  ρ_rng : 0 < κ.ρ ∧ κ.ρ < 1 / 4000 ∧ binEntropy (1000 * κ.ρ) < κ.a / 10 ^ 9
  KB_big : 10 ^ 6 * κ.R ≤ κ.KB
  A0_big : 10 ^ 6 * κ.R ≤ κ.A0
  bucket : 40 ≤ κ.Kp ∧ 0 < κ.cp ∧ κ.Kp * κ.θstar ≤ κ.θ0 / 2 ∧
    κ.cp * 4 ≤ κ.θ0 / 2 ∧ 0 < κ.θstar
  Kcell_big : 100 / κ.θstar ≤ κ.Kcell
  cperm_rng : 0 < κ.cperm ∧ κ.cperm < κ.α / 10
  c5_pos : 0 < κ.c5
  /-- P14.1c: the list-test exponent is an absolute constant; Azuma with deviation margin `.3ak`
  over `k` increments of range `< 1.5` gives exponent `≥ .08 a²k`, so any `c5 ≤ 1/1000` is valid. -/
  c5_le : κ.c5 ≤ 1 / 1000
  c14_pos : 0 < κ.c14
  cChernoff_pos : 0 < κ.cChernoff
  h0_pos : 0 < κ.h0
  d0_pos : 0 < κ.d0
  nearProduct : NearProductConstants κ.d0
  Q0_large : ∀ q : ℝ, κ.Q0 ≤ q → QCond κ q
  bounded : BoundedCond κ
  β_rng : 0 < κ.β ∧ κ.β ≤ 0.02 / (1 + κ.KB + 2 * κ.A0) ∧ κ.β < 1 / 16

/-- C12.K: choose the fixed constants from initial and deep discrepancy stage data. -/
theorem exists_admissible (T : Stage) (η0 : ℝ) (hη0 : 0 < η0)
    (hDeep : ∀ ε : ℝ, 0 < ε → ∃ x α : ℝ, 0 < x ∧ 0 < α ∧ DeepDisc T x α ε) :
    ∃ κ : CConsts, κ.Admissible ∧ κ.η0 = η0 ∧
      DeepDisc T κ.xs κ.α 0.04 ∧ DeepDisc T κ.xι κ.αι (κ.ι / 2) := by
  sorry

end HypercubeRamsey
