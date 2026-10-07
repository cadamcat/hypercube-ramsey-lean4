import HypercubeRamsey.PartC.Core
import HypercubeRamsey.S03.NearProductInjection
import HypercubeRamsey.PartC.Consts_sol_consts_adm

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
  classical
  obtain ⟨x, α₀, hx, hα₀, hdisc⟩ := hDeep 0.04 (by norm_num)
  obtain ⟨xs, hxs, hxs'⟩ := exists_between (show (0 : ℝ) < min x 0.01 by positivity)
  obtain ⟨α, hα, hα'⟩ := exists_between (show (0 : ℝ) < min α₀ 0.01 by positivity)
  have hxsx : xs ≤ x := (hxs'.trans_le (min_le_left _ _)).le
  have hxs01 : xs < 0.01 := hxs'.trans_le (min_le_right _ _)
  have hαα : α ≤ α₀ := (hα'.trans_le (min_le_left _ _)).le
  have hα01 : α < 0.01 := hα'.trans_le (min_le_right _ _)
  have hdisc' := Lane_sol_consts_adm.deep_mono hdisc hxsx hαα
  obtain ⟨ι, hι, hι'⟩ := exists_between
    (show (0 : ℝ) < min xs (min η0 0.01) / 1000 by positivity)
  obtain ⟨xι, αι, hxι, hαι, hdiscι⟩ := hDeep (ι / 2) (by positivity)
  obtain ⟨A', P', n₀, ε, hε, hclock⟩ := clock_sampling 5 2 (by norm_num)
  let A := max A' 1
  let Pc := max P' 1
  let Astar := ⌈A⌉₊
  let Pstar := ⌈Pc⌉₊
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hPc : 0 < Pc := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hclock' : ClockConstants 5 2 Astar Pstar 1e-8 := by
    refine ⟨by norm_num, rfl, A, Pc, max n₀ 1, ε, hA, hPc,
      Nat.le_ceil _, Nat.le_ceil _, le_max_right _ _, hε, ?_⟩
    intro n hn g hg R K _ _ _ Ω _ _ lab laws F sc h1 h2 h3 h4 h5 h6
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right n₀ 1).trans hn
    apply hclock n ((le_max_left _ _).trans hn) g hg lab laws F sc h1
    · intro a y
      exact (h2 a y).trans (Real.rpow_le_rpow_of_exponent_le hn1
        (neg_le_neg (le_max_left _ _)))
    · exact h3
    · exact h4
    · exact h5
    · intro k
      exact (h6 k).trans (Real.rpow_le_rpow_of_exponent_le hn1
        (neg_le_neg (le_max_left _ _)))
  let P := max Pstar (100 * (200 + 10))
  let R := P ^ 2
  let L := 500 * R
  let u := 2 * (10 * L ^ 2 + 1)
  have hu : Even u ∧ 10 * L ^ 2 < u := by
    constructor
    · exact ⟨10 * L ^ 2 + 1, by dsimp [u]; omega⟩
    · dsimp [u]
      omega
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  obtain ⟨ξ, hξ, hξ'⟩ := exists_between
    (show (0 : ℝ) < α * Real.rpow 2 (-(10 * (u : ℝ) + 100)) from
      mul_pos hα (Real.rpow_pos_of_pos (by norm_num) _))
  obtain ⟨θ, hθ, hθ'⟩ := exists_between
    (show (0 : ℝ) < ξ ^ 2 / (3 * 4 ^ (u + 3)) by positivity)
  let a := θ / 100
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨aC, haC, haC'⟩ := exists_between
    (show (0 : ℝ) < min η0 1 / 10 ^ 6 by positivity)
  obtain ⟨aB, haB, haB'⟩ := exists_between
    (show (0 : ℝ) < min (aC / 1000) xι by positivity)
  have haBaC : aB < aC / 1000 := haB'.trans_le (min_le_left _ _)
  have haBxι : aB ≤ xι := (haB'.trans_le (min_le_right _ _)).le
  have haC1 : aC < 1 / 10 ^ 6 := haC'.trans_le
    (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have haB1 : aB < 1 := by linarith only [haBaC, haC1]
  let C := Cstar u ξ
  let m := max 2 (20000 * |C| + 2)
  let M1 := m ^ 2
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hM1 : 4 ≤ M1 ∧ 2 * C / Real.sqrt M1 ≤ 1e-4 := by
    constructor
    · have he : 2 ≤ m := le_max_left _ _
      dsimp [M1]
      nlinarith only [he]
    · rw [show Real.sqrt M1 = m by exact Real.sqrt_sq hm.le]
      apply (div_le_iff₀ hm).mpr
      have he : 20000 * |C| + 2 ≤ m := le_max_right _ _
      nlinarith only [he, le_abs_self C]
  have hM1pos : 0 < M1 := lt_of_lt_of_le (by norm_num) hM1.1
  let Cb := 100 * aC / aB + 101
  have hCbEq : Cb * aB = 100 * aC + 101 * aB := by
    dsimp [Cb]
    field_simp [haB.ne']
  have hCb100 : 100 * aC / aB + 100 < Cb := by dsimp [Cb]; linarith only []
  have hCb1 : 1 < Cb := by
    have hr : 0 < 100 * aC / aB := by positivity
    dsimp [Cb]
    linarith only [hr]
  obtain ⟨Mlo, hMlo⟩ := exists_nat_gt (Cb + 100)
  have hMlopos : (0 : ℝ) < Mlo := by linarith only [hMlo, hCb1]
  obtain ⟨cq, hcq, hcq'⟩ := exists_between
    (show (0 : ℝ) < 1 / (20 * (Mlo : ℝ)) by positivity)
  obtain ⟨Mhi, hMhi⟩ := exists_nat_gt ((Mlo : ℝ) + 10 / cq + 10 / cq)
  have hdiv : 0 < 10 / cq := div_pos (by norm_num) hcq
  have hMhi1 : (Mlo : ℝ) + 10 / cq ≤ Mhi := by linarith only [hMhi, hdiv]
  have hMhipos : (0 : ℝ) < Mhi := by linarith only [hMhi1, hMlopos, hdiv]
  have hcqMhi : 5 < cq * Mhi := by
    have he : 10 / cq < (Mhi : ℝ) := by linarith only [hMhi1, hMlopos]
    have he' := (div_lt_iff₀ hcq).mp he
    nlinarith only [he']
  obtain ⟨ω, hω, hω'⟩ := exists_between
    (show (0 : ℝ) < aC / (500 * (Mhi : ℝ)) by positivity)
  have hωsmall : 5 * ω * Mhi < aC / 100 := by
    have he := (lt_div_iff₀ (show 0 < 500 * (Mhi : ℝ) by positivity)).mp hω'
    nlinarith only [he]
  obtain ⟨ρ, hρ, hρ', hentropy⟩ := Lane_sol_consts_adm.entropy_small a ha
  have hρentropy : binEntropy (1000 * ρ) < a / 10 ^ 9 := by
    have h0 : 1000 * ρ ≠ 0 := ne_of_gt (by positivity)
    have h1 : 1000 * ρ ≠ 1 := by nlinarith only [hρ']
    simpa only [binEntropy, ite_eq_right h0, ite_eq_right h1] using hentropy
  let KB := 10 ^ 6 * (R : ℝ)
  let A0 := 10 ^ 6 * (R : ℝ)
  let θstar : ℝ := 1e-8 / (4 * 40)
  let cp : ℝ := 1e-8 / 16
  let Kcell := 100 / θstar
  obtain ⟨cperm, hcperm, hcperm'⟩ := exists_between (show (0 : ℝ) < α / 10 by positivity)
  obtain ⟨d₀, hd₀⟩ := near_product_injection
  let d0 := max d₀ 1
  have hd0 : NearProductConstants d0 := by
    intro d hd
    exact hd₀ d ((le_max_left _ _).trans hd)
  have hlarge := Lane_sol_consts_adm.large_bounds a aC aB M1 Cb Mlo Mhi ω C u
    ha hu0 hM1pos haC haB haB1 hCb1
    (by linarith only [hMlo, hCb1, haC1])
    (by linarith only [hMlo, hCb1]) (by linarith only [hMlo])
    (by nlinarith only [hCbEq, haC, haB])
    (by nlinarith only [hCbEq, hωsmall, haC, haB])
    (by nlinarith only [hωsmall, haC])
  obtain ⟨H, hH⟩ := eventually_atTop.mp (Lane_sol_consts_adm.height_bounds a ω ha hω)
  have hheight : ∀ᶠ q : ℝ in atTop, H ≤ q ^ (Mlo : ℝ) :=
    (tendsto_rpow_atTop hMlopos).eventually (eventually_ge_atTop H)
  obtain ⟨Q0, hQ0⟩ := eventually_atTop.mp
    (hlarge.and ((Lane_sol_consts_adm.bin_bounds Mhi d0).and hheight))
  have hdyad : Tendsto (fun j : ℕ => ((2 : ℕ) ^ j : ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hdyadexp := (Lane_sol_consts_adm.tendsto_power_exp_power 0 aC 1 haC
    (by norm_num)).comp hdyad
  obtain ⟨j, hj, hjexp⟩ := ((hdyad.eventually (eventually_gt_atTop (M1 * Q0))).and
    (hdyadexp.eventually (gt_mem_nhds (show (0 : ℝ) < a / 4000 by positivity)))).exists
  let Qbd := 2 ^ j
  let Kbd := max 1 (Real.exp (C * Qbd))
  obtain ⟨β, hβ, hβ'⟩ := exists_between
    (show (0 : ℝ) < min (0.02 / (1 + KB + 2 * A0)) (1 / 16) by
      dsimp [KB, A0]
      positivity)
  let κ : CConsts := {
    η0 := η0, xs := xs, α := α, ι := ι, xι := xι, αι := αι,
    Ac := 200, P := P, R := R, L := L, u := u, ξ := ξ, θ := θ,
    Astar := Astar, Pstar := Pstar, θ0 := 1e-8,
    aC := aC, aB := aB, M1 := M1, Cb := Cb, Mlo := Mlo, Mhi := Mhi,
    cq := cq, ω := ω, a := a, ρ := ρ, KB := KB, A0 := A0,
    Q0 := Q0, Kbd := Kbd, Qbd := Qbd, θstar := θstar, Kp := 40, cp := cp,
    Kcell := Kcell, cperm := cperm, β := β, c5 := 1 / 1000,
    c14 := 1, cChernoff := 1, h0 := 1, d0 := d0 }
  refine ⟨κ, ?_, rfl, hdisc', hdiscι⟩
  refine {
    η0_pos := hη0, xs_rng := ⟨hxs, hxs01⟩, α_rng := ⟨hα, hα01⟩,
    ι_rng := ⟨hι, hι'⟩, xι_pos := hxι, αι_pos := hαι,
    Ac_eq := rfl, P_big := ⟨le_max_left _ _, le_max_right _ _⟩,
    R_eq := rfl, L_eq := rfl, u_rng := hu, ξ_rng := ⟨hξ, hξ'⟩,
    θ_rng := ⟨hθ, hθ'⟩, clock := hclock', aC_rng := ⟨haC, haC'⟩,
    aB_rng := ⟨haB, haBaC, haBxι⟩, M1_big := hM1, Cb_big := hCb100,
    Mlo_big := hMlo, cq_rng := ⟨hcq, hcq'⟩, Mhi_big := ⟨hMhi1, hcqMhi⟩,
    ω_rng := ⟨hω, hωsmall⟩, a_eq := rfl, ρ_rng := ⟨hρ, hρ', hρentropy⟩,
    KB_big := le_rfl, A0_big := le_rfl,
    bucket := by norm_num [κ, θstar, cp], Kcell_big := le_rfl,
    cperm_rng := ⟨hcperm, hcperm'⟩, c5_pos := by norm_num [κ],
    c5_le := le_rfl, c14_pos := by norm_num [κ], cChernoff_pos := by norm_num [κ],
    h0_pos := by norm_num [κ], d0_pos := lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    nearProduct := hd0, Q0_large := ?_, bounded := ?_,
    β_rng := ⟨hβ, (hβ'.trans_le (min_le_left _ _)).le, hβ'.trans_le (min_le_right _ _)⟩ }
  · intro q hq
    obtain ⟨hl, hb, hh⟩ := hQ0 q hq
    rcases hl with ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8⟩
    refine ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, ?_⟩
    intro h hlow hhigh
    have hheight := hH (h : ℝ) (hh.trans hlow)
    rcases hheight with ⟨hh1, hht, hhl, hh2, hh3, hh4, hh5⟩
    refine ⟨by exact_mod_cast hh1, hht, hhl, hh2, hh3, hh4, ?_, hb.1, hb.2.1, ?_, ?_⟩
    · simpa only [κ, sliceEps, sliceK, Nat.cast_ofNat, Real.rpow_eq_pow, Real.rpow_ofNat,
        show (1 : ℝ) + 1 = 2 by norm_num] using hh5
    · exact hhigh.le.trans hb.2.2.1
    · simpa only [κ, neg_mul, one_mul] using hb.2.2.2
  · refine ⟨⟨j, rfl⟩, ?_, ?_, le_max_left _ _, le_max_right _ _⟩
    · simpa only [κ, Qbd, Nat.cast_pow, Nat.cast_ofNat] using hj
    · simpa only [κ, Qbd, Function.comp_def, Real.rpow_eq_pow, Nat.cast_pow,
        Nat.cast_ofNat, Real.rpow_zero, one_mul, neg_mul] using hjexp.le

end HypercubeRamsey
