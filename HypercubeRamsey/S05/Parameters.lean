import HypercubeRamsey.S05.Defs

set_option maxHeartbeats 400000

/-!
# D5.1: parameter order and scales

The choices are parameterized by the theorem inputs.  The definitions below make the chunk, severity,
segment, pool, and history lengths available to later nodes.
-/

namespace HypercubeRamsey

open Filter
noncomputable section
variable {γ : ℝ} {K' : ℝ} {χ : ℝ}

/-- Binary entropy in natural logarithms. -/
def binaryEntropy5 (x : ℝ) : ℝ := -x * Real.log x - (1 - x) * Real.log (1 - x)

/-- The fixed constants and order of choices in D5.1 (05:57–61, 05:762–783).  `Kcap` is the Step 1 prior-cap
constant `K'` (05:207–211) and `Kpp` the block-density constant `K''` of `A_K` (05:263–268).
`hdelta_a` reserves slack at every exponent gap; `hKpp_budget` pays for the Step 2 density losses.
`hK1_eta` ensures high blocks fit inside every observed key prefix. These constraints respect the
choice order: first shrink `δ`, then enlarge `K''`, then choose `K₁` above `η` and its requested threshold. -/
structure Params5 (γ K' χ : ℝ) where
  a : Fin 9 → ℝ
  tau0 : ℝ
  tau1 : ℝ
  delta : ℝ
  q0 : ℕ
  Kh : ℝ
  K1 : ℝ
  K2 : ℝ
  KD : ℝ
  Ks : ℝ
  KB : ℝ
  eta : ℝ
  nu0 : ℝ
  nu1 : ℝ
  alpha : ℝ
  rho : ℝ
  Kcap : ℝ
  Kpp : ℝ
  hγ : 0 < γ ∧ γ < 1
  hK : 0 < K'
  hχ : 0 < χ
  ha0 : a 0 = 1 / 3
  ha_order : ∀ i j : Fin 9, i.val < j.val → a i < a j
  hgap : a 8 < tau0 ∧ tau0 < tau1 ∧ tau1 < Real.log 2
  hdelta : 0 < delta ∧ delta < min (tau0 - a 8) (tau1 - tau0) / 100
  hdelta_a : ∀ i j : Fin 9, i.val < j.val → delta < (a j - a i) / 100
  hq0 : 0 < q0 ∧
    (2 / χ ^ 2) * (10 / 9 : ℝ) ^ q0 ≤ Real.exp (a 0 * q0)
  hKh : 0 < Kh
  heta : 0 < eta ∧ Kh * eta + 1 / 200 < 3 / 100
  hK1 : 0 < K1
  hK1_eta : eta ≤ K1
  hK2 : 0 < K2
  hKD : 0 < KD
  hKs : 0 < Ks
  hKB : 0 < KB
  hnu0 : 0 < nu0
  hnu1 : tau0 / tau1 < nu1 ∧ nu1 + nu0 < 1
  halpha : 0 < alpha ∧ alpha < 1 / 50
  hrho : 0 < rho ∧ 2 * rho < 1 / 2
  hEntropy : binaryEntropy5 (2 * rho) < Real.log 2 - tau1
  hKcap : 0 < Kcap
  hKpp : 0 < Kpp
  hKpp_budget : max (a 0) (a 1 + delta) ≤ Kpp

/-- Number of fine sign chunks, `m = ⌈n^α⌉`. -/
def Params5.m (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ p.alpha⌉₊

/-- Low/high interface severity, `J = ⌊m^(1/20)⌋`. -/
def Params5.J (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌊(p.m n : ℝ) ^ (1 / 20 : ℝ)⌋₊

/-- Number of IDs allowed in a local mapping. -/
def Params5.T (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌈(p.m n : ℝ) ^ (1 / 1000 : ℝ)⌉₊

/-- Round a nonnegative real length up to a multiple of the segment length. -/
def roundedSegments5 (q : ℕ) (x : ℝ) : ℕ := q * ⌈x / q⌉₊

/-- Segment-rounded stream prefix length `u_j`. -/
def Params5.u (p : Params5 γ K' χ) (n j : ℕ) : ℕ :=
  roundedSegments5 p.q0 (p.K1 * ((j : ℝ) + 4) * Real.log (p.m n : ℝ))

/-- Step 1's observed prefix endpoint `b_j = u_(j+1)`. -/
def Params5.prefixEnd (p : Params5 γ K' χ) (n j : ℕ) : ℕ := p.u n (j + 1)

/-- Low tuple length `k_j`. -/
def Params5.k (p : Params5 γ K' χ) (n j : ℕ) : ℕ :=
  let u := p.u n j
  if u = 0 then 0 else
    u * ⌈(p.K2 * (((j : ℝ) + 4) * Real.log (p.m n : ℝ) +
      (p.m n : ℝ) ^ (1 / 50 : ℝ))) / u⌉₊

/-- Segment-rounded high tuple block length. -/
def Params5.uStar (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  roundedSegments5 p.q0 (p.eta * Real.log (p.m n : ℝ))

/-- High tuple length `k_*`. -/
def Params5.kStar (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  let u := p.uStar n
  if u = 0 then 0 else u * ⌈((p.m n : ℝ) ^ (1 / 200 : ℝ)) / u⌉₊

/-- High history length `s`. -/
def Params5.s (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  ⌈p.Ks * (p.J n : ℝ) * Real.log (p.m n : ℝ)⌉₊

/-- Full high-pool size in entries, denoted `M_*` in D5.1. -/
def Params5.poolSize (p : Params5 γ K' χ) (n : ℕ) : ℕ :=
  let u := p.uStar n
  if u = 0 then 0 else
    u * ⌈Real.exp (p.Kh * u) * (p.kStar n : ℝ) / u⌉₊

/-- Entropy inequality required by the residual-coordinate height radius. -/
def Params5.DL (p : Params5 γ K' χ) (n : ℕ) : ℝ := (p.m n : ℝ) ^ (15 / 100 : ℝ)

/-- High row cap exponent `D_H = K_D J log m`. -/
def Params5.DH (p : Params5 γ K' χ) (n : ℕ) : ℝ :=
  p.KD * (p.J n : ℝ) * Real.log (p.m n : ℝ)

/-- The four eventual scale relations listed in D5.1. -/
def Params5.ScaleRelations (p : Params5 γ K' χ) : Prop :=
  Tendsto (fun n : ℕ =>
    (p.T n : ℝ) * p.poolSize n / (p.J n : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ =>
    (p.T n : ℝ) * Real.log (n : ℝ) / (p.kStar n : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ =>
    (p.T n : ℝ) * Real.log (n : ℝ) / (p.m n : ℝ) ^ (1 / 50 : ℝ)) atTop (nhds 0) ∧
  Tendsto (fun n : ℕ =>
    ((p.T n + p.J n : ℕ) : ℝ) / (p.s n : ℝ)) atTop (nhds 0)

/-! ### The order of the large and small constants (05:762–783)

The constants that the paper takes "sufficiently large" (or `α` "sufficiently small") are chosen in order, each
after the ones it may depend on.  A node that needs such a constant states its need as a threshold function of
the earlier constants (`ParamReq5`); D5.1 then chooses all constants meeting every requested threshold. -/

/-- Constants fixed first: the exponent ladder `a`, `τ₀, τ₁, δ`, `υ₀, υ₁`, `ρ` and `q₀`. -/
abbrev Pre05 := (Fin 9 → ℝ) × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℕ
/-- ... then the Step 1 cap constant `K'`, the block constant `K''`, `K_h` and `η`. -/
abbrev Pre15 := Pre05 × ℝ × ℝ × ℝ × ℝ
/-- ... then `K₁`. -/
abbrev Pre25 := Pre15 × ℝ
/-- ... then `K₂`. -/
abbrev Pre35 := Pre25 × ℝ
/-- ... then `K_D`. -/
abbrev Pre45 := Pre35 × ℝ
/-- ... then `K_s`. -/
abbrev Pre55 := Pre45 × ℝ
/-- ... then `K_B`; `α` is chosen last. -/
abbrev Pre65 := Pre55 × ℝ

def Params5.pre0 (p : Params5 γ K' χ) : Pre05 :=
  (p.a, p.tau0, p.tau1, p.delta, p.nu0, p.nu1, p.rho, p.q0)
def Params5.pre1 (p : Params5 γ K' χ) : Pre15 := (p.pre0, p.Kcap, p.Kpp, p.Kh, p.eta)
def Params5.pre2 (p : Params5 γ K' χ) : Pre25 := (p.pre1, p.K1)
def Params5.pre3 (p : Params5 γ K' χ) : Pre35 := (p.pre2, p.K2)
def Params5.pre4 (p : Params5 γ K' χ) : Pre45 := (p.pre3, p.KD)
def Params5.pre5 (p : Params5 γ K' χ) : Pre55 := (p.pre4, p.Ks)
def Params5.pre6 (p : Params5 γ K' χ) : Pre65 := (p.pre5, p.KB)

/-- Thresholds requested by the nodes: lower bounds for the large constants and a positive upper bound for
`α`, each a function of the constants chosen before it. -/
structure ParamReq5 where
  Kcap : Pre05 → ℝ
  Kpp : Pre05 → ℝ
  Kh : Pre05 → ℝ
  K1 : Pre15 → ℝ
  K2 : Pre25 → ℝ
  KD : Pre35 → ℝ
  Ks : Pre45 → ℝ
  KB : Pre55 → ℝ
  alpha : Pre65 → ℝ
  alpha_pos : ∀ x, 0 < alpha x

/-- A parameter choice meets the requested thresholds. -/
def ParamReq5.Holds (R : ParamReq5) (p : Params5 γ K' χ) : Prop :=
  R.Kcap p.pre0 ≤ p.Kcap ∧ R.Kpp p.pre0 ≤ p.Kpp ∧ R.Kh p.pre0 ≤ p.Kh ∧ R.K1 p.pre1 ≤ p.K1 ∧
    R.K2 p.pre2 ≤ p.K2 ∧ R.KD p.pre3 ≤ p.KD ∧ R.Ks p.pre4 ≤ p.Ks ∧ R.KB p.pre5 ≤ p.KB ∧
      p.alpha ≤ R.alpha p.pre6

/-- The pointwise strongest of two threshold requests. -/
def ParamReq5.join (R R' : ParamReq5) : ParamReq5 where
  Kcap x := max (R.Kcap x) (R'.Kcap x)
  Kpp x := max (R.Kpp x) (R'.Kpp x)
  Kh x := max (R.Kh x) (R'.Kh x)
  K1 x := max (R.K1 x) (R'.K1 x)
  K2 x := max (R.K2 x) (R'.K2 x)
  KD x := max (R.KD x) (R'.KD x)
  Ks x := max (R.Ks x) (R'.Ks x)
  KB x := max (R.KB x) (R'.KB x)
  alpha x := min (R.alpha x) (R'.alpha x)
  alpha_pos x := lt_min (R.alpha_pos x) (R'.alpha_pos x)

theorem ParamReq5.holds_of_join {R R' : ParamReq5} {p : Params5 γ K' χ}
    (h : (R.join R').Holds p) : R.Holds p ∧ R'.Holds p := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [ParamReq5.join, max_le_iff, le_min_iff] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨⟨h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, h8.1, h9.1⟩,
    ⟨h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2⟩⟩

/-- D5.1 (05:57–61, 05:762–783, 05:785–816): the constants can be chosen in the paper's order, meeting any
requested thresholds, with the eventual scale relations. -/
theorem D5_1_params (γ K' χ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1)
    (hK : 0 < K') (hχ : 0 < χ) (R : ParamReq5) :
    ∃ p : Params5 γ K' χ, p.ScaleRelations ∧ R.Holds p := by
  classical
  let a : Fin 9 → ℝ := fun i => 1 / 3 + (i.val : ℝ) / 500
  let tau0 : ℝ := 9 / 25
  let tau1 : ℝ := 2 / 5
  let delta : ℝ := 1 / 100000
  let nu0 : ℝ := 1 / 50
  let nu1 : ℝ := 91 / 100
  let rho : ℝ := 1 / 1000
  let B : ℝ := Real.exp (1 / 3 : ℝ) * (9 / 10)
  have hB : 1 < B := by
    dsimp [B]
    have h := Real.add_one_lt_exp (by norm_num : (1 / 3 : ℝ) ≠ 0)
    nlinarith
  have hBpowTendsto : Tendsto (fun q : ℕ => B ^ q) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hB
  obtain ⟨qN, hqN⟩ :=
    (hBpowTendsto.eventually_ge_atTop (2 / χ ^ 2)).exists
  let q0 : ℕ := qN + 1
  have hq0pos : 0 < q0 := by omega
  have hBstep : B ^ qN ≤ B ^ (qN + 1) := by
    calc
      B ^ qN = B ^ qN * 1 := by ring
      _ ≤ B ^ qN * B := mul_le_mul_of_nonneg_left hB.le (by positivity)
      _ = B ^ (qN + 1) := by rw [pow_succ]
  have hBpow : 2 / χ ^ 2 ≤ B ^ q0 := by
    exact hqN.trans (by simpa [q0] using hBstep)
  have hq0ineq : (2 / χ ^ 2) * (10 / 9 : ℝ) ^ q0 ≤
      Real.exp ((q0 : ℝ) * (1 / 3 : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hBpow (by positivity : 0 ≤ (10 / 9 : ℝ) ^ q0)
    have hcancel : (9 / 10 : ℝ) ^ q0 * (10 / 9 : ℝ) ^ q0 = 1 := by
      rw [← mul_pow]
      norm_num
    have hprod : B ^ q0 * (10 / 9 : ℝ) ^ q0 =
        Real.exp ((q0 : ℝ) * (1 / 3 : ℝ)) := by
      calc
        B ^ q0 * (10 / 9 : ℝ) ^ q0 =
            (Real.exp (1 / 3 : ℝ) ^ q0) * ((9 / 10 : ℝ) ^ q0 * (10 / 9 : ℝ) ^ q0) := by
              dsimp [B]
              rw [mul_pow]
              ring
        _ = Real.exp (1 / 3 : ℝ) ^ q0 := by
          rw [hcancel, mul_one]
        _ = Real.exp ((q0 : ℝ) * (1 / 3 : ℝ)) := (Real.exp_nat_mul (1 / 3 : ℝ) q0).symm
    exact hmul.trans_eq hprod
  let pre0 : Pre05 := (a, tau0, tau1, delta, nu0, nu1, rho, q0)
  let Kcap : ℝ := max (R.Kcap pre0) 1
  let Kpp : ℝ := max (R.Kpp pre0) (max (a 0) (a 1 + delta))
  let Kh : ℝ := max (R.Kh pre0) 1
  let eta : ℝ := 1 / (100 * Kh)
  let pre1 : Pre15 := (pre0, Kcap, Kpp, Kh, eta)
  let K1 : ℝ := max (R.K1 pre1) eta
  let pre2 : Pre25 := (pre1, K1)
  let K2 : ℝ := max (R.K2 pre2) 1
  let pre3 : Pre35 := (pre2, K2)
  let KD : ℝ := max (R.KD pre3) 1
  let pre4 : Pre45 := (pre3, KD)
  let Ks : ℝ := max (R.Ks pre4) 1
  let pre5 : Pre55 := (pre4, Ks)
  let KB : ℝ := max (R.KB pre5) 1
  let pre6 : Pre65 := (pre5, KB)
  let alpha : ℝ := min (R.alpha pre6 / 2) (1 / 100)
  have hKcapPos : 0 < Kcap := by
    dsimp [Kcap]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hKppBudget : max (a 0) (a 1 + delta) ≤ Kpp := by
    dsimp [Kpp]
    exact le_max_right _ _
  have hKppPos : 0 < Kpp := by
    have h0 : 0 < a 0 := by norm_num [a]
    exact lt_of_lt_of_le h0 (le_trans (le_max_left _ _) hKppBudget)
  have hKhPos : 0 < Kh := by
    dsimp [Kh]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hetaPos : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaProduct : Kh * eta = 1 / 100 := by
    dsimp [eta]
    field_simp [ne_of_gt hKhPos]
  have hK1Pos : 0 < K1 := by
    dsimp [K1]
    exact lt_of_lt_of_le hetaPos (le_max_right _ _)
  have hK2Pos : 0 < K2 := by
    dsimp [K2]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hKDPos : 0 < KD := by
    dsimp [KD]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hKsPos : 0 < Ks := by
    dsimp [Ks]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hKBPos : 0 < KB := by
    dsimp [KB]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hbin40 : Real.binEntropy (1 / 40 : ℝ) ≤ 13 / 100 := by
    have hlog2 : Real.log 2 < 7 / 10 := by
      exact lt_trans Real.log_two_lt_d9 (by norm_num)
    have hlog40 : Real.log 40 < 21 / 5 := by
      calc
        Real.log 40 < Real.log 64 := Real.log_lt_log (by norm_num) (by norm_num)
        _ = 6 * Real.log 2 := by
          rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, Real.log_pow]
          norm_num
        _ < 6 * (7 / 10) := by nlinarith
        _ = 21 / 5 := by norm_num
    have hfirst : (1 / 40 : ℝ) * Real.log 40 < 21 / 200 := by nlinarith
    have hy : 0 < (1 - 1 / 40 : ℝ)⁻¹ := by norm_num
    have hyne : (1 - 1 / 40 : ℝ)⁻¹ ≠ 1 := by norm_num
    have hlogy := Real.log_lt_sub_one_of_pos hy hyne
    have hsecond : (1 - 1 / 40 : ℝ) * Real.log ((1 - 1 / 40 : ℝ)⁻¹) ≤ 1 / 40 := by
      calc
        (1 - 1 / 40 : ℝ) * Real.log ((1 - 1 / 40 : ℝ)⁻¹) ≤
            (1 - 1 / 40 : ℝ) * ((1 - 1 / 40 : ℝ)⁻¹ - 1) :=
          (mul_lt_mul_of_pos_left hlogy (by norm_num)).le
        _ = 1 / 40 := by norm_num
    change (1 / 40 : ℝ) * Real.log ((1 / 40 : ℝ)⁻¹) +
      (1 - 1 / 40 : ℝ) * Real.log ((1 - 1 / 40 : ℝ)⁻¹) ≤ 13 / 100
    rw [show (1 / 40 : ℝ)⁻¹ = 40 by norm_num]
    linarith
  have hbin : Real.binEntropy (2 * rho) ≤ 13 / 100 := by
    have hqmem : 2 * rho ∈ Set.Icc (0 : ℝ) (2⁻¹) := by norm_num [rho]
    have h40mem : (1 / 40 : ℝ) ∈ Set.Icc (0 : ℝ) (2⁻¹) := by norm_num
    calc
      Real.binEntropy (2 * rho) ≤ Real.binEntropy (1 / 40 : ℝ) :=
        Real.binEntropy_strictMonoOn.monotoneOn hqmem h40mem (by norm_num [rho])
      _ ≤ 13 / 100 := hbin40
  have hbinEq : binaryEntropy5 (2 * rho) = Real.binEntropy (2 * rho) := by
    unfold binaryEntropy5 Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hEntropy : binaryEntropy5 (2 * rho) < Real.log 2 - tau1 := by
    rw [hbinEq]
    have hgap : (13 / 100 : ℝ) < Real.log 2 - 2 / 5 := by
      have hlog := Real.log_two_gt_d9
      norm_num [tau1]
      linarith
    exact lt_of_le_of_lt hbin hgap
  have halphaPos : 0 < alpha := by
    dsimp [alpha]
    exact lt_min (div_pos (R.alpha_pos pre6) (by norm_num)) (by norm_num)
  have halphaSmall : alpha < 1 / 50 := by
    dsimp [alpha]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let p : Params5 γ K' χ := {
    a := a
    tau0 := tau0
    tau1 := tau1
    delta := delta
    q0 := q0
    Kh := Kh
    K1 := K1
    K2 := K2
    KD := KD
    Ks := Ks
    KB := KB
    eta := eta
    nu0 := nu0
    nu1 := nu1
    alpha := alpha
    rho := rho
    Kcap := Kcap
    Kpp := Kpp
    hγ := ⟨hγ, hγ'⟩
    hK := hK
    hχ := hχ
    ha0 := by norm_num [a]
    ha_order := by
      intro i j hij
      have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
      dsimp [a]
      nlinarith
    hgap := by
      constructor
      · norm_num [a, tau0]
      constructor
      · norm_num [tau0, tau1]
      · have hlog := Real.log_two_gt_d9
        norm_num [tau1]
        linarith
    hdelta := by
      constructor
      · norm_num [delta]
      · norm_num [a, tau0, tau1, delta]
    hdelta_a := by
      intro i j hij
      have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
      have hn : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hij
      have hnCast : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hn
      have hgap' : (1 : ℝ) ≤ (j.val : ℝ) - i.val := by linarith
      dsimp [a, delta]
      nlinarith [hgap']
    hq0 := by
      refine ⟨by exact_mod_cast hq0pos, ?_⟩
      simpa [a, mul_comm] using hq0ineq
    hKh := hKhPos
    heta := by
      constructor
      · exact hetaPos
      · rw [hetaProduct]
        norm_num
    hK1 := hK1Pos
    hK1_eta := by dsimp [K1]; exact le_max_right _ _
    hK2 := hK2Pos
    hKD := hKDPos
    hKs := hKsPos
    hKB := hKBPos
    hnu0 := by norm_num [nu0]
    hnu1 := by
      constructor <;> norm_num [tau0, tau1, nu0, nu1]
    halpha := ⟨halphaPos, halphaSmall⟩
    hrho := by norm_num [rho]
    hEntropy := hEntropy
    hKcap := hKcapPos
    hKpp := hKppPos
    hKpp_budget := hKppBudget
  }
  let M : ℕ → ℝ := fun n => (p.m n : ℝ)
  have hM : Tendsto M atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ p.alpha) atTop atTop :=
      (tendsto_rpow_atTop p.halpha.1).comp tendsto_natCast_atTop_atTop
    have hmle (n : ℕ) : (n : ℝ) ^ p.alpha ≤ M n := by
      dsimp [M, Params5.m]
      exact Nat.le_ceil _
    exact tendsto_atTop_mono hmle hpow
  have hlogM : Tendsto (fun n => Real.log (M n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hM
  have hlogDiv (r : ℝ) (hr : 0 < r) :
      Tendsto (fun n => Real.log (M n) / (M n) ^ r) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_atTop hr).comp_tendsto hM).tendsto_div_nhds_zero
  have hTupper : ∀ᶠ n : ℕ in atTop, (p.T n : ℝ) ≤ 2 * (M n) ^ (1 / 1000 : ℝ) := by
    have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).comp hM
    filter_upwards [hpow.eventually_ge_atTop 1] with n hn
    have hn' : 1 ≤ (M n) ^ (1 / 1000 : ℝ) := by
      change 1 ≤ (M n) ^ (1 / 1000 : ℝ) at hn
      exact hn
    have hceil : (p.T n : ℝ) < (M n) ^ (1 / 1000 : ℝ) + 1 := by
      dsimp [Params5.T, M]
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
    calc
      (p.T n : ℝ) ≤ (M n) ^ (1 / 1000 : ℝ) + 1 := hceil.le
      _ ≤ 2 * (M n) ^ (1 / 1000 : ℝ) := by nlinarith [hn']
  have hJlower : ∀ᶠ n : ℕ in atTop, (M n) ^ (1 / 20 : ℝ) / 2 ≤ p.J n := by
    have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hM
    filter_upwards [hpow.eventually_ge_atTop 2] with n hn
    have hn' : 2 ≤ (M n) ^ (1 / 20 : ℝ) := by
      change 2 ≤ (M n) ^ (1 / 20 : ℝ) at hn
      exact hn
    have hfloor : (M n) ^ (1 / 20 : ℝ) < (p.J n : ℝ) + 1 := by
      dsimp [Params5.J]
      exact Nat.lt_floor_add_one _
    have hminus : (M n) ^ (1 / 20 : ℝ) - 1 < p.J n := by linarith
    have hhalf : (M n) ^ (1 / 20 : ℝ) / 2 ≤ (M n) ^ (1 / 20 : ℝ) - 1 := by
      nlinarith [hn']
    exact hhalf.trans (le_of_lt hminus)
  have hJupper (n : ℕ) : (p.J n : ℝ) ≤ (M n) ^ (1 / 20 : ℝ) := by
    dsimp [Params5.J, M]
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg (p.m n)) _)
  have hsLower : ∀ᶠ n : ℕ in atTop,
      p.Ks * (p.J n : ℝ) * Real.log (M n) ≤ (p.s n : ℝ) := by
    filter_upwards [hlogM.eventually_ge_atTop 1] with n hln
    dsimp [Params5.s]
    exact Nat.le_ceil _
  have hinvLog : Tendsto (fun n => (Real.log (M n))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlogM
  have huPos : ∀ᶠ n : ℕ in atTop, 0 < p.uStar n := by
    have hlog := hlogM.eventually_ge_atTop 1
    filter_upwards [hlog] with n hln
    have hq : (0 : ℝ) < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
    have harg : 0 < p.eta * Real.log (M n) / (p.q0 : ℝ) :=
      div_pos (mul_pos p.heta.1 (lt_of_lt_of_le zero_lt_one hln)) hq
    have hceil : 0 < (Nat.ceil (p.eta * Real.log (M n) / (p.q0 : ℝ)) : ℝ) :=
      lt_of_lt_of_le harg (Nat.le_ceil _)
    dsimp [Params5.uStar, roundedSegments5]
    exact Nat.mul_pos p.hq0.1 (by exact_mod_cast hceil)
  have hkStarLower : ∀ᶠ n : ℕ in atTop, (M n) ^ (1 / 200 : ℝ) ≤ p.kStar n := by
    filter_upwards [huPos] with n hu
    have huR : (0 : ℝ) < (p.uStar n : ℝ) := by exact_mod_cast hu
    have hceil : (M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ) ≤
        (Nat.ceil ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) : ℝ) := Nat.le_ceil _
    have hmul := mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg (p.uStar n))
    have hcancel : (p.uStar n : ℝ) *
        ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) = (M n) ^ (1 / 200 : ℝ) := by
      field_simp [ne_of_gt huR]
    have hmul' : (M n) ^ (1 / 200 : ℝ) ≤
        (p.uStar n : ℝ) * (Nat.ceil ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) : ℝ) := by
      calc
        (M n) ^ (1 / 200 : ℝ) =
            (p.uStar n : ℝ) * ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) := hcancel.symm
        _ ≤ (p.uStar n : ℝ) *
            (Nat.ceil ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) : ℝ) := hmul
    have hk : (p.kStar n : ℝ) =
        (p.uStar n : ℝ) *
          (Nat.ceil ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) : ℝ) := by
      simp [Params5.kStar, hu.ne', M]
    exact hk ▸ hmul'
  have hlogN : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ Real.log (M n) / p.alpha := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hpowle : (n : ℝ) ^ p.alpha ≤ M n := by
      dsimp [M, Params5.m]
      exact Nat.le_ceil _
    have hlogle : p.alpha * Real.log (n : ℝ) ≤ Real.log (M n) := by
      calc
        p.alpha * Real.log (n : ℝ) = Real.log ((n : ℝ) ^ p.alpha) := by
          rw [Real.log_rpow hnpos]
        _ ≤ Real.log (M n) := Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hpowle
    exact (le_div_iff₀ p.halpha.1).2 (by nlinarith [hlogle])
  have huStarUpper : ∀ᶠ n : ℕ in atTop,
      (p.uStar n : ℝ) ≤ (M n) ^ (1 / 200 : ℝ) := by
    have hsmall := hlogDiv (1 / 200 : ℝ) (by norm_num)
    have hsmall' : ∀ᶠ n : ℕ in atTop,
        Real.log (M n) / (M n) ^ (1 / 200 : ℝ) ≤ 1 / (2 * p.eta) := by
      filter_upwards [hsmall.eventually (Iio_mem_nhds (by positivity : 0 < (1 / (2 * p.eta) : ℝ)))]
        with n hn
      exact hn.le
    have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp hM
    filter_upwards [hsmall', hpow.eventually_ge_atTop (2 * (p.q0 : ℝ)),
      hM.eventually_ge_atTop 1] with n hs hq hMn
    have hMpos : 0 < M n := lt_of_lt_of_le (by norm_num) hMn
    have hlog : 0 ≤ Real.log (M n) := Real.log_nonneg hMn
    have hpowpos : 0 < (M n) ^ (1 / 200 : ℝ) := Real.rpow_pos_of_pos hMpos _
    have hqpos : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
    have hlogBound' : Real.log (M n) ≤
        (1 / (2 * p.eta)) * (M n) ^ (1 / 200 : ℝ) := (div_le_iff₀ hpowpos).mp hs
    have hlogBound : Real.log (M n) ≤ (M n) ^ (1 / 200 : ℝ) / (2 * p.eta) := by
      calc
        _ ≤ (1 / (2 * p.eta)) * (M n) ^ (1 / 200 : ℝ) := hlogBound'
        _ = (M n) ^ (1 / 200 : ℝ) / (2 * p.eta) := by ring
    have hetaLog : p.eta * Real.log (M n) ≤ (M n) ^ (1 / 200 : ℝ) / 2 := by
      calc
        p.eta * Real.log (M n) ≤ p.eta * ((M n) ^ (1 / 200 : ℝ) / (2 * p.eta)) :=
          mul_le_mul_of_nonneg_left hlogBound p.heta.1.le
        _ = (M n) ^ (1 / 200 : ℝ) / 2 := by field_simp [ne_of_gt p.heta.1]
    have hq' : 2 * (p.q0 : ℝ) ≤ (M n) ^ (1 / 200 : ℝ) := by simpa using hq
    have hqBound : (p.q0 : ℝ) ≤ (M n) ^ (1 / 200 : ℝ) / 2 := by nlinarith [hq']
    have huEq : (p.uStar n : ℝ) = (p.q0 : ℝ) *
        (Nat.ceil (p.eta * Real.log (M n) / (p.q0 : ℝ)) : ℝ) := by
      simp [Params5.uStar, roundedSegments5, M]
    have harg : 0 ≤ p.eta * Real.log (M n) / (p.q0 : ℝ) :=
      div_nonneg (mul_nonneg p.heta.1.le hlog) hqpos.le
    have hceil := Nat.ceil_lt_add_one harg
    rw [huEq]
    calc
      (p.q0 : ℝ) * (Nat.ceil (p.eta * Real.log (M n) / (p.q0 : ℝ)) : ℝ) ≤
          (p.q0 : ℝ) * (p.eta * Real.log (M n) / (p.q0 : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hceil.le hqpos.le
      _ = p.eta * Real.log (M n) + (p.q0 : ℝ) := by
        field_simp [ne_of_gt hqpos]
      _ ≤ (M n) ^ (1 / 200 : ℝ) := by linarith
  have hkStarUpper : ∀ᶠ n : ℕ in atTop,
      (p.kStar n : ℝ) ≤ 2 * (M n) ^ (1 / 200 : ℝ) := by
    filter_upwards [huPos, huStarUpper] with n hu hU
    have huR : 0 < (p.uStar n : ℝ) := by exact_mod_cast hu
    have harg : 0 ≤ (M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ) :=
      div_nonneg (Real.rpow_nonneg (by positivity) _) huR.le
    have hceil := Nat.ceil_lt_add_one harg
    have hkEq : (p.kStar n : ℝ) = (p.uStar n : ℝ) *
        (Nat.ceil ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) : ℝ) := by
      simp [Params5.kStar, hu.ne', M]
    rw [hkEq]
    calc
      (p.uStar n : ℝ) *
          (Nat.ceil ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ)) : ℝ) ≤
          (p.uStar n : ℝ) * ((M n) ^ (1 / 200 : ℝ) / (p.uStar n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hceil.le huR.le
      _ = (M n) ^ (1 / 200 : ℝ) + (p.uStar n : ℝ) := by
        field_simp [ne_of_gt huR]
      _ ≤ 2 * (M n) ^ (1 / 200 : ℝ) := by linarith
  have hpoolUpper : ∀ᶠ n : ℕ in atTop,
      (p.poolSize n : ℝ) ≤ (2 * Real.exp (p.Kh * (p.q0 : ℝ)) + 1) *
        (M n) ^ (15 / 1000 : ℝ) := by
    have hKhEta : p.Kh * p.eta = 1 / 100 := by
      change Kh * eta = 1 / 100
      nlinarith [hetaProduct]
    filter_upwards [huPos, huStarUpper, hkStarUpper, hM.eventually_ge_atTop 1]
      with n hu hU hk hMn
    have huR : 0 < (p.uStar n : ℝ) := by exact_mod_cast hu
    have hMpos : 0 < M n := lt_of_lt_of_le (by norm_num) hMn
    have hpowPos : 0 < (M n) ^ (1 / 200 : ℝ) := Real.rpow_pos_of_pos hMpos _
    have huBound : (p.uStar n : ℝ) ≤ p.eta * Real.log (M n) + (p.q0 : ℝ) := by
      have huEq : (p.uStar n : ℝ) = (p.q0 : ℝ) *
          (Nat.ceil (p.eta * Real.log (M n) / (p.q0 : ℝ)) : ℝ) := by
        simp [Params5.uStar, roundedSegments5, M]
      have hqpos : 0 < (p.q0 : ℝ) := by exact_mod_cast p.hq0.1
      have harg : 0 ≤ p.eta * Real.log (M n) / (p.q0 : ℝ) :=
        div_nonneg (mul_nonneg p.heta.1.le (Real.log_nonneg hMn)) hqpos.le
      rw [huEq]
      calc
        (p.q0 : ℝ) * (Nat.ceil (p.eta * Real.log (M n) / (p.q0 : ℝ)) : ℝ) ≤
            (p.q0 : ℝ) * (p.eta * Real.log (M n) / (p.q0 : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one harg).le hqpos.le
        _ = p.eta * Real.log (M n) + (p.q0 : ℝ) := by
          field_simp [ne_of_gt hqpos]
    have hKu : p.Kh * (p.uStar n : ℝ) ≤
        (1 / 100 : ℝ) * Real.log (M n) + p.Kh * (p.q0 : ℝ) := by
      calc
        _ ≤ p.Kh * (p.eta * Real.log (M n) + (p.q0 : ℝ)) :=
          mul_le_mul_of_nonneg_left huBound p.hKh.le
        _ = _ := by rw [mul_add, ← hKhEta]; ring
    have hExp : Real.exp (p.Kh * (p.uStar n : ℝ)) ≤
        Real.exp (p.Kh * (p.q0 : ℝ)) * (M n) ^ (1 / 100 : ℝ) := by
      have hpowExp : Real.exp ((1 / 100 : ℝ) * Real.log (M n)) =
          (M n) ^ (1 / 100 : ℝ) := by
        rw [mul_comm]
        exact (Real.rpow_def_of_pos hMpos (1 / 100 : ℝ)).symm
      calc
        _ ≤ Real.exp ((1 / 100 : ℝ) * Real.log (M n) + p.Kh * (p.q0 : ℝ)) :=
          Real.exp_le_exp.mpr hKu
        _ = Real.exp (p.Kh * (p.q0 : ℝ)) * (M n) ^ (1 / 100 : ℝ) := by
          rw [Real.exp_add, hpowExp]
          ring
    have hpowAdd : (M n) ^ (1 / 100 : ℝ) * (M n) ^ (1 / 200 : ℝ) =
        (M n) ^ (15 / 1000 : ℝ) := by
      rw [← Real.rpow_add hMpos]
      congr 1
      norm_num
    have hpoolEq : (p.poolSize n : ℝ) = (p.uStar n : ℝ) *
        (Nat.ceil (Real.exp (p.Kh * (p.uStar n : ℝ)) * (p.kStar n : ℝ) /
          (p.uStar n : ℝ)) : ℝ) := by
      simp [Params5.poolSize, hu.ne', M]
    have hceilArg : 0 ≤ Real.exp (p.Kh * (p.uStar n : ℝ)) *
        (p.kStar n : ℝ) / (p.uStar n : ℝ) :=
      div_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)) huR.le
    have hceil := Nat.ceil_lt_add_one hceilArg
    rw [hpoolEq]
    calc
      (p.uStar n : ℝ) *
          (Nat.ceil (Real.exp (p.Kh * (p.uStar n : ℝ)) * (p.kStar n : ℝ) /
            (p.uStar n : ℝ)) : ℝ) ≤
          (p.uStar n : ℝ) *
            (Real.exp (p.Kh * (p.uStar n : ℝ)) * (p.kStar n : ℝ) /
              (p.uStar n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hceil.le huR.le
      _ = Real.exp (p.Kh * (p.uStar n : ℝ)) * (p.kStar n : ℝ) +
          (p.uStar n : ℝ) := by
        field_simp [ne_of_gt huR]
      _ ≤ Real.exp (p.Kh * (p.q0 : ℝ)) * (M n) ^ (1 / 100 : ℝ) *
            (2 * (M n) ^ (1 / 200 : ℝ)) + (M n) ^ (1 / 200 : ℝ) := by
        have hExpR : 0 ≤ Real.exp (p.Kh * (p.q0 : ℝ)) * (M n) ^ (1 / 100 : ℝ) := by
          positivity
        exact add_le_add
          (mul_le_mul hExp hk (Nat.cast_nonneg _) hExpR)
          hU
      _ ≤ (2 * Real.exp (p.Kh * (p.q0 : ℝ)) + 1) * (M n) ^ (15 / 1000 : ℝ) := by
        have hsmall : (M n) ^ (1 / 200 : ℝ) ≤ (M n) ^ (15 / 1000 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hMn (by norm_num)
        have hcoeff : 0 ≤ 2 * Real.exp (p.Kh * (p.q0 : ℝ)) := by positivity
        calc
          _ = 2 * Real.exp (p.Kh * (p.q0 : ℝ)) *
                ((M n) ^ (1 / 100 : ℝ) * (M n) ^ (1 / 200 : ℝ)) +
                (M n) ^ (1 / 200 : ℝ) := by ring
          _ = 2 * Real.exp (p.Kh * (p.q0 : ℝ)) * (M n) ^ (15 / 1000 : ℝ) +
                (M n) ^ (1 / 200 : ℝ) := by rw [hpowAdd]
          _ ≤ 2 * Real.exp (p.Kh * (p.q0 : ℝ)) * (M n) ^ (15 / 1000 : ℝ) +
                (M n) ^ (15 / 1000 : ℝ) := add_le_add le_rfl hsmall
          _ = (2 * Real.exp (p.Kh * (p.q0 : ℝ)) + 1) *
                (M n) ^ (15 / 1000 : ℝ) := by ring
  refine ⟨p, ?_, ?_⟩
  · dsimp [Params5.ScaleRelations]
    refine ⟨?_, ?_, ?_, ?_⟩
    · let f : ℕ → ℝ := fun n =>
        (p.T n : ℝ) * (p.poolSize n : ℝ) / (p.J n : ℝ)
      let C : ℝ := 2 * Real.exp (p.Kh * (p.q0 : ℝ)) + 1
      have hdecay : Tendsto (fun n => (M n) ^ (-(17 / 500 : ℝ))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17 / 500)).comp hM
      have hlim : Tendsto (fun n => (4 * C) * (M n) ^ (-(17 / 500 : ℝ)))
          atTop (nhds 0) := by simpa using hdecay.const_mul (4 * C)
      have hpowProd (n : ℕ) (hn : 0 < M n) :
          (M n) ^ (1 / 1000 : ℝ) * (M n) ^ (15 / 1000 : ℝ) =
            (M n) ^ (16 / 1000 : ℝ) := by
        rw [← Real.rpow_add hn]
        congr 1
        norm_num
      have hbound : ∀ᶠ n : ℕ in atTop,
          f n ≤ (4 * C) * (M n) ^ (-(17 / 500 : ℝ)) := by
        filter_upwards [hTupper, hpoolUpper, hJlower, hM.eventually_ge_atTop 1]
          with n ht hp hj hMn
        have hMpos : 0 < M n := lt_of_lt_of_le (by norm_num) hMn
        have hMsmall : 0 < (M n) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hMpos _
        have hJpos : 0 < (p.J n : ℝ) :=
          lt_of_lt_of_le (div_pos hMsmall (by norm_num)) hj
        have hCpos : 0 ≤ C := by positivity
        have hp' : (p.poolSize n : ℝ) ≤ C * (M n) ^ (15 / 1000 : ℝ) := by
          simpa [C] using hp
        have hnum : (p.T n : ℝ) * (p.poolSize n : ℝ) ≤
            (2 * C) * (M n) ^ (16 / 1000 : ℝ) := by
          calc
            _ ≤ (2 * (M n) ^ (1 / 1000 : ℝ)) *
                  (C * (M n) ^ (15 / 1000 : ℝ)) :=
              mul_le_mul ht hp' (Nat.cast_nonneg _) (by positivity)
            _ = (2 * C) * ((M n) ^ (1 / 1000 : ℝ) *
                  (M n) ^ (15 / 1000 : ℝ)) := by ring
            _ = (2 * C) * (M n) ^ (16 / 1000 : ℝ) := by rw [hpowProd n hMpos]
        have hbase : (p.J n : ℝ) ≥ (M n) ^ (1 / 20 : ℝ) / 2 := hj
        have hnumNonneg : 0 ≤ (2 * C) * (M n) ^ (16 / 1000 : ℝ) := by positivity
        have hstep : f n ≤
            ((2 * C) * (M n) ^ (16 / 1000 : ℝ)) / ((M n) ^ (1 / 20 : ℝ) / 2) := by
          dsimp [f]
          calc
            _ ≤ ((2 * C) * (M n) ^ (16 / 1000 : ℝ)) / (p.J n : ℝ) :=
              div_le_div_of_nonneg_right hnum hJpos.le
            _ ≤ ((2 * C) * (M n) ^ (16 / 1000 : ℝ)) /
                  ((M n) ^ (1 / 20 : ℝ) / 2) :=
              div_le_div_of_nonneg_left hnumNonneg (div_pos hMsmall (by norm_num)) hbase
        have hpowSub : (M n) ^ (16 / 1000 : ℝ) / (M n) ^ (1 / 20 : ℝ) =
            (M n) ^ (-(17 / 500 : ℝ)) := by
          rw [← Real.rpow_sub hMpos]
          congr 1
          norm_num
        have hratio :
            ((2 * C) * (M n) ^ (16 / 1000 : ℝ)) /
                ((M n) ^ (1 / 20 : ℝ) / 2) =
              (4 * C) * (M n) ^ (-(17 / 500 : ℝ)) := by
          calc
            _ = (4 * C) * ((M n) ^ (16 / 1000 : ℝ) /
                  (M n) ^ (1 / 20 : ℝ)) := by ring
            _ = _ := by rw [hpowSub]
        exact hstep.trans_eq hratio
      have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n := by
        filter_upwards with n
        exact div_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        tendsto_const_nhds hlim hnonneg hbound
    · let f : ℕ → ℝ := fun n =>
        (p.T n : ℝ) * Real.log (n : ℝ) / (p.kStar n : ℝ)
      have hlim : Tendsto (fun n => (2 / p.alpha) * (Real.log (M n) / (M n) ^ (1 / 250 : ℝ)))
          atTop (nhds 0) := by
        simpa [Function.comp_def] using
          (hlogDiv (1 / 250 : ℝ) (by norm_num)).const_mul (2 / p.alpha)
      set_option maxHeartbeats 400000 in
      have hbound : ∀ᶠ n : ℕ in atTop,
          f n ≤ (2 / p.alpha) * (Real.log (M n) / (M n) ^ (1 / 250 : ℝ)) := by
        filter_upwards [hTupper, hkStarLower, hlogN, eventually_ge_atTop (1 : ℕ),
          hM.eventually_ge_atTop 1] with n ht hk hln hn hMn
        have hMpos : 0 < M n := lt_of_lt_of_le (by norm_num) hMn
        have hlogMnonneg : 0 ≤ Real.log (M n) := Real.log_nonneg hMn
        have hlogNnonneg : 0 ≤ Real.log (n : ℝ) := by
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from hn))
        have hstarPos : 0 < (p.kStar n : ℝ) := by
          exact lt_of_lt_of_le (Real.rpow_pos_of_pos hMpos _) hk
        have hdenPos : 0 < (M n) ^ (1 / 250 : ℝ) := Real.rpow_pos_of_pos hMpos _
        have hpowRel : (M n) ^ (1 / 1000 : ℝ) * (M n) ^ (1 / 250 : ℝ) =
            (M n) ^ (1 / 200 : ℝ) := by
          rw [← Real.rpow_add hMpos]
          congr 1
          norm_num
        have hnum := mul_le_mul ht hln hlogNnonneg (by positivity)
        have hnum' := mul_le_mul_of_nonneg_right hnum
          (Real.rpow_nonneg hMpos.le (1 / 250 : ℝ))
        have hcoeff : 0 ≤ (2 / p.alpha) * Real.log (M n) := by positivity
        have hright := mul_le_mul_of_nonneg_left hk hcoeff
        have hcross :
            (p.T n : ℝ) * Real.log (n : ℝ) * (M n) ^ (1 / 250 : ℝ) ≤
              ((2 / p.alpha) * Real.log (M n)) * (p.kStar n : ℝ) := by
          calc
            _ ≤ (2 * (M n) ^ (1 / 1000 : ℝ) * (Real.log (M n) / p.alpha)) *
                  (M n) ^ (1 / 250 : ℝ) := hnum'
            _ = ((2 / p.alpha) * Real.log (M n)) * (M n) ^ (1 / 200 : ℝ) := by
              calc
                _ = ((2 / p.alpha) * Real.log (M n)) *
                    ((M n) ^ (1 / 1000 : ℝ) * (M n) ^ (1 / 250 : ℝ)) := by ring
                _ = _ := by rw [hpowRel]
            _ ≤ _ := hright
        have hdiv := (div_le_div_iff₀ hstarPos hdenPos).2 hcross
        dsimp [f]
        calc
          _ ≤ ((2 / p.alpha) * Real.log (M n)) / (M n) ^ (1 / 250 : ℝ) := hdiv
          _ = (2 / p.alpha) * (Real.log (M n) / (M n) ^ (1 / 250 : ℝ)) := by ring
      have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n := by
        filter_upwards [eventually_ge_atTop (1 : ℕ), huPos] with n hn hu
        have hnlog : 0 ≤ Real.log (n : ℝ) := by
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from hn))
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hnlog)
          (by exact_mod_cast (Nat.zero_le (p.kStar n)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hnonneg hbound
    · let f : ℕ → ℝ := fun n =>
        (p.T n : ℝ) * Real.log (n : ℝ) / (M n) ^ (1 / 50 : ℝ)
      have hlim : Tendsto (fun n => (2 / p.alpha) * (Real.log (M n) / (M n) ^ (19 / 1000 : ℝ)))
          atTop (nhds 0) := by
        simpa [Function.comp_def] using
          (hlogDiv (19 / 1000 : ℝ) (by norm_num)).const_mul (2 / p.alpha)
      have hbound : ∀ᶠ n : ℕ in atTop,
          f n ≤ (2 / p.alpha) * (Real.log (M n) / (M n) ^ (19 / 1000 : ℝ)) := by
        filter_upwards [hTupper, hlogN, eventually_ge_atTop (1 : ℕ),
          hM.eventually_ge_atTop 1] with n ht hln hn hMn
        have hMpos : 0 < M n := lt_of_lt_of_le (by norm_num) hMn
        have hlogNnonneg : 0 ≤ Real.log (n : ℝ) := by
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from hn))
        have hdenPos : 0 < (M n) ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hMpos _
        have hsmallPos : 0 < (M n) ^ (19 / 1000 : ℝ) := Real.rpow_pos_of_pos hMpos _
        have hpowRel : (M n) ^ (1 / 1000 : ℝ) * (M n) ^ (19 / 1000 : ℝ) =
            (M n) ^ (1 / 50 : ℝ) := by
          rw [← Real.rpow_add hMpos]
          congr 1
          norm_num
        have hnum := mul_le_mul ht hln hlogNnonneg (by positivity)
        have hnum' := mul_le_mul_of_nonneg_right hnum
          (Real.rpow_nonneg hMpos.le (19 / 1000 : ℝ))
        have hcross :
            (p.T n : ℝ) * Real.log (n : ℝ) * (M n) ^ (19 / 1000 : ℝ) ≤
              ((2 / p.alpha) * Real.log (M n)) * (M n) ^ (1 / 50 : ℝ) := by
          calc
            _ ≤ (2 * (M n) ^ (1 / 1000 : ℝ) * (Real.log (M n) / p.alpha)) *
                  (M n) ^ (19 / 1000 : ℝ) := hnum'
            _ = ((2 / p.alpha) * Real.log (M n)) * (M n) ^ (1 / 50 : ℝ) := by
              calc
                _ = ((2 / p.alpha) * Real.log (M n)) *
                    ((M n) ^ (1 / 1000 : ℝ) * (M n) ^ (19 / 1000 : ℝ)) := by ring
                _ = _ := by rw [hpowRel]
        have hdiv := (div_le_div_iff₀ hdenPos hsmallPos).2 hcross
        dsimp [f]
        calc
          _ ≤ ((2 / p.alpha) * Real.log (M n)) / (M n) ^ (19 / 1000 : ℝ) := hdiv
          _ = (2 / p.alpha) * (Real.log (M n) / (M n) ^ (19 / 1000 : ℝ)) := by ring
      have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n := by
        filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
        have hnlog : 0 ≤ Real.log (n : ℝ) := by
          exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n from hn))
        exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hnlog)
          (Real.rpow_nonneg (by positivity) _)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hnonneg hbound
    · let f : ℕ → ℝ := fun n => (p.T n + p.J n : ℕ) / (p.s n : ℝ)
      have hdecay : Tendsto (fun n => (M n) ^ (-(49 / 1000 : ℝ))) atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 49 / 1000)).comp hM
      have hlim : Tendsto
          (fun n => (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) +
            (2 / p.Ks) * (Real.log (M n))⁻¹) atTop (nhds 0) :=
        by simpa using (hdecay.const_mul (4 / p.Ks)).add (hinvLog.const_mul (2 / p.Ks))
      have hbound : ∀ᶠ n : ℕ in atTop,
          f n ≤ (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) +
            (2 / p.Ks) * (Real.log (M n))⁻¹ := by
        filter_upwards [hTupper, hJlower, hsLower, hlogM.eventually_ge_atTop 1,
          hM.eventually_ge_atTop 1] with n ht hj hs hln hMn
        have hMpos : 0 < M n := lt_of_lt_of_le (by norm_num) hMn
        have hlogPos : 0 < Real.log (M n) := lt_of_lt_of_le zero_lt_one hln
        have hMfine : 0 < (M n) ^ (1 / 20 : ℝ) := Real.rpow_pos_of_pos hMpos _
        have hlowPos : 0 < p.Ks * ((M n) ^ (1 / 20 : ℝ) / 2) * Real.log (M n) :=
          mul_pos (mul_pos p.hKs (div_pos hMfine (by norm_num))) hlogPos
        let M001 : ℝ := (M n) ^ (1 / 1000 : ℝ)
        let M05 : ℝ := (M n) ^ (1 / 20 : ℝ)
        let U : ℝ := 2 * M001 + M05
        let L : ℝ := p.Ks * (M05 / 2) * Real.log (M n)
        have hnum : (p.T n + p.J n : ℝ) ≤ U := by
          have h := add_le_add ht (hJupper n)
          simpa only [Nat.cast_add, U, M001, M05] using h
        have hJlog : ((M n) ^ (1 / 20 : ℝ) / 2) * Real.log (M n) ≤
            (p.J n : ℝ) * Real.log (M n) :=
          mul_le_mul_of_nonneg_right hj hlogPos.le
        have hlow' : p.Ks * (((M n) ^ (1 / 20 : ℝ) / 2) * Real.log (M n)) ≤
            (p.s n : ℝ) := by
          have hs' := hs
          rw [mul_assoc] at hs'
          calc
            _ ≤ p.Ks * ((p.J n : ℝ) * Real.log (M n)) :=
              mul_le_mul_of_nonneg_left hJlog p.hKs.le
            _ ≤ (p.s n : ℝ) := hs'
        have hlow : L ≤ (p.s n : ℝ) := by
          dsimp [L]
          rw [mul_assoc]
          exact hlow'
        have hSpos : 0 < (p.s n : ℝ) := lt_of_lt_of_le hlowPos hlow
        have hM001nonneg : 0 ≤ M001 := Real.rpow_nonneg hMpos.le _
        have hM05nonneg : 0 ≤ M05 := Real.rpow_nonneg hMpos.le _
        have hU_nonneg : 0 ≤ U := by
          dsimp [U]
          exact add_nonneg (mul_nonneg (by norm_num) hM001nonneg) hM05nonneg
        have hcross : (p.T n + p.J n : ℝ) * L ≤ U * (p.s n : ℝ) := by
          calc
            _ ≤ U * L := mul_le_mul_of_nonneg_right hnum hlowPos.le
            _ ≤ U * (p.s n : ℝ) := mul_le_mul_of_nonneg_left hlow hU_nonneg
        have hcrossCast : ((p.T n + p.J n : ℕ) : ℝ) * L ≤ U * (p.s n : ℝ) := by
          simpa only [Nat.cast_add] using hcross
        have hbase : f n ≤ U / L := by
          dsimp [f]
          exact (div_le_div_iff₀ hSpos hlowPos).2 hcrossCast
        have hratio : U / L =
            (4 * ((M n) ^ (1 / 1000 : ℝ) / (M n) ^ (1 / 20 : ℝ)) + 2) /
              (p.Ks * Real.log (M n)) := by
          dsimp [U, L, M001, M05]
          field_simp [ne_of_gt p.hKs, ne_of_gt hMfine, ne_of_gt hlogPos]
          <;> ring
        have hpow : (M n) ^ (1 / 1000 : ℝ) / (M n) ^ (1 / 20 : ℝ) =
            (M n) ^ (-(49 / 1000 : ℝ)) := by
          have h := (Real.rpow_sub hMpos (1 / 1000 : ℝ) (1 / 20 : ℝ)).symm
          norm_num at h ⊢
          exact h
        have hinv : (Real.log (M n))⁻¹ ≤ 1 := by
          simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hln
        have hdivcoef : 0 ≤ (4 : ℝ) / p.Ks := div_nonneg (by norm_num) p.hKs.le
        have hpowcoef : 0 ≤ (M n) ^ (-(49 / 1000 : ℝ)) :=
          Real.rpow_nonneg hMpos.le (-(49 / 1000 : ℝ))
        have hcoef : 0 ≤ (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) :=
          mul_nonneg hdivcoef hpowcoef
        have hfirst : (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) *
              (Real.log (M n))⁻¹ ≤ (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) :=
          (mul_le_mul_of_nonneg_left hinv hcoef).trans_eq (by ring)
        have hsplit : (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) *
              (Real.log (M n))⁻¹ + (2 / p.Ks) * (Real.log (M n))⁻¹ =
            (4 * (M n) ^ (-(49 / 1000 : ℝ)) + 2) /
              (p.Ks * Real.log (M n)) := by
          field_simp [ne_of_gt p.hKs, ne_of_gt hlogPos]
          <;> ring
        calc
          f n ≤ U / L := hbase
          _ = (4 * ((M n) ^ (1 / 1000 : ℝ) / (M n) ^ (1 / 20 : ℝ)) + 2) /
                (p.Ks * Real.log (M n)) := hratio
          _ = (4 * (M n) ^ (-(49 / 1000 : ℝ)) + 2) /
                (p.Ks * Real.log (M n)) := by rw [hpow]
          _ = (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) *
                (Real.log (M n))⁻¹ + (2 / p.Ks) * (Real.log (M n))⁻¹ := hsplit.symm
          _ ≤ (4 / p.Ks) * (M n) ^ (-(49 / 1000 : ℝ)) +
                (2 / p.Ks) * (Real.log (M n))⁻¹ := by linarith [hfirst]
      have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n := by
        filter_upwards with n
        exact div_nonneg
          (by exact_mod_cast (Nat.zero_le (p.T n + p.J n)))
          (by exact_mod_cast (Nat.zero_le (p.s n)))
      set_option maxHeartbeats 400000 in
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hnonneg hbound
  · dsimp [ParamReq5.Holds]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change R.Kcap pre0 ≤ Kcap
      exact le_max_left _ _
    · change R.Kpp pre0 ≤ Kpp
      exact le_max_left _ _
    · change R.Kh pre0 ≤ Kh
      exact le_max_left _ _
    · change R.K1 pre1 ≤ K1
      exact le_max_left _ _
    · change R.K2 pre2 ≤ K2
      exact le_max_left _ _
    · change R.KD pre3 ≤ KD
      exact le_max_left _ _
    · change R.Ks pre4 ≤ Ks
      exact le_max_left _ _
    · change R.KB pre5 ≤ KB
      exact le_max_left _ _
    · change alpha ≤ R.alpha pre6
      calc
        alpha = min (R.alpha pre6 / 2) (1 / 100) := rfl
        _ ≤ R.alpha pre6 / 2 := min_le_left _ _
        _ ≤ R.alpha pre6 := div_le_self (R.alpha_pos pre6).le (by norm_num)

end
end HypercubeRamsey
