import HypercubeRamsey.S05.Defs

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
  sorry

end
end HypercubeRamsey
