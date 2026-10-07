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

/-- The fixed constants and order of choices in D5.1. -/
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
  b : ℝ
  b0 : ℝ
  theta : ℝ
  sigma : ℝ
  zeta : ℝ
  hγ : 0 < γ ∧ γ < 1
  hK : 0 < K'
  hχ : 0 < χ
  ha0 : a 0 = 1 / 3
  ha_order : ∀ i j : Fin 9, i.val < j.val → a i < a j
  hgap : a 8 < tau0 ∧ tau0 < tau1 ∧ tau1 < Real.log 2
  hdelta : 0 < delta ∧ delta < min (tau0 - a 8) (tau1 - tau0) / 100
  hq0 : 0 < q0 ∧
    (2 / χ ^ 2) * (10 / 9 : ℝ) ^ q0 ≤ Real.exp (a 0 * q0)
  hKh : 0 < Kh
  heta : 0 < eta ∧ Kh * eta + 1 / 200 < 3 / 100
  hK1 : 0 < K1
  hK2 : 0 < K2
  hKD : 0 < KD
  hKs : 0 < Ks
  hKB : 0 < KB
  hnu0 : 0 < nu0
  hnu1 : tau0 / tau1 < nu1 ∧ nu1 + nu0 < 1
  halpha : 0 < alpha ∧ alpha < 1 / 50
  hrho : 0 < rho ∧ 2 * rho < 1 / 2
  hEntropy : binaryEntropy5 (2 * rho) < Real.log 2 - tau1
  hb : 0 < b0 ∧ b0 < b ∧ b < alpha / 1000
  htheta : 9 / 10 < theta ∧ theta < 1
  hsigmazeta : 0 < sigma ∧ 0 < zeta

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

/-- D5.1: the parameter order can be chosen, including the eventual scale inequalities. -/
theorem D5_1_params (γ K' χ : ℝ) (hγ : 0 < γ) (hγ' : γ < 1)
    (hK : 0 < K') (hχ : 0 < χ) :
    ∃ p : Params5 γ K' χ, p.ScaleRelations := by
  sorry

end
end HypercubeRamsey
