import HypercubeRamsey.S06.Context

/-!
# The raw Section 6 experiment through the hidden scalars, and the Step 1 and Step 2 objects

L6.1-Defs, part 2 (06:60–65, 06:93–157, 06:165–226).  Raw order (06:135–140):
`V₀ → (A_w, I_(w,int), I_(w,bdy))_w → (Z_ℓ)_ℓ → centre tuples`.

* `V₀ ~ Π'|_{S₀}`; given `V₀`, the `A_w` are iid from `Π'` restricted to the partners of `V₀`.
* Given the parents, independent base tags `I_h ~ T₀^h = η_{P_h}` restricted to `d_G(μ_i, P*_h) ≥ c₁`.
* Given the base, independent hidden scalars `Z_ℓ ~ π_h` (`ℓ = (h,t)`): at `(w,int)` the posterior of `A_w`
  given `V₀` and `(I_s)_{s ∈ C(h)}`; at `(w,bdy)` the posterior of `V₀` given the candidates `A_u` at the bins
  of `C(h)` and `(I_s)_{s ∈ C(h)}`.  `π_{ℓ,-s}` omits `I_s`; `π_ℓ(·; i)` replaces `I_s` by `i`.
* Step 2: for a type `β` at key `h` with list `S`, the gate `G_β` (Step 1 ratio comparisons for deleting `I_h`,
  computed with the alternative tag), the integrand against `T₀^h`, the masses `m_S`, `m_{S−ℓ}`, and the
  normalized laws `T_β`, `T_{β,−ℓ}`.
* A centre tuple of type `β` is a fresh tag `i ~ T_β` and `k` labels iid from `μ_i` conditioned to hit every
  required named variable (06:125–133).

Every posterior uses the raw experiment and only its listed observations; replacing a named variable
re-evaluates every later formula (06:145–157).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

namespace Ctx6

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-! ### Sample spaces -/

/-- Coarse base data `(A, I)`: a candidate at every bin and a base tag at every key. -/
abbrev Coarse : Type := (X.Bin → Fin N) × (X.Key → X.ι)

/-- Base data `(V₀, A, I)`. -/
abbrev Base : Type := Fin N × X.Coarse

/-- Hidden scalars `Z`. -/
abbrev Hid : Type := X.HKey → Fin N

/-- Histories through the hidden scalars. -/
abbrev Hist : Type := X.Base × X.Hid

instance instFintypeCoarse : Fintype X.Coarse := inferInstanceAs (Fintype ((X.Bin → Fin N) × (X.Key → X.ι)))
instance instDecEqCoarse : DecidableEq X.Coarse := inferInstanceAs (DecidableEq ((X.Bin → Fin N) × (X.Key → X.ι)))
instance instFintypeBase : Fintype X.Base := inferInstanceAs (Fintype (Fin N × X.Coarse))
instance instDecEqBase : DecidableEq X.Base := inferInstanceAs (DecidableEq (Fin N × X.Coarse))
instance instFintypeHid : Fintype X.Hid := inferInstanceAs (Fintype (X.HKey → Fin N))
instance instDecEqHid : DecidableEq X.Hid := inferInstanceAs (DecidableEq (X.HKey → Fin N))
instance instFintypeHist : Fintype X.Hist := inferInstanceAs (Fintype (X.Base × X.Hid))
instance instDecEqHist : DecidableEq X.Hist := inferInstanceAs (DecidableEq (X.Base × X.Hid))

/-- Parent values of a base. -/
def parOf (b : X.Base) : Par6 X.Bin N := (b.1, b.2.1)

/-- Replace a named parent in a base (06:395–396). -/
def withPar (b : X.Base) (nm : ParentName6 X.Bin) (y : Fin N) : X.Base :=
  ((X.parOf b).set nm y |>.1, ((X.parOf b).set nm y).2, b.2.2)

/-- Replace a base tag (06:196). -/
def withTag (b : X.Base) (s : X.Key) (i : X.ι) : X.Base := (b.1, b.2.1, Function.update b.2.2 s i)

/-- Replace a hidden scalar in a history. -/
def withHid (H : X.Hist) (ℓ : X.HKey) (ξ : Fin N) : X.Hist := (H.1, Function.update H.2 ℓ ξ)

/-- Replace a named parent in a history (hidden values kept; their laws are re-evaluated by every formula). -/
def withParH (H : X.Hist) (nm : ParentName6 X.Bin) (ξ : Fin N) : X.Hist := (X.withPar H.1 nm ξ, H.2)

/-! ### Raw parent and base-tag laws (06:60–65, 06:93–104) -/

/-- The initial law `Π'|_{S₀}`. -/
def initLaw : Law N := restrictOr6 X.par.piPrime (· ∈ X.par.S₀) X.y₀

/-- The candidate law given `V₀ = v`: `Π'` restricted to the partners of `v`. -/
def candLaw (v : Fin N) : Law N := partnerLaw6 X.par.piPrime (related6 E G M) v X.y₀

/-- The base-tag law `T₀^h` at parent values `pv`. -/
def tagLawAt (pv : Par6 X.Bin N) (h : X.Key) : FinProb X.ι :=
  baseTagLaw6 M E G (pv.val (primaryName6 h)) (pv.val (otherPrimaryName6 h)) X.i₀

/-- The raw coarse law given `V₀ = v`: iid candidates, then independent base tags. -/
def coarseLaw (v : Fin N) : FinProb X.Coarse :=
  FinProb.bind (FinProb.pi fun _ : X.Bin => X.candLaw v) fun A => FinProb.pi (X.tagLawAt (v, A))

/-- The raw base law. -/
def baseLaw : FinProb X.Base := FinProb.bind X.initLaw X.coarseLaw

/-! ### Hidden-scalar posteriors (06:106–113) and Step 1 tests (06:165–189) -/

/-- The parent-posterior weight at key `h`, candidate `y` for the named primary `P_h`, observing the tags on
the key list `obs`: interior prior `cand(V₀)`; boundary prior `init` times the candidate likelihoods at the bins
of `C(h)`. -/
def hidWeight (b : X.Base) (h : X.Key) (obs : Finset X.Key) (y : Fin N) : ℝ :=
  let pv := (X.parOf b).set (primaryName6 h) y
  let prior : ℝ := match h.2 with
    | .interior => (X.candLaw b.1).w y
    | .boundary => X.initLaw.w y * ∏ u ∈ X.binsOf (X.C h), (X.candLaw y).w (b.2.1 u)
  prior * ∏ s ∈ obs, (X.tagLawAt pv s).w (b.2.2 s)

/-- `π_h` (`π_ℓ = π_h` for `ℓ = (h,t)`). -/
def hidPost (b : X.Base) (h : X.Key) : Law N := normalize6 (X.hidWeight b h (X.C h)) X.y₀

/-- `π_{h,-s}`: the observation `I_s` omitted. -/
def hidPostDel (b : X.Base) (h s : X.Key) : Law N := normalize6 (X.hidWeight b h ((X.C h).erase s)) X.y₀

/-- `π_h(·; I_s = i)`. -/
def hidPostRep (b : X.Base) (h s : X.Key) (i : X.ι) : Law N := X.hidPost (X.withTag b s i) h

/-- The hidden scalars are independent given the base. -/
def hidLaw (b : X.Base) : FinProb X.Hid := FinProb.pi fun ℓ => X.hidPost b ℓ.1

/-- The raw law of histories through the hidden scalars. -/
def rawHist : FinProb X.Hist := FinProb.bind X.baseLaw X.hidLaw

/-- Step 1 absolute cap `N max π_h ≤ n^{d₁}` (06:170). -/
def Step1Cap (b : X.Base) (h : X.Key) : Prop := ∀ y, (N : ℝ) * (X.hidPost b h).w y ≤ (n : ℝ) ^ d₁

/-- Step 1 deletion test `π_h ≤ n^{d₁} π_{h,-s}` (06:170–171). -/
def Step1Del (b : X.Base) (h s : X.Key) : Prop :=
  ∀ y, (X.hidPost b h).w y ≤ (n : ℝ) ^ d₁ * (X.hidPostDel b h s).w y

/-- All Step 1 tests at key `h`. -/
def Step1OK (b : X.Base) (h : X.Key) : Prop := X.Step1Cap b h ∧ ∀ s ∈ X.C h, X.Step1Del b h s

/-! ### Step 2: the tag of a centre tuple (06:191–226) -/

/-- The gate `G_β`: the Step 1 ratio comparisons for deleting `I_h` at the keys of `S`, computed with the
alternative value `i` (laws compared on all labels; no realized `Z` is read). -/
def tagGate (b : X.Base) (β : X.Ty) (i : X.ι) : Prop :=
  ∀ ℓ ∈ β.obs, ∀ y, (X.hidPostRep b ℓ.1 β.key i).w y ≤ (n : ℝ) ^ d₁ * (X.hidPostDel b ℓ.1 β.key).w y

/-- The Step 2 integrand against `T₀^h` on the list `S` (06:197–200). -/
def tagWeight (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) (i : X.ι) : ℝ :=
  (X.tagLawAt (X.parOf H.1) β.key).w i * (if X.tagGate H.1 β i then 1 else 0) *
    ∏ ℓ ∈ S, safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ)) ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ))

/-- `m_S`. -/
def tagMass (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) : ℝ := ∑ i, X.tagWeight H β S i

/-- The normalized Step 2 integrand. -/
def tagPost (H : X.Hist) (β : X.Ty) (S : Finset X.HKey) : FinProb X.ι := normalize6 (X.tagWeight H β S) X.i₀

/-- `T_β`. -/
def Tβ (H : X.Hist) (β : X.Ty) : FinProb X.ι := X.tagPost H β β.obs

/-- `T_{β,-ℓ}`. -/
def TβDel (H : X.Hist) (β : X.Ty) (ℓ : X.HKey) : FinProb X.ι := X.tagPost H β (β.obs.erase ℓ)

/-- The Step 2 threshold `n^{-δ₂ u_β}`. -/
def step2Thr (β : X.Ty) : ℝ := (n : ℝ) ^ (-(δ₂ * β.u))

/-- The Step 2 tests: positivity, `m_S ≥ n^{-δ₂u}`, `m_S/m_{S−ℓ} ≥ n^{-δ₂u}` (06:201). -/
def Step2Tests (H : X.Hist) (β : X.Ty) : Prop :=
  0 < X.tagMass H β β.obs ∧ X.step2Thr β ≤ X.tagMass H β β.obs ∧
    ∀ ℓ ∈ β.obs, X.step2Thr β * X.tagMass H β (β.obs.erase ℓ) ≤ X.tagMass H β β.obs

/-- A Step 2 failure: the true tag `I_h` passes the gate and a test fails (06:211). -/
def Step2Fail (H : X.Hist) (β : X.Ty) : Prop := X.tagGate H.1 β (H.1.2.2 β.key) ∧ ¬ X.Step2Tests H β

/-! ### Centre tuples (06:125–133, 06:150–157) -/

/-- The value of a named variable in a history. -/
def varVal (H : X.Hist) : X.Name → Fin N
  | .par p => (X.parOf H.1).val p
  | .hid ℓ => H.2 ℓ

/-- The labels hitting every listed named variable. -/
def reqNbhd (H : X.Hist) (S : Finset X.Name) : Finset (Fin N) :=
  Finset.univ.filter fun x => ∀ nm ∈ S, Hits E G x (X.varVal H nm)

/-- `μ_i` conditioned to hit every listed variable (fallback label off the gate). -/
def labelLaw (H : X.Hist) (S : Finset X.Name) (i : X.ι) : Law N :=
  restrictOr6 (M.μ i) (· ∈ X.reqNbhd H S) X.y₀

/-- A tagged tuple: one fresh tag and `k` labels; it is one primitive observation (06:150–152). -/
abbrev Tuple : Type := X.ι × (Fin X.k → Fin N)

instance instFintypeTuple : Fintype X.Tuple := inferInstanceAs (Fintype (X.ι × (Fin X.k → Fin N)))
instance instDecEqTuple : DecidableEq X.Tuple := inferInstanceAs (DecidableEq (X.ι × (Fin X.k → Fin N)))

/-- A tuple law: a tag from `T`, then `k` iid labels hitting the listed variables. -/
def tupleLawOn (H : X.Hist) (S : Finset X.Name) (T : FinProb X.ι) : FinProb X.Tuple :=
  FinProb.bind T fun i => FinProb.pi fun _ : Fin X.k => X.labelLaw H S i

/-- The raw tuple law of type `β` at history `H`. -/
def tupleLaw (H : X.Hist) (β : X.Ty) : FinProb X.Tuple := X.tupleLawOn H (reqNames6 β) (X.Tβ H β)

/-- Tuple data on an ID set: one tuple for every (ID, type) pair. -/
abbrev Data (Id : Type) [Fintype Id] [DecidableEq Id] : Type := Id × X.Ty → X.Tuple

instance instFintypeData (Id : Type) [Fintype Id] [DecidableEq Id] : Fintype (X.Data Id) :=
  inferInstanceAs (Fintype (Id × X.Ty → X.Tuple))

/-- Independent raw tuples at every (ID, type) pair given the history (06:141–144). -/
def dataLaw (Id : Type) [Fintype Id] [DecidableEq Id] (H : X.Hist) : FinProb (X.Data Id) :=
  FinProb.pi fun e : Id × X.Ty => X.tupleLaw H e.2

/-- The raw law of a history and independent tuple data. -/
def rawHistData (Id : Type) [Fintype Id] [DecidableEq Id] : FinProb (X.Hist × X.Data Id) :=
  FinProb.bind X.rawHist (X.dataLaw Id)

end Ctx6

end

end S06
end HypercubeRamsey
