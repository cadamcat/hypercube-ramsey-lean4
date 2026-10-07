import HypercubeRamsey.S06.Params

/-!
# Section 6 vocabulary: keys, named parents, types, and the mixture laws

L6.1-Defs, part 1 (06:31–40, 06:78–123).  Coarse keys `h = (w, int/bdy)`, the key relation `C(h)`, named
primary variables (`P_(w,int) = A_w`, `P_(w,bdy) = V₀`), hidden keys `ℓ = (h, t)`, even-role types, and the
second-side mixture `Π`, its tag posterior `η_y`, the first-side law `B_y`, and the restricted base-tag law.
Zero-safe normalizations use a fixed fallback point (06:145–147).
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-! ### Finite normalization helpers -/

/-- Normalize a weight function (negative parts clipped); the fixed point `ω₀` is used when the mass is zero
(06:145–147: fixed local fallbacks on undefined branches). -/
def normalize6 {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (ω₀ : Ω) : FinProb Ω :=
  if h : 0 < ∑ ω, max 0 (f ω) then
    { w := fun ω => max 0 (f ω) / ∑ ω', max 0 (f ω')
      nonneg := fun ω => div_nonneg (le_max_left _ _) h.le
      sum_eq_one := by rw [← Finset.sum_div]; exact div_self h.ne' }
  else
    { w := fun ω => if ω = ω₀ then 1 else 0
      nonneg := fun ω => by split_ifs <;> norm_num
      sum_eq_one := by simp }

/-- A law restricted to a set, with the fallback point when the set has zero mass. -/
def restrictOr6 {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) (ω₀ : Ω) : FinProb Ω :=
  normalize6 (fun ω => if A ω then P.w ω else 0) ω₀

/-- A zero-safe likelihood ratio; posterior ratios are only used on their reference support. -/
def safeRatio6 (a b : ℝ) : ℝ := if b = 0 then 0 else a / b

/-- Point mass on a finite type. -/
def pointMass6 {Ω : Type*} [Fintype Ω] (a : Ω) : FinProb Ω where
  w b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-! ### Coarse keys and the key relation (06:78–91) -/

inductive KeyFlag6 where
  | interior
  | boundary
  deriving DecidableEq

instance : Fintype KeyFlag6 := by
  refine ⟨{KeyFlag6.interior, KeyFlag6.boundary}, ?_⟩
  intro x
  cases x <;> simp

instance : Inhabited KeyFlag6 := ⟨KeyFlag6.interior⟩

abbrev CoarseKey6 (W : Type*) := W × KeyFlag6

/-- The coarse relation connects each key to itself, the two keys at a bin, and boundary keys at adjacent
bins (06:86–89). -/
def keyAdjacent6 {W : Type*} (binAdjacent : W → W → Prop) (a b : CoarseKey6 W) : Prop :=
  a = b ∨ a.1 = b.1 ∨ (a.2 = .boundary ∧ b.2 = .boundary ∧ binAdjacent a.1 b.1)

/-- `C(h)`: all neighbours of `h` in the key relation, with `h` itself (06:88–89). -/
def keyNeighborhood6 {W : Type*} [Fintype W] (binAdjacent : W → W → Prop) (h : CoarseKey6 W) :
    Finset (CoarseKey6 W) :=
  Finset.univ.filter (keyAdjacent6 binAdjacent h)

/-! ### Named parent variables (06:78–86, 06:155–157) -/

/-- The name of a parent variable: `V₀` or a candidate `A_w`.  Equal realized values never merge names. -/
inductive ParentName6 (W : Type*) where
  | initial
  | candidate (w : W)
  deriving DecidableEq

/-- `P_h`: `A_w` at `(w,int)`, `V₀` at `(w,bdy)` (06:80–83). -/
def primaryName6 {W : Type*} (h : CoarseKey6 W) : ParentName6 W :=
  match h.2 with
  | .interior => .candidate h.1
  | .boundary => .initial

/-- `P*_h`: the other member of `{A_w, V₀}` (06:84). -/
def otherPrimaryName6 {W : Type*} (h : CoarseKey6 W) : ParentName6 W :=
  match h.2 with
  | .interior => .initial
  | .boundary => .candidate h.1

/-- Parent values `(V₀, A)`. -/
abbrev Par6 (W : Type*) (N : ℕ) := Fin N × (W → Fin N)

/-- The value of a named parent. -/
def Par6.val {W : Type*} {N : ℕ} (pv : Par6 W N) : ParentName6 W → Fin N
  | .initial => pv.1
  | .candidate w => pv.2 w

/-- Replace the value of one named parent; all formulas below are re-evaluated at the new value (06:184–187
of Section 5, 06:395–396). -/
def Par6.set {W : Type*} [DecidableEq W] {N : ℕ} (pv : Par6 W N) (nm : ParentName6 W) (y : Fin N) :
    Par6 W N :=
  match nm with
  | .initial => (y, pv.2)
  | .candidate w => (pv.1, Function.update pv.2 w y)

/-! ### Hidden keys, modes and types (06:106–123) -/

/-- A hidden key `ℓ = (h, t)` (06:107). -/
abbrev HiddenKey6 (W : Type*) (m : ℕ) := CoarseKey6 W × CubeVertex m

inductive Mode6 where
  | low
  | high
  deriving DecidableEq

instance : Fintype Mode6 := by
  refine ⟨{Mode6.low, Mode6.high}, ?_⟩
  intro x
  cases x <;> simp

/-- An even-role type: its key `h`, its mode, its severity `j` (retained for low types, `0` at high), and its
observation list `S` (06:118–122).  A high type carries no sign beyond its list. -/
abbrev Type6 (W : Type*) (m : ℕ) := CoarseKey6 W × Mode6 × Fin (m + 1) × Finset (HiddenKey6 W m)

namespace Type6

variable {W : Type*} {m : ℕ}

def key (β : Type6 W m) : CoarseKey6 W := β.1
def mode (β : Type6 W m) : Mode6 := β.2.1
def sev (β : Type6 W m) : ℕ := β.2.2.1.val
def obs (β : Type6 W m) : Finset (HiddenKey6 W m) := β.2.2.2

/-- `u_β = j + 1` at low, `1` at high (06:123). -/
def u (β : Type6 W m) : ℕ :=
  match β.mode with
  | .low => β.sev + 1
  | .high => 1

end Type6

/-- Severity as an element of `Fin (m+1)` (severities never exceed `m`). -/
def sevFin6 (m j : ℕ) : Fin (m + 1) := ⟨min j m, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Low observation list: `(s,t)` for `s ∈ C(h)`, and `(h, t^a)` for `a ∈ F` (06:120). -/
def lowObservations6 {W : Type*} [Fintype W] {m : ℕ} (binAdjacent : W → W → Prop)
    (h : CoarseKey6 W) (t : CubeVertex m) (F : Finset (Fin m)) : Finset (HiddenKey6 W m) :=
  (keyNeighborhood6 binAdjacent h).image (fun s => (s, t)) ∪
    F.image (fun a => (h, Function.update t a (!t a)))

/-- High observation list: `(h,t)` when `j = J+1`, empty otherwise (06:121). -/
def highObservations6 {W : Type*} {m : ℕ} (h : CoarseKey6 W) (t : CubeVertex m) (j J : ℕ) :
    Finset (HiddenKey6 W m) :=
  if j = J + 1 then {(h, t)} else ∅

/-- The type of an even position with key `h`, sign `t`, flippable set `F`, severity `j` (06:118–123). -/
def makeType6 {W : Type*} [Fintype W] {m : ℕ} (binAdjacent : W → W → Prop)
    (h : CoarseKey6 W) (t : CubeVertex m) (F : Finset (Fin m)) (j J : ℕ) : Type6 W m :=
  if j ≤ J then (h, .low, sevFin6 m j, lowObservations6 binAdjacent h t F)
  else (h, .high, 0, highObservations6 h t j J)

/-! ### Mixture and posterior vocabulary (06:31–40, 06:93–104) -/

/-- The tag law `Λ` as a finite probability. -/
def tagLaw6 {N : ℕ} (M : TagMix N) : FinProb M.ι where
  w := M.Λ
  nonneg := M.Λ_nonneg
  sum_eq_one := M.Λ_sum

/-- The second-side mixture `Π = ∑ Λ(i) ν_i` (06:33). -/
def secondMixture6 {N : ℕ} (M : TagMix N) : Law N :=
  Law.mix (tagLaw6 M) M.ν

/-- The tag posterior `η_y(i) = Λ(i)ν_i(y)/Π(y)`, with fallback `Λ` when `Π(y) = 0` (06:34). -/
def tagPosterior6 {N : ℕ} (M : TagMix N) (y : Fin N) : FinProb M.ι :=
  if hy : 0 < (secondMixture6 M).w y then
    { w := fun i => M.Λ i * (M.ν i).w y / (secondMixture6 M).w y
      nonneg := fun i => div_nonneg (mul_nonneg (M.Λ_nonneg i) ((M.ν i).nonneg y)) hy.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt hy) }
  else tagLaw6 M

/-- `B_y = ∑ η_y(i) μ_i` (06:35). -/
def broadLaw6 {N : ℕ} (M : TagMix N) (y : Fin N) : Law N :=
  Law.mix (tagPosterior6 M y) M.μ

/-- The base-tag law `T₀`: `η_{P}` restricted to tags whose first law sees the opposite primary with
degree `≥ c₁`, fallback tag off the support (06:93–95). -/
def baseTagLaw6 {N : ℕ} (M : TagMix N) (E : Fin N → Fin N → Prop) (G : Colour)
    (parent opposite : Fin N) (fallback : M.ι) : FinProb M.ι :=
  restrictOr6 (tagPosterior6 M parent) (fun i => c₁ ≤ colDeg E G (M.μ i) opposite) fallback

/-- `Π'` restricted to the relation partners of `y`, with a fixed fallback (06:61–63). -/
def partnerLaw6 {N : ℕ} (piPrime : Law N) (related : Fin N → Fin N → Prop) (y fallback : Fin N) :
    Law N :=
  restrictOr6 piPrime (related y) fallback

end

end S06
end HypercubeRamsey
