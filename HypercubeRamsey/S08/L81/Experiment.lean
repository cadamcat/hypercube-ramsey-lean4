import HypercubeRamsey.S08.L81.Trim
import HypercubeRamsey.Tools.HeavyTrunc

/-!
# Lemma 8.1: the staged experiment

Source: `sections/08-…tex`, proof of Lemma 8.1 (lines 12–455); blueprint `research/blueprint/PART-B.md` §3.8.
Every object of the construction is an explicit finite formula of the context `D : Ctx η₀ β p h` (the trimmed
mixture `D.M` with tags `ι`, the colouring `D.E` in colour `D.G`, the dimension `D.n`):

* Step 2 (08:48–123): the tuple prior `R' = E_Λ ν_i^{⊗h}`, raw hidden tuples `Θ : Key → Y^h`, the posterior tag
  weight `η_g`, the hit masses `d_i^-, d_i^+` and their omitted variants, `A_g`, `Δ`, the centre law `S_g` (`tilt`),
  the single-anchor law `U_{g,i}` (`anchorU`) and the base gates;
* Step 4 (08:139–176): the candidate-independent references, the fixed-presentation likelihood `F_ξ` (`Fcand`), its
  marginal `M` (`Mden`), the product reference `Q` (`Qref`), `ε₀`, the tests `q_{g,k}` (`qgk`) and `q_L` (`qL`);
* Step 5 (08:178–225): the hidden events and the hidden law (raw tuples conditioned on avoiding them), positions,
  tags, activations and ties, candidate lists, bad lists, the greedy maximal disjoint family of bad lists at each odd
  cell, forbidden IDs, eligibility and the height selection rule in every slice;
* Steps 6–8 (08:227–300): the raw local experiment at a candidate, the realized presentation of an odd cell, its
  validity, the selection adjustment `F_ξ a_ξ` (`Gsel`), the selected posterior, the truncated row `p⁰` and the
  ordinary-anchor hit test giving the odd row `p`;
* Steps 9–12 (08:304–454): selected-anchor loads and their comparison `B_g`, the anchor events (denominator test,
  hit test, predictive alarms), the anchor law, odd and even column sums, the posterior even rows, the clock
  sampler's output property.

Rows are subprobabilities which vanish on invalid presentations, so their support statements hold everywhere.
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- An indicator is nonnegative. -/
theorem ind_nonneg (P : Prop) : (0 : ℝ) ≤ if P then 1 else 0 := by split_ifs <;> norm_num

/-- Greedy maximal disjoint subfamily of a list, in list order (08:208). -/
def greedy {α β : Type*} (ids : α → Finset β) (l : List α) : List α :=
  l.foldl (fun acc L => if Disjoint (ids L) (acc.foldr (fun L' s => ids L' ∪ s) ∅) then acc ++ [L] else acc) []

namespace Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

/-- Keys of the context. -/
abbrev KeyT := Key η₀ D.n
/-- Residual words of the context. -/
abbrev ResT := Res η₀ D.n
/-- Cells of the context. -/
abbrev CellT := Cell η₀ D.n
/-- Centre IDs in one slice: a residual location and a level (Lemma 3.8). -/
abbrev Loc := (hdP η₀ D.n).Loc
/-- Hidden tuples `Y^h`. -/
abbrev Tup := Fin h → Fin D.N
/-- Hidden histories: one tuple per grid key. -/
abbrev Hist := D.KeyT → D.Tup
/-- The cross keys of `g` as a type. -/
abbrev CrossSub (g : D.KeyT) := {u : D.KeyT // u ∈ crossKeys g}

/-! ## Step 2: hidden tuples, centre laws, anchor laws and base gates (08:48–123) -/

/-- The trimmed tag law. -/
def tagLaw : FinProb D.M.ι := ⟨D.M.Λ, D.M.Λ_nonneg, D.M.Λ_sum⟩

/-- The aggregate first law `E_Λ μ_i`. -/
def muBar : Law D.N := Law.mix D.tagLaw D.M.μ

/-- `R' = E_Λ ν_i^{⊗h}` (08:51). -/
def R' : FinProb D.Tup :=
  FinProb.map (FinProb.bind D.tagLaw fun i => FinProb.pi fun _ : Fin h => D.M.ν i) Prod.snd

/-- Raw hidden tuples, independent over keys. -/
def rawHidden : FinProb D.Hist := FinProb.pi fun _ => D.R'

/-- The posterior tag weight `η_g(i) = Λ(i) ν_i^{⊗h}(θ) / R'(θ)` of a tuple (`Λ` when `R'(θ) = 0`) (08:52). -/
def postW (θ : D.Tup) (i : D.M.ι) : ℝ :=
  if D.R'.w θ = 0 then D.M.Λ i else D.M.Λ i * (∏ j, (D.M.ν i).w (θ j)) / D.R'.w θ

theorem postW_nonneg (θ : D.Tup) (i : D.M.ι) : 0 ≤ D.postW θ i := by
  unfold postW
  split_ifs
  · exact D.M.Λ_nonneg i
  · exact div_nonneg (mul_nonneg (D.M.Λ_nonneg i) (Finset.prod_nonneg fun j _ => (D.M.ν i).nonneg _))
      (D.R'.nonneg θ)

/-- `x` hits every coordinate of `θ` in the chosen colour. -/
def hitsAll (x : Fin D.N) (θ : D.Tup) : Prop := ∀ j, Hits D.E D.G x (θ j)

/-- `x` hits every cross tuple `Θ_u`, `u ∈ E(g)`. -/
def crossHit (Θ : D.Hist) (g : D.KeyT) (x : Fin D.N) : Prop := ∀ u ∈ crossKeys g, D.hitsAll x (Θ u)

/-- `x` hits `Θ_u` for every `u ∈ E(g) ∪ {g}`. -/
def ownHit (Θ : D.Hist) (g : D.KeyT) (x : Fin D.N) : Prop := D.crossHit Θ g x ∧ D.hitsAll x (Θ g)

/-- `d_i^-` (08:56). -/
def dMinus (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : ℝ :=
  ∑ x, (D.M.μ i).w x * if D.crossHit Θ g x then 1 else 0

/-- `d_i^+` (08:58). -/
def dPlus (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : ℝ :=
  ∑ x, (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0

/-- `d_i^-` with the cross key `u₀` omitted (08:81). -/
def dOmit (Θ : D.Hist) (g u₀ : D.KeyT) (i : D.M.ι) : ℝ :=
  ∑ x, (D.M.μ i).w x * if ∀ u ∈ (crossKeys g).erase u₀, D.hitsAll x (Θ u) then 1 else 0

/-- `A_g = 2^{-h|E(g)|}` (08:60). -/
def AG (g : D.KeyT) : ℝ := ((2 : ℝ) ^ (h * (crossKeys g).card))⁻¹

/-- `Δ = e^{-n^{p/2}}` (08:60). -/
def Δ : ℝ := Real.exp (-(D.n : ℝ) ^ (p / 2))

/-- The lower cutoff `e^{-n^{2τ}}` (08:66). -/
def cut : ℝ := Real.exp (-(D.n : ℝ) ^ (2 * tau8 η₀))

/-- The cutoffs of `S_g` (08:66–67). -/
def GateOpen (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : Prop :=
  D.cut ≤ D.dMinus Θ g i ∧ (1 - D.Δ) * D.dMinus Θ g i ≤ D.dPlus Θ g i

theorem dMinus_nonneg (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : 0 ≤ D.dMinus Θ g i :=
  Finset.sum_nonneg fun x _ => mul_nonneg ((D.M.μ i).nonneg x) (ind_nonneg _)

/-- The unnormalized centre weight `η_g(i) d_i^- 1[cutoffs]` (08:65). -/
def tiltW (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : ℝ :=
  D.postW (Θ g) i * D.dMinus Θ g i * if D.GateOpen Θ g i then 1 else 0

theorem tiltW_nonneg (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : 0 ≤ D.tiltW Θ g i :=
  mul_nonneg (mul_nonneg (D.postW_nonneg _ i) (D.dMinus_nonneg Θ g i)) (ind_nonneg _)

/-- The normalizer `Z_g` (08:68). -/
def ZG (Θ : D.Hist) (g : D.KeyT) : ℝ := ∑ i, D.tiltW Θ g i

/-- The centre law `S_g` (08:65); the tag law is the fallback when `Z_g = 0`. -/
def tilt (Θ : D.Hist) (g : D.KeyT) : FinProb D.M.ι := normOr (D.tiltW Θ g) (D.tiltW_nonneg Θ g) D.tagLaw

/-- The single-anchor law `U_{g,i}` (08:70–73); `μ_i` is the fallback when `d_i^+ = 0`. -/
def anchorU (Θ : D.Hist) (g : D.KeyT) (i : D.M.ι) : Law D.N :=
  normOr (fun x => (D.M.μ i).w x * if D.ownHit Θ g x then 1 else 0)
    (fun x => mul_nonneg ((D.M.μ i).nonneg x) (ind_nonneg _)) (D.M.μ i)

/-- Base gate (G1) at `g`: `η_g ≤ e^{hn^β + n^{τ/2}} Λ` (08:78). -/
def Gate1 (Θ : D.Hist) (g : D.KeyT) : Prop :=
  ∀ i, D.postW (Θ g) i ≤ Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * D.M.Λ i

/-- Base gate (G2) at `g`: `.8A_g ≤ Z_g ≤ 1.2A_g` (08:79). -/
def Gate2 (Θ : D.Hist) (g : D.KeyT) : Prop :=
  (8 / 10 : ℝ) * D.AG g ≤ D.ZG Θ g ∧ D.ZG Θ g ≤ (12 / 10 : ℝ) * D.AG g

/-- Base gates (G3) and (G4) at `g` (08:80–81): `∫ d^- dη_g` and `∫ d^- dΛ` within a factor `1.1` of `A_g`, and
the same with any one cross key omitted, against `2^h A_g`. -/
def Gate34 (Θ : D.Hist) (g : D.KeyT) : Prop :=
  (D.AG g / (11 / 10) ≤ ∑ i, D.postW (Θ g) i * D.dMinus Θ g i ∧
    ∑ i, D.postW (Θ g) i * D.dMinus Θ g i ≤ (11 / 10) * D.AG g) ∧
  (D.AG g / (11 / 10) ≤ ∑ i, D.M.Λ i * D.dMinus Θ g i ∧
    ∑ i, D.M.Λ i * D.dMinus Θ g i ≤ (11 / 10) * D.AG g) ∧
  ∀ u₀ ∈ crossKeys g,
    ((2 : ℝ) ^ h * D.AG g / (11 / 10) ≤ ∑ i, D.postW (Θ g) i * D.dOmit Θ g u₀ i ∧
      ∑ i, D.postW (Θ g) i * D.dOmit Θ g u₀ i ≤ (11 / 10) * (2 : ℝ) ^ h * D.AG g) ∧
    ((2 : ℝ) ^ h * D.AG g / (11 / 10) ≤ ∑ i, D.M.Λ i * D.dOmit Θ g u₀ i ∧
      ∑ i, D.M.Λ i * D.dOmit Θ g u₀ i ≤ (11 / 10) * (2 : ℝ) ^ h * D.AG g)

/-- The base gates at `g` (08:76–81). -/
def BaseGates (Θ : D.Hist) (g : D.KeyT) : Prop := D.Gate1 Θ g ∧ D.Gate2 Θ g ∧ D.Gate34 Θ g

/-! ## Step 4: the fixed-presentation reference experiment (08:139–176) -/

/-- The base gates at `g` and at its grid neighbours (08:142). -/
def CandGate (Θ : D.Hist) (g : D.KeyT) : Prop := D.BaseGates Θ g ∧ ∀ u ∈ crossKeys g, D.BaseGates Θ u

/-- The internal reference `Λ(i) d_i^-`, normalized (08:144); it does not read `Θ_g`. -/
def refInt (Θ : D.Hist) (g : D.KeyT) : FinProb D.M.ι :=
  normOr (fun i => D.M.Λ i * D.dMinus Θ g i)
    (fun i => mul_nonneg (D.M.Λ_nonneg i) (D.dMinus_nonneg Θ g i)) D.tagLaw

/-- `x` hits the cross tuples of `u` other than `g`. -/
def omitHit (Θ : D.Hist) (u g : D.KeyT) (x : Fin D.N) : Prop := ∀ w ∈ (crossKeys u).erase g, D.hitsAll x (Θ w)

/-- The cross reference at `u ∈ E(g)`: `η_u(i) μ_i(x)` on hits of the cross tuples of `u` other than `g`,
normalized (08:147); it does not read `Θ_g`.  The fallback is `Λ(i) μ_i(x)`. -/
def refCross (Θ : D.Hist) (g u : D.KeyT) : FinProb (D.M.ι × Fin D.N) :=
  normOr (fun q => D.postW (Θ u) q.1 * (D.M.μ q.1).w q.2 * if D.omitHit Θ u g q.2 then 1 else 0)
    (fun q => mul_nonneg (mul_nonneg (D.postW_nonneg _ _) ((D.M.μ q.1).nonneg _)) (ind_nonneg _))
    (FinProb.bind D.tagLaw D.M.μ)

/-- Observed data at an odd cell of key `g`: internal tags indexed by `J` (absent entries `none`), and one pair
(tag, anchor) per cross key. -/
abbrev Obs (J : Type) (g : D.KeyT) := (J → Option D.M.ι) × (D.CrossSub g → D.M.ι × Fin D.N)

/-- `ε₀ = e^{-δhs log n}`, `δ = 10⁻⁴` (08:161). -/
def eps0 : ℝ := Real.exp (-((1 / 10000 : ℝ) * h * sC η₀ D.n * Real.log D.n))

/-- The internal density factor at candidate `ξ` (1 at an absent entry). -/
def intRatio (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (o : Option D.M.ι) : ℝ :=
  o.elim 1 fun i => (D.tilt (Function.update Θ g ξ) g).w i / (D.refInt Θ g).w i

/-- The cross density factor at candidate `ξ`. -/
def crossRatio (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (u : D.CrossSub g) (q : D.M.ι × Fin D.N) : ℝ :=
  (D.tilt (Function.update Θ g ξ) u.1).w q.1 * (D.anchorU (Function.update Θ g ξ) u.1 q.1).w q.2 /
    (D.refCross Θ g u.1).w q

theorem intRatio_nonneg (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (o : Option D.M.ι) :
    0 ≤ D.intRatio Θ g ξ o := by
  cases o with
  | none => simp [intRatio]
  | some i => exact div_nonneg ((D.tilt _ g).nonneg i) ((D.refInt Θ g).nonneg i)

theorem crossRatio_nonneg (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (u : D.CrossSub g) (q : D.M.ι × Fin D.N) :
    0 ≤ D.crossRatio Θ g ξ u q :=
  div_nonneg (mul_nonneg ((D.tilt _ _).nonneg _) ((D.anchorU _ _ _).nonneg _)) ((D.refCross Θ g u.1).nonneg q)

/-- `F_ξ`: the product observation density against `Q`, times the candidate's base-gate indicator (08:158). -/
def Fcand {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (o : D.Obs J g) : ℝ :=
  (if D.CandGate (Function.update Θ g ξ) g then 1 else 0) * (∏ j, D.intRatio Θ g ξ (o.1 j)) *
    ∏ u, D.crossRatio Θ g ξ u (o.2 u)

theorem Fcand_nonneg {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (ξ : D.Tup) (o : D.Obs J g) :
    0 ≤ D.Fcand Θ g ξ o :=
  mul_nonneg (mul_nonneg (ind_nonneg _) (Finset.prod_nonneg fun j _ => D.intRatio_nonneg Θ g ξ _))
    (Finset.prod_nonneg fun u _ => D.crossRatio_nonneg Θ g ξ u _)

/-- `M = ∫ F_ξ dR'(ξ)` (08:160). -/
def Mden {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (o : D.Obs J g) : ℝ :=
  ∑ ξ, D.R'.w ξ * D.Fcand Θ g ξ o

/-- The product reference `Q` of observed data (08:158). -/
def Qref {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (o : D.Obs J g) : ℝ :=
  (∏ j, (o.1 j).elim 1 fun i => (D.refInt Θ g).w i) * ∏ u, (D.refCross Θ g u.1).w (o.2 u)

theorem Qref_nonneg {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (o : D.Obs J g) :
    0 ≤ D.Qref Θ g o := by
  refine mul_nonneg (Finset.prod_nonneg fun j _ => ?_) (Finset.prod_nonneg fun u _ => (D.refCross _ _ _).nonneg _)
  cases o.1 j with
  | none => simp
  | some i => exact (D.refInt Θ g).nonneg i

/-- The base posterior `F_ξ dR'(ξ) / M` (`R'` when `M = 0`) (08:163). -/
def basePost {J : Type} [Fintype J] (Θ : D.Hist) (g : D.KeyT) (o : D.Obs J g) : FinProb D.Tup :=
  normOr (fun ξ => D.R'.w ξ * D.Fcand Θ g ξ o) (fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Fcand_nonneg Θ g ξ o)) D.R'

/-- The true hypothetical data weight with `k` internal tags: tags from `S_g`, cross pairs from `S_u(i)U_{u,i}`
(08:140). -/
def trueW (Θ : D.Hist) (g : D.KeyT) {k : ℕ} (t : Fin k → D.M.ι) (c : D.CrossSub g → D.M.ι × Fin D.N) : ℝ :=
  (∏ j, (D.tilt Θ g).w (t j)) * ∏ u, (D.tilt Θ u.1).w (c u).1 * (D.anchorU Θ u.1 (c u).1).w (c u).2

/-- `q_{g,k}`: the true-gated probability of `M < ε₀` over hypothetical tags and cross anchors with `k` internal
IDs (08:179). -/
def qgk (Θ : D.Hist) (g : D.KeyT) (k : ℕ) : ℝ :=
  ∑ t : Fin k → D.M.ι, ∑ c : D.CrossSub g → D.M.ι × Fin D.N,
    (if D.CandGate Θ g then 1 else 0) * D.trueW Θ g t c *
      if D.Mden Θ g (J := Fin k) ((fun j => some (t j)), c) < D.eps0 then 1 else 0

/-- `q_L`: for fixed internal tags `oi` and cross tags `ct`, the true-gated probability of `M < ε₀` over
hypothetical cross anchors (08:191). -/
def qL (Θ : D.Hist) (g : D.KeyT) (oi : D.Loc → Option D.M.ι) (ct : D.CrossSub g → D.M.ι) : ℝ :=
  ∑ x : D.CrossSub g → Fin D.N,
    (if D.CandGate Θ g then 1 else 0) * (∏ u, (D.anchorU Θ u.1 (ct u)).w (x u)) *
      if D.Mden Θ g (oi, fun u => (ct u, x u)) < D.eps0 then 1 else 0

/-! ## Step 5: hidden-history conditioning and local selection (08:178–225) -/

/-- The combined hidden event at `g` (08:184): a base gate fails, or `q_{g,k} > ε₀^{1/2}` for some `k ≤ T`. -/
def HBad (Θ : D.Hist) (g : D.KeyT) : Prop :=
  ¬ D.BaseGates Θ g ∨ ∃ k ≤ TC η₀ D.n, Real.sqrt D.eps0 < D.qgk Θ g k

/-- The hidden law: raw tuples conditioned on avoiding every hidden event (08:184–189). -/
def hiddenLaw : FinProb D.Hist := condOr D.rawHidden fun Θ => ∀ g, ¬ D.HBad Θ g

/-- Prospective centre positions in every slice. -/
abbrev Pos := D.KeyT → D.Loc → Bool
/-- A tag at every prospective centre ID. -/
abbrev Tags := D.KeyT → D.Loc → D.M.ι
/-- Activations in every slice. -/
abbrev Acts := D.KeyT → D.Loc → Bool
/-- Tie priorities in every slice. -/
abbrev TieAll := D.KeyT → (hdP η₀ D.n).Ties

/-- Independent positions across slices (08:126). -/
def posLaw : FinProb D.Pos := FinProb.pi fun _ => (hdP η₀ D.n).posLaw

/-- Independent tags `∼ S_g` at the IDs of slice `g`, given the hidden tuples (08:127). -/
def tagLawAll (Θ : D.Hist) : FinProb D.Tags := FinProb.pi fun g => FinProb.pi fun _ : D.Loc => D.tilt Θ g

/-- Independent activations across slices. -/
def actLaw : FinProb D.Acts := FinProb.pi fun _ => (hdP η₀ D.n).actLaw

/-- Independent tie priorities across slices. -/
def tieLaw : FinProb D.TieAll := FinProb.pi fun _ => (hdP η₀ D.n).tieLaw

/-- A local list at an odd cell of key `g`: internal IDs of slice `g` and one ID in each cross slice. -/
abbrev LList (g : D.KeyT) := Finset D.Loc × (D.CrossSub g → D.Loc)

/-- The IDs (slice, location) of a list. -/
def listIds (g : D.KeyT) (L : D.LList g) : Finset (D.KeyT × D.Loc) :=
  L.1.image (fun ℓ => (g, ℓ)) ∪ Finset.univ.image fun u : D.CrossSub g => (u.1, L.2 u)

/-- A candidate list at the odd cell `c` (08:196): at most `T` present internal IDs in the balls of the ordinary
even neighbours (all levels), and a present ID in the ball of `c`'s residual word in each cross slice. -/
def Cand (P : D.Pos) (c : D.CellT) (L : D.LList c.1) : Prop :=
  L.1.card ≤ TC η₀ D.n ∧
  (∀ ℓ ∈ L.1, P c.1 ℓ = true ∧ ∃ b ∈ ordNbrs c.2, _root_.hammingDist ℓ.1 b ≤ rH D.n) ∧
  ∀ u, P u.1 (L.2 u) = true ∧ _root_.hammingDist (L.2 u).1 c.2 ≤ rH D.n

/-- The internal tag data of a list. -/
def listInt (t : D.Tags) (g : D.KeyT) (L : D.LList g) : D.Loc → Option D.M.ι :=
  fun ℓ => if ℓ ∈ L.1 then some (t g ℓ) else none

/-- The cross tags of a list. -/
def listCrossTag (t : D.Tags) (g : D.KeyT) (L : D.LList g) : D.CrossSub g → D.M.ι :=
  fun u => t u.1 (L.2 u)

/-- A bad list: `q_L > ε₀^{1/4}` (08:195). -/
def BadList (Θ : D.Hist) (t : D.Tags) (c : D.CellT) (L : D.LList c.1) : Prop :=
  Real.sqrt (Real.sqrt D.eps0) < D.qL Θ c.1 (D.listInt t c.1 L) (D.listCrossTag t c.1 L)

/-- The fixed ordering of local lists at key `g`. -/
def listOrder (g : D.KeyT) : List (D.LList g) := (Finset.univ : Finset (D.LList g)).toList

/-- The maximal disjoint family of bad candidate lists at `c`, greedy in the fixed order (08:208). -/
def family (Θ : D.Hist) (P : D.Pos) (t : D.Tags) (c : D.CellT) : List (D.LList c.1) :=
  greedy (D.listIds c.1) ((D.listOrder c.1).filter fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L))

/-- `ℓ` is forbidden at the even site `e` (08:208–209): it is an ID of slice `e.1` in a family list at an odd cell
of which `e` is a padded even neighbour, and lies in the ball of `e`. -/
def Forbidden (Θ : D.Hist) (P : D.Pos) (t : D.Tags) (e : D.CellT) (ℓ : D.Loc) : Prop :=
  ∃ c : D.CellT, PadNbr c e ∧ ∃ L ∈ D.family Θ P t c, (e.1, ℓ) ∈ D.listIds c.1 L ∧
    _root_.hammingDist ℓ.1 e.2 ≤ rH D.n

/-- Eligibility in slice `g` (08:212): present IDs of the site-level ball that are not forbidden. -/
def elig (Θ : D.Hist) (P : D.Pos) (t : D.Tags) (g : D.KeyT) : (hdP η₀ D.n).EligMap :=
  fun b j => Finset.univ.filter fun ℓ : D.Loc =>
    P g ℓ = true ∧ ℓ.2 = j ∧ _root_.hammingDist ℓ.1 b ≤ rH D.n ∧ ¬ D.Forbidden Θ P t (g, b) ℓ

/-- Activations, ties and tags, drawn after the positions. -/
abbrev TAT := (D.Tags × D.Acts) × D.TieAll

/-- The pre-anchor history: hidden tuples, positions, tags, activations, ties. -/
abbrev Pre := (D.Hist × D.Pos) × D.TAT

instance instFintypeTags : Fintype D.Tags := inferInstance
instance instFintypeActs : Fintype D.Acts := inferInstance
instance instFintypeTieAll : Fintype D.TieAll := inferInstance
instance instFintypeTAT : Fintype D.TAT := inferInstanceAs (Fintype ((D.Tags × D.Acts) × D.TieAll))
instance instFintypePos : Fintype D.Pos := inferInstance
instance instFintypeHist : Fintype D.Hist := inferInstance
instance instFintypePre : Fintype D.Pre := inferInstanceAs (Fintype ((D.Hist × D.Pos) × D.TAT))
instance instFintypePosTAT : Fintype (D.Pos × D.TAT) := inferInstance

/-- Raw tags, activations and ties given the hidden tuples. -/
def rawTAT (Θ : D.Hist) : FinProb D.TAT := ((D.tagLawAll Θ).prod D.actLaw).prod D.tieLaw

/-- The law of the pre-anchor history: hidden law, independent positions, then raw tags, activations, ties. -/
def preLaw : FinProb D.Pre := FinProb.bind (FinProb.bind D.hiddenLaw fun _ => D.posLaw) fun q => D.rawTAT q.1

/-- The selected centre at the even cell `c`: the long height rule of its slice (08:214). -/
def sel (q : D.Pre) (c : D.CellT) : Option D.Loc :=
  (hdP η₀ D.n).selection Finset.univ (q.1.2 c.1) (q.2.1.2 c.1) (D.elig q.1.1 q.1.2 q.2.1.1 c.1) (q.2.2 c.1) c.2

/-- The number of present IDs of level `j` in the ball of the site `b` of slice `g`. -/
def ballCount (P : D.Pos) (g : D.KeyT) (b : D.ResT) (j : Fin (HH η₀ D.n + 1)) : ℕ :=
  (Finset.univ.filter fun u : D.ResT => P g (u, j) = true ∧ _root_.hammingDist u b ≤ rH D.n).card

/-- Prospective ball counts between `λ/2` and `2λ` everywhere (08:196, 211). -/
def PosOK (P : D.Pos) : Prop :=
  ∀ g b j, (hdP η₀ D.n).lam / 2 ≤ D.ballCount P g b j ∧ (D.ballCount P g b j : ℝ) ≤ 2 * (hdP η₀ D.n).lam

/-- Fewer than `n` lists in every maximal family (08:208). -/
def FewBad (Θ : D.Hist) (P : D.Pos) (t : D.Tags) : Prop := ∀ c, (D.family Θ P t c).length < D.n

/-- Good Lipschitz heights in every slice (08:214). -/
def GoodH (Θ : D.Hist) (P : D.Pos) (t : D.Tags) (A : D.Acts) : Prop :=
  ∀ g, (hdP η₀ D.n).GoodHeights Finset.univ (P g) (A g) (D.elig Θ P t g)

/-- Selection success. -/
def SelOK (q : D.Pre) : Prop :=
  D.PosOK q.1.2 ∧ D.FewBad q.1.1 q.1.2 q.2.1.1 ∧ D.GoodH q.1.1 q.1.2 q.2.1.1 q.2.1.2

/-- A pre-anchor history in the support of its law: hidden events avoided and every tag of positive centre
probability. -/
def Supp (q : D.Pre) : Prop :=
  (∀ g, ¬ D.HBad q.1.1 g) ∧ ∀ g ℓ, 0 < (D.tilt q.1.1 g).w (q.2.1.1 g ℓ)

/-- A successful pre-anchor history. -/
def Good (q : D.Pre) : Prop := D.Supp q ∧ D.SelOK q

/-- Legal eligibility on the height consultation domain of the even cell `e` (08:314). -/
def LocalLegal (Θ : D.Hist) (P : D.Pos) (t : D.Tags) (e : D.CellT) : Prop :=
  (hdP η₀ D.n).Legal (P e.1) (D.elig Θ P t e.1) ((hdP η₀ D.n).domBall Finset.univ e.2 (hdP η₀ D.n).Rlong)

/-! ## Steps 6–8: presentations, selection adjustment, posterior rows (08:227–300) -/

/-- Anchors at every cell. -/
abbrev Anch := D.CellT → Fin D.N

instance instFintypeAnch : Fintype D.Anch := inferInstance
instance instFintypeTATAnch : Fintype (D.TAT × D.Anch) := inferInstance
instance instFintypePreAnch : Fintype (D.Pre × D.Anch) := inferInstance

/-- The tag of the selected centre. -/
def selTag (q : D.Pre) (c : D.CellT) : Option D.M.ι := (D.sel q c).map (q.2.1.1 c.1)

/-- The selected anchor law `U_{g, i(g,a)}`; the aggregate first law after a failed selection. -/
def Usel (q : D.Pre) (c : D.CellT) : Law D.N :=
  match D.selTag q c with
  | some i => D.anchorU q.1.1 c.1 i
  | none => D.muBar

/-- Raw anchors: independent `W_c ∼ U_{g, i(c)}` (08:133–134). -/
def rawAnchors (q : D.Pre) : FinProb D.Anch := FinProb.pi fun c => D.Usel q c

/-- The raw local experiment at hidden tuples `Θ` and positions `P` (08:228): raw tags, activations, ties, the
selections they induce, then raw anchors. -/
def rawLaw (Θ : D.Hist) (P : D.Pos) : FinProb (D.TAT × D.Anch) :=
  FinProb.bind (D.rawTAT Θ) fun ω => D.rawAnchors ((Θ, P), ω)

/-- The distinct internal IDs selected at the ordinary even neighbours of `c`. -/
def intIds (q : D.Pre) (c : D.CellT) : Finset D.Loc :=
  (ordNbrs c.2).biUnion fun b => (D.sel q (c.1, b)).toFinset

/-- The ID selected at the cross cell `(u, a)`. -/
def crossId (q : D.Pre) (c : D.CellT) (u : D.CrossSub c.1) : D.Loc := (D.sel q (u.1, c.2)).getD default

/-- A presentation at an odd cell of key `g`: internal tags at the internal IDs (`none` elsewhere), and the cross
ID, its tag and the cross anchor at each cross key. -/
abbrev Pres (g : D.KeyT) := (D.Loc → Option D.M.ι) × (D.CrossSub g → D.Loc × D.M.ι × Fin D.N)

/-- The realized presentation of the odd cell `c` (08:140, 230); ordinary anchors are not observed. -/
def presOf (q : D.Pre) (W : D.Anch) (c : D.CellT) : D.Pres c.1 :=
  (fun ℓ => if ℓ ∈ D.intIds q c then some (q.2.1.1 c.1 ℓ) else none,
    fun u => (D.crossId q c u, q.2.1.1 u.1 (D.crossId q c u), W (u.1, c.2)))

/-- The observed data of a presentation. -/
def obsOf {g : D.KeyT} (π : D.Pres g) : D.Obs D.Loc g := (π.1, fun u => ((π.2 u).2.1, (π.2 u).2.2))

/-- Incident-ball position counts at most `2λ` at all levels (08:228). -/
def PosCountOK (P : D.Pos) (c : D.CellT) : Prop :=
  ∀ e, PadNbr c e → ∀ j, (D.ballCount P e.1 e.2 j : ℝ) ≤ 2 * (hdP η₀ D.n).lam

/-- A valid presentation (08:228): the true base gates, legitimate selections with at most `T` internal IDs, the
position gate and `M ≥ ε₀`. -/
def PresValid (q : D.Pre) (W : D.Anch) (c : D.CellT) : Prop :=
  D.CandGate q.1.1 c.1 ∧ (∀ b ∈ ordNbrs c.2, (D.sel q (c.1, b)).isSome) ∧
  (∀ u : D.CrossSub c.1, (D.sel q (u.1, c.2)).isSome) ∧ (D.intIds q c).card ≤ TC η₀ D.n ∧
  D.PosCountOK q.1.2 c ∧ D.eps0 ≤ D.Mden q.1.1 c.1 (D.obsOf (D.presOf q W c))

/-- `F_ξ a_ξ`: the subdensity against `Q_L` of validly presenting `π`, in the raw local experiment with `Θ_g`
replaced by the candidate `ξ` (08:230–240).  It reads `Θ` only off `g`. -/
def Gsel (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (ξ : D.Tup) (π : D.Pres c.1) : ℝ :=
  (D.rawLaw (Function.update Θ c.1 ξ) P).pr (fun z =>
    D.PresValid ((Function.update Θ c.1 ξ, P), z.1) z.2 c ∧
      D.presOf ((Function.update Θ c.1 ξ, P), z.1) z.2 c = π) / D.Qref Θ c.1 (D.obsOf π)

theorem Gsel_nonneg (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (ξ : D.Tup) (π : D.Pres c.1) :
    0 ≤ D.Gsel Θ P c ξ π :=
  div_nonneg (pr_nonneg _ _) (D.Qref_nonneg _ _ _)

/-- `M^a = ∫ F_ξ a_ξ dR'(ξ)` (08:244). -/
def Mad (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (π : D.Pres c.1) : ℝ := ∑ ξ, D.R'.w ξ * D.Gsel Θ P c ξ π

/-- The selected-presentation posterior when `M^a ≥ ε₀ M`, the base posterior otherwise (08:245–247). -/
def selPost (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (π : D.Pres c.1) : FinProb D.Tup :=
  if D.eps0 * D.Mden Θ c.1 (D.obsOf π) ≤ D.Mad Θ P c π then
    normOr (fun ξ => D.R'.w ξ * D.Gsel Θ P c ξ π) (fun ξ => mul_nonneg (D.R'.nonneg ξ) (D.Gsel_nonneg Θ P c ξ π))
      (D.basePost Θ c.1 (D.obsOf π))
  else D.basePost Θ c.1 (D.obsOf π)

/-- The heavy threshold exponent `.01 s log n` (08:257). -/
def heavyB : ℝ := (1 / 100 : ℝ) * sC η₀ D.n * Real.log D.n

/-- The mass of the average coordinate marginal off the heavy labels. -/
def lightMass (Q : FinProb D.Tup) : ℝ :=
  ∑ y, averageCoordinateMarginal Q y * if y ∈ heavyCoordinateSet Q D.heavyB then 0 else 1

/-- The truncated row of a presentation (08:256–264): the average coordinate marginal of the selected posterior,
with the heavy labels deleted, normalized (zero if nothing is left). -/
def p0w (Θ : D.Hist) (P : D.Pos) (c : D.CellT) (π : D.Pres c.1) (y : Fin D.N) : ℝ :=
  if D.lightMass (D.selPost Θ P c π) = 0 then 0 else
    averageCoordinateMarginal (D.selPost Θ P c π) y *
      (if y ∈ heavyCoordinateSet (D.selPost Θ P c π) D.heavyB then 0 else 1) / D.lightMass (D.selPost Θ P c π)

/-- `p⁰_{g,a}`: the truncated row of the realized presentation, zero on invalid presentations (08:264). -/
def p0 (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) : ℝ :=
  if D.PresValid q W c then D.p0w q.1.1 q.1.2 c (D.presOf q W c) y else 0

/-- `y` hits the realized anchors at all ordinary even neighbours (08:293). -/
def OrdHit (W : D.Anch) (c : D.CellT) (y : Fin D.N) : Prop := ∀ b ∈ ordNbrs c.2, Hits D.E D.G (W (c.1, b)) y

/-- The mass of `p⁰` retained by the ordinary-anchor hit test. -/
def ordRet (q : D.Pre) (W : D.Anch) (c : D.CellT) : ℝ := ∑ y, D.p0 q W c y * if D.OrdHit W c y then 1 else 0

/-- Validity of the odd task: a valid presentation passing the hit test with retained mass `≥ .98` (08:293). -/
def Valid8 (q : D.Pre) (W : D.Anch) (c : D.CellT) : Prop := D.PresValid q W c ∧ (98 / 100 : ℝ) ≤ D.ordRet q W c

/-- The odd row `p_{g,a}` (08:293): `p⁰` restricted to ordinary hits, normalized; zero when invalid. -/
def prow (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) : ℝ :=
  if D.Valid8 q W c then D.p0 q W c y * (if D.OrdHit W c y then 1 else 0) / D.ordRet q W c else 0

/-! ## Step 9: selected-anchor loads (08:304–363) -/

/-- The normalized selected anchor law `N U_{g, i(g,a)}(x)` at the even cell `e` (zero after a failed
selection). -/
def selLoad (q : D.Pre) (e : D.CellT) (x : Fin D.N) : ℝ :=
  match D.selTag q e with
  | some i => D.N * (D.anchorU q.1.1 e.1 i).w x
  | none => 0

/-- The selected-anchor load bound with constant `C` (08:307–310). -/
def LoadOK (C : ℝ) (q : D.Pre) : Prop :=
  ∀ x, (Fintype.card (EvenRole D.n) : ℝ)⁻¹ * ∑ a : EvenRole D.n, D.selLoad q (cellOf η₀ a.1) x ≤ C

/-- The comparison mean `B_g(x)` with `C₁ = 8` (08:327–331). -/
def Bcomp (Θ : D.Hist) (g : D.KeyT) (x : Fin D.N) : ℝ :=
  if D.BaseGates Θ g then
    8 * (D.AG g)⁻¹ * (if D.crossHit Θ g x then 1 else 0) * ∑ i, D.postW (Θ g) i * (D.N * (D.M.μ i).w x)
  else 0

/-- The comparison-mean load bound with constant `C` (08:345–350). -/
def CompOK (C : ℝ) (Θ : D.Hist) : Prop :=
  ∀ x, (Fintype.card (EvenRole D.n) : ℝ)⁻¹ * ∑ a : EvenRole D.n, D.Bcomp Θ (keyOf η₀ a.1) x ≤ C

/-! ## Step 10: anchor avoidance and predictive alarms (08:365–393) -/

/-- The denominator test fails at the odd cell `c`. -/
def DenFail (q : D.Pre) (W : D.Anch) (c : D.CellT) : Prop :=
  D.Mden q.1.1 c.1 (D.obsOf (D.presOf q W c)) < D.eps0

/-- The ordinary-hit test fails at the odd cell `c`. -/
def HitFail (q : D.Pre) (W : D.Anch) (c : D.CellT) : Prop := D.ordRet q W c < 98 / 100

/-- `F_z(y)` at the even vertex `v` (08:370): the neighbouring odd rows with the anchor of `v`'s cell replaced by
`z`.  Rows vanish on invalid tasks, so the validity indicator is built in. -/
def starLik (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (z : Fin D.N) (y : Fin D.n → Fin D.N) : ℝ :=
  ∏ j, D.prow q (Function.update W (cellOf η₀ v) z) (cellOf η₀ (cubeFlip v j)) (y j)

/-- `M_v(y) = ∫ F_z(y) dU_v(z)` (08:372). -/
def starMarg (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (y : Fin D.n → Fin D.N) : ℝ :=
  ∑ z, (D.Usel q (cellOf η₀ v)).w z * D.starLik q W v z y

/-- One factor of `Q_v` (08:377–378): `p⁰` at a valid neighbour of the same grid key, the uniform weight `1/N`
elsewhere. -/
def refRow (q : D.Pre) (W : D.Anch) (e c : D.CellT) (y : Fin D.N) : ℝ :=
  if c.1 = e.1 ∧ D.PresValid q W c then D.p0 q W c y else (D.N : ℝ)⁻¹

/-- `Q_v(y)` (08:377). -/
def starRef (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (y : Fin D.n → Fin D.N) : ℝ :=
  ∏ j, D.refRow q W (cellOf η₀ v) (cellOf η₀ (cubeFlip v j)) (y j)

/-- Predictive failure (08:383–384). -/
def PredFail (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) (y : Fin D.n → Fin D.N) : Prop :=
  D.starMarg q W v y = 0 ∨ D.starMarg q W v y < Real.exp (-(4 / 100 : ℝ) * D.n) * D.starRef q W v y

/-- The conditional product-sampling probability of predictive failure at `v` (08:385). -/
def alarmRate (q : D.Pre) (W : D.Anch) (v : CubeVertex D.n) : ℝ :=
  ∑ y : Fin D.n → Fin D.N, (∏ j, D.prow q W (cellOf η₀ (cubeFlip v j)) (y j)) *
    if D.PredFail q W v y then 1 else 0

/-- A predictive alarm at the cell `c` (08:385–388): some even vertex of `c` has rate `> e^{-.02n}`. -/
def Alarm (q : D.Pre) (W : D.Anch) (c : D.CellT) : Prop :=
  ∃ a : EvenRole D.n, cellOf η₀ a.1 = c ∧ Real.exp (-(2 / 100 : ℝ) * D.n) < D.alarmRate q W a.1

/-- The grouped event of a cell (08:387). -/
def CellBad (q : D.Pre) (W : D.Anch) (c : D.CellT) : Prop := D.DenFail q W c ∨ D.HitFail q W c ∨ D.Alarm q W c

/-- The anchor law: raw anchors conditioned on avoiding every cell event (08:393). -/
def anchorLaw (q : D.Pre) : FinProb D.Anch := condOr (D.rawAnchors q) fun W => ∀ c, ¬ D.CellBad q W c

/-- The staged law of the pre-anchor history and the anchors. -/
def stagedLaw : FinProb (D.Pre × D.Anch) := FinProb.bind D.preLaw D.anchorLaw

/-! ## Steps 11–12: column sums, even rows and the clock sampler (08:395–454) -/

/-- The odd column sum at a second-side label. -/
def oddCol (q : D.Pre) (W : D.Anch) (y : Fin D.N) : ℝ := ∑ u : OddRole D.n, D.prow q W (cellOf η₀ u.1) y

/-- The posterior even row `w_v(x; y) = U_v(x) F_x(y) / M_v(y)` (08:428–429). -/
def evenRowAt (q : D.Pre) (W : D.Anch) (a : EvenRole D.n) (y : Fin D.n → Fin D.N) (x : Fin D.N) : ℝ :=
  D.starLik q W a.1 x y * (D.Usel q (cellOf η₀ a.1)).w x / D.starMarg q W a.1 y

/-- The posterior even row at the odd assignment `f`. -/
def evenRow (q : D.Pre) (W : D.Anch) (f : OddRole D.n → Fin D.N) (a : EvenRole D.n) (x : Fin D.N) : ℝ :=
  D.evenRowAt q W a (nbrLabels f a) x

/-- The even column sum at a first-side label. -/
def evenCol (q : D.Pre) (W : D.Anch) (f : OddRole D.n → Fin D.N) (x : Fin D.N) : ℝ :=
  ∑ a : EvenRole D.n, D.evenRow q W f a x

/-- The star integral of one even role (08:441–449): independent neighbour draws from the odd rows, predictive
success retained, times the normalized even row at `x`. -/
def evenStar (q : D.Pre) (W : D.Anch) (a : EvenRole D.n) (x : Fin D.N) : ℝ :=
  ∑ y : Fin D.n → Fin D.N, (∏ j, D.prow q W (cellOf η₀ (cubeFlip a.1 j)) (y j)) *
    ((if D.PredFail q W a.1 y then 0 else 1) * (D.N * D.evenRowAt q W a y x))

/-- A successful prehistory (08:425): no cell event and odd column sums at most `θ₀ = 10⁻⁸`. -/
def GoodPre (q : D.Pre) (W : D.Anch) : Prop :=
  (∀ c, ¬ D.CellBad q W c) ∧ ∀ y, D.oddCol q W y ≤ (1e-8 : ℝ)

/-- The clock-sampler output (08:425–426, Lemma 3.10 with `B = 3`): injective odd labels avoiding every predictive
failure, with joint upper comparison at most twice the product of the odd rows on at most `n^3` odd roles. -/
def ClockOK (q : D.Pre) (W : D.Anch) (J : FinProb (OddRole D.n → Fin D.N)) : Prop :=
  (∀ f, J.w f ≠ 0 → Function.Injective f ∧ ∀ a : EvenRole D.n, ¬ D.PredFail q W a.1 (nbrLabels f a)) ∧
    ∀ (S : Finset (OddRole D.n)) (o : OddRole D.n → Fin D.N), (S.card : ℝ) ≤ (D.n : ℝ) ^ 3 →
      J.pr (fun f => ∀ u ∈ S, f u = o u) ≤ 2 * ∏ u ∈ S, D.prow q W (cellOf η₀ u.1) (o u)

end Ctx

end HypercubeRamsey.S08
