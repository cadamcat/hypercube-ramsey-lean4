import HypercubeRamsey.S06.Centres

/-!
# Selected odd posteriors

L6.1j (06:572–657).  Rows are attached to actual odd roles and computed at their state.  A high role uses
`p_b = L_b` at its actual descriptor.  A low role corrects for the selection event: fix the base, all hidden
scalars except `Z_ℓ`, and the prospective positions; in the raw proxy experiment with target `ξ` every consulted
tuple is regenerated and the short-rule selections are computed with their activations and ties.  The table
`a_ξ(o)` is the presentation probability of the descriptor with data `o` divided by its gated likelihood
`F_ξ(o) Q^data(o)` (06:583–598).  If `M^a ≥ e^{−.02k} M` the row is proportional to `F_ξ a_ξ dπ_ℓ`, otherwise it is
`L_b`; the same short-rule table is used for descriptors presented by the long rule; invalid rows are zero.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-- The proxy experiment at fixed positions: tuples (at the given history), activations and ties (06:578–581). -/
def proxyLaw (H : X.Hist) : FinProb ((X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties) :=
  ((X.dataLaw X.Loc H).prod X.hp.actLaw).prod X.hp.tieLaw

/-- The centre data with positions `P` and the remaining proxy randomness `ω`. -/
def assemble (P : X.Loc → Bool) (ω : (X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties) : X.Centre :=
  (((P, ω.1.1), ω.1.2), ω.2)

/-- A valid short-rule presentation of the descriptor `D` with data `o` at the odd state `b` (06:589–603). -/
def Presents (H : X.Hist) (C : X.Centre) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) : Prop :=
  X.OddValid H C X.Rshort b ∧ X.actDesc H C X.Rshort b = D ∧ ∀ e ∈ D, X.tup C e = o e

/-- `P_ξ(valid proxy presentation of D, O_D = o)`: the target replaced by `ξ`, all tuples regenerated. -/
def presProb (H : X.Hist) (P : X.Loc → Bool) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc)
    (ξ : Fin N) : ℝ :=
  (X.proxyLaw (X.withHid H (X.tgt b) ξ)).pr fun ω =>
    X.Presents (X.withHid H (X.tgt b) ξ) (X.assemble P ω) b D o

/-- The gated tuple likelihood `F_ξ(o) = Θ_b(ξ) ∏_e g_e(o_e | ξ)`. -/
def lowF (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) (ξ : Fin N) : ℝ :=
  (if X.LowGate H b D ξ then 1 else 0) * ∏ e ∈ D, X.lowLik H b ξ e.2 (o e)

/-- The reference density `Q^data_D(o)`. -/
def lowQ (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) : ℝ :=
  ∏ e ∈ D, (X.lowRef H b e.2).w (o e)

/-- The adjustment table `a_ξ(o)` (06:589–598). -/
def table (H : X.Hist) (P : X.Loc → Bool) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc)
    (ξ : Fin N) : ℝ :=
  safeRatio6 (X.presProb H P b D o ξ) (X.lowF H b D o ξ * X.lowQ H b D o)

/-- The adjusted integrand `π_ℓ(ξ) F_ξ(o) a_ξ(o)`. -/
def adjWeight (H : X.Hist) (P : X.Loc → Bool) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc)
    (ξ : Fin N) : ℝ :=
  (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ * X.table H P b D o ξ

/-- The low row: adjusted if `M^a ≥ e^{−.02k} M`, else `L_b` (06:605–608). -/
def lowRow (H : X.Hist) (P : X.Loc → Bool) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) :
    Law N :=
  if X.s3Thr * (∑ ξ, (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ) ≤ ∑ ξ, X.adjWeight H P b D o ξ
  then normalize6 (X.adjWeight H P b D o) X.y₀ else X.s3Post H b D o

/-- The row at an odd state under the rule of radius `R`; zero on invalidity (06:575–576, 06:611–612). -/
def oddRowAt (H : X.Hist) (C : X.Centre) (R : ℕ) (b : X.State) : Fin N → ℝ :=
  if X.OddValid H C R b then
    match X.stMode b with
    | .low => (X.lowRow H (X.pos C) b (X.actDesc H C R b) (X.tup C)).w
    | .high => (X.s3Post H b (X.actDesc H C R b) (X.tup C)).w
  else fun _ => 0

/-- The row `p_b` of an actual odd role (long rule). -/
def oddRow (H : X.Hist) (C : X.Centre) (u : CubeVertex n) : Fin N → ℝ :=
  X.oddRowAt H C X.Rlong (X.g.L.stateOf u)

/-- The proxy row `p_b^{pr}` (short rule). -/
def proxyRow (H : X.Hist) (C : X.Centre) (u : CubeVertex n) : Fin N → ℝ :=
  X.oddRowAt H C X.Rshort (X.g.L.stateOf u)

/-! ### L6.1j predicates -/

/-- The table lies in `[0,1]`: the presentation probability is at most the gated likelihood (06:589–594). -/
def TableOK : Prop :=
  ∀ (H : X.Hist) (P : X.Loc → Bool) (b : X.State) (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) (ξ : Fin N),
    X.BaseSupp H.1 → X.stMode b = .low → X.presProb H P b D o ξ ≤ X.lowF H b D o ξ * X.lowQ H b D o

/-- Valid rows are probability laws with the deletion and cap bounds and common-neighbour support
(06:612–620). -/
def OddRowBounds : Prop :=
  ∀ (H : X.Hist) (C : X.Centre) (u : CubeVertex n), X.histLaw.w H ≠ 0 → ¬ IsEvenRole u →
    X.OddValid H C X.Rlong (X.g.L.stateOf u) →
      (∀ y, 0 ≤ X.oddRow H C u y) ∧ (∑ y, X.oddRow H C u y = 1) ∧
      (∀ y, (N : ℝ) * X.oddRow H C u y ≤
        if X.stMode (X.g.L.stateOf u) = .low then Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))
        else (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) ∧
      (∀ y, X.oddRow H C u y ≠ 0 → ∀ e ∈ X.actDesc H C X.Rlong (X.g.L.stateOf u), ∀ r,
        Hits E G ((X.tup C e).2 r) y) ∧
      (∀ c ∈ X.actDesc H C X.Rlong (X.g.L.stateOf u), X.Matching (X.g.L.stateOf u) c.2 → ∀ y,
        X.oddRow H C u y ≤ Real.exp ((2 / 10) * X.k) *
          (X.s3Del H (X.g.L.stateOf u) (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C) c).w y)

/-- Valid proxy rows have the same caps (06:612–619, short-rule descriptors). -/
def ProxyCap : Prop :=
  ∀ (H : X.Hist) (C : X.Centre) (u : CubeVertex n), X.histLaw.w H ≠ 0 → ¬ IsEvenRole u →
    X.OddValid H C X.Rshort (X.g.L.stateOf u) → ∀ y, 0 ≤ X.proxyRow H C u y ∧
      (N : ℝ) * X.proxyRow H C u y ≤
        if X.stMode (X.g.L.stateOf u) = .low then Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))
        else (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)

/-- The raw proxy mean is at most `2π_ℓ(y)` under the original prior, at any fixed positions (06:622–637). -/
def ProxyMean : Prop :=
  ∀ (H : X.Hist) (P : X.Loc → Bool) (u : CubeVertex n), X.BaseSupp H.1 → ¬ IsEvenRole u →
    X.stMode (X.g.L.stateOf u) = .low → ∀ y,
      ∑ ξ, (X.hidPost H.1 (X.tgt (X.g.L.stateOf u)).1).w ξ *
        (X.proxyLaw (X.withHid H (X.tgt (X.g.L.stateOf u)) ξ)).expect (fun ω =>
          X.proxyRow (X.withHid H (X.tgt (X.g.L.stateOf u)) ξ) (X.assemble P ω) u y) ≤
        2 * (X.hidPost H.1 (X.tgt (X.g.L.stateOf u)).1).w y

/-- The long mean exceeds the proxy mean by at most `o(1)` (06:639–657). -/
def LongShort : Prop :=
  ∀ (H : X.Hist) (u : CubeVertex n), X.histLaw.w H ≠ 0 → ¬ IsEvenRole u → ∀ y,
    (X.centreLaw H).expect (fun C => (N : ℝ) * X.oddRow H C u y) ≤
      (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) + 1

def OddRowFacts : Prop := X.TableOK ∧ X.OddRowBounds ∧ X.ProxyCap ∧ X.ProxyMean ∧ X.LongShort

end Ctx6

/-- L6.1j (table, 06:583–598): presentation implies the candidate gate; the recorded tuples have their product
laws; Step 2 support gives the domination of the tuple law by `g_e` times the reference. -/
theorem L6_1j_table (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp → X.TableOK := by
  sorry

/-- L6.1j (rows, 06:605–620): the adjusted row is at most `e^{.02k} L_b`, keeping `e^{.2k} Q_{−c}` and the caps;
the same bounds for proxy rows. -/
theorem L6_1j_rows (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.TableOK → X.Step3LowBounds → X.Step3HighBounds → X.HistSupport → X.OddRowBounds ∧ X.ProxyCap := by
  sorry

/-- L6.1j (proxy mean, 06:622–637): cancellation of the adjusted normalizer against the presentation density,
disjoint presentation events; fallback `≤ e^{−.02k}(#descriptors) π_ℓ(y)`, `#descriptors < e^{.01k}` on the
position-count gate. -/
theorem L6_1j_proxy (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TableOK → X.DescCount → X.ProxyMean := by
  sorry

/-- L6.1j (long versus short, 06:639–657): couple both rules by positions, activations and ties; mismatch at one
of `O(n)` neighbouring sites `≤ e^{−3m^{1/5}}` (L3.8, `height_selection_short`), times the cap `e^{m^{.15}}`. -/
theorem L6_1j_longshort (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.CountsBound → X.MarksBound → X.EligDet → X.OddRowBounds → X.LongShort := by
  sorry

/-- L6.1j assembled from its nodes. -/
theorem oddRowFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.StepFacts → X.StageFacts → X.CentreFacts → X.OddRowFacts := by
  have h := (L6_1j_table γ p₀ K hadm).and <| (L6_1j_rows γ p₀ K hadm).and <|
    (L6_1j_proxy γ p₀ K hadm).and (L6_1j_longshort γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hTa, hRo, hPr, hLS⟩ hS hT ⟨hC, hM, hE, _hH, _hV, _hU⟩
  obtain ⟨_hTD, _hC1, _hD1, _h2, _h2d, h2s, _hS, hN, _h3l, _h3h, hbl, hbh⟩ := hS
  have htab := hTa h2s
  obtain ⟨hrows, hpcap⟩ := hRo htab hbl hbh hT.2.2.2
  exact ⟨htab, hrows, hpcap, hPr htab hN, hLS hC hM hE hrows⟩

end

end S06
end HypercubeRamsey
