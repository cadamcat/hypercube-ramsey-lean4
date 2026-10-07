import HypercubeRamsey.S06.Centres

set_option maxHeartbeats 5000000

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
  refine ⟨1, 1, fun n N E G M X hL hStep2Supp => ?_⟩
  intro H P b D o ξ hBase hMode
  classical
  let Hξ := X.withHid H (X.tgt b) ξ
  let obsData : X.Data X.Loc → Prop := fun d => ∀ e ∈ D, d e = o e
  have hPiEvent
      (R : (X.Loc × X.Ty) → FinProb X.Tuple) (S : Finset (X.Loc × X.Ty))
      (t : X.Data X.Loc) :
      (FinProb.pi R).pr (fun d => ∀ e ∈ S, d e = t e) =
        ∏ e ∈ S, (R e).w (t e) := by
    let tS : (∀ e : {e // e ∈ S}, X.Tuple) := fun e => t e.1
    let indicator : (∀ e : {e // e ∈ S}, X.Tuple) → ℝ := fun z => if z = tS then 1 else 0
    have hDep (d : ∀ e : X.Loc × X.Ty, X.Tuple) :
        (∀ e ∈ S, d e = t e) ↔ (fun e : {e // e ∈ S} => d e.1) = tS := by
      constructor
      · intro h
        funext e
        exact h e.1 e.2
      · intro h e he
        have := congrFun h ⟨e, he⟩
        exact this
    have hPrExpect :
        (FinProb.pi R).pr (fun d => ∀ e ∈ S, d e = t e) =
          (FinProb.pi R).expect (fun d : (∀ e : X.Loc × X.Ty, X.Tuple) =>
            indicator (fun e : {e // e ∈ S} => d e.1)) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hp : ∀ e ∈ S, d e = t e
      · have hf : (fun e : {e // e ∈ S} => d e.1) = tS := (hDep d).mp hp
        simp only [if_pos hp, indicator, if_pos hf, mul_one]
      · have hf : (fun e : {e // e ∈ S} => d e.1) ≠ tS := by
          intro h
          exact hp (fun e he => congrFun h ⟨e, he⟩)
        simp only [if_neg hp, indicator, if_neg hf, mul_zero]
    rw [hPrExpect, FinProb.pi_marginal_expect]
    simp [FinProb.expect, FinProb.pi, indicator, tS]
    exact Finset.prod_attach S (fun e => (R e).w (t e))
  have hDataPr : (X.dataLaw X.Loc Hξ).pr obsData =
      ∏ e ∈ D, (X.tupleLaw Hξ e.2).w (o e) := by
    simpa [Ctx6.dataLaw, obsData] using
      (hPiEvent (fun e : X.Loc × X.Ty => X.tupleLaw Hξ e.2) D o)
  have hPrProdFst {α β : Type} [Fintype α] [Fintype β]
      (Q : FinProb α) (R : FinProb β) (A : α → Prop) :
      (Q.prod R).pr (fun z => A z.1) = Q.pr A := by
    classical
    unfold FinProb.pr FinProb.prod
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, if A a then Q.w a * R.w b else 0) =
          ∑ a, if A a then Q.w a * ∑ b, R.w b else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hA : A a <;> simp [hA, Finset.mul_sum]
      _ = ∑ a, if A a then Q.w a else 0 := by simp [R.sum_eq_one]
  have hProxyProj (A : X.Data X.Loc → Prop) :
      (X.proxyLaw Hξ).pr (fun ω => A ω.1.1) = (X.dataLaw X.Loc Hξ).pr A := by
    unfold Ctx6.proxyLaw
    calc
      (((X.dataLaw X.Loc Hξ).prod X.hp.actLaw).prod X.hp.tieLaw).pr
          (fun ω => A ω.1.1) =
        ((X.dataLaw X.Loc Hξ).prod X.hp.actLaw).pr (fun z => A z.1) :=
          hPrProdFst ((X.dataLaw X.Loc Hξ).prod X.hp.actLaw) X.hp.tieLaw
            (fun z => A z.1)
      _ = (X.dataLaw X.Loc Hξ).pr A :=
        hPrProdFst (X.dataLaw X.Loc Hξ) X.hp.actLaw A
  have hTypeAtState (w : CubeVertex n) :
      X.stType (X.g.L.stateOf w) = X.evenType w := by
    unfold Ctx6.stType Ctx6.evenType ChunkLayout6.stType
    simp [X.facts.key_eq w, X.facts.sign_eq w, X.facts.flippable_eq w,
      X.facts.severity_eq w]
  have hStateEven {a : X.State} (ha : a ∈ X.g.L.evenStates) :
      ∃ w, IsEvenRole w ∧ X.g.L.stateOf w = a := by
    unfold ChunkLayout6.evenStates at ha
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨w, hw, hstate⟩
    exact ⟨w, hw, hstate⟩
  have hTypeOcc (a : X.State) (ha : a ∈ X.g.L.evenStates) : X.stType a ∈ X.occTypes := by
    obtain ⟨w, hw, hstate⟩ := hStateEven ha
    have htype := hTypeAtState w
    rw [hstate] at htype
    unfold Ctx6.occTypes
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, htype.symm⟩
  have hNbrEven {a : X.State} (ha : a ∈ X.g.L.stNbr b) : a ∈ X.g.L.evenStates := by
    classical
    unfold ChunkLayout6.stNbr at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨u, v, _hu, hv, _hb, hst, _hadj⟩
    unfold ChunkLayout6.evenStates
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, hst⟩
  have hPresentImp (ω : (X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties)
      (hp : X.Presents Hξ (X.assemble P ω) b D o) :
      X.LowGate Hξ b D ξ ∧ obsData ω.1.1 := by
    rcases hp with ⟨hValid, hDesc, hObs⟩
    have hTrueGate : X.S3TrueGate Hξ b (X.actDesc Hξ (X.assemble P ω) X.Rshort b) :=
      hValid.2.2.2.2.1
    have hGate : X.LowGate Hξ b D ξ := by
      have hGate' : X.LowGate Hξ b (X.actDesc Hξ (X.assemble P ω) X.Rshort b) ξ := by
        simpa [Ctx6.S3TrueGate, Ctx6.trueTarget, Ctx6.withHid, Hξ, hMode] using hTrueGate
      rw [hDesc] at hGate'
      exact hGate'
    refine ⟨hGate, ?_⟩
    intro e he
    have heObs := hObs e he
    simpa [Ctx6.assemble, Ctx6.tup] using heObs
  have hDescriptorTypes (hExists : ∃ ω : (X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties,
      X.Presents Hξ (X.assemble P ω) b D o) : ∀ e ∈ D, e.2 ∈ X.occTypes := by
    intro e he
    obtain ⟨ω, hp⟩ := hExists
    rcases hp with ⟨hValid, hDesc, _hObs⟩
    have he' : e ∈ X.actDesc Hξ (X.assemble P ω) X.Rshort b := by rw [hDesc]; exact he
    simp only [Ctx6.actDesc, Finset.mem_image, Finset.mem_univ, true_and] at he'
    rcases he' with ⟨a, heq⟩
    have hTypeEq : e.2 = X.stType a.1 := (congrArg Prod.snd heq).symm
    rw [hTypeEq]
    exact hTypeOcc a.1 (hNbrEven a.2)
  have hModeLow : modeOf6 X.J (X.g.L.stSeverity b) = .low := by
    simpa [Ctx6.stMode] using hMode
  have hDescriptorTarget (hExists : ∃ ω : (X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties,
      X.Presents Hξ (X.assemble P ω) b D o) : ∀ e ∈ D, X.tgt b ∈ e.2.obs := by
    intro e he
    obtain ⟨ω, hp⟩ := hExists
    rcases hp with ⟨hValid, hDesc, _hObs⟩
    have he' : e ∈ X.actDesc Hξ (X.assemble P ω) X.Rshort b := by rw [hDesc]; exact he
    simp only [Ctx6.actDesc, Finset.mem_image, Finset.mem_univ, true_and] at he'
    rcases he' with ⟨a, heq⟩
    have hTypeEq : e.2 = X.stType a.1 := (congrArg Prod.snd heq).symm
    have hCover := X.facts.low_target_covered b a.1 a.2 hModeLow
    have hCover' : X.tgt b ∈ (X.stType a.1).obs := by
      change X.g.L.stTarget b ∈ (X.g.L.stType (J₆ X.g.L.m) a.1).obs
      exact hCover
    change X.tgt b ∈ e.2.obs
    rw [hTypeEq]
    exact hCover'
  have hSafeRatioNonneg {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) : 0 ≤ safeRatio6 a c := by
    unfold safeRatio6
    split_ifs <;> positivity
  have hSafeRatioMul {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
      (hsupp : 0 < a → 0 < c) : safeRatio6 a c * c = a := by
    by_cases hc0 : c = 0
    · have ha0 : a = 0 := by
        by_contra hne
        have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
        exact (ne_of_gt (hsupp haPos)) hc0
      simp [safeRatio6, hc0, ha0]
    · unfold safeRatio6
      rw [if_neg hc0]
      field_simp
  have hTupleRatioNonneg (H₁ H₂ : X.Hist) (β : X.Ty) (refTag : FinProb X.ι)
      (drop : X.Name) (z : X.Tuple) : 0 ≤ X.tupleRatio H₁ H₂ β refTag drop z := by
    unfold Ctx6.tupleRatio
    apply mul_nonneg
    · exact hSafeRatioNonneg ((X.Tβ H₁ β).nonneg z.1) (refTag.nonneg z.1)
    · apply Finset.prod_nonneg
      intro r hr
      exact hSafeRatioNonneg
        ((X.labelLaw H₁ (reqNames6 β) z.1).nonneg (z.2 r))
        ((X.labelLaw H₂ ((reqNames6 β).erase drop) z.1).nonneg (z.2 r))
  have hLowLikNonneg (H₁ : X.Hist) (b : X.State) (zξ : Fin N) (β : X.Ty)
      (z : X.Tuple) : 0 ≤ X.lowLik H₁ b zξ β z := by
    unfold Ctx6.lowLik
    exact hTupleRatioNonneg (X.withHid H₁ (X.tgt b) zξ) H₁ β
      (X.TβDel H₁ β (X.tgt b)) (.hid (X.tgt b)) z
  have hLowFNonneg (D : Finset (X.Loc × X.Ty)) (z : X.Data X.Loc) (zξ : Fin N) :
      0 ≤ X.lowF H b D z zξ := by
    unfold Ctx6.lowF
    apply mul_nonneg
    · split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro e he
      exact hLowLikNonneg H b zξ e.2 (z e)
  have hLowQNonneg (D : Finset (X.Loc × X.Ty)) (z : X.Data X.Loc) :
      0 ≤ X.lowQ H b D z := by
    unfold Ctx6.lowQ
    apply Finset.prod_nonneg
    intro e he
    exact (X.lowRef H b e.2).nonneg (z e)
  have hTupleWeight (H₀ : X.Hist) (β : X.Ty) (z : X.Tuple) :
      (X.tupleLaw H₀ β).w z =
        (X.Tβ H₀ β).w z.1 *
          ∏ r, (X.labelLaw H₀ (reqNames6 β) z.1).w (z.2 r) := by
    simp [Ctx6.tupleLaw, Ctx6.tupleLawOn, FinProb.bind, FinProb.pi]
  have hTupleRefWeight (H₀ : X.Hist) (β : X.Ty) (refTag : FinProb X.ι)
      (drop : X.Name) (z : X.Tuple) :
      (X.tupleRef H₀ β refTag drop).w z =
        refTag.w z.1 *
          ∏ r, (X.labelLaw H₀ ((reqNames6 β).erase drop) z.1).w (z.2 r) := by
    simp [Ctx6.tupleRef, Ctx6.tupleLawOn, FinProb.bind, FinProb.pi]
  have hTagWeightNonneg (H₀ : X.Hist) (β : X.Ty) (S : Finset X.HKey) (i : X.ι) :
      0 ≤ X.tagWeight H₀ β S i := by
    unfold Ctx6.tagWeight
    apply mul_nonneg
    · apply mul_nonneg
      · exact (X.tagLawAt (X.parOf H₀.1) β.key).nonneg i
      · split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro ℓ hℓ
      exact hSafeRatioNonneg
        ((X.hidPostRep H₀.1 ℓ.1 β.key i).nonneg (H₀.2 ℓ))
        ((X.hidPostDel H₀.1 ℓ.1 β.key).nonneg (H₀.2 ℓ))
  have hTagMassClipEq (H₀ : X.Hist) (β : X.Ty) (S : Finset X.HKey) :
      (∑ i, max 0 (X.tagWeight H₀ β S i)) = X.tagMass H₀ β S := by
    unfold Ctx6.tagMass
    apply Finset.sum_congr rfl
    intro i hi
    exact max_eq_right (hTagWeightNonneg H₀ β S i)
  have hTagPostWeight (H₀ : X.Hist) (β : X.Ty) (S : Finset X.HKey)
      (hMass : 0 < X.tagMass H₀ β S) (i : X.ι) :
      (X.tagPost H₀ β S).w i = X.tagWeight H₀ β S i / X.tagMass H₀ β S := by
    have hClipPos : 0 < ∑ j, max 0 (X.tagWeight H₀ β S j) := by
      rw [hTagMassClipEq]
      exact hMass
    unfold Ctx6.tagPost normalize6
    rw [dif_pos hClipPos]
    change max 0 (X.tagWeight H₀ β S i) /
        (∑ j, max 0 (X.tagWeight H₀ β S j)) = _
    rw [max_eq_right (hTagWeightNonneg H₀ β S i), hTagMassClipEq]
  have hTagDelWeightEq (β : X.Ty) (i : X.ι) :
      X.tagWeight Hξ β (β.obs.erase (X.tgt b)) i =
        X.tagWeight H β (β.obs.erase (X.tgt b)) i := by
    have hfactor : ∀ ℓ ∈ β.obs.erase (X.tgt b),
        safeRatio6 ((X.hidPostRep Hξ.1 ℓ.1 β.key i).w (Hξ.2 ℓ))
            ((X.hidPostDel Hξ.1 ℓ.1 β.key).w (Hξ.2 ℓ)) =
          safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) := by
      intro ℓ hℓ
      have hneq : ℓ ≠ X.tgt b := (Finset.mem_erase.mp hℓ).1
      have hval : Hξ.2 ℓ = H.2 ℓ := by
        simp [Hξ, Ctx6.withHid, Function.update_of_ne hneq]
      rw [hval]
      rfl
    have hprod :
        (∏ ℓ ∈ β.obs.erase (X.tgt b),
          safeRatio6 ((X.hidPostRep Hξ.1 ℓ.1 β.key i).w (Hξ.2 ℓ))
            ((X.hidPostDel Hξ.1 ℓ.1 β.key).w (Hξ.2 ℓ))) =
        (∏ ℓ ∈ β.obs.erase (X.tgt b),
          safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ))) := by
      apply Finset.prod_congr rfl
      exact hfactor
    unfold Ctx6.tagWeight
    change (X.tagLawAt (X.parOf Hξ.1) β.key).w i *
        (if X.tagGate Hξ.1 β i then 1 else 0) *
          (∏ ℓ ∈ β.obs.erase (X.tgt b),
            safeRatio6 ((X.hidPostRep Hξ.1 ℓ.1 β.key i).w (Hξ.2 ℓ))
              ((X.hidPostDel Hξ.1 ℓ.1 β.key).w (Hξ.2 ℓ))) =
      (X.tagLawAt (X.parOf H.1) β.key).w i *
      (if X.tagGate H.1 β i then 1 else 0) *
        (∏ ℓ ∈ β.obs.erase (X.tgt b),
          safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)))
    rw [hprod]
    simp [Hξ, Ctx6.withHid]
  have hTagFullFactor (β : X.Ty) (hTarget : X.tgt b ∈ β.obs) (i : X.ι) :
      X.tagWeight Hξ β β.obs i =
        X.tagWeight Hξ β (β.obs.erase (X.tgt b)) i *
          safeRatio6 ((X.hidPostRep Hξ.1 (X.tgt b).1 β.key i).w (Hξ.2 (X.tgt b)))
            ((X.hidPostDel Hξ.1 (X.tgt b).1 β.key).w (Hξ.2 (X.tgt b))) := by
    unfold Ctx6.tagWeight
    rw [← Finset.mul_prod_erase β.obs
      (fun ℓ => safeRatio6 ((X.hidPostRep Hξ.1 ℓ.1 β.key i).w (Hξ.2 ℓ))
        ((X.hidPostDel Hξ.1 ℓ.1 β.key).w (Hξ.2 ℓ))) hTarget]
    ring
  have hTagDelMassEq (β : X.Ty) :
      X.tagMass Hξ β (β.obs.erase (X.tgt b)) =
        X.tagMass H β (β.obs.erase (X.tgt b)) := by
    unfold Ctx6.tagMass
    apply Finset.sum_congr rfl
    intro i hi
    exact hTagDelWeightEq β i
  have hTagSupport (β : X.Ty) (hTarget : X.tgt b ∈ β.obs)
      (hTests : X.Step2Tests Hξ β) (i : X.ι)
      (hPost : 0 < (X.Tβ Hξ β).w i) :
      0 < (X.TβDel H β (X.tgt b)).w i := by
    have hRawFull : 0 < X.tagWeight Hξ β β.obs i := by
      have hEq := hTagPostWeight Hξ β β.obs hTests.1 i
      have hDiv : 0 < X.tagWeight Hξ β β.obs i / X.tagMass Hξ β β.obs := by
        rw [← hEq]
        exact hPost
      exact (div_pos_iff_of_pos_right hTests.1).mp hDiv
    have hRawDelNonneg := hTagWeightNonneg Hξ β (β.obs.erase (X.tgt b)) i
    have hRawDel : 0 < X.tagWeight Hξ β (β.obs.erase (X.tgt b)) i := by
      by_contra hNot
      have hle : X.tagWeight Hξ β (β.obs.erase (X.tgt b)) i ≤ 0 := le_of_not_gt hNot
      have hzero : X.tagWeight Hξ β (β.obs.erase (X.tgt b)) i = 0 :=
        le_antisymm hle hRawDelNonneg
      rw [hTagFullFactor β hTarget i, hzero] at hRawFull
      simp at hRawFull
    have hMassDel : 0 < X.tagMass Hξ β (β.obs.erase (X.tgt b)) := by
      unfold Ctx6.tagMass
      have hs := Finset.single_le_sum (fun j hj => hTagWeightNonneg Hξ β (β.obs.erase (X.tgt b)) j)
        (Finset.mem_univ i)
      exact lt_of_lt_of_le hRawDel hs
    have hMassRef : 0 < X.tagMass H β (β.obs.erase (X.tgt b)) := by
      rw [← hTagDelMassEq β]
      exact hMassDel
    have hRawRef : 0 < X.tagWeight H β (β.obs.erase (X.tgt b)) i := by
      rw [← hTagDelWeightEq β i]
      exact hRawDel
    change 0 < (X.tagPost H β (β.obs.erase (X.tgt b))).w i
    rw [hTagPostWeight H β (β.obs.erase (X.tgt b)) hMassRef i]
    exact div_pos hRawRef hMassRef
  have hKeysSupp (β : X.Ty) : X.KeysSupp H.1 (X.typeKeys β) := by
    rcases hBase with ⟨hV, hBins, hTags⟩
    refine ⟨hV, ?_, ?_⟩
    · intro u hu
      apply hBins u
      unfold Ctx6.binsOf at hu ⊢
      rcases Finset.mem_image.mp hu with ⟨k, hk, hku⟩
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hku⟩
    · intro s hs
      exact hTags s (Finset.mem_univ _)
  have hClipMassEq (H₀ : X.Hist) (S : Finset X.Name) (i : X.ι) :
      (∑ x, max 0 (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0)) =
        ∑ x ∈ X.reqNbhd H₀ S, (M.μ i).w x := by
    classical
    have hmax (x : Fin N) :
        max 0 (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0) =
          if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0 := by
      by_cases hx : x ∈ X.reqNbhd H₀ S
      · simp [hx, max_eq_right ((M.μ i).nonneg x)]
      · simp [hx]
    have hsum :
        (∑ x, if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0) =
          ∑ x ∈ X.reqNbhd H₀ S, (M.μ i).w x := by
      calc
        (∑ x, if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0) =
            ∑ x, @ite ℝ (x ∈ X.reqNbhd H₀ S) (Finset.decidableMem x (X.reqNbhd H₀ S))
              ((M.μ i).w x) 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases h : x ∈ X.reqNbhd H₀ S <;> simp [h]
        _ = ∑ x ∈ X.reqNbhd H₀ S, (M.μ i).w x :=
          Fintype.sum_ite_mem (X.reqNbhd H₀ S) (fun x => (M.μ i).w x)
    calc
      (∑ x, max 0 (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0)) =
          ∑ x, if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hmax x
      _ = ∑ x ∈ X.reqNbhd H₀ S, (M.μ i).w x := hsum
  have hLabelWeightFormula (H₀ : X.Hist) (S : Finset X.Name) (i : X.ι)
      (hClipPos : 0 < ∑ x, max 0
        (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0)) (x : Fin N) :
      (X.labelLaw H₀ S i).w x =
        (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0) /
          (∑ x, max 0 (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0)) := by
    have hClipDecEq :
        (∑ z, max 0 (@ite ℝ (z ∈ X.reqNbhd H₀ S)
          (propDecidable (z ∈ X.reqNbhd H₀ S)) ((M.μ i).w z) 0)) =
        ∑ z, max 0 (if z ∈ X.reqNbhd H₀ S then (M.μ i).w z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : z ∈ X.reqNbhd H₀ S <;> simp [h]
    have hClipPos' : 0 < ∑ ω, max 0
        ((fun z => @ite ℝ (z ∈ X.reqNbhd H₀ S)
          (propDecidable (z ∈ X.reqNbhd H₀ S)) ((M.μ i).w z) 0) ω) := by
      simpa only [Function.comp_apply] using
        (lt_of_lt_of_eq hClipPos hClipDecEq.symm)
    unfold Ctx6.labelLaw restrictOr6 normalize6
    simp [hClipPos']
    have hnum : max 0 (@ite ℝ (x ∈ X.reqNbhd H₀ S)
        (propDecidable (x ∈ X.reqNbhd H₀ S)) ((M.μ i).w x) 0) =
          (if x ∈ X.reqNbhd H₀ S then (M.μ i).w x else 0) := by
      by_cases hx : x ∈ X.reqNbhd H₀ S
      · simp [hx, max_eq_right ((M.μ i).nonneg x)]
      · simp [hx]
    rw [hnum, hClipDecEq]
  have hVarValueEq (nm : X.Name) (hnm : nm ≠ .hid (X.tgt b)) :
      X.varVal Hξ nm = X.varVal H nm := by
    cases nm with
    | par p => rfl
    | hid ℓ =>
      have hneq : ℓ ≠ X.tgt b := by
        intro h
        apply hnm
        subst ℓ
        rfl
      change Hξ.2 ℓ = H.2 ℓ
      simp [Hξ, Ctx6.withHid, Function.update_of_ne hneq]
  have hReqNbhdSub (β : X.Ty) (x : Fin N)
      (hx : x ∈ X.reqNbhd Hξ (reqNames6 β)) :
      x ∈ X.reqNbhd H ((reqNames6 β).erase (.hid (X.tgt b))) := by
    unfold Ctx6.reqNbhd at hx ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro nm hnm
    have hnm' : nm ∈ reqNames6 β := Finset.mem_of_mem_erase hnm
    have hval := hVarValueEq nm ((Finset.mem_erase.mp hnm).1)
    rw [← hval]
    exact hx nm hnm'
  have hLabelSupport (β : X.Ty) (i : X.ι)
      (hCommon : c₁ / 2 ≤ ∑ x ∈ X.reqNbhd Hξ (reqNames6 β), (M.μ i).w x)
      (x : Fin N) :
      0 < (X.labelLaw Hξ (reqNames6 β) i).w x →
        0 < (X.labelLaw H ((reqNames6 β).erase (.hid (X.tgt b))) i).w x := by
    have hC1 : 0 < c₁ / 2 := by norm_num [c₁, c₀]
    let cand := X.reqNbhd Hξ (reqNames6 β)
    let ref := X.reqNbhd H ((reqNames6 β).erase (.hid (X.tgt b)))
    have hCandClipPos :
        0 < ∑ z, max 0 (if z ∈ cand then (M.μ i).w z else 0) := by
      calc
        0 < c₁ / 2 := hC1
        _ ≤ ∑ z ∈ cand, (M.μ i).w z := by simpa [cand] using hCommon
        _ = ∑ z, max 0 (if z ∈ cand then (M.μ i).w z else 0) := by
          simpa [cand] using (hClipMassEq Hξ (reqNames6 β) i).symm
    have hClipLe :
        (∑ z, max 0 (if z ∈ cand then (M.μ i).w z else 0)) ≤
          ∑ z, max 0 (if z ∈ ref then (M.μ i).w z else 0) := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hCand : z ∈ cand
      · have hRef : z ∈ ref := hReqNbhdSub β z hCand
        rw [if_pos hCand, if_pos hRef]
      · have hzero : max 0 (if z ∈ cand then (M.μ i).w z else 0) = 0 := by
          simp [hCand]
        rw [hzero]
        exact le_max_left _ _
    have hRefClipPos :
        0 < ∑ z, max 0 (if z ∈ ref then (M.μ i).w z else 0) :=
      lt_of_lt_of_le hCandClipPos hClipLe
    intro hxw
    rw [hLabelWeightFormula Hξ (reqNames6 β) i hCandClipPos x] at hxw
    have hxCand : x ∈ cand := by
      by_contra hnot
      have hnot' : x ∉ X.reqNbhd Hξ (reqNames6 β) := by simpa [cand] using hnot
      simp [hnot'] at hxw
    have hμpos : 0 < (M.μ i).w x := by
      by_contra hnot
      have hle : (M.μ i).w x ≤ 0 := le_of_not_gt hnot
      have hzero : (M.μ i).w x = 0 := le_antisymm hle ((M.μ i).nonneg x)
      have hxCand' : x ∈ X.reqNbhd Hξ (reqNames6 β) := by simpa [cand] using hxCand
      simp [hxCand', hzero] at hxw
    have hxRef : x ∈ ref := hReqNbhdSub β x hxCand
    rw [hLabelWeightFormula H ((reqNames6 β).erase (.hid (X.tgt b))) i hRefClipPos x]
    have hxRef' : x ∈ X.reqNbhd H ((reqNames6 β).erase (.hid (X.tgt b))) := by
      simpa [ref] using hxRef
    have hNumPos :
        0 < if x ∈ X.reqNbhd H ((reqNames6 β).erase (.hid (X.tgt b))) then (M.μ i).w x else 0 := by
      rw [if_pos hxRef']
      exact hμpos
    exact div_pos hNumPos hRefClipPos
  by_cases hExists : ∃ ω : (X.Data X.Loc × (X.Loc → Bool)) × X.hp.Ties,
      X.Presents Hξ (X.assemble P ω) b D o
  · obtain ⟨ω₀, hPresents₀⟩ := hExists
    have hGate := (hPresentImp ω₀ hPresents₀).1
    have hTypes := hDescriptorTypes ⟨ω₀, hPresents₀⟩
    have hTupleDom (e : X.Loc × X.Ty) (he : e ∈ D) :
        (X.tupleLaw Hξ e.2).w (o e) ≤
          X.lowLik H b ξ e.2 (o e) * (X.lowRef H b e.2).w (o e) := by
      by_cases hZero : (X.tupleLaw Hξ e.2).w (o e) = 0
      · rw [hZero]
        exact mul_nonneg (hLowLikNonneg H b ξ e.2 (o e))
          ((X.lowRef H b e.2).nonneg (o e))
      · have hTuplePos : 0 < (X.tupleLaw Hξ e.2).w (o e) :=
          lt_of_le_of_ne ((X.tupleLaw Hξ e.2).nonneg (o e)) (Ne.symm hZero)
        have hTagPos : 0 < (X.Tβ Hξ e.2).w (o e).1 := by
          have hEq := hTupleWeight Hξ e.2 (o e)
          rw [hEq] at hTuplePos
          by_contra hNot
          have hle : (X.Tβ Hξ e.2).w (o e).1 ≤ 0 := le_of_not_gt hNot
          have hTagZero : (X.Tβ Hξ e.2).w (o e).1 = 0 :=
            le_antisymm hle ((X.Tβ Hξ e.2).nonneg (o e).1)
          rw [hTagZero] at hTuplePos
          simp at hTuplePos
        have hTests : X.Step2Tests Hξ e.2 := by
          simpa [Ctx6.withHid, Hξ] using hGate.2.2 e he
        have hCommon := hStep2Supp Hξ e.2 (hTypes e he) (hKeysSupp e.2) hTests
          (o e).1 hTagPos
        have hTarget := hDescriptorTarget ⟨ω₀, hPresents₀⟩ e he
        have hRefTagPos := hTagSupport e.2 hTarget hTests (o e).1 hTagPos
        have hLabProdNonneg :
            0 ≤ ∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r) := by
          apply Finset.prod_nonneg
          intro r hr
          exact (X.labelLaw Hξ (reqNames6 e.2) (o e).1).nonneg ((o e).2 r)
        have hLabProdPos :
            0 < ∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r) := by
          have hEq := hTupleWeight Hξ e.2 (o e)
          rw [hEq] at hTuplePos
          by_contra hNot
          have hle :
              (∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r)) ≤ 0 := le_of_not_gt hNot
          have hProdZero :
              (∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r)) = 0 :=
            le_antisymm hle hLabProdNonneg
          rw [hProdZero] at hTuplePos
          simp at hTuplePos
        have hLabProdNe :
            (∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r)) ≠ 0 := ne_of_gt hLabProdPos
        have hLabEachPos (r : Fin X.k) :
            0 < (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r) := by
          have hne := (Finset.prod_ne_zero_iff.mp hLabProdNe) r (Finset.mem_univ r)
          exact lt_of_le_of_ne
            ((X.labelLaw Hξ (reqNames6 e.2) (o e).1).nonneg ((o e).2 r)) (Ne.symm hne)
        have hLabSupp (r : Fin X.k) :
            0 < (X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r) :=
          hLabelSupport e.2 (o e).1 hCommon.1 ((o e).2 r) (hLabEachPos r)
        have hTagMul :
            safeRatio6 ((X.Tβ Hξ e.2).w (o e).1)
                ((X.TβDel H e.2 (X.tgt b)).w (o e).1) *
              (X.TβDel H e.2 (X.tgt b)).w (o e).1 =
                (X.Tβ Hξ e.2).w (o e).1 :=
          hSafeRatioMul ((X.Tβ Hξ e.2).nonneg (o e).1)
            ((X.TβDel H e.2 (X.tgt b)).nonneg (o e).1)
            (hTagSupport e.2 hTarget hTests (o e).1)
        have hLabMul (r : Fin X.k) :
            safeRatio6
                ((X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r))
                ((X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r)) *
              (X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r) =
                (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r) :=
          hSafeRatioMul
            ((X.labelLaw Hξ (reqNames6 e.2) (o e).1).nonneg ((o e).2 r))
            ((X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).nonneg ((o e).2 r))
            (fun hp => hLabelSupport e.2 (o e).1 hCommon.1 ((o e).2 r) hp)
        have hLabProd :
            (∏ r, safeRatio6
                ((X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r))
                ((X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r))) *
              (∏ r, (X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r)) =
                ∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r) := by
          calc
            _ = ∏ r, safeRatio6
                  ((X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r))
                  ((X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r)) *
                (X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r) := by
                  rw [← Finset.prod_mul_distrib]
            _ = ∏ r, (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r) := by
                  apply Finset.prod_congr rfl
                  intro r hr
                  exact hLabMul r
        let tagNum := (X.Tβ Hξ e.2).w (o e).1
        let tagDen := (X.TβDel H e.2 (X.tgt b)).w (o e).1
        let tagRat := safeRatio6 tagNum tagDen
        let labNum : Fin X.k → ℝ := fun r =>
          (X.labelLaw Hξ (reqNames6 e.2) (o e).1).w ((o e).2 r)
        let labDen : Fin X.k → ℝ := fun r =>
          (X.labelLaw H ((reqNames6 e.2).erase (.hid (X.tgt b))) (o e).1).w ((o e).2 r)
        let labRat : Fin X.k → ℝ := fun r => safeRatio6 (labNum r) (labDen r)
        have hLabProd' : (∏ r, labRat r) * (∏ r, labDen r) = ∏ r, labNum r := by
          simpa [labRat, labNum, labDen] using hLabProd
        have hTagMul' : tagRat * tagDen = tagNum := by
          simpa [tagRat, tagDen, tagNum] using hTagMul
        have hCombined :
            (tagNum * (∏ r, labNum r)) =
              (tagRat * (∏ r, labRat r)) * (tagDen * (∏ r, labDen r)) := by
          calc
            (tagNum * (∏ r, labNum r)) = tagNum * ((∏ r, labRat r) * (∏ r, labDen r)) := by
              rw [← hLabProd']
            _ = (tagRat * tagDen) * ((∏ r, labRat r) * (∏ r, labDen r)) :=
              congrArg (fun q => q * ((∏ r, labRat r) * (∏ r, labDen r))) hTagMul'.symm
            _ = (tagRat * (∏ r, labRat r)) * (tagDen * (∏ r, labDen r)) := by ring
        have hPointEq :
            (X.tupleLaw Hξ e.2).w (o e) =
              (X.tupleRatio Hξ H e.2 (X.TβDel H e.2 (X.tgt b)) (.hid (X.tgt b)) (o e)) *
                ((X.tupleRef H e.2 (X.TβDel H e.2 (X.tgt b)) (.hid (X.tgt b))).w (o e)) := by
          calc
            (X.tupleLaw Hξ e.2).w (o e) = tagNum * (∏ r, labNum r) := by
              simpa [tagNum, labNum] using hTupleWeight Hξ e.2 (o e)
            _ = X.tupleRatio Hξ H e.2 (X.TβDel H e.2 (X.tgt b))
                  (.hid (X.tgt b)) (o e) *
                (X.tupleRef H e.2 (X.TβDel H e.2 (X.tgt b))
                  (.hid (X.tgt b))).w (o e) := by
              rw [hTupleRefWeight]
              unfold Ctx6.tupleRatio
              simpa [tagNum, tagDen, tagRat, labNum, labDen, labRat] using hCombined
        change (X.tupleLaw Hξ e.2).w (o e) ≤
          X.tupleRatio Hξ H e.2 (X.TβDel H e.2 (X.tgt b))
            (.hid (X.tgt b)) (o e) *
              (X.tupleRef H e.2 (X.TβDel H e.2 (X.tgt b))
                (.hid (X.tgt b))).w (o e)
        exact le_of_eq hPointEq
    have hPresLeData : X.presProb H P b D o ξ ≤ (X.dataLaw X.Loc Hξ).pr obsData := by
      unfold Ctx6.presProb
      calc
        (X.proxyLaw Hξ).pr (fun ω => X.Presents Hξ (X.assemble P ω) b D o) ≤
            (X.proxyLaw Hξ).pr (fun ω => X.LowGate Hξ b D ξ ∧ obsData ω.1.1) :=
          pr_mono6 _ (fun ω hp => hPresentImp ω hp)
        _ = (X.dataLaw X.Loc Hξ).pr obsData := by
          calc
            (X.proxyLaw Hξ).pr (fun ω => X.LowGate Hξ b D ξ ∧ obsData ω.1.1) =
                (X.proxyLaw Hξ).pr (fun ω => obsData ω.1.1) := by
                  congr 1
                  funext ω
                  simp [hGate]
            _ = (X.dataLaw X.Loc Hξ).pr obsData := hProxyProj obsData
    have hGateOrig : X.LowGate H b D ξ := by
      simpa [Ctx6.LowGate, Ctx6.withHid, Hξ] using hGate
    have hProdDom :
        (∏ e ∈ D, (X.tupleLaw Hξ e.2).w (o e)) ≤
          ∏ e ∈ D, X.lowLik H b ξ e.2 (o e) * (X.lowRef H b e.2).w (o e) := by
      apply Finset.prod_le_prod₀
      · intro e he
        exact (X.tupleLaw Hξ e.2).nonneg (o e)
      · intro e he
        exact hTupleDom e he
    have hProdEq :
        (∏ e ∈ D, X.lowLik H b ξ e.2 (o e) * (X.lowRef H b e.2).w (o e)) =
          X.lowF H b D o ξ * X.lowQ H b D o := by
      rw [Ctx6.lowF, Ctx6.lowQ]
      simp [hGateOrig]
      exact (Finset.prod_mul_distrib (s := D)
        (f := fun e => X.lowLik H b ξ e.2 (o e))
        (g := fun e => (X.lowRef H b e.2).w (o e)))
    calc
      X.presProb H P b D o ξ ≤ (X.dataLaw X.Loc Hξ).pr obsData := hPresLeData
      _ = ∏ e ∈ D, (X.tupleLaw Hξ e.2).w (o e) := hDataPr
      _ ≤ ∏ e ∈ D, X.lowLik H b ξ e.2 (o e) * (X.lowRef H b e.2).w (o e) := hProdDom
      _ = X.lowF H b D o ξ * X.lowQ H b D o := hProdEq
  · have hZero : X.presProb H P b D o ξ = 0 := by
      unfold Ctx6.presProb
      exact pr_zero_of_supp6 (X.proxyLaw Hξ)
        (by intro ω hω hp; exact hExists ⟨ω, hp⟩)
    have hNonneg : 0 ≤ X.lowF H b D o ξ * X.lowQ H b D o :=
      mul_nonneg (hLowFNonneg D o ξ) (hLowQNonneg D o)
    calc
      X.presProb H P b D o ξ = 0 := hZero
      _ ≤ X.lowF H b D o ξ * X.lowQ H b D o := hNonneg

/-- L6.1j (rows, 06:605–620): the adjusted row is at most `e^{.02k} L_b`, keeping `e^{.2k} Q_{−c}` and the caps;
the same bounds for proxy rows. -/
theorem L6_1j_rows (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.TableOK → X.Step3LowBounds → X.Step3HighBounds → X.HistSupport → X.OddRowBounds ∧ X.ProxyCap := by
  have hExp := height_exponents6_admissible p₀ hadm.2.2.1
  have hα : 0 < α₆ p₀ := hExp.1
  let δ := α₆ p₀ / 20
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hRatio : Filter.Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ) ^ δ)
      Filter.atTop (nhds 0) :=
    (_root_.isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp _root_.tendsto_natCast_atTop_atTop
  have hRatioEvent : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (k : ℝ) / (k : ℝ) ^ δ < 1 :=
    hRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨nLog, hnLogEvent⟩ := Filter.eventually_atTop.1 hRatioEvent
  refine ⟨max 300 nLog, 1, fun n N E G M X hL => ?_⟩
  have hnLog : nLog ≤ n := le_trans (le_max_right _ _) hL.1
  intro hTable hLow hHigh hHist
  have hDescIn (H : X.Hist) (C : X.Centre) (b : X.State) (R : ℕ)
      (hb : b ∈ X.g.L.oddStates) (hValid : X.OddValid H C R b) :
      X.actDesc H C R b ∈ X.descsIn b (fun _ => Finset.univ) := by
    classical
    let φ : X.g.L.stNbr b → X.Loc := fun a => (X.choice H C R a.1).getD X.defaultLoc
    have hDesc : X.descOf b φ = X.actDesc H C R b := by rfl
    have hPerm : ∀ a : X.g.L.stNbr b, φ a ∈ (Finset.univ : Finset X.Loc) := by
      intro a
      simp
    have hImage : Finset.univ.image φ = (X.actDesc H C R b).image Prod.fst := by
      let pairFun := fun a : X.g.L.stNbr b => (φ a, X.stType a.1)
      have hPair : X.actDesc H C R b = Finset.univ.image pairFun := by rfl
      calc
        Finset.univ.image φ = Finset.univ.image (Prod.fst ∘ pairFun) := by rfl
        _ = (Finset.univ.image pairFun).image Prod.fst := Finset.image_image.symm
        _ = (X.actDesc H C R b).image Prod.fst := by rw [hPair]
    have hCard : (Finset.univ.image φ).card ≤ X.T := by
      rw [hImage]
      exact hValid.2.2.2.1
    unfold Ctx6.descsIn
    apply Finset.mem_image.mpr
    refine ⟨φ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hDesc⟩
    exact ⟨hPerm, hCard⟩
  have hSafeRatioNonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ safeRatio6 a b := by
    unfold safeRatio6
    split_ifs with hz
    · exact le_rfl
    · exact div_nonneg ha hb
  have hSafeRatioLeOne {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ b) :
      safeRatio6 a b ≤ 1 := by
    unfold safeRatio6
    by_cases hz : b = 0
    · simp [hz]
    · rw [if_neg hz]
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hz)
      exact (div_le_one hbpos).2 hab
  have hTupleRatioNonneg (Hξ H : X.Hist) (β : X.Ty) (refTag : FinProb X.ι)
      (drop : X.Name) (o : X.Tuple) : X.tupleRatio Hξ H β refTag drop o ≥ 0 := by
    unfold Ctx6.tupleRatio
    apply mul_nonneg
    · exact hSafeRatioNonneg ((X.Tβ Hξ β).nonneg o.1) (refTag.nonneg o.1)
    · apply Finset.prod_nonneg
      intro r hr
      exact hSafeRatioNonneg
        ((X.labelLaw Hξ (reqNames6 β) o.1).nonneg (o.2 r))
        ((X.labelLaw H ((reqNames6 β).erase drop) o.1).nonneg (o.2 r))
  have hLowLikNonneg (H : X.Hist) (b : X.State) (ξ : Fin N) (β : X.Ty)
      (o : X.Tuple) : 0 ≤ X.lowLik H b ξ β o := by
    unfold Ctx6.lowLik
    exact hTupleRatioNonneg (X.withHid H (X.tgt b) ξ) H β
      (X.TβDel H β (X.tgt b)) (.hid (X.tgt b)) o
  have hLowFNonneg (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) (ξ : Fin N) : 0 ≤ X.lowF H b D o ξ := by
    unfold Ctx6.lowF
    apply mul_nonneg
    · split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro e he
      exact hLowLikNonneg H b ξ e.2 (o e)
  have hLowQNonneg (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) : 0 ≤ X.lowQ H b D o := by
    unfold Ctx6.lowQ
    apply Finset.prod_nonneg
    intro e he
    exact (X.lowRef H b e.2).nonneg (o e)
  have hTableLeOne (H : X.Hist) (P : X.Loc → Bool) (b : X.State)
      (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) (ξ : Fin N)
      (hBase : X.BaseSupp H.1) (hMode : X.stMode b = .low) : X.table H P b D o ξ ≤ 1 := by
    have hF := hLowFNonneg H b D o ξ
    have hQ := hLowQNonneg H b D o
    have hDen : 0 ≤ X.lowF H b D o ξ * X.lowQ H b D o := mul_nonneg hF hQ
    by_cases hz : X.lowF H b D o ξ * X.lowQ H b D o = 0
    · unfold Ctx6.table HypercubeRamsey.S06.safeRatio6
      simp [hz]
    · have hDenPos : 0 < X.lowF H b D o ξ * X.lowQ H b D o :=
        lt_of_le_of_ne hDen (Ne.symm hz)
      unfold Ctx6.table HypercubeRamsey.S06.safeRatio6
      rw [if_neg hz]
      exact (div_le_one hDenPos).2 (hTable H P b D o ξ hBase hMode)
  have hAdjLeBase (H : X.Hist) (P : X.Loc → Bool) (b : X.State)
      (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc)
      (hBase : X.BaseSupp H.1) (hMode : X.stMode b = .low) (ξ : Fin N) :
      X.adjWeight H P b D o ξ ≤ (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ := by
    have hPrior : 0 ≤ (X.hidPost H.1 (X.tgt b).1).w ξ := (X.hidPost H.1 (X.tgt b).1).nonneg ξ
    calc
      X.adjWeight H P b D o ξ =
          (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ * X.table H P b D o ξ := rfl
      _ ≤ (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ * 1 :=
        mul_le_mul_of_nonneg_left (hTableLeOne H P b D o ξ hBase hMode)
          (mul_nonneg hPrior (hLowFNonneg H b D o ξ))
      _ = (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ := by ring
  have hTableNonneg (H : X.Hist) (P : X.Loc → Bool) (b : X.State)
      (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) (ξ : Fin N) :
      0 ≤ X.table H P b D o ξ := by
    have hF := hLowFNonneg H b D o ξ
    have hQ := hLowQNonneg H b D o
    have hDen : 0 ≤ X.lowF H b D o ξ * X.lowQ H b D o := mul_nonneg hF hQ
    have hPres : 0 ≤ X.presProb H P b D o ξ := by
      unfold Ctx6.presProb
      exact pr_nonneg6 _ _
    exact hSafeRatioNonneg hPres hDen
  let baseWeight (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) (ξ : Fin N) : ℝ :=
    (X.hidPost H.1 (X.tgt b).1).w ξ * X.lowF H b D o ξ
  have hBaseWeightNonneg (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) (ξ : Fin N) : 0 ≤ baseWeight H b D o ξ := by
    have hPrior : 0 ≤ (X.hidPost H.1 (X.tgt b).1).w ξ :=
      (X.hidPost H.1 (X.tgt b).1).nonneg ξ
    exact mul_nonneg hPrior (hLowFNonneg H b D o ξ)
  have hBaseWeightEq (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) (hMode : X.stMode b = .low) (ξ : Fin N) :
      baseWeight H b D o ξ = X.s3Weight H b D o none ξ := by
    simp [baseWeight, Ctx6.s3Weight, hMode, Ctx6.lowWeight, Ctx6.lowF]
  have hAdjWeightNonneg (H : X.Hist) (P : X.Loc → Bool) (b : X.State)
      (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) (ξ : Fin N) :
      0 ≤ X.adjWeight H P b D o ξ := by
    unfold Ctx6.adjWeight
    have hPrior : 0 ≤ (X.hidPost H.1 (X.tgt b).1).w ξ :=
      (X.hidPost H.1 (X.tgt b).1).nonneg ξ
    exact mul_nonneg (mul_nonneg hPrior (hLowFNonneg H b D o ξ)) (hTableNonneg H P b D o ξ)
  have hBaseMassEq (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) (hMode : X.stMode b = .low) :
      (∑ ξ, baseWeight H b D o ξ) = X.s3Mass H b D o none := by
    unfold Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact hBaseWeightEq H b D o hMode ξ
  have hBaseClipEq (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) :
      (∑ ξ, max 0 (baseWeight H b D o ξ)) = ∑ ξ, baseWeight H b D o ξ := by
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact max_eq_right (hBaseWeightNonneg H b D o ξ)
  have hS3PostWeight (H : X.Hist) (b : X.State) (D : Finset (X.Loc × X.Ty))
      (o : X.Data X.Loc) (hMode : X.stMode b = .low) (hTests : X.S3Tests H b D o)
      (ξ : Fin N) :
      (X.s3Post H b D o).w ξ = baseWeight H b D o ξ / ∑ η, baseWeight H b D o η := by
    have hS3ClipEq :
        (∑ η, max 0 (X.s3Weight H b D o none η)) = ∑ η, baseWeight H b D o η := by
      calc
        (∑ η, max 0 (X.s3Weight H b D o none η)) =
            ∑ η, max 0 (baseWeight H b D o η) := by
          apply Finset.sum_congr rfl
          intro η hη
          rw [(hBaseWeightEq H b D o hMode η).symm]
        _ = ∑ η, baseWeight H b D o η := hBaseClipEq H b D o
    have hS3ClipPos : 0 < ∑ η, max 0 (X.s3Weight H b D o none η) := by
      rw [hS3ClipEq, hBaseMassEq H b D o hMode]
      exact hTests.1
    unfold Ctx6.s3Post normalize6
    simp only [dif_pos hS3ClipPos]
    have hNum : max 0 (X.s3Weight H b D o none ξ) = baseWeight H b D o ξ := by
      rw [← hBaseWeightEq H b D o hMode ξ]
      exact max_eq_right (hBaseWeightNonneg H b D o ξ)
    rw [hNum, hS3ClipEq]
  have hLowRowDom (H : X.Hist) (P : X.Loc → Bool) (b : X.State)
      (D : Finset (X.Loc × X.Ty)) (o : X.Data X.Loc) (hBase : X.BaseSupp H.1)
      (hMode : X.stMode b = .low) (hTests : X.S3Tests H b D o) :
      ∀ ξ, (X.lowRow H P b D o).w ξ ≤
        Real.exp ((2 / 100 : ℝ) * X.k) * (X.s3Post H b D o).w ξ := by
    intro ξ
    have hThrPos : 0 < X.s3Thr := Real.exp_pos _
    have hBaseMassPos : 0 < ∑ η, baseWeight H b D o η := by
      rw [hBaseMassEq H b D o hMode]
      exact hTests.1
    have hBaseClipEq := hBaseClipEq H b D o
    have hBaseClipPos : 0 < ∑ η, max 0 (baseWeight H b D o η) := by
      rw [hBaseClipEq]
      exact hBaseMassPos
    unfold Ctx6.lowRow
    by_cases hAdjust : X.s3Thr * (∑ η, baseWeight H b D o η) ≤
        ∑ η, X.adjWeight H P b D o η
    · rw [if_pos (by simpa [baseWeight] using hAdjust)]
      have hAdjSumEq :
          (∑ η, max 0 (X.adjWeight H P b D o η)) =
            ∑ η, X.adjWeight H P b D o η := by
        apply Finset.sum_congr rfl
        intro η hη
        exact max_eq_right (hAdjWeightNonneg H P b D o η)
      have hAdjSumPos : 0 < ∑ η, X.adjWeight H P b D o η := by
        have h := hAdjust
        nlinarith [hThrPos, hBaseMassPos]
      have hAdjClipPos : 0 < ∑ η, max 0 (X.adjWeight H P b D o η) := by
        rw [hAdjSumEq]
        exact hAdjSumPos
      have hAdjNorm : (normalize6 (X.adjWeight H P b D o) X.y₀).w ξ =
          X.adjWeight H P b D o ξ / ∑ η, X.adjWeight H P b D o η := by
        unfold normalize6
        simp only [dif_pos hAdjClipPos]
        rw [max_eq_right (hAdjWeightNonneg H P b D o ξ), hAdjSumEq]
      rw [hAdjNorm, hS3PostWeight H b D o hMode hTests ξ]
      have hFactor : Real.exp ((2 / 100 : ℝ) * X.k) = 1 / X.s3Thr := by
        simp [Ctx6.s3Thr, Real.exp_neg]
      rw [hFactor]
      have hCross : X.adjWeight H P b D o ξ *
          (X.s3Thr * ∑ η, baseWeight H b D o η) ≤
            baseWeight H b D o ξ * (∑ η, X.adjWeight H P b D o η) := by
        calc
          X.adjWeight H P b D o ξ * (X.s3Thr * ∑ η, baseWeight H b D o η) ≤
              baseWeight H b D o ξ * (X.s3Thr * ∑ η, baseWeight H b D o η) :=
            mul_le_mul_of_nonneg_right
              (hAdjLeBase H P b D o hBase hMode ξ)
              (mul_nonneg hThrPos.le hBaseMassPos.le)
          _ ≤ baseWeight H b D o ξ * (∑ η, X.adjWeight H P b D o η) :=
            mul_le_mul_of_nonneg_left hAdjust (hBaseWeightNonneg H b D o ξ)
      have hRatio := (div_le_div_iff₀ hAdjSumPos (mul_pos hThrPos hBaseMassPos)).2 hCross
      calc
        X.adjWeight H P b D o ξ / (∑ η, X.adjWeight H P b D o η) ≤
            baseWeight H b D o ξ / (X.s3Thr * ∑ η, baseWeight H b D o η) := hRatio
        _ = 1 / X.s3Thr *
              (baseWeight H b D o ξ / ∑ η, baseWeight H b D o η) := by
          field_simp [ne_of_gt hThrPos, ne_of_gt hBaseMassPos]
    · rw [if_neg (by simpa [baseWeight] using hAdjust)]
      have hExpOne : (1 : ℝ) ≤ Real.exp ((2 / 100 : ℝ) * X.k) := by
        have hArg : 0 ≤ (2 / 100 : ℝ) * X.k := by positivity
        linarith [Real.add_one_le_exp ((2 / 100 : ℝ) * X.k)]
      calc
        (X.s3Post H b D o).w ξ = 1 * (X.s3Post H b D o).w ξ := by ring
        _ ≤ Real.exp ((2 / 100 : ℝ) * X.k) * (X.s3Post H b D o).w ξ :=
          mul_le_mul_of_nonneg_right hExpOne ((X.s3Post H b D o).nonneg ξ)
  have hn300 : 300 ≤ n := le_trans (le_max_left _ _) hL.1
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hLogRatio := hnLogEvent n hnLog
  have hLogBound : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ := by
    have hpowPos : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos hnPos _
    exact (div_lt_one hpowPos).1 hLogRatio |>.le
  have hmLower : (n : ℝ) ^ α₆ p₀ ≤ (X.m : ℝ) := by
    change (n : ℝ) ^ α₆ p₀ ≤ (X.g.L.m : ℝ)
    rw [X.g.m_eq]
    exact Nat.le_ceil _
  have hmNatPos : 0 < X.m := by
    change 0 < X.g.L.m
    rw [X.g.m_eq]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnPos _)
  have hm1 : (1 : ℝ) ≤ X.m := by exact_mod_cast (show 1 ≤ X.m by omega)
  have hDeltaPow : (n : ℝ) ^ δ = ((n : ℝ) ^ α₆ p₀) ^ (1 / 20 : ℝ) := by
    rw [show δ = α₆ p₀ * (1 / 20 : ℝ) by dsimp [δ]; ring, Real.rpow_mul (by positivity)]
  have hLogM : (n : ℝ) ^ δ ≤ (X.m : ℝ) ^ (1 / 20 : ℝ) := by
    rw [hDeltaPow]
    exact Real.rpow_le_rpow (by positivity) hmLower (by norm_num)
  have hLogMDirect : Real.log (n : ℝ) ≤ (X.m : ℝ) ^ (1 / 20 : ℝ) := hLogBound.trans hLogM
  have hJle : (X.J : ℝ) ≤ (X.m : ℝ) ^ (1 / 25 : ℝ) := by
    change (J₆ X.g.L.m : ℝ) ≤ (X.g.L.m : ℝ) ^ (1 / 25 : ℝ)
    exact Nat.floor_le (by positivity)
  have hJLog : (X.J : ℝ) * Real.log (n : ℝ) ≤ (X.m : ℝ) ^ (9 / 100 : ℝ) := by
    calc
      (X.J : ℝ) * Real.log (n : ℝ) ≤
          (X.m : ℝ) ^ (1 / 25 : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hJle (Real.log_nonneg hn1)
      _ ≤ (X.m : ℝ) ^ (1 / 25 : ℝ) * (X.m : ℝ) ^ (1 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_left hLogMDirect (Real.rpow_nonneg (by positivity) _)
      _ = (X.m : ℝ) ^ (9 / 100 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        norm_num
  have hkBound : (X.k : ℝ) ≤ κ₆ * (X.J : ℝ) * Real.log n + 1 := by
    change (Nat.ceil (κ₆ * (J₆ X.g.L.m : ℝ) * Real.log n) : ℝ) ≤ _
    have hq : 0 ≤ κ₆ * (J₆ X.g.L.m : ℝ) * Real.log n :=
      mul_nonneg (mul_nonneg (by norm_num [κ₆]) (Nat.cast_nonneg _)) (Real.log_nonneg hn1)
    exact (Nat.ceil_lt_add_one hq).le
  have hKsmall : (2 / 100 : ℝ) * X.k ≤
      (2 / 100 : ℝ) * κ₆ * (X.m : ℝ) ^ (9 / 100 : ℝ) + 2 / 100 := by
    calc
      (2 / 100 : ℝ) * X.k ≤
          (2 / 100 : ℝ) * (κ₆ * (X.J : ℝ) * Real.log n + 1) :=
        mul_le_mul_of_nonneg_left hkBound (by norm_num)
      _ = (2 / 100 : ℝ) * κ₆ * ((X.J : ℝ) * Real.log n) + 2 / 100 := by ring
      _ ≤ (2 / 100 : ℝ) * κ₆ * (X.m : ℝ) ^ (9 / 100 : ℝ) + 2 / 100 := by
        have hCoeffPos : 0 ≤ (2 / 100 : ℝ) * κ₆ := by norm_num [κ₆]
        calc
          (2 / 100 : ℝ) * κ₆ * ((X.J : ℝ) * Real.log n) + 2 / 100 =
              2 / 100 + (2 / 100 : ℝ) * κ₆ * ((X.J : ℝ) * Real.log n) := by ring
          _ ≤ 2 / 100 + (2 / 100 : ℝ) * κ₆ * (X.m : ℝ) ^ (9 / 100 : ℝ) :=
            add_le_add_right (mul_le_mul_of_nonneg_left hJLog hCoeffPos) _
          _ = (2 / 100 : ℝ) * κ₆ * (X.m : ℝ) ^ (9 / 100 : ℝ) + 2 / 100 := by ring
  have hCoeff : (2 / 100 : ℝ) * κ₆ + 2 / 100 ≤ 1 / 2 := by norm_num [κ₆]
  have hm09one : (1 : ℝ) ≤ (X.m : ℝ) ^ (9 / 100 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num : (0 : ℝ) ≤ 9 / 100)
    simpa using h
  have hm0915 : (X.m : ℝ) ^ (9 / 100 : ℝ) ≤ (X.m : ℝ) ^ (15 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hKMargin : (2 / 100 : ℝ) * X.k ≤ (X.m : ℝ) ^ (15 / 100 : ℝ) / 2 := by
    have hsmall :
        (2 / 100 : ℝ) * κ₆ * (X.m : ℝ) ^ (9 / 100 : ℝ) + 2 / 100 ≤
          (1 / 2 : ℝ) * (X.m : ℝ) ^ (9 / 100 : ℝ) := by
      have hpowNonneg : 0 ≤ (X.m : ℝ) ^ (9 / 100 : ℝ) := Real.rpow_nonneg (by positivity) _
      nlinarith [mul_le_mul_of_nonneg_right hCoeff hpowNonneg, hm09one]
    calc
      (2 / 100 : ℝ) * X.k ≤
          (2 / 100 : ℝ) * κ₆ * (X.m : ℝ) ^ (9 / 100 : ℝ) + 2 / 100 := hKsmall
      _ ≤ (1 / 2 : ℝ) * (X.m : ℝ) ^ (9 / 100 : ℝ) := hsmall
      _ ≤ (1 / 2 : ℝ) * (X.m : ℝ) ^ (15 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hm0915 (by norm_num)
      _ = (X.m : ℝ) ^ (15 / 100 : ℝ) / 2 := by ring
  have hOddRows : X.OddRowBounds := by
    intro H C u hH hu hValid
    let b := X.g.L.stateOf u
    have hbOdd : b ∈ X.g.L.oddStates := by
      unfold b ChunkLayout6.oddStates
      exact Finset.mem_image.mpr
        ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
    rcases hHist H hH with ⟨hBase, _hHid, _hV0, _hStep1, _hStep2, _hRates⟩
    let D := X.actDesc H C X.Rlong b
    have hD : D ∈ X.descsIn b (fun _ => Finset.univ) := hDescIn H C b X.Rlong hbOdd hValid
    have hTests : X.S3Tests H b D (X.tup C) := hValid.2.2.2.2.2
    cases hMode : X.stMode b
    · have hRowEq (y : Fin N) : X.oddRow H C u y = (X.lowRow H (X.pos C) b D (X.tup C)).w y := by
        simp [Ctx6.oddRow, Ctx6.oddRowAt, b, D, hValid, hMode]
      have hStep := hLow X.Loc b (fun _ => Finset.univ) hbOdd hMode D hD H (X.tup C) hBase hTests
      obtain ⟨hDel, hCap, hSupport⟩ := hStep
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro y
        rw [hRowEq y]
        exact (X.lowRow H (X.pos C) b D (X.tup C)).nonneg y
      · calc
          (∑ y, X.oddRow H C u y) = ∑ y, (X.lowRow H (X.pos C) b D (X.tup C)).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hRowEq y
          _ = 1 := (X.lowRow H (X.pos C) b D (X.tup C)).sum_eq_one
      · intro y
        have hrow := hLowRowDom H (X.pos C) b D (X.tup C) hBase hMode hTests y
        calc
          (N : ℝ) * X.oddRow H C u y = (N : ℝ) * (X.lowRow H (X.pos C) b D (X.tup C)).w y := by
            rw [hRowEq y]
          _ ≤ (N : ℝ) * (Real.exp ((2 / 100 : ℝ) * X.k) * (X.s3Post H b D (X.tup C)).w y) :=
            mul_le_mul_of_nonneg_left hrow (by positivity)
          _ = Real.exp ((2 / 100 : ℝ) * X.k) *
              ((N : ℝ) * (X.s3Post H b D (X.tup C)).w y) := by ring
          _ ≤ Real.exp ((2 / 100 : ℝ) * X.k) * Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (hCap y) (Real.exp_nonneg _)
          _ = Real.exp ((2 / 100 : ℝ) * X.k + (X.m : ℝ) ^ (15 / 100 : ℝ) / 2) := by
            rw [← Real.exp_add]
          _ ≤ Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) :=
            Real.exp_le_exp.mpr (by linarith [hKMargin])
      · intro y hrow e he r
        have hrowEq := hRowEq y
        rw [hrowEq] at hrow
        have hrowPos : 0 < (X.lowRow H (X.pos C) b D (X.tup C)).w y :=
          lt_of_le_of_ne ((X.lowRow H (X.pos C) b D (X.tup C)).nonneg y) (Ne.symm hrow)
        have hpostNonneg := (X.s3Post H b D (X.tup C)).nonneg y
        have hpostPos : 0 < (X.s3Post H b D (X.tup C)).w y := by
          by_contra hnot
          have hzero : (X.s3Post H b D (X.tup C)).w y = 0 := le_antisymm (le_of_not_gt hnot) hpostNonneg
          have hdom := hLowRowDom H (X.pos C) b D (X.tup C) hBase hMode hTests y
          rw [hzero] at hdom
          simp at hdom
          linarith
        have hhit := hSupport y hpostPos e he r
        exact hhit
      · intro c hc hmatching y
        have hrow := hLowRowDom H (X.pos C) b D (X.tup C) hBase hMode hTests y
        have hdel := hDel c hc hmatching y
        calc
          X.oddRow H C u y ≤ Real.exp ((2 / 100 : ℝ) * X.k) * (X.s3Post H b D (X.tup C)).w y := by
            rw [hRowEq y]
            exact hrow
          _ ≤ Real.exp ((2 / 100 : ℝ) * X.k) *
              (Real.exp ((16 / 100 : ℝ) * X.k) * (X.s3Del H b D (X.tup C) c).w y) :=
            mul_le_mul_of_nonneg_left hdel (Real.exp_nonneg _)
          _ = Real.exp ((18 / 100 : ℝ) * X.k) * (X.s3Del H b D (X.tup C) c).w y := by
            calc
              Real.exp ((2 / 100 : ℝ) * X.k) *
                  (Real.exp ((16 / 100 : ℝ) * X.k) * (X.s3Del H b D (X.tup C) c).w y) =
                  (Real.exp ((2 / 100 : ℝ) * X.k) * Real.exp ((16 / 100 : ℝ) * X.k)) *
                    (X.s3Del H b D (X.tup C) c).w y := by ring
              _ = Real.exp ((18 / 100 : ℝ) * X.k) * (X.s3Del H b D (X.tup C) c).w y := by
                rw [← Real.exp_add]
                congr 1
                ring_nf
          _ ≤ Real.exp ((2 / 10 : ℝ) * X.k) * (X.s3Del H b D (X.tup C) c).w y :=
            mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ X.k by positivity]))
              ((X.s3Del H b D (X.tup C) c).nonneg y)
    · have hRowEq (y : Fin N) : X.oddRow H C u y = (X.s3Post H b D (X.tup C)).w y := by
        simp [Ctx6.oddRow, Ctx6.oddRowAt, b, D, hValid, hMode]
      have hStep := hHigh X.Loc b (fun _ => Finset.univ) hbOdd hMode D hD H (X.tup C) hBase hTests
      obtain ⟨hDel, hCap, hSupport⟩ := hStep
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro y
        rw [hRowEq y]
        exact (X.s3Post H b D (X.tup C)).nonneg y
      · calc
          (∑ y, X.oddRow H C u y) = ∑ y, (X.s3Post H b D (X.tup C)).w y := by
            apply Finset.sum_congr rfl
            intro y hy
            exact hRowEq y
          _ = 1 := (X.s3Post H b D (X.tup C)).sum_eq_one
      · intro y
        rw [hRowEq y]
        simpa using hCap y
      · intro y hrow e he r
        rw [hRowEq y] at hrow
        have hrowPos : 0 < (X.s3Post H b D (X.tup C)).w y :=
          lt_of_le_of_ne ((X.s3Post H b D (X.tup C)).nonneg y) (Ne.symm hrow)
        exact hSupport y hrowPos e he r
      · intro c hc hmatching y
        rw [hRowEq y]
        have hdel := hDel c hc hmatching y
        exact hdel.trans <| mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ X.k by positivity]))
          ((X.s3Del H b D (X.tup C) c).nonneg y)
  have hProxyCap : X.ProxyCap := by
    intro H C u hH hu hValid y
    let b := X.g.L.stateOf u
    have hbOdd : b ∈ X.g.L.oddStates := by
      unfold b ChunkLayout6.oddStates
      exact Finset.mem_image.mpr
        ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
    rcases hHist H hH with ⟨hBase, _hHid, _hV0, _hStep1, _hStep2, _hRates⟩
    let D := X.actDesc H C X.Rshort b
    have hD : D ∈ X.descsIn b (fun _ => Finset.univ) := hDescIn H C b X.Rshort hbOdd hValid
    have hTests : X.S3Tests H b D (X.tup C) := hValid.2.2.2.2.2
    cases hMode : X.stMode b
    · have hRowEq : X.proxyRow H C u y = (X.lowRow H (X.pos C) b D (X.tup C)).w y := by
        simp [Ctx6.proxyRow, Ctx6.oddRowAt, b, D, hValid, hMode]
      have hStep := hLow X.Loc b (fun _ => Finset.univ) hbOdd hMode D hD H (X.tup C) hBase hTests
      obtain ⟨_hDel, hCap, _hSupport⟩ := hStep
      refine ⟨?_, ?_⟩
      · rw [hRowEq]
        exact (X.lowRow H (X.pos C) b D (X.tup C)).nonneg y
      · have hrow := hLowRowDom H (X.pos C) b D (X.tup C) hBase hMode hTests y
        calc
          (N : ℝ) * X.proxyRow H C u y =
              (N : ℝ) * (X.lowRow H (X.pos C) b D (X.tup C)).w y := by rw [hRowEq]
          _ ≤ (N : ℝ) * (Real.exp ((2 / 100 : ℝ) * X.k) * (X.s3Post H b D (X.tup C)).w y) :=
            mul_le_mul_of_nonneg_left hrow (by positivity)
          _ = Real.exp ((2 / 100 : ℝ) * X.k) *
              ((N : ℝ) * (X.s3Post H b D (X.tup C)).w y) := by ring
          _ ≤ Real.exp ((2 / 100 : ℝ) * X.k) * Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (hCap y) (Real.exp_nonneg _)
          _ = Real.exp ((2 / 100 : ℝ) * X.k + (X.m : ℝ) ^ (15 / 100 : ℝ) / 2) := by
            rw [← Real.exp_add]
          _ ≤ Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) :=
            Real.exp_le_exp.mpr (by linarith [hKMargin])
    · have hRowEq : X.proxyRow H C u y = (X.s3Post H b D (X.tup C)).w y := by
        simp [Ctx6.proxyRow, Ctx6.oddRowAt, b, D, hValid, hMode]
      have hStep := hHigh X.Loc b (fun _ => Finset.univ) hbOdd hMode D hD H (X.tup C) hBase hTests
      obtain ⟨_hDel, hCap, _hSupport⟩ := hStep
      refine ⟨?_, ?_⟩
      · rw [hRowEq]
        exact (X.s3Post H b D (X.tup C)).nonneg y
      · rw [hRowEq]
        exact hCap y
  exact ⟨hOddRows, hProxyCap⟩

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
  have hExp := height_exponents6_admissible p₀ hadm.2.2.1
  rcases hExp with ⟨hα, _, _, hθ, hαrange, ⟨hAdm⟩⟩
  let reg : HDRegime (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀)) D₀₆ :=
    .lin (1 / 400) ⟨by norm_num, by norm_num⟩
  obtain ⟨nShort, hshort⟩ :=
    height_selection_short J₀₆ (b₀₆ (α₆ p₀)) (b₆ (α₆ p₀)) (σ₆ (α₆ p₀))
      (ζ₆ (α₆ p₀)) (θ₆ (α₆ p₀)) (a₆ (α₆ p₀)) cd₆ Cd₆ (α₆ p₀) D₀₆ hAdm reg hθ
      ⟨hα, hαrange⟩
  let δ := α₆ p₀ / 20
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hLogRatio : Filter.Tendsto (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ) ^ δ)
      Filter.atTop (nhds 0) :=
    (_root_.isLittleO_log_rpow_atTop hδ).tendsto_div_nhds_zero.comp _root_.tendsto_natCast_atTop_atTop
  have hLogEvent : ∀ᶠ k : ℕ in Filter.atTop,
      Real.log (k : ℝ) / (k : ℝ) ^ δ < 1 :=
    hLogRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨nLog, hnLogEvent⟩ := Filter.eventually_atTop.1 hLogEvent
  have hPowM20 : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (α₆ p₀ / 5)) Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by positivity)).comp _root_.tendsto_natCast_atTop_atTop
  obtain ⟨nM20, hnM20Event⟩ :=
    Filter.eventually_atTop.1 (hPowM20.eventually_ge_atTop 10)
  refine ⟨max 300 (max nShort (max nLog nM20)), 1, fun n N E G M X hL => ?_⟩
  have hn300 : 300 ≤ n := le_trans (le_max_left _ _) hL.1
  have hnAux : max nShort (max nLog nM20) ≤ n := le_trans (le_max_right _ _) hL.1
  have hnShort : nShort ≤ n := le_trans (le_max_left _ _) hnAux
  have hnLog : nLog ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hnAux)
  have hnM20 : nM20 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hnAux)
  have hStateEven {a b' : X.State} (ha : a ∈ X.g.L.stNbr b') : a ∈ X.g.L.evenStates := by
    classical
    unfold ChunkLayout6.stNbr at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rcases ha with ⟨u', v', _hu', hv', _hb', hst, _hadj⟩
    unfold ChunkLayout6.evenStates
    exact Finset.mem_image.mpr ⟨v', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩, hst⟩
  have hSiteMem {a b' : X.State} (ha : a ∈ X.g.L.stNbr b') : X.site a ∈ X.sites := by
    rw [Ctx6.sites]
    exact Finset.mem_image.mpr ⟨a, hStateEven ha, rfl⟩
  have hn200 : 200 ≤ n := by omega
  have hn200r : (200 : ℝ) ≤ n := by exact_mod_cast hn200
  have hrEq : X.hp.r = ⌊(1 / 100 : ℝ) * n⌋₊ := by rfl
  have hrLower : (n : ℝ) / 200 ≤ (X.hp.r : ℝ) := by
    rw [hrEq]
    have hfloor := Nat.lt_floor_add_one ((1 / 100 : ℝ) * n)
    nlinarith [hfloor, hn200r]
  have hrUpper : (X.hp.r : ℝ) ≤ (n : ℝ) / 100 := by
    rw [hrEq]
    calc
      (⌊(1 / 100 : ℝ) * n⌋₊ : ℝ) ≤ (1 / 100 : ℝ) * n :=
        Nat.floor_le (by positivity)
      _ = (n : ℝ) / 100 := by ring
  have hdUpper : (X.hp.d : ℝ) ≤ 2 * n := X.code.d_upper
  have hdLower : (1 / 2 : ℝ) * n ≤ X.hp.d := X.code.d_lower
  have hreg : reg.ok n X.hp.d X.hp.r := by
    constructor
    · calc
        (1 / 400 : ℝ) * X.hp.d ≤ (1 / 400 : ℝ) * (2 * n) :=
          mul_le_mul_of_nonneg_left hdUpper (by norm_num)
        _ = (n : ℝ) / 200 := by ring
        _ ≤ (X.hp.r : ℝ) := hrLower
    · have hfour : (4 : ℝ) * (X.hp.r : ℝ) ≤ X.hp.d := by
        calc
          (4 : ℝ) * (X.hp.r : ℝ) ≤ 4 * ((n : ℝ) / 100) :=
            mul_le_mul_of_nonneg_left hrUpper (by norm_num)
          _ ≤ (1 / 2 : ℝ) * n := by nlinarith
          _ ≤ X.hp.d := hdLower
      exact_mod_cast hfour
  have hPrProdFst {A B : Type} [Fintype A] [Fintype B]
      (P : FinProb A) (Q : FinProb B) (ev : A → Prop) :
      (P.prod Q).pr (fun z => ev z.1) = P.pr ev := by
    classical
    unfold FinProb.pr FinProb.prod
    rw [Fintype.sum_prod_type]
    calc
      (∑ a, ∑ b, if ev a then P.w a * Q.w b else 0) =
          ∑ a, if ev a then P.w a * ∑ b, Q.w b else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : ev a <;> simp [h, Finset.mul_sum]
      _ = ∑ a, if ev a then P.w a else 0 := by simp [Q.sum_eq_one]
  have hPrFinsetUnion {A Ω : Type} [Fintype A] [Fintype Ω]
      (P : FinProb Ω) (S : Finset A) (ev : A → Ω → Prop) (q : ℝ)
      (hbound : ∀ a ∈ S, P.pr (fun ω => ev a ω) ≤ q) :
      P.pr (fun ω => ∃ a ∈ S, ev a ω) ≤ (S.card : ℝ) * q := by
    classical
    revert hbound
    induction S using Finset.induction_on with
    | empty =>
        intro hbound
        simp [FinProb.pr]
    | @insert a S ha ih =>
        intro hbound
        have hboundS : ∀ x ∈ S, P.pr (fun ω => ev x ω) ≤ q := by
          intro x hx
          exact hbound x (Finset.mem_insert_of_mem hx)
        have hEventEq (ω : Ω) :
            (∃ x ∈ insert a S, ev x ω) ↔ (ev a ω ∨ ∃ x ∈ S, ev x ω) := by
          constructor
          · rintro ⟨x, hx, hEv⟩
            rcases Finset.mem_insert.mp hx with hxa | hxS
            · subst x
              exact Or.inl hEv
            · exact Or.inr ⟨x, hxS, hEv⟩
          · rintro (hEv | ⟨x, hxS, hEv⟩)
            · exact ⟨a, Finset.mem_insert_self _ _, hEv⟩
            · exact ⟨x, Finset.mem_insert_of_mem hxS, hEv⟩
        have hEventFun :
            (fun ω => ∃ x ∈ insert a S, ev x ω) =
              (fun ω => ev a ω ∨ ∃ x ∈ S, ev x ω) := by
          funext ω
          exact propext (hEventEq ω)
        calc
          P.pr (fun ω => ∃ x ∈ insert a S, ev x ω) =
              P.pr (fun ω => ev a ω ∨ ∃ x ∈ S, ev x ω) := by rw [hEventFun]
          _ ≤ P.pr (fun ω => ev a ω) + P.pr (fun ω => ∃ x ∈ S, ev x ω) := pr_or_le6 P _ _
          _ ≤ q + (S.card : ℝ) * q := add_le_add (hbound a (Finset.mem_insert_self _ _)) (ih hboundS)
          _ = (insert a S).card * q := by
            rw [Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
            ring
  have hLogRatioN := hnLogEvent n hnLog
  have hLogBound : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ := by
    have hp : 0 < (n : ℝ) ^ δ := Real.rpow_pos_of_pos (by positivity) _
    exact (div_lt_one hp).1 hLogRatioN |>.le
  have hmLower : (n : ℝ) ^ α₆ p₀ ≤ (X.m : ℝ) := by
    change (n : ℝ) ^ α₆ p₀ ≤ (X.g.L.m : ℝ)
    rw [X.g.m_eq]
    exact Nat.le_ceil _
  have hmNatPos : 0 < X.m := by
    change 0 < X.g.L.m
    rw [X.g.m_eq]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  have hm1 : (1 : ℝ) ≤ X.m := by exact_mod_cast (show 1 ≤ X.m by omega)
  have hDeltaPow : (n : ℝ) ^ δ = ((n : ℝ) ^ α₆ p₀) ^ (1 / 20 : ℝ) := by
    rw [show δ = α₆ p₀ * (1 / 20 : ℝ) by dsimp [δ]; ring, Real.rpow_mul (by positivity)]
  have hLogM : (n : ℝ) ^ δ ≤ (X.m : ℝ) ^ (1 / 20 : ℝ) := by
    rw [hDeltaPow]
    exact Real.rpow_le_rpow (by positivity) hmLower (by norm_num)
  have hLogMDirect : Real.log (n : ℝ) ≤ (X.m : ℝ) ^ (1 / 20 : ℝ) := hLogBound.trans hLogM
  have hJle : (X.J : ℝ) ≤ (X.m : ℝ) ^ (1 / 25 : ℝ) := by
    change (J₆ X.g.L.m : ℝ) ≤ (X.g.L.m : ℝ) ^ (1 / 25 : ℝ)
    exact Nat.floor_le (by positivity)
  have hJLog : (X.J : ℝ) * Real.log (n : ℝ) ≤ (X.m : ℝ) ^ (9 / 100 : ℝ) := by
    calc
      (X.J : ℝ) * Real.log (n : ℝ) ≤
          (X.m : ℝ) ^ (1 / 25 : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hJle (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
      _ ≤ (X.m : ℝ) ^ (1 / 25 : ℝ) * (X.m : ℝ) ^ (1 / 20 : ℝ) :=
        mul_le_mul_of_nonneg_left hLogMDirect (Real.rpow_nonneg (by positivity) _)
      _ = (X.m : ℝ) ^ (9 / 100 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        norm_num
  have hmPow20 : 10 ≤ (X.m : ℝ) ^ (1 / 5 : ℝ) := by
    have hComp : (n : ℝ) ^ (α₆ p₀ / 5) = ((n : ℝ) ^ α₆ p₀) ^ (1 / 5 : ℝ) := by
      rw [show α₆ p₀ / 5 = α₆ p₀ * (1 / 5 : ℝ) by ring, Real.rpow_mul (by positivity)]
    have hLow : (n : ℝ) ^ (α₆ p₀ / 5) ≤ (X.m : ℝ) ^ (1 / 5 : ℝ) := by
      rw [hComp]
      exact Real.rpow_le_rpow (by positivity) hmLower (by norm_num)
    exact le_trans (hnM20Event n hnM20) hLow
  intro hCounts hMarks hElig hRows
  intro H u hHistU hu y
  let b := X.g.L.stateOf u
  have hbOdd : b ∈ X.g.L.oddStates := by
    unfold b ChunkLayout6.oddStates
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
  let Esel : (X.Loc → Bool) → X.Data X.Loc → X.hp.EligMap := fun P d =>
    X.elig H (((P, d), fun _ => false), fun _ => Equiv.refl _)
  let shortLevelCount : ℕ := ⌈(n : ℝ) ^ α₆ p₀⌉₊
  let Pbase : FinProb (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) :=
    ((X.hp.posLaw.prod (X.dataLaw X.Loc H)).prod X.hp.actLaw)
  let Pshort : FinProb (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) :=
    ((X.hp.posLawForced none).prod (X.dataLaw X.Loc H)).prod X.hp.actLaw
  have hPosWeightEq (P : X.Loc → Bool) :
      (X.hp.posLawForced none).w P = X.hp.posLaw.w P := by
    simp [HDParams.posLawForced, HDParams.posLaw, FinProb.pi]
  have hBaseShortPr (A : (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) → Prop) :
      Pbase.pr A = Pshort.pr A := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro z hz
    simp [Pbase, Pshort, FinProb.prod, hPosWeightEq]
  have hCentreProj (A : (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) → Prop) :
      (X.centreLaw H).pr (fun C => A ((X.pos C, X.tup C), X.act C)) = Pbase.pr A := by
    simpa [Ctx6.centreLaw, Ctx6.pos, Ctx6.tup, Ctx6.act, Pbase] using
      (hPrProdFst Pbase X.hp.tieLaw A)
  have hShortAt (a : X.State) (ha : a ∈ X.g.L.stNbr b) :
      (X.centreLaw H).pr (fun C => X.EligOK H C ∧
        X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong (X.site a) ≠
          X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) (X.hp.Rshort shortLevelCount) (X.site a)) ≤
        Real.exp (-3 * (shortLevelCount : ℝ) ^ (1 / 5 : ℝ)) := by
    let v : CubeVertex X.hp.d := X.site a
    have hv : v ∈ X.sites := hSiteMem ha
    let shortBad : (((X.Loc → Bool) × X.Data X.Loc) × (X.Loc → Bool)) → Prop := fun ω =>
      X.hp.Legal ω.1.1 (Esel ω.1.1 ω.1.2)
          (X.hp.domBall X.sites v X.hp.Rlong) ∧
        X.hp.height X.sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) X.hp.Rlong v ≠
          X.hp.height X.sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)
            (X.hp.Rshort shortLevelCount) v
    have hImp (C : X.Centre) :
        X.EligOK H C ∧
          X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong v ≠
            X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C)
              (X.hp.Rshort shortLevelCount) v → shortBad ((X.pos C, X.tup C), X.act C) := by
      rintro ⟨hLegal, hDiff⟩
      have hEligC : X.elig H C = Esel (X.pos C) (X.tup C) := rfl
      refine ⟨?_, ?_⟩
      · intro w hw j
        have hwSite : w ∈ X.sites := (Finset.mem_filter.mp hw).1
        have hAt := hLegal w hwSite j
        rw [hEligC] at hAt
        change X.hp.LegalAt (X.pos C) (Esel (X.pos C) (X.tup C)) w j
        exact hAt
      · rw [hEligC] at hDiff
        change X.hp.height X.sites (X.pos C) (X.act C)
          (Esel (X.pos C) (X.tup C)) X.hp.Rlong v ≠
          X.hp.height X.sites (X.pos C) (X.act C)
            (Esel (X.pos C) (X.tup C)) (X.hp.Rshort shortLevelCount) v
        exact hDiff
    have hmono := pr_mono6 (X.centreLaw H)
      (A := fun C => X.EligOK H C ∧
          X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong v ≠
            X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) (X.hp.Rshort shortLevelCount) v)
      (B := fun C => shortBad ((X.pos C, X.tup C), X.act C)) hImp
    have hshortBound := hshort X.hp rfl rfl rfl rfl rfl hnShort X.code.d_lower X.code.d_upper hreg
      X.sites v hv none (X.dataLaw X.Loc H) Esel
    calc
      (X.centreLaw H).pr (fun C => X.EligOK H C ∧
          X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong v ≠
            X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C)
              (X.hp.Rshort shortLevelCount) v) ≤
          (X.centreLaw H).pr (fun C => shortBad ((X.pos C, X.tup C), X.act C)) := hmono
      _ = Pbase.pr shortBad := hCentreProj shortBad
      _ = Pshort.pr shortBad := hBaseShortPr shortBad
      _ ≤ Real.exp (-3 * (shortLevelCount : ℝ) ^ (1 / 5 : ℝ)) := by
        change (((X.hp.posLawForced none).prod (X.dataLaw X.Loc H)).prod X.hp.actLaw).pr
          (fun ω => X.hp.Legal ω.1.1 (Esel ω.1.1 ω.1.2)
              (X.hp.domBall X.sites v X.hp.Rlong) ∧
            X.hp.height X.sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) X.hp.Rlong v ≠
              X.hp.height X.sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)
                (X.hp.Rshort shortLevelCount) v) ≤
          Real.exp (-3 * (shortLevelCount : ℝ) ^ (1 / 5 : ℝ))
        exact hshortBound
  have hShortLevel : shortLevelCount = X.m := by
    dsimp [shortLevelCount, Ctx6.m]
    exact X.g.m_eq.symm
  let shortErr : ℝ := Real.exp (-3 * (shortLevelCount : ℝ) ^ (1 / 5 : ℝ))
  have hShortErrNonneg : 0 ≤ shortErr := by
    dsimp [shortErr]
    positivity
  let badHeight : X.Centre → Prop := fun C =>
    ∃ a ∈ X.g.L.stNbr b, X.EligOK H C ∧
      X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong (X.site a) ≠
        X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C)
          (X.hp.Rshort shortLevelCount) (X.site a)
  have hBadHeight :
      (X.centreLaw H).pr badHeight ≤ ((X.g.L.stNbr b).card : ℝ) * shortErr := by
    exact hPrFinsetUnion (X.centreLaw H) (X.g.L.stNbr b)
      (fun a C => X.EligOK H C ∧
        X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong (X.site a) ≠
          X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C)
            (X.hp.Rshort shortLevelCount) (X.site a)) shortErr
      (by
        intro a ha
        simpa [shortErr] using hShortAt a ha)
  have hNbrCard : ((X.g.L.stNbr b).card : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast X.facts.nbr_card b
  let bad : X.Centre → Prop := fun C =>
    ¬ X.CountsOK C ∨ (X.CountsOK C ∧ ¬ X.MarksOK H C) ∨ badHeight C
  have hBadPr : (X.centreLaw H).pr bad ≤
      2 * Real.exp (-(n : ℝ)) + 3 * (n : ℝ) * shortErr := by
    have h1 := pr_or_le6 (X.centreLaw H) (fun C => ¬ X.CountsOK C)
      (fun C => (X.CountsOK C ∧ ¬ X.MarksOK H C) ∨ badHeight C)
    have h2 := pr_or_le6 (X.centreLaw H) (fun C => X.CountsOK C ∧ ¬ X.MarksOK H C) badHeight
    calc
      (X.centreLaw H).pr bad ≤
          (X.centreLaw H).pr (fun C => ¬ X.CountsOK C) +
            (X.centreLaw H).pr (fun C => (X.CountsOK C ∧ ¬ X.MarksOK H C) ∨ badHeight C) := h1
      _ ≤ (X.centreLaw H).pr (fun C => ¬ X.CountsOK C) +
          ((X.centreLaw H).pr (fun C => X.CountsOK C ∧ ¬ X.MarksOK H C) +
            (X.centreLaw H).pr badHeight) := by nlinarith [h2]
      _ ≤ Real.exp (-(n : ℝ)) +
          (Real.exp (-(n : ℝ)) + ((X.g.L.stNbr b).card : ℝ) * shortErr) := by
        exact add_le_add (hCounts H) (add_le_add (hMarks H hHistU) hBadHeight)
      _ ≤ 2 * Real.exp (-(n : ℝ)) + 3 * (n : ℝ) * shortErr := by
        have hCardErr := mul_le_mul_of_nonneg_right hNbrCard hShortErrNonneg
        nlinarith [hCardErr]
  have hAlphaOne : α₆ p₀ ≤ 1 :=
    (height_exponents6_admissible p₀ hadm.2.2.1).2.2.1.trans (by norm_num)
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnPos : (0 : ℝ) < n := by positivity
  have hmLeN : X.m ≤ n := by
    change X.g.L.m ≤ n
    rw [X.g.m_eq]
    have hpow : (n : ℝ) ^ α₆ p₀ ≤ n := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnReal hAlphaOne
    exact Nat.ceil_le.mpr hpow
  have hmLeNR : (X.m : ℝ) ≤ n := by exact_mod_cast hmLeN
  have hnPowHalf : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
    have hsqrt : (2 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
      have hroot := Real.sqrt_nonneg (n : ℝ)
      nlinarith
    simpa only [Real.sqrt_eq_rpow] using hsqrt
  have hnPow85 : (2 : ℝ) ≤ (n : ℝ) ^ (85 / 100 : ℝ) := by
    exact hnPowHalf.trans (Real.rpow_le_rpow_of_exponent_le hnReal (by norm_num))
  have hnPow15Half : (n : ℝ) ^ (15 / 100 : ℝ) ≤ n / 2 := by
    have hprod : (n : ℝ) ^ (15 / 100 : ℝ) * (n : ℝ) ^ (85 / 100 : ℝ) = n := by
      rw [← Real.rpow_add hnPos]
      norm_num [Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_left hnPow85
      (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (15 / 100 : ℝ))
    nlinarith
  have hmPow15Half : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ n / 2 := by
    exact (Real.rpow_le_rpow (by positivity) hmLeNR (by norm_num)).trans hnPow15Half
  let rowCap : ℝ := Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))
  have hMpow05 : (X.m : ℝ) ^ (5 / 100 : ℝ) ≤ (X.m : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hMpow09 : (X.m : ℝ) ^ (9 / 100 : ℝ) ≤ (X.m : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hMpow09To15 : (X.m : ℝ) ^ (9 / 100 : ℝ) ≤ (X.m : ℝ) ^ (15 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hMpow15 : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ (X.m : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  have hHighCap : (n : ℝ) ^ ((5 / 100 : ℝ) * (X.J : ℝ)) ≤ rowCap := by
    rw [Real.rpow_def_of_pos hnPos]
    rw [show rowCap = Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) by rfl]
    apply Real.exp_le_exp.mpr
    have hJterm := mul_le_mul_of_nonneg_left hJLog (by norm_num : (0 : ℝ) ≤ 5 / 100)
    calc
      Real.log (n : ℝ) * ((5 / 100 : ℝ) * (X.J : ℝ)) =
          (5 / 100 : ℝ) * ((X.J : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ (5 / 100 : ℝ) * (X.m : ℝ) ^ (9 / 100 : ℝ) := hJterm
      _ ≤ (X.m : ℝ) ^ (15 / 100 : ℝ) := by
        have hnonneg : 0 ≤ (X.m : ℝ) ^ (15 / 100 : ℝ) := Real.rpow_nonneg (by positivity) _
        nlinarith [hMpow09To15]
  have hLongCap (C : X.Centre) : (N : ℝ) * X.oddRow H C u y ≤ rowCap := by
    by_cases hValid : X.OddValid H C X.Rlong b
    · obtain ⟨_, _, hcap, _, _⟩ := hRows H C u hHistU hu hValid
      cases hMode : X.stMode b
      · simpa [Ctx6.oddRow, b, hMode, rowCap] using hcap y
      · have h := hcap y
        rw [hMode] at h
        exact h.trans hHighCap
    · have hrow : X.oddRow H C u y = 0 := by
        simp [Ctx6.oddRow, Ctx6.oddRowAt, b, hValid]
      calc
        (N : ℝ) * X.oddRow H C u y = 0 := by rw [hrow]; ring
        _ ≤ rowCap := by dsimp [rowCap]; positivity
  have hProxyNonneg (C : X.Centre) : 0 ≤ X.proxyRow H C u y := by
    by_cases hValid : X.OddValid H C X.Rshort b
    · cases hMode : X.stMode b
      · simpa [Ctx6.proxyRow, Ctx6.oddRowAt, b, hValid, hMode] using
          (X.lowRow H (X.pos C) b (X.actDesc H C X.Rshort b) (X.tup C)).nonneg y
      · simpa [Ctx6.proxyRow, Ctx6.oddRowAt, b, hValid, hMode] using
          (X.s3Post H b (X.actDesc H C X.Rshort b) (X.tup C)).nonneg y
    · simp [Ctx6.proxyRow, Ctx6.oddRowAt, b, hValid]
  have hHeightAllEq (C : X.Centre) (hEC : X.EligOK H C) (hNo : ¬ badHeight C) :
      ∀ a ∈ X.g.L.stNbr b,
        X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong (X.site a) =
          X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C)
            (X.hp.Rshort shortLevelCount) (X.site a) := by
    intro a ha
    by_contra hne
    exact hNo ⟨a, ha, hEC, hne⟩
  have hChoiceEq (C : X.Centre) (hEC : X.EligOK H C) (hNo : ¬ badHeight C) :
      ∀ a : X.g.L.stNbr b,
        X.choice H C X.Rlong a.1 = X.choice H C X.Rshort a.1 := by
    intro a
    let v : CubeVertex X.hp.d := X.site a.1
    have hEq := hHeightAllEq C hEC hNo a.1 a.2
    have hEq' : X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) X.hp.Rlong v =
        X.hp.height X.sites (X.pos C) (X.act C) (X.elig H C) (X.hp.Rshort X.m) v := by
      simpa [hShortLevel] using hEq
    simp only [Ctx6.choice, Ctx6.Rlong, Ctx6.Rshort]
    change X.hp.selectionAt X.sites (X.pos C) (X.act C) (X.elig H C) (X.ties C) X.hp.Rlong v =
      X.hp.selectionAt X.sites (X.pos C) (X.act C) (X.elig H C) (X.ties C) (X.hp.Rshort X.m) v
    simp [HDParams.selectionAt, hEq']
  have hDescEq (C : X.Centre) (hEC : X.EligOK H C) (hNo : ¬ badHeight C) :
      X.actDesc H C X.Rlong b = X.actDesc H C X.Rshort b := by
    have hFun :
        (fun a : X.g.L.stNbr b =>
          ((X.choice H C X.Rlong a.1).getD X.defaultLoc, X.stType a.1)) =
        (fun a : X.g.L.stNbr b =>
          ((X.choice H C X.Rshort a.1).getD X.defaultLoc, X.stType a.1)) := by
      funext a
      rw [hChoiceEq C hEC hNo a]
    simpa [Ctx6.actDesc] using congrArg (fun f => Finset.univ.image f) hFun
  have hValidityEq (C : X.Centre) (hEC : X.EligOK H C) (hNo : ¬ badHeight C) :
      X.OddValid H C X.Rlong b ↔ X.OddValid H C X.Rshort b := by
    constructor
    · intro hLong
      rcases hLong with ⟨hSome, hCounts', hLevel, hCard, hGate, hTests⟩
      refine ⟨?_, hCounts', ?_, ?_, ?_, ?_⟩
      · intro a ha
        have hq := hChoiceEq C hEC hNo ⟨a, ha⟩
        rw [← hq]
        exact hSome a ha
      · obtain ⟨j, hj⟩ := hLevel
        refine ⟨j, ?_⟩
        intro a ha ℓ hchoice
        have hq := hChoiceEq C hEC hNo ⟨a, ha⟩
        have hchoiceLong : X.choice H C X.Rlong a = some ℓ := by
          rw [hq]
          exact hchoice
        exact hj a ha ℓ hchoiceLong
      · rw [← hDescEq C hEC hNo]
        exact hCard
      · rw [← hDescEq C hEC hNo]
        exact hGate
      · rw [← hDescEq C hEC hNo]
        exact hTests
    · intro hShort
      rcases hShort with ⟨hSome, hCounts', hLevel, hCard, hGate, hTests⟩
      refine ⟨?_, hCounts', ?_, ?_, ?_, ?_⟩
      · intro a ha
        have hq := hChoiceEq C hEC hNo ⟨a, ha⟩
        rw [hq]
        exact hSome a ha
      · obtain ⟨j, hj⟩ := hLevel
        refine ⟨j, ?_⟩
        intro a ha ℓ hchoice
        have hq := hChoiceEq C hEC hNo ⟨a, ha⟩
        have hchoiceShort : X.choice H C X.Rshort a = some ℓ := by
          rw [← hq]
          exact hchoice
        exact hj a ha ℓ hchoiceShort
      · rw [hDescEq C hEC hNo]
        exact hCard
      · rw [hDescEq C hEC hNo]
        exact hGate
      · rw [hDescEq C hEC hNo]
        exact hTests
  have hRowsEq (C : X.Centre) (hEC : X.EligOK H C) (hNo : ¬ badHeight C) :
      X.oddRow H C u y = X.proxyRow H C u y := by
    have hviff := hValidityEq C hEC hNo
    by_cases hLong : X.OddValid H C X.Rlong b
    · have hShort : X.OddValid H C X.Rshort b := hviff.mp hLong
      simp [Ctx6.oddRow, Ctx6.proxyRow, Ctx6.oddRowAt, b, hLong, hShort,
        hDescEq C hEC hNo]
    · have hShort : ¬ X.OddValid H C X.Rshort b := by
        intro h
        exact hLong (hviff.mpr h)
      simp [Ctx6.oddRow, Ctx6.proxyRow, Ctx6.oddRowAt, b, hLong, hShort]
  have hPointwise (C : X.Centre) :
      (N : ℝ) * X.oddRow H C u y ≤
        (N : ℝ) * X.proxyRow H C u y + rowCap * (if bad C then 1 else 0) := by
    by_cases hBad : bad C
    · have hNonneg := mul_nonneg (show (0 : ℝ) ≤ N by positivity) (hProxyNonneg C)
      simp [hBad]
      nlinarith [hLongCap C, hNonneg]
    · have hCountsC : X.CountsOK C := by
        by_contra hC
        exact hBad (Or.inl hC)
      have hMarksC : X.MarksOK H C := by
        by_contra hM
        exact hBad (Or.inr (Or.inl ⟨hCountsC, hM⟩))
      have hEC := hElig H C hCountsC hMarksC
      have hNo : ¬ badHeight C := by
        intro hH
        exact hBad (Or.inr (Or.inr hH))
      have hEq := hRowsEq C hEC hNo
      calc
        (N : ℝ) * X.oddRow H C u y = (N : ℝ) * X.proxyRow H C u y := by rw [hEq]
        _ ≤ (N : ℝ) * X.proxyRow H C u y + rowCap * (if bad C then 1 else 0) := by
          rw [if_neg hBad]
          simp
  have hIndicator : (X.centreLaw H).expect (fun C => if bad C then (1 : ℝ) else 0) =
      (X.centreLaw H).pr bad := by
    unfold FinProb.expect FinProb.pr
    apply Finset.sum_congr rfl
    intro C hC
    by_cases h : bad C <;> simp [h]
  have hExpectBound :
      (X.centreLaw H).expect (fun C => (N : ℝ) * X.oddRow H C u y) ≤
        (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) +
          rowCap * (X.centreLaw H).pr bad := by
    calc
      (X.centreLaw H).expect (fun C => (N : ℝ) * X.oddRow H C u y) ≤
          (X.centreLaw H).expect (fun C =>
            (N : ℝ) * X.proxyRow H C u y + rowCap * (if bad C then 1 else 0)) :=
        FinProb.expect_mono _ hPointwise
      _ = (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) +
            rowCap * (X.centreLaw H).pr bad := by
        rw [FinProb.expect_add]
        exact congrArg (fun r =>
          (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) + r)
          (by rw [FinProb.expect_smul, hIndicator])
  have hExpNegBound (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 / (x + 1) := by
    have hprod : Real.exp (-x) * Real.exp x = 1 := by
      rw [← Real.exp_add]
      simp
    have hlin : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have hmul : (x + 1) * Real.exp (-x) ≤ 1 := by
      calc
        (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
          mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
        _ = 1 := by rw [mul_comm, hprod]
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < x + 1)).2
    nlinarith [hmul]
  have hExpMinus10 := hExpNegBound 10 (by norm_num)
  have hExpMinus150 := hExpNegBound 150 (by norm_num)
  have hNHalf150 : (150 : ℝ) ≤ (n : ℝ) / 2 := by
    have hn300R : (300 : ℝ) ≤ n := by exact_mod_cast hn300
    linarith
  have hFailBudget : rowCap * (2 * Real.exp (-(n : ℝ))) ≤ 1 / 2 := by
    calc
      rowCap * (2 * Real.exp (-(n : ℝ))) =
          2 * (Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) * Real.exp (-(n : ℝ))) := by
            dsimp [rowCap]
            ring
      _ = 2 * Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ) - n) := by
        rw [← Real.exp_add]
        congr 1
      _ ≤ 2 * Real.exp (-((n : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith [hmPow15Half])
      _ ≤ 2 * Real.exp (-150) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith [hNHalf150])
      _ ≤ 2 / 151 := by
        calc
          2 * Real.exp (-150) ≤ 2 * (1 / ((150 : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hExpMinus150 (by norm_num)
          _ = 2 / 151 := by norm_num
      _ ≤ 1 / 2 := by norm_num
  have hShortErrEq : shortErr = Real.exp (-3 * (X.m : ℝ) ^ (1 / 5 : ℝ)) := by
    dsimp [shortErr]
    rw [hShortLevel]
  have hTailExponent : Real.log (n : ℝ) + (X.m : ℝ) ^ (15 / 100 : ℝ) -
      3 * (X.m : ℝ) ^ (1 / 5 : ℝ) ≤ -10 := by
    have hLogM05 : Real.log (n : ℝ) ≤ (X.m : ℝ) ^ (5 / 100 : ℝ) := by
      simpa only [show (1 / 20 : ℝ) = 5 / 100 by norm_num] using hLogMDirect
    have hLogSmall : Real.log (n : ℝ) ≤ (X.m : ℝ) ^ (1 / 5 : ℝ) := hLogM05.trans hMpow05
    nlinarith [hLogSmall, hMpow15, hmPow20]
  have hTailBudget : rowCap * (3 * (n : ℝ) * shortErr) ≤ 1 / 2 := by
    have hProduct : rowCap * ((n : ℝ) * shortErr) =
        Real.exp (Real.log (n : ℝ) + (X.m : ℝ) ^ (15 / 100 : ℝ) -
          3 * (X.m : ℝ) ^ (1 / 5 : ℝ)) := by
      change Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) * ((n : ℝ) * shortErr) = _
      rw [hShortErrEq]
      conv_lhs => arg 2; arg 1; rw [← Real.exp_log hnPos]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1 <;> ring
    calc
      rowCap * (3 * (n : ℝ) * shortErr) = 3 * (rowCap * ((n : ℝ) * shortErr)) := by ring
      _ = 3 * Real.exp (Real.log (n : ℝ) + (X.m : ℝ) ^ (15 / 100 : ℝ) -
          3 * (X.m : ℝ) ^ (1 / 5 : ℝ)) := by rw [hProduct]
      _ ≤ 3 * Real.exp (-10) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hTailExponent) (by norm_num)
      _ ≤ 3 / 11 := by
        calc
          3 * Real.exp (-10) ≤ 3 * (1 / ((10 : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hExpMinus10 (by norm_num)
          _ = 3 / 11 := by norm_num
      _ ≤ 1 / 2 := by norm_num
  have hErrorBudget :
      rowCap * (2 * Real.exp (-(n : ℝ)) + 3 * (n : ℝ) * shortErr) ≤ 1 := by
    calc
      rowCap * (2 * Real.exp (-(n : ℝ)) + 3 * (n : ℝ) * shortErr) =
          rowCap * (2 * Real.exp (-(n : ℝ))) + rowCap * (3 * (n : ℝ) * shortErr) := by ring
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hFailBudget hTailBudget
      _ = 1 := by norm_num
  have hError : rowCap * (X.centreLaw H).pr bad ≤ 1 := by
    calc
      rowCap * (X.centreLaw H).pr bad ≤
          rowCap * (2 * Real.exp (-(n : ℝ)) + 3 * (n : ℝ) * shortErr) :=
        mul_le_mul_of_nonneg_left hBadPr (by positivity)
      _ ≤ 1 := hErrorBudget
  change (X.centreLaw H).expect (fun C => (N : ℝ) * X.oddRow H C u y) ≤
    (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) + 1
  calc
    (X.centreLaw H).expect (fun C => (N : ℝ) * X.oddRow H C u y) ≤
        (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) +
          rowCap * (X.centreLaw H).pr bad := hExpectBound
    _ ≤ (X.centreLaw H).expect (fun C => (N : ℝ) * X.proxyRow H C u y) + 1 :=
      by nlinarith [hError]

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
