import HypercubeRamsey.S06.Step3Defs
import HypercubeRamsey.S06.Steps_q_s06_steps2

/-!
# Steps 1–3: the predictive tests and their consequences

L6.1c (06:165–189), L6.1d (06:191–226), L6.1e(iii) (06:265–295), L6.1f (06:297–366), L6.1g (06:368–447).

Each step is a predicate on a context, and each node proves it for all contexts of large dimension, possibly
from the predicates of earlier steps (stated as hypotheses, so that the section assembly uses every node).

* Raw failure bounds (`Step1CapBound`, `Step1DelBound`, `Step2Bound`, `Step3TestLow`, `Step3TestHigh`): each test
  fails, jointly with its true gate, with raw probability at most its threshold.
* Deterministic consequences on passing tests (`TagDom`, `Step2Dom`, `Step2Supp`, `Step3LowBounds`,
  `Step3HighBounds`), at bases in the raw support (`BaseSupp`) or the local part of it (`KeysSupp`).
* Descriptor sizes and counts (`DescSize`, `DescCount`).
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

/-! ### Support of the raw base experiment -/

/-- The base variables on the key list `S` lie in the raw support: `V₀ ∈ supp Π'|_{S₀}`, the candidates at the
bins of `S` in the partner law of `V₀`, the base tags of `S` in their laws. -/
def KeysSupp (b : X.Base) (S : Finset X.Key) : Prop :=
  0 < X.initLaw.w b.1 ∧ (∀ u ∈ X.binsOf S, 0 < (X.candLaw b.1).w (b.2.1 u)) ∧
    ∀ s ∈ S, 0 < (X.tagLawAt (X.parOf b) s).w (b.2.2 s)

/-- The whole base lies in the raw support. -/
def BaseSupp (b : X.Base) : Prop := X.KeysSupp b Finset.univ

/-- The keys whose base variables enter a type's Step 2 objects. -/
def typeKeys (β : X.Ty) : Finset X.Key := insert β.key (β.obs.biUnion fun ℓ => X.C ℓ.1)

/-! ### Step 1 (06:165–189) -/

/-- The base-tag law is dominated: `T₀ ≤ n^{d₀} Λ` whenever the primary is heavy and related to the other
primary (06:96–104, 06:159–160; restriction mass `≥ c₀ − c₁ = c₁`, `η_y ≤ n^{2D_*}Λ`). -/
def TagDom : Prop :=
  ∀ (pv : Par6 X.Bin N) (h : X.Key), pv.val (primaryName6 h) ∈ X.par.heavy →
    related6 E G M (pv.val (primaryName6 h)) (pv.val (otherPrimaryName6 h)) →
      ∀ i, (X.tagLawAt pv h).w i ≤ (n : ℝ) ^ d₀ * M.Λ i

/-- Step 1 cap failure has raw probability `≤ n^{-δ₁/2}` (06:182–189). -/
def Step1CapBound : Prop :=
  ∀ h ∈ X.step1Keys, X.baseLaw.pr (fun b => ¬ X.Step1Cap b h) ≤ (n : ℝ) ^ (-(δ₁ / 2))

/-- Step 1 deletion failure has raw probability `≤ n^{-δ₁/2}` (06:173–181). -/
def Step1DelBound : Prop :=
  ∀ h ∈ X.step1Keys, ∀ s ∈ X.C h, X.baseLaw.pr (fun b => ¬ X.Step1Del b h s) ≤ (n : ℝ) ^ (-(δ₁ / 2))

end Ctx6

/-- L6.1c (base tags, 06:93–104, 06:159–160). -/
theorem L6_1c_tag (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom := by
  sorry

/-- L6.1c (cap, 06:182–189): uniform references for the bounded candidate list and `Λ` for incoming tags; the
predictive-denominator calculation (L3.7) with `d₀, δ₁ ≪ d₁`. -/
theorem L6_1c_cap (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step1CapBound := by
  sorry

/-- L6.1c (deletion, 06:173–181): the incoming tag has likelihood `≤ n^{d₀} Λ(i)` at every supported parent
value; its predictive density is `< n^{-δ₁}` with probability `≤ n^{-δ₁}`; Bayes off that event. -/
theorem L6_1c_del (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step1DelBound := by
  sorry

namespace Ctx6

/-! ### Step 2 (06:191–226) -/

/-- Step 2 failure has raw probability `≤ n^{-δ₂u_β/2}` at every occurring type (06:201–211: the true-gated
subdensity of `Z_S` relative to `∏ π_{ℓ,−h}` is `m_S`; `(1 + |S|) n^{-δ₂u} ≤ n^{-δ₂u/2}`). -/
def Step2Bound : Prop :=
  ∀ β ∈ X.occTypes, X.rawHist.pr (fun H => X.Step2Fail H β) ≤ (n : ℝ) ^ (-(δ₂ * β.u / 2))

/-- On the Step 2 tests: `T_β ≤ n^{d₂u}Λ` and `T_β ≤ n^{d₂u} T_{β,−ℓ}` (06:212–220; `|S| ≤ 602 u_β`), at any
values of the hidden scalars. -/
def Step2Dom : Prop :=
  ∀ (H : X.Hist) (β : X.Ty), β ∈ X.occTypes → X.KeysSupp H.1 {β.key} → X.Step2Tests H β →
    (∀ i, (X.Tβ H β).w i ≤ (n : ℝ) ^ (d₂ * β.u) * M.Λ i) ∧
      ∀ ℓ ∈ β.obs, ∀ i, (X.Tβ H β).w i ≤ (n : ℝ) ^ (d₂ * β.u) * (X.TβDel H β ℓ).w i

/-- A required name whose primary is the type's own named primary. -/
def MatchName (β : X.Ty) : X.Name → Prop
  | .par p => p = primaryName6 β.key
  | .hid ℓ => primaryName6 ℓ.1 = primaryName6 β.key

/-- On the Step 2 tests every tag in the support of `T_β` sees every matching-primary required variable with
degree `≥ 1 − ε`, and the common-hit set has `μ_i`-mass `≥ c₁/2` (06:220–226). -/
def Step2Supp : Prop :=
  ∀ (H : X.Hist) (β : X.Ty), β ∈ X.occTypes → X.KeysSupp H.1 (X.typeKeys β) → X.Step2Tests H β →
    ∀ i, 0 < (X.Tβ H β).w i →
      c₁ / 2 ≤ ∑ x ∈ X.reqNbhd H (reqNames6 β), (M.μ i).w x ∧
        ∀ nm ∈ reqNames6 β, X.MatchName β nm → 1 - X.ε ≤ colDeg E G (M.μ i) (X.varVal H nm)

end Ctx6

/-- L6.1d (failure, 06:201–211). -/
theorem L6_1d_fail (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Bound := by
  sorry

/-- L6.1d (domination, 06:212–220): the absolute ratio is `≤ n^{d₀ + d₁|S| + δ₂u}`, the deleted ratio
`≤ n^{d₁ + δ₂u}`, both below `n^{d₂u}`. -/
theorem L6_1d_dom (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.TagDom → X.Step2Dom := by
  sorry

/-- L6.1d (support, 06:220–226): positive likelihood for `Z_{(h',t')}` forces the base tag at `h ∈ C(h')` to see
that value (`≥ 1 − ε` for the same named primary, `≥ c₁` in the crossing case); at most one required column
has degree only `c₁`; `c₁ − O(mε) ≥ c₁/2`. -/
theorem L6_1d_supp (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp := by
  sorry

namespace Ctx6

/-! ### Descriptor sizes and counts (06:265–295) -/

/-- A descriptor at an odd state observes `O(T + J)` tuples (06:270–273). -/
def DescSize : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id),
    b ∈ X.g.L.oddStates → ∀ D ∈ X.descsIn b perm, (D.card : ℝ) ≤ 10 ^ 4 * (X.T + X.J + 1)

/-- With at most `P` permitted IDs per neighbouring state, the number of descriptors is
`exp(O(T log(nP) + (J+1) log T))` (06:274–281). -/
def DescCount : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id) (P : ℕ),
    b ∈ X.g.L.oddStates → (∀ a, (perm a).card ≤ P) →
      ((X.descsIn b perm).card : ℝ) ≤
        Real.exp (10 ^ 4 * (X.T * Real.log (3 * n * P + 2) + (X.J + 1) * Real.log (X.T + 2)))

end Ctx6

set_option maxHeartbeats 400000 in
/-- L6.1e (sizes, 06:270–273): constantly many generic types, each with at most `T` IDs; `O(J+1)` exceptional
states, one ID each. -/
theorem L6_1e_size (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescSize := by
  refine ⟨4, 0, ?_⟩
  intro n N E G M X hLarge
  have hn : 4 ≤ n := hLarge.1
  intro Id _ _ b perm hb D hD
  have hD' : D ∈ ((Finset.univ : Finset (X.g.L.stNbr b → Id)).filter
      (fun φ => (∀ a, φ a ∈ perm a) ∧ (Finset.univ.image φ).card ≤ X.T)).image
      (X.descOf b) := by
    simpa only [Ctx6.descsIn] using hD
  rcases Finset.mem_image.mp hD' with ⟨φ, hφ, rfl⟩
  have hφ' := (Finset.mem_filter.mp hφ).2
  rcases hφ' with ⟨hperm, hfan⟩
  let S : Finset Id := Finset.univ.image φ
  have hScard : S.card ≤ X.T := by simpa [S] using hfan
  have hids : ∀ a, φ a ∈ S := fun a => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  let Tys : Finset X.Ty := Lane_q_s06_steps2.neighborTypeForms6 X b
  have hTys : Tys.card ≤ 3 * 602 := Lane_q_s06_steps2.neighborTypeForms6_card X b
  let Trans : Finset (X.g.L.stNbr b) := Finset.univ.filter
    (fun a => X.stMode a.1 ≠ X.stMode b)
  let Var : Finset (X.g.L.stNbr b) := Finset.univ.filter
    (fun a => (X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
      (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
        X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b))
  let Bad : Finset (X.g.L.stNbr b) := Trans ∪ Var
  have hBadCard : Bad.card ≤ 1 + 21 * (X.J + 2) := by
    simpa [Bad, Trans, Var] using Lane_q_s06_steps2.descriptorBadStates6_card X b hb hn
  have hclass : ∀ a, X.stType a.1 ∈ Tys ∨ a ∈ Bad := by
    intro a
    by_cases hbad : a ∈ Bad
    · exact Or.inr hbad
    · have htrans : ¬ X.stMode a.1 ≠ X.stMode b := by
        intro hmode
        exact hbad (Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmode⟩)
      have hmode : X.stMode a.1 = X.stMode b := not_ne_iff.mp htrans
      have hvar : ¬ ((X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
          (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
            X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b)) := by
        intro hv
        exact hbad (Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
      by_cases hlow : X.stMode b = .low
      · by_cases hsign : X.g.L.stSign a.1 = X.g.L.stSign b
        · by_cases hflip : X.g.L.stFlippable a.1 = X.g.L.stFlippable b
          · exact Or.inl <| Lane_q_s06_steps2.neighbor_type_mem_forms6 X a.2 hsign hflip
          · have hcontr := hvar ⟨Or.inl hlow, Or.inr hflip⟩
            exact False.elim hcontr
        · have hcontr := hvar ⟨Or.inl hlow, Or.inl hsign⟩
          exact False.elim hcontr
      · have hhigh : X.stMode b = .high := by
          cases hm : X.stMode b with
          | low => exact False.elim (hlow hm)
          | high => rfl
        have hmodeHigh : X.stMode a.1 = .high := hmode.trans hhigh
        by_cases hboundary : X.g.L.stSeverity a.1 = X.J + 1
        · by_cases hsign : X.g.L.stSign a.1 = X.g.L.stSign b
          · by_cases hflip : X.g.L.stFlippable a.1 = X.g.L.stFlippable b
            · exact Or.inl <| Lane_q_s06_steps2.neighbor_type_mem_forms6 X a.2 hsign hflip
            · have hcontr := hvar ⟨Or.inr hboundary, Or.inr hflip⟩
              exact False.elim hcontr
          · have hcontr := hvar ⟨Or.inr hboundary, Or.inl hsign⟩
            exact False.elim hcontr
        · exact Or.inl <| Lane_q_s06_steps2.neighbor_type_mem_forms_high6 X a.2 hmodeHigh hboundary
  have hdescNat : (X.descOf b φ).card ≤ 1806 * X.T + 1 + 21 * (X.J + 2) := by
    have hsplit := Lane_q_s06_steps2.descOf_card_le_split X b φ S Tys Bad hids hclass
    have hprod : S.card * Tys.card ≤ X.T * 1806 := by
      exact Nat.mul_le_mul hScard (by simpa using hTys)
    calc
      (X.descOf b φ).card ≤ S.card * Tys.card + Bad.card := hsplit
      _ ≤ X.T * 1806 + (1 + 21 * (X.J + 2)) := Nat.add_le_add hprod hBadCard
      _ = 1806 * X.T + 1 + 21 * (X.J + 2) := by omega
  have hfinal : 1806 * X.T + 1 + 21 * (X.J + 2) ≤ 10 ^ 4 * (X.T + X.J + 1) := by omega
  exact_mod_cast hdescNat.trans hfinal

set_option maxHeartbeats 1000000 in
/-- L6.1e (counts, 06:274–281): list the at most `T` IDs, a subset for each generic type, one listed ID for each
exceptional state. -/
theorem L6_1e_count (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount := by
  refine ⟨4, 0, ?_⟩
  intro n N E G M X hLarge
  have hn : 4 ≤ n := hLarge.1
  intro Id _ _ b perm P hb hperm
  let AllIds : Finset Id := (X.g.L.stNbr b).attach.biUnion perm
  have hAllIds : AllIds.card ≤ 3 * n * P := by
    calc
      AllIds.card ≤ ∑ a ∈ (X.g.L.stNbr b).attach, (perm a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ (X.g.L.stNbr b).attach, P := by
        apply Finset.sum_le_sum
        intro a ha
        exact hperm a
      _ = (X.g.L.stNbr b).card * P := by simp
      _ ≤ (3 * n) * P := Nat.mul_le_mul_right P (X.facts.nbr_card b)
  let SmallIds : Finset (Finset Id) := AllIds.powerset.filter fun S => S.card ≤ X.T
  have hSmallSub : SmallIds ⊆
      (Finset.range (X.T + 1)).biUnion fun k => AllIds.powersetCard k := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hSub, hCard⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨S.card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hSub, rfl⟩
  have hSmallCard : SmallIds.card ≤ (AllIds.card + 2) ^ (2 * X.T) := by
    calc
      SmallIds.card ≤ ((Finset.range (X.T + 1)).biUnion fun k => AllIds.powersetCard k).card :=
        Finset.card_le_card hSmallSub
      _ ≤ (AllIds.card + 2) ^ (2 * X.T) :=
        Lane_q_s06_steps2.smallPowersetCount6 AllIds X.T
  let Tys : Finset X.Ty := Lane_q_s06_steps2.neighborTypeForms6 X b
  have hTys : Tys.card ≤ 3 * 602 := Lane_q_s06_steps2.neighborTypeForms6_card X b
  let Trans : Finset (X.g.L.stNbr b) := Finset.univ.filter
    (fun a => X.stMode a.1 ≠ X.stMode b)
  let Var : Finset (X.g.L.stNbr b) := Finset.univ.filter
    (fun a => (X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
      (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
        X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b))
  let Bad : Finset (X.g.L.stNbr b) := Trans ∪ Var
  have hBadCard : Bad.card ≤ 1 + 21 * (X.J + 2) := by
    simpa [Bad, Trans, Var] using Lane_q_s06_steps2.descriptorBadStates6_card X b hb hn
  have hclass : ∀ a, X.stType a.1 ∈ Tys ∨ a ∈ Bad := by
    intro a
    by_cases hbad : a ∈ Bad
    · exact Or.inr hbad
    · have htrans : ¬ X.stMode a.1 ≠ X.stMode b := by
        intro hmode
        exact hbad (Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmode⟩)
      have hmode : X.stMode a.1 = X.stMode b := not_ne_iff.mp htrans
      have hvar : ¬ ((X.stMode b = .low ∨ X.g.L.stSeverity a.1 = X.J + 1) ∧
          (X.g.L.stSign a.1 ≠ X.g.L.stSign b ∨
            X.g.L.stFlippable a.1 ≠ X.g.L.stFlippable b)) := by
        intro hv
        exact hbad (Finset.mem_union.mpr <| Or.inr <|
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
      by_cases hlow : X.stMode b = .low
      · by_cases hsign : X.g.L.stSign a.1 = X.g.L.stSign b
        · by_cases hflip : X.g.L.stFlippable a.1 = X.g.L.stFlippable b
          · exact Or.inl <| Lane_q_s06_steps2.neighbor_type_mem_forms6 X a.2 hsign hflip
          · have hcontr := hvar ⟨Or.inl hlow, Or.inr hflip⟩
            exact False.elim hcontr
        · have hcontr := hvar ⟨Or.inl hlow, Or.inl hsign⟩
          exact False.elim hcontr
      · have hhigh : X.stMode b = .high := by
          cases hm : X.stMode b with
          | low => exact False.elim (hlow hm)
          | high => rfl
        have hmodeHigh : X.stMode a.1 = .high := hmode.trans hhigh
        by_cases hboundary : X.g.L.stSeverity a.1 = X.J + 1
        · by_cases hsign : X.g.L.stSign a.1 = X.g.L.stSign b
          · by_cases hflip : X.g.L.stFlippable a.1 = X.g.L.stFlippable b
            · exact Or.inl <| Lane_q_s06_steps2.neighbor_type_mem_forms6 X a.2 hsign hflip
            · have hcontr := hvar ⟨Or.inr hboundary, Or.inr hflip⟩
              exact False.elim hcontr
          · have hcontr := hvar ⟨Or.inr hboundary, Or.inl hsign⟩
            exact False.elim hcontr
        · exact Or.inl <| Lane_q_s06_steps2.neighbor_type_mem_forms_high6 X a.2 hmodeHigh hboundary
  let GoodType : Type := {β : X.Ty // β ∈ Tys}
  let BadType : Type := {a : X.g.L.stNbr b // a ∈ Bad}
  let SmallType : Type := {s : Finset Id // s ∈ SmallIds}
  let Enc : Type := Σ s : SmallType, Finset (s.1 × GoodType) × (BadType → s.1)
  let decode : Enc → Finset (Id × X.Ty) := fun code =>
    Lane_q_s06_steps2.decodeDescCode6
      (fun a : X.g.L.stNbr b => X.stType a.1) code.2
  have hSmallEach : ∀ s, s ∈ SmallIds → s.card ≤ X.T := by
    intro s hs
    exact (Finset.mem_filter.mp hs).2
  have hGoodCard : Fintype.card GoodType ≤ 1806 := by
    have hTys1806 : Tys.card ≤ 1806 := by omega
    simpa [GoodType] using hTys1806
  let E : ℕ := 1 + 21 * (X.J + 2)
  have hBadTypeCard : Fintype.card BadType ≤ E := by
    simpa [BadType, E] using hBadCard
  have hEncCard : Fintype.card Enc ≤
      SmallIds.card * (2 ^ (X.T * 1806)) * ((X.T + 1) ^ E) :=
    Lane_q_s06_steps2.sigmaPatternCard6 SmallIds X.T E hSmallEach hGoodCard hBadTypeCard
  have hcover : X.descsIn b perm ⊆ Finset.univ.image decode := by
    intro D hD
    have hD' : D ∈ ((Finset.univ : Finset (X.g.L.stNbr b → Id)).filter
        (fun φ => (∀ a, φ a ∈ perm a) ∧ (Finset.univ.image φ).card ≤ X.T)).image
        (X.descOf b) := by
      simpa only [Ctx6.descsIn] using hD
    rcases Finset.mem_image.mp hD' with ⟨φ, hφ, rfl⟩
    have hφ' := (Finset.mem_filter.mp hφ).2
    rcases hφ' with ⟨hφPerm, hfan⟩
    let S : Finset Id := Finset.univ.image φ
    have hScard : S.card ≤ X.T := by simpa [S] using hfan
    have hids : ∀ a, φ a ∈ S := fun a =>
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have hSsub : S ⊆ AllIds := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨a, ha, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_attach _ _, hφPerm a⟩
    have hSmem : S ∈ SmallIds :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSsub, hScard⟩
    let s : SmallType := ⟨S, hSmem⟩
    have hDimage : X.descOf b φ =
        Finset.univ.image (fun a : X.g.L.stNbr b => (φ a, X.stType a.1)) := rfl
    obtain ⟨c, hcode⟩ := Lane_q_s06_steps2.exists_descCode6 S Tys Bad φ
      (fun a : X.g.L.stNbr b => X.stType a.1) (X.descOf b φ) hDimage hids hclass
    let code : Enc := ⟨s, c⟩
    have hdecode : decode code = X.descOf b φ := by
      simpa [decode, code, GoodType, BadType] using hcode
    exact Finset.mem_image.mpr ⟨code, Finset.mem_univ _, hdecode⟩
  have hdescEnc : (X.descsIn b perm).card ≤ Fintype.card Enc := by
    calc
      (X.descsIn b perm).card ≤ (Finset.univ.image decode).card := Finset.card_le_card hcover
      _ ≤ Fintype.card Enc := by
        calc
          (Finset.univ.image decode).card ≤ Finset.univ.card := Finset.card_image_le
          _ = Fintype.card Enc := by simp
  let E : ℕ := 1 + 21 * (X.J + 2)
  let B0 : ℕ := 3 * n * P + 2
  have hE : E ≤ 43 * (X.J + 1) := by dsimp [E]; omega
  have hBase : AllIds.card + 2 ≤ B0 := by dsimp [B0]; omega
  have hBaseTwo : 2 ≤ B0 := by dsimp [B0]; omega
  have hSmallPow : SmallIds.card ≤ B0 ^ (2 * X.T) :=
    hSmallCard.trans (Nat.pow_le_pow_left hBase _)
  have hGenericPow : 2 ^ (X.T * 1806) ≤ B0 ^ (X.T * 1806) :=
    Nat.pow_le_pow_left hBaseTwo _
  have hSmallGeneric : SmallIds.card * 2 ^ (X.T * 1806) ≤ B0 ^ (1808 * X.T) := by
    calc
      SmallIds.card * 2 ^ (X.T * 1806) ≤ B0 ^ (2 * X.T) * 2 ^ (X.T * 1806) :=
        Nat.mul_le_mul_right _ hSmallPow
      _ ≤ B0 ^ (2 * X.T) * B0 ^ (X.T * 1806) :=
        Nat.mul_le_mul_left _ hGenericPow
      _ = B0 ^ (1808 * X.T) := by rw [← Nat.pow_add]; congr 1 <;> omega
  have hExceptionPow : (X.T + 1) ^ E ≤ (X.T + 2) ^ (43 * (X.J + 1)) := by
    calc
      (X.T + 1) ^ E ≤ (X.T + 2) ^ E := Nat.pow_le_pow_left (by omega) _
      _ ≤ (X.T + 2) ^ (43 * (X.J + 1)) := Nat.pow_le_pow_right (by omega) hE
  have hCodeNat : SmallIds.card * (2 ^ (X.T * 1806)) * ((X.T + 1) ^ E) ≤
      B0 ^ (1808 * X.T) * (X.T + 2) ^ (43 * (X.J + 1)) := by
    exact Nat.mul_le_mul hSmallGeneric hExceptionPow
  have hDescNat : (X.descsIn b perm).card ≤
      B0 ^ (1808 * X.T) * (X.T + 2) ^ (43 * (X.J + 1)) :=
    hdescEnc.trans (hEncCard.trans hCodeNat)
  have hDescRealNat : ((X.descsIn b perm).card : ℝ) ≤
      (B0 : ℝ) ^ (1808 * X.T) * (X.T + 2 : ℝ) ^ (43 * (X.J + 1)) := by
    exact_mod_cast hDescNat
  have hPowB : (B0 : ℝ) ^ (1808 * X.T) =
      Real.exp (((1808 * X.T : ℕ) : ℝ) * Real.log (B0 : ℝ)) := by
    exact Lane_q_s06_steps2.natPow_eq_exp_log6 B0 (1808 * X.T) (by dsimp [B0]; omega)
  have hPowT : (X.T + 2 : ℝ) ^ (43 * (X.J + 1)) =
      Real.exp (((43 * (X.J + 1) : ℕ) : ℝ) * Real.log (X.T + 2 : ℝ)) := by
    simpa [Nat.cast_add] using
      Lane_q_s06_steps2.natPow_eq_exp_log6 (X.T + 2) (43 * (X.J + 1)) (by omega)
  have hLogB : 0 ≤ Real.log (B0 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B0 by dsimp [B0]; omega))
  have hLogT : 0 ≤ Real.log (X.T + 2 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X.T + 2 by omega))
  have hCoeff :
      (((1808 * X.T : ℕ) : ℝ) * Real.log (B0 : ℝ) +
        ((43 * (X.J + 1) : ℕ) : ℝ) * Real.log (X.T + 2 : ℝ)) ≤
      (10000 : ℝ) * ((X.T : ℝ) * Real.log (B0 : ℝ) +
        (X.J + 1 : ℝ) * Real.log (X.T + 2 : ℝ)) := by
    have hTnonneg : 0 ≤ (X.T : ℝ) := Nat.cast_nonneg _
    have hJnonneg : 0 ≤ (X.J + 1 : ℝ) := by
      exact_mod_cast (Nat.zero_le (X.J + 1))
    have hTcoef : (1808 : ℝ) * (X.T : ℝ) ≤ 10000 * (X.T : ℝ) :=
      mul_le_mul_of_nonneg_right (by norm_num) hTnonneg
    have hJcoef : ((43 * (X.J + 1) : ℕ) : ℝ) ≤
        (10000 : ℝ) * (X.J + 1 : ℝ) := by
      exact_mod_cast (Nat.mul_le_mul_right (X.J + 1) (by norm_num : 43 ≤ 10000))
    have hTterm : ((1808 * X.T : ℕ) : ℝ) * Real.log (B0 : ℝ) ≤
        (10000 : ℝ) * ((X.T : ℝ) * Real.log (B0 : ℝ)) := by
      rw [Nat.cast_mul]
      calc
        (1808 : ℝ) * (X.T : ℝ) * Real.log (B0 : ℝ) ≤
            10000 * (X.T : ℝ) * Real.log (B0 : ℝ) :=
          mul_le_mul_of_nonneg_right hTcoef hLogB
        _ = (10000 : ℝ) * ((X.T : ℝ) * Real.log (B0 : ℝ)) := by ring
    have hJterm : ((43 * (X.J + 1) : ℕ) : ℝ) * Real.log (X.T + 2 : ℝ) ≤
        (10000 : ℝ) * ((X.J + 1 : ℝ) * Real.log (X.T + 2 : ℝ)) := by
      calc
        ((43 * (X.J + 1) : ℕ) : ℝ) * Real.log (X.T + 2 : ℝ) ≤
            ((10000 : ℝ) * (X.J + 1 : ℝ)) * Real.log (X.T + 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hJcoef hLogT
        _ = (10000 : ℝ) * ((X.J + 1 : ℝ) * Real.log (X.T + 2 : ℝ)) := by ring
    calc
      (((1808 * X.T : ℕ) : ℝ) * Real.log (B0 : ℝ) +
          ((43 * (X.J + 1) : ℕ) : ℝ) * Real.log (X.T + 2 : ℝ)) ≤
        (10000 : ℝ) * ((X.T : ℝ) * Real.log (B0 : ℝ)) +
          (10000 : ℝ) * ((X.J + 1 : ℝ) * Real.log (X.T + 2 : ℝ)) :=
        add_le_add hTterm hJterm
      _ = (10000 : ℝ) * ((X.T : ℝ) * Real.log (B0 : ℝ) +
          (X.J + 1 : ℝ) * Real.log (X.T + 2 : ℝ)) := by ring
  calc
    ((X.descsIn b perm).card : ℝ) ≤
        (B0 : ℝ) ^ (1808 * X.T) * (X.T + 2 : ℝ) ^ (43 * (X.J + 1)) := hDescRealNat
    _ = Real.exp (((1808 * X.T : ℕ) : ℝ) * Real.log (B0 : ℝ) +
          ((43 * (X.J + 1) : ℕ) : ℝ) * Real.log (X.T + 2 : ℝ)) := by
      rw [hPowB, hPowT, ← Real.exp_add]
    _ ≤ Real.exp (10 ^ 4 *
          ((X.T : ℝ) * Real.log (3 * n * P + 2) +
            (X.J + 1 : ℝ) * Real.log (X.T + 2))) := by
      apply Real.exp_le_exp.mpr
      rw [show (10 : ℝ) ^ 4 = 10000 by norm_num]
      simpa [B0, Nat.cast_mul, Nat.cast_add] using hCoeff

namespace Ctx6

/-! ### Step 3 (06:297–447) -/

/-- Raw Step 3 failure bounds at low targets: for every descriptor of occurring types, each data test fails
jointly with the true-target gate with raw probability `≤ e^{−.02k}` (06:346–353). -/
def Step3TestLow : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State), b ∈ X.g.L.oddStates → X.stMode b = .low →
    ∀ D : Finset (Id × X.Ty), (∀ e ∈ D, e.2 ∈ X.occTypes) →
      (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ≤ X.s3Thr ∧
      ∀ c ∈ D, (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧
        X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) ≤ X.s3Thr

/-- Raw Step 3 failure bounds at high targets; the probability integrates `H_loc` too (06:418–426). -/
def Step3TestHigh : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State), b ∈ X.g.L.oddStates → X.stMode b = .high →
    ∀ D : Finset (Id × X.Ty), (∀ e ∈ D, e.2 ∈ X.occTypes) →
      (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none < X.s3Thr) ≤ X.s3Thr ∧
      ∀ c ∈ D, (X.rawHistData Id).pr (fun ω => X.S3TrueGate ω.1 b D ∧
        X.s3Mass ω.1 b D ω.2 none < X.s3Thr * X.s3Mass ω.1 b D ω.2 (some c)) ≤ X.s3Thr

/-- Low Step 3 consequences on the data tests: `L_b ≤ e^{.16k} Q_{−c}` for matching tuples, `N max L_b ≤
e^{m^{.15}/2}`, and every supported candidate hits every observed entry (06:355–366). -/
def Step3LowBounds : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id),
    b ∈ X.g.L.oddStates → X.stMode b = .low → ∀ D ∈ X.descsIn b perm, ∀ (H : X.Hist) (o : X.Data Id),
      X.BaseSupp H.1 → X.S3Tests H b D o →
        (∀ c ∈ D, X.Matching b c.2 → ∀ ξ,
          (X.s3Post H b D o).w ξ ≤ Real.exp ((16 / 100) * X.k) * (X.s3Del H b D o c).w ξ) ∧
        (∀ ξ, (N : ℝ) * (X.s3Post H b D o).w ξ ≤ Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ) / 2)) ∧
        (∀ ξ, 0 < (X.s3Post H b D o).w ξ → ∀ e ∈ D, ∀ r, Hits E G ((o e).2 r) ξ)

/-- High Step 3 consequences: `L_b ≤ e^{.16k} Q_{−c}` for matching tuples, `N max L_b ≤ n^{.05J}`, support
(06:428–447). -/
def Step3HighBounds : Prop :=
  ∀ (Id : Type) [Fintype Id] [DecidableEq Id] (b : X.State) (perm : X.g.L.stNbr b → Finset Id),
    b ∈ X.g.L.oddStates → X.stMode b = .high → ∀ D ∈ X.descsIn b perm, ∀ (H : X.Hist) (o : X.Data Id),
      X.BaseSupp H.1 → X.S3Tests H b D o →
        (∀ c ∈ D, X.Matching b c.2 → ∀ ξ,
          (X.s3Post H b D o).w ξ ≤ Real.exp ((16 / 100) * X.k) * (X.s3Del H b D o c).w ξ) ∧
        (∀ ξ, (N : ℝ) * (X.s3Post H b D o).w ξ ≤ (n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) ∧
        (∀ ξ, 0 < (X.s3Post H b D o).w ξ → ∀ e ∈ D, ∀ r, Hits E G ((o e).2 r) ξ)

end Ctx6

set_option maxHeartbeats 400000 in
private theorem lowConditionalMassTest6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (H : X.Hist) (b : X.State) (hmode : X.stMode b = .low)
    (hStep2Supp : X.Step2Supp) (hBaseSupp : X.BaseSupp H.1)
    (D : Finset (Id × X.Ty)) (hTypes : ∀ e ∈ D, e.2 ∈ X.occTypes) :
    (∑ ξ, (X.hidPost H.1 (X.tgt b).1).w ξ *
      (X.dataLaw Id (X.withHid H (X.tgt b) ξ)).pr
        (fun o => X.LowGate H b D ξ ∧ X.s3Mass H b D o none < X.s3Thr) ≤ X.s3Thr) ∧
      ∀ c ∈ D, ∑ ξ, (X.hidPost H.1 (X.tgt b).1).w ξ *
        (X.dataLaw Id (X.withHid H (X.tgt b) ξ)).pr
          (fun o => X.LowGate H b D ξ ∧
            X.s3Mass H b D o none < X.s3Thr * X.s3Mass H b D o (some c)) ≤ X.s3Thr := by
  classical
  let t := X.tgt b
  let Idx := {e : Id × X.Ty // e ∈ D}
  let Ω := ∀ e : Idx, X.Tuple
  let eD := Equiv.piEquivPiSubtypeProd (fun e : Id × X.Ty => e ∈ D)
    (fun _ => X.Tuple)
  let o₀ : X.Data Id := fun _ => (X.i₀, fun _ => X.y₀)
  let complete : Ω → X.Data Id := fun a => eD.symm (a, fun e => o₀ e.1)
  let π : Law N := X.hidPost H.1 t.1
  let Qcoord : Idx → FinProb X.Tuple := fun e => X.lowRef H b e.1.2
  let Q : FinProb Ω := FinProb.pi Qcoord
  let P : Fin N → FinProb Ω := fun ξ =>
    FinProb.pi fun e : Idx => X.tupleLaw (X.withHid H t ξ) e.1.2
  let gate : Fin N → Prop := fun ξ => X.LowGate H b D ξ
  let lik : Fin N → Ω → ℝ := fun ξ a =>
    ∏ e ∈ D, X.lowLik H b ξ e.2 (complete a e)
  let likDel : Fin N → (Id × X.Ty) → Ω → ℝ := fun ξ c a =>
    ∏ e ∈ D, if (some c : Option (Id × X.Ty)) = some e then 1 else
      X.lowLik H b ξ e.2 (complete a e)
  let mass : Ω → ℝ := fun a => X.s3Mass H b D (complete a) none
  let massDel : (Id × X.Ty) → Ω → ℝ := fun c a =>
    X.s3Mass H b D (complete a) (some c)
  have hComplete (a : Ω) (e : Id × X.Ty) (he : e ∈ D) :
      complete a e = a ⟨e, he⟩ := by
    simp [complete, eD, Equiv.piEquivPiSubtypeProd_symm_apply, he]
  have hproduct (ξ : Fin N) (a : Ω) :
      (∏ e ∈ D, if (none : Option (Id × X.Ty)) = some e then 1 else
        X.lowLik H b ξ e.2 (complete a e)) = lik ξ a := by
    simp [lik]
  have hprod (ξ : Fin N) (a : Ω) :
      lik ξ a = ∏ e : Idx, X.lowLik H b ξ e.1.2 (a e) := by
    let f : Id × X.Ty → ℝ := fun e => X.lowLik H b ξ e.2 (complete a e)
    have hattach : (∏ e : Idx, f e.1) = ∏ e ∈ D, f e := by
      rw [Finset.univ_eq_attach]
      simpa [f] using Finset.prod_attach D f
    calc
      lik ξ a = ∏ e ∈ D, f e := rfl
      _ = ∏ e : Idx, f e.1 := hattach.symm
      _ = ∏ e : Idx, X.lowLik H b ξ e.1.2 (a e) := by
        apply Finset.prod_congr rfl
        intro e he
        dsimp [f]
        rw [hComplete a e.1 e.2]
  have hKeySupp : ∀ β : X.Ty, X.KeysSupp H.1 (X.typeKeys β) := by
    change X.KeysSupp H.1 Finset.univ at hBaseSupp
    intro β
    rcases hBaseSupp with ⟨hinit, hbins, htags⟩
    refine ⟨hinit, ?_, ?_⟩
    · intro u hu
      apply hbins u
      rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
    · intro s hs
      exact htags s (Finset.mem_univ s)
  have hmix : ∀ a : Ω,
      mass a = ∑ ξ, if gate ξ then π.w ξ * lik ξ a else 0 := by
    intro a
    unfold mass Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ hξ
    have hterm : X.s3Weight H b D (complete a) none ξ =
        if gate ξ then π.w ξ * lik ξ a else 0 := by
      by_cases hg : gate ξ
      · simp only [Ctx6.s3Weight, hmode, Ctx6.lowWeight, gate, if_pos hg]
        rw [hproduct ξ a]
        simp only [mul_one]
        change (X.hidPost H.1 t.1).w ξ * lik ξ a = π.w ξ * lik ξ a
        rfl
      · simp only [Ctx6.s3Weight, hmode, Ctx6.lowWeight, gate, if_neg hg]
        simp
    exact hterm
  have hmixDel (c : Id × X.Ty) (a : Ω) :
      massDel c a = ∑ ξ, if gate ξ then π.w ξ * likDel ξ c a else 0 := by
    unfold massDel Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ hξ
    by_cases hg : gate ξ
    · simp only [Ctx6.s3Weight, hmode, Ctx6.lowWeight, gate, if_pos hg]
      simp only [mul_one]
      change π.w ξ *
          (∏ e ∈ D, if (some c : Option (Id × X.Ty)) = some e then 1 else
            X.lowLik H b ξ e.2 (complete a e)) = π.w ξ * likDel ξ c a
      rfl
    · simp only [Ctx6.s3Weight, hmode, Ctx6.lowWeight, gate, if_neg hg]
      simp
  have hmassDelNonneg (c : Id × X.Ty) (a : Ω) : 0 ≤ massDel c a := by
    unfold massDel Ctx6.s3Mass
    apply Finset.sum_nonneg
    intro ξ hξ
    simp only [Ctx6.s3Weight, hmode, Ctx6.lowWeight]
    apply mul_nonneg
    · apply mul_nonneg ((X.hidPost H.1 (X.tgt b).1).nonneg ξ)
      split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro e he
      split_ifs
      · norm_num
      · exact Lane_q_s06_steps2.lowLik_nonneg6 X H b ξ e.2 (complete a e)
  have hdom : ∀ ξ (a : Ω), gate ξ → (P ξ).w a ≤ Q.w a * lik ξ a := by
    intro ξ a hg
    have hgate := hg
    unfold gate Ctx6.LowGate at hgate
    rcases hgate with ⟨hprior, hcap, htests⟩
    have hprodle :
        (∏ e : Idx, (X.tupleLaw (X.withHid H t ξ) e.1.2).w (a e)) ≤
          ∏ e : Idx, (X.lowRef H b e.1.2).w (a e) *
            X.lowLik H b ξ e.1.2 (a e) := by
      apply Finset.prod_le_prod₀
      · intro e he
        exact (X.tupleLaw (X.withHid H t ξ) e.1.2).nonneg (a e)
      · intro e he
        have hstep : X.Step2Tests (X.withHid H t ξ) e.1.2 := htests e.1 e.2
        have hlabel (i : X.ι) (hi : 0 <
            (X.Tβ (X.withHid H t ξ) e.1.2).w i) :
            0 < ∑ x ∈ X.reqNbhd (X.withHid H t ξ) (reqNames6 e.1.2), (M.μ i).w x := by
          have hs := hStep2Supp (X.withHid H t ξ) e.1.2
            (hTypes e.1 e.2) (hKeySupp e.1.2) hstep i hi
          exact lt_of_lt_of_le (by norm_num [c₁, c₀]) hs.1
        exact Lane_q_s06_steps2.lowTupleLaw_subdensity6 X H b e.1.2 ξ hstep hlabel (a e)
    have hPweight : (P ξ).w a =
      ∏ e : Idx, (X.tupleLaw (X.withHid H t ξ) e.1.2).w (a e) := rfl
    have hQweight : Q.w a =
        ∏ e : Idx, (X.lowRef H b e.1.2).w (a e) := rfl
    calc
      (P ξ).w a = ∏ e : Idx, (X.tupleLaw (X.withHid H t ξ) e.1.2).w (a e) := hPweight
      _ ≤ ∏ e : Idx, (X.lowRef H b e.1.2).w (a e) *
            X.lowLik H b ξ e.1.2 (a e) := hprodle
      _ = Q.w a * lik ξ a := by
        rw [Finset.prod_mul_distrib, ← hQweight, ← hprod ξ a]
  have hsmall :
      (∑ a : Ω, if mass a < X.s3Thr then Q.w a * mass a else 0) ≤ X.s3Thr :=
    Lane_q_s06_steps2.subdensity_small_mass6 Q mass X.s3Thr
      (le_of_lt (by unfold Ctx6.s3Thr; exact Real.exp_pos _))
  have hmixBound := Lane_q_s06_steps2.mixture_subdensity_bound6 π Q P gate lik mass
    (fun _ => X.s3Thr) X.s3Thr hmix hdom hsmall
  have hmassDep (H' : X.Hist) (drop : Option (Id × X.Ty)) (o o' : X.Data Id)
      (hag : ∀ e ∈ D, o e = o' e) :
      X.s3Mass H' b D o drop = X.s3Mass H' b D o' drop := by
    unfold Ctx6.s3Mass
    apply Finset.sum_congr rfl
    intro ξ hξ
    simp only [Ctx6.s3Weight, hmode, Ctx6.lowWeight]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    rw [hag e he]
  have hprob (ξ : Fin N) :
      (X.dataLaw Id (X.withHid H t ξ)).pr
        (fun o => gate ξ ∧ X.s3Mass H b D o none < X.s3Thr) =
      (P ξ).pr (fun a => gate ξ ∧ mass a < X.s3Thr) := by
    have hAdep : ∀ o o', (∀ e ∈ D, o e = o' e) →
        ((gate ξ ∧ X.s3Mass H b D o none < X.s3Thr) ↔
          (gate ξ ∧ X.s3Mass H b D o' none < X.s3Thr)) := by
      intro o o' hag
      rw [hmassDep H none o o' hag]
    have hred := Lane_q_s06_steps2.dataLaw_pr_depends6 X
      (X.withHid H t ξ) D (fun o => gate ξ ∧ X.s3Mass H b D o none < X.s3Thr)
      hAdep o₀
    simpa [P, mass, complete, gate] using hred
  have hprobDel (ξ : Fin N) (c : Id × X.Ty) :
      (X.dataLaw Id (X.withHid H t ξ)).pr
        (fun o => gate ξ ∧ X.s3Mass H b D o none <
          X.s3Thr * X.s3Mass H b D o (some c)) =
      (P ξ).pr (fun a => gate ξ ∧ mass a < X.s3Thr * massDel c a) := by
    have hAdep : ∀ o o', (∀ e ∈ D, o e = o' e) →
        ((gate ξ ∧ X.s3Mass H b D o none <
            X.s3Thr * X.s3Mass H b D o (some c)) ↔
          (gate ξ ∧ X.s3Mass H b D o' none <
            X.s3Thr * X.s3Mass H b D o' (some c))) := by
      intro o o' hag
      rw [hmassDep H none o o' hag, hmassDep H (some c) o o' hag]
    have hred := Lane_q_s06_steps2.dataLaw_pr_depends6 X
      (X.withHid H t ξ) D
      (fun o => gate ξ ∧ X.s3Mass H b D o none <
        X.s3Thr * X.s3Mass H b D o (some c)) hAdep o₀
    simpa [P, mass, massDel, complete, gate] using hred
  have hmassDelNN (c : Id × X.Ty) : ∀ a : Ω, 0 ≤ massDel c a := by
    intro a
    exact hmassDelNonneg c a
  have hdelInt (ξ : Fin N) (c : Id × X.Ty) :
      ∑ a : Ω, Q.w a * likDel ξ c a ≤ 1 := by
    let fdel : Idx → X.Tuple → ℝ := fun e o =>
      if (some c : Option (Id × X.Ty)) = some e.1 then 1 else
        X.lowLik H b ξ e.1.2 o
    have hfdel : ∀ e o, 0 ≤ fdel e o := by
      intro e o
      by_cases he : e.1 = c
      · simp [fdel, he]
      · have hne : c ≠ e.1 := Ne.symm he
        simp [fdel, hne, Lane_q_s06_steps2.lowLik_nonneg6]
    have hInt : ∀ e : Idx, ∑ o, (Qcoord e).w o * fdel e o ≤ 1 := by
      intro e
      by_cases he : e.1 = c
      · simp [fdel, he, (Qcoord e).sum_eq_one]
      · have hne : c ≠ e.1 := Ne.symm he
        have hratio := Lane_q_s06_steps2.lowLik_integral_le_one6 X H b ξ e.1.2
        simpa [fdel, hne, Qcoord] using hratio
    have hprodDel (a : Ω) : likDel ξ c a = ∏ e : Idx, fdel e (a e) := by
      let g : Id × X.Ty → ℝ := fun e =>
        if (some c : Option (Id × X.Ty)) = some e then 1 else
          X.lowLik H b ξ e.2 (complete a e)
      have hattach : (∏ e : Idx, g e.1) = ∏ e ∈ D, g e := by
        rw [Finset.univ_eq_attach]
        simpa [g] using Finset.prod_attach D g
      calc
        likDel ξ c a = ∏ e ∈ D, g e := rfl
        _ = ∏ e : Idx, g e.1 := hattach.symm
        _ = ∏ e : Idx, fdel e (a e) := by
          apply Finset.prod_congr rfl
          intro e he
          simp [fdel, g, hComplete a e.1 e.2]
    have hsumInt :
        ∑ a : Ω, Q.w a * likDel ξ c a =
          ∏ e : Idx, ∑ o, (Qcoord e).w o * fdel e o := by
      calc
        ∑ a : Ω, Q.w a * likDel ξ c a =
            ∑ a : Ω, (∏ e : Idx, (Qcoord e).w (a e)) *
              (∏ e : Idx, fdel e (a e)) := by
          apply Finset.sum_congr rfl
          intro a ha
          change (∏ e : Idx, (Qcoord e).w (a e)) * likDel ξ c a = _
          rw [hprodDel a]
        _ = ∑ a : Ω, ∏ e : Idx, ((Qcoord e).w (a e) * fdel e (a e)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.prod_mul_distrib]
        _ = ∏ e : Idx, ∑ o, (Qcoord e).w o * fdel e o :=
          (Fintype.prod_sum (fun e o => (Qcoord e).w o * fdel e o)).symm
    have hprodle : ∀ s : Finset Idx,
        (∏ e ∈ s, ∑ o, (Qcoord e).w o * fdel e o) ≤ 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s he ih =>
        rw [Finset.prod_insert he]
        have hnonneg : 0 ≤ ∏ e ∈ s, ∑ o, (Qcoord e).w o * fdel e o :=
          Finset.prod_nonneg fun i hi => Finset.sum_nonneg fun o ho =>
            mul_nonneg ((Qcoord i).nonneg o) (hfdel i o)
        exact mul_le_one₀ (hInt e) hnonneg ih
    calc
      ∑ a : Ω, Q.w a * likDel ξ c a =
          ∏ e : Idx, ∑ o, (Qcoord e).w o * fdel e o := hsumInt
      _ ≤ 1 := by simpa using hprodle Finset.univ
  have hdelMassInt (c : Id × X.Ty) :
      ∑ a : Ω, Q.w a * massDel c a ≤ 1 := by
    calc
      ∑ a : Ω, Q.w a * massDel c a =
          ∑ a : Ω, Q.w a * ∑ ξ, if gate ξ then π.w ξ * likDel ξ c a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hmixDel c a]
      _ = ∑ a : Ω, ∑ ξ, Q.w a *
          (if gate ξ then π.w ξ * likDel ξ c a else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      _ = ∑ ξ, ∑ a : Ω, Q.w a *
          (if gate ξ then π.w ξ * likDel ξ c a else 0) := by
        rw [Finset.sum_comm]
      _ = ∑ ξ, π.w ξ *
          (if gate ξ then ∑ a : Ω, Q.w a * likDel ξ c a else 0) := by
        apply Finset.sum_congr rfl
        intro ξ hξ
        by_cases hg : gate ξ
        · simp only [if_pos hg]
          calc
            (∑ a : Ω, Q.w a * (π.w ξ * likDel ξ c a)) =
                ∑ a : Ω, π.w ξ * (Q.w a * likDel ξ c a) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
            _ = π.w ξ * ∑ a : Ω, Q.w a * likDel ξ c a := by rw [Finset.mul_sum]
        · simp [hg]
      _ ≤ ∑ ξ, π.w ξ := by
        apply Finset.sum_le_sum
        intro ξ hξ
        by_cases hg : gate ξ
        · simp only [if_pos hg]
          calc
            π.w ξ * ∑ a : Ω, Q.w a * likDel ξ c a ≤ π.w ξ * 1 :=
              mul_le_mul_of_nonneg_left (hdelInt ξ c) (π.nonneg ξ)
            _ = π.w ξ := by ring
        · simp only [if_neg hg, mul_zero]
          exact π.nonneg ξ
      _ = 1 := π.sum_eq_one
  have hthr : 0 < X.s3Thr := by
    unfold Ctx6.s3Thr
    exact Real.exp_pos _
  have hsmallRatio (c : Id × X.Ty) :
      (∑ a : Ω, if mass a < X.s3Thr * massDel c a then Q.w a * mass a else 0) ≤ X.s3Thr :=
    Lane_q_s06_steps2.subdensity_ratio_small_mass6 Q mass (massDel c) X.s3Thr
      (hmassDelNN c) hthr.le
      (hdelMassInt c)
  have hmixBoundRatio (c : Id × X.Ty) :
      ∑ ξ, π.w ξ * (P ξ).pr (fun a => gate ξ ∧ mass a < X.s3Thr * massDel c a) ≤ X.s3Thr := by
    exact Lane_q_s06_steps2.mixture_subdensity_bound6 π Q P gate lik mass
      (fun a => X.s3Thr * massDel c a) X.s3Thr hmix hdom (hsmallRatio c)
  constructor
  · calc
      ∑ ξ, π.w ξ *
          (X.dataLaw Id (X.withHid H t ξ)).pr
            (fun o => gate ξ ∧ X.s3Mass H b D o none < X.s3Thr) =
        ∑ ξ, π.w ξ * (P ξ).pr (fun a => gate ξ ∧ mass a < X.s3Thr) := by
          apply Finset.sum_congr rfl
          intro ξ hξ
          rw [hprob ξ]
      _ ≤ X.s3Thr := by simpa [π, gate] using hmixBound
  · intro c hc
    calc
      ∑ ξ, π.w ξ *
          (X.dataLaw Id (X.withHid H t ξ)).pr
            (fun o => gate ξ ∧
              X.s3Mass H b D o none < X.s3Thr * X.s3Mass H b D o (some c)) =
        ∑ ξ, π.w ξ *
          (P ξ).pr (fun a => gate ξ ∧ mass a < X.s3Thr * massDel c a) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            rw [hprobDel ξ c]
      _ ≤ X.s3Thr := hmixBoundRatio c

set_option maxHeartbeats 400000 in
private theorem rawLowTestBound6 {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (hmode : X.stMode b = .low) (D : Finset (Id × X.Ty))
    (del : X.Hist → X.Data Id → ℝ)
    (hdelInv : ∀ H H' : X.Hist, H.1 = H'.1 →
      (∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) → ∀ o, del H o = del H' o)
    (hcond : ∀ H : X.Hist, X.BaseSupp H.1 →
      ∑ ξ, (X.hidPost H.1 (X.tgt b).1).w ξ *
        (X.dataLaw Id (X.withHid H (X.tgt b) ξ)).pr
          (fun o => X.LowGate H b D ξ ∧ X.s3Mass H b D o none < X.s3Thr * del H o) ≤ X.s3Thr) :
    (X.rawHistData Id).pr
      (fun ω => X.S3TrueGate ω.1 b D ∧ X.s3Mass ω.1 b D ω.2 none <
        X.s3Thr * del ω.1 ω.2) ≤ X.s3Thr := by
  classical
  let failure : X.Hist → X.Data Id → Prop := fun H o =>
    X.S3TrueGate H b D ∧ X.s3Mass H b D o none < X.s3Thr * del H o
  rw [Lane_q_s06_steps2.rawHistData_pr_expand6 X failure]
  have hhidden (base : X.Base) (hBaseSupp : X.BaseSupp base) :
      (X.hidLaw base).expect (fun z =>
        (X.dataLaw Id (base, z)).pr (failure (base, z))) ≤ X.s3Thr := by
    let target := X.tgt b
    let P : X.HKey → Law N := fun ℓ => X.hidPost base ℓ.1
    let restLaw : FinProb (({h : X.HKey // h ∉ ({target} : Finset X.HKey)} → Fin N)) :=
      FinProb.pi fun h : {h : X.HKey // h ∉ ({target} : Finset X.HKey)} =>
        X.hidPost base h.1.1
    let F : X.Hid → ℝ := fun z =>
      (X.dataLaw Id (base, z)).pr (failure (base, z))
    have hsplit := Lane_q_s06_steps2.pi_expect_split_coord6 P target F
    have hrest (r : {h : X.HKey // h ∉ ({target} : Finset X.HKey)} → Fin N) :
        ∑ ξ, (X.hidPost base target.1).w ξ *
          F (Lane_q_s06_steps2.piCoordAssemble6 target r ξ) ≤ X.s3Thr := by
      let z₀ : X.Hid := Lane_q_s06_steps2.piCoordAssemble6 target r X.y₀
      let H₀ : X.Hist := (base, z₀)
      have hcondBound :
          ∑ ξ, (X.hidPost H₀.1 target.1).w ξ *
            (X.dataLaw Id (X.withHid H₀ target ξ)).pr
              (fun o => X.LowGate H₀ b D ξ ∧ X.s3Mass H₀ b D o none <
                X.s3Thr * del H₀ o) ≤ X.s3Thr := by
        exact hcond H₀ hBaseSupp
      have hpr (ξ : Fin N) :
          F (Lane_q_s06_steps2.piCoordAssemble6 target r ξ) =
            (X.dataLaw Id (X.withHid H₀ target ξ)).pr
              (fun o => X.LowGate H₀ b D ξ ∧ X.s3Mass H₀ b D o none <
                X.s3Thr * del H₀ o) := by
        let zξ : X.Hid := Lane_q_s06_steps2.piCoordAssemble6 target r ξ
        let Hξ : X.Hist := (base, zξ)
        have hz : zξ = Function.update z₀ target ξ := by
          funext h
          by_cases hh : h = target
          · subst h
            simp [zξ, z₀, Lane_q_s06_steps2.piCoordAssemble6]
          · simp [zξ, z₀, Lane_q_s06_steps2.piCoordAssemble6, hh]
        have hHist : Hξ = X.withHid H₀ target ξ := by
          apply Prod.ext
          · rfl
          · exact hz
        have hbase : Hξ.1 = H₀.1 := rfl
        have hother : ∀ h, h ≠ target → Hξ.2 h = H₀.2 h := by
          intro h hne
          rw [hHist]
          simp [Ctx6.withHid, hne]
        have htrue : X.trueTarget Hξ b = ξ := by
          simp [Ctx6.trueTarget, hmode, Hξ, zξ, target,
            Lane_q_s06_steps2.piCoordAssemble6]
        have hgate : X.S3TrueGate Hξ b D ↔ X.LowGate H₀ b D ξ := by
          have hagree := Lane_q_s06_steps2.lowGate_eq_of_hidden_agree6 X Hξ H₀ b D ξ
            hbase hother
          simpa [Ctx6.S3TrueGate, hmode, htrue] using Iff.of_eq hagree
        have hmass (o : X.Data Id) :
            X.s3Mass Hξ b D o none = X.s3Mass H₀ b D o none :=
          Lane_q_s06_steps2.s3Mass_low_eq_of_hidden_agree6 X Hξ H₀ b D o none
            hmode hbase hother
        have hdel (o : X.Data Id) : del Hξ o = del H₀ o :=
          hdelInv Hξ H₀ hbase hother o
        have hEvent (o : X.Data Id) :
            failure Hξ o ↔ X.LowGate H₀ b D ξ ∧ X.s3Mass H₀ b D o none <
              X.s3Thr * del H₀ o := by
          simp only [failure, hgate, hmass, hdel]
        have hEvent' (o : X.Data Id) :
            failure (X.withHid H₀ target ξ) o ↔
              X.LowGate H₀ b D ξ ∧ X.s3Mass H₀ b D o none <
                X.s3Thr * del H₀ o := by
          rw [← hHist]
          exact hEvent o
        change (X.dataLaw Id Hξ).pr (failure Hξ) = _
        rw [hHist]
        unfold FinProb.pr
        apply Finset.sum_congr rfl
        intro o ho
        have hev := propext (hEvent' o)
        simp [hev]
      calc
        ∑ ξ, (X.hidPost base target.1).w ξ *
            F (Lane_q_s06_steps2.piCoordAssemble6 target r ξ) =
          ∑ ξ, (X.hidPost H₀.1 target.1).w ξ *
            (X.dataLaw Id (X.withHid H₀ target ξ)).pr
              (fun o => X.LowGate H₀ b D ξ ∧ X.s3Mass H₀ b D o none <
                X.s3Thr * del H₀ o) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            rw [hpr ξ]
        _ ≤ X.s3Thr := by simpa [H₀] using hcondBound
    change (FinProb.pi P).expect F ≤ X.s3Thr
    rw [Lane_q_s06_steps2.pi_expect_split_coord6 P target F]
    calc
      (∑ r : {h : X.HKey // h ∉ ({target} : Finset X.HKey)} → Fin N,
          (restLaw.w r) * ∑ ξ, (X.hidPost base target.1).w ξ *
            F (Lane_q_s06_steps2.piCoordAssemble6 target r ξ)) ≤
        ∑ r : {h : X.HKey // h ∉ ({target} : Finset X.HKey)} → Fin N,
          restLaw.w r * X.s3Thr := by
        apply Finset.sum_le_sum
        intro r hr
        exact mul_le_mul_of_nonneg_left (hrest r) (restLaw.nonneg r)
      _ = X.s3Thr := by
        rw [← Finset.sum_mul, restLaw.sum_eq_one]
        ring
  have hbaseBound (base : X.Base) :
      X.baseLaw.w base * (X.hidLaw base).expect (fun z =>
        (X.dataLaw Id (base, z)).pr (failure (base, z))) ≤
        X.baseLaw.w base * X.s3Thr := by
    by_cases hz : X.baseLaw.w base = 0
    · simp [hz]
    · have hpos : 0 < X.baseLaw.w base := by
        exact lt_of_le_of_ne (X.baseLaw.nonneg base) (Ne.symm hz)
      have hfac := Lane_q_s06_steps2.baseLaw_pos_factors6 X base hpos
      have hBaseSupp : X.BaseSupp base := by
        change X.KeysSupp base Finset.univ
        rcases hfac with ⟨hinit, hcand, htags⟩
        exact ⟨hinit, (fun u hu => hcand u), (fun s hs => htags s)⟩
      exact mul_le_mul_of_nonneg_left (hhidden base hBaseSupp) (X.baseLaw.nonneg base)
  calc
    (∑ base : X.Base, X.baseLaw.w base *
        (X.hidLaw base).expect (fun z =>
          (X.dataLaw Id (base, z)).pr (failure (base, z)))) ≤
      ∑ base : X.Base, X.baseLaw.w base * X.s3Thr := by
        apply Finset.sum_le_sum
        intro base hbase
        exact hbaseBound base
    _ = X.s3Thr := by
      rw [← Finset.sum_mul, X.baseLaw.sum_eq_one]
      ring

/-- L6.1f (tests, 06:340–353): `M` is the true-gated subdensity relative to `Q^data` and `∫ M_{−c} dQ^data ≤ 1`. -/
theorem L6_1f_tests (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp → X.Step3TestLow := by
  classical
  refine ⟨0, 0, ?_⟩
  intro n N E G M X hLarge
  intro hStep2Supp
  intro Id instFin instDec b hb hmode D hTypes
  constructor
  · let delOne : X.Hist → X.Data Id → ℝ := fun _ _ => 1
    have hdelInv : ∀ H H' : X.Hist, H.1 = H'.1 →
        (∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) → ∀ o, delOne H o = delOne H' o := by
      intro H H' hbase hother o
      rfl
    have hcond : ∀ H : X.Hist, X.BaseSupp H.1 →
        ∑ ξ, (X.hidPost H.1 (X.tgt b).1).w ξ *
          (X.dataLaw Id (X.withHid H (X.tgt b) ξ)).pr
            (fun o => X.LowGate H b D ξ ∧ X.s3Mass H b D o none < X.s3Thr * delOne H o) ≤ X.s3Thr := by
      intro H hBaseSupp
      have hc := lowConditionalMassTest6 X H b hmode hStep2Supp hBaseSupp D hTypes
      simpa [delOne] using hc.1
    have hraw := rawLowTestBound6 X b hmode D delOne hdelInv hcond
    simpa [delOne] using hraw
  · intro c hc
    let delC : X.Hist → X.Data Id → ℝ := fun H o => X.s3Mass H b D o (some c)
    have hdelInv : ∀ H H' : X.Hist, H.1 = H'.1 →
        (∀ h, h ≠ X.tgt b → H.2 h = H'.2 h) → ∀ o, delC H o = delC H' o := by
      intro H H' hbase hother o
      exact Lane_q_s06_steps2.s3Mass_low_eq_of_hidden_agree6 X H H' b D o
        (some c) hmode hbase hother
    have hcond : ∀ H : X.Hist, X.BaseSupp H.1 →
        ∑ ξ, (X.hidPost H.1 (X.tgt b).1).w ξ *
          (X.dataLaw Id (X.withHid H (X.tgt b) ξ)).pr
            (fun o => X.LowGate H b D ξ ∧
              X.s3Mass H b D o none < X.s3Thr * delC H o) ≤ X.s3Thr := by
      intro H hBaseSupp
      have hcnd := lowConditionalMassTest6 X H b hmode hStep2Supp hBaseSupp D hTypes
      simpa [delC] using hcnd.2 c hc
    have hraw := rawLowTestBound6 X b hmode D delC hdelInv hcond
    simpa [delC] using hraw

/-- L6.1f (bounds, 06:324–336, 06:355–366): tuple ratios `n^{d₂u}(1+4ε/c₁)^k` (matching), `n^{d₂u}(2/c₁)^k`
(nonmatching, at most one); prior cap, `O(T+J)` tuples; `O(J² log n) = o(m^{.15})`. -/
theorem L6_1f_bounds (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Dom → X.Step2Supp → X.DescSize → X.Step3LowBounds := by
  sorry

/-- L6.1g (tests, 06:411–426): the local list is closed under kernel inputs, so its marginal is the product of
its kernels; the deleted density integrates to at most one. -/
theorem L6_1g_tests (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp → X.Step3TestHigh := by
  sorry

/-- L6.1g (bounds, 06:428–447): the width budget `O(1 + d₀ log n) + O(J d₁ log n) + O((T+J) d₂ log n) + o(k) +
k log(2/c₁) + .02k < .05 J log n`. -/
theorem L6_1g_bounds (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.TagDom → X.Step2Dom → X.Step2Supp → X.DescSize → X.Step3HighBounds := by
  sorry

namespace Ctx6

/-- All Step 1–3 predicates (the conjunction assembled in the section proof). -/
def StepFacts : Prop :=
  X.TagDom ∧ X.Step1CapBound ∧ X.Step1DelBound ∧ X.Step2Bound ∧ X.Step2Dom ∧ X.Step2Supp ∧ X.DescSize ∧
    X.DescCount ∧ X.Step3TestLow ∧ X.Step3TestHigh ∧ X.Step3LowBounds ∧ X.Step3HighBounds

end Ctx6

/-- Steps 1–3 assembled from their nodes. -/
theorem stepFacts6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.StepFacts := by
  have h := (L6_1c_tag γ p₀ K hadm).and <| (L6_1c_cap γ p₀ K hadm).and <| (L6_1c_del γ p₀ K hadm).and <|
    (L6_1d_fail γ p₀ K hadm).and <| (L6_1d_dom γ p₀ K hadm).and <| (L6_1d_supp γ p₀ K hadm).and <|
    (L6_1e_size γ p₀ K hadm).and <| (L6_1e_count γ p₀ K hadm).and <| (L6_1f_tests γ p₀ K hadm).and <|
    (L6_1g_tests γ p₀ K hadm).and <| (L6_1f_bounds γ p₀ K hadm).and (L6_1g_bounds γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hT, hC, hD, h2, h2d, h2s, hS, hN, h3l, h3h, hbl, hbh⟩
  exact ⟨hT, hC hT, hD hT, h2, h2d hT, h2s, hS, hN, h3l h2s, h3h h2s, hbl (h2d hT) h2s hS,
    hbh hT (h2d hT) h2s hS⟩

end

end S06
end HypercubeRamsey
