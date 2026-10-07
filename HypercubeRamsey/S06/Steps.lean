import HypercubeRamsey.S06.Step3Defs
import HypercubeRamsey.S06.Steps_q_s06_steps1

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
open Filter
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
  have he : 0 < d₀ - 2 * Dstar₆ := by
    have hf := constants6_facts
    linarith
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (d₀ - 2 * Dstar₆)) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, 1 / c₁ ≤ (n : ℝ) ^ (d₀ - 2 * Dstar₆) :=
    htend.eventually (eventually_ge_atTop (1 / c₁))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  let n₀' := max 1 n₀
  refine ⟨n₀', 1, ?_⟩
  intro n N E G M X hlarge
  have hn1nat : 1 ≤ n := le_trans (le_max_left 1 n₀) hlarge.1
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1nat
  have hnexp : (n : ℝ) ^ (d₀ - 2 * Dstar₆) ≥ 1 / c₁ :=
    hn₀ n (le_trans (le_max_right 1 n₀) hlarge.1)
  intro pv key hheavy hrelated i
  let η := tagPosterior6 M (pv.val (primaryName6 key))
  let f : M.ι → ℝ := fun j => colDeg E G (M.μ j) (pv.val (otherPrimaryName6 key))
  have haverage : c₀ ≤ ∑ j, η.w j * f j := by
    calc
      c₀ ≤ colDeg E G (broadLaw6 M (pv.val (primaryName6 key))) (pv.val (otherPrimaryName6 key)) :=
        hrelated.1
      _ = ∑ j, η.w j * f j := by
        simpa [η, f, broadLaw6] using
          (colDeg_mix6 E G (tagPosterior6 M (pv.val (primaryName6 key))) M.μ
            (pv.val (otherPrimaryName6 key)))
  have hc : 0 ≤ c₁ := by norm_num [c₁, c₀]
  have htwoc : 2 * c₁ = c₀ := by norm_num [c₁, c₀]
  have hmassSum : c₁ ≤ ∑ j, if c₁ ≤ f j then η.w j else 0 := by
    apply mass_ge_from_average6 η f c₁ hc _ (fun j => colDeg_nonneg6 E G (M.μ j) _)
      (fun j => colDeg_le_one6 E G (M.μ j) _)
    rw [htwoc]
    exact haverage
  have hmass : c₁ ≤ η.pr (fun j => c₁ ≤ f j) := by
    simpa [FinProb.pr] using hmassSum
  have hcap : ∀ j, η.w j ≤ (n : ℝ) ^ (2 * Dstar₆) * M.Λ j := by
    intro j
    exact X.par.eta_cap (pv.val (primaryName6 key)) hheavy j
  simpa [Ctx6.tagLawAt, baseTagLaw6, η, f] using
    (restricted_tag_bound6 M (pv.val (primaryName6 key)) i X.i₀
      (fun j => c₁ ≤ f j) hmass hcap hn1 hnexp)

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
  refine ⟨1, 1, ?_⟩
  intro n N E G M X hlarge hTagDom
  have hn1nat : 1 ≤ n := hlarge.1
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1nat
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  intro H β hβ hKeys hTests
  rcases hKeys with ⟨hinit, ⟨hcands, _htags⟩⟩
  have hbin : β.key.1 ∈ X.binsOf {β.key} := by
    simp [Ctx6.binsOf]
  have hcand : 0 < (X.candLaw H.1.1).w (H.1.2.1 β.key.1) := hcands _ hbin
  have hparent := parent_heavy_related_of_local_support X β.key H.1 hinit hcand
  have hbaseTag : ∀ i, (X.tagLawAt (X.parOf H.1) β.key).w i ≤
      (n : ℝ) ^ d₀ * M.Λ i := by
    intro i
    exact hTagDom (X.parOf H.1) β.key hparent.1 hparent.2 i
  have hcardN := occType_obs_card_le X β hβ
  have hcard : (β.obs.card : ℝ) ≤ 602 * (β.u : ℝ) := by exact_mod_cast hcardN
  have huNat : 1 ≤ β.u := by
    cases hm : β.mode <;> simp [Type6.u, hm] <;> omega
  have hu : 1 ≤ (β.u : ℝ) := by exact_mod_cast huNat
  have hd0 : 0 ≤ d₀ := by norm_num [d₀]
  have hd1 : 0 ≤ d₁ := by norm_num [d₁]
  have hd2 : 0 ≤ δ₂ := by norm_num [δ₂]
  have hD : 602 * d₁ + δ₂ + d₀ < d₂ := by
    rcases constants6_facts with ⟨_, _, _, hD, _, _, _, _⟩
    exact hD
  have hcoeff : d₀ + 602 * d₁ + δ₂ ≤ d₂ := by linarith
  have hExp : d₀ + d₁ * (β.obs.card : ℝ) + δ₂ * (β.u : ℝ) ≤
      d₂ * (β.u : ℝ) := by
    have hcardMul := mul_le_mul_of_nonneg_left hcard hd1
    have huMul := mul_le_mul_of_nonneg_left hu hd0
    calc
      d₀ + d₁ * (β.obs.card : ℝ) + δ₂ * (β.u : ℝ) ≤
          d₀ * (β.u : ℝ) + (602 * d₁) * (β.u : ℝ) + δ₂ * (β.u : ℝ) := by nlinarith
      _ = (d₀ + 602 * d₁ + δ₂) * (β.u : ℝ) := by ring
      _ ≤ d₂ * (β.u : ℝ) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  have hExpDel : d₁ + δ₂ * (β.u : ℝ) ≤ d₂ * (β.u : ℝ) := by
    have hsmall : d₁ + δ₂ ≤ d₂ := by linarith [hD]
    have hu0 : 0 ≤ (β.u : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hsmall hu0
    have hd1u : d₁ ≤ d₁ * (β.u : ℝ) := by nlinarith [hd1, hu]
    calc
      d₁ + δ₂ * (β.u : ℝ) ≤ d₁ * (β.u : ℝ) + δ₂ * (β.u : ℝ) := by linarith
      _ = (d₁ + δ₂) * (β.u : ℝ) := by ring
      _ ≤ d₂ * (β.u : ℝ) := hmul
  have hpow : (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ) + δ₂ * (β.u : ℝ)) ≤
      (n : ℝ) ^ (d₂ * (β.u : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 hExp
  have hpowDel : (n : ℝ) ^ (d₁ + δ₂ * (β.u : ℝ)) ≤
      (n : ℝ) ^ (d₂ * (β.u : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 hExpDel
  have hweightNonneg : ∀ S : Finset X.HKey, ∀ i,
      0 ≤ X.tagWeight H β S i := by
    intro S i
    unfold Ctx6.tagWeight
    have hgate : 0 ≤ if X.tagGate H.1 β i then (1 : ℝ) else 0 := by split_ifs <;> norm_num
    apply mul_nonneg
    · exact mul_nonneg ((X.tagLawAt (X.parOf H.1) β.key).nonneg i) hgate
    · apply Finset.prod_nonneg
      intro ℓ hℓ
      exact safeRatio6_nonneg
        ((X.hidPostRep H.1 ℓ.1 β.key i).nonneg (H.2 ℓ))
        ((X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ))
  have hfullMassPos : 0 < X.tagMass H β β.obs := hTests.1
  have hfullSumPos : 0 < ∑ i, X.tagWeight H β β.obs i := by
    simpa [Ctx6.tagMass] using hfullMassPos
  have hfullNorm (i : X.ι) : (X.Tβ H β).w i =
      X.tagWeight H β β.obs i / X.tagMass H β β.obs := by
    simpa [Ctx6.Tβ, Ctx6.tagPost, Ctx6.tagMass] using
      (normalize6_weight_formula (fun j => X.tagWeight H β β.obs j) X.i₀ i
        (fun j => hweightNonneg β.obs j) hfullSumPos)
  have htagWeightBound : ∀ i, X.tagWeight H β β.obs i ≤
      (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i := by
    intro i
    by_cases hgate : X.tagGate H.1 β i
    · have hratio : ∀ ℓ ∈ β.obs,
          0 ≤ safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
              ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) ∧
            safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
              ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) ≤ (n : ℝ) ^ d₁ := by
          intro ℓ hℓ
          have hrep := (X.hidPostRep H.1 ℓ.1 β.key i).nonneg (H.2 ℓ)
          have hdel := (X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ)
          refine ⟨safeRatio6_nonneg hrep hdel, safeRatio6_le_of_le_mul hrep hdel
            (Real.rpow_nonneg (Nat.cast_nonneg n) _) ?_⟩
          exact hgate ℓ hℓ (H.2 ℓ)
      have hprod : (∏ ℓ ∈ β.obs, safeRatio6
            ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ))) ≤
            (n : ℝ) ^ (d₁ * (β.obs.card : ℝ)) := by
        rw [Real.rpow_mul_natCast (Nat.cast_nonneg n) d₁ β.obs.card]
        exact prod_le_const_pow_card β.obs
          (fun ℓ => safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)))
          ((n : ℝ) ^ d₁) (Real.rpow_nonneg (Nat.cast_nonneg n) _) (fun ℓ hℓ => (hratio ℓ hℓ).1)
          (fun ℓ hℓ => (hratio ℓ hℓ).2)
      have htag0 : 0 ≤ (X.tagLawAt (X.parOf H.1) β.key).w i :=
        (X.tagLawAt (X.parOf H.1) β.key).nonneg i
      have htag := hbaseTag i
      unfold Ctx6.tagWeight
      simp only [if_pos hgate, mul_one]
      calc
        (X.tagLawAt (X.parOf H.1) β.key).w i *
            (∏ ℓ ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
              ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ))) ≤
            (X.tagLawAt (X.parOf H.1) β.key).w i * (n : ℝ) ^ (d₁ * (β.obs.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod htag0
        _ ≤ (n : ℝ) ^ d₀ * M.Λ i * (n : ℝ) ^ (d₁ * (β.obs.card : ℝ)) :=
          mul_le_mul_of_nonneg_right htag (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i := by
          calc
            ((n : ℝ) ^ d₀ * M.Λ i) * (n : ℝ) ^ (d₁ * (β.obs.card : ℝ)) =
                ((n : ℝ) ^ d₀ * (n : ℝ) ^ (d₁ * (β.obs.card : ℝ))) * M.Λ i := by ring
            _ = (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i := by
              rw [← Real.rpow_add hnpos]
    · have hΛ : 0 ≤ M.Λ i := M.Λ_nonneg i
      unfold Ctx6.tagWeight
      simp only [if_neg hgate, mul_zero, zero_mul]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hΛ
  refine ⟨?_, ?_⟩
  · intro i
    have hupper : 0 ≤ (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (M.Λ_nonneg i)
    have hthreshold : (n : ℝ) ^ (-(δ₂ * β.u)) ≤ X.tagMass H β β.obs := by
      simpa [Ctx6.step2Thr] using hTests.2.1
    have hthresholdPos : 0 < (n : ℝ) ^ (-(δ₂ * β.u)) := Real.rpow_pos_of_pos hnpos _
    calc
      (X.Tβ H β).w i = X.tagWeight H β β.obs i / X.tagMass H β β.obs := hfullNorm i
      _ ≤ ((n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i) /
          X.tagMass H β β.obs := div_le_div_of_nonneg_right (htagWeightBound i) hfullMassPos.le
      _ ≤ ((n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i) /
          ((n : ℝ) ^ (-(δ₂ * β.u))) :=
            div_le_div_of_nonneg_left hupper hthresholdPos hthreshold
      _ = (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ) + δ₂ * (β.u : ℝ)) * M.Λ i := by
            rw [div_eq_mul_inv, Real.rpow_neg hnpos.le, inv_inv]
            calc
              ((n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) * M.Λ i) *
                  (n : ℝ) ^ (δ₂ * (β.u : ℝ)) =
                  ((n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ)) *
                    (n : ℝ) ^ (δ₂ * (β.u : ℝ))) * M.Λ i := by ring
              _ = (n : ℝ) ^ (d₀ + d₁ * (β.obs.card : ℝ) + δ₂ * (β.u : ℝ)) * M.Λ i := by
                rw [← Real.rpow_add hnpos]
      _ ≤ (n : ℝ) ^ (d₂ * (β.u : ℝ)) * M.Λ i :=
            mul_le_mul_of_nonneg_right hpow (M.Λ_nonneg i)
  · intro ℓ hℓ i
    have hdelMassPos : 0 < X.tagMass H β (β.obs.erase ℓ) := by
      have hex : ∃ j, 0 < X.tagWeight H β β.obs j := by
        by_contra hnone
        push_neg at hnone
        have hall : ∀ j, X.tagWeight H β β.obs j = 0 := by
          intro j
          exact le_antisymm (hnone j) (hweightNonneg β.obs j)
        have hzero : (∑ j, X.tagWeight H β β.obs j) = 0 := by
          rw [Finset.sum_eq_zero (fun j hj => hall j)]
        rw [← Ctx6.tagMass] at hzero
        linarith
      obtain ⟨j, hj⟩ := hex
      have hratio : 0 ≤ safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key j).w (H.2 ℓ))
          ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) ∧
        safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key j).w (H.2 ℓ))
          ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) ≤ (n : ℝ) ^ d₁ := by
        by_cases hg : X.tagGate H.1 β j
        · have ha := (X.hidPostRep H.1 ℓ.1 β.key j).nonneg (H.2 ℓ)
          have hb := (X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ)
          exact ⟨safeRatio6_nonneg ha hb,
            safeRatio6_le_of_le_mul ha hb (Real.rpow_nonneg (Nat.cast_nonneg n) _)
              (hg ℓ hℓ (H.2 ℓ))⟩
        · have hw : X.tagWeight H β β.obs j = 0 := by
            unfold Ctx6.tagWeight
            simp [hg]
          rw [hw] at hj
          norm_num at hj
      have hpoint : X.tagWeight H β β.obs j ≤ (n : ℝ) ^ d₁ *
          X.tagWeight H β (β.obs.erase ℓ) j := by
        by_cases hg : X.tagGate H.1 β j
        · have hratio' : safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key j).w (H.2 ℓ))
              ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) ≤ (n : ℝ) ^ d₁ := hratio.2
          have hprodRel :
              (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) ≤
              (n : ℝ) ^ d₁ * (∏ s ∈ β.obs.erase ℓ, safeRatio6
                ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
            have heq : (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) =
                safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key j).w (H.2 ℓ))
                  ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) *
                  (∏ s ∈ β.obs.erase ℓ, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                    ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
              rw [← Finset.prod_erase_mul β.obs
                (fun s => safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) hℓ]
              ring
            calc
              (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) =
                  safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key j).w (H.2 ℓ))
                    ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) *
                    (∏ s ∈ β.obs.erase ℓ, safeRatio6
                      ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                      ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := heq
              _ ≤ (n : ℝ) ^ d₁ * (∏ s ∈ β.obs.erase ℓ, safeRatio6
                    ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                    ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) :=
                    mul_le_mul_of_nonneg_right hratio'
                      (Finset.prod_nonneg fun s hs =>
                        safeRatio6_nonneg ((X.hidPostRep H.1 s.1 β.key j).nonneg (H.2 s))
                          ((X.hidPostDel H.1 s.1 β.key).nonneg (H.2 s)))
          have htag0 := (X.tagLawAt (X.parOf H.1) β.key).nonneg j
          have hbase : (X.tagLawAt (X.parOf H.1) β.key).w j *
              (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) ≤
              (n : ℝ) ^ d₁ * (X.tagLawAt (X.parOf H.1) β.key).w j *
                (∏ s ∈ β.obs.erase ℓ, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
            calc
              _ ≤ (X.tagLawAt (X.parOf H.1) β.key).w j *
                    ((n : ℝ) ^ d₁ * (∏ s ∈ β.obs.erase ℓ, safeRatio6
                      ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                      ((X.hidPostDel H.1 s.1 β.key).w (H.2 s)))) :=
                    mul_le_mul_of_nonneg_left hprodRel htag0
              _ = _ := by ring
          calc
            X.tagWeight H β β.obs j = (X.tagLawAt (X.parOf H.1) β.key).w j *
                (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
                    simp [Ctx6.tagWeight, hg]
            _ ≤ (n : ℝ) ^ d₁ * (X.tagLawAt (X.parOf H.1) β.key).w j *
                  (∏ s ∈ β.obs.erase ℓ, safeRatio6 ((X.hidPostRep H.1 s.1 β.key j).w (H.2 s))
                    ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := hbase
            _ = (n : ℝ) ^ d₁ * X.tagWeight H β (β.obs.erase ℓ) j := by
                  simp [Ctx6.tagWeight, hg]
                  ring
        · have hfullZero : X.tagWeight H β β.obs j = 0 := by
            unfold Ctx6.tagWeight
            simp [hg]
          have hdelZero : X.tagWeight H β (β.obs.erase ℓ) j = 0 := by
            unfold Ctx6.tagWeight
            simp [hg]
          rw [hfullZero, hdelZero]
          simp
      have hdelj : 0 < X.tagWeight H β (β.obs.erase ℓ) j := by
        by_contra hnonpos
        have hz : X.tagWeight H β (β.obs.erase ℓ) j = 0 :=
          le_antisymm (le_of_not_gt hnonpos) (hweightNonneg (β.obs.erase ℓ) j)
        rw [hz] at hpoint
        simp at hpoint
        linarith
      have hlesum : X.tagWeight H β (β.obs.erase ℓ) j ≤
          ∑ q, X.tagWeight H β (β.obs.erase ℓ) q :=
        Finset.single_le_sum (fun q hq => hweightNonneg (β.obs.erase ℓ) q) (Finset.mem_univ j)
      have hsumPos : 0 < ∑ q, X.tagWeight H β (β.obs.erase ℓ) q :=
        lt_of_lt_of_le hdelj hlesum
      simpa [Ctx6.tagMass] using hsumPos
    have hdelSumPos : 0 < ∑ j, X.tagWeight H β (β.obs.erase ℓ) j := by
      simpa [Ctx6.tagMass] using hdelMassPos
    have hdelNorm (j : X.ι) : (X.TβDel H β ℓ).w j =
        X.tagWeight H β (β.obs.erase ℓ) j / X.tagMass H β (β.obs.erase ℓ) := by
      simpa [Ctx6.TβDel, Ctx6.tagPost, Ctx6.tagMass] using
        (normalize6_weight_formula (fun q => X.tagWeight H β (β.obs.erase ℓ) q) X.i₀ j
          (fun q => hweightNonneg (β.obs.erase ℓ) q) hdelSumPos)
    have hratioWeight : X.tagWeight H β β.obs i ≤ (n : ℝ) ^ d₁ *
        X.tagWeight H β (β.obs.erase ℓ) i := by
      by_cases hg : X.tagGate H.1 β i
      · have hratio' : safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) ≤ (n : ℝ) ^ d₁ := by
          exact safeRatio6_le_of_le_mul
            ((X.hidPostRep H.1 ℓ.1 β.key i).nonneg (H.2 ℓ))
            ((X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ))
            (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hg ℓ hℓ (H.2 ℓ))
        have hprodRel :
            (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
              ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) ≤
            (n : ℝ) ^ d₁ * (∏ s ∈ β.obs.erase ℓ, safeRatio6
              ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
              ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
          have heq : (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) =
              safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
                ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) *
                (∏ s ∈ β.obs.erase ℓ, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
            rw [← Finset.prod_erase_mul β.obs
              (fun s => safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) hℓ]
            ring
          calc
            (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) =
                safeRatio6 ((X.hidPostRep H.1 ℓ.1 β.key i).w (H.2 ℓ))
                  ((X.hidPostDel H.1 ℓ.1 β.key).w (H.2 ℓ)) *
                  (∏ s ∈ β.obs.erase ℓ, safeRatio6
                    ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                    ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := heq
            _ ≤ (n : ℝ) ^ d₁ * (∏ s ∈ β.obs.erase ℓ, safeRatio6
                  ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) :=
                  mul_le_mul_of_nonneg_right hratio'
                    (Finset.prod_nonneg fun s hs =>
                      safeRatio6_nonneg ((X.hidPostRep H.1 s.1 β.key i).nonneg (H.2 s))
                        ((X.hidPostDel H.1 s.1 β.key).nonneg (H.2 s)))
        have htag0 := (X.tagLawAt (X.parOf H.1) β.key).nonneg i
        have hbase : (X.tagLawAt (X.parOf H.1) β.key).w i *
            (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
              ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) ≤
            (n : ℝ) ^ d₁ * (X.tagLawAt (X.parOf H.1) β.key).w i *
              (∏ s ∈ β.obs.erase ℓ, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
          calc
            _ ≤ (X.tagLawAt (X.parOf H.1) β.key).w i *
                  ((n : ℝ) ^ d₁ * (∏ s ∈ β.obs.erase ℓ, safeRatio6
                    ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                    ((X.hidPostDel H.1 s.1 β.key).w (H.2 s)))) :=
                  mul_le_mul_of_nonneg_left hprodRel htag0
            _ = _ := by ring
        calc
          X.tagWeight H β β.obs i = (X.tagLawAt (X.parOf H.1) β.key).w i *
              (∏ s ∈ β.obs, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := by
                  simp [Ctx6.tagWeight, hg]
          _ ≤ (n : ℝ) ^ d₁ * (X.tagLawAt (X.parOf H.1) β.key).w i *
                (∏ s ∈ β.obs.erase ℓ, safeRatio6 ((X.hidPostRep H.1 s.1 β.key i).w (H.2 s))
                  ((X.hidPostDel H.1 s.1 β.key).w (H.2 s))) := hbase
          _ = (n : ℝ) ^ d₁ * X.tagWeight H β (β.obs.erase ℓ) i := by
                simp [Ctx6.tagWeight, hg]
                ring
      · simp [Ctx6.tagWeight, hg]
    have hdelTest : (n : ℝ) ^ (-(δ₂ * β.u)) * X.tagMass H β (β.obs.erase ℓ) ≤
        X.tagMass H β β.obs := by
      simpa [Ctx6.step2Thr] using hTests.2.2 ℓ hℓ
    have hpowA : 0 < (n : ℝ) ^ (δ₂ * (β.u : ℝ)) := Real.rpow_pos_of_pos hnpos _
    have hcancel : (n : ℝ) ^ (δ₂ * (β.u : ℝ)) *
        (n : ℝ) ^ (-(δ₂ * (β.u : ℝ))) = 1 := by
      calc
        _ = (n : ℝ) ^ (δ₂ * (β.u : ℝ) + -(δ₂ * (β.u : ℝ))) := by
              rw [← Real.rpow_add hnpos]
        _ = 1 := by simp
    have hmassDelLe : X.tagMass H β (β.obs.erase ℓ) ≤
        (n : ℝ) ^ (δ₂ * (β.u : ℝ)) * X.tagMass H β β.obs := by
      calc
        X.tagMass H β (β.obs.erase ℓ) =
            (n : ℝ) ^ (δ₂ * (β.u : ℝ)) *
              ((n : ℝ) ^ (-(δ₂ * (β.u : ℝ))) * X.tagMass H β (β.obs.erase ℓ)) := by
                rw [← mul_assoc, hcancel, one_mul]
        _ ≤ (n : ℝ) ^ (δ₂ * (β.u : ℝ)) * X.tagMass H β β.obs :=
              mul_le_mul_of_nonneg_left hdelTest (le_of_lt hpowA)
    have hmassRatio : X.tagMass H β (β.obs.erase ℓ) / X.tagMass H β β.obs ≤
        (n : ℝ) ^ (δ₂ * (β.u : ℝ)) := (div_le_iff₀ hfullMassPos).2 hmassDelLe
    have hfrac : X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β β.obs ≤
        (n : ℝ) ^ (δ₂ * (β.u : ℝ)) *
          (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β (β.obs.erase ℓ)) := by
      have hmul := mul_le_mul_of_nonneg_right hmassRatio
        (div_nonneg (hweightNonneg (β.obs.erase ℓ) i) hdelMassPos.le)
      have heq : X.tagMass H β (β.obs.erase ℓ) / X.tagMass H β β.obs *
          (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β (β.obs.erase ℓ)) =
          X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β β.obs := by
        field_simp [ne_of_gt hdelMassPos, ne_of_gt hfullMassPos]
        <;> ring
      rw [← heq]
      exact hmul
    have hstep : (X.Tβ H β).w i ≤
        (n : ℝ) ^ (d₁ + δ₂ * (β.u : ℝ)) * (X.TβDel H β ℓ).w i := by
      calc
        (X.Tβ H β).w i = X.tagWeight H β β.obs i / X.tagMass H β β.obs := hfullNorm i
        _ ≤ ((n : ℝ) ^ d₁ * X.tagWeight H β (β.obs.erase ℓ) i) / X.tagMass H β β.obs :=
              div_le_div_of_nonneg_right hratioWeight hfullMassPos.le
        _ = (n : ℝ) ^ d₁ * (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β β.obs) := by
              field_simp [ne_of_gt hfullMassPos]
              <;> ring
        _ ≤ (n : ℝ) ^ d₁ * ((n : ℝ) ^ (δ₂ * (β.u : ℝ)) *
              (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β (β.obs.erase ℓ))) :=
              mul_le_mul_of_nonneg_left hfrac (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = (n : ℝ) ^ (d₁ + δ₂ * (β.u : ℝ)) * (X.TβDel H β ℓ).w i := by
              rw [hdelNorm i]
              calc
                (n : ℝ) ^ d₁ * ((n : ℝ) ^ (δ₂ * (β.u : ℝ)) *
                    (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β (β.obs.erase ℓ))) =
                    ((n : ℝ) ^ d₁ * (n : ℝ) ^ (δ₂ * (β.u : ℝ))) *
                      (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β (β.obs.erase ℓ)) := by ring
                _ = (n : ℝ) ^ (d₁ + δ₂ * (β.u : ℝ)) *
                      (X.tagWeight H β (β.obs.erase ℓ) i / X.tagMass H β (β.obs.erase ℓ)) := by
                        rw [← Real.rpow_add hnpos]
    calc
      (X.Tβ H β).w i ≤ (n : ℝ) ^ (d₁ + δ₂ * (β.u : ℝ)) * (X.TβDel H β ℓ).w i := hstep
      _ ≤ (n : ℝ) ^ (d₂ * (β.u : ℝ)) * (X.TβDel H β ℓ).w i :=
            mul_le_mul_of_nonneg_right hpowDel ((X.TβDel H β ℓ).nonneg i)

/-- L6.1d (support, 06:220–226): positive likelihood for `Z_{(h',t')}` forces the base tag at `h ∈ C(h')` to see
that value (`≥ 1 − ε` for the same named primary, `≥ c₁` in the crossing case); at most one required column
has degree only `c₁`; `c₁ − O(mε) ≥ c₁/2`. -/
theorem L6_1d_supp (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp := by
  rcases hadm with ⟨_, _, hp₀, _⟩
  obtain ⟨nErr, hnErr⟩ := Filter.eventually_atTop.1
    (Lane_q_s06_steps1.eventually_m6_req_error hp₀)
  refine ⟨max 1 nErr, 1, ?_⟩
  intro n N E G M X hlarge
  have hn1Nat : 1 ≤ n := le_trans (le_max_left 1 nErr) hlarge.1
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn1Nat
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hErr : (602 * ((X.m : ℝ) + 1) + 2) * X.ε ≤ c₁ / 2 := by
    have h := hnErr n (le_trans (le_max_right 1 nErr) hlarge.1)
    simpa [Ctx6.m, Ctx6.ε, m₆, ε₆, X.g.m_eq] using h
  have hεpos : 0 < X.ε := by
    simp [Ctx6.ε, ε₆]
    exact Real.rpow_pos_of_pos hnpos _
  intro H β hβ hKeys hTests i hi
  have hMatchEquiv : ∀ nm : X.Name, matchesPrimaryName6 β nm ↔ X.MatchName β nm := by
    intro nm
    cases nm <;> rfl
  have hMatchEquiv : ∀ nm : X.Name, matchesPrimaryName6 β nm ↔ X.MatchName β nm := by
    intro nm
    cases nm <;> rfl
  let S : Finset X.Name := reqNames6 β
  have hbin : β.key.1 ∈ X.binsOf (X.typeKeys β) := by
    unfold Ctx6.binsOf Ctx6.typeKeys
    exact Finset.mem_image.mpr ⟨β.key, Finset.mem_insert_self _ _, rfl⟩
  have hcand : 0 < (X.candLaw H.1.1).w (H.1.2.1 β.key.1) := hKeys.2.1 _ hbin
  have hparent := parent_heavy_related_of_local_support X β.key H.1 hKeys.1 hcand
  have hmass : 0 < X.tagMass H β β.obs := hTests.1
  have hweight : 0 < X.tagWeight H β β.obs i :=
    Lane_q_s06_steps1.Tβ_pos_tagWeight X H β i hmass hi
  have htagPos := Lane_q_s06_steps1.tagWeight_pos_tagLaw X H β β.obs i hweight
  have hbaseTag := Lane_q_s06_steps1.baseTag_pos_accept_of_average X (X.parOf H.1) β.key
    hparent.2.1 i htagPos
  have hmixParent := Lane_q_s06_steps1.posterior_heavy_pos_mixture X hn1Nat
    ((X.parOf H.1).val (primaryName6 β.key)) hparent.1
  have hnuParent := Lane_q_s06_steps1.tagPosterior_pos_nu_of_positive_mixture X
    ((X.parOf H.1).val (primaryName6 β.key)) i hmixParent hbaseTag.2
  have hdegParent := X.hDeg i ((X.parOf H.1).val (primaryName6 β.key)) hnuParent.1 hnuParent.2
  have hdegree : ∀ nm ∈ S,
      (if matchesPrimaryName6 β nm then 1 - X.ε else c₁) ≤
        colDeg E G (M.μ i) (X.varVal H nm) := by
    intro nm hnm
    cases nm with
    | par p =>
        change VarName6.par p ∈ reqNames6 β at hnm
        have hparentName : p = primaryName6 β.key ∨ p = otherPrimaryName6 β.key := by
          by_cases hmode : β.mode = .high
          · simp [reqNames6, hmode] at hnm
            rcases hnm with hprimary | hother
            · exact Or.inl hprimary
            · exact Or.inr hother
          · simp [reqNames6, hmode] at hnm
            exact Or.inl hnm
        rcases hparentName with hprimary | hother
        · have hmatch : matchesPrimaryName6 β (.par p) := by
            simp [matchesPrimaryName6, hprimary]
          have hparentHigh : 1 - X.ε ≤
              colDeg E G (M.μ i) ((X.parOf H.1).val (primaryName6 β.key)) := by
            change 1 - (n : ℝ) ^ (-p₀) ≤ _
            exact hdegParent
          have hde : (if matchesPrimaryName6 β (.par p) then 1 - X.ε else c₁) ≤
              colDeg E G (M.μ i) (X.varVal H (.par p)) := by
            rw [if_pos hmatch]
            change 1 - X.ε ≤ colDeg E G (M.μ i) (X.varVal H (.par p))
            simpa [Ctx6.varVal, hprimary] using hparentHigh
          exact hde
        · have hnot : ¬ matchesPrimaryName6 β (.par p) := by
            have hne : primaryName6 β.key ≠ otherPrimaryName6 β.key := by
              cases hflag : β.key.2 <;> simp [primaryName6, otherPrimaryName6, hflag]
            intro hm
            have hp : p = primaryName6 β.key := by simpa [matchesPrimaryName6] using hm
            exact hne (hp.symm.trans hother)
          have hde : (if matchesPrimaryName6 β (.par p) then 1 - X.ε else c₁) ≤
              colDeg E G (M.μ i) (X.varVal H (.par p)) := by
            rw [if_neg hnot]
            change c₁ ≤ colDeg E G (M.μ i) (X.varVal H (.par p))
            simpa [Ctx6.varVal, hother] using hbaseTag.1
          exact hde
    | hid ℓ =>
        change VarName6.hid ℓ ∈ reqNames6 β at hnm
        have hℓ : ℓ ∈ β.obs := by
          by_cases hmode : β.mode = .high
          · simp [reqNames6, hmode] at hnm
            exact hnm
          · simpa [reqNames6, hmode] using hnm
        have hkeyrel := occObs_key_mem_C X β hβ ℓ hℓ
        have hratio := Lane_q_s06_steps1.tagWeight_pos_ratio X H β β.obs i ℓ hℓ hweight
        have hrepPos := Lane_q_s06_steps1.safeRatio6_pos_num
          ((X.hidPostRep H.1 ℓ.1 β.key i).nonneg (H.2 ℓ))
          ((X.hidPostDel H.1 ℓ.1 β.key).nonneg (H.2 ℓ)) hratio
        have hrepWeight := Lane_q_s06_steps1.hidPostRep_pos_weight X H.1 β ℓ hℓ
          hKeys hkeyrel i htagPos (H.2 ℓ) hrepPos
        let pvS := (X.parOf (X.withTag H.1 β.key i)).set (primaryName6 ℓ.1) (H.2 ℓ)
        have htagModWeight := Lane_q_s06_steps1.hidWeight_pos_tagFactor
          X (X.withTag H.1 β.key i) ℓ.1 (X.C ℓ.1) (H.2 ℓ) β.key hkeyrel hrepWeight
        have htagMod : 0 < (X.tagLawAt pvS β.key).w i := by
          simpa [pvS, Ctx6.withTag, Ctx6.parOf] using htagModWeight
        have hpair0 := Lane_q_s06_steps1.hidWeight_parent_related_at_neighbor X
          (X.withTag H.1 β.key i) β.key ℓ.1 (H.2 ℓ) hKeys.1 hrepWeight hkeyrel
        have hpair : pvS.val (primaryName6 β.key) ∈ X.par.heavy ∧
            related6 E G M (pvS.val (primaryName6 β.key)) (pvS.val (otherPrimaryName6 β.key)) := by
          simpa [pvS] using hpair0
        have hbaseMod := Lane_q_s06_steps1.baseTag_pos_accept_of_average X pvS β.key
          hpair.2.1 i htagMod
        by_cases hmatch : matchesPrimaryName6 β (.hid ℓ)
        · have hnames : primaryName6 ℓ.1 = primaryName6 β.key := by
            simpa [matchesPrimaryName6] using hmatch
          have hval : pvS.val (primaryName6 β.key) = H.2 ℓ := by
            cases hp : primaryName6 β.key <;>
              simp [pvS, Ctx6.parOf, Par6.val, Par6.set, hnames, hp]
          have hmix := Lane_q_s06_steps1.posterior_heavy_pos_mixture X hn1Nat
            (pvS.val (primaryName6 β.key)) hpair.1
          have hnu := Lane_q_s06_steps1.tagPosterior_pos_nu_of_positive_mixture X
            (pvS.val (primaryName6 β.key)) i hmix hbaseMod.2
          have hdeg := X.hDeg i (pvS.val (primaryName6 β.key)) hnu.1 hnu.2
          have hde : (if matchesPrimaryName6 β (.hid ℓ) then 1 - X.ε else c₁) ≤
              colDeg E G (M.μ i) (X.varVal H (.hid ℓ)) := by
            rw [if_pos hmatch]
            change 1 - X.ε ≤ colDeg E G (M.μ i) (X.varVal H (.hid ℓ))
            have hdeg' : 1 - X.ε ≤ colDeg E G (M.μ i) (pvS.val (primaryName6 β.key)) := by
              change 1 - (n : ℝ) ^ (-p₀) ≤ _
              exact hdeg
            simpa [Ctx6.varVal, hval] using hdeg'
          exact hde
        · have hcrossOr := Lane_q_s06_steps1.neighbor_primary_eq_or_other ℓ.1 β.key
            (by
              change β.key ∈ Finset.univ.filter (keyAdjacent6 binAdjacent6 ℓ.1) at hkeyrel
              exact (Finset.mem_filter.mp hkeyrel).2)
          have hcross : primaryName6 ℓ.1 = otherPrimaryName6 β.key := by
            rcases hcrossOr with hsame | hcross
            · exact False.elim (hmatch (by simpa [matchesPrimaryName6] using hsame))
            · exact hcross
          have hval : pvS.val (otherPrimaryName6 β.key) = H.2 ℓ := by
            cases hp : otherPrimaryName6 β.key <;>
              simp [pvS, Ctx6.parOf, Par6.val, Par6.set, hcross, hp]
          have hde : (if matchesPrimaryName6 β (.hid ℓ) then 1 - X.ε else c₁) ≤
              colDeg E G (M.μ i) (X.varVal H (.hid ℓ)) := by
            rw [if_neg hmatch]
            change c₁ ≤ colDeg E G (M.μ i) (X.varVal H (.hid ℓ))
            simpa [Ctx6.varVal, hval] using hbaseMod.1
          exact hde
  obtain ⟨e, heS, hrest⟩ := Lane_q_s06_steps1.exists_req_except_matching6 X β hβ
  have heMatch : ∀ nm ∈ S.erase e, X.MatchName β nm := by
    intro nm hnm
    exact (hMatchEquiv nm).1 (hrest nm hnm)
  have hedegC : c₁ ≤ colDeg E G (M.μ i) (X.varVal H e) := by
    by_cases hm : matchesPrimaryName6 β e
    · have hde := hdegree e heS
      have hfactor : 1 ≤ 602 * ((X.m : ℝ) + 1) + 2 := by
        have hm0 : 0 ≤ (X.m : ℝ) := Nat.cast_nonneg _
        nlinarith
      have hεle : X.ε ≤ c₁ / 2 := by nlinarith [hErr, hfactor, hεpos]
      have hhigh : 1 - X.ε ≤ colDeg E G (M.μ i) (X.varVal H e) := by
        rw [if_pos hm] at hde
        exact hde
      have hc1small : c₁ ≤ 1 / 2 := by norm_num [c₁, c₀]
      have hc1high : c₁ ≤ 1 - X.ε := by linarith [hεle, hc1small]
      exact hc1high.trans hhigh
    · simpa [hm] using hdegree e heS
  have hmiss : ∀ nm ∈ S.erase e,
      (M.μ i).pr (fun x => ¬ Hits E G x (X.varVal H nm)) ≤ X.ε := by
    intro nm hnm
    have hmatch := heMatch nm hnm
    have hde := hdegree nm (Finset.mem_of_mem_erase hnm)
    have hhigh : 1 - X.ε ≤ colDeg E G (M.μ i) (X.varVal H nm) := by
      have hm : matchesPrimaryName6 β nm := (hMatchEquiv nm).2 hmatch
      rw [if_pos hm] at hde
      exact hde
    rw [Lane_q_s06_steps1.pr_not_eq_one_sub_pr6,
      ← Lane_q_s06_steps1.colDeg_eq_pr6 E G (M.μ i) (X.varVal H nm)]
    linarith
  have hcommon := pr_forall_lower6 (M.μ i) S
    (fun nm x => Hits E G x (X.varVal H nm)) e c₁ X.ε (le_of_lt hεpos) heS
    (by simpa [Lane_q_s06_steps1.colDeg_eq_pr6 E G (M.μ i) (X.varVal H e)] using hedegC) hmiss
  have hcardNat : S.card ≤ 602 * β.u + 2 := by
    have hcard : S.card ≤ β.obs.card + 2 := by
      simpa [S] using Lane_q_s06_steps1.reqNames_card_le6 X β
    have hobsCard := occType_obs_card_le X β hβ
    calc
      S.card ≤ β.obs.card + 2 := hcard
      _ ≤ 602 * β.u + 2 := Nat.add_le_add_right hobsCard 2
  have hu : β.u ≤ X.m + 1 := by
    change Type6.u β ≤ X.g.L.m + 1
    have hsevLe : β.2.2.1.val ≤ X.g.L.m := Nat.lt_succ_iff.mp β.2.2.1.isLt
    cases hmode : β.mode
    · rw [Type6.u, hmode]
      exact Nat.succ_le_succ hsevLe
    · simp [Type6.u, hmode]
  have hcardReal : (S.card : ℝ) ≤ 602 * ((X.m : ℝ) + 1) + 2 := by
    have hcardR : (S.card : ℝ) ≤ 602 * (β.u : ℝ) + 2 := by exact_mod_cast hcardNat
    have huR : (β.u : ℝ) ≤ (X.m : ℝ) + 1 := by exact_mod_cast hu
    nlinarith
  have hloss : (S.card : ℝ) * X.ε ≤ c₁ / 2 := by
    calc
      (S.card : ℝ) * X.ε ≤ (602 * ((X.m : ℝ) + 1) + 2) * X.ε :=
        mul_le_mul_of_nonneg_right hcardReal (le_of_lt hεpos)
      _ ≤ c₁ / 2 := hErr
  have hprobCommon : c₁ / 2 ≤
      (M.μ i).pr (fun x => ∀ nm ∈ S, Hits E G x (X.varVal H nm)) := by
    linarith [hcommon, hloss]
  have hprobEq : (M.μ i).pr (fun x => ∀ nm ∈ S, Hits E G x (X.varVal H nm)) =
      ∑ x ∈ X.reqNbhd H S, (M.μ i).w x := by
    classical
    unfold FinProb.pr Ctx6.reqNbhd
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hhit : ∀ nm ∈ S, Hits E G x (X.varVal H nm) <;> simp [hhit]
  constructor
  · rw [hprobEq] at hprobCommon
    exact hprobCommon
  · intro nm hnm hmatch
    have hde := hdegree nm hnm
    have hm : matchesPrimaryName6 β nm := (hMatchEquiv nm).2 hmatch
    rw [if_pos hm] at hde
    exact hde

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

/-- L6.1e (sizes, 06:270–273): constantly many generic types, each with at most `T` IDs; `O(J+1)` exceptional
states, one ID each. -/
theorem L6_1e_size (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescSize := by
  sorry

/-- L6.1e (counts, 06:274–281): list the at most `T` IDs, a subset for each generic type, one listed ID for each
exceptional state. -/
theorem L6_1e_count (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.DescCount := by
  sorry

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

/-- L6.1f (tests, 06:340–353): `M` is the true-gated subdensity relative to `Q^data` and `∫ M_{−c} dQ^data ≤ 1`. -/
theorem L6_1f_tests (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.Step2Supp → X.Step3TestLow := by
  sorry

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
