import HypercubeRamsey.S03.Height.Selection_p_height_main
import HypercubeRamsey.S03.Height.Split_opus_height_sol_hs_paths
import HypercubeRamsey.S03.Height.Split_opus_height_sol_hs_ovl_tail
import HypercubeRamsey.S03.Height.Split_opus_height_g_hs_count
import HypercubeRamsey.S03.Height.Split_opus_height_sol_hs_act

set_option maxHeartbeats 400000

/-!
# L3.8 parts 1–2: split of the remaining work (lane opus-height)

This file reduces `height_selection_global` and `height_selection_positive` to a small set of
exactly stated sub-lemmas (the "leaves", marked `LEAF` in their doc strings) and proves the
assembly of both targets from them in full.

The reduction follows TeX 03:319–584 (Lemma 3.8, Steps 1–5):

* Section 1 bundles the standard parameter hypotheses as `Std`.
* Section 2 defines the relaxed scale objects of Step 1: eligibility is read only inside a
  deterministic center domain `C`, bad site-levels only inside a deterministic path domain `Dom`,
  legality is required within metric distance `2R` of the start, and `relSup` is the
  eligibility supremum `B_i(P)` of (03:388–392). `ScaleClaim i` is the induction claim
  (03:393–396), uniform in `C`, `Dom` and the start.
* Section 3 states the leaves. The scale induction is `scale_claim_base` (Step 2) and
  `scale_claim_step` (Steps 3–4); `scale_claim_all` assembles them. The step itself is further
  split in Section 5.
* Section 4 assembles the two frozen targets (Step 5).

Helpers are public only inside `HypercubeRamsey.Lane_opus_height`.
-/

namespace HypercubeRamsey

namespace Lane_opus_height

open OAI.HypercubeRamsey
open Lane_p_height_main
open scoped BigOperators

/-! ## 0. Finite-probability helpers (proved) -/

theorem pr_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · simp only [if_neg hA]
    split_ifs with hB
    · exact P.nonneg ω
    · rfl

theorem pr_or_le {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) : P.pr (fun ω => A ω ∨ B ω) ≤ P.pr A + P.pr B := by
  classical
  simp only [FinProb.pr]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω <;> by_cases hB : B ω <;> simp [hA, hB] <;> linarith [P.nonneg ω]

theorem pr_finset_exists_le {Ω X : Type*} [Fintype Ω]
    (P : FinProb Ω) (S : Finset X) (F : X → Ω → Prop) :
    P.pr (fun ω => ∃ x ∈ S, F x ω) ≤ ∑ x ∈ S, P.pr (F x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert x S hx ih =>
      have hEq : (fun ω => ∃ y ∈ insert x S, F y ω) =
          (fun ω => F x ω ∨ ∃ y ∈ S, F y ω) := by
        funext ω
        apply propext
        simp
      rw [hEq]
      calc
        P.pr (fun ω => F x ω ∨ ∃ y ∈ S, F y ω)
            ≤ P.pr (F x) + P.pr (fun ω => ∃ y ∈ S, F y ω) := pr_or_le _ _ _
        _ ≤ P.pr (F x) + ∑ y ∈ S, P.pr (F y) := add_le_add le_rfl ih
        _ = ∑ y ∈ insert x S, P.pr (F y) := by simp [hx]

theorem pr_le_one {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) : P.pr A ≤ 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ ω, if A ω then P.w ω else 0) ≤ ∑ ω, P.w ω := by
      apply Finset.sum_le_sum
      intro ω _
      split_ifs <;> simp [P.nonneg ω]
    _ = 1 := P.sum_eq_one

theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A : Ω → Prop) : 0 ≤ P.pr A := by
  classical
  unfold FinProb.pr
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> simp [P.nonneg ω]

theorem prod_pr_eq_sections {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) = ∑ a, P.w a * Q.pr (F a) := by
  classical
  change (∑ ab : α × β, if F ab.1 ab.2 then P.w ab.1 * Q.w ab.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, if F a b then P.w a * Q.w b else 0) =
    P.w a * ∑ b, if F a b then Q.w b else 0
  calc
    (∑ b, if F a b then P.w a * Q.w b else 0)
        = ∑ b, P.w a * (if F a b then Q.w b else 0) := by
            apply Finset.sum_congr rfl
            intro b _
            by_cases h : F a b <;> simp [h]
    _ = P.w a * ∑ b, if F a b then Q.w b else 0 := by rw [Finset.mul_sum]

theorem prod_pr_le_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) (g : α → ℝ)
    (hF : ∀ a, Q.pr (F a) ≤ g a) :
    (P.prod Q).pr (fun ab => F ab.1 ab.2) ≤ P.expect g := by
  rw [prod_pr_eq_sections]
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (hF a) (P.nonneg a)

theorem expect_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f g : Ω → ℝ)
    (hfg : ∀ ω, f ω ≤ g ω) : P.expect f ≤ P.expect g := by
  unfold FinProb.expect
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hfg ω) (P.nonneg ω)

theorem expect_const {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  unfold FinProb.expect
  rw [← Finset.sum_mul, P.sum_eq_one, one_mul]

theorem expect_sum {Ω X : Type*} [Fintype Ω] (P : FinProb Ω) (S : Finset X)
    (f : X → Ω → ℝ) : P.expect (fun ω => ∑ x ∈ S, f x ω) = ∑ x ∈ S, P.expect (f x) := by
  unfold FinProb.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-! ## 1. Standard parameter hypotheses -/

/-- The hypotheses shared by the frozen targets, bundled. -/
structure Std (J₀ b₀ b σ ζ c_d C_d : ℝ) (D : ℕ) (reg : HDRegime b₀ b D)
    (p : HDParams) : Prop where
  hD : p.D = D
  hH : p.H = topScale p.n σ ζ
  hlam : p.lam = (p.n : ℝ) ^ J₀
  hb₀ : p.b₀ = b₀
  hb : p.b = b
  hdlo : c_d * p.n ≤ p.d
  hdhi : (p.d : ℝ) ≤ C_d * p.n
  hreg : reg.ok p.n p.d p.r

/-! ## 2. Relaxed scale objects (TeX 03:376–404) -/

/-- Present active centers of the deterministic center domain `C` in the same-level
`(r+D)`-ball of a site-level. -/
def relCrowd (p : HDParams) (C : Finset p.Loc) (P A : p.Loc → Bool)
    (v : CubeVertex p.d) (j : Fin (p.H + 1)) : ℕ :=
  (Finset.univ.filter (fun u : CubeVertex p.d =>
    (u, j) ∈ C ∧ P (u, j) = true ∧ A (u, j) = true ∧
      _root_.hammingDist u v ≤ p.r + p.D)).card

/-- Relaxed badness inside the center domain `C` with crowd threshold `t n^b`. -/
def relBadAt (p : HDParams) (C : Finset p.Loc) (t : ℝ) (P A : p.Loc → Bool)
    (E : p.EligMap) (v : CubeVertex p.d) (j : Fin (p.H + 1)) : Prop :=
  (∀ ℓ ∈ E v j, ℓ ∈ C → A ℓ = false) ∨
    t * (p.n : ℝ) ^ p.b < (relCrowd p C P A v j : ℝ)

/-- The bad predicate consulted by relaxed walks: only site-levels of the path domain `Dom`
can be bad, and levels above `H` are never bad. -/
def relBad (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p)) (t : ℝ)
    (P A : p.Loc → Bool) (E : p.EligMap) : CubeVertex p.d → ℕ → Prop :=
  fun v k => (v, k) ∈ Dom ∧ ∃ hk : k < p.H + 1, relBadAt p C t P A E v ⟨k, hk⟩

/-- Relaxed legality of `E` for a scale-`R` failure from `x`: at every site-level of `Dom`
within metric distance `2R` of `x`, the part of the eligible set inside `C` consists of
present same-level centers of the `r`-ball and has at least `sλ` members. -/
def relLegal (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p)) (s : ℝ)
    (P : p.Loc → Bool) (E : p.EligMap) (x : HDState p) (R : ℕ) : Prop :=
  ∀ (v : CubeVertex p.d) (j : Fin (p.H + 1)), (v, j.val) ∈ Dom →
    hdScaleDistance p.D x (v, j.val) < 2 * R →
      (∀ ℓ ∈ E v j, ℓ ∈ C → P ℓ = true ∧ ℓ.2 = j ∧ _root_.hammingDist ℓ.1 v ≤ p.r) ∧
      s * p.lam ≤ (((E v j).filter (fun ℓ => ℓ ∈ C)).card : ℝ)

/-- The relaxed scale-`R` failure from `x` (stopped walk with net rise at least `-ηR`). -/
def relFail (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p)) (t η : ℝ)
    (P A : p.Loc → Bool) (E : p.EligMap) (x : HDState p) (R : ℕ) : Prop :=
  hdScaleThresholdFailure (Finset.univ : p.Sites) (relBad p C Dom t P A E) x R η

open Classical in
/-- `B(P)` of TeX 03:388–392: the supremum over legal eligibility maps of the conditional
activation probability of a relaxed failure (zero when no legal map exists). -/
noncomputable def relSup (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p))
    (s t η : ℝ) (x : HDState p) (R : ℕ) (P : p.Loc → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun E : p.EligMap =>
    if relLegal p C Dom s P E x R then
      p.actLaw.pr (fun A => relFail p C Dom t η P A E x R)
    else 0)

/-- The induction claim (TeX 03:393–396) at scale index `i`, uniform in the center domain,
the path domain and the start. -/
def ScaleClaim (p : HDParams) (σ ζ a θ : ℝ) (i : ℕ) : Prop :=
  ∀ (C : Finset p.Loc) (Dom : Set (HDState p)) (x : HDState p),
    p.posLaw.expect (relSup p C Dom
      (hdScaleEligibilityFraction (hdScaleIndex p.n σ ζ) i)
      (hdScaleCrowdFraction (hdScaleIndex p.n σ ζ) i)
      (hdScaleSlope (hdScaleIndex p.n σ ζ) i) x (hdScaleRadius p.n σ i)) ≤
      Real.exp (-((p.n : ℝ) ^ a * (hdScaleRadius p.n σ i : ℝ) ^ θ))

/-- The center domain with the forced center erased (TeX 03:534–541). -/
def forcedFree (p : HDParams) (forced : Option p.Loc) : Finset p.Loc :=
  Finset.univ.filter (fun ℓ => forced ≠ some ℓ)

/-- The path domain of a queried-site set. -/
def siteDom (p : HDParams) (Sites : p.Sites) : Set (HDState p) := {y | y.1 ∈ Sites}

/-- Possible bad site-levels for a positive height reached below the base scale. -/
def baseStarts (p : HDParams) (Dom : p.Sites) (v : CubeVertex p.d) (R₀ : ℕ) :
    Finset (HDState p) :=
  ((Finset.univ : Finset (CubeVertex p.d × Fin (p.H + 1))).filter (fun y =>
    y.1 ∈ Dom ∧ hdScaleDistance p.D (v, 0) (y.1, y.2.val) < 2 * R₀)).image
      (fun y => (y.1, y.2.val))

/-- Possible level-zero starts at spatial metric distance below `R` from the query. -/
def midStarts (p : HDParams) (Dom : p.Sites) (v : CubeVertex p.d) (R : ℕ) :
    Finset (CubeVertex p.d) :=
  Dom.filter (fun u => hdScaleDistance p.D (v, 0) (u, 0) < R)

theorem posLawForced_none (p : HDParams) : p.posLawForced none = p.posLaw := by
  unfold HDParams.posLawForced HDParams.posLaw
  simp

/-! ## 3. Leaves -/

/-- Eventual numerics under the standard hypotheses (proved). -/
theorem std_eventually (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, Std J₀ b₀ b σ ζ c_d C_d D reg p → n₀ ≤ p.n →
      0 < p.D ∧ 0 < p.H ∧ 30 ≤ p.lam ∧ 4 ≤ (p.n : ℝ) ^ p.b := by
  have hJ : 0 < J₀ := by linarith [hp.hJ]
  have hb : 0 < b := by linarith [hp.hb.1, hp.hb.2.1]
  have h1 : ∀ᶠ n : ℕ in Filter.atTop, (30 : ℝ) ≤ (n : ℝ) ^ J₀ :=
    (Filter.tendsto_atTop.1 ((tendsto_rpow_atTop hJ).comp tendsto_natCast_atTop_atTop)) 30
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ b :=
    (Filter.tendsto_atTop.1 ((tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop)) 4
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨n₀, fun p hstd hn => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [hstd.hD]
    exact hp.hD
  · rw [hstd.hH, topScale_eq_hdScaleRadius]
    unfold hdScaleRadius
    exact Nat.mul_pos (pow_pos (by unfold hdScaleMultiplier; omega) _)
      (by unfold heightBaseRadius; omega)
  · rw [hstd.hlam]
    exact (hn₀ p.n hn).1
  · rw [hstd.hb]
    exact (hn₀ p.n hn).2

/-- Two Boolean product laws that agree off one coordinate give the same expectation to a
function that ignores that coordinate. -/
theorem pi_bool_expect_eq_of_eq_off {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q Q' : ι → FinProb Bool) (i₀ : ι) (hQ : ∀ i, i ≠ i₀ → Q i = Q' i)
    (f : (ι → Bool) → ℝ) (hf : ∀ ω b, f (Function.update ω i₀ b) = f ω) :
    (FinProb.pi Q).expect f = (FinProb.pi Q').expect f := by
  have key : ∀ Q : ι → FinProb Bool, (FinProb.pi Q).expect f =
      (∑ ω : ι → Bool, (∏ i ∈ Finset.univ.erase i₀, (Q i).w (ω i)) * f ω) / 2 := by
    intro Q
    let g : (ι → Bool) → ℝ := fun ω => (∏ i ∈ Finset.univ.erase i₀, (Q i).w (ω i)) * f ω
    let σ : (ι → Bool) → (ι → Bool) := fun ω => Function.update ω i₀ (!(ω i₀))
    have hσ0 : ∀ ω, σ ω i₀ = !(ω i₀) := by
      intro ω
      simp [σ]
    have hσσ : Function.Involutive σ := by
      intro ω
      funext i
      by_cases hi : i = i₀
      · subst hi
        rw [hσ0, hσ0, Bool.not_not]
      · simp [σ, Function.update_of_ne hi]
    have hgσ : ∀ ω, g (σ ω) = g ω := by
      intro ω
      simp only [g]
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        simp only [σ]
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      · exact hf ω _
    have hexp : (FinProb.pi Q).expect f = ∑ ω, (Q i₀).w (ω i₀) * g ω := by
      unfold FinProb.expect FinProb.pi
      apply Finset.sum_congr rfl
      intro ω _
      simp only [g]
      rw [← Finset.mul_prod_erase Finset.univ (fun i => (Q i).w (ω i)) (Finset.mem_univ i₀)]
      ring
    have hswap : ∑ ω, (Q i₀).w (ω i₀) * g ω = ∑ ω, (Q i₀).w (!(ω i₀)) * g ω := by
      calc
        ∑ ω, (Q i₀).w (ω i₀) * g ω = ∑ ω, (Q i₀).w (σ ω i₀) * g (σ ω) :=
          (Equiv.sum_comp (hσσ.toPerm σ) (fun ω => (Q i₀).w (ω i₀) * g ω)).symm
        _ = ∑ ω, (Q i₀).w (!(ω i₀)) * g ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [hσ0, hgσ]
    have hbool : ∀ bb : Bool, (Q i₀).w bb + (Q i₀).w (!bb) = 1 := by
      have h1 := (Q i₀).sum_eq_one
      rw [Fintype.sum_bool] at h1
      intro bb
      cases bb <;> simp <;> linarith
    have htwo : 2 * ∑ ω, (Q i₀).w (ω i₀) * g ω = ∑ ω, g ω := by
      calc
        2 * ∑ ω, (Q i₀).w (ω i₀) * g ω =
            ∑ ω, (Q i₀).w (ω i₀) * g ω + ∑ ω, (Q i₀).w (!(ω i₀)) * g ω := by
          rw [← hswap]
          ring
        _ = ∑ ω, ((Q i₀).w (ω i₀) + (Q i₀).w (!(ω i₀))) * g ω := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ω _
          ring
        _ = ∑ ω, g ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [hbool, one_mul]
    rw [hexp]
    linarith
  rw [key Q, key Q']
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [hQ i (Finset.ne_of_mem_erase hi)]

/-- Forced-center transfer, TeX 03:534–541 (proved). A function that does not read the forced
coordinate has the same expectation under the forced and the unforced position laws. -/
theorem posLawForced_expect_eq (p : HDParams) (forced : Option p.Loc)
    (f : (p.Loc → Bool) → ℝ) (hf : FinProb.DependsOn f (forcedFree p forced)) :
    (p.posLawForced forced).expect f = p.posLaw.expect f := by
  rcases forced with _ | ℓ₀
  · rw [posLawForced_none]
  · unfold HDParams.posLawForced HDParams.posLaw
    apply pi_bool_expect_eq_of_eq_off _ _ ℓ₀
    · intro i hi
      have : ¬ (some ℓ₀ = some i) := fun h => hi (Option.some_inj.mp h).symm
      simp only [this, if_false]
    · intro ω bb
      apply hf
      intro i hi
      have hne : i ≠ ℓ₀ := by
        intro h
        subst h
        simp [forcedFree] at hi
      exact Function.update_of_ne hne _ _

/-- `relSup` reads the prospective positions only inside its center domain (proved). -/
theorem relSup_dependsOn (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p))
    (s t η : ℝ) (x : HDState p) (R : ℕ) :
    FinProb.DependsOn (relSup p C Dom s t η x R) C := by
  intro P P' hPP'
  have hcrowd : ∀ A v j, relCrowd p C P A v j = relCrowd p C P' A v j := by
    intro A v j
    unfold relCrowd
    congr 1
    apply Finset.filter_congr
    intro u _
    constructor
    · rintro ⟨hC, hP, hA, hd⟩
      exact ⟨hC, by rw [← hPP' _ hC]; exact hP, hA, hd⟩
    · rintro ⟨hC, hP, hA, hd⟩
      exact ⟨hC, by rw [hPP' _ hC]; exact hP, hA, hd⟩
  have hbad : ∀ A E, relBad p C Dom t P A E = relBad p C Dom t P' A E := by
    intro A E
    funext v k
    unfold relBad relBadAt
    simp only [hcrowd]
  have hfail : ∀ A E, relFail p C Dom t η P A E x R = relFail p C Dom t η P' A E x R := by
    intro A E
    unfold relFail
    rw [hbad]
  have hlegal : ∀ E, relLegal p C Dom s P E x R ↔ relLegal p C Dom s P' E x R := by
    intro E
    unfold relLegal
    constructor
    · intro h v j hv hd
      obtain ⟨h1, h2⟩ := h v j hv hd
      exact ⟨fun ℓ hℓ hC => by rw [← hPP' ℓ hC]; exact h1 ℓ hℓ hC, h2⟩
    · intro h v j hv hd
      obtain ⟨h1, h2⟩ := h v j hv hd
      exact ⟨fun ℓ hℓ hC => by rw [hPP' ℓ hC]; exact h1 ℓ hℓ hC, h2⟩
  unfold relSup
  congr 1
  funext E
  simp only [hfail]
  by_cases hL : relLegal p C Dom s P E x R
  · rw [if_pos hL, if_pos ((hlegal E).mp hL)]
  · rw [if_neg hL, if_neg (fun h => hL ((hlegal E).mpr h))]

/-- LEAF (actual events are relaxed events, TeX 03:398–404 and 03:534–541). On legal actual
eligibility, an actual stopped-path failure is a relaxed failure with the forced center erased;
averaging the eligibility supremum dominates the joint probability. -/
theorem actual_pr_le_forced_expect (p : HDParams) (hlam : 30 ≤ p.lam)
    (hnb : 4 ≤ (p.n : ℝ) ^ p.b) (forced : Option p.Loc) (Sites : p.Sites)
    {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
    (Esel : (p.Loc → Bool) → Aux → p.EligMap) (x : HDState p) (R : ℕ) (s t η : ℝ)
    (hs : s ≤ 3 / 10) (ht : t ≤ 3 / 4) :
    (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x R η) ≤
      (p.posLawForced forced).expect
        (relSup p (forcedFree p forced) (siteDom p Sites) s t η x R) := by
  sorry

/-- LEAF (Step 2, TeX 03:406–420). Base-scale claim for every radius up to `R₀`, uniform in
the domains and the start. Adapts `height_scale_zero_relaxed_failure_bound` (helper file) to
an arbitrary start level, center domain `C`, and the eligibility supremum. -/
theorem scale_claim_base (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, Std J₀ b₀ b σ ζ c_d C_d D reg p → n₀ ≤ p.n →
      ∀ R : ℕ, 1 ≤ R → R ≤ heightBaseRadius p.n →
      ∀ s t η : ℝ, 1 / 4 ≤ s → 3 / 5 ≤ t → t ≤ 3 / 4 → η ≤ 1 / 2 →
      ∀ (C : Finset p.Loc) (Dom : Set (HDState p)) (x : HDState p),
        p.posLaw.expect (relSup p C Dom s t η x R) ≤
          Real.exp (-((p.n : ℝ) ^ a * (heightBaseRadius p.n : ℝ) ^ θ)) := by
  sorry

/-- LEAF (deterministic, TeX 03:544–553). If the global height property fails, some level-zero
start has an actual top-scale failure (paths are not spatially restricted here). -/
theorem not_goodHeights_top_failure (p : HDParams) (hD : 0 < p.D) (hH : 0 < p.H)
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap) (η : ℝ) (hη : 0 ≤ η)
    (hbad : ¬ p.GoodHeights Sites P A E) :
    ∃ u ∈ Sites, hdScaleFailure Sites P A E (u, 0) p.H η := by
  classical
  by_contra hno
  have hnone : ∀ u ∈ Sites, ¬ hdScaleFailure Sites P A E (u, 0) p.H η := by
    simpa only [not_exists, not_and] using hno
  exact hbad (Lane_sol_hs_paths.goodHeights_of_no_failure hD hη hnone)

/-- LEAF (deterministic, TeX 03:555–564). A positive long height is witnessed by a bad
site-level near the query (displacement below `R₀`), by a scale-`i` failure from a level-zero
start within `R_{i+1}` (displacement in `[R_i, R_{i+1})`), or by a top-scale failure. -/
theorem positive_height_witness (p : HDParams) (hD : 0 < p.D) (σ ζ : ℝ)
    (hH : p.H = hdScaleRadius p.n σ (hdScaleIndex p.n σ ζ))
    (Sites : p.Sites) (P A : p.Loc → Bool) (E : p.EligMap) (v : CubeVertex p.d)
    (hv : v ∈ Sites) (hpos : 0 < p.height Sites P A E p.Rlong v) :
    (∃ y ∈ baseStarts p (p.domBall Sites v p.Rlong) v (heightBaseRadius p.n),
        hdScaleFailure (p.domBall Sites v p.Rlong) P A E y 1 (1 / 2)) ∨
    (∃ i ∈ Finset.range (hdScaleIndex p.n σ ζ),
      ∃ u ∈ midStarts p (p.domBall Sites v p.Rlong) v (hdScaleRadius p.n σ (i + 1)),
        hdScaleFailure (p.domBall Sites v p.Rlong) P A E (u, 0) (hdScaleRadius p.n σ i)
          (hdScaleSlope (hdScaleIndex p.n σ ζ) i)) ∨
    (∃ u ∈ p.domBall Sites v p.Rlong,
      hdScaleFailure (p.domBall Sites v p.Rlong) P A E (u, 0)
        (hdScaleRadius p.n σ (hdScaleIndex p.n σ ζ))
        (hdScaleSlope (hdScaleIndex p.n σ ζ) (hdScaleIndex p.n σ ζ))) := by
  classical
  have hr := height_reach_at_height Sites P A E v p.Rlong hv
  obtain ⟨u, hu, ⟨path⟩⟩ := Lane_sol_hs_paths.reach_path
    (p.domBall Sites v p.Rlong)
    (fun w hw hq => Finset.mem_filter.mpr ⟨hw, hq⟩) hr
  have hfirst := Lane_sol_hs_paths.path_first_bad path hpos
  let L := hdScaleDistance p.D (v, 0) (u, 0)
  by_cases hbase : L < heightBaseRadius p.n
  · left
    refine ⟨(u, 0), ?_, Lane_sol_hs_paths.failure_one_of_bad hD hu hfirst.1 hfirst.2⟩
    unfold baseStarts
    apply Finset.mem_image.mpr
    refine ⟨(u, ⟨0, by omega⟩), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hu, ?_⟩
    change L < 2 * heightBaseRadius p.n
    have hR : 1 ≤ heightBaseRadius p.n := by unfold heightBaseRadius; omega
    omega
  · let h := hdScaleIndex p.n σ ζ
    have hfinish := Lane_sol_hs_paths.zero_distance_le_finish (p := p) u v
      (p.height Sites P A E p.Rlong v)
    by_cases htop : hdScaleRadius p.n σ h ≤ L
    · right; right
      refine ⟨u, hu, Lane_sol_hs_paths.failure_of_path path ?_ (htop.trans hfinish)⟩
      have hs := hdScaleThreshold_fractions_bounds (Nat.le_refl h)
      linarith [hs.2.2.2.2.1]
    · obtain ⟨i, hi, hlo, hhi⟩ := Lane_sol_hs_paths.scale_bracket p.n σ h L
        (by omega) (by omega)
      right; left
      refine ⟨i, Finset.mem_range.mpr hi, u, Finset.mem_filter.mpr ⟨hu, hhi⟩,
        Lane_sol_hs_paths.failure_of_path path ?_ (hlo.trans hfinish)⟩
      have hs := hdScaleThreshold_fractions_bounds (Nat.le_of_lt hi)
      linarith [hs.2.2.2.2.1]

/-- LEAF (counting). -/
theorem baseStarts_card_le (p : HDParams) (hD : 0 < p.D) (Dom : p.Sites)
    (v : CubeVertex p.d) (R₀ : ℕ) :
    ((baseStarts p Dom v R₀).card : ℝ) ≤
      ((p.H + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (2 * p.D * R₀) := by
  have hsub : baseStarts p Dom v R₀ ⊆
      (((Finset.univ : Finset (CubeVertex p.d × Fin (p.H + 1))).filter (fun y =>
        hdScaleDistance p.D (v, 0) (y.1, y.2.val) < 2 * R₀)).image (fun y => (y.1, y.2.val))) := by
    intro y hy
    simp only [baseStarts, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rcases hy with ⟨x, ⟨⟨_hxDom, hxdist⟩, rfl⟩⟩
    exact ⟨x, hxdist, rfl⟩
  have hcard := Finset.card_le_card hsub
  have hbound := Lane_g_hs_count.scale_pairs_card_le p hD (v, 0) (2 * R₀)
  have hle : (baseStarts p Dom v R₀).card ≤ (p.H + 1) * (p.d + 1) ^ (2 * p.D * R₀) := by
    have hmul : p.D * (2 * R₀) = 2 * p.D * R₀ := by ring
    rw [hmul] at hbound
    exact hcard.trans hbound
  exact_mod_cast hle

/-- LEAF (counting). -/
theorem midStarts_card_le (p : HDParams) (hD : 0 < p.D) (Dom : p.Sites)
    (v : CubeVertex p.d) (R : ℕ) :
    ((midStarts p Dom v R).card : ℝ) ≤ ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R) := by
  have hsub : midStarts p Dom v R ⊆
      Finset.univ.filter (fun u : CubeVertex p.d => _root_.hammingDist u v ≤ p.D * R) := by
    intro u hu
    simp only [midStarts, Finset.mem_filter] at hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hdist := hu.2
    have h1 := Lane_g_hs_count.hammingDist_le_of_hdScaleDistance_lt hD (v, 0) (u, 0) R hdist
    rw [_root_.hammingDist_comm] at h1
    exact h1
  have hcard := Finset.card_le_card hsub
  have hbound := Lane_g_hs_count.cube_ball_card_le_pow p.d (p.D * R) v
  have hle : (midStarts p Dom v R).card ≤ (p.d + 1) ^ (p.D * R) := hcard.trans hbound
  exact_mod_cast hle

/-- LEAF (arithmetic, TeX 03:544–547). -/
theorem global_arith (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ)) ≤
        Real.exp (-(n : ℝ) ^ (1 + c)) := by
  sorry

/-- LEAF (arithmetic, TeX 03:555–569). -/
theorem positive_arith (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      ((topScale n σ ζ + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (2 * D * heightBaseRadius n) *
          Real.exp (-((n : ℝ) ^ a * (heightBaseRadius n : ℝ) ^ θ)) +
        (∑ i ∈ Finset.range (hdScaleIndex n σ ζ),
          ((d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius n σ (i + 1)) *
            Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ i : ℝ) ^ θ)) +
        (2 : ℝ) ^ d * Real.exp (-((n : ℝ) ^ a * (topScale n σ ζ : ℝ) ^ θ))) ≤
      Real.exp (-(n : ℝ) ^ c) := by
  sorry

/-! ## 3b. The induction step (TeX 03:422–533), split and assembled -/

/-- The rectangular center domain of a child failure from `y` at radius `R`: levels within `2R`
and spatial radius `r + 2DR + D`. It contains every eligible set and crowd region consulted by
a child failure and by the child's legality region (metric distance below `2R`). -/
def childDom (p : HDParams) (y : HDState p) (R : ℕ) : Finset p.Loc :=
  Finset.univ.filter (fun ℓ => Nat.dist y.2 ℓ.2.val < 2 * R ∧
    _root_.hammingDist y.1 ℓ.1 ≤ p.r + 2 * p.D * R + p.D)

/-- The private center domain of child `y` in configuration `Y` (TeX 03:470–473). Private
domains of distinct children are disjoint by construction. -/
def privateDom (p : HDParams) (C : Finset p.Loc) (Y : Finset (HDState p))
    (y : HDState p) (R : ℕ) : Finset p.Loc :=
  (C ∩ childDom p y R).filter (fun ℓ => ∀ y' ∈ Y, y' ≠ y → ℓ ∉ childDom p y' R)

/-- The center-domain overlap of two children. -/
def overlapDom (p : HDParams) (C : Finset p.Loc) (y y' : HDState p) (R : ℕ) : Finset p.Loc :=
  C ∩ childDom p y R ∩ childDom p y' R

/-- Prospective-position overlap exception (TeX 03:475–481). -/
def posExc (p : HDParams) (C : Finset p.Loc) (Y : Finset (HDState p)) (R : ℕ) (ε : ℝ)
    (P : p.Loc → Bool) : Prop :=
  ∃ y ∈ Y, ∃ y' ∈ Y, y ≠ y' ∧
    ε * p.lam / (Y.card : ℝ) <
      (((overlapDom p C y y' R).filter (fun ℓ => P ℓ = true)).card : ℝ)

/-- Active-center overlap exception (TeX 03:475–481). -/
def actExc (p : HDParams) (C : Finset p.Loc) (Y : Finset (HDState p)) (R : ℕ) (ε : ℝ)
    (P A : p.Loc → Bool) : Prop :=
  ∃ y ∈ Y, ∃ y' ∈ Y, y ≠ y' ∧
    ε * (p.n : ℝ) ^ p.b / (Y.card : ℝ) <
      (((overlapDom p C y y' R).filter (fun ℓ => P ℓ = true ∧ A ℓ = true)).card : ℝ)

/-- Site-levels (levels at most `H`) at metric distance below `R` from `x`. -/
def scaleBall (p : HDParams) (x : HDState p) (R : ℕ) : Finset (HDState p) :=
  ((Finset.univ : Finset (CubeVertex p.d × Fin (p.H + 1))).filter (fun y =>
    hdScaleDistance p.D x (y.1, y.2.val) < R)).image (fun y => (y.1, y.2.val))

/-- Pairwise metric separation by at least `g`. -/
def Separated (p : HDParams) (g : ℕ) (Y : Finset (HDState p)) : Prop :=
  ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → g ≤ hdScaleDistance p.D y y'

open Classical in
/-- Child configurations: `q` starts in the parent ball, pairwise separated by `g`. -/
noncomputable def configs (p : HDParams) (x : HDState p) (R g q : ℕ) :
    Finset (Finset (HDState p)) :=
  (scaleBall p x R).powerset.filter (fun Y => Y.card = q ∧ Separated p g Y)

/-- The overlap loss fraction `ε`: the eligibility gap of the schedule. -/
noncomputable def stepEps (h : ℕ) : ℝ := 1 / (20 * ((h + 1 : ℕ) : ℝ))

/-- The number of children in a configuration, `q = ⌊M / (16 (h+1) (2K+1))⌋`. -/
noncomputable def stepQ (n : ℕ) (σ ζ : ℝ) (K : ℕ) : ℕ :=
  ⌊(hdScaleMultiplier n σ : ℝ) /
    (16 * ((hdScaleIndex n σ ζ + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1))⌋₊

/-- The bound used for each overlap exception at child radius `R'`. -/
noncomputable def stepExc (n : ℕ) (b σ : ℝ) (R' : ℕ) : ℝ :=
  Real.exp (-((n : ℝ) ^ (b - 2 * σ) * (R' : ℝ)))

theorem hdScaleRadius_pred (n : ℕ) (σ : ℝ) {i : ℕ} (hi : 1 ≤ i) :
    hdScaleRadius n σ i = hdScaleMultiplier n σ * hdScaleRadius n σ (i - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simpa using hdScaleRadius_succ n σ k

theorem relSup_nonneg (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p))
    (s t η : ℝ) (x : HDState p) (R : ℕ) (P : p.Loc → Bool) :
    0 ≤ relSup p C Dom s t η x R P := by
  classical
  unfold relSup
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (fun _ _ => ∅ : p.EligMap)))
  split_ifs
  · exact pr_nonneg _ _
  · exact le_rfl

/-- Bounding the eligibility supremum by a uniform bound on legal maps. -/
theorem relSup_le (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p))
    (s t η : ℝ) (x : HDState p) (R : ℕ) (P : p.Loc → Bool) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ E : p.EligMap, relLegal p C Dom s P E x R →
      p.actLaw.pr (fun A => relFail p C Dom t η P A E x R) ≤ c) :
    relSup p C Dom s t η x R P ≤ c := by
  classical
  unfold relSup
  apply Finset.sup'_le
  intro E _
  split_ifs with hleg
  · exact h E hleg
  · exact hc

/-- A legal map's failure probability is at most the supremum. -/
theorem le_relSup (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p))
    (s t η : ℝ) (x : HDState p) (R : ℕ) (P : p.Loc → Bool) (E : p.EligMap)
    (hE : relLegal p C Dom s P E x R) :
    p.actLaw.pr (fun A => relFail p C Dom t η P A E x R) ≤ relSup p C Dom s t η x R P := by
  classical
  unfold relSup
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ E))
  rw [if_pos hE]

theorem expect_nonneg {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ P.expect f := by
  unfold FinProb.expect
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (P.nonneg ω) (hf ω))

theorem expect_add {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f g : Ω → ℝ) :
    P.expect (fun ω => f ω + g ω) = P.expect f + P.expect g := by
  unfold FinProb.expect
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

theorem expect_indicator {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop)
    [DecidablePred A] : P.expect (fun ω => if A ω then (1 : ℝ) else 0) = P.pr A := by
  classical
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : A ω <;> simp [h]

theorem expect_section_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (F : α → β → Prop) :
    P.expect (fun a => Q.pr (F a)) = (P.prod Q).pr (fun ab => F ab.1 ab.2) := by
  rw [prod_pr_eq_sections]
  rfl

/-- The schedule gaps used by one step (proved). -/
theorem schedule_gaps {h i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    hdScaleEligibilityFraction h (i - 1) + stepEps h ≤ hdScaleEligibilityFraction h i ∧
    hdScaleCrowdFraction h (i - 1) + stepEps h ≤ hdScaleCrowdFraction h i ∧
    0 ≤ hdScaleSlope h i ∧ hdScaleSlope h i < hdScaleSlope h (i - 1) ∧ 0 ≤ stepEps h := by
  have hb := hdScaleThreshold_fractions_bounds hih
  have hs := hdScaleThreshold_fractions_strict hih (by omega)
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub hi1]
    simp
  have hcast2 : ((i - 1 + 1 : ℕ) : ℝ) = (i : ℝ) := by
    rw [Nat.sub_add_cancel hi1]
  have hden : (0 : ℝ) < ((h + 1 : ℕ) : ℝ) := by positivity
  refine ⟨?_, ?_, le_trans (by norm_num) hb.2.2.2.2.1, hs.2.2, ?_⟩
  · unfold hdScaleEligibilityFraction stepEps
    rw [hcast]
    have e : (i : ℝ) / (20 * ((h + 1 : ℕ) : ℝ)) =
        ((i : ℝ) - 1) / (20 * ((h + 1 : ℕ) : ℝ)) + 1 / (20 * ((h + 1 : ℕ) : ℝ)) := by
      rw [← add_div, sub_add_cancel]
    linarith
  · unfold hdScaleCrowdFraction stepEps
    rw [hcast2]
    have e1 : (3 / 20 : ℝ) * ((i + 1 : ℕ) : ℝ) / ((h + 1 : ℕ) : ℝ) =
        (3 / 20 : ℝ) * (i : ℝ) / ((h + 1 : ℕ) : ℝ) + (3 / 20) / ((h + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have e2 : 1 / (20 * ((h + 1 : ℕ) : ℝ)) ≤ (3 / 20) / ((h + 1 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hden]
      nlinarith
    linarith
  · unfold stepEps
    positivity

/-- LEAF (deterministic, TeX 03:425–447). A relaxed parent failure contains `q` separated
child failures with the parent's bad statuses. The helper file proves the core as
`hdParentFailure_has_many_separated_child_failure_starts` (with `K_L = 2K+1`, `δ = q/M`);
what remains is to read chunk failures as `relFail` and place the chunk starts in the ball. -/
theorem parent_fail_children (p : HDParams) (hD : 0 < p.D) (C : Finset p.Loc)
    (Dom : Set (HDState p)) (t ηP ηC : ℝ) (P A : p.Loc → Bool) (E : p.EligMap)
    (x : HDState p) (R' M K q : ℕ) (hM : 2 ≤ M) (hR' : 0 < R') (hK : 1 ≤ K)
    (hηP : 0 ≤ ηP) (hηPC : ηP < ηC)
    (hlarge : (1 + ηC) * (2 * (K : ℝ) + 1) * (q : ℝ) + (1 + ηC) < (ηC - ηP) * (M : ℝ))
    (hfail : relFail p C Dom t ηP P A E x (M * R')) :
    ∃ Y ∈ configs p x (M * R') (K * R') q, ∀ y ∈ Y, relFail p C Dom t ηC P A E y R' := by
  sorry

/-- LEAF (Step 4 transfer and activation independence, TeX 03:483–512). For fixed positions and
a fixed parent-legal eligibility map, outside the position exception: every child failure with
the parent's statuses is, outside the activation exception, a failure in its private domain at
the child thresholds, the private failures depend on disjoint activations (use `xFinner` with
`d = 1` on `actLaw`), and each is bounded by its private supremum. -/
theorem config_activation_bound (p : HDParams) (hD : 0 < p.D) (hlam : 0 ≤ p.lam)
    (C : Finset p.Loc) (Dom : Set (HDState p)) (sP sC tP tC η ε : ℝ)
    (P : p.Loc → Bool) (E : p.EligMap) (x : HDState p) (R' M g q : ℕ) (hM : 2 ≤ M)
    (hε : 0 ≤ ε) (hs : sC + ε ≤ sP) (ht : tC + ε ≤ tP)
    (Y : Finset (HDState p)) (hY : Y ∈ configs p x (M * R') g q)
    (hlegal : relLegal p C Dom sP P E x (M * R'))
    (hpos : ¬ posExc p C Y R' ε P) :
    p.actLaw.pr (fun A => ∀ y ∈ Y, relFail p C Dom tP η P A E y R') ≤
      p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
        ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC η y R' P := by
  classical
  have hCsub (y : HDState p) : privateDom p C Y y R' ⊆ C := by
    intro ℓ hℓ
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hℓ).1).1
  have hYball : Y ⊆ scaleBall p x (M * R') :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hY).1
  have hyDist (y : HDState p) (hy : y ∈ Y) : hdScaleDistance p.D x y < M * R' := by
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp (hYball hy)
    have hz' := (Finset.mem_filter.mp hz).2
    simpa [hzy] using hz'
  have hparent (y : HDState p) (hy : y ∈ Y) (v : CubeVertex p.d)
      (j : Fin (p.H + 1)) (hd : hdScaleDistance p.D y (v, j.val) < 2 * R') :
      hdScaleDistance p.D x (v, j.val) < 2 * (M * R') := by
    have htri := hdScaleDistance_triangle hD x y (v, j.val)
    have hm := Nat.mul_le_mul_right R' hM
    have hxy := hyDist y hy
    omega
  have hchild (y : HDState p) (v : CubeVertex p.d) (j : Fin (p.H + 1))
      (hd : hdScaleDistance p.D y (v, j.val) < 2 * R')
      (ℓ : p.Loc) (hj : ℓ.2 = j) (hs : _root_.hammingDist ℓ.1 v ≤ p.r + p.D) :
      ℓ ∈ childDom p y R' := by
    have hlev : Nat.dist y.2 ℓ.2.val < 2 * R' := by
      rw [hj]
      exact lt_of_le_of_lt (Nat.le_max_left _ _) hd
    have hspace := hdScaleDistance_hamming_bound hD hd
    have hham : _root_.hammingDist y.1 ℓ.1 ≤ p.r + 2 * p.D * R' + p.D := by
      calc
        _ ≤ _root_.hammingDist y.1 v + _root_.hammingDist v ℓ.1 :=
          _root_.hammingDist_triangle _ _ _
        _ ≤ p.D * (2 * R') + (p.r + p.D) :=
          Nat.add_le_add hspace (by simpa [_root_.hammingDist_comm] using hs)
        _ = _ := by ring
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlev, hham⟩
  have hposPair (y : HDState p) (hy : y ∈ Y) (z : HDState p) (hz : z ∈ Y)
      (hne : y ≠ z) :
      (((overlapDom p C y z R').filter (fun ℓ => P ℓ = true)).card : ℝ) ≤
        ε * p.lam / Y.card := by
    exact le_of_not_gt (fun h => hpos ⟨y, hy, z, hz, hne, h⟩)
  have hlegChild (y : HDState p) (hy : y ∈ Y) :
      relLegal p (privateDom p C Y y R') Dom sC P E y R' := by
    intro v j hdom hd
    obtain ⟨hEv, hEc⟩ := hlegal v j hdom (hparent y hy v j hd)
    constructor
    · intro ℓ hℓ hpriv
      exact hEv ℓ hℓ (hCsub y hpriv)
    · let F := (E v j).filter (fun ℓ => ℓ ∈ C)
      have hF : ∀ ℓ ∈ F, ℓ ∈ C ∧ ℓ ∈ childDom p y R' ∧ P ℓ = true := by
        intro ℓ hℓ
        obtain ⟨hEℓ, hCℓ⟩ := Finset.mem_filter.mp hℓ
        obtain ⟨hPℓ, hjℓ, hrℓ⟩ := hEv ℓ hEℓ hCℓ
        exact ⟨hCℓ, hchild y v j hd ℓ hjℓ (by omega), hPℓ⟩
      have hloss := Lane_sol_hs_act.private_loss C F (fun z => childDom p z R') Y y hy
        (fun ℓ => P ℓ = true) (ε * p.lam) (mul_nonneg hε hlam) hF (hposPair y hy)
      have hsub : F.filter (fun ℓ => ∀ z ∈ Y, z ≠ y → ℓ ∉ childDom p z R') ⊆
          (E v j).filter (fun ℓ => ℓ ∈ privateDom p C Y y R') := by
        intro ℓ hℓ
        obtain ⟨hFℓ, hprivate⟩ := Finset.mem_filter.mp hℓ
        obtain ⟨hCℓ, hchildℓ, hPℓ⟩ := hF ℓ hFℓ
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hFℓ).1,
          Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hCℓ, hchildℓ⟩, hprivate⟩⟩
      have hcard : ((F.filter (fun ℓ => ∀ z ∈ Y, z ≠ y → ℓ ∉ childDom p z R')).card : ℝ) ≤
          (((E v j).filter (fun ℓ => ℓ ∈ privateDom p C Y y R')).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hgap := mul_le_mul_of_nonneg_right hs hlam
      change sP * p.lam ≤ (F.card : ℝ) at hEc
      nlinarith
  have hcrowdIds (B : Finset p.Loc) (A : p.Loc → Bool) (v : CubeVertex p.d)
      (j : Fin (p.H + 1)) :
      relCrowd p B P A v j =
        (B.filter (fun ℓ => ℓ.2 = j ∧ P ℓ = true ∧ A ℓ = true ∧
          _root_.hammingDist ℓ.1 v ≤ p.r + p.D)).card := by
    unfold relCrowd
    apply Finset.card_bij (fun u _ => (u, j))
    · intro u hu
      obtain ⟨hB, hP, hA, hd⟩ := (Finset.mem_filter.mp hu).2
      exact Finset.mem_filter.mpr ⟨hB, rfl, hP, hA, hd⟩
    · intro u hu u' hu' heq
      exact congrArg Prod.fst heq
    · intro ℓ hℓ
      obtain ⟨hB, hj, hP, hA, hd⟩ := Finset.mem_filter.mp hℓ
      have heq : (ℓ.1, j) = ℓ := Prod.ext rfl hj.symm
      refine ⟨ℓ.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
      change (ℓ.1, j) ∈ B ∧ P (ℓ.1, j) = true ∧ A (ℓ.1, j) = true ∧
        _root_.hammingDist ℓ.1 v ≤ p.r + p.D
      rw [heq]
      exact ⟨hB, hP, hA, hd⟩
  have htransfer (A : p.Loc → Bool) (hact : ¬ actExc p C Y R' ε P A)
      (y : HDState p) (hy : y ∈ Y) :
      relFail p C Dom tP η P A E y R' →
        relFail p (privateDom p C Y y R') Dom tC η P A E y R' := by
    apply Lane_sol_hs_act.failure_mono
    intro v k hd hbad
    obtain ⟨hdom, hk, hb⟩ := hbad
    let j : Fin (p.H + 1) := ⟨k, hk⟩
    refine ⟨hdom, hk, ?_⟩
    rcases hb with habs | hcrowd
    · left
      intro ℓ hℓ hpriv
      exact habs ℓ hℓ (hCsub y hpriv)
    · right
      have hd2 : hdScaleDistance p.D y (v, j.val) < 2 * R' := by
        dsimp [j]
        omega
      let F := C.filter (fun ℓ => ℓ.2 = j ∧ P ℓ = true ∧ A ℓ = true ∧
        _root_.hammingDist ℓ.1 v ≤ p.r + p.D)
      have hF : ∀ ℓ ∈ F, ℓ ∈ C ∧ ℓ ∈ childDom p y R' ∧ (P ℓ = true ∧ A ℓ = true) := by
        intro ℓ hℓ
        obtain ⟨hCℓ, hjℓ, hPℓ, hAℓ, hrℓ⟩ := Finset.mem_filter.mp hℓ
        exact ⟨hCℓ, hchild y v j hd2 ℓ hjℓ hrℓ, hPℓ, hAℓ⟩
      have hov (z : HDState p) (hz : z ∈ Y) (hne : y ≠ z) :
          (((C ∩ childDom p y R' ∩ childDom p z R').filter
            (fun ℓ => P ℓ = true ∧ A ℓ = true)).card : ℝ) ≤
            ε * (p.n : ℝ) ^ p.b / Y.card :=
        le_of_not_gt (fun h => hact ⟨y, hy, z, hz, hne, h⟩)
      have hloss := Lane_sol_hs_act.private_loss C F (fun z => childDom p z R') Y y hy
        (fun ℓ => P ℓ = true ∧ A ℓ = true) (ε * (p.n : ℝ) ^ p.b)
        (mul_nonneg hε (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hF hov
      have hsub : F.filter (fun ℓ => ∀ z ∈ Y, z ≠ y → ℓ ∉ childDom p z R') ⊆
          (privateDom p C Y y R').filter (fun ℓ => ℓ.2 = j ∧ P ℓ = true ∧
            A ℓ = true ∧ _root_.hammingDist ℓ.1 v ≤ p.r + p.D) := by
        intro ℓ hℓ
        obtain ⟨hFℓ, hprivate⟩ := Finset.mem_filter.mp hℓ
        obtain ⟨hCℓ, hchildℓ, hPAℓ⟩ := hF ℓ hFℓ
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hCℓ, hchildℓ⟩, hprivate⟩,
            (Finset.mem_filter.mp hFℓ).2⟩
      have hcard : ((F.filter (fun ℓ => ∀ z ∈ Y, z ≠ y → ℓ ∉ childDom p z R')).card : ℝ) ≤
          (relCrowd p (privateDom p C Y y R') P A v j : ℝ) := by
        rw [hcrowdIds]
        exact_mod_cast Finset.card_le_card hsub
      have hgap := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (Nat.cast_nonneg p.n) p.b)
      change tP * (p.n : ℝ) ^ p.b < (relCrowd p C P A v j : ℝ) at hcrowd
      rw [hcrowdIds] at hcrowd
      change tP * (p.n : ℝ) ^ p.b < (F.card : ℝ) at hcrowd
      change tC * (p.n : ℝ) ^ p.b < (relCrowd p (privateDom p C Y y R') P A v j : ℝ)
      nlinarith
  have hdisj : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z →
      Disjoint (privateDom p C Y y R') (privateDom p C Y z R') := by
    intro y hy z hz hne
    apply Finset.disjoint_left.mpr
    intro ℓ hℓy hℓz
    exact (Finset.mem_filter.mp hℓy).2 z hz hne.symm
      (Finset.mem_inter.mp (Finset.mem_filter.mp hℓz).1).2
  have hscope (y : HDState p) : FinProb.DependsOn
      (fun A => relFail p (privateDom p C Y y R') Dom tC η P A E y R')
      (privateDom p C Y y R') := by
    intro A A' hAA'
    let B := privateDom p C Y y R'
    have hc (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
        relCrowd p B P A v j = relCrowd p B P A' v j := by
      unfold relCrowd
      congr 1
      apply Finset.filter_congr
      intro u _
      constructor
      · rintro ⟨hB, hP, hA, hd⟩
        exact ⟨hB, hP, by rw [← hAA' _ hB]; exact hA, hd⟩
      · rintro ⟨hB, hP, hA, hd⟩
        exact ⟨hB, hP, by rw [hAA' _ hB]; exact hA, hd⟩
    have hb (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
        relBadAt p B tC P A E v j = relBadAt p B tC P A' E v j := by
      apply propext
      unfold relBadAt
      rw [hc]
      apply or_congr _ Iff.rfl
      constructor
      · intro h ℓ hE hB
        rw [← hAA' ℓ hB]
        exact h ℓ hE hB
      · intro h ℓ hE hB
        rw [hAA' ℓ hB]
        exact h ℓ hE hB
    have hb' : relBad p B Dom tC P A E = relBad p B Dom tC P A' E := by
      funext v k
      simp only [relBad, hb]
    change relFail p B Dom tC η P A E y R' = relFail p B Dom tC η P A' E y R'
    unfold relFail
    rw [hb']
  have hfactor : p.actLaw.pr (fun A => ∀ y ∈ Y,
      relFail p (privateDom p C Y y R') Dom tC η P A E y R') =
      ∏ y ∈ Y, p.actLaw.pr (fun A =>
        relFail p (privateDom p C Y y R') Dom tC η P A E y R') :=
    Lane_sol_hs_act.pr_all_disjoint
      (fun _ : p.Loc => FinProb.bernoulli ((p.n : ℝ) ^ p.b₀ / p.lam)) Y
      (fun y => privateDom p C Y y R')
      (fun y A => relFail p (privateDom p C Y y R') Dom tC η P A E y R') hdisj
      (fun y _ => hscope y)
  calc
    p.actLaw.pr (fun A => ∀ y ∈ Y, relFail p C Dom tP η P A E y R')
        ≤ p.actLaw.pr (fun A => actExc p C Y R' ε P A ∨
          ∀ y ∈ Y, relFail p (privateDom p C Y y R') Dom tC η P A E y R') := by
          apply pr_mono
          intro A hfail
          by_cases hact : actExc p C Y R' ε P A
          · exact Or.inl hact
          · exact Or.inr (fun y hy => htransfer A hact y hy (hfail y hy))
    _ ≤ p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
          p.actLaw.pr (fun A => ∀ y ∈ Y,
            relFail p (privateDom p C Y y R') Dom tC η P A E y R') := pr_or_le _ _ _
    _ = p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
          ∏ y ∈ Y, p.actLaw.pr (fun A =>
            relFail p (privateDom p C Y y R') Dom tC η P A E y R') := by rw [hfactor]
    _ ≤ p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
          ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC η y R' P := by
          apply add_le_add le_rfl
          apply Finset.prod_le_prod₀
          · intro y hy
            exact pr_nonneg _ _
          · intro y hy
            exact le_relSup _ _ _ _ _ _ _ _ _ _ (hlegChild y hy)

/-- Private suprema factor under the position law (TeX 03:508–512): proved from `xFinner`
(`d = 1`), `relSup_dependsOn`, and disjointness of private domains. -/
theorem private_factorization (p : HDParams) (C : Finset p.Loc) (Dom : Set (HDState p))
    (s t η : ℝ) (Y : Finset (HDState p)) (R' : ℕ) :
    p.posLaw.expect (fun P => ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom s t η y R' P) ≤
      ∏ y ∈ Y, p.posLaw.expect (relSup p (privateDom p C Y y R') Dom s t η y R') := by
  have hdeg : ∀ ℓ : p.Loc,
      (Finset.univ.filter (fun b : Y => ℓ ∈ privateDom p C Y b.1 R')).card ≤ 1 := by
    intro ℓ
    apply Finset.card_le_one.mpr
    intro b₁ hb₁ b₂ hb₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
    by_contra hne
    have hne' : b₂.1 ≠ b₁.1 := fun h => hne (Subtype.ext h.symm)
    unfold privateDom at hb₁ hb₂
    have h1 := (Finset.mem_filter.mp hb₁).2 b₂.1 b₂.2 hne'
    have h2 := (Finset.mem_inter.mp (Finset.mem_filter.mp hb₂).1).2
    exact h1 h2
  have key := xFinner (fun _ : p.Loc => FinProb.bernoulli (p.lam / (p.V : ℝ)))
    (fun b : Y => privateDom p C Y b.1 R') 1 one_pos hdeg
    (fun b P => relSup p (privateDom p C Y b.1 R') Dom s t η b.1 R' P)
    (fun b P => relSup_nonneg _ _ _ _ _ _ _ _ _)
    (fun b => relSup_dependsOn _ _ _ _ _ _ _ _)
  simp only [pow_one, Nat.cast_one, inv_one, Real.rpow_eq_pow, Real.rpow_one] at key
  have hL : (fun P => ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom s t η y R' P) =
      (fun P => ∏ b : Y, relSup p (privateDom p C Y b.1 R') Dom s t η b.1 R' P) := by
    funext P
    exact (Finset.prod_coe_sort Y
      (fun y => relSup p (privateDom p C Y y R') Dom s t η y R' P)).symm
  have hR : ∏ y ∈ Y, p.posLaw.expect (relSup p (privateDom p C Y y R') Dom s t η y R') =
      ∏ b : Y, p.posLaw.expect (relSup p (privateDom p C Y b.1 R') Dom s t η b.1 R') :=
    (Finset.prod_coe_sort Y
      (fun y => p.posLaw.expect (relSup p (privateDom p C Y y R') Dom s t η y R'))).symm
  rw [hL, hR]
  exact key

/-- LEAF (Step 3 geometry and Step 4 count tails, TeX 03:449–481). For a fixed large
separation multiple `K` (depending on the regime), every overlap exception of a separated
configuration is exponentially rare. Inputs in the helper file: the child-domain overlap
volume bounds `hdChildCenterDomain_overlap_*_bound_of_sep_scale` and the region-count tails
`position_overlap_union_bound_of_volume` / `active_overlap_union_bound_of_volume` (these are
`private` there and must be made public, or re-proved here, for this file to use them). -/
theorem overlap_bounds (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ n₀ : ℕ, ∀ p : HDParams, Std J₀ b₀ b σ ζ c_d C_d D reg p → n₀ ≤ p.n →
      ∀ i : ℕ, 1 ≤ i → i ≤ hdScaleIndex p.n σ ζ →
      ∀ (C : Finset p.Loc) (x : HDState p) (Y : Finset (HDState p)),
        Y ∈ configs p x (hdScaleMultiplier p.n σ * hdScaleRadius p.n σ (i - 1))
          (K * hdScaleRadius p.n σ (i - 1)) (stepQ p.n σ ζ K) →
        p.posLaw.pr (posExc p C Y (hdScaleRadius p.n σ (i - 1))
            (stepEps (hdScaleIndex p.n σ ζ))) ≤
          stepExc p.n b σ (hdScaleRadius p.n σ (i - 1)) ∧
        (p.posLaw.prod p.actLaw).pr (fun ω => actExc p C Y (hdScaleRadius p.n σ (i - 1))
            (stepEps (hdScaleIndex p.n σ ζ)) ω.1 ω.2) ≤
          stepExc p.n b σ (hdScaleRadius p.n σ (i - 1)) := by
  classical
  have hJ : 0 < J₀ := by linarith [hp.hJ]
  have hσ : 0 < σ ∧ σ < 1 := ⟨hp.hsz.1, lt_trans hp.hsz.2.1 hp.hsz.2.2.1⟩
  have hbJ : b ≤ J₀ := by linarith [hp.hb.2.2, hp.hJ]
  have hb₀J : b₀ ≤ J₀ := by linarith [hp.hb.2.1, hp.hb.2.2, hp.hJ]
  have hbσ : 0 ≤ b - 2 * σ := by
    linarith [hp.ha.1, hp.ha.2.2, hp.hsz.1, hp.hsz.2.1, hp.hsz.2.2.2.2]
  obtain ⟨K, hK, NV, hvol⟩ :=
    Lane_sol_hs_ovl.volume_decay_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨NL, hlamVol⟩ :=
    height_volume_ge_lambda_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨NT, htail⟩ :=
    Lane_sol_hs_ovl.tail_environment_eventually J₀ b₀ b σ hJ hσ hbJ hb₀J hbσ
  refine ⟨K, hK, max 2 (max NV (max NL NT)), ?_⟩
  intro p hpstd hn i hi1 hih C x Y hY
  let h := hdScaleIndex p.n σ ζ
  let R := hdScaleRadius p.n σ (i - 1)
  let q := stepQ p.n σ ζ K
  let e := (p.n : ℝ) ^ (b - 2 * σ)
  have hcfg := (Finset.mem_filter.mp hY).2
  have hYcard : Y.card = q := hcfg.1
  by_cases hqzero : q = 0
  · have hYempty : Y = ∅ := Finset.card_eq_zero.mp (hYcard.trans hqzero)
    constructor <;> simp [hYempty, posExc, actExc, FinProb.pr, stepExc, Real.exp_nonneg]
  have hq : 0 < q := by omega
  have hqbound : (q : ℝ) ≤ (hdScaleMultiplier p.n σ : ℝ) /
      (16 * ((h + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1)) := by
    dsimp [q, stepQ, h]
    exact Nat.floor_le (by positivity)
  obtain ⟨he1, hmeanP, hmeanA, hτP, hτA, hpair⟩ :=
    htail p.n (by omega) (i - 1) h K q hK hq hqbound
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hn2 : 2 ≤ p.n := by omega
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
  have hlam : 0 < p.lam := by rw [hpstd.hlam]; exact Real.rpow_pos_of_pos hnpos _
  have hlV : p.lam ≤ (p.V : ℝ) :=
    hlamVol p hpstd.hD hpstd.hlam (by omega) hpstd.hdlo hpstd.hreg
  have hV : 0 < (p.V : ℝ) := hlam.trans_le hlV
  have hP1 : p.lam / (p.V : ℝ) ≤ 1 := (div_le_one hV).2 hlV
  have hA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1 := by
    apply (div_le_one hlam).2
    rw [hpstd.hb₀, hpstd.hlam]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hb₀J
  let I := (Y ×ˢ Y).filter (fun yy => yy.1 ≠ yy.2)
  let T := fun yy : HDState p × HDState p => overlapDom p C yy.1 yy.2 R
  have hchild : ∀ y : HDState p, childDom p y R = hdChildCenterDomain y (2 * R) := by
    intro y
    ext ℓ
    simp [childDom, hdChildCenterDomain, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  have hvolT : ∀ yy ∈ I, ((T yy).card : ℝ) ≤ (p.V : ℝ) * Real.exp (-4 * (R : ℝ)) := by
    intro yy hyy
    obtain ⟨hyyY, hne⟩ := Finset.mem_filter.mp hyy
    obtain ⟨hy, hy'⟩ := Finset.mem_product.mp hyyY
    have hsep := hcfg.2 yy.1 hy yy.2 hy' hne
    have hv := hvol p hpstd.hD hpstd.hdlo hpstd.hdhi hpstd.hreg (by omega)
      (i - 1) (by omega) yy.1 yy.2 hsep
    have hsub : T yy ⊆ childDom p yy.1 R ∩ childDom p yy.2 R := by
      intro ℓ hℓ
      obtain ⟨hℓ₁, hℓ₂⟩ := Finset.mem_inter.mp hℓ
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hℓ₁).2, hℓ₂⟩
    calc
      _ ≤ ((childDom p yy.1 R ∩ childDom p yy.2 R).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ _ := by simpa [hchild, R] using hv
  have hcardNat : I.card ≤ q * q := by
    calc
      _ ≤ (Y ×ˢ Y).card := Finset.card_filter_le _ _
      _ = q * q := by rw [Finset.card_product, hYcard]
  have hcard : (I.card : ℝ) ≤ Real.exp (e * (R : ℝ)) := by
    calc
      _ ≤ (q : ℝ) ^ 2 := by exact_mod_cast (by simpa [pow_two] using hcardNat : I.card ≤ q ^ 2)
      _ ≤ _ := hpair
  constructor
  · calc
      _ ≤ p.posLaw.pr (fun P => ∃ yy ∈ I,
          stepEps h * p.lam / (q : ℝ) < (((T yy).filter (fun ℓ => P ℓ = true)).card : ℝ)) := by
        apply pr_mono
        intro P hP
        obtain ⟨y, hy, y', hy', hne, hcount⟩ := hP
        refine ⟨(y, y'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hy'⟩, hne⟩, ?_⟩
        simpa [T, hYcard] using hcount
      _ ≤ _ := Lane_sol_hs_ovl.position_regions_tail I T (stepEps h * p.lam / (q : ℝ)) e R
        hV hlam.le hP1 he (by simpa [stepEps, hpstd.hlam] using hτP)
        (by simpa [hpstd.hlam, R] using hmeanP) hcard hvolT
  · calc
      _ ≤ (p.posLaw.prod p.actLaw).pr (fun ω => ∃ yy ∈ I,
          stepEps h * (p.n : ℝ) ^ p.b / (q : ℝ) <
            (((T yy).filter (fun ℓ => ω.1 ℓ = true ∧ ω.2 ℓ = true)).card : ℝ)) := by
        apply pr_mono
        intro ω hω
        obtain ⟨y, hy, y', hy', hne, hcount⟩ := hω
        refine ⟨(y, y'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hy'⟩, hne⟩, ?_⟩
        simpa [T, hYcard] using hcount
      _ ≤ _ := Lane_sol_hs_ovl.active_regions_tail I T
        (stepEps h * (p.n : ℝ) ^ p.b / (q : ℝ)) e R hV hlam hP1 hA1 he
        (by simpa [stepEps, hpstd.hb] using hτA)
        (by simpa [hpstd.hb₀, R] using hmeanA) hcard hvolT

/-- LEAF (counting). -/
theorem configs_card_le (p : HDParams) (hD : 0 < p.D) (x : HDState p) (R g q : ℕ) :
    ((configs p x R g q).card : ℝ) ≤
      (((p.H + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * R)) ^ q := by
  classical
  have hpow := Lane_g_hs_count.powerset_filter_card_le_pow (scaleBall p x R) q (Separated p g)
  have hball : (scaleBall p x R).card ≤ (p.H + 1) * (p.d + 1) ^ (p.D * R) :=
    Lane_g_hs_count.scale_pairs_card_le p hD x R
  have hle : (configs p x R g q).card ≤ ((p.H + 1) * (p.d + 1) ^ (p.D * R)) ^ q := by
    unfold configs
    exact hpow.trans (Nat.pow_le_pow_left hball q)
  exact_mod_cast hle

/-- LEAF (arithmetic, TeX 03:517–533): configuration count times the accumulated error is below
the parent target. -/
theorem step_arith (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (K : ℕ) (hK : 1 ≤ K) :
    ∃ n₀ : ℕ, ∀ n d : ℕ, n₀ ≤ n → (d : ℝ) ≤ C_d * n →
      ∀ i : ℕ, 1 ≤ i → i ≤ hdScaleIndex n σ ζ →
        (((topScale n σ ζ + 1 : ℕ) : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ (D * (hdScaleMultiplier n σ * hdScaleRadius n σ (i - 1)))) ^
            (stepQ n σ ζ K) *
          (stepExc n b σ (hdScaleRadius n σ (i - 1)) +
            stepExc n b σ (hdScaleRadius n σ (i - 1)) +
            Real.exp (-((n : ℝ) ^ a * (hdScaleRadius n σ (i - 1) : ℝ) ^ θ)) ^
              (stepQ n σ ζ K)) ≤
        Real.exp (-((n : ℝ) ^ a *
          ((hdScaleMultiplier n σ * hdScaleRadius n σ (i - 1) : ℕ) : ℝ) ^ θ)) := by
  sorry

/-- LEAF (arithmetic): the separated-children count condition of `parent_fail_children`. -/
theorem step_large (σ ζ : ℝ) (hσ : 0 < σ) (hζ : 0 < ζ ∧ ζ < 1) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ i : ℕ, 1 ≤ i → i ≤ hdScaleIndex n σ ζ →
      (1 + hdScaleSlope (hdScaleIndex n σ ζ) (i - 1)) * (2 * (K : ℝ) + 1) *
            (stepQ n σ ζ K : ℝ) +
          (1 + hdScaleSlope (hdScaleIndex n σ ζ) (i - 1)) <
        (hdScaleSlope (hdScaleIndex n σ ζ) (i - 1) - hdScaleSlope (hdScaleIndex n σ ζ) i) *
          (hdScaleMultiplier n σ : ℝ) := by
  sorry

open Classical in
/-- One scale of the induction (Steps 3–4), assembled from the leaves above. -/
theorem scale_claim_step (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, Std J₀ b₀ b σ ζ c_d C_d D reg p → n₀ ≤ p.n →
      ∀ i : ℕ, 1 ≤ i → i ≤ hdScaleIndex p.n σ ζ →
        ScaleClaim p σ ζ a θ (i - 1) → ScaleClaim p σ ζ a θ i := by
  obtain ⟨K, hK, nG, hG⟩ := overlap_bounds J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nA, hA⟩ := step_arith J₀ b₀ b σ ζ θ a c_d C_d D hp K hK
  obtain ⟨nL, hL⟩ := step_large σ ζ hp.hsz.1
    ⟨lt_trans hp.hsz.1 hp.hsz.2.1, hp.hsz.2.2.1⟩ K
  obtain ⟨nE, hE⟩ := std_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  refine ⟨max (max nG nA) (max nL nE), ?_⟩
  intro p hstd hn i hi1 hih hIH C Dom x
  have hnG : nG ≤ p.n := le_of_max_le_left (le_of_max_le_left hn)
  have hnA : nA ≤ p.n := le_of_max_le_right (le_of_max_le_left hn)
  have hnL : nL ≤ p.n := le_of_max_le_left (le_of_max_le_right hn)
  have hnE : nE ≤ p.n := le_of_max_le_right (le_of_max_le_right hn)
  obtain ⟨hD0, _, hlam30, _⟩ := hE p hstd hnE
  have hlam0 : 0 ≤ p.lam := le_trans (by norm_num) hlam30
  rw [hdScaleRadius_pred p.n σ hi1]
  obtain ⟨hsgap, htgap, hηP0, hηPC, hε0⟩ :=
    schedule_gaps (h := hdScaleIndex p.n σ ζ) hi1 hih
  set h := hdScaleIndex p.n σ ζ with hh
  set R' := hdScaleRadius p.n σ (i - 1) with hR'
  set M := hdScaleMultiplier p.n σ with hM
  set q := stepQ p.n σ ζ K with hq
  set ε := stepEps h with hε
  set sP := hdScaleEligibilityFraction h i with hsP
  set sC := hdScaleEligibilityFraction h (i - 1) with hsC
  set tP := hdScaleCrowdFraction h i with htP
  set tC := hdScaleCrowdFraction h (i - 1) with htC
  set ηP := hdScaleSlope h i with hηP
  set ηC := hdScaleSlope h (i - 1) with hηC
  set β := Real.exp (-((p.n : ℝ) ^ a * (R' : ℝ) ^ θ)) with hβ
  set cfg := configs p x (M * R') (K * R') q with hcfg
  have hM2 : 2 ≤ M := le_max_left 2 _
  have hR'pos : 0 < R' := by
    rw [hR']
    unfold hdScaleRadius
    exact Nat.mul_pos (pow_pos (by unfold hdScaleMultiplier; omega) _)
      (by unfold heightBaseRadius; omega)
  have hlarge := hL p.n hnL i hi1 hih
  -- the per-position bound, uniform in the eligibility map
  have hpt : ∀ P : p.Loc → Bool, relSup p C Dom sP tP ηP x (M * R') P ≤
      ∑ Y ∈ cfg, ((if posExc p C Y R' ε P then (1 : ℝ) else 0) +
        p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
        ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P) := by
    intro P
    have hterm_nonneg : ∀ Y ∈ cfg, (0 : ℝ) ≤
        (if posExc p C Y R' ε P then (1 : ℝ) else 0) +
          p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
          ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P := by
      intro Y _
      have h1 : (0 : ℝ) ≤ (if posExc p C Y R' ε P then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      have h2 := pr_nonneg p.actLaw (fun A => actExc p C Y R' ε P A)
      have h3 : (0 : ℝ) ≤ ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P :=
        Finset.prod_nonneg (fun y _ => relSup_nonneg _ _ _ _ _ _ _ _ _)
      linarith
    refine relSup_le p C Dom sP tP ηP x (M * R') P _ (Finset.sum_nonneg hterm_nonneg) ?_
    intro E hleg
    · calc
        p.actLaw.pr (fun A => relFail p C Dom tP ηP P A E x (M * R'))
            ≤ p.actLaw.pr (fun A => ∃ Y ∈ cfg, ∀ y ∈ Y, relFail p C Dom tP ηC P A E y R') :=
              pr_mono _ _ _ (fun A hf => parent_fail_children p hD0 C Dom tP ηP ηC P A E x
                R' M K q hM2 hR'pos hK hηP0 hηPC hlarge hf)
        _ ≤ ∑ Y ∈ cfg, p.actLaw.pr (fun A => ∀ y ∈ Y, relFail p C Dom tP ηC P A E y R') :=
              pr_finset_exists_le _ _ _
        _ ≤ _ := by
              apply Finset.sum_le_sum
              intro Y hY
              have h2 := pr_nonneg p.actLaw (fun A => actExc p C Y R' ε P A)
              have h3 : (0 : ℝ) ≤
                  ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P :=
                Finset.prod_nonneg (fun y _ => relSup_nonneg _ _ _ _ _ _ _ _ _)
              by_cases hpos : posExc p C Y R' ε P
              · have h1 := pr_le_one p.actLaw
                  (fun A => ∀ y ∈ Y, relFail p C Dom tP ηC P A E y R')
                rw [if_pos hpos]
                linarith
              · have hb := config_activation_bound p hD0 hlam0 C Dom sP sC tP tC ηC ε P E x
                  R' M (K * R') q hM2 hε0 hsgap htgap Y hY hleg hpos
                rw [if_neg hpos]
                linarith
  -- average over positions
  have hY : ∀ Y ∈ cfg,
      p.posLaw.expect (fun P => (if posExc p C Y R' ε P then (1 : ℝ) else 0) +
          p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
          ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P) ≤
        stepExc p.n b σ R' + stepExc p.n b σ R' + β ^ q := by
    intro Y hYc
    obtain ⟨hposB, hactB⟩ := hG p hstd hnG i hi1 hih C x Y hYc
    have hcard : Y.card = q := ((Finset.mem_filter.mp hYc).2).1
    have hfac := private_factorization p C Dom sC tC ηC Y R'
    have hprod : ∏ y ∈ Y, p.posLaw.expect (relSup p (privateDom p C Y y R') Dom sC tC ηC y R')
        ≤ β ^ q := by
      calc
        ∏ y ∈ Y, p.posLaw.expect (relSup p (privateDom p C Y y R') Dom sC tC ηC y R')
            ≤ ∏ _y ∈ Y, β := by
              apply Finset.prod_le_prod₀
              · intro y _
                exact expect_nonneg _ _ (fun P => relSup_nonneg _ _ _ _ _ _ _ _ _)
              · intro y _
                exact hIH (privateDom p C Y y R') Dom y
        _ = β ^ q := by rw [Finset.prod_const, hcard]
    rw [expect_add, expect_add, expect_indicator, expect_section_pr p.posLaw p.actLaw
      (fun P A => actExc p C Y R' ε P A)]
    linarith
  have hcfgcard := configs_card_le p hD0 x (M * R') (K * R') q
  have herr0 : 0 ≤ stepExc p.n b σ R' + stepExc p.n b σ R' + β ^ q := by
    have : 0 ≤ β := (Real.exp_pos _).le
    unfold stepExc
    positivity
  have harith := hA p.n p.d hnA hstd.hdhi i hi1 hih
  rw [← hstd.hH, ← hstd.hD] at harith
  calc
    p.posLaw.expect (relSup p C Dom sP tP ηP x (M * R'))
        ≤ p.posLaw.expect (fun P => ∑ Y ∈ cfg,
            ((if posExc p C Y R' ε P then (1 : ℝ) else 0) +
              p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
              ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P)) :=
          expect_mono _ _ _ hpt
    _ = ∑ Y ∈ cfg, p.posLaw.expect (fun P =>
            (if posExc p C Y R' ε P then (1 : ℝ) else 0) +
              p.actLaw.pr (fun A => actExc p C Y R' ε P A) +
              ∏ y ∈ Y, relSup p (privateDom p C Y y R') Dom sC tC ηC y R' P) :=
          expect_sum _ _ _
    _ ≤ ∑ _Y ∈ cfg, (stepExc p.n b σ R' + stepExc p.n b σ R' + β ^ q) :=
          Finset.sum_le_sum hY
    _ = (cfg.card : ℝ) * (stepExc p.n b σ R' + stepExc p.n b σ R' + β ^ q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((p.H + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (p.D * (M * R'))) ^ q *
          (stepExc p.n b σ R' + stepExc p.n b σ R' + β ^ q) :=
          mul_le_mul_of_nonneg_right hcfgcard herr0
    _ ≤ _ := harith

/-! ## 4. Assembly (proved from the leaves) -/

/-- The scale induction (TeX 03:393–396) at every index up to the top. -/
theorem scale_claim_all (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ n₀ : ℕ, ∀ p : HDParams, Std J₀ b₀ b σ ζ c_d C_d D reg p → n₀ ≤ p.n →
      ∀ i : ℕ, i ≤ hdScaleIndex p.n σ ζ → ScaleClaim p σ ζ a θ i := by
  obtain ⟨n1, hbase⟩ := scale_claim_base J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨n2, hstep⟩ := scale_claim_step J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  refine ⟨max n1 n2, ?_⟩
  intro p hstd hn i hi
  have hn1 : n1 ≤ p.n := le_of_max_le_left hn
  have hn2 : n2 ≤ p.n := le_of_max_le_right hn
  induction i with
  | zero =>
      intro C Dom x
      have hR0 : hdScaleRadius p.n σ 0 = heightBaseRadius p.n := by
        simp [hdScaleRadius]
      have hbounds := hdScaleThreshold_fractions_bounds (h := hdScaleIndex p.n σ ζ)
        (i := 0) (Nat.zero_le _)
      rw [hR0]
      exact hbase p hstd hn1 (heightBaseRadius p.n)
        (by unfold heightBaseRadius; omega) le_rfl _ _ _
        hbounds.1 hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.2 C Dom x
  | succ k ih =>
      have hk := ih (by omega)
      exact hstep p hstd hn2 (k + 1) (by omega) hi (by simpa using hk)

/-- Bound for one actual failure event, through the relaxed claim. -/
theorem actual_pr_le_expect (p : HDParams) (hlam : 30 ≤ p.lam)
    (hnb : 4 ≤ (p.n : ℝ) ^ p.b) (forced : Option p.Loc) (Sites : p.Sites)
    {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
    (Esel : (p.Loc → Bool) → Aux → p.EligMap) (x : HDState p) (R : ℕ) (s t η : ℝ)
    (hs : s ≤ 3 / 10) (ht : t ≤ 3 / 4) :
    (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
      p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x R η) ≤
      p.posLaw.expect (relSup p (forcedFree p forced) (siteDom p Sites) s t η x R) := by
  calc
    _ ≤ (p.posLawForced forced).expect
          (relSup p (forcedFree p forced) (siteDom p Sites) s t η x R) :=
        actual_pr_le_forced_expect p hlam hnb forced Sites πAux Esel x R s t η hs ht
    _ = p.posLaw.expect (relSup p (forcedFree p forced) (siteDom p Sites) s t η x R) :=
        posLawForced_expect_eq p forced _
          (relSup_dependsOn p (forcedFree p forced) (siteDom p Sites) s t η x R)

/-- L3.8(i), assembled. Same statement as `HypercubeRamsey.height_selection_global`. -/
theorem height_selection_global_proof (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
            ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) ≤
          Real.exp (-(p.n : ℝ) ^ (1 + c)) := by
  obtain ⟨c, hc, nA, hA⟩ := global_arith J₀ b₀ b σ ζ θ a c_d C_d D hp
  obtain ⟨nC, hC⟩ := scale_claim_all J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nE, hE⟩ := std_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  refine ⟨c, hc, max nA (max nC nE), ?_⟩
  intro p hD hH hlam hb₀ hb hn hdlo hdhi hreg Sites Aux _ πAux Esel
  have hstd : Std J₀ b₀ b σ ζ c_d C_d D reg p := ⟨hD, hH, hlam, hb₀, hb, hdlo, hdhi, hreg⟩
  have hnA : nA ≤ p.n := le_of_max_le_left hn
  have hnC : nC ≤ p.n := le_of_max_le_left (le_of_max_le_right hn)
  have hnE : nE ≤ p.n := le_of_max_le_right (le_of_max_le_right hn)
  obtain ⟨hD0, hH0, hlam30, hnb4⟩ := hE p hstd hnE
  have hHR : p.H = hdScaleRadius p.n σ (hdScaleIndex p.n σ ζ) :=
    hH.trans (topScale_eq_hdScaleRadius _ _ _)
  have hbounds := hdScaleThreshold_fractions_bounds (h := hdScaleIndex p.n σ ζ)
    (i := hdScaleIndex p.n σ ζ) le_rfl
  set h := hdScaleIndex p.n σ ζ with hh
  set s := hdScaleEligibilityFraction h h
  set t := hdScaleCrowdFraction h h
  set η := hdScaleSlope h h
  have hη0 : 0 ≤ η := le_trans (by norm_num) hbounds.2.2.2.2.1
  let F : CubeVertex p.d → ((p.Loc → Bool) × Aux) × (p.Loc → Bool) → Prop :=
    fun u ω => p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
      hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) (u, 0) p.H η
  have hsub : ∀ ω : ((p.Loc → Bool) × Aux) × (p.Loc → Bool),
      (p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
        ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2)) → ∃ u ∈ Sites, F u ω := by
    rintro ω ⟨hlegal, hgood⟩
    obtain ⟨u, hu, hfail⟩ := not_goodHeights_top_failure p hD0 hH0 Sites ω.1.1 ω.2
      (Esel ω.1.1 ω.1.2) η hη0 hgood
    exact ⟨u, hu, hlegal, hfail⟩
  have hterm : ∀ u ∈ Sites, ((p.posLaw.prod πAux).prod p.actLaw).pr (F u) ≤
      Real.exp (-((p.n : ℝ) ^ a * (topScale p.n σ ζ : ℝ) ^ θ)) := by
    intro u _
    have h1 := actual_pr_le_expect p hlam30 hnb4 none Sites πAux Esel (u, 0) p.H s t η
      hbounds.2.1 hbounds.2.2.2.1
    rw [posLawForced_none] at h1
    have h2 := hC p hstd hnC h le_rfl (forcedFree p none) (siteDom p Sites) (u, 0)
    rw [← hHR] at h2
    exact (h1.trans h2).trans_eq (by rw [hH])
  have hcard : (Sites.card : ℝ) ≤ (2 : ℝ) ^ p.d := by
    have h := Finset.card_le_univ Sites
    rw [card_cubeVertex] at h
    exact_mod_cast h
  have hexp0 : 0 ≤ Real.exp (-((p.n : ℝ) ^ a * (topScale p.n σ ζ : ℝ) ^ θ)) :=
    (Real.exp_pos _).le
  calc
    ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω =>
        p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          ¬ p.GoodHeights Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2))
        ≤ ((p.posLaw.prod πAux).prod p.actLaw).pr (fun ω => ∃ u ∈ Sites, F u ω) :=
          pr_mono _ _ _ hsub
    _ ≤ ∑ u ∈ Sites, ((p.posLaw.prod πAux).prod p.actLaw).pr (F u) :=
          pr_finset_exists_le _ _ _
    _ ≤ ∑ _u ∈ Sites, Real.exp (-((p.n : ℝ) ^ a * (topScale p.n σ ζ : ℝ) ^ θ)) :=
          Finset.sum_le_sum hterm
    _ = (Sites.card : ℝ) * Real.exp (-((p.n : ℝ) ^ a * (topScale p.n σ ζ : ℝ) ^ θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ p.d * Real.exp (-((p.n : ℝ) ^ a * (topScale p.n σ ζ : ℝ) ^ θ)) :=
          mul_le_mul_of_nonneg_right hcard hexp0
    _ ≤ Real.exp (-(p.n : ℝ) ^ (1 + c)) := hA p.n p.d hnA hdhi

/-- L3.8(ii), assembled. Same statement as `HypercubeRamsey.height_selection_positive`. -/
theorem height_selection_positive_proof (J₀ b₀ b σ ζ θ a c_d C_d : ℝ) (D : ℕ)
    (hp : HDAdmissible J₀ b₀ b σ ζ θ a c_d C_d D) (reg : HDRegime b₀ b D) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ p : HDParams, p.D = D → p.H = topScale p.n σ ζ →
      p.lam = (p.n : ℝ) ^ J₀ → p.b₀ = b₀ → p.b = b → n₀ ≤ p.n →
      c_d * p.n ≤ p.d → (p.d : ℝ) ≤ C_d * p.n → reg.ok p.n p.d p.r →
      ∀ (Sites : p.Sites) (v : CubeVertex p.d) (_hv : v ∈ Sites) (forced : Option p.Loc)
        {Aux : Type*} [Fintype Aux] (πAux : FinProb Aux)
        (Esel : (p.Loc → Bool) → Aux → p.EligMap),
        (((p.posLawForced forced).prod πAux).prod p.actLaw).pr (fun ω =>
          p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) (p.domBall Sites v p.Rlong) ∧
            0 < p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v) ≤
          Real.exp (-(p.n : ℝ) ^ c) := by
  obtain ⟨c, hc, nA, hA⟩ := positive_arith J₀ b₀ b σ ζ θ a c_d C_d D hp
  obtain ⟨nC, hC⟩ := scale_claim_all J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nB, hB⟩ := scale_claim_base J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nE, hE⟩ := std_eventually J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  refine ⟨c, hc, max (max nA nC) (max nB nE), ?_⟩
  intro p hD hH hlam hb₀ hb hn hdlo hdhi hreg Sites v hv forced Aux _ πAux Esel
  have hstd : Std J₀ b₀ b σ ζ c_d C_d D reg p := ⟨hD, hH, hlam, hb₀, hb, hdlo, hdhi, hreg⟩
  have hnA : nA ≤ p.n := le_of_max_le_left (le_of_max_le_left hn)
  have hnC : nC ≤ p.n := le_of_max_le_right (le_of_max_le_left hn)
  have hnB : nB ≤ p.n := le_of_max_le_left (le_of_max_le_right hn)
  have hnE : nE ≤ p.n := le_of_max_le_right (le_of_max_le_right hn)
  obtain ⟨hD0, hH0, hlam30, hnb4⟩ := hE p hstd hnE
  have hHR : p.H = hdScaleRadius p.n σ (hdScaleIndex p.n σ ζ) :=
    hH.trans (topScale_eq_hdScaleRadius _ _ _)
  set h := hdScaleIndex p.n σ ζ with hh
  set Dom := p.domBall Sites v p.Rlong with hDom
  set R₀ := heightBaseRadius p.n with hR₀
  let μ := ((p.posLawForced forced).prod πAux).prod p.actLaw
  let Fail : HDState p → ℕ → ℝ → ((p.Loc → Bool) × Aux) × (p.Loc → Bool) → Prop :=
    fun x R η ω => p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Dom ∧
      hdScaleFailure Dom ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x R η
  -- the three witness families
  let EvA : ((p.Loc → Bool) × Aux) × (p.Loc → Bool) → Prop :=
    fun ω => ∃ y ∈ baseStarts p Dom v R₀, Fail y 1 (1 / 2) ω
  let EvB : ((p.Loc → Bool) × Aux) × (p.Loc → Bool) → Prop :=
    fun ω => ∃ i ∈ Finset.range h, ∃ u ∈ midStarts p Dom v (hdScaleRadius p.n σ (i + 1)),
      Fail (u, 0) (hdScaleRadius p.n σ i) (hdScaleSlope h i) ω
  let EvC : ((p.Loc → Bool) × Aux) × (p.Loc → Bool) → Prop :=
    fun ω => ∃ u ∈ Dom, Fail (u, 0) (hdScaleRadius p.n σ h) (hdScaleSlope h h) ω
  have hsub : ∀ ω : ((p.Loc → Bool) × Aux) × (p.Loc → Bool),
      (p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Dom ∧
        0 < p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v) →
        EvA ω ∨ (EvB ω ∨ EvC ω) := by
    rintro ω ⟨hlegal, hpos⟩
    rcases positive_height_witness p hD0 σ ζ hHR Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) v hv hpos
      with ⟨y, hy, hf⟩ | ⟨i, hi, u, hu, hf⟩ | ⟨u, hu, hf⟩
    · exact Or.inl ⟨y, hy, hlegal, hf⟩
    · exact Or.inr (Or.inl ⟨i, hi, u, hu, hlegal, hf⟩)
    · exact Or.inr (Or.inr ⟨u, hu, hlegal, hf⟩)
  -- one-event bound through the relaxed claims
  have hkey : ∀ (x : HDState p) (R : ℕ) (s t η : ℝ), s ≤ 3 / 10 → t ≤ 3 / 4 →
      μ.pr (Fail x R η) ≤
        p.posLaw.expect (relSup p (forcedFree p forced) (siteDom p Dom) s t η x R) :=
    fun x R s t η hs ht =>
      actual_pr_le_expect p hlam30 hnb4 forced Dom πAux Esel x R s t η hs ht
  set eBase := Real.exp (-((p.n : ℝ) ^ a * (R₀ : ℝ) ^ θ)) with heBase
  set e : ℕ → ℝ := fun i => Real.exp (-((p.n : ℝ) ^ a * (hdScaleRadius p.n σ i : ℝ) ^ θ))
    with he
  have hA1 : μ.pr EvA ≤ ((baseStarts p Dom v R₀).card : ℝ) * eBase := by
    calc
      μ.pr EvA ≤ ∑ y ∈ baseStarts p Dom v R₀, μ.pr (Fail y 1 (1 / 2)) :=
          pr_finset_exists_le _ _ _
      _ ≤ ∑ _y ∈ baseStarts p Dom v R₀, eBase := by
          apply Finset.sum_le_sum
          intro y _
          refine (hkey y 1 (1 / 4) (3 / 5) (1 / 2) (by norm_num) (by norm_num)).trans ?_
          exact hB p hstd hnB 1 le_rfl (by unfold heightBaseRadius; omega)
            (1 / 4) (3 / 5) (1 / 2) le_rfl le_rfl (by norm_num) le_rfl
            (forcedFree p forced) (siteDom p Dom) y
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hB1 : μ.pr EvB ≤ ∑ i ∈ Finset.range h,
      ((midStarts p Dom v (hdScaleRadius p.n σ (i + 1))).card : ℝ) * e i := by
    calc
      μ.pr EvB ≤ ∑ i ∈ Finset.range h, μ.pr (fun ω =>
          ∃ u ∈ midStarts p Dom v (hdScaleRadius p.n σ (i + 1)),
            Fail (u, 0) (hdScaleRadius p.n σ i) (hdScaleSlope h i) ω) :=
          pr_finset_exists_le _ _ _
      _ ≤ ∑ i ∈ Finset.range h,
          ((midStarts p Dom v (hdScaleRadius p.n σ (i + 1))).card : ℝ) * e i := by
          apply Finset.sum_le_sum
          intro i hi
          have hih : i ≤ h := le_of_lt (Finset.mem_range.mp hi)
          have hbounds := hdScaleThreshold_fractions_bounds (h := h) (i := i) hih
          calc
            _ ≤ ∑ u ∈ midStarts p Dom v (hdScaleRadius p.n σ (i + 1)),
                μ.pr (Fail (u, 0) (hdScaleRadius p.n σ i) (hdScaleSlope h i)) :=
                pr_finset_exists_le _ _ _
            _ ≤ ∑ _u ∈ midStarts p Dom v (hdScaleRadius p.n σ (i + 1)), e i := by
                apply Finset.sum_le_sum
                intro u _
                refine (hkey (u, 0) (hdScaleRadius p.n σ i) (hdScaleEligibilityFraction h i)
                  (hdScaleCrowdFraction h i) (hdScaleSlope h i) hbounds.2.1
                  hbounds.2.2.2.1).trans ?_
                exact hC p hstd hnC i hih (forcedFree p forced) (siteDom p Dom) (u, 0)
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hC1 : μ.pr EvC ≤ (Dom.card : ℝ) * e h := by
    have hbounds := hdScaleThreshold_fractions_bounds (h := h) (i := h) le_rfl
    calc
      μ.pr EvC ≤ ∑ u ∈ Dom, μ.pr (Fail (u, 0) (hdScaleRadius p.n σ h) (hdScaleSlope h h)) :=
          pr_finset_exists_le _ _ _
      _ ≤ ∑ _u ∈ Dom, e h := by
          apply Finset.sum_le_sum
          intro u _
          refine (hkey (u, 0) (hdScaleRadius p.n σ h) (hdScaleEligibilityFraction h h)
            (hdScaleCrowdFraction h h) (hdScaleSlope h h) hbounds.2.1
            hbounds.2.2.2.1).trans ?_
          exact hC p hstd hnC h le_rfl (forcedFree p forced) (siteDom p Dom) (u, 0)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  -- cardinalities
  have hcardA : ((baseStarts p Dom v R₀).card : ℝ) ≤
      ((topScale p.n σ ζ + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (2 * D * R₀) := by
    have := baseStarts_card_le p hD0 Dom v R₀
    rw [hH, hD] at this
    exact this
  have hcardB : ∀ i, ((midStarts p Dom v (hdScaleRadius p.n σ (i + 1))).card : ℝ) ≤
      ((p.d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius p.n σ (i + 1)) := by
    intro i
    have := midStarts_card_le p hD0 Dom v (hdScaleRadius p.n σ (i + 1))
    rw [hD] at this
    exact this
  have hcardC : (Dom.card : ℝ) ≤ (2 : ℝ) ^ p.d := by
    have h := Finset.card_le_univ Dom
    rw [card_cubeVertex] at h
    exact_mod_cast h
  have heh : e h = Real.exp (-((p.n : ℝ) ^ a * (topScale p.n σ ζ : ℝ) ^ θ)) := by
    simp only [he]
    rw [← topScale_eq_hdScaleRadius]
  have heB : 0 ≤ eBase := (Real.exp_pos _).le
  have he0 : ∀ i, 0 ≤ e i := fun i => (Real.exp_pos _).le
  calc
    μ.pr (fun ω => p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Dom ∧
        0 < p.height Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) p.Rlong v)
        ≤ μ.pr (fun ω => EvA ω ∨ (EvB ω ∨ EvC ω)) := pr_mono _ _ _ hsub
    _ ≤ μ.pr EvA + (μ.pr EvB + μ.pr EvC) := by
        refine (pr_or_le _ _ _).trans ?_
        exact add_le_add le_rfl (pr_or_le _ _ _)
    _ ≤ ((baseStarts p Dom v R₀).card : ℝ) * eBase +
        ((∑ i ∈ Finset.range h,
          ((midStarts p Dom v (hdScaleRadius p.n σ (i + 1))).card : ℝ) * e i) +
          (Dom.card : ℝ) * e h) :=
        add_le_add hA1 (add_le_add hB1 hC1)
    _ ≤ ((topScale p.n σ ζ + 1 : ℕ) : ℝ) * ((p.d + 1 : ℕ) : ℝ) ^ (2 * D * R₀) * eBase +
        ((∑ i ∈ Finset.range h,
          ((p.d + 1 : ℕ) : ℝ) ^ (D * hdScaleRadius p.n σ (i + 1)) * e i) +
          (2 : ℝ) ^ p.d * e h) := by
        refine add_le_add (mul_le_mul_of_nonneg_right hcardA heB)
          (add_le_add ?_ (mul_le_mul_of_nonneg_right hcardC (he0 h)))
        exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcardB i) (he0 i))
    _ ≤ Real.exp (-(p.n : ℝ) ^ c) := by
        rw [heh]
        exact hA p.n p.d hnA hdhi

end Lane_opus_height

end HypercubeRamsey
