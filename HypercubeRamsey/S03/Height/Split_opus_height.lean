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
  classical
  let C := forcedFree p forced
  let Dom := siteDom p Sites
  let N : ℝ := (p.n : ℝ) ^ p.b
  have hN : 4 ≤ N := by simpa [N] using hnb
  have hn : 0 < p.n := by
    by_contra h
    have hn0 : p.n = 0 := by omega
    have hcast : (p.n : ℝ) = 0 := by exact_mod_cast hn0
    by_cases hb0 : p.b = 0
    · rw [hb0, Real.rpow_zero] at hnb
      norm_num at hnb
    · rw [hcast, Real.zero_rpow hb0] at hnb
      norm_num at hnb
  have hn2 : 2 ≤ p.n := by
    by_contra h
    have hnle : p.n ≤ 1 := by omega
    have hn1 : p.n = 1 := by omega
    rw [hn1] at hnb
    norm_num at hnb
  have hb : 0 < p.b := by
    by_contra h
    have hpow : (p.n : ℝ) ^ p.b ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ p.n by omega))
        (le_of_not_gt h)
    linarith [hnb, hpow]
  have filterCardLoss (S : Finset p.Loc) :
      S.card ≤ (S.filter (fun ℓ => ℓ ∈ C)).card + 1 := by
    cases forced with
    | none =>
        have hsub : S ⊆ S.filter (fun ℓ => ℓ ∈ C) := by
          intro ℓ hℓ
          apply Finset.mem_filter.mpr
          exact ⟨hℓ, by simp [C, forcedFree]⟩
        have hcard := Finset.card_le_card hsub
        omega
    | some f =>
        let T := S.filter (fun ℓ => ℓ ∈ C)
        have hsub : S ⊆ insert f T := by
          intro ℓ hℓ
          by_cases hℓf : ℓ = f
          · subst ℓ
            exact Finset.mem_insert_self _ _
          · apply Finset.mem_insert_of_mem
            apply Finset.mem_filter.mpr
            have hneq : f ≠ ℓ := Ne.symm hℓf
            exact ⟨hℓ, by simp [T, C, forcedFree, hneq]⟩
        have hcard := Finset.card_le_card hsub
        have hinsert : (insert f T).card ≤ T.card + 1 := Finset.card_insert_le f T
        simpa [T] using hcard.trans hinsert
  have hbound : ∀ pa : (p.Loc → Bool) × Aux,
      p.actLaw.pr (fun A =>
        p.Legal pa.1 (Esel pa.1 pa.2) Sites ∧
          hdScaleFailure Sites pa.1 A (Esel pa.1 pa.2) x R η) ≤
        relSup p C Dom s t η x R pa.1 := by
    intro pa
    let P := pa.1
    let E := Esel pa.1 pa.2
    have crowdCardLoss (A : p.Loc → Bool) (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
        (Finset.univ.filter (fun u : CubeVertex p.d =>
          P (u, j) = true ∧ A (u, j) = true ∧
            _root_.hammingDist u v ≤ p.r + p.D)).card ≤
          relCrowd p C P A v j + 1 := by
      let active : CubeVertex p.d → Prop := fun u =>
        P (u, j) = true ∧ A (u, j) = true ∧
          _root_.hammingDist u v ≤ p.r + p.D
      let U : Finset (CubeVertex p.d) := Finset.univ.filter active
      let V : Finset (CubeVertex p.d) :=
        Finset.univ.filter (fun u => (u, j) ∈ C ∧ active u)
      change U.card ≤ V.card + 1
      cases forced with
      | none =>
          have hsub : U ⊆ V := by
            intro u hu
            have hactive := (Finset.mem_filter.mp hu).2
            have hC : (u, j) ∈ C := by simp [C, forcedFree]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hC, hactive⟩⟩
          have hcard : U.card ≤ V.card := Finset.card_le_card hsub
          omega
      | some f =>
          have hsub : U ⊆ insert f.1 V := by
            intro u hu
            by_cases huf : u = f.1
            · subst u
              exact Finset.mem_insert_self _ _
            · apply Finset.mem_insert_of_mem
              apply Finset.mem_filter.mpr
              have hneq : f ≠ (u, j) := by
                intro heq
                exact huf (congrArg Prod.fst heq).symm
              have hC : (u, j) ∈ C := by
                simp [C, forcedFree, hneq]
              exact ⟨Finset.mem_univ _, ⟨hC, (Finset.mem_filter.mp hu).2⟩⟩
          have hcard : U.card ≤ (insert f.1 V).card := Finset.card_le_card hsub
          have hinsert : (insert f.1 V).card ≤ V.card + 1 :=
            Finset.card_insert_le f.1 V
          exact hcard.trans hinsert
    by_cases hlegal : p.Legal P E Sites
    · have hrelLegal : relLegal p C Dom s P E x R := by
        intro v j hv _
        change v ∈ Sites at hv
        rcases (show p.LegalAt P E v j from hlegal v hv j) with ⟨hitems, hsize⟩
        refine ⟨?_, ?_⟩
        · intro ℓ hℓ _
          exact hitems ℓ hℓ
        · let F := (E v j).filter (fun ℓ => ℓ ∈ C)
          have hloss : (E v j).card ≤ F.card + 1 := by
            simpa [F] using filterCardLoss (E v j)
          have hlossR : ((E v j).card : ℝ) ≤ (F.card : ℝ) + 1 := by
            exact_mod_cast hloss
          have hbase : (3 / 10 : ℝ) * p.lam ≤ (F.card : ℝ) := by
            have hmargin : (3 / 10 : ℝ) * p.lam ≤ p.lam / 3 - 1 := by
              nlinarith [hlam]
            have hsize' : p.lam / 3 - 1 ≤ (F.card : ℝ) := by
              nlinarith [hsize, hlossR]
            exact hmargin.trans hsize'
          have hlam0 : 0 ≤ p.lam := by linarith
          have hs' : s * p.lam ≤ (3 / 10 : ℝ) * p.lam :=
            mul_le_mul_of_nonneg_right hs hlam0
          have hsizeC : s * p.lam ≤ (F.card : ℝ) := hs'.trans hbase
          simpa [F] using hsizeC
      have hrelFail : ∀ A : p.Loc → Bool,
          p.Legal P E Sites ∧ hdScaleFailure Sites P A E x R η →
            relFail p C Dom t η P A E x R := by
        intro A hEvent
        rcases hEvent with ⟨_, hfail⟩
        have crowdCardLoss' (v : CubeVertex p.d) (j : Fin (p.H + 1)) :
            (Finset.univ.filter (fun u : CubeVertex p.d =>
              P (u, j) = true ∧ A (u, j) = true ∧
                _root_.hammingDist u v ≤ p.r + p.D)).card ≤
              relCrowd p C P A v j + 1 := by
          exact crowdCardLoss A v j
        have badAtRel (v : CubeVertex p.d) (j : Fin (p.H + 1))
            (hbad : p.Bad P A E v j) : relBadAt p C t P A E v j := by
          rcases hbad with hhole | hcrowd
          · exact Or.inl (fun ℓ hℓ _ => hhole ℓ hℓ)
          · right
            let U : Finset (CubeVertex p.d) := Finset.univ.filter (fun u =>
              P (u, j) = true ∧ A (u, j) = true ∧
                _root_.hammingDist u v ≤ p.r + p.D)
            have hcount : N < (U.card : ℝ) := by
              simpa [N, U] using hcrowd
            have hloss : (U.card : ℝ) ≤ (relCrowd p C P A v j : ℝ) + 1 := by
              exact_mod_cast crowdCardLoss' v j
            by_cases hN4 : N = 4
            · have hcount4 : (4 : ℝ) < (U.card : ℝ) := by simpa [hN4] using hcount
              have hchildR : (3 : ℝ) < (relCrowd p C P A v j : ℝ) := by
                nlinarith [hcount4, hloss]
              have htN : t * N ≤ 3 := by rw [hN4]; nlinarith [ht]
              exact lt_of_le_of_lt htN hchildR
            · have hNgt : 4 < N := lt_of_le_of_ne hN (Ne.symm hN4)
              have htN : t * N ≤ (3 / 4 : ℝ) * N :=
                mul_le_mul_of_nonneg_right ht (by linarith [hNgt])
              have hmargin : (3 / 4 : ℝ) * N < N - 1 := by nlinarith
              have hchild : N - 1 < (relCrowd p C P A v j : ℝ) := by
                nlinarith [hcount, hloss]
              exact (lt_of_le_of_lt htN hmargin).trans hchild
        have hwalkConv : ∀ {start finish},
            HDScaleWalk Sites P A E x R start finish →
              HDThresholdWalk (Finset.univ : p.Sites)
                (relBad p C Dom t P A E) x R start finish := by
          intro start finish walk
          induction walk with
          | stop hstop => exact HDThresholdWalk.stop hstop
          | @up v j finish hinside hv hj hbad tail ih =>
              let hjFin : j < p.H + 1 := Classical.choose hbad
              have hbadAt : p.Bad P A E v ⟨j, hjFin⟩ := Classical.choose_spec hbad
              apply HDThresholdWalk.up hinside (Finset.mem_univ v) hj ?_ ih
              have hDom : (v, j) ∈ Dom := by
                change v ∈ Sites
                exact hv
              exact ⟨hDom, ⟨hjFin, badAtRel v ⟨j, hjFin⟩ hbadAt⟩⟩
          | @down v v' j finish hinside hv' hj hstep tail ih =>
              exact HDThresholdWalk.down hinside (Finset.mem_univ v') hj hstep ih
        change hdScaleThresholdFailure (Finset.univ : p.Sites)
          (relBad p C Dom t P A E) x R η
        rcases hfail with ⟨finish, ⟨walk⟩, hnet⟩
        exact ⟨finish, ⟨hwalkConv walk⟩, hnet⟩
      have hinc : ∀ A : p.Loc → Bool,
          (p.Legal P E Sites ∧ hdScaleFailure Sites P A E x R η) →
            relFail p C Dom t η P A E x R := hrelFail
      calc
        p.actLaw.pr (fun A => p.Legal P E Sites ∧ hdScaleFailure Sites P A E x R η)
            ≤ p.actLaw.pr (fun A => relFail p C Dom t η P A E x R) :=
              pr_mono _ _ _ hinc
        _ ≤ relSup p C Dom s t η x R P := by
              unfold relSup
              refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ E))
              rw [if_pos hrelLegal]
    · have hzero : p.actLaw.pr
          (fun A => p.Legal P E Sites ∧ hdScaleFailure Sites P A E x R η) = 0 := by
        unfold FinProb.pr
        simp [hlegal]
      rw [hzero]
      unfold relSup
      refine le_trans ?_ (Finset.le_sup' _
        (Finset.mem_univ (fun _ _ => ∅ : p.EligMap)))
      split_ifs
      · exact pr_nonneg _ _
      · exact le_rfl
  calc
    (((p.posLawForced forced).prod πAux).prod p.actLaw).pr
        (fun ω => p.Legal ω.1.1 (Esel ω.1.1 ω.1.2) Sites ∧
          hdScaleFailure Sites ω.1.1 ω.2 (Esel ω.1.1 ω.1.2) x R η)
        ≤ ((p.posLawForced forced).prod πAux).expect
            (fun pa => relSup p C Dom s t η x R pa.1) :=
          prod_pr_le_expect _ _ _ _ hbound
    _ = (p.posLawForced forced).expect (relSup p C Dom s t η x R) := by
      unfold FinProb.expect FinProb.prod
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro P hP
      calc
        (∑ a : Aux,
            (p.posLawForced forced).w P * πAux.w a *
              relSup p C Dom s t η x R P)
            = ∑ a : Aux,
                ((p.posLawForced forced).w P * relSup p C Dom s t η x R P) *
                  πAux.w a := by
                    apply Finset.sum_congr rfl
                    intro a ha
                    ring
        _ = ((p.posLawForced forced).w P * relSup p C Dom s t η x R P) *
              ∑ a : Aux, πAux.w a := by rw [Finset.mul_sum]
        _ = (p.posLawForced forced).w P * relSup p C Dom s t η x R P := by
              rw [πAux.sum_eq_one]
              ring

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
  classical
  rcases hp.hsz with ⟨hσpos, hσζ, hζone, hθpos, hθone⟩
  rcases hp.hb with ⟨hb₀pos, hb₀b, hbone⟩
  have hJgap : 1 < J₀ - b₀ := by linarith [hp.hJ, hb₀b, hbone]
  obtain ⟨nGeom, hGeomAll⟩ := height_local_geometry_eventually
    J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nVol, hVolAll⟩ := height_volume_ge_lambda_eventually
    J₀ b₀ b σ ζ θ a c_d C_d D hp reg
  obtain ⟨nDim, hDimAll⟩ := heightBaseRadius_times_D_le_dimension_eventually
    D c_d hp.hD hp.hd.1
  have hCdpos : 0 < C_d := lt_of_lt_of_le hp.hd.1 hp.hd.2
  have heCount : 0 < b₀ / 4 := by positivity
  obtain ⟨nCount, hCountAll⟩ := hdScaleBallSiteLevels_exp_bound D C_d (b₀ / 4)
    hp.hD hCdpos heCount
  have hAbsorbExp : 0 < b₀ / 4 := by positivity
  obtain ⟨nAbsorb, hAbsorbAll⟩ := exists_nat_rpow_ge
    (e := b₀ / 4) (C := 3) hAbsorbExp
  obtain ⟨nRad, hRadAll⟩ := heightBaseRadius_le_logsq
  have hζpos : 0 < ζ := lt_trans hσpos hσζ
  have honeθ : 0 < 1 - θ := sub_pos.mpr hθone
  have hsumPos : 0 < ζ + σ + (1 - θ) := by positivity
  have haPos : 0 < a := lt_trans hsumPos hp.ha.1
  obtain ⟨nArith, hArithAll⟩ := height_base_exp_arithmetic a b₀ θ haPos hp.ha.2.1
    ⟨hθpos, hθone⟩
  let N1 := max nGeom nVol
  let N2 := max nDim (max nCount nAbsorb)
  let N3 := max nRad nArith
  let Ntail := max N1 (max N2 N3)
  let Nall := max 30 (max 2 Ntail)
  refine ⟨Nall, ?_⟩
  intro p hstd hn R hRone hRle s t η hs htlo hthi hη C Dom x
  have hCore : max 2 Ntail ≤ p.n := le_trans (Nat.le_max_right 30 _) hn
  have hn30 : 30 ≤ p.n := le_trans (Nat.le_max_left 30 _) hn
  have hn2 : 2 ≤ p.n := le_trans (Nat.le_max_left 2 _) hCore
  have hNtail : Ntail ≤ p.n := le_trans (Nat.le_max_right 2 _) hCore
  have hN1 : N1 ≤ p.n := le_trans (Nat.le_max_left N1 _) hNtail
  have hN23 : max N2 N3 ≤ p.n := le_trans (Nat.le_max_right N1 _) hNtail
  have hN2 : N2 ≤ p.n := le_trans (Nat.le_max_left N2 N3) hN23
  have hN3 : N3 ≤ p.n := le_trans (Nat.le_max_right N2 N3) hN23
  have hnGeom : nGeom ≤ p.n := le_trans (Nat.le_max_left nGeom nVol) hN1
  have hnVol : nVol ≤ p.n := le_trans (Nat.le_max_right nGeom nVol) hN1
  have hN2tail : max nCount nAbsorb ≤ p.n := le_trans (Nat.le_max_right nDim _) hN2
  have hnDim : nDim ≤ p.n := le_trans (Nat.le_max_left nDim _) hN2
  have hnCountAbsorb : max nCount nAbsorb ≤ p.n := hN2tail
  have hnCount : nCount ≤ p.n := le_trans (Nat.le_max_left nCount nAbsorb) hnCountAbsorb
  have hnAbsorb : nAbsorb ≤ p.n := le_trans (Nat.le_max_right nCount nAbsorb) hnCountAbsorb
  have hnRad : nRad ≤ p.n := le_trans (Nat.le_max_left nRad nArith) hN3
  have hnArith : nArith ≤ p.n := le_trans (Nat.le_max_right nRad nArith) hN3
  have hGeom := hGeomAll p hstd.hD hstd.hb₀ hstd.hb hnGeom
    hstd.hdlo hstd.hdhi hstd.hreg
  have hVol := hVolAll p hstd.hD hstd.hlam hnVol hstd.hdlo hstd.hreg
  have hR0 : (heightBaseRadius p.n : ℝ) ≤ 2 * (Real.log (p.n : ℝ)) ^ 2 :=
    hRadAll p.n hnRad
  have hR0pos : 0 < heightBaseRadius p.n :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hR0dim := hDimAll p.n p.d hnDim hstd.hdlo
  have hDdim : p.D * heightBaseRadius p.n ≤ p.d := by
    rw [hstd.hD]
    exact hR0dim
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast (by omega : 0 < p.n)
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast (by omega : 1 ≤ p.n)
  have hlamPos : 0 < p.lam := by
    rw [hstd.hlam]
    exact Real.rpow_pos_of_pos hnpos _
  have hVpos : 0 < (p.V : ℝ) := lt_of_lt_of_le hlamPos hVol
  have hDpos : 0 < p.D := by
    rw [hstd.hD]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one hp.hD
  have hlamLower : (p.n : ℝ) ^ p.b₀ ≤ p.lam := by
    rw [hstd.hlam, hstd.hb₀]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hJgap])
  have hpowGap : (p.n : ℝ) ≤ (p.n : ℝ) ^ (J₀ - b₀) := by
    have h := Real.rpow_le_rpow_of_exponent_le hn1
      (show (1 : ℝ) ≤ J₀ - b₀ by linarith [hJgap])
    simpa only [Real.rpow_one] using h
  have hpowEq : (p.n : ℝ) ^ J₀ =
      (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (J₀ - b₀) := by
    calc
      _ = (p.n : ℝ) ^ (b₀ + (J₀ - b₀)) := by congr 1 <;> ring
      _ = _ := Real.rpow_add hnpos _ _
  have hlamFactor : 30 * (p.n : ℝ) ^ p.b₀ ≤ p.lam := by
    rw [hstd.hlam, hstd.hb₀, hpowEq]
    calc
      30 * (p.n : ℝ) ^ b₀ ≤ (p.n : ℝ) * (p.n : ℝ) ^ b₀ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn30)
          (Real.rpow_nonneg hnpos.le _)
      _ = (p.n : ℝ) ^ b₀ * (p.n : ℝ) := by ring
      _ ≤ (p.n : ℝ) ^ b₀ * (p.n : ℝ) ^ (J₀ - b₀) :=
        mul_le_mul_of_nonneg_left hpowGap (Real.rpow_nonneg hnpos.le _)
  have hqA0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam :=
    div_pos (Real.rpow_pos_of_pos hnpos _) hlamPos
  have hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1 :=
    (div_le_one hlamPos).2 hlamLower
  have hqP0 : 0 < p.lam / (p.V : ℝ) := div_pos hlamPos hVpos
  have hqP1 : p.lam / (p.V : ℝ) ≤ 1 := (div_le_one hVpos).2 hVol
  have hGeomBand := hGeom.2.2
  have hqA1' : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1 := hqA1
  have htLower : (11 : ℝ) / 20 ≤ t := by linarith [htlo]
  let δsite : ℝ := 4 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8)
  let T := hdScaleBallSiteLevels (Finset.univ : p.Sites) x R
  let T0 := hdScaleBallSiteLevels (Finset.univ : p.Sites) (x.1, 0)
    (heightBaseRadius p.n)
  let B0 : Finset (CubeVertex p.d) := Finset.univ.filter (fun u =>
    (_root_.hammingDist x.1 u + max 1 p.D - 1) / max 1 p.D < heightBaseRadius p.n)
  let L : Finset (Fin (p.H + 1)) := Finset.univ.filter
    (fun j => Nat.dist x.2 j.val < R)
  let L0 : Finset (Fin (p.H + 1)) := Finset.univ.filter
    (fun j => j.val < heightBaseRadius p.n)
  have hTsub : T ⊆ B0.product L := by
    intro y hy
    have hdist : hdScaleDistance p.D x (y.1, y.2.val) < R := by
      simpa [T, hdScaleBallSiteLevels] using hy
    have hmax : max (Nat.dist x.2 y.2.val)
        ((_root_.hammingDist x.1 y.1 + max 1 p.D - 1) / max 1 p.D) < R := by
      simpa [hdScaleDistance] using hdist
    rcases max_lt_iff.mp hmax with ⟨hlev, hspace⟩
    change y ∈ B0 ×ˢ L
    rw [Finset.mem_product]
    constructor
    · simp only [B0, Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_lt_of_le hspace hRle
    · simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlev
  have hT0eq : T0 = B0.product L0 := by
    ext y
    simp [T0, B0, L0, hdScaleBallSiteLevels, hdScaleDistance,
      Nat.dist_zero_left, max_lt_iff, and_comm]
  have hLinterval : L.card ≤ (Finset.Icc (x.2 - R) (x.2 + R)).card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin (p.H + 1) => j.val)
    · intro j hj
      have hdist : Nat.dist x.2 j.val < R := by simpa [L] using hj
      change j.val ∈ Finset.Icc (x.2 - R) (x.2 + R)
      simp only [Finset.mem_Icc]
      rcases le_total x.2 j.val with hle | hge
      · rw [Nat.dist_eq_sub_of_le hle] at hdist
        constructor <;> omega
      · rw [Nat.dist_eq_sub_of_le_right hge] at hdist
        constructor <;> omega
    · intro j hj j' hj' hval
      exact Fin.ext hval
  have hIcc : (Finset.Icc (x.2 - R) (x.2 + R)).card ≤ 2 * R + 1 := by
    simp
    omega
  have hLcard : L.card ≤ 3 * heightBaseRadius p.n := by
    have hR0one : 1 ≤ heightBaseRadius p.n := by omega
    omega
  have hLall : L.card ≤ p.H + 1 := by
    calc
      L.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ L)
      _ = p.H + 1 := by simp
  let m := min (p.H + 1) (heightBaseRadius p.n)
  have hmH : m ≤ p.H + 1 := Nat.min_le_left _ _
  have hmR : m ≤ heightBaseRadius p.n := Nat.min_le_right _ _
  have hL0card : L0.card = min (p.H + 1) (heightBaseRadius p.n) := by
    simpa [L0] using (Fin.card_filter_val_lt (n := p.H + 1)
      (m := heightBaseRadius p.n))
  have hL0lower : m ≤ L0.card := by rw [hL0card]
  have hLratio : L.card ≤ 3 * L0.card := by
    have hmin : min (p.H + 1) (3 * heightBaseRadius p.n) ≤
        3 * min (p.H + 1) (heightBaseRadius p.n) := by omega
    calc
      L.card ≤ min (p.H + 1) (3 * heightBaseRadius p.n) :=
        Nat.le_min.mpr ⟨hLall, hLcard⟩
      _ ≤ 3 * m := hmin
      _ ≤ 3 * L0.card := Nat.mul_le_mul_left 3 hL0lower
  have hTcard : T.card ≤ 3 * T0.card := by
    calc
      T.card ≤ (B0.product L).card := Finset.card_le_card hTsub
      _ = B0.card * L.card := Finset.card_product B0 L
      _ ≤ B0.card * (3 * L0.card) := Nat.mul_le_mul_left B0.card hLratio
      _ = 3 * (B0.card * L0.card) := by ring
      _ = 3 * T0.card := by
        have hT0card : T0.card = B0.card * L0.card := by
          simpa [hT0eq] using (Finset.card_product B0 L0)
        rw [← hT0card]
  have hT0count := hCountAll (Finset.univ : p.Sites) (x.1, 0)
    (heightBaseRadius p.n) hnCount hstd.hD hstd.hdhi hR0 hR0pos rfl hDdim
  have hTcardReal : (T.card : ℝ) ≤ 3 * (T0.card : ℝ) := by exact_mod_cast hTcard
  have hTcountSmall : (T.card : ℝ) ≤
      3 * Real.exp ((p.n : ℝ) ^ (b₀ / 4)) := by
    exact hTcardReal.trans (mul_le_mul_of_nonneg_left hT0count (by norm_num))
  have hU : 3 ≤ (p.n : ℝ) ^ (b₀ / 4) := hAbsorbAll p.n hnAbsorb
  have hU2 : ((p.n : ℝ) ^ (b₀ / 4)) * ((p.n : ℝ) ^ (b₀ / 4)) =
      (p.n : ℝ) ^ (b₀ / 2) := by
    calc
      _ = (p.n : ℝ) ^ ((b₀ / 4) + (b₀ / 4)) :=
        (Real.rpow_add hnpos _ _).symm
      _ = _ := by congr 1 <;> ring
  have hlog3 : Real.log 3 ≤ 3 := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).2
    have h := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hAbsorb : 3 * Real.exp ((p.n : ℝ) ^ (b₀ / 4)) ≤
      Real.exp ((p.n : ℝ) ^ (b₀ / 2)) := by
    let u := (p.n : ℝ) ^ (b₀ / 4)
    have hu : 3 ≤ u := hU
    have hlog : Real.log 3 + u ≤ u * u := by
      dsimp [u]
      nlinarith [hlog3, hU]
    calc
      3 * Real.exp u = Real.exp (Real.log 3 + u) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
      _ ≤ Real.exp (u * u) := Real.exp_le_exp.mpr hlog
      _ = Real.exp ((p.n : ℝ) ^ (b₀ / 2)) := by rw [← hU2]
  have hTcount : (T.card : ℝ) ≤ Real.exp ((p.n : ℝ) ^ (b₀ / 2)) :=
    hTcountSmall.trans hAbsorb
  have hForall : ∀ (Esel : (p.Loc → Bool) → p.EligMap),
      (p.posLaw.prod p.actLaw).pr (fun ω =>
        relLegal p C Dom s ω.1 (Esel ω.1) x R ∧
          relFail p C Dom t η ω.1 ω.2 (Esel ω.1) x R) ≤ (T.card : ℝ) * δsite := by
    intro Esel
    let siteBad (v : CubeVertex p.d) (j : Fin (p.H + 1))
        (P A : p.Loc → Bool) : Prop :=
      relLegal p C Dom s P (Esel P) x R ∧
        (v, j.val) ∈ Dom ∧ hdScaleDistance p.D x (v, j.val) < 2 * R ∧
          relBadAt p C t P A (Esel P) v j
    have hLocal : ∀ v : CubeVertex p.d, ∀ j : Fin (p.H + 1),
        (p.posLaw.prod p.actLaw).pr (fun ω => siteBad v j ω.1 ω.2) ≤ δsite := by
      intro v j
      let Reg := heightCrowdRegion v j
      let μ : ℝ := (Reg.card : ℝ) * (p.lam / (p.V : ℝ))
      let posCount : (p.Loc → Bool) → ℝ := fun P =>
        (heightCrowdIDs P v j).card
      let posBad : (p.Loc → Bool) → Prop := fun P =>
        posCount P ≤ μ / 2 ∨ (11 / 10 : ℝ) * μ < posCount P
      have hposTails := position_count_tails Reg hqP0 hqP1
      have hposUpper := position_count_upper_eleven_tenths Reg hqP0 hqP1
      have hposBad : p.posLaw.pr posBad ≤
          Real.exp (-μ / 8) + Real.exp (-μ / 210) := by
        have hlow : p.posLaw.pr (fun P => posCount P ≤ μ / 2) ≤ Real.exp (-μ / 8) := by
          simpa [posCount, μ, Reg, heightCrowdIDs_card_eq_position_count] using hposTails.1
        have hhigh : p.posLaw.pr (fun P =>
            (11 / 10 : ℝ) * μ < posCount P) ≤ Real.exp (-μ / 210) := by
          simpa [posCount, μ, Reg, heightCrowdIDs_card_eq_position_count, mul_assoc] using hposUpper
        calc
          _ ≤ p.posLaw.pr (fun P => posCount P ≤ μ / 2) +
              p.posLaw.pr (fun P => (11 / 10 : ℝ) * μ < posCount P) := pr_or_le _ _ _
          _ ≤ _ := add_le_add hlow hhigh
      have hregion := heightCrowdRegion_volume_bounds v j hGeom.1 hGeom.2.1
      have hproduct : (p.lam / (p.V : ℝ)) *
          ((p.n : ℝ) ^ p.b₀ / p.lam) = (p.n : ℝ) ^ p.b₀ / (p.V : ℝ) := by
        field_simp [hlamPos.ne', hVpos.ne']
      have hregionLower : (p.n : ℝ) ^ p.b₀ ≤
          (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) *
            ((p.n : ℝ) ^ p.b₀ / p.lam) := by
        calc
          (p.n : ℝ) ^ p.b₀ = (p.V : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) := by
            field_simp [hVpos.ne']
          _ ≤ (Reg.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) :=
            mul_le_mul_of_nonneg_right hregion.1
              (div_nonneg (Real.rpow_nonneg hnpos.le _) hVpos.le)
          _ = _ := by rw [← hproduct]; ring
      have hratio : (Reg.card : ℝ) / (p.V : ℝ) ≤
          1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D := by
        apply (div_le_iff₀ hVpos).2
        nlinarith [hregion.2]
      have hregionUpper : 4 * (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) *
          ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (p.n : ℝ) ^ p.b := by
        calc
          _ = 4 * (Reg.card : ℝ) *
              ((p.lam / (p.V : ℝ)) * ((p.n : ℝ) ^ p.b₀ / p.lam)) := by ring
          _ = 4 * (Reg.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / (p.V : ℝ)) := by
            rw [hproduct]
          _ = 4 * (p.n : ℝ) ^ p.b₀ * ((Reg.card : ℝ) / (p.V : ℝ)) := by ring
          _ ≤ 4 * (p.n : ℝ) ^ p.b₀ *
              (1 + (p.D : ℝ) * ((p.d : ℝ) / p.r) ^ p.D) :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ ≤ (p.n : ℝ) ^ p.b := hGeomBand
      have hLamFactor' : 30 * (p.n : ℝ) ^ p.b₀ ≤
          (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) := by
        have hμ : p.lam ≤ (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) := by
          calc
            p.lam = (p.V : ℝ) * (p.lam / (p.V : ℝ)) := by field_simp [hVpos.ne']
            _ ≤ (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) :=
              mul_le_mul_of_nonneg_right hregion.1 (div_nonneg hlamPos.le hVpos.le)
        exact hlamFactor.trans hμ
      have hpos1 : Real.exp (-((Reg.card : ℝ) * (p.lam / (p.V : ℝ)) / 8)) ≤
          Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
        apply Real.exp_le_exp.mpr
        have hx := Real.rpow_nonneg hnpos.le p.b₀
        have hsmall : (p.n : ℝ) ^ p.b₀ ≤ (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) := by
          calc
            (p.n : ℝ) ^ p.b₀ = 1 * (p.n : ℝ) ^ p.b₀ := by ring
            _ ≤ 30 * (p.n : ℝ) ^ p.b₀ :=
              mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 30) hx
            _ ≤ _ := hLamFactor'
        have hdiv := div_le_div_of_nonneg_right hsmall (by norm_num : (0 : ℝ) ≤ 8)
        convert neg_le_neg hdiv using 1 <;> ring
      have hpos2 : Real.exp (-((Reg.card : ℝ) * (p.lam / (p.V : ℝ)) / 210)) ≤
          Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
        apply Real.exp_le_exp.mpr
        have hx := Real.rpow_nonneg hnpos.le p.b₀
        have h210 : 210 * (p.n : ℝ) ^ p.b₀ ≤ 240 * (p.n : ℝ) ^ p.b₀ :=
          mul_le_mul_of_nonneg_right (by norm_num : (210 : ℝ) ≤ 240) hx
        have h240 : 240 * (p.n : ℝ) ^ p.b₀ ≤
            8 * ((Reg.card : ℝ) * (p.lam / (p.V : ℝ))) := by
          calc
            _ = 8 * (30 * (p.n : ℝ) ^ p.b₀) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hLamFactor' (by norm_num)
        have hscaled := h210.trans h240
        have hdiv := div_le_div_of_nonneg_right hscaled (by norm_num : (0 : ℝ) ≤ 1680)
        have hterm : (p.n : ℝ) ^ p.b₀ / 8 ≤
            ((Reg.card : ℝ) * (p.lam / (p.V : ℝ))) / 210 := by
          calc
            _ = (210 * (p.n : ℝ) ^ p.b₀) / 1680 := by ring
            _ ≤ (8 * ((Reg.card : ℝ) * (p.lam / (p.V : ℝ))) / 1680) := hdiv
            _ = _ := by ring
        convert neg_le_neg hterm using 1 <;> ring
      have hqA0 : 0 < (p.n : ℝ) ^ p.b₀ / p.lam :=
        div_pos (Real.rpow_pos_of_pos hnpos _) hlamPos
      have hqA1 : (p.n : ℝ) ^ p.b₀ / p.lam ≤ 1 := (div_le_one hlamPos).2 hlamLower
      have hsections : ∀ P : p.Loc → Bool, ¬ posBad P →
          p.actLaw.pr (siteBad v j P) ≤
            2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
        intro P hnotBad
        by_cases hcond : relLegal p C Dom s P (Esel P) x R ∧
            (v, j.val) ∈ Dom ∧ hdScaleDistance p.D x (v, j.val) < 2 * R
        · have hlegal := hcond.1 v j hcond.2.1 hcond.2.2
          let EAt := ((Esel P) v j).filter (fun ℓ => ℓ ∈ C)
          have hsize : s * p.lam ≤ (EAt.card : ℝ) := by
            simpa [EAt] using hlegal.2
          have hposLow : μ / 2 < (heightCrowdIDs P v j).card := by
            have hnot : ¬ (heightCrowdIDs P v j).card ≤ μ / 2 := by
              intro h
              exact hnotBad (Or.inl (by simpa [posCount] using h))
            exact lt_of_not_ge hnot
          have hposHigh : (heightCrowdIDs P v j).card ≤ (11 / 10 : ℝ) * μ := by
            have hnot : ¬ (11 / 10 : ℝ) * μ < (heightCrowdIDs P v j).card := by
              intro h
              exact hnotBad (Or.inr (by simpa [posCount] using h))
            exact le_of_not_gt hnot
          have hmeanLower : (p.n : ℝ) ^ p.b₀ / 2 ≤
              (heightCrowdIDs P v j).card * ((p.n : ℝ) ^ p.b₀ / p.lam) := by
            have hprod := mul_le_mul_of_nonneg_right hposLow.le hqA0.le
            dsimp [μ] at hprod
            have hhalf : (p.n : ℝ) ^ p.b₀ / 2 ≤
                ((Reg.card : ℝ) * (p.lam / (p.V : ℝ)) *
                  ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2 :=
              div_le_div_of_nonneg_right hregionLower (by norm_num)
            calc
              _ ≤ _ := hhalf
              _ = (μ / 2) * ((p.n : ℝ) ^ p.b₀ / p.lam) := by dsimp [μ]; ring
              _ ≤ _ := hprod
          have hmeanUpper : 2 * (heightCrowdIDs P v j).card *
              ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ t * (p.n : ℝ) ^ p.b := by
            have hprod := mul_le_mul_of_nonneg_right hposHigh hqA0.le
            have hfirst : 2 * (heightCrowdIDs P v j).card *
                ((p.n : ℝ) ^ p.b₀ / p.lam) ≤ (11 / 20 : ℝ) * (p.n : ℝ) ^ p.b := by
              calc
                2 * (heightCrowdIDs P v j).card *
                    ((p.n : ℝ) ^ p.b₀ / p.lam) =
                      2 * ((heightCrowdIDs P v j).card *
                        ((p.n : ℝ) ^ p.b₀ / p.lam)) := by ring
                _ ≤ 2 * ((11 / 10 : ℝ) * μ * ((p.n : ℝ) ^ p.b₀ / p.lam)) :=
                  mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)
                _ = (11 / 5 : ℝ) * μ * ((p.n : ℝ) ^ p.b₀ / p.lam) := by ring
                _ ≤ (11 / 20 : ℝ) * (p.n : ℝ) ^ p.b := by
                  have hu : 4 * μ * ((p.n : ℝ) ^ p.b₀ / p.lam) ≤
                      (p.n : ℝ) ^ p.b := by simpa [μ, mul_assoc] using hregionUpper
                  calc
                    _ = (11 / 20 : ℝ) *
                        (4 * μ * ((p.n : ℝ) ^ p.b₀ / p.lam)) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left hu (by norm_num)
            exact hfirst.trans (mul_le_mul_of_nonneg_right htLower
              (Real.rpow_nonneg hnpos.le _))
          have hsubset : ∀ A : p.Loc → Bool, siteBad v j P A →
              (∀ ℓ ∈ EAt, A ℓ = false) ∨
                t * (p.n : ℝ) ^ p.b <
                  ∑ ℓ, if ℓ ∈ heightCrowdIDs P v j ∧ A ℓ = true then (1 : ℝ) else 0 := by
            intro A hA
            rcases hA.2.2.2 with hhole | hcrowd
            · exact Or.inl (by
                intro ℓ hℓ
                have hℓ' := Finset.mem_filter.mp hℓ
                exact hhole ℓ hℓ'.1 hℓ'.2)
            · right
              have hcard : relCrowd p C P A v j ≤
                  (Finset.univ.filter (fun u : CubeVertex p.d =>
                    P (u, j) = true ∧ A (u, j) = true ∧
                      _root_.hammingDist u v ≤ p.r + p.D)).card := by
                unfold relCrowd
                apply Finset.card_le_card
                intro u hu
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
                rcases hu with ⟨hC, hP, hA', hdist⟩
                exact ⟨hP, hA', hdist⟩
              have hcardReal : (relCrowd p C P A v j : ℝ) ≤
                  ((Finset.univ.filter (fun u : CubeVertex p.d =>
                    P (u, j) = true ∧ A (u, j) = true ∧
                      _root_.hammingDist u v ≤ p.r + p.D)).card : ℝ) := by
                exact_mod_cast hcard
              calc
                t * (p.n : ℝ) ^ p.b < (relCrowd p C P A v j : ℝ) := hcrowd
                _ ≤ _ := hcardReal
                _ = _ := (height_crowd_active_count_eq P A v j).symm
          have hact := activation_hole_or_crowd EAt (heightCrowdIDs P v j)
            (t * (p.n : ℝ) ^ p.b) hmeanUpper hqA0 hqA1
          have hbadProb : p.actLaw.pr (fun A =>
              relBadAt p C t P A (Esel P) v j) ≤
                Real.exp (-((EAt.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) +
                  Real.exp (-((heightCrowdIDs P v j).card *
                    ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) := by
            calc
              _ ≤ p.actLaw.pr (fun A => (∀ ℓ ∈ EAt, A ℓ = false) ∨
                  t * (p.n : ℝ) ^ p.b <
                    ∑ ℓ, if ℓ ∈ heightCrowdIDs P v j ∧ A ℓ = true then (1 : ℝ) else 0) :=
                      pr_mono _ _ _ (fun A hA => hsubset A (by
                        exact ⟨hcond.1, hcond.2.1, hcond.2.2, hA⟩))
              _ ≤ _ := hact
          have hlamq : p.lam * ((p.n : ℝ) ^ p.b₀ / p.lam) = (p.n : ℝ) ^ p.b₀ := by
            field_simp [hlamPos.ne']
          have hHoleMean : s * (p.n : ℝ) ^ p.b₀ ≤
              (EAt.card : ℝ) * ((p.n : ℝ) ^ p.b₀ / p.lam) := by
            calc
              _ = s * (p.lam * ((p.n : ℝ) ^ p.b₀ / p.lam)) := by rw [hlamq]
              _ = (s * p.lam) * ((p.n : ℝ) ^ p.b₀ / p.lam) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hsize hqA0.le
          have hHoleExp : Real.exp (-((EAt.card : ℝ) *
              ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) ≤
                Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) := by
            apply Real.exp_le_exp.mpr
            have hdiv := div_le_div_of_nonneg_right hHoleMean
              (by norm_num : (0 : ℝ) ≤ 2)
            convert neg_le_neg hdiv using 1 <;> try ring
          have hCrowdExp : Real.exp (-((heightCrowdIDs P v j).card *
              ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) ≤
                Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) := by
            apply Real.exp_le_exp.mpr
            have hdiv := div_le_div_of_nonneg_right hmeanLower
              (by norm_num : (0 : ℝ) ≤ 3)
            convert neg_le_neg hdiv using 1 <;> try ring
          have hholeSmall : Real.exp (-s * (p.n : ℝ) ^ p.b₀ / 2) ≤
              Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
            apply Real.exp_le_exp.mpr
            have hx := Real.rpow_nonneg hnpos.le p.b₀
            have hcoef := mul_le_mul_of_nonneg_right hs hx
            have hdiv := div_le_div_of_nonneg_right hcoef (by norm_num : (0 : ℝ) ≤ 2)
            have hscaled : ((1 / 4 : ℝ) * (p.n : ℝ) ^ p.b₀) / 2 ≤
                (s * (p.n : ℝ) ^ p.b₀) / 2 := hdiv
            have hneg := neg_le_neg hscaled
            convert hneg using 1 <;> ring
          have hcrowdSmall : Real.exp (-((p.n : ℝ) ^ p.b₀) / 6) ≤
              Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
            apply Real.exp_le_exp.mpr
            have hx := Real.rpow_nonneg hnpos.le p.b₀
            have hdiv : ((p.n : ℝ) ^ p.b₀) / 8 ≤ ((p.n : ℝ) ^ p.b₀) / 6 := by
              exact div_le_div_of_nonneg_left hx (by norm_num : (0 : ℝ) < 6)
                (by norm_num : (6 : ℝ) ≤ 8)
            have hneg := neg_le_neg hdiv
            convert hneg using 1 <;> ring
          have hmono : p.actLaw.pr (siteBad v j P) ≤
              p.actLaw.pr (fun A => relBadAt p C t P A (Esel P) v j) := by
            apply pr_mono
            intro A hA
            exact hA.2.2.2
          calc
            _ ≤ _ := hmono.trans hbadProb
            _ ≤ 2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
              have hholeBound := hHoleExp.trans hholeSmall
              have hcrowdBound := hCrowdExp.trans hcrowdSmall
              calc
                Real.exp (-((EAt.card : ℝ) *
                    ((p.n : ℝ) ^ p.b₀ / p.lam)) / 2) +
                  Real.exp (-((heightCrowdIDs P v j).card *
                    ((p.n : ℝ) ^ p.b₀ / p.lam)) / 3) ≤
                  Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) +
                    Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) :=
                      add_le_add hholeBound hcrowdBound
                _ = _ := by ring
        · have hzero : p.actLaw.pr (siteBad v j P) = 0 := by
            have hevent : (fun A => siteBad v j P A) = fun _ => False := by
              funext A
              apply propext
              constructor
              · intro hA
                exact hcond ⟨hA.1, hA.2.1, hA.2.2.1⟩
              · intro hfalse
                exact False.elim hfalse
            change p.actLaw.pr (fun A => siteBad v j P A) = 0
            rw [hevent]
            simp [FinProb.pr]
          rw [hzero]
          positivity
      have hsitePr := finprob_prod_pr_le_bad_or_small p.posLaw p.actLaw posBad
        (siteBad v j) (2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8)) (by positivity) hsections
      calc
        _ ≤ p.posLaw.pr posBad + 2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := hsitePr
        _ ≤ _ := by
          have hposBad' : p.posLaw.pr posBad ≤
              2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
            calc
              _ ≤ Real.exp (-μ / 8) + Real.exp (-μ / 210) := hposBad
              _ ≤ _ := by
                have hmu : p.lam ≤ (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) := by
                  calc
                    p.lam = (p.V : ℝ) * (p.lam / (p.V : ℝ)) := by
                      field_simp [hVpos.ne']
                    _ ≤ (Reg.card : ℝ) * (p.lam / (p.V : ℝ)) :=
                      mul_le_mul_of_nonneg_right hregion.1 (div_nonneg hlamPos.le hVpos.le)
                have hmuLarge : 30 * (p.n : ℝ) ^ p.b₀ ≤ μ := by
                  simpa [μ] using hLamFactor'
                have hterm1 : Real.exp (-μ / 8) ≤
                    Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
                  apply Real.exp_le_exp.mpr
                  have hx := hlamLower.trans hmu
                  have hdiv := div_le_div_of_nonneg_right hx
                    (by norm_num : (0 : ℝ) ≤ 8)
                  convert neg_le_neg hdiv using 1 <;> ring
                have hterm2 : Real.exp (-μ / 210) ≤
                    Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by
                  apply Real.exp_le_exp.mpr
                  have hx := Real.rpow_nonneg hnpos.le p.b₀
                  have h210 : 210 * (p.n : ℝ) ^ p.b₀ ≤ 240 * (p.n : ℝ) ^ p.b₀ :=
                    mul_le_mul_of_nonneg_right (by norm_num : (210 : ℝ) ≤ 240) hx
                  have h240 : 240 * (p.n : ℝ) ^ p.b₀ ≤ 8 * μ := by
                    calc
                      _ = 8 * (30 * (p.n : ℝ) ^ p.b₀) := by ring
                      _ ≤ _ := mul_le_mul_of_nonneg_left hmuLarge (by norm_num)
                  have hscaled := h210.trans h240
                  have hdiv := div_le_div_of_nonneg_right hscaled
                    (by norm_num : (0 : ℝ) ≤ 1680)
                  have hbound : (p.n : ℝ) ^ p.b₀ / 8 ≤ μ / 210 := by
                    calc
                      _ = (210 * (p.n : ℝ) ^ p.b₀) / 1680 := by ring
                      _ ≤ (8 * μ) / 1680 := hdiv
                      _ = _ := by ring
                  convert neg_le_neg hbound using 1 <;> ring
                linarith [hterm1, hterm2]
          calc
            p.posLaw.pr posBad + 2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) ≤
                2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) +
                  2 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) :=
              add_le_add hposBad' le_rfl
            _ = 4 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8) := by ring
    have hFailSubset : ∀ ω : (p.Loc → Bool) × (p.Loc → Bool),
        (relLegal p C Dom s ω.1 (Esel ω.1) x R ∧
          relFail p C Dom t η ω.1 ω.2 (Esel ω.1) x R) →
        ∃ y ∈ T, siteBad y.1 y.2 ω.1 ω.2 := by
      intro ω hω
      have hfail : hdScaleThresholdFailure (Finset.univ : p.Sites)
          (relBad p C Dom t ω.1 ω.2 (Esel ω.1)) x R η := by
        simpa [relFail] using hω.2
      obtain ⟨v, k, hv, hbad, hdist⟩ := hdScaleThresholdFailure_has_local_bad
        (Finset.univ : p.Sites) (relBad p C Dom t ω.1 ω.2 (Esel ω.1)) x R η
        hDpos (by omega) (by linarith [hη]) hfail
      have hbad' : (v, k) ∈ Dom ∧
          ∃ hk : k < p.H + 1, relBadAt p C t ω.1 ω.2 (Esel ω.1) v ⟨k, hk⟩ := by
        simpa [relBad] using hbad
      rcases hbad' with ⟨hDom, hk, hbadAt⟩
      let j : Fin (p.H + 1) := ⟨k, hk⟩
      have hdist2 : hdScaleDistance p.D x (v, k) < 2 * R := by omega
      have hmemT : (v, j) ∈ T := by
        simp [T, hdScaleBallSiteLevels, j, hdist]
      exact ⟨(v, j), hmemT, hω.1, hDom, by simpa [j] using hdist2,
        by simpa [j] using hbadAt⟩
    have hUnion : (p.posLaw.prod p.actLaw).pr (fun ω =>
        relLegal p C Dom s ω.1 (Esel ω.1) x R ∧
          relFail p C Dom t η ω.1 ω.2 (Esel ω.1) x R) ≤ (T.card : ℝ) * δsite := by
      calc
        _ ≤ (p.posLaw.prod p.actLaw).pr (fun ω =>
            ∃ y ∈ T, siteBad y.1 y.2 ω.1 ω.2) :=
          pr_mono _ _ _ (fun ω hω => hFailSubset ω hω)
        _ ≤ ∑ y ∈ T, (p.posLaw.prod p.actLaw).pr
            (fun ω => siteBad y.1 y.2 ω.1 ω.2) :=
          pr_finset_exists_le (p.posLaw.prod p.actLaw) T
            (fun y ω => siteBad y.1 y.2 ω.1 ω.2)
        _ ≤ ∑ y ∈ T, δsite := by
          apply Finset.sum_le_sum
          intro y hy
          exact hLocal y.1 y.2
        _ = (T.card : ℝ) * δsite := by simp
    exact hUnion
  let val (P : p.Loc → Bool) (E : p.EligMap) : ℝ :=
    if relLegal p C Dom s P E x R then
      p.actLaw.pr (fun A => relFail p C Dom t η P A E x R)
    else 0
  have hmax : ∀ P : p.Loc → Bool,
      ∃ E, E ∈ (Finset.univ : Finset p.EligMap) ∧
        relSup p C Dom s t η x R P = val P E := by
    intro P
    unfold relSup
    exact Finset.exists_mem_eq_sup' Finset.univ_nonempty (val P)
  let Esel : (p.Loc → Bool) → p.EligMap := fun P => Classical.choose (hmax P)
  have hEsel : ∀ P : p.Loc → Bool,
      relSup p C Dom s t η x R P = val P (Esel P) :=
    fun P => (Classical.choose_spec (hmax P)).2
  have hscore : ∀ P : p.Loc → Bool,
      val P (Esel P) = p.actLaw.pr (fun A =>
        relLegal p C Dom s P (Esel P) x R ∧ relFail p C Dom t η P A (Esel P) x R) := by
    intro P
    by_cases hlegal : relLegal p C Dom s P (Esel P) x R
    · simp [val, hlegal, FinProb.pr]
    · simp [val, hlegal, FinProb.pr]
  have hExpEq : p.posLaw.expect (relSup p C Dom s t η x R) =
      (p.posLaw.prod p.actLaw).pr (fun ω =>
        relLegal p C Dom s ω.1 (Esel ω.1) x R ∧
          relFail p C Dom t η ω.1 ω.2 (Esel ω.1) x R) := by
    calc
      _ = p.posLaw.expect (fun P => val P (Esel P)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro P hP
        rw [hEsel P]
      _ = p.posLaw.expect (fun P => p.actLaw.pr (fun A =>
          relLegal p C Dom s P (Esel P) x R ∧
            relFail p C Dom t η P A (Esel P) x R)) := by
        unfold FinProb.expect
        apply Finset.sum_congr rfl
        intro P hP
        change p.posLaw.w P * val P (Esel P) = _
        rw [hscore P]
      _ = _ := by
        simpa [FinProb.expect] using
          (prod_pr_eq_sections p.posLaw p.actLaw (fun P A =>
            relLegal p C Dom s P (Esel P) x R ∧
              relFail p C Dom t η P A (Esel P) x R)).symm
  have hProbability : p.posLaw.expect (relSup p C Dom s t η x R) ≤
      (T.card : ℝ) * δsite := by rw [hExpEq]; exact hForall Esel
  calc
    p.posLaw.expect (relSup p C Dom s t η x R) ≤ (T.card : ℝ) * δsite := hProbability
    _ ≤ Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
        (4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by
      calc
        _ ≤ Real.exp ((p.n : ℝ) ^ (b₀ / 2)) * δsite :=
          mul_le_mul_of_nonneg_right hTcount (by positivity)
        _ = Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
            (4 * Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by
              change Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
                (4 * Real.exp (-((p.n : ℝ) ^ p.b₀) / 8)) = _
              rw [show (p.n : ℝ) ^ p.b₀ = (p.n : ℝ) ^ b₀ by rw [hstd.hb₀]]
    _ = 4 * Real.exp ((p.n : ℝ) ^ (b₀ / 2) - (p.n : ℝ) ^ b₀ / 8) := by
      calc
        _ = 4 * (Real.exp ((p.n : ℝ) ^ (b₀ / 2)) *
            Real.exp (-((p.n : ℝ) ^ b₀) / 8)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (-((p.n : ℝ) ^ a * (heightBaseRadius p.n : ℝ) ^ θ)) :=
      hArithAll p.n hnArith

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
  classical
  let bad := relBad p C Dom t P A E
  change hdScaleThresholdFailure (Finset.univ : p.Sites) bad x (M * R') ηP at hfail
  rcases hfail with ⟨finish, hwalkNonempty, hnet⟩
  let walk : HDThresholdWalk (Finset.univ : p.Sites) bad x (M * R') x finish :=
    Classical.choice hwalkNonempty
  obtain ⟨chunks, suffix, hchunk⟩ :=
    hdThresholdWalk_exists_chunking (Finset.univ : p.Sites) bad x (M * R') R' hD hR' walk
  have chunkStartBounds :
      ∀ {start finish : HDState p}
        (parentWalk : HDThresholdWalk (Finset.univ : p.Sites) bad x (M * R') start finish)
        (chunkList : List (HDChunk p (Finset.univ : p.Sites) bad R'))
        (tailWalk : Σ suffixStart : HDState p,
          HDThresholdWalk (Finset.univ : p.Sites) bad x (M * R') suffixStart finish),
        HDThresholdChunking (Finset.univ : p.Sites) bad x (M * R') R'
          parentWalk chunkList tailWalk →
        ∀ c ∈ chunkList,
          hdScaleDistance p.D x c.1 < M * R' ∧ c.1.2 ≤ p.H := by
    intro start finish parentWalk chunkList tailWalk hchunk
    induction hchunk with
    | done hinside => intro c hc; simp at hc
    | @more start finish middle chunks suffixStart walk childWalk rest suffix hcut htail ih =>
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with hc | hc
        · subst c
          change hdScaleDistance p.D x start < M * R' ∧ start.2 ≤ p.H
          have hstart : hdScaleDistance p.D x start < M * R' ∧ start.2 ≤ p.H := by
            cases hcut with
            | upExit hparent _ hj _ _ _ _ =>
                exact ⟨by simpa using hparent, by simpa using (Nat.le_of_lt hj)⟩
            | upContinue hparent _ hj _ _ _ _ _ =>
                exact ⟨by simpa using hparent, by simpa using (Nat.le_of_lt hj)⟩
            | downExit hparent _ hj _ _ _ _ =>
                exact ⟨by simpa using hparent, by omega⟩
            | downContinue hparent _ hj _ _ _ _ _ =>
                exact ⟨by simpa using hparent, by omega⟩
          exact hstart
        · exact ih c hc
  have hstartBounds : ∀ c ∈ chunks,
      hdScaleDistance p.D x c.1 < M * R' ∧ c.1.2 ≤ p.H :=
    chunkStartBounds walk chunks suffix hchunk
  have walkFinishOutside :
      ∀ {start finish : HDState p},
        HDThresholdWalk (Finset.univ : p.Sites) bad x (M * R') start finish →
          M * R' ≤ hdScaleDistance p.D x finish := by
    intro start finish w
    induction w with
    | stop hstop => exact hstop
    | up _ _ _ _ _ ih => exact ih
    | down _ _ _ _ _ ih => exact ih
  have hboundary : M * R' ≤ hdScaleDistance p.D x finish := walkFinishOutside walk
  have hparentNet : -(ηP * ((M * R' : ℕ) : ℝ)) ≤ (finish.2 : ℝ) - x.2 := by
    simpa using hnet
  have hηC0 : 0 ≤ ηC := le_trans hηP hηPC.le
  let K₀ : ℕ := 2 * K + 1
  let δ : ℝ := (q : ℝ) / (M : ℝ)
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hδM : δ * (M : ℝ) = (q : ℝ) := by
    dsimp [δ]
    field_simp
  have hK₀cast : (K₀ : ℝ) = 2 * (K : ℝ) + 1 := by
    dsimp [K₀]
    push_cast
    ring
  have hgap : 0 < K * R' := Nat.mul_pos (by omega) hR'
  have hbudget : 2 * (K * R') + R' = K₀ * R' := by
    dsimp [K₀]
    ring
  have hlarge' :
      (1 + ηC) * (K₀ : ℝ) * δ * (M : ℝ) + (1 + ηC) <
        (ηC - ηP) * (M : ℝ) := by
    calc
      (1 + ηC) * (K₀ : ℝ) * δ * (M : ℝ) + (1 + ηC) =
          (1 + ηC) * (K₀ : ℝ) * (δ * (M : ℝ)) + (1 + ηC) := by ring
      _ = (1 + ηC) * (2 * (K : ℝ) + 1) * (q : ℝ) + (1 + ηC) := by
            rw [hK₀cast, hδM]
      _ < (ηC - ηP) * (M : ℝ) := hlarge
  obtain ⟨S, hSsubset, hSsep, hScard⟩ :=
    hdParentFailure_has_many_separated_child_failure_starts
      (p := p) hD (Sites := Finset.univ) (bad := bad)
      (parentOrigin := x) (start := x) (finish := finish)
      (parentRadius := M * R') (childRadius := R') (gap := K * R')
      (M := M) (K := K₀) (ηParent := ηP) (ηChild := ηC) (δ := δ)
      (walk := walk) (chunks := chunks) (suffix := suffix)
      hchunk hM hR' hgap hbudget hηP hηC0 hηPC hlarge' hboundary hparentNet
  have hqreal : (q : ℝ) ≤ (S.card : ℝ) := by
    calc
      (q : ℝ) = δ * (M : ℝ) := hδM.symm
      _ ≤ (S.card : ℝ) := hScard
  have hq : q ≤ S.card := by exact_mod_cast hqreal
  obtain ⟨Y, hYS, hYcard⟩ := Finset.exists_subset_card_eq hq
  have Sprops : ∀ y ∈ S,
      y ∈ scaleBall p x (M * R') ∧ relFail p C Dom t ηC P A E y R' := by
    intro y hy
    have hySet : y ∈ hdFailureStartSet ηC chunks := hSsubset hy
    unfold hdFailureStartSet at hySet
    rcases Finset.mem_image.mp hySet with ⟨c, hcFiltered, hcy⟩
    have hcFilter := Finset.mem_filter.mp hcFiltered
    have hcList : c ∈ chunks := by simpa using hcFilter.1
    have hcFail : hdThresholdChunkFailure ηC c := hcFilter.2
    have hbounds := hstartBounds c hcList
    have hballC : c.1 ∈ scaleBall p x (M * R') := by
      unfold scaleBall
      apply Finset.mem_image.mpr
      refine ⟨(c.1.1, ⟨c.1.2, by omega⟩),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa using hbounds.1
      · rfl
    have hfailC : relFail p C Dom t ηC P A E c.1 R' := by
      change hdScaleThresholdFailure (Finset.univ : p.Sites) bad c.1 R' ηC
      rcases c with ⟨childStart, ⟨childFinish, childWalk⟩⟩
      have hchildNet : -(ηC * (R' : ℝ)) ≤
          (childFinish.2 : ℝ) - childStart.2 := by
        simpa [hdThresholdChunkFailure, hdThresholdChunkRise] using hcFail
      exact ⟨childFinish, ⟨childWalk⟩, hchildNet⟩
    have hball : y ∈ scaleBall p x (M * R') := by
      rw [← hcy]
      exact hballC
    have hfailY : relFail p C Dom t ηC P A E y R' := by
      simpa [hcy] using hfailC
    exact ⟨hball, hfailY⟩
  have hYball : Y ⊆ scaleBall p x (M * R') := by
    intro y hy
    exact (Sprops y (hYS hy)).1
  have hYsep : Separated p (K * R') Y := by
    intro y hy y' hy' hne
    exact hSsep y (hYS hy) y' (hYS hy') hne
  refine ⟨Y, ?_, ?_⟩
  · unfold configs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr hYball, ?_⟩
    exact ⟨hYcard, hYsep⟩
  · intro y hy
    exact (Sprops y (hYS hy)).2

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

set_option maxHeartbeats 1200000 in
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
  have hσ : 0 < σ := hp.hsz.1
  have hσζ : σ < ζ := hp.hsz.2.1
  have hζ : ζ < 1 := hp.hsz.2.2.1
  have hθ : 0 < θ := hp.hsz.2.2.2.1
  have hθ1 : θ < 1 := hp.hsz.2.2.2.2
  have ha : 0 < a := by linarith [hp.ha.1, hσ, hσζ, hζ]
  have hgapF : 0 < b - 4 * σ := by linarith [hp.ha.2.2, ha]
  have hgapBase : 0 < a - σ - (1 - ζ) * (1 - θ) := by
    have hζpos : 0 < ζ := by linarith [hσ, hσζ]
    have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
    have hprod : 0 < ζ * (1 - θ) := mul_pos hζpos h1θ
    nlinarith [hp.ha.1, hprod]
  have hgapTail : 0 < b - 2 * σ - (a + σ * θ) := by
    have hσθ : σ * θ < σ := by
      calc
        σ * θ < σ * 1 := mul_lt_mul_of_pos_left hθ1 hσ
        _ = σ := by ring
    nlinarith [hp.ha.2.2, hσθ]
  let δ : ℝ := min ((b - 4 * σ) / 2)
    ((a - σ - (1 - ζ) * (1 - θ)) / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδF : δ < b - 4 * σ := by
    dsimp [δ]
    have h1 : 0 < (b - 4 * σ) / 2 := by linarith
    have h2 : 0 < (a - σ - (1 - ζ) * (1 - θ)) / 2 := by linarith
    have hm : min ((b - 4 * σ) / 2)
        ((a - σ - (1 - ζ) * (1 - θ)) / 2) ≤ (b - 4 * σ) / 2 := min_le_left _ _
    linarith
  have hδBase : δ < a - σ - (1 - ζ) * (1 - θ) := by
    dsimp [δ]
    have h1 : 0 < (b - 4 * σ) / 2 := by linarith
    have h2 : 0 < (a - σ - (1 - ζ) * (1 - θ)) / 2 := by linarith
    have hm : min ((b - 4 * σ) / 2)
        ((a - σ - (1 - ζ) * (1 - θ)) / 2) ≤
          (a - σ - (1 - ζ) * (1 - θ)) / 2 := min_le_right _ _
    linarith
  have powerAbsorb : ∀ (C e f : ℝ), 0 ≤ C → e < f →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) ^ e ≤ (n : ℝ) ^ f := by
    intro C e f hC hef
    obtain ⟨N, hN⟩ := exists_nat_rpow_ge (e := f - e) (C := C) (sub_pos.mpr hef)
    refine ⟨max 1 N, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := le_trans (Nat.le_max_left 1 N) hn
    have hnN : N ≤ n := le_trans (Nat.le_max_right 1 N) hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hNpow : C ≤ (n : ℝ) ^ (f - e) := hN n hnN
    calc
      C * (n : ℝ) ^ e ≤ (n : ℝ) ^ (f - e) * (n : ℝ) ^ e :=
        mul_le_mul_of_nonneg_right hNpow (Real.rpow_nonneg hnpos.le _)
      _ = (n : ℝ) ^ f := by
        calc
          _ = (n : ℝ) ^ ((f - e) + e) := (Real.rpow_add hnpos (f - e) e).symm
          _ = _ := by congr 1 <;> ring
  let B : ℕ := ⌈1 / σ⌉₊
  let L : ℝ := 16 * ((B : ℝ) + 1) * (2 * (K : ℝ) + 1)
  let Ccount : ℝ := 18 * ((D + 1 : ℕ) : ℝ)
  let Cbase : ℝ := 2 * Ccount + Real.log 2
  let Xbase : ℝ := 2 * σ + δ + (1 - ζ) * (1 - θ)
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hCcount : 0 < Ccount := by
    dsimp [Ccount]
    positivity
  have hCbase : 0 < Cbase := by
    dsimp [Cbase]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hXbase : 0 ≤ Xbase := by
    dsimp [Xbase]
    positivity
  have hFexp : 0 < b - 2 * σ := by linarith [hgapF, hσ]
  have hTargetGap : a + σ * θ < b - 2 * σ := by linarith [hgapTail]
  have hCountGap : 2 * σ + δ < b - 2 * σ := by linarith [hgapF, hδF]
  have hBaseGap : Xbase < a + σ := by
    dsimp [Xbase]
    linarith [hδBase]
  obtain ⟨Nlog, hlogN⟩ := log_le_rpow_eventually δ hδ
  obtain ⟨Ncd, hcdN⟩ := exists_nat_rpow_ge (e := δ)
    (C := Real.log (C_d + 1)) hδ
  obtain ⟨N7, h7N⟩ := exists_nat_rpow_ge (e := δ)
    (C := Real.log 7) hδ
  obtain ⟨Nmult, hmultN⟩ := exists_nat_rpow_ge (e := σ) (C := 12 * L) hσ
  obtain ⟨Nq, hqN⟩ := exists_nat_rpow_ge (e := σ * (1 - θ)) (C := 12 * L)
    (mul_pos hσ (sub_pos.mpr hθ1))
  obtain ⟨NerrCount, herrCountN⟩ := powerAbsorb (3 * Ccount) (2 * σ + δ)
    (b - 2 * σ) (by positivity) hCountGap
  obtain ⟨NerrBase, herrBaseN⟩ := powerAbsorb 9 (a + σ * θ) (b - 2 * σ)
    (by norm_num) hTargetGap
  obtain ⟨NerrConst, herrConstN⟩ := powerAbsorb (3 * Real.log 4) 0 (b - 2 * σ)
    (by positivity) hFexp
  obtain ⟨Nbase, hbaseN⟩ := powerAbsorb (4 * L * Cbase) Xbase (a + σ)
    (by positivity) hBaseGap
  let N : ℕ := max 2 (max Nlog (max Ncd (max N7
    (max Nmult (max Nq (max NerrCount (max NerrBase (max NerrConst Nbase))))))))
  exact ⟨N, fun n d hn hdim i hi1 hih => by
    have hnAll := hn
    dsimp [N] at hnAll
    simp only [max_le_iff] at hnAll
    rcases hnAll with ⟨hn2, hNlog, hNcd, hN7, hNmult, hNq,
      hNerrCount, hNerrBase, hNerrConst, hNbase⟩
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    let h : ℕ := hdScaleIndex n σ ζ
    let M : ℕ := hdScaleMultiplier n σ
    let R : ℕ := hdScaleRadius n σ (i - 1)
    let q : ℕ := stepQ n σ ζ K
    let U : ℝ := ((h + 1 : ℕ) : ℝ)
    let den : ℝ := 16 * U * (2 * (K : ℝ) + 1)
    have hidx : h ≤ B := by
      dsimp [h, B]
      exact hdScaleIndex_le_ceil_inv_sigma hn2 hσ ⟨by linarith [hσ, hσζ], hζ⟩
    have hMlower : (n : ℝ) ^ σ ≤ (M : ℝ) := by
      have hceil : (n : ℝ) ^ σ ≤ (⌈(n : ℝ) ^ σ⌉₊ : ℝ) := by
        exact_mod_cast Nat.le_ceil ((n : ℝ) ^ σ)
      have hmax : ⌈(n : ℝ) ^ σ⌉₊ ≤ hdScaleMultiplier n σ := by
        unfold hdScaleMultiplier
        exact Nat.le_max_right _ _
      exact hceil.trans (by exact_mod_cast hmax)
    have hnσone : 1 ≤ (n : ℝ) ^ σ := by
      calc
        1 = (n : ℝ) ^ (0 : ℝ) := by simp
        _ ≤ (n : ℝ) ^ σ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hMupper : (M : ℝ) ≤ 3 * (n : ℝ) ^ σ := by
      have hceil : (⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ (n : ℝ) ^ σ + 1 :=
        (Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le σ)).le
      have hmax : (max 2 ⌈(n : ℝ) ^ σ⌉₊ : ℝ) ≤ 3 * (n : ℝ) ^ σ := by
        exact max_le (by nlinarith [hnσone]) (by nlinarith [hceil, hnσone])
      simpa [M, hdScaleMultiplier] using hmax
    have hRone : 1 ≤ R := by
      apply Nat.one_le_iff_ne_zero.mpr
      dsimp [R, hdScaleRadius]
      apply Nat.mul_ne_zero
      · apply pow_ne_zero
        dsimp [hdScaleMultiplier]
        omega
      · dsimp [heightBaseRadius]
        omega
    have hRpos : 0 < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    have hRoneR : 1 ≤ (R : ℝ) := by exact_mod_cast hRone
    have htargetOne : 1 ≤ (n : ℝ) ^ (1 - ζ) := by
      calc
        1 = (n : ℝ) ^ (0 : ℝ) := by simp
        _ ≤ (n : ℝ) ^ (1 - ζ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hζ])
    have hceilTargetLt :
        (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) < (n : ℝ) ^ (1 - ζ) + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg hnpos.le _)
    have hceilTargetLe :
        (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) := by
      nlinarith [hceilTargetLt, htargetOne]
    have hRprev : (R : ℝ) < (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := by
      have hspec := (hdScaleIndex_spec n σ ζ).2 (i - 1) (by omega)
      dsimp [R]
      exact_mod_cast hspec
    have hRupper : (R : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) :=
      le_trans hRprev.le hceilTargetLe
    have htopPrev :
        (hdScaleRadius n σ (h - 1) : ℝ) <
          (⌈(n : ℝ) ^ (1 - ζ)⌉₊ : ℝ) := by
      have hspec := (hdScaleIndex_spec n σ ζ).2 (h - 1) (by omega)
      dsimp [h]
      exact_mod_cast hspec
    have htopPrevLe :
        (hdScaleRadius n σ (h - 1) : ℝ) ≤ 2 * (n : ℝ) ^ (1 - ζ) :=
      le_trans htopPrev.le hceilTargetLe
    have hhpos : 1 ≤ h := by dsimp [h]; omega
    have hTopCast : (topScale n σ ζ : ℝ) =
        (M : ℝ) * (hdScaleRadius n σ (h - 1) : ℝ) := by
      rw [topScale_eq_hdScaleRadius, hdScaleRadius_pred n σ hhpos]
      simp [h, M, Nat.cast_mul]
    have hprodPow : (n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ) =
        (n : ℝ) ^ (1 - ζ + σ) := by
      calc
        _ = (n : ℝ) ^ (σ + (1 - ζ)) := (Real.rpow_add hnpos σ (1 - ζ)).symm
        _ = _ := by congr 1 <;> ring
    have htopScaleLe : (topScale n σ ζ : ℝ) ≤ 6 * (n : ℝ) := by
      rw [hTopCast]
      calc
        (M : ℝ) * (hdScaleRadius n σ (h - 1) : ℝ) ≤
            (3 * (n : ℝ) ^ σ) * (2 * (n : ℝ) ^ (1 - ζ)) :=
          mul_le_mul hMupper htopPrevLe (by positivity) (by positivity)
        _ = 6 * (n : ℝ) ^ (1 - ζ + σ) := by
          calc
            _ = 6 * ((n : ℝ) ^ σ * (n : ℝ) ^ (1 - ζ)) := by ring
            _ = _ := by rw [hprodPow]
        _ ≤ 6 * (n : ℝ) := by
          have hexp : (n : ℝ) ^ (1 - ζ + σ) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hσζ])
          have hpow : (n : ℝ) ^ (1 - ζ + σ) ≤ (n : ℝ) := by
            simpa only [Real.rpow_one] using hexp
          exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hTopPlus : ((topScale n σ ζ + 1 : ℕ) : ℝ) ≤ 7 * (n : ℝ) := by
      push_cast
      nlinarith [htopScaleLe, hn1]
    have hdPlus : ((d + 1 : ℕ) : ℝ) ≤ (C_d + 1) * (n : ℝ) := by
      have hdCast : (d : ℝ) ≤ C_d * n := by exact_mod_cast hdim
      push_cast
      nlinarith [hdCast, hn1]
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ := hlogN n hNlog
    have hlogCd : Real.log (C_d + 1) ≤ (n : ℝ) ^ δ := hcdN n hNcd
    have hlog7 : Real.log 7 ≤ (n : ℝ) ^ δ := h7N n hN7
    have hlogTop : Real.log ((topScale n σ ζ + 1 : ℕ) : ℝ) ≤
        2 * (n : ℝ) ^ δ := by
      calc
        _ ≤ Real.log (7 * (n : ℝ)) := Real.log_le_log (by positivity) hTopPlus
        _ = Real.log 7 + Real.log (n : ℝ) := by
          rw [Real.log_mul (by norm_num) hnpos.ne']
        _ ≤ 2 * (n : ℝ) ^ δ := by linarith [hlog7, hlogn]
    have hlogd : Real.log ((d + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ δ := by
      have hCdpos : 0 < C_d := lt_of_lt_of_le hp.hd.1 hp.hd.2
      calc
        _ ≤ Real.log ((C_d + 1) * (n : ℝ)) := Real.log_le_log (by positivity) hdPlus
        _ = Real.log (C_d + 1) + Real.log (n : ℝ) := by
          rw [Real.log_mul (by linarith [hCdpos]) hnpos.ne']
        _ ≤ 2 * (n : ℝ) ^ δ := by linarith [hlogCd, hlogn]
    have hdenPos : 0 < den := by
      dsimp [den, U]
      positivity
    have hdenBound : den ≤ L := by
      have hUbound : ((h + 1 : ℕ) : ℝ) ≤ (B : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ hidx
      have hfac : 0 ≤ 2 * (K : ℝ) + 1 := by positivity
      change 16 * U * (2 * (K : ℝ) + 1) ≤
        16 * ((B : ℝ) + 1) * (2 * (K : ℝ) + 1)
      calc
        16 * U * (2 * (K : ℝ) + 1) =
            (16 * U) * (2 * (K : ℝ) + 1) := by ring
        _ ≤ (16 * ((B : ℝ) + 1)) * (2 * (K : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUbound (by norm_num)) hfac
        _ = _ := by ring
    have hUone : 1 ≤ U := by
      dsimp [U]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le h)
    have hKfactor : 1 ≤ 2 * (K : ℝ) + 1 := by
      have hKnonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith [hKnonneg]
    have hdenOne : 1 ≤ den := by
      dsimp [den]
      have h16U : (16 : ℝ) ≤ (16 : ℝ) * U := by
        calc
          (16 : ℝ) = 16 * 1 := by ring
          _ ≤ 16 * U := mul_le_mul_of_nonneg_left hUone (by norm_num)
      have hprod' : (16 * U) * 1 ≤
          (16 * U) * (2 * (K : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hKfactor
          (show (0 : ℝ) ≤ 16 * U by positivity)
      have hprod : 16 * U ≤ 16 * U * (2 * (K : ℝ) + 1) := by
        calc
          16 * U = (16 * U) * 1 := by ring
          _ ≤ _ := hprod'
      linarith
    have hqfloor : (q : ℝ) + 1 >
        (M : ℝ) / den := by
      have hfloor : (stepQ n σ ζ K : ℝ) + 1 >
          (hdScaleMultiplier n σ : ℝ) /
            (16 * ((hdScaleIndex n σ ζ + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1)) := by
        unfold stepQ
        exact_mod_cast Nat.lt_floor_add_one _
      simpa [q, M, den, U, h] using hfloor
    have hqupper : (q : ℝ) ≤ (M : ℝ) := by
      have hfloor : (q : ℝ) ≤ (M : ℝ) / den := by
        have hfloor' : (stepQ n σ ζ K : ℝ) ≤
            (hdScaleMultiplier n σ : ℝ) /
              (16 * ((hdScaleIndex n σ ζ + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1)) := by
          unfold stepQ
          exact_mod_cast Nat.floor_le (by positivity)
        simpa [q, M, den, U, h] using hfloor'
      have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
      have hMden : (M : ℝ) ≤ (M : ℝ) * den := by
        calc
          (M : ℝ) = (M : ℝ) * 1 := by ring
          _ ≤ (M : ℝ) * den := mul_le_mul_of_nonneg_left hdenOne hMnonneg
      exact le_trans hfloor ((div_le_iff₀ hdenPos).2 hMden)
    have hMlarge : 12 * L ≤ (M : ℝ) := by
      calc
        12 * L ≤ (n : ℝ) ^ σ := hmultN n hNmult
        _ ≤ (M : ℝ) := hMlower
    have hMLargeDiv : 12 ≤ (M : ℝ) / L := by
      exact (le_div_iff₀ hL).2 (by simpa [mul_comm] using hMlarge)
    have hdenLower : (M : ℝ) / L ≤ (M : ℝ) / den := by
      apply (le_div_iff₀ hdenPos).2
      calc
        (M : ℝ) / L * den ≤ (M : ℝ) / L * L :=
          mul_le_mul_of_nonneg_left hdenBound (by positivity)
        _ = (M : ℝ) := by field_simp [ne_of_gt hL]
    have hqLower : (M : ℝ) / (2 * L) ≤ (q : ℝ) := by
      have hhalf : (M : ℝ) / L = 2 * ((M : ℝ) / (2 * L)) := by
        field_simp [ne_of_gt hL]
        <;> ring
      have hqgt : (M : ℝ) / L < (q : ℝ) + 1 := lt_of_le_of_lt hdenLower hqfloor
      rw [hhalf] at hqgt
      linarith [hMLargeDiv]
    have hnmultLarge : 12 * L ≤ (n : ℝ) ^ σ := hmultN n hNmult
    have hnqLarge : 12 * L ≤ (n : ℝ) ^ (σ * (1 - θ)) := hqN n hNq
    have hpowSigmaSplit :
        (n : ℝ) ^ (σ * θ) * (n : ℝ) ^ (σ * (1 - θ)) = (n : ℝ) ^ σ := by
      calc
        _ = (n : ℝ) ^ (σ * θ + σ * (1 - θ)) :=
          (Real.rpow_add hnpos (σ * θ) (σ * (1 - θ))).symm
        _ = _ := by congr 1 <;> ring
    have hq6 : 6 * (n : ℝ) ^ (σ * θ) ≤ (q : ℝ) := by
      have hmultprod : 12 * L * (n : ℝ) ^ (σ * θ) ≤ (n : ℝ) ^ σ := by
        calc
          12 * L * (n : ℝ) ^ (σ * θ) ≤
              (n : ℝ) ^ (σ * (1 - θ)) * (n : ℝ) ^ (σ * θ) :=
            mul_le_mul_of_nonneg_right hnqLarge (Real.rpow_nonneg hnpos.le _)
          _ = (n : ℝ) ^ σ := by
            rw [mul_comm, hpowSigmaSplit]
      have hdiv : 6 * (n : ℝ) ^ (σ * θ) ≤ (n : ℝ) ^ σ / (2 * L) := by
        apply (le_div_iff₀ (mul_pos (by norm_num) hL)).2
        calc
          (6 * (n : ℝ) ^ (σ * θ)) * (2 * L) =
              12 * L * (n : ℝ) ^ (σ * θ) := by ring
          _ ≤ (n : ℝ) ^ σ := hmultprod
      have hqNlower : (n : ℝ) ^ σ / (2 * L) ≤ (q : ℝ) :=
        le_trans (div_le_div_of_nonneg_right hMlower (by positivity)) hqLower
      exact le_trans hdiv hqNlower
    have hMtheta : (M : ℝ) ^ θ ≤ 3 * (n : ℝ) ^ (σ * θ) := by
      have hnPow : ((n : ℝ) ^ σ) ^ θ = (n : ℝ) ^ (σ * θ) := by
        rw [← Real.rpow_mul hnpos.le]
      calc
        (M : ℝ) ^ θ ≤ (3 * (n : ℝ) ^ σ) ^ θ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hMupper hθ.le
        _ = (3 : ℝ) ^ θ * ((n : ℝ) ^ σ) ^ θ := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le _)]
        _ = (3 : ℝ) ^ θ * (n : ℝ) ^ (σ * θ) := by rw [hnPow]
        _ ≤ 3 * (n : ℝ) ^ (σ * θ) := by
          have h3 : (3 : ℝ) ^ θ ≤ 3 := by
            calc
              (3 : ℝ) ^ θ ≤ (3 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1.le
              _ = 3 := by rw [Real.rpow_one]
          exact mul_le_mul h3 le_rfl (Real.rpow_nonneg hnpos.le _) (by positivity)
    have hqBig : 2 * (M : ℝ) ^ θ ≤ (q : ℝ) := by
      calc
        2 * (M : ℝ) ^ θ ≤ 2 * (3 * (n : ℝ) ^ (σ * θ)) :=
          mul_le_mul_of_nonneg_left hMtheta (by norm_num)
        _ = 6 * (n : ℝ) ^ (σ * θ) := by ring
        _ ≤ (q : ℝ) := hq6
    have hRthetaLe : (R : ℝ) ^ θ ≤ (R : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hRoneR hθ1.le
    have hRthetaOne : 1 ≤ (R : ℝ) ^ θ := by
      calc
        1 = (R : ℝ) ^ (0 : ℝ) := by simp
        _ ≤ (R : ℝ) ^ θ := Real.rpow_le_rpow_of_exponent_le hRoneR (by linarith [hθ])
    have hRsplit : (R : ℝ) = (R : ℝ) ^ θ * (R : ℝ) ^ (1 - θ) := by
      calc
        (R : ℝ) = (R : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (R : ℝ) ^ (θ + (1 - θ)) := by congr 1 <;> ring
        _ = _ := Real.rpow_add hRpos θ (1 - θ)
    have hRremain : (R : ℝ) ^ (1 - θ) ≤ 2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := by
      have hbase : (R : ℝ) ^ (1 - θ) ≤
          (2 * (n : ℝ) ^ (1 - ζ)) ^ (1 - θ) := by
        have h1θ : 0 ≤ 1 - θ := by linarith [hθ1]
        exact Real.rpow_le_rpow (by positivity) hRupper h1θ
      have hnest : ((n : ℝ) ^ (1 - ζ)) ^ (1 - θ) =
          (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := by
        rw [← Real.rpow_mul hnpos.le]
      have htwo : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
        have htwo' : (2 : ℝ) ^ (1 - θ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hθ])
        simpa only [Real.rpow_one] using htwo'
      calc
        _ ≤ (2 * (n : ℝ) ^ (1 - ζ)) ^ (1 - θ) := hbase
        _ = 2 ^ (1 - θ) * ((n : ℝ) ^ (1 - ζ)) ^ (1 - θ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le _)]
        _ = 2 ^ (1 - θ) * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := by rw [hnest]
        _ ≤ 2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) :=
          mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hnpos.le _)
    have hRpowExponent : (R : ℝ) ^ (1 - θ) ≤
        2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)) := hRremain
    let A : ℝ := ((topScale n σ ζ + 1 : ℕ) : ℝ) *
      ((d + 1 : ℕ) : ℝ) ^ (D * (M * R))
    have hApos : 0 < A := by
      dsimp [A]
      positivity
    have hlogA : Real.log A ≤ 2 * (n : ℝ) ^ δ +
        ((D * (M * R) : ℕ) : ℝ) * (2 * (n : ℝ) ^ δ) := by
      have hlogEq : Real.log A =
          Real.log ((topScale n σ ζ + 1 : ℕ) : ℝ) +
            ((D * (M * R) : ℕ) : ℝ) * Real.log ((d + 1 : ℕ) : ℝ) := by
        dsimp [A]
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      rw [hlogEq]
      exact add_le_add hlogTop
        (mul_le_mul_of_nonneg_left hlogd (Nat.cast_nonneg _))
    let Cexp : ℝ := (q : ℝ) * Real.log A
    have hqden : 0 < den := hdenPos
    have hdenFact : 1 ≤ den := hdenOne
    have hqCount : Cexp ≤ Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) := by
      have hqlog := mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg q)
      have hlogNonneg : 0 ≤ 2 * (n : ℝ) ^ δ +
          ((D * (M * R) : ℕ) : ℝ) * (2 * (n : ℝ) ^ δ) := by positivity
      have hqterm : (q : ℝ) *
          (2 * (n : ℝ) ^ δ + ((D * (M * R) : ℕ) : ℝ) * (2 * (n : ℝ) ^ δ)) ≤
            (M : ℝ) *
              (2 * (n : ℝ) ^ δ + ((D * (M * R) : ℕ) : ℝ) * (2 * (n : ℝ) ^ δ)) :=
        mul_le_mul_of_nonneg_right hqupper hlogNonneg
      have hraw : Cexp ≤ 2 * (M : ℝ) * (n : ℝ) ^ δ +
          2 * (D : ℝ) * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by
        dsimp [Cexp]
        calc
          _ ≤ (q : ℝ) *
              (2 * (n : ℝ) ^ δ + ((D * (M * R) : ℕ) : ℝ) * (2 * (n : ℝ) ^ δ)) := hqlog
          _ ≤ (M : ℝ) *
              (2 * (n : ℝ) ^ δ + ((D * (M * R) : ℕ) : ℝ) * (2 * (n : ℝ) ^ δ)) := hqterm
          _ = _ := by push_cast; ring
      have hMone : 1 ≤ (M : ℝ) := le_trans hnσone hMlower
      have hMRone : 1 ≤ (M : ℝ) * (R : ℝ) := by
        calc
          1 = 1 * 1 := by ring
          _ ≤ (M : ℝ) * (R : ℝ) :=
            mul_le_mul hMone hRoneR (by norm_num) (by positivity)
      have hMterm : (M : ℝ) * (n : ℝ) ^ δ ≤
          (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by
        have hmul : 1 * ((M : ℝ) * (n : ℝ) ^ δ) ≤
            ((M : ℝ) * (R : ℝ)) * ((M : ℝ) * (n : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_right hMRone
            (show 0 ≤ (M : ℝ) * (n : ℝ) ^ δ by positivity)
        calc
          (M : ℝ) * (n : ℝ) ^ δ = 1 * ((M : ℝ) * (n : ℝ) ^ δ) := by ring
          _ ≤ ((M : ℝ) * (R : ℝ)) * ((M : ℝ) * (n : ℝ) ^ δ) := hmul
          _ = (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by ring
      have hraw' : Cexp ≤
          (2 + 2 * (D : ℝ)) * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by
        calc
          Cexp ≤ 2 * (M : ℝ) * (n : ℝ) ^ δ +
              2 * (D : ℝ) * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := hraw
          _ ≤ 2 * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ +
              2 * (D : ℝ) * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by
            have hMterm2 : 2 * (M : ℝ) * (n : ℝ) ^ δ ≤
                2 * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by
              calc
                2 * (M : ℝ) * (n : ℝ) ^ δ =
                    2 * ((M : ℝ) * (n : ℝ) ^ δ) := by ring
                _ ≤ 2 * ((M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ) :=
                  mul_le_mul_of_nonneg_left hMterm (show (0 : ℝ) ≤ 2 by norm_num)
                _ = _ := by ring
            exact add_le_add hMterm2 le_rfl
          _ = (2 + 2 * (D : ℝ)) * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := by ring
      have hM2 : (M : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ (2 * σ) := by
        calc
          (M : ℝ) ^ 2 ≤ (3 * (n : ℝ) ^ σ) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) hMupper 2
          _ = 9 * (n : ℝ) ^ (2 * σ) := by
            rw [mul_pow]
            have hpow : ((n : ℝ) ^ σ) ^ 2 = (n : ℝ) ^ (2 * σ) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
              congr 1
              ring
            rw [hpow]
            ring
      have hpowδ : (n : ℝ) ^ (2 * σ) * (n : ℝ) ^ δ =
          (n : ℝ) ^ (2 * σ + δ) := (Real.rpow_add hnpos (2 * σ) δ).symm
      have hcoeff : (2 + 2 * (D : ℝ)) * 9 = Ccount := by
        dsimp [Ccount]
        push_cast
        ring
      have hDnonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
      have hcoefNonneg : 0 ≤ 2 + 2 * (D : ℝ) :=
        add_nonneg (by norm_num) (mul_nonneg (by norm_num) hDnonneg)
      have hcoefM2 : (2 + 2 * (D : ℝ)) * (M : ℝ) ^ 2 ≤
          (2 + 2 * (D : ℝ)) * (9 * (n : ℝ) ^ (2 * σ)) :=
        mul_le_mul_of_nonneg_left hM2 hcoefNonneg
      calc
        Cexp ≤ (2 + 2 * (D : ℝ)) * (M : ℝ) ^ 2 * (R : ℝ) * (n : ℝ) ^ δ := hraw'
        _ ≤ (2 + 2 * (D : ℝ)) * (9 * (n : ℝ) ^ (2 * σ)) *
            (R : ℝ) * (n : ℝ) ^ δ := by
          have hRnonneg : 0 ≤ (R : ℝ) := Nat.cast_nonneg R
          have hδnonneg : 0 ≤ (n : ℝ) ^ δ := Real.rpow_nonneg hnpos.le _
          calc
            ((2 + 2 * (D : ℝ)) * (M : ℝ) ^ 2) * (R : ℝ) * (n : ℝ) ^ δ =
                (((2 + 2 * (D : ℝ)) * (M : ℝ) ^ 2) * (R : ℝ)) * (n : ℝ) ^ δ := by ring
            _ ≤ (((2 + 2 * (D : ℝ)) * (9 * (n : ℝ) ^ (2 * σ))) *
                  (R : ℝ)) * (n : ℝ) ^ δ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoefM2 hRnonneg) hδnonneg
            _ = _ := by ring
        _ = Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) := by
          calc
            ((2 + 2 * (D : ℝ)) * (9 * (n : ℝ) ^ (2 * σ))) *
                (R : ℝ) * (n : ℝ) ^ δ =
              ((2 + 2 * (D : ℝ)) * 9) *
                ((n : ℝ) ^ (2 * σ) * (n : ℝ) ^ δ) * (R : ℝ) := by ring
            _ = Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) := by
              rw [hcoeff, hpowδ]
    let T : ℝ := (n : ℝ) ^ a *
      ((M * R : ℕ) : ℝ) ^ θ
    let F : ℝ := (n : ℝ) ^ (b - 2 * σ) * (R : ℝ)
    let G : ℝ := (n : ℝ) ^ a * (R : ℝ) ^ θ
    have hTfact : T = (n : ℝ) ^ a * (M : ℝ) ^ θ * (R : ℝ) ^ θ := by
      change (n : ℝ) ^ a * ((M * R : ℕ) : ℝ) ^ θ =
        (n : ℝ) ^ a * (M : ℝ) ^ θ * (R : ℝ) ^ θ
      have hcast : ((M * R : ℕ) : ℝ) = (M : ℝ) * (R : ℝ) := by exact_mod_cast Nat.cast_mul M R
      calc
        (n : ℝ) ^ a * ((M * R : ℕ) : ℝ) ^ θ =
            (n : ℝ) ^ a * ((M : ℝ) * (R : ℝ)) ^ θ := by rw [hcast]
        _ = (n : ℝ) ^ a * ((M : ℝ) ^ θ * (R : ℝ) ^ θ) := by
          rw [Real.mul_rpow (Nat.cast_nonneg M) (Nat.cast_nonneg R)]
        _ = (n : ℝ) ^ a * (M : ℝ) ^ θ * (R : ℝ) ^ θ := by ring
    have hTupper : T ≤ 3 * (n : ℝ) ^ (a + σ * θ) * (R : ℝ) := by
      rw [hTfact]
      calc
        (n : ℝ) ^ a * (M : ℝ) ^ θ * (R : ℝ) ^ θ ≤
            (n : ℝ) ^ a * (3 * (n : ℝ) ^ (σ * θ)) * (R : ℝ) := by
          have hMR : (M : ℝ) ^ θ * (R : ℝ) ^ θ ≤
              (3 * (n : ℝ) ^ (σ * θ)) * (R : ℝ) :=
            mul_le_mul hMtheta hRthetaLe (by positivity) (by positivity)
          calc
            (n : ℝ) ^ a * (M : ℝ) ^ θ * (R : ℝ) ^ θ =
                (n : ℝ) ^ a * ((M : ℝ) ^ θ * (R : ℝ) ^ θ) := by ring
            _ ≤ (n : ℝ) ^ a * ((3 * (n : ℝ) ^ (σ * θ)) * (R : ℝ)) :=
              mul_le_mul_of_nonneg_left hMR (by positivity)
            _ = (n : ℝ) ^ a * (3 * (n : ℝ) ^ (σ * θ)) * (R : ℝ) := by ring
        _ = 3 * (n : ℝ) ^ (a + σ * θ) * (R : ℝ) := by
          calc
            (n : ℝ) ^ a * (3 * (n : ℝ) ^ (σ * θ)) * (R : ℝ) =
                3 * ((n : ℝ) ^ a * (n : ℝ) ^ (σ * θ)) * (R : ℝ) := by ring
            _ = 3 * (n : ℝ) ^ (a + σ * θ) * (R : ℝ) := by
              have hpow : (n : ℝ) ^ a * (n : ℝ) ^ (σ * θ) =
                  (n : ℝ) ^ (a + σ * θ) :=
                (Real.rpow_add hnpos a (σ * θ)).symm
              rw [hpow]
    have hTleBase : T ≤ (q : ℝ) / 2 * (n : ℝ) ^ a * (R : ℝ) ^ θ := by
      rw [hTfact]
      have hqhalf : (M : ℝ) ^ θ ≤ (q : ℝ) / 2 := by linarith [hqBig]
      calc
        (n : ℝ) ^ a * (M : ℝ) ^ θ * (R : ℝ) ^ θ ≤
            (n : ℝ) ^ a * ((q : ℝ) / 2) * (R : ℝ) ^ θ := by
          have hleft : (n : ℝ) ^ a * (M : ℝ) ^ θ ≤
              (n : ℝ) ^ a * ((q : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hqhalf (Real.rpow_nonneg hnpos.le _)
          exact mul_le_mul_of_nonneg_right hleft (Real.rpow_nonneg hRpos.le _)
        _ = _ := by ring
    have hqHalfLower : (n : ℝ) ^ σ / (4 * L) ≤ (q : ℝ) / 2 := by
      have hqNlower : (n : ℝ) ^ σ / (2 * L) ≤ (q : ℝ) :=
        le_trans (div_le_div_of_nonneg_right hMlower (by positivity)) hqLower
      have hhalf : (n : ℝ) ^ σ / (4 * L) =
          ((n : ℝ) ^ σ / (2 * L)) / 2 := by
        field_simp [ne_of_gt hL]
        <;> ring
      rw [hhalf]
      exact div_le_div_of_nonneg_right hqNlower (by norm_num)
    have hSurplus : (n : ℝ) ^ (a + σ) * (R : ℝ) ^ θ / (4 * L) ≤
        (q : ℝ) / 2 * (n : ℝ) ^ a * (R : ℝ) ^ θ := by
      have hpow : (n : ℝ) ^ (a + σ) = (n : ℝ) ^ a * (n : ℝ) ^ σ := by
        rw [← Real.rpow_add hnpos a σ]
      rw [hpow]
      have hmul := mul_le_mul_of_nonneg_right hqHalfLower
        (mul_nonneg (Real.rpow_nonneg hnpos.le a) (Real.rpow_nonneg hRpos.le θ))
      have hmul' : ((n : ℝ) ^ σ / (4 * L)) *
          ((n : ℝ) ^ a * (R : ℝ) ^ θ) ≤
          ((q : ℝ) / 2) * ((n : ℝ) ^ a * (R : ℝ) ^ θ) := hmul
      calc
        (n : ℝ) ^ a * (n : ℝ) ^ σ * (R : ℝ) ^ θ / (4 * L) =
            ((n : ℝ) ^ σ / (4 * L)) * ((n : ℝ) ^ a * (R : ℝ) ^ θ) := by ring
        _ ≤ ((q : ℝ) / 2) * ((n : ℝ) ^ a * (R : ℝ) ^ θ) := hmul'
        _ = (q : ℝ) / 2 * (n : ℝ) ^ a * (R : ℝ) ^ θ := by ring
    have hBaseSlack : T + (n : ℝ) ^ (a + σ) * (R : ℝ) ^ θ / (4 * L) ≤
        (q : ℝ) * (n : ℝ) ^ a * (R : ℝ) ^ θ := by
      calc
        T + (n : ℝ) ^ (a + σ) * (R : ℝ) ^ θ / (4 * L) ≤
            ((q : ℝ) / 2 * (n : ℝ) ^ a * (R : ℝ) ^ θ) +
              ((q : ℝ) / 2 * (n : ℝ) ^ a * (R : ℝ) ^ θ) :=
          add_le_add hTleBase hSurplus
        _ = (q : ℝ) * (n : ℝ) ^ a * (R : ℝ) ^ θ := by ring
    have hRpowLower : 1 ≤ (R : ℝ) ^ θ := hRthetaOne
    have hRpow : (R : ℝ) ^ θ ≤ (R : ℝ) := hRthetaLe
    have hRremainUpper : (R : ℝ) = (R : ℝ) ^ θ * (R : ℝ) ^ (1 - θ) := hRsplit
    have hCbaseCost : Cexp + Real.log 2 ≤
        Cbase * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by
      have hXone : 1 ≤ (n : ℝ) ^ Xbase := by
        calc
          1 = (n : ℝ) ^ (0 : ℝ) := by simp
          _ ≤ (n : ℝ) ^ Xbase :=
            Real.rpow_le_rpow_of_exponent_le hn1 hXbase
      have hcountRewritten : Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) ≤
          2 * Ccount * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by
        have hpowX : (n : ℝ) ^ (2 * σ + δ) *
            (n : ℝ) ^ ((1 - ζ) * (1 - θ)) = (n : ℝ) ^ Xbase := by
          dsimp [Xbase]
          exact (Real.rpow_add hnpos (2 * σ + δ) ((1 - ζ) * (1 - θ))).symm
        calc
          Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) =
              (Ccount * (n : ℝ) ^ (2 * σ + δ)) *
                ((R : ℝ) ^ θ * (R : ℝ) ^ (1 - θ)) := by
            calc
              _ = (Ccount * (n : ℝ) ^ (2 * σ + δ)) * (R : ℝ) := by ring
              _ = _ := congrArg
                (fun r : ℝ => (Ccount * (n : ℝ) ^ (2 * σ + δ)) * r) hRsplit
          _ ≤ Ccount * (n : ℝ) ^ (2 * σ + δ) *
              ((R : ℝ) ^ θ * (2 * (n : ℝ) ^ ((1 - ζ) * (1 - θ)))) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hRpowExponent
                (Real.rpow_nonneg hRpos.le θ)
            · positivity
          _ = 2 * Ccount *
              ((n : ℝ) ^ (2 * σ + δ) * (n : ℝ) ^ ((1 - ζ) * (1 - θ))) *
                (R : ℝ) ^ θ := by ring
          _ = 2 * Ccount * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by rw [hpowX]
      have hlog2nonneg : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
      have hlog2bound : Real.log 2 ≤ Real.log 2 * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by
        have hfactor : 1 ≤ (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by
          calc
            1 ≤ (n : ℝ) ^ Xbase := hXone
            _ ≤ (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by
              calc
                (n : ℝ) ^ Xbase = (n : ℝ) ^ Xbase * 1 := by ring
                _ ≤ (n : ℝ) ^ Xbase * (R : ℝ) ^ θ :=
                  mul_le_mul_of_nonneg_left hRpowLower (by positivity)
        calc
          Real.log 2 = Real.log 2 * 1 := by ring
          _ ≤ Real.log 2 * ((n : ℝ) ^ Xbase * (R : ℝ) ^ θ) :=
            mul_le_mul_of_nonneg_left hfactor hlog2nonneg
          _ = Real.log 2 * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by ring
      have hcountBase' : Cexp + Real.log 2 ≤
          (2 * Ccount + Real.log 2) * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by
        calc
          Cexp + Real.log 2 ≤ Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) + Real.log 2 :=
            add_le_add_left hqCount (Real.log 2)
          _ ≤ 2 * Ccount * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ +
              Real.log 2 * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ :=
            add_le_add hcountRewritten hlog2bound
          _ = (2 * Ccount + Real.log 2) * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := by ring
      simpa [Cbase] using hcountBase'
    have hBaseBudget : Cexp + Real.log 2 ≤
        (n : ℝ) ^ (a + σ) * (R : ℝ) ^ θ / (4 * L) := by
      have hAbsorb := hbaseN n hNbase
      have hAbsorbDiv : Cbase * (n : ℝ) ^ Xbase ≤
          (n : ℝ) ^ (a + σ) / (4 * L) := by
        apply (le_div_iff₀ (mul_pos (by norm_num) hL)).2
        calc
          Cbase * (n : ℝ) ^ Xbase * (4 * L) =
              4 * L * Cbase * (n : ℝ) ^ Xbase := by ring
          _ ≤ (n : ℝ) ^ (a + σ) := hAbsorb
      calc
        Cexp + Real.log 2 ≤ Cbase * (n : ℝ) ^ Xbase * (R : ℝ) ^ θ := hCbaseCost
        _ ≤ ((n : ℝ) ^ (a + σ) / (4 * L)) * (R : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right hAbsorbDiv (Real.rpow_nonneg hRpos.le _)
        _ = _ := by ring
    have hFbudget : Cexp + T + Real.log 4 ≤ F := by
      have hFcoeff : Ccount * (n : ℝ) ^ (2 * σ + δ) +
            3 * (n : ℝ) ^ (a + σ * θ) + Real.log 4 ≤
          (n : ℝ) ^ (b - 2 * σ) := by
        have h1 := herrCountN n hNerrCount
        have h2 := herrBaseN n hNerrBase
        have h3 := herrConstN n hNerrConst
        have h3' : 3 * Real.log 4 ≤ (n : ℝ) ^ (b - 2 * σ) := by simpa using h3
        have hsum :
            3 * Ccount * (n : ℝ) ^ (2 * σ + δ) +
                9 * (n : ℝ) ^ (a + σ * θ) + 3 * Real.log 4 ≤
              (n : ℝ) ^ (b - 2 * σ) + (n : ℝ) ^ (b - 2 * σ) +
                (n : ℝ) ^ (b - 2 * σ) :=
          add_le_add (add_le_add h1 h2) h3'
        calc
          _ = (3 * Ccount * (n : ℝ) ^ (2 * σ + δ) +
                9 * (n : ℝ) ^ (a + σ * θ) + 3 * Real.log 4) / 3 := by ring
          _ ≤ ((n : ℝ) ^ (b - 2 * σ) + (n : ℝ) ^ (b - 2 * σ) +
                (n : ℝ) ^ (b - 2 * σ)) / 3 :=
            div_le_div_of_nonneg_right hsum (by norm_num)
          _ = (n : ℝ) ^ (b - 2 * σ) := by ring
      have hlog4 : 0 ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
      have hlog4R : Real.log 4 ≤ Real.log 4 * (R : ℝ) := by
        calc
          Real.log 4 = Real.log 4 * 1 := by ring
          _ ≤ Real.log 4 * (R : ℝ) := mul_le_mul_of_nonneg_left hRoneR hlog4
      have hcoeffR :
          Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) +
            3 * (n : ℝ) ^ (a + σ * θ) * (R : ℝ) + Real.log 4 ≤
          (Ccount * (n : ℝ) ^ (2 * σ + δ) +
            3 * (n : ℝ) ^ (a + σ * θ) + Real.log 4) * (R : ℝ) := by
        calc
          _ = (Ccount * (n : ℝ) ^ (2 * σ + δ) +
              3 * (n : ℝ) ^ (a + σ * θ)) * (R : ℝ) + Real.log 4 := by ring
          _ ≤ (Ccount * (n : ℝ) ^ (2 * σ + δ) +
              3 * (n : ℝ) ^ (a + σ * θ)) * (R : ℝ) +
                Real.log 4 * (R : ℝ) := by
            calc
              _ = Real.log 4 +
                  (Ccount * (n : ℝ) ^ (2 * σ + δ) +
                    3 * (n : ℝ) ^ (a + σ * θ)) * (R : ℝ) := by ring
              _ ≤ Real.log 4 * (R : ℝ) +
                  (Ccount * (n : ℝ) ^ (2 * σ + δ) +
                    3 * (n : ℝ) ^ (a + σ * θ)) * (R : ℝ) :=
                add_le_add_left hlog4R _
              _ = _ := by ring
          _ = _ := by ring
      calc
        _ ≤ Ccount * (n : ℝ) ^ (2 * σ + δ) * (R : ℝ) +
            3 * (n : ℝ) ^ (a + σ * θ) * (R : ℝ) + Real.log 4 :=
          add_le_add (add_le_add hqCount hTupper) le_rfl
        _ ≤ (Ccount * (n : ℝ) ^ (2 * σ + δ) +
            3 * (n : ℝ) ^ (a + σ * θ) + Real.log 4) * (R : ℝ) := hcoeffR
        _ ≤ (n : ℝ) ^ (b - 2 * σ) * (R : ℝ) :=
          mul_le_mul_of_nonneg_right hFcoeff (by positivity)
        _ = F := by rfl
    let Gbase : ℝ := (q : ℝ) * G
    have hBaseCostSlack : Cexp + T + Real.log 2 ≤ Gbase := by
      have hbaseBudget := hBaseBudget
      have hBaseSlack := hBaseSlack
      dsimp [Gbase, G]
      nlinarith [hBaseBudget, hBaseSlack]
    have hAq : A ^ q = Real.exp Cexp := by
      calc
        A ^ q = (Real.exp (Real.log A)) ^ q := by rw [Real.exp_log hApos]
        _ = Real.exp ((q : ℝ) * Real.log A) := by rw [← Real.exp_nat_mul]
        _ = Real.exp Cexp := by rfl
    have hExpMul (x y : ℝ) : Real.exp x * Real.exp y = Real.exp (x + y) := by
      rw [← Real.exp_add]
    have hlog2exp : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hlog4exp : Real.exp (-Real.log 4) = (1 / 4 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num
    have hErrHalf :
        A ^ q * (Real.exp (-F) + Real.exp (-F)) ≤
          (1 / 2 : ℝ) * Real.exp (-T) := by
      have hExpLe : Real.exp (Cexp - F) ≤ Real.exp (-T - Real.log 4) :=
        Real.exp_le_exp.mpr (by linarith [hFbudget])
      have hExpLe' : Real.exp (Cexp - F) ≤
          (1 / 4 : ℝ) * Real.exp (-T) := by
        calc
          _ ≤ Real.exp (-T - Real.log 4) := hExpLe
          _ = Real.exp (-T) * Real.exp (-Real.log 4) := by
            rw [hExpMul]
            congr 1 <;> ring
          _ = (1 / 4 : ℝ) * Real.exp (-T) := by rw [hlog4exp]; ring
      calc
        _ = 2 * Real.exp (Cexp - F) := by
          rw [hAq]
          calc
            _ = Real.exp Cexp * Real.exp (-F) + Real.exp Cexp * Real.exp (-F) := by ring
            _ = _ := by
              rw [hExpMul]
              have harg : Cexp + -F = Cexp - F := by ring
              rw [harg]
              ring
        _ ≤ (1 / 2 : ℝ) * Real.exp (-T) := by
          calc
            _ ≤ 2 * ((1 / 4 : ℝ) * Real.exp (-T)) :=
              mul_le_mul_of_nonneg_left hExpLe' (by norm_num)
            _ = _ := by ring
    have hExpBasePow : (Real.exp (-G)) ^ q = Real.exp (-Gbase) := by
      calc
        (Real.exp (-G)) ^ q = Real.exp ((q : ℝ) * (-G)) := by
          rw [← Real.exp_nat_mul]
        _ = Real.exp (-Gbase) := by
          congr 1
          dsimp [Gbase]
          ring
    have hBaseHalf :
        A ^ q * (Real.exp (-G)) ^ q ≤ (1 / 2 : ℝ) * Real.exp (-T) := by
      have hExpLe : Real.exp (Cexp - Gbase) ≤ Real.exp (-T - Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith [hBaseCostSlack])
      have hExpLe' : Real.exp (Cexp - Gbase) ≤
          (1 / 2 : ℝ) * Real.exp (-T) := by
        calc
          _ ≤ Real.exp (-T - Real.log 2) := hExpLe
          _ = Real.exp (-T) * Real.exp (-Real.log 2) := by
            rw [hExpMul]
            congr 1 <;> ring
          _ = (1 / 2 : ℝ) * Real.exp (-T) := by rw [hlog2exp]; ring
      calc
        _ = Real.exp (Cexp - Gbase) := by
          rw [hAq, hExpBasePow]
          calc
            Real.exp Cexp * Real.exp (-Gbase) =
                Real.exp (Cexp + -Gbase) := hExpMul _ _
            _ = Real.exp (Cexp - Gbase) := by congr 1 <;> ring
        _ ≤ _ := hExpLe'

    change A ^ q * (Real.exp (-F) + Real.exp (-F) + (Real.exp (-G)) ^ q) ≤
      Real.exp (-T)
    calc
      _ = A ^ q * (Real.exp (-F) + Real.exp (-F)) + A ^ q * (Real.exp (-G)) ^ q := by
        rw [mul_add]
      _ ≤ (1 / 2 : ℝ) * Real.exp (-T) + (1 / 2 : ℝ) * Real.exp (-T) :=
        add_le_add hErrHalf hBaseHalf
      _ = Real.exp (-T) := by ring
   ⟩

/-- LEAF (arithmetic): the separated-children count condition of `parent_fail_children`. -/
theorem step_large (σ ζ : ℝ) (hσ : 0 < σ) (hζ : 0 < ζ ∧ ζ < 1) (K : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ i : ℕ, 1 ≤ i → i ≤ hdScaleIndex n σ ζ →
      (1 + hdScaleSlope (hdScaleIndex n σ ζ) (i - 1)) * (2 * (K : ℝ) + 1) *
            (stepQ n σ ζ K : ℝ) +
          (1 + hdScaleSlope (hdScaleIndex n σ ζ) (i - 1)) <
        (hdScaleSlope (hdScaleIndex n σ ζ) (i - 1) - hdScaleSlope (hdScaleIndex n σ ζ) i) *
          (hdScaleMultiplier n σ : ℝ) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ σ) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hσ).comp tendsto_natCast_atTop_atTop
  let B : ℕ := ⌈1 / σ⌉₊
  have hB : 0 < ((B + 1 : ℕ) : ℝ) := by positivity
  have hC : 0 < 11 * ((B + 1 : ℕ) : ℝ) := by positivity
  have hEventually : ∀ᶠ n : ℕ in Filter.atTop,
      11 * ((B + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ σ :=
    (Filter.tendsto_atTop.1 hpow) (11 * ((B + 1 : ℕ) : ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨max 2 N, ?_⟩
  intro n hn i hi1 hih
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_left 2 N) hn
  have hNn : N ≤ n := le_trans (Nat.le_max_right 2 N) hn
  let h : ℕ := hdScaleIndex n σ ζ
  let M : ℕ := hdScaleMultiplier n σ
  let U : ℝ := ((h + 1 : ℕ) : ℝ)
  have hidx : h ≤ B := by
    dsimp [h, B]
    exact hdScaleIndex_le_ceil_inv_sigma hn2 hσ hζ
  have hUpos : 0 < U := by positivity
  have hUbound : U ≤ ((B : ℝ) + 1) := by
    dsimp [U]
    exact_mod_cast Nat.succ_le_succ hidx
  have hnPower : 11 * ((B + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ σ := hN n hNn
  have hMlarge : 11 * ((B : ℝ) + 1) ≤ (M : ℝ) := by
    calc
      11 * ((B : ℝ) + 1) = 11 * ((B + 1 : ℕ) : ℝ) := by simp
      _ ≤ (n : ℝ) ^ σ := hnPower
      _ ≤ (⌈(n : ℝ) ^ σ⌉₊ : ℝ) := by exact_mod_cast Nat.le_ceil ((n : ℝ) ^ σ)
      _ ≤ (M : ℝ) := by
        dsimp [M, hdScaleMultiplier]
        exact_mod_cast (Nat.le_max_right 2 ⌈(n : ℝ) ^ σ⌉₊)
  have hM10 : 10 * U ≤ (M : ℝ) := by
    have hBnonneg : 0 ≤ (B : ℝ) + 1 := by positivity
    nlinarith [hUbound, hMlarge, hBnonneg]
  have hslope : 1 + hdScaleSlope h (i - 1) ≤ 3 / 2 := by
    have hf := hdScaleThreshold_fractions_bounds (h := h) (i := i - 1) (by omega)
    rcases hf with ⟨_, _, _, _, _, hupper⟩
    linarith
  have hsub : h - (i - 1) = (h - i) + 1 := by omega
  have hsubCast : ((h - (i - 1) : ℕ) : ℝ) = ((h - i : ℕ) : ℝ) + 1 := by
    exact_mod_cast hsub
  have hslopeGap : hdScaleSlope h (i - 1) - hdScaleSlope h i = 1 / (4 * U) := by
    dsimp [hdScaleSlope, U]
    rw [hsubCast]
    ring
  have hqbound : (stepQ n σ ζ K : ℝ) ≤
      (M : ℝ) / (16 * U * (2 * (K : ℝ) + 1)) := by
    have hfloor : (stepQ n σ ζ K : ℝ) ≤
        (hdScaleMultiplier n σ : ℝ) /
          (16 * ((hdScaleIndex n σ ζ + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1)) := by
      unfold stepQ
      exact_mod_cast Nat.floor_le (by positivity :
        0 ≤ (hdScaleMultiplier n σ : ℝ) /
          (16 * ((hdScaleIndex n σ ζ + 1 : ℕ) : ℝ) * (2 * (K : ℝ) + 1)))
    simpa [h, M, U] using hfloor
  have hqterm :
      (1 + hdScaleSlope h (i - 1)) * (2 * (K : ℝ) + 1) * (stepQ n σ ζ K : ℝ) ≤
        3 * (M : ℝ) / (32 * U) := by
    calc
      _ ≤ (3 / 2) * (2 * (K : ℝ) + 1) * (stepQ n σ ζ K : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hslope (by positivity)
        · exact Nat.cast_nonneg _
      _ ≤ (3 / 2) * (2 * (K : ℝ) + 1) *
          ((M : ℝ) / (16 * U * (2 * (K : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hqbound (by positivity)
      _ = 3 * (M : ℝ) / (32 * U) := by
        have hKpos : 0 < 2 * (K : ℝ) + 1 := by positivity
        field_simp [ne_of_gt hUpos, ne_of_gt hKpos]
        <;> ring
  have hsum :
      (1 + hdScaleSlope h (i - 1)) * (2 * (K : ℝ) + 1) * (stepQ n σ ζ K : ℝ) +
          (1 + hdScaleSlope h (i - 1)) ≤
        3 * (M : ℝ) / (32 * U) + 3 / 2 := by
    exact add_le_add hqterm hslope
  let z : ℝ := (M : ℝ) / (32 * U)
  have hz : 5 / 16 ≤ z := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * U)).2
    nlinarith [hM10]
  have hratio : (M : ℝ) / (4 * U) = 8 * z := by
    dsimp [z]
    field_simp [ne_of_gt hUpos]
    <;> ring
  have hstrict : 3 * (M : ℝ) / (32 * U) + 3 / 2 < (M : ℝ) / (4 * U) := by
    rw [hratio]
    have hz' : 3 * (M : ℝ) / (32 * U) = 3 * z := by dsimp [z]; ring
    rw [hz']
    nlinarith [hz]
  have htarget :
      (hdScaleSlope h (i - 1) - hdScaleSlope h i) * (M : ℝ) =
        (M : ℝ) / (4 * U) := by
    rw [hslopeGap]
    dsimp [U]
    ring
  have hfinal :
      (1 + hdScaleSlope h (i - 1)) * (2 * (K : ℝ) + 1) * (stepQ n σ ζ K : ℝ) +
          (1 + hdScaleSlope h (i - 1)) <
        (hdScaleSlope h (i - 1) - hdScaleSlope h i) * (M : ℝ) := by
    calc
      _ ≤ 3 * (M : ℝ) / (32 * U) + 3 / 2 := hsum
      _ < (M : ℝ) / (4 * U) := hstrict
      _ = (hdScaleSlope h (i - 1) - hdScaleSlope h i) * (M : ℝ) := htarget.symm
  simpa [h, M] using hfinal

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
