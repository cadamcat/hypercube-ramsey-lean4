import HypercubeRamsey.S18.Nodes_sol_s18_n1_caps
import HypercubeRamsey.Framework.FinProbLemmas

/-! The support premise needed by the variance argument in Section 18:195–204.
This file leaves the frozen L18_1b statement unchanged. -/
namespace HypercubeRamsey.Lane_sol_s18_1b
open Classical
open scoped BigOperators
open S18

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

/-- This is the support needed to apply R2 to the empirical sketch. -/
def InitialSketchSupport (D : LateData hPT) (j : Fin D.geom.r) {b : Pos T k}
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b) : Prop :=
  ∀ a t, (D.initialPrior (flipPos b a) h.1).w (side.2.1 a t) ≠ 0

/-- Proposed repair: retain the conclusion and restrict only the sketch support.
The original `S18.BroadDeletionFacts` is not changed. -/
def SupportedBroadDeletionFacts (D : LateData hPT) (K27 : ℝ) : Prop :=
  ∀ (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (side : D.encoding.base.RowOut b), b ∈ D.encoding.base.classes j → D.gate j b h →
    InitialSketchSupport D j h side → D.R1 j side → D.R2 j h side →
    (∀ order ∈ D.testOrders b, ∀ q, q ≤ order.length →
      Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤ D.retainedMass j side (D.prefixTests order q)) ∧
    D.deletionConclusion j side ∧
    (∀ a x, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 →
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if Hits (T.S.E k) PT.tiling.c x y then D.labelWeight j side Finset.univ y else 0) ≤
        (1 / 2) * Real.exp (K27 * l * D.error (flipPos b a) j)) ∧
    (∀ a x z, (D.initialPrior (flipPos b a) h.1).w x ≠ 0 →
      (D.initialPrior (flipPos b a) h.1).w z ≠ 0 → D.nonconflict (flipPos b a) x z →
      let l := if a ∈ PT.tiling.Icoord (D.geom.patchOf b) then (PT.tiling.P (D.geom.patchOf b)).h else 1
      (∑ y, if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y
        then D.labelWeight j side Finset.univ y else 0) ≤
          (1 / 4) * Real.exp (K27 * l * D.error (flipPos b a) j))

/-- The product formula only constrains samples in a row of nonzero weight. -/
theorem reference_current_support (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b.1)
    (hside : (D.encoding.kernels.refK j b h).w side ≠ 0) :
    ∀ a t, (D.currentPrior j (flipPos b.1 a) h).w (side.2.1 a t) ≠ 0 := by
  rw [hT.reference_formula] at hside
  have hprod := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hside).1).2
  intro a t
  exact Finset.prod_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hprod a (Finset.mem_univ a)) t (Finset.mem_univ t)

/-- The gate rules out posterior fallback, so current support lies in initial support. -/
theorem gated_initial_of_current_support (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : Pos T k) (h : D.encoding.base.History j.castSucc)
    (hb : b ∈ D.encoding.base.classes j) (hg : D.gate j b h)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k))
    (hx : (D.currentPrior j (flipPos b a) h).w x ≠ 0) :
    (D.initialPrior (flipPos b a) h.1).w x ≠ 0 := by
  obtain ⟨hv, hmass⟩ := Lane_sol_s18_n1_caps.gated_current_mass D hsmall j b h hg hb a
  intro hzero
  apply hx
  rw [LateData.currentPrior, Lane_sol_s18_n1_caps.priorAt_weight D h _ hv hmass]
  simp [Lane_sol_s18_n1_caps.rawWeight, hzero]

/-- Thus the missing variance premise is automatic on the reference support. -/
theorem reference_initial_sketch_support (D : LateData hPT) (hT : TransitionData D)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b.1)
    (hg : D.gate j b.1 h) (hside : (D.encoding.kernels.refK j b h).w side ≠ 0) :
    InitialSketchSupport D j h side := by
  intro a t
  exact gated_initial_of_current_support D hsmall j b.1 h b.2 hg a _
    (reference_current_support D hT j b h side hside a t)

/-- Side data with an unsupported sketch slot has zero reference weight. -/
theorem reference_zero_of_unsupported (D : LateData hPT) (hT : TransitionData D)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (j : Fin D.geom.r) (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (side : D.encoding.base.RowOut b.1)
    (hg : D.gate j b.1 h) (a : Fin (T.S.n k)) (t : Fin (sketchLength T k))
    (hzero : (D.initialPrior (flipPos b.1 a) h.1).w (side.2.1 a t) = 0) :
    (D.encoding.kernels.refK j b h).w side = 0 := by
  by_contra hside
  exact reference_initial_sketch_support D hT hsmall j b h side hg hside a t hzero

/-! A finite local obstruction. The comparison law and the mask law have
disjoint supports. Initial labels are fair bits under both laws; unsupported
sketch labels are fair independent bits under the comparison law and all miss
the mask. This models the quantifier gap, not a full Stage/LateData instance. -/

namespace Obstruction

abbrev Row (l m : ℕ) := Fin l ⊕ Fin m
abbrev Host (l m : ℕ) := Bool × (Row l m → Bool)

noncomputable def bits (l m : ℕ) : FinProb (Row l m → Bool) :=
  FinProb.uniform Finset.univ ⟨fun _ => false, Finset.mem_univ _⟩

noncomputable def comparison (l m : ℕ) : FinProb (Host l m) :=
  FinProb.map (bits l m) (fun ω => (false, ω))

noncomputable def mask (l m : ℕ) : FinProb (Host l m) :=
  FinProb.map (bits l m) (fun ω => (true, ω))

noncomputable def initial (l m : ℕ) (hl : 0 < l) : FinProb (Row l m) :=
  FinProb.map (FinProb.uniform Finset.univ ⟨⟨0, hl⟩, Finset.mem_univ _⟩) Sum.inl

/-- The labels used by the adverse sketch have zero initial-prior weight. -/
theorem initial_unsupported (l m : ℕ) (hl : 0 < l) (t : Fin m) :
    (initial l m hl).w (.inr t) = 0 := by
  simp [initial, FinProb.map]

def hit {l m : ℕ} (x : Row l m) (y : Host l m) : Prop :=
  match x with
  | .inl _ => y.2 x = true
  | .inr _ => y.1 = false ∧ y.2 x = true

noncomputable def indicator {l m : ℕ} (x : Row l m) (y : Host l m) : ℝ :=
  if hit x y then 1 else 0

noncomputable def sign (b : Bool) : ℝ := if b then 1 else -1

private def flip {ι : Type*} [DecidableEq ι] (a : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun ω := Function.update ω a (!ω a)
  invFun ω := Function.update ω a (!ω a)
  left_inv ω := by funext i; by_cases hi : i = a <;> simp [hi]
  right_inv ω := by funext i; by_cases hi : i = a <;> simp [hi]

private theorem bits_flip (l m : ℕ) (a : Row l m) (f : (Row l m → Bool) → ℝ) :
    (bits l m).expect f = (bits l m).expect (fun ω => f (flip a ω)) := by
  unfold FinProb.expect
  apply Fintype.sum_equiv (flip a)
  intro ω
  have hinv : flip a (flip a ω) = ω := (flip a).left_inv ω
  simp [bits, FinProb.uniform, hinv]

private theorem pr_eq_expect {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (fun ω => if A ω then 1 else 0) := by
  unfold FinProb.pr FinProb.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : A ω <;> simp [h]

private theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

private theorem mean_sign (l m : ℕ) (a : Row l m) :
    (bits l m).expect (fun ω => sign (ω a)) = 0 := by
  have hh := bits_flip l m a (fun ω => sign (ω a))
  have hn : (fun ω => sign (flip a ω a)) = (fun ω => (-1 : ℝ) * sign (ω a)) := by
    funext ω
    simp [flip, sign_not]
  rw [hn, FinProb.expect_smul] at hh
  linarith

private theorem mean_sign_pair (l m : ℕ) (a b : Row l m) (hab : a ≠ b) :
    (bits l m).expect (fun ω => sign (ω a) * sign (ω b)) = 0 := by
  have hh := bits_flip l m a (fun ω => sign (ω a) * sign (ω b))
  have hn : (fun ω => sign (flip a ω a) * sign (flip a ω b)) =
      (fun ω => (-1 : ℝ) * (sign (ω a) * sign (ω b))) := by
    funext ω
    simp [flip, hab.symm, sign_not]
  rw [hn, FinProb.expect_smul] at hh
  linarith

private theorem fair_bit (l m : ℕ) (a : Row l m) :
    (bits l m).expect (fun ω => if ω a = true then 1 else 0) = 1 / 2 := by
  have hpoint : (fun ω : Row l m → Bool => sign (ω a)) =
      (fun ω => 2 * (if ω a = true then (1 : ℝ) else 0) + (-1)) := by
    funext ω
    cases ω a <;> norm_num [sign]
  have hh := mean_sign l m a
  rw [hpoint, FinProb.expect_add, FinProb.expect_smul, FinProb.expect_const] at hh
  linarith

private theorem fair_pair (l m : ℕ) (a b : Row l m) (hab : a ≠ b) :
    (bits l m).expect (fun ω => if ω a = true ∧ ω b = true then 1 else 0) = 1 / 4 := by
  have hpoint : (fun ω : Row l m → Bool => sign (ω a) * sign (ω b)) =
      (fun ω => 4 * (if ω a = true ∧ ω b = true then (1 : ℝ) else 0) +
        ((-2) * (if ω a = true then (1 : ℝ) else 0) +
          ((-2) * (if ω b = true then (1 : ℝ) else 0) + 1))) := by
    funext ω
    cases ω a <;> cases ω b <;> norm_num [sign]
  have hh := mean_sign_pair l m a b hab
  rw [hpoint, FinProb.expect_add, FinProb.expect_smul, FinProb.expect_add,
    FinProb.expect_smul, FinProb.expect_add, FinProb.expect_smul,
    FinProb.expect_const, fair_bit, fair_bit] at hh
  linarith

/-- The supported labels have exactly the first moment required by R2. -/
theorem initial_single_moment (l m : ℕ) (x : Fin l) :
    (mask l m).expect (indicator (.inl x)) = 1 / 2 := by
  rw [mask, FinProb.map_expect]
  convert fair_bit l m (.inl x) using 1
  congr 1
  funext ω
  by_cases hx : ω (.inl x) = true <;> simp [indicator, hit, hx]

/-- Every distinct supported pair has exactly the second moment required by R2. -/
theorem initial_pair_moment (l m : ℕ) (x z : Fin l) (hxz : x ≠ z) :
    (mask l m).pr (fun y => hit (.inl x) y ∧ hit (.inl z) y) = 1 / 4 := by
  rw [pr_eq_expect]
  rw [mask, FinProb.map_expect]
  convert fair_pair l m (.inl x) (.inl z) (by simpa using hxz) using 1
  congr 1
  funext ω
  by_cases hx : ω (.inl x) = true <;> by_cases hz : ω (.inl z) = true <;> simp [hit, hx, hz]

noncomputable def correlation {l m : ℕ} (x z : Row l m) : ℝ :=
  (comparison l m).expect (fun y => (2 * indicator x y - 1) * (2 * indicator z y - 1))

/-- Under the comparison law only equal sketch labels conflict. -/
theorem correlation_eq (l m : ℕ) (x z : Row l m) :
    correlation x z = if x = z then 1 else 0 := by
  unfold correlation comparison
  rw [FinProb.map_expect]
  have hp (x : Row l m) (ω : Row l m → Bool) :
      2 * indicator x (false, ω) - 1 = sign (ω x) := by
    cases x <;> cases h : ω _ <;> norm_num [indicator, hit, sign, h]
  simp_rw [hp]
  by_cases hxz : x = z
  · subst z
    simp only [ite_true]
    have hp : (fun ω : Row l m → Bool => sign (ω x) * sign (ω x)) = fun _ => (1 : ℝ) := by
      funext ω
      cases ω x <;> norm_num [sign]
    rw [hp, FinProb.expect_const]
  · rw [ite_eq_right hxz]
    exact mean_sign_pair l m x z hxz

/-- A distinct unsupported sketch has diagonal conflict fraction 1/m. -/
theorem sketch_conflict_fraction (l m : ℕ) (hm : 0 < m) (ξ : ℝ)
    (hξ : 0 ≤ ξ) (hξ1 : ξ < 1) :
    (∑ t : Fin m, ∑ u : Fin m,
      if ξ < |correlation (.inr t : Row l m) (.inr u)| then (1 : ℝ) else 0) /
        (m : ℝ) ^ 2 = 1 / m := by
  have hp (t u : Fin m) :
      (if ξ < |correlation (.inr t : Row l m) (.inr u)| then (1 : ℝ) else 0) =
        if t = u then 1 else 0 := by
    rw [correlation_eq]
    by_cases htu : t = u <;> simp [htu, hξ1, not_lt.mpr hξ]
  simp_rw [hp]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- Nevertheless its hit fraction under the masked law is identically zero. -/
theorem sketch_hit_zero (l m : ℕ) (ω : Row l m → Bool) :
    (∑ t : Fin m, indicator (.inr t) (true, ω)) / (m : ℝ) = 0 := by
  simp [indicator, hit]

/-- For every positive threshold the first test retains zero mask mass. -/
theorem retention_zero (l m : ℕ) (e : ℝ) (he : e < 1 / 2) :
    (mask l m).pr (fun y => 1 / 2 - e ≤
      (∑ t : Fin m, indicator (.inr t) y) / (m : ℝ)) = 0 := by
  rw [pr_eq_expect]
  rw [mask, FinProb.map_expect]
  have hh : ¬ 1 / 2 - e ≤ (0 : ℝ) := by linarith
  simp_rw [sketch_hit_zero, ite_eq_right hh]
  exact FinProb.expect_const _ 0

/-- Small positive errors do not make the conflict hypothesis impossible. -/
theorem exists_sketch_size (e : ℝ) (he : 0 < e) :
    ∃ m : ℕ, 0 < m ∧ 1 / (m : ℝ) ≤ 2 * e ^ 4 := by
  let m := ⌈1 / (2 * e ^ 4)⌉₊ + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have he4 : 0 < 2 * e ^ 4 := by positivity
  have hc : 1 / (2 * e ^ 4) ≤ (m : ℝ) := by
    have hh := Nat.le_ceil (1 / (2 * e ^ 4))
    dsimp [m]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨m, hm, (div_le_iff₀ hmR).mpr ?_⟩
  have hh := (div_le_iff₀ he4).mp hc
  nlinarith

/-- Local R1 and supported R2 moment estimates coexist with zero retention.
This holds for arbitrarily small e, by choosing m with 1/m ≤ 2e^4. -/
theorem local_obstruction (l m : ℕ) (hm : 0 < m) (e ξ : ℝ) (he : e < 1 / 2)
    (hξ : 0 ≤ ξ) (hξ1 : ξ < 1) (hconf : 1 / (m : ℝ) ≤ 2 * e ^ 4) :
    ((∑ t : Fin m, ∑ u : Fin m,
      if ξ < |correlation (.inr t : Row l m) (.inr u)| then (1 : ℝ) else 0) /
        (m : ℝ) ^ 2 ≤ 2 * e ^ 4) ∧
    (∀ x : Fin l, (mask l m).expect (indicator (.inl x)) = 1 / 2) ∧
    (∀ x z : Fin l, |correlation (.inl x : Row l m) (.inl z)| ≤ ξ →
      (mask l m).pr (fun y => hit (.inl x) y ∧ hit (.inl z) y) = 1 / 4) ∧
    (mask l m).pr (fun y => 1 / 2 - e ≤
      (∑ t : Fin m, indicator (.inr t) y) / (m : ℝ)) = 0 := by
  refine ⟨?_, initial_single_moment l m, ?_, retention_zero l m e he⟩
  · rw [sketch_conflict_fraction l m hm ξ hξ hξ1]
    exact hconf
  · intro x z hnc
    apply initial_pair_moment l m x z
    intro hxz
    subst z
    rw [correlation_eq] at hnc
    norm_num at hnc
    linarith

end Obstruction
end HypercubeRamsey.Lane_sol_s18_1b
