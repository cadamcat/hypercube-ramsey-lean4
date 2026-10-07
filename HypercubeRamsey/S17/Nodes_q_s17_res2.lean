import HypercubeRamsey.S17.Needs
import HypercubeRamsey.Framework.FinProbLemmas
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Finite-product tools for lane q-s17-res2

These lemmas only bridge the project's `FinLaw` notation to the already
proved product-expectation facts for `FinProb`.
-/

namespace HypercubeRamsey
namespace Lane_q_s17_res2

open Classical

theorem law_ext {Ω : Type*} [Fintype Ω] {P Q : FinLaw Ω}
    (h : ∀ ω, P.w ω = Q.w ω) : P = Q := by
  cases P with
  | mk w₁ hnon₁ hsum₁ =>
    cases Q with
    | mk w₂ hnon₂ hsum₂ =>
      have hw : w₁ = w₂ := funext h
      cases hw
      rfl

theorem nonempty_of_finLaw {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : Nonempty Ω := by
  classical
  by_contra h
  haveI : IsEmpty Ω := ⟨fun x => h ⟨x⟩⟩
  have hsum : (∑ x, P.w x) = 0 := by simp
  rw [P.sum_one] at hsum
  norm_num at hsum

noncomputable def asFinProb {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : FinProb Ω where
  w := P.w
  nonneg := P.nonneg
  sum_eq_one := P.sum_one

theorem asFinProb_pr {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    (asFinProb P).pr A = P.pr A := by
  classical
  unfold FinProb.pr FinLaw.pr asFinProb
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hA : A ω <;> simp [hA]

theorem pi_expect_mul_of_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i))
    (f g : (∀ i, Ω i) → ℝ) (s t : Finset ι)
    (hf : FinProb.DependsOn f s) (hg : FinProb.DependsOn g t)
    (hst : Disjoint s t) :
    (FinLaw.pi P).E (fun ω => f ω * g ω) =
      (FinLaw.pi P).E f * (FinLaw.pi P).E g := by
  have h := FinProb.pi_expect_mul_of_disjoint (fun i => asFinProb (P i))
    f g s t hf hg hst
  simpa [FinProb.expect, FinLaw.E, FinProb.pi, FinLaw.pi, asFinProb] using h

theorem pi_expect_depends
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) (ω₀ : ∀ i, Ω i)
    (hf : FinProb.DependsOn f s) :
    (FinLaw.pi P).E f =
      (FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).E
        (fun a => f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm
          (a, fun i => ω₀ i.1))) := by
  have h := FinProb.pi_expect_depends (fun i => asFinProb (P i)) s f ω₀ hf
  simpa [FinProb.expect, FinLaw.E, FinProb.pi, FinLaw.pi, asFinProb] using h

theorem pi_marginal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (s : Finset ι)
    (a : ∀ i : {i // i ∈ s}, Ω i.1) :
    (FinLaw.map (FinLaw.pi P) (fun ω (i : {i // i ∈ s}) => ω i.1)).w a =
      (FinLaw.pi (fun i : {i // i ∈ s} => P i.1)).w a := by
  have h := FinProb.pi_marginal (fun i => asFinProb (P i)) s a
  simpa [FinProb.map, FinLaw.map, FinProb.pi, FinLaw.pi, asFinProb] using h

theorem pi_eval_weight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (x : Ω i) :
    (FinLaw.map (FinLaw.pi P) (fun ω => ω i)).w x = (P i).w x := by
  classical
  let s : Finset ι := {i}
  let a : ∀ j : {j // j ∈ s}, Ω j.1 := fun j =>
    cast (congrArg Ω (Finset.mem_singleton.mp j.2).symm) x
  have hMarg := pi_marginal P s a
  have hFiber : ∀ ω : (∀ j, Ω j),
      (ω i = x) ↔ (fun j : {j // j ∈ s} => ω j.1) = a := by
    intro ω
    constructor
    · intro hx
      funext q
      rcases q with ⟨q, hq⟩
      have hq' : q = i := Finset.mem_singleton.mp (by simpa [s] using hq)
      subst q
      simp [a, hx]
    · intro hf
      have h := congrFun hf ⟨i, by simp [s]⟩
      simpa [a, s] using h
  have hMap :
      (FinLaw.map (FinLaw.pi P) (fun ω => ω i)).w x =
        (FinLaw.map (FinLaw.pi P)
          (fun ω (j : {j // j ∈ s}) => ω j.1)).w a := by
    unfold FinLaw.map
    apply Finset.sum_congr rfl
    intro ω hω
    simp only [hFiber ω]
  calc
    (FinLaw.map (FinLaw.pi P) (fun ω => ω i)).w x =
        (FinLaw.map (FinLaw.pi P)
          (fun ω (j : {j // j ∈ s}) => ω j.1)).w a := hMap
    _ = (FinLaw.pi (fun j : {j // j ∈ s} => P j.1)).w a := hMarg
    _ = (P i).w x := by
      haveI : Subsingleton {j // j ∈ s} := by
        refine ⟨?_⟩
        intro q r
        apply Subtype.ext
        exact (Finset.mem_singleton.mp q.2).trans
          (Finset.mem_singleton.mp r.2).symm
      simp [FinLaw.pi, a, s]

theorem map_pi
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω Β : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Β i)]
    [DecidableEq (∀ i, Β i)]
    (P : ∀ i, FinLaw (Ω i)) (g : ∀ i, Ω i → Β i) :
    FinLaw.map (FinLaw.pi P) (fun ω i => g i (ω i)) =
      FinLaw.pi (fun i => FinLaw.map (P i) (g i)) := by
  classical
  apply law_ext
  intro b
  change
    (∑ ω : (∀ i, Ω i),
      if (fun i => g i (ω i)) = b then ∏ i, (P i).w (ω i) else 0) =
      ∏ i, ∑ x : Ω i, if g i x = b i then (P i).w x else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : ∀ i, g i (ω i) = b i
  · have hf : (fun i => g i (ω i)) = b := funext h
    simp [h, hf]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    have hf : (fun i => g i (ω i)) ≠ b := by
      intro heq
      apply h
      intro j
      simpa using congrFun heq j
    rw [if_neg hf]
    have hzero : (∏ i, if g i (ω i) = b i then (P i).w (ω i) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [hzero]

theorem E_mono
    {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) {f g : Ω → ℝ}
    (hfg : ∀ ω, f ω ≤ g ω) : P.E f ≤ P.E g := by
  unfold FinLaw.E
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hfg ω) (P.nonneg ω)

private theorem finProb_pr_iUnion_le_sum
    {Ω α : Type*} [Fintype Ω] [Fintype α]
    (P : FinProb Ω) (E : α → Ω → Prop) :
    ∀ s : Finset α,
      P.pr (fun ω => ∃ a ∈ s, E a ω) ≤ ∑ a ∈ s, P.pr (E a) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => simp [FinProb.pr]
  | @insert a s ha ih =>
      calc
        P.pr (fun ω => ∃ b ∈ insert a s, E b ω) =
            P.pr (fun ω => E a ω ∨ ∃ b ∈ s, E b ω) := by
              congr 1
              funext ω
              simp [ha]
        _ ≤ P.pr (E a) + P.pr (fun ω => ∃ b ∈ s, E b ω) :=
          FinProb.pr_union P (E a) (fun ω => ∃ b ∈ s, E b ω)
        _ ≤ P.pr (E a) + ∑ b ∈ s, P.pr (E b) :=
          add_le_add (le_rfl) ih
        _ = ∑ b ∈ insert a s, P.pr (E b) := by rw [Finset.sum_insert ha]

theorem pr_iUnion_le_sum
    {Ω α : Type*} [Fintype Ω] [Fintype α]
    (P : FinLaw Ω) (E : α → Ω → Prop) :
    P.pr (fun ω => ∃ a, E a ω) ≤ ∑ a, P.pr (E a) := by
  have h := finProb_pr_iUnion_le_sum (asFinProb P) E Finset.univ
  have h' : (asFinProb P).pr (fun ω => ∃ a, E a ω) ≤
      ∑ a, (asFinProb P).pr (E a) := by simpa using h
  calc
    P.pr (fun ω => ∃ a, E a ω) = (asFinProb P).pr (fun ω => ∃ a, E a ω) :=
      (asFinProb_pr P _).symm
    _ ≤ ∑ a, (asFinProb P).pr (E a) := h'
    _ = ∑ a, P.pr (E a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact asFinProb_pr P (E a)

theorem pr_mono
    {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) {A B : Ω → Prop}
    (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hB : B ω
  · by_cases hA : A ω
    · simp [hA, hB]
    · simp [hA, hB, P.nonneg ω]
  · have hA : ¬ A ω := fun h => hB (hAB ω h)
    simp [hA, hB]

theorem sum_geometric_tail
    {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (s M : ℕ) :
    (∑ m ∈ (Finset.range (M + 1)).filter (fun m => s ≤ m), q ^ m) ≤
      2 * q ^ s := by
  classical
  let S : Finset ℕ := (Finset.range (M + 1)).filter (fun m => s ≤ m)
  let shift : ℕ → ℕ := fun m => m - s
  have hinj : (S : Set ℕ).InjOn shift := by
    intro a ha b hb hab
    have ha' : a ∈ S := ha
    have hb' : b ∈ S := hb
    change a ∈ (Finset.range (M + 1)).filter (fun m => s ≤ m) at ha'
    change b ∈ (Finset.range (M + 1)).filter (fun m => s ≤ m) at hb'
    simp only [Finset.mem_filter, Finset.mem_range] at ha' hb'
    dsimp [shift] at hab
    omega
  have hsumImage : (∑ m ∈ S, q ^ shift m) = ∑ r ∈ S.image shift, q ^ r := by
    rw [← Finset.sum_image hinj]
  have hImageSubset : S.image shift ⊆ Finset.range (M + 1) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨m, hm, rfl⟩
    have hm' : m ∈ S := hm
    change m ∈ (Finset.range (M + 1)).filter (fun n => s ≤ n) at hm'
    simp only [Finset.mem_filter, Finset.mem_range] at hm'
    simp only [Finset.mem_range]
    have hshift : m - s < M + 1 := by omega
    simpa [shift] using hshift
  have hsmall : ∀ r, q ^ r ≤ (1 / 2 : ℝ) ^ r := by
    intro r
    gcongr
  have hsumSmall : (∑ r ∈ S.image shift, q ^ r) ≤ 2 := by
    calc
      _ ≤ ∑ r ∈ S.image shift, (1 / (2 : ℝ)) ^ r := by
        apply Finset.sum_le_sum
        intro r hr
        exact hsmall r
      _ ≤ ∑ r ∈ Finset.range (M + 1), (1 / (2 : ℝ)) ^ r := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hImageSubset
        intro r hr hnr
        exact pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) r
      _ ≤ 2 := sum_geometric_two_le (M + 1)
  have hpoint : ∀ m ∈ S, q ^ m ≤ q ^ s * q ^ shift m := by
    intro m hm
    have hms : s ≤ m := (Finset.mem_filter.mp hm).2
    rw [← pow_add, Nat.add_sub_of_le hms]
  calc
    (∑ m ∈ S, q ^ m) ≤ ∑ m ∈ S, q ^ s * q ^ shift m :=
      Finset.sum_le_sum hpoint
    _ = q ^ s * ∑ m ∈ S, q ^ shift m := by rw [Finset.mul_sum]
    _ ≤ q ^ s * 2 := by
      rw [hsumImage]
      exact mul_le_mul_of_nonneg_left hsumSmall (pow_nonneg hq0 s)
    _ = 2 * q ^ s := by ring
    _ = 2 * q ^ s := by ring

theorem fin_depth_eq_of_step
    {n : ℕ} (d e : Fin (n + 1) → ℕ)
    (hend : d (Fin.last n) = e (Fin.last n))
    (hbound : ∀ j : Fin n,
      d j.succ ≤ d j.castSucc + 2 ∧ e j.succ ≤ e j.castSucc + 2)
    (hstep : ∀ j : Fin n,
      d j.castSucc + 2 - d j.succ = e j.castSucc + 2 - e j.succ) :
    d = e := by
  induction n with
  | zero =>
      funext i
      induction i using Fin.lastCases with
      | last => exact hend
      | cast i => exact Fin.elim0 i
  | succ n ih =>
      have hprev : d (Fin.castSucc (Fin.last n)) = e (Fin.castSucc (Fin.last n)) := by
        have hD : d (Fin.last (n + 1)) ≤ d (Fin.castSucc (Fin.last n)) + 2 := by
          simpa only [Fin.succ_last] using (hbound (Fin.last n)).1
        have hE : e (Fin.last (n + 1)) ≤ e (Fin.castSucc (Fin.last n)) + 2 := by
          simpa only [Fin.succ_last] using (hbound (Fin.last n)).2
        have hStepLast :
            d (Fin.castSucc (Fin.last n)) + 2 - d (Fin.last (n + 1)) =
              e (Fin.castSucc (Fin.last n)) + 2 - e (Fin.last (n + 1)) := by
          simpa only [Fin.succ_last] using hstep (Fin.last n)
        have hDcancel := Nat.sub_add_cancel hD
        have hEcancel := Nat.sub_add_cancel hE
        rw [hStepLast] at hDcancel
        rw [hend] at hDcancel
        rw [hEcancel] at hDcancel
        omega
      have hinit : Fin.init d = Fin.init e := by
        apply ih
        · exact hprev
        · intro j
          have hNext : (j.castSucc).succ = (j.succ).castSucc := by
            apply Fin.ext
            rfl
          simpa only [Fin.init, hNext] using hbound j.castSucc
        · intro j
          have hs := hstep j.castSucc
          have hNext : (j.castSucc).succ = (j.succ).castSucc := by
            apply Fin.ext
            rfl
          simpa only [Fin.init, hNext] using hs
      funext i
      induction i using Fin.lastCases with
      | cast j => exact congrFun hinit j
      | last => exact hend

theorem sum_range_depth_gaps (m : ℕ) (d : ℕ → ℕ)
    (hbound : ∀ i < m, d (i + 1) ≤ d i + 2) :
    (∑ i ∈ Finset.range m, (d i + 2 - d (i + 1))) + d m = d 0 + 2 * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hlast := hbound m (Nat.lt_succ_self m)
      have hcancel := Nat.sub_add_cancel hlast
      rw [Finset.sum_range_succ]
      calc
        _ = (∑ i ∈ Finset.range m, (d i + 2 - d (i + 1))) +
              ((d m + 2 - d (m + 1)) + d (m + 1)) := by omega
        _ = (∑ i ∈ Finset.range m, (d i + 2 - d (i + 1))) + (d m + 2) := by
              rw [hcancel]
        _ = ((∑ i ∈ Finset.range m, (d i + 2 - d (i + 1))) + d m) + 2 := by omega
        _ = (d 0 + 2 * m) + 2 := by rw [ih (by intro i hi; exact hbound i (by omega))]
        _ = d 0 + 2 * (m + 1) := by omega

theorem map_E
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  have h := FinProb.map_expect (asFinProb P) f g
  simpa [FinProb.expect, FinLaw.E, FinProb.map, FinLaw.map, asFinProb] using h

theorem map_equiv_weight
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (e : α ≃ β) (y : β) :
    (FinLaw.map P e).w y = P.w (e.symm y) := by
  classical
  change (∑ x, if e x = y then P.w x else 0) = P.w (e.symm y)
  rw [Finset.sum_eq_single (e.symm y)]
  · simp
  · intro x hx hxne
    have he : e x ≠ y := fun h => hxne (e.injective (by simpa using h))
    simp [he]
  · simp

theorem pi_expect_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω Β : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Β i)]
    [DecidableEq (∀ i, Β i)]
    (P : ∀ i, FinLaw (Ω i)) (g : ∀ i, Ω i → Β i)
    (F : (∀ i, Β i) → ℝ) :
    (FinLaw.pi P).E (fun ω => F (fun i => g i (ω i))) =
      (FinLaw.pi (fun i => FinLaw.map (P i) (g i))).E F := by
  rw [← map_E (FinLaw.pi P) (fun ω i => g i (ω i)) F]
  rw [map_pi]

abbrev TapeCoordinate
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (Ts : ℕ) :=
  Σ C : D.G.Cell, Fin (Ts + 2)

abbrev FlatTapes
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (Ts : ℕ) :=
  ∀ i : TapeCoordinate D Ts, TapeEntry D.F i.1

def flattenTapes
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (Ts : ℕ) :
    Tapes D.F Ts ≃ FlatTapes D Ts where
  toFun t i := t i.1 i.2
  invFun t C r := t ⟨C, r⟩
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

noncomputable def flatTapeLaw
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (Ts : ℕ) : FinLaw (FlatTapes D Ts) :=
  FinLaw.pi fun i => FinLaw.pi fun P => D.F.fresh i.1 P

theorem tapeLaw_expect_flatten
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (Ts : ℕ)
    (H : FlatTapes D Ts → ℝ) :
    (tapeLaw D.F Ts).E (fun t => H (flattenTapes D Ts t)) =
      (flatTapeLaw D Ts).E H := by
  classical
  let e := flattenTapes D Ts
  rw [FinLaw.E, FinLaw.E, ← Equiv.sum_comp e.symm]
  apply Finset.sum_congr rfl
  intro t _ht
  rw [e.apply_symm_apply]
  congr 1
  change
      (∏ C, ∏ r, ∏ P, (D.F.fresh C P).w (e.symm t C r P)) =
      ∏ i : TapeCoordinate D Ts, ∏ P, (D.F.fresh i.1 P).w (t i P)
  simpa [e, flattenTapes] using
    (Fintype.prod_sigma' (fun C r =>
      ∏ P, (D.F.fresh C P).w (t ⟨C, r⟩ P))).symm

end Lane_q_s17_res2
end HypercubeRamsey
