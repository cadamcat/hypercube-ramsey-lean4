import HypercubeRamsey.S07.FilterNodes
import HypercubeRamsey.S03.Mixtures
import HypercubeRamsey.Framework.FinProbLemmas

/-!
Lane q-s07-prof helpers for the finite menu, subprobability mixture, and simultaneous tag profiles.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable def pointProb_q_s07_prof {α : Type*} [Fintype α] [DecidableEq α] (a : α) : FinProb α where
  w b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  sum_eq_one := by simp

noncomputable def profileSplitEquiv_q_s07_prof {ι α : Type*} (j : ι) :
    (ι → α) ≃ α × ({i : ι // i ≠ j} → α) where
  toFun σ := (σ j, fun i => σ i.1)
  invFun p i := if h : i = j then p.1 else p.2 ⟨i, h⟩
  left_inv σ := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨a, τ⟩
    apply Prod.ext
    · simp
    · funext i
      simp [i.2]

theorem pi_expect_update_split_q_s07_prof {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (P : ι → FinProb α) (j : ι) (R : FinProb α)
    (f : (ι → α) → ℝ) :
    (FinProb.pi (Function.update P j R)).expect f =
      ∑ a, R.w a * (FinProb.pi (fun i : {i : ι // i ≠ j} => P i.1)).expect
        (fun τ => f ((profileSplitEquiv_q_s07_prof j).symm (a, τ))) := by
  classical
  let O := {i : ι // i ≠ j}
  let P₀ : O → FinProb α := fun i => P i.1
  let e : (ι → α) ≃ α × (O → α) := profileSplitEquiv_q_s07_prof j
  have heval (a : α) (τ : O → α) : (e.symm (a, τ)) j = a := by
    simp [e, profileSplitEquiv_q_s07_prof]
  have hevalO (a : α) (τ : O → α) (i : O) : (e.symm (a, τ)) i.1 = τ i := by
    simp [e, profileSplitEquiv_q_s07_prof, i.2]
  have hprod (a : α) (τ : O → α) :
      (∏ i, (Function.update P j R i).w ((e.symm (a, τ)) i)) =
        R.w a * ∏ i : O, (P₀ i).w (τ i) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => (Function.update P j R i).w ((e.symm (a, τ)) i)) j]
    rw [show (Function.update P j R j).w ((e.symm (a, τ)) j) = R.w a by
      simp [heval a τ]]
    congr 1
    apply Fintype.prod_congr
    intro i
    rw [Function.update_of_ne i.2, hevalO a τ i]
  simp only [FinProb.expect, FinProb.pi]
  rw [← Equiv.sum_comp e.symm
    (fun σ => (∏ i, (Function.update P j R i).w (σ i)) * f σ)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [hprod]
  ring

theorem pi_expect_update_mix_q_s07_prof {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (P : ι → FinProb α) (j : ι) (R : FinProb α)
    (f : (ι → α) → ℝ) :
    (FinProb.pi (Function.update P j R)).expect f =
      ∑ a, R.w a * (FinProb.pi (Function.update P j (pointProb_q_s07_prof a))).expect f := by
  classical
  rw [pi_expect_update_split_q_s07_prof]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pi_expect_update_split_q_s07_prof]
  simp [pointProb_q_s07_prof]

theorem pi_expect_coordinate_q_s07_prof {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (P : ι → FinProb α) (j : ι) (f : α → ℝ) :
    (FinProb.pi P).expect (fun σ => f (σ j)) = (P j).expect f := by
  classical
  have h := pi_expect_update_mix_q_s07_prof P j (P j) (fun σ => f (σ j))
  have hpoint (a : α) :
      (FinProb.pi (Function.update P j (pointProb_q_s07_prof a))).expect
        (fun σ => f (σ j)) = f a := by
    rw [pi_expect_update_split_q_s07_prof]
    have hfun (b : α) : (fun τ : {i : ι // i ≠ j} → α =>
        f ((profileSplitEquiv_q_s07_prof j).symm (b, τ) j)) = fun _ => f b := by
      funext τ
      simp [profileSplitEquiv_q_s07_prof]
    change (∑ b : α, (if b = a then 1 else 0) *
      (FinProb.pi (fun i : {i : ι // i ≠ j} => P i.1)).expect
        (fun τ => f ((profileSplitEquiv_q_s07_prof j).symm (b, τ) j))) = f a
    simp_rw [hfun]
    simp_rw [FinProb.expect_const]
    simp
  have h' : (FinProb.pi P).expect (fun σ => f (σ j)) =
      ∑ a, (P j).w a * f a := by
    simp_rw [hpoint] at h
    simpa [Function.update] using h
  have h'' : (FinProb.pi P).expect (fun σ => f (σ j)) =
      (P j).expect f := by
    rw [h']
    rfl
  exact h''

noncomputable def rawCellMean_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (σ : Γ.Key → M.ι) (c : Γ.Cell) (y : Fin N) : ℝ :=
  (rawAnchors Γ M σ).expect (fun W => cellRow Γ M σ W c y)

theorem rawRowMean_eq_expect_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (c : Γ.Cell) (y : Fin N) :
    rawRowMean Γ M Q c y = (FinProb.pi Q).expect (fun σ =>
      rawCellMean_q_s07_prof Γ M σ c y) := rfl

theorem rawRowMean_update_mix_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (g : Γ.Key) (R : FinProb M.ι)
    (c : Γ.Cell) (y : Fin N) :
    rawRowMean Γ M (Function.update Q g R) c y =
      ∑ i, R.w i * rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) c y := by
  simpa [rawRowMean_eq_expect_q_s07_prof, rawCellMean_q_s07_prof] using
    (pi_expect_update_mix_q_s07_prof Q g R
      (rawCellMean_q_s07_prof Γ M · c y))

theorem expect_sum_q_s07_prof {α Ω : Type*} [Fintype α] [Fintype Ω]
    (P : FinProb Ω) (f : α → Ω → ℝ) :
    (∑ a, P.expect (f a)) = P.expect (fun ω => ∑ a, f a ω) := by
  simp only [FinProb.expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [← Finset.mul_sum]

theorem rawRowMean_nonneg_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hrow : RowLaw Γ M) (Q : Γ.Key → FinProb M.ι) (c : Γ.Cell) (y : Fin N) :
    0 ≤ rawRowMean Γ M Q c y := by
  unfold rawRowMean FinProb.expect
  apply Finset.sum_nonneg
  intro σ hσ
  apply mul_nonneg
  · exact (FinProb.pi Q).nonneg σ
  · apply Finset.sum_nonneg
    intro W hW
    exact mul_nonneg ((rawAnchors Γ M σ).nonneg W) ((hrow σ W c).1 y)

theorem rawRowMean_sum_le_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hrow : RowLaw Γ M) (Q : Γ.Key → FinProb M.ι) (c : Γ.Cell) :
    ∑ y, rawRowMean Γ M Q c y ≤ 1 := by
  calc
    ∑ y, rawRowMean Γ M Q c y = (FinProb.pi Q).expect (fun σ => ∑ y,
        (rawAnchors Γ M σ).expect (fun W => cellRow Γ M σ W c y)) := by
          change (∑ y, (FinProb.pi Q).expect (fun σ =>
            (rawAnchors Γ M σ).expect (fun W => cellRow Γ M σ W c y))) = _
          rw [expect_sum_q_s07_prof]
    _ = (FinProb.pi Q).expect (fun σ =>
        (rawAnchors Γ M σ).expect (fun W => ∑ y, cellRow Γ M σ W c y)) := by
          congr 1
          funext σ
          exact expect_sum_q_s07_prof (rawAnchors Γ M σ)
            (fun y W => cellRow Γ M σ W c y)
    _ ≤ (FinProb.pi Q).expect (fun _ => 1) := by
        apply FinProb.expect_mono
        intro σ
        calc
          (rawAnchors Γ M σ).expect (fun W => ∑ y, cellRow Γ M σ W c y) ≤
              (rawAnchors Γ M σ).expect (fun _ => 1) := by
                apply FinProb.expect_mono
                intro W
                exact (hrow σ W c).2.1
          _ = 1 := FinProb.expect_const _ _
    _ = 1 := FinProb.expect_const _ _

theorem rawRowMean_zero_of_nu_atom_zero_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hrow : RowLaw Γ M) (Q : Γ.Key → FinProb M.ι) (g : Γ.Key) (i : M.ι)
    (t : Γ.AuxWord) (y : Fin N) (hν : (M.ν i).w y = 0) :
    rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y = 0 := by
  rw [rawRowMean_eq_expect_q_s07_prof, pi_expect_update_split_q_s07_prof]
  have hfixed : (FinProb.pi (fun k : {k : Γ.Key // k ≠ g} => Q k.1)).expect
      (fun τ => rawCellMean_q_s07_prof Γ M
        ((profileSplitEquiv_q_s07_prof g).symm (i, τ)) (g, t) y) = 0 := by
    unfold FinProb.expect FinProb.pi
    apply Finset.sum_eq_zero
    intro τ hτ
    have htag : ((profileSplitEquiv_q_s07_prof g).symm (i, τ)) g = i := by
      simp [profileSplitEquiv_q_s07_prof]
    have hcell : rawCellMean_q_s07_prof Γ M
        ((profileSplitEquiv_q_s07_prof g).symm (i, τ)) (g, t) y = 0 := by
      unfold rawCellMean_q_s07_prof FinProb.expect
      apply Finset.sum_eq_zero
      intro W hW
      have hrowzero : cellRow Γ M ((profileSplitEquiv_q_s07_prof g).symm (i, τ)) W
          (g, t) y = 0 := by
        by_contra hne
        have hsupp := (hrow _ W (g, t)).2.2.2 y hne
        have hν' : (M.ν (((profileSplitEquiv_q_s07_prof g).symm (i, τ)) (g, t).1)).w y = 0 := by
          simpa [htag] using hν
        exact hsupp.2 hν'
      simp [hrowzero]
    simp [hcell]
  simpa [pointProb_q_s07_prof] using hfixed

theorem rawRowAverage_update_mix_q_s07_prof {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (Q : Γ.Key → FinProb M.ι) (g : Γ.Key) (R : FinProb M.ι) (y : Fin N) (a : ℝ) :
    a * ∑ t : Γ.AuxWord, rawRowMean Γ M (Function.update Q g R) (g, t) y =
      ∑ i, R.w i * (a * ∑ t : Γ.AuxWord,
        rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) := by
  calc
    a * ∑ t : Γ.AuxWord, rawRowMean Γ M (Function.update Q g R) (g, t) y =
        ∑ t : Γ.AuxWord, a * rawRowMean Γ M (Function.update Q g R) (g, t) y := by
          rw [Finset.mul_sum]
    _ = ∑ t : Γ.AuxWord, a *
        ∑ i, R.w i * rawRowMean Γ M
          (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [rawRowMean_update_mix_q_s07_prof]
    _ = ∑ i, ∑ t : Γ.AuxWord, R.w i * (a * rawRowMean Γ M
          (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) := by
          calc
            _ = ∑ t : Γ.AuxWord, ∑ i,
                  R.w i * (a * rawRowMean Γ M
                    (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) := by
                    apply Finset.sum_congr rfl
                    intro t ht
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
            _ = _ := by rw [Finset.sum_comm]
    _ = ∑ i, R.w i * (a * ∑ t : Γ.AuxWord,
          rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            ∑ t : Γ.AuxWord, R.w i * (a * rawRowMean Γ M
                (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) =
              ∑ t : Γ.AuxWord, (R.w i * a) * rawRowMean Γ M
                (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  ring
            _ = (R.w i * a) * ∑ t : Γ.AuxWord,
                rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
                  rw [Finset.mul_sum]
            _ = R.w i * (a * ∑ t : Γ.AuxWord,
                rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) := by ring

theorem menu7_of_available_q_s07_prof {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    {X Y : Finset (Fin N)} {d p κ : ℝ} (hκ : 0 ≤ κ)
    (h : AvailableAt κ (PGridPure G d p).toPatch n N E X Y) :
    Nonempty (Menu7 n N E G X Y d p κ) := by
  classical
  let I := {r : Finset (Fin N) × Finset (Fin N) //
    (r.1.card : ℝ) ≤ κ * N ∧ (r.2.card : ℝ) ≤ κ * N}
  letI : Fintype I := Fintype.ofFinite I
  have hAvail : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N →
      (RY.card : ℝ) ≤ κ * N →
      ∃ A B, (A, B) ∈ (PGridPure G d p).toPatch n N E ∧
        A ⊆ X \ RX ∧ B ⊆ Y \ RY := h
  let makeWitness (r : I) : ∃ μ ν : Law N,
      μ.SupportedIn X ∧ ν.SupportedIn Y ∧ PGridPure G d p n N E μ ν ∧
      (∀ x ∈ r.1.1, μ.w x = 0) ∧ (∀ y ∈ r.1.2, ν.w y = 0) := by
    obtain ⟨A, B, hAB, hAX, hBY⟩ := hAvail r.1.1 r.1.2 r.2.1 r.2.2
    change ∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧
      PGridPure G d p n N E μ ν at hAB
    obtain ⟨μ, ν, hμA, hνB, hpure⟩ := hAB
    refine ⟨μ, ν, ?_, ?_, hpure, ?_, ?_⟩
    · intro x hx
      apply hμA x
      intro hxA
      exact hx (Finset.mem_sdiff.mp (hAX hxA)).1
    · intro y hy
      apply hνB y
      intro hyB
      exact hy (Finset.mem_sdiff.mp (hBY hyB)).1
    · intro x hxRX
      apply hμA x
      intro hxA
      exact (Finset.mem_sdiff.mp (hAX hxA)).2 hxRX
    · intro y hyRY
      apply hνB y
      intro hyB
      exact (Finset.mem_sdiff.mp (hBY hyB)).2 hyRY
  let μsel (i : I) : Law N := Classical.choose (makeWitness i)
  let νsel (i : I) : Law N := Classical.choose (Classical.choose_spec (makeWitness i))
  have selSpec (i : I) :
      (μsel i).SupportedIn X ∧ (νsel i).SupportedIn Y ∧
        PGridPure G d p n N E (μsel i) (νsel i) ∧
        (∀ x ∈ i.1.1, (μsel i).w x = 0) ∧ (∀ y ∈ i.1.2, (νsel i).w y = 0) := by
    exact Classical.choose_spec (Classical.choose_spec (makeWitness i))
  refine ⟨{
    ι := I
    μ := μsel
    ν := νsel
    μ_supp := fun i => (selSpec i).1
    ν_supp := fun i => (selSpec i).2.1
    pure := fun i => (selSpec i).2.2.1
    avail := ?_
  }⟩
  intro RX RY hRX hRY
  let i : I := ⟨(RX, RY), ⟨hRX, hRY⟩⟩
  exact ⟨i, (selSpec i).2.2.2.1, (selSpec i).2.2.2.2⟩

theorem balanced_mixture_sub_q_s07_prof : BalancedSub := by
  classical
  intro N hN ι inst μ v κ hκ hv0 hvsum havail
  by_cases hκlt : κ < 1
  · let ν : ι × Fin N → Law N := fun a => {
      w := fun y => v a.1 y + (1 - ∑ z, v a.1 z) * (Law.dirac a.2).w y
      nonneg := fun y => add_nonneg (hv0 a.1 y)
        (mul_nonneg (sub_nonneg.mpr (hvsum a.1)) ((Law.dirac a.2).nonneg y))
      sum_eq_one := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, (Law.dirac a.2).sum_eq_one]
        linarith [hvsum a.1]
    }
    have havail' : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N →
        (RY.card : ℝ) ≤ κ * N →
        ∃ a : ι × Fin N, (∀ x ∈ RX, (μ a.1).w x = 0) ∧
          (∀ y ∈ RY, (ν a).w y = 0) := by
      intro RX RY hRX hRY
      obtain ⟨i, hiμ, hiv⟩ := havail RX RY hRX hRY
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hRlt : (RY.card : ℝ) < (N : ℝ) := by
        calc
          (RY.card : ℝ) ≤ κ * N := hRY
          _ < 1 * (N : ℝ) := mul_lt_mul_of_pos_right hκlt hNreal
          _ = (N : ℝ) := by ring
      have hcard : RY.card < N := by exact_mod_cast hRlt
      have hex : ∃ y : Fin N, y ∉ RY := by
        by_contra hno
        have hsub : (Finset.univ : Finset (Fin N)) ⊆ RY := by
          intro y hyU
          by_contra hyR
          exact hno ⟨y, hyR⟩
        have hle := Finset.card_le_card hsub
        have hNle : N ≤ RY.card := by simpa using hle
        omega
      obtain ⟨y₀, hy₀⟩ := hex
      refine ⟨(i, y₀), hiμ, ?_⟩
      intro y hy
      have hyne : y ≠ y₀ := by
        intro heq
        subst y
        exact hy₀ hy
      have hdirac : (Law.dirac y₀).w y = 0 := by simp [Law.dirac, hyne]
      rw [show (ν (i, y₀)).w y =
        v i y + (1 - ∑ z, v i z) * (Law.dirac y₀).w y by rfl]
      rw [hiv y hy, hdirac]
      simp
    obtain ⟨t₀, ht₀, ht₁, hμbound, hνbound⟩ :=
      balanced_mixture hN (fun a : ι × Fin N => μ a.1) ν κ hκ havail'
    let t : FinProb (ι × Fin N) := {
      w := t₀
      nonneg := ht₀
      sum_eq_one := ht₁
    }
    let ρ : FinProb ι := {
      w := fun i => ∑ y : Fin N, t.w (i, y)
      nonneg := fun i => Finset.sum_nonneg fun y _ => t.nonneg (i, y)
      sum_eq_one := by
        simpa only [Fintype.sum_prod_type] using t.sum_eq_one
    }
    refine ⟨ρ, ?_, ?_⟩
    · intro x
      have heq : (∑ i, ρ.w i * (μ i).w x) =
          ∑ a : ι × Fin N, t.w a * (μ a.1).w x := by
        calc
          _ = ∑ i, ∑ y : Fin N, t.w (i, y) * (μ i).w x := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [ρ]
            rw [Finset.sum_mul]
          _ = ∑ a : ι × Fin N, t.w a * (μ a.1).w x := by
            rw [Fintype.sum_prod_type]
      rw [heq]
      exact hμbound x
    · intro y
      have heq : (∑ i, ρ.w i * v i y) =
          ∑ a : ι × Fin N, t.w a * v a.1 y := by
        calc
          _ = ∑ i, ∑ z : Fin N, t.w (i, z) * v i y := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [ρ]
            rw [Finset.sum_mul]
          _ = ∑ a : ι × Fin N, t.w a * v a.1 y := by
            rw [Fintype.sum_prod_type]
      have hvle : ∀ a : ι × Fin N, v a.1 y ≤ (ν a).w y := by
        intro a
        dsimp [ν]
        exact le_add_of_nonneg_right
          (mul_nonneg (sub_nonneg.mpr (hvsum a.1)) ((Law.dirac a.2).nonneg y))
      rw [heq]
      calc
        _ ≤ ∑ a : ι × Fin N, t.w a * (ν a).w y := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hvle a) (t.nonneg a)
        _ ≤ 4 / (κ * N) := hνbound y
  · have hκge : 1 ≤ κ := le_of_not_gt hκlt
    have hbudget : ((Finset.univ : Finset (Fin N)).card : ℝ) ≤ κ * N := by
      rw [Finset.card_fin]
      have hNreal : 0 ≤ (N : ℝ) := by positivity
      nlinarith
    obtain ⟨i, hi, _⟩ := havail (Finset.univ) ∅ hbudget (by
      simp
      exact mul_nonneg hκ.le (by positivity))
    have hzero : ∑ x : Fin N, (μ i).w x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact hi x (by simp)
    rw [(μ i).sum_eq_one] at hzero
    norm_num at hzero

theorem grid_profiles_q_s07_prof (hBS : BalancedSub) {d : ℝ} {n s ℓ q N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ}
    (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hκ : 0 < κ) (hN : 0 < N) (hrow : RowLaw Γ M) :
    Nonempty (Profiles7 Γ M (4 / κ)) := by
  classical
  letI : DecidableEq Γ.Key := Fintype.decidablePiFintype
  letI : Fintype M.ι := M.fin
  letI : DecidableEq M.ι := Classical.decEq _
  have hκN : 0 ≤ κ * (N : ℝ) := mul_nonneg hκ.le (by positivity)
  have hzeroBudget : ((∅ : Finset (Fin N)).card : ℝ) ≤ κ * N := by
    simpa using hκN
  have hMne : Nonempty M.ι := by
    obtain ⟨i, _, _⟩ := M.avail ∅ ∅ hzeroBudget hzeroBudget
    exact ⟨i⟩
  letI : Nonempty M.ι := hMne
  let coeff : ℝ := ((2 : ℝ) ^ q)⁻¹
  have hcoeff0 : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hAuxCard : Fintype.card Γ.AuxWord = 2 ^ q := by
    simp [GridGeom.AuxWord, Γ.aux_card]
  have hAuxCardR : (Fintype.card Γ.AuxWord : ℝ) = (2 : ℝ) ^ q := by
    exact_mod_cast hAuxCard
  have hcoeff : coeff * (Fintype.card Γ.AuxWord : ℝ) = 1 := by
    dsimp [coeff]
    rw [hAuxCardR]
    exact inv_mul_cancel₀ (by positivity)
  let decode : Fin (N + N) → Sum (Fin N) (Fin N) :=
    finSumFinEquiv.symm
  let Xout : ∀ g : Γ.Key, (∀ k, M.ι) → Fin (N + N) → ℝ := fun g σ r =>
    match decode r with
    | Sum.inl x => (N : ℝ) * (M.μ (σ g)).w x
    | Sum.inr y => (N : ℝ) *
        (coeff * ∑ t : Γ.AuxWord, rawCellMean_q_s07_prof Γ M σ (g, t) y)
  let m : Γ.Key → ℕ := fun _ => N + N
  let b : ∀ g : Γ.Key, Fin (m g) → ℝ := fun _ _ => 4 / κ
  have hresp : ∀ g (qprof : ∀ k : Γ.Key, M.ι → ℝ),
      (∀ k i, 0 ≤ qprof k i) → (∀ k, ∑ i, qprof k i = 1) →
      ∃ qg : M.ι → ℝ, (∀ i, 0 ≤ qg i) ∧ ∑ i, qg i = 1 ∧
        ∀ r, ∑ σ : (∀ k : Γ.Key, M.ι),
          (∏ k, (Function.update qprof g qg) k (σ k)) * Xout g σ r ≤ b g r := by
    intro g qprof hq0 hqsum
    let Q : Γ.Key → FinProb M.ι := fun k =>
      ⟨qprof k, hq0 k, hqsum k⟩
    let v : M.ι → Fin N → ℝ := fun i y =>
      coeff * ∑ t : Γ.AuxWord,
        rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y
    have hv0 : ∀ i y, 0 ≤ v i y := by
      intro i y
      dsimp [v]
      apply mul_nonneg hcoeff0
      apply Finset.sum_nonneg
      intro t ht
      exact rawRowMean_nonneg_q_s07_prof Γ M hrow
        (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y
    have hvsum : ∀ i, ∑ y, v i y ≤ 1 := by
      intro i
      have htbound (t : Γ.AuxWord) :
          ∑ y, rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y ≤ 1 :=
        rawRowMean_sum_le_q_s07_prof Γ M hrow
          (Function.update Q g (pointProb_q_s07_prof i)) (g, t)
      have hfubini :
          (∑ y, coeff * ∑ t : Γ.AuxWord,
            rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y) =
          coeff * ∑ t : Γ.AuxWord, ∑ y,
            rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
        calc
          _ = ∑ y, ∑ t : Γ.AuxWord, coeff *
              rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.mul_sum]
          _ = ∑ t : Γ.AuxWord, ∑ y, coeff *
              rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
                rw [Finset.sum_comm]
          _ = ∑ t : Γ.AuxWord, coeff * ∑ y,
              rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
                apply Finset.sum_congr rfl
                intro t ht
                rw [Finset.mul_sum]
          _ = coeff * ∑ t : Γ.AuxWord, ∑ y,
              rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
                rw [← Finset.mul_sum]
      calc
        ∑ y, v i y = coeff * ∑ t : Γ.AuxWord, ∑ y,
            rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y := by
              simpa [v] using hfubini
        _ ≤ coeff * (Fintype.card Γ.AuxWord : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ hcoeff0
              calc
                ∑ t : Γ.AuxWord, ∑ y,
                    rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y ≤
                    ∑ t : Γ.AuxWord, (1 : ℝ) := by
                      apply Finset.sum_le_sum
                      intro t ht
                      exact htbound t
                _ = (Fintype.card Γ.AuxWord : ℝ) := by simp
        _ = 1 := hcoeff
    have havailV : ∀ RX RY : Finset (Fin N), (RX.card : ℝ) ≤ κ * N →
        (RY.card : ℝ) ≤ κ * N →
        ∃ i, (∀ x ∈ RX, (M.μ i).w x = 0) ∧ (∀ y ∈ RY, v i y = 0) := by
      intro RX RY hRX hRY
      obtain ⟨i, hiμ, hiν⟩ := M.avail RX RY hRX hRY
      refine ⟨i, hiμ, ?_⟩
      intro y hy
      have hzero : ∀ t : Γ.AuxWord,
          rawRowMean Γ M (Function.update Q g (pointProb_q_s07_prof i)) (g, t) y = 0 := by
        intro t
        exact rawRowMean_zero_of_nu_atom_zero_q_s07_prof Γ M hrow Q g i t y (hiν y hy)
      dsimp [v]
      simp_rw [hzero]
      simp
    obtain ⟨T, hμbound, hvbound⟩ :=
      hBS hN M.μ v κ hκ hv0 hvsum havailV
    let P' : Γ.Key → FinProb M.ι := Function.update Q g T
    have hweights : ∀ σ : (∀ k : Γ.Key, M.ι),
        (∏ k, (Function.update qprof g T.w) k (σ k)) =
          (∏ k, (P' k).w (σ k)) := by
      intro σ
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hkg : k = g
      · subst k
        simp [P', Q]
      · simp [P', Q, hkg]
    have hpayexp (F : (∀ k : Γ.Key, M.ι) → ℝ) :
        (∑ σ : (∀ k : Γ.Key, M.ι),
          (∏ k, (Function.update qprof g T.w) k (σ k)) * F σ) =
          (FinProb.pi P').expect F := by
      simp only [FinProb.expect, FinProb.pi]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hweights]
    refine ⟨T.w, T.nonneg, T.sum_eq_one, ?_⟩
    intro r
    cases hd : decode r with
    | inl x =>
        have hEq :
            (∑ σ : (∀ k : Γ.Key, M.ι),
              (∏ k, (Function.update qprof g T.w) k (σ k)) * Xout g σ r) =
            (N : ℝ) * ∑ i, T.w i * (M.μ i).w x := by
          calc
            _ = (∑ σ : (∀ k : Γ.Key, M.ι),
                  (∏ k, (Function.update qprof g T.w) k (σ k)) *
                    ((N : ℝ) * (M.μ (σ g)).w x)) := by
                  apply Finset.sum_congr rfl
                  intro σ hσ
                  simp [Xout, hd]
            _ = (FinProb.pi P').expect (fun σ =>
                  (N : ℝ) * (M.μ (σ g)).w x) := hpayexp _
            _ = (N : ℝ) * ∑ i, T.w i * (M.μ i).w x := by
                  have hcoord := pi_expect_coordinate_q_s07_prof P' g
                    (fun i => (M.μ i).w x)
                  rw [FinProb.expect_smul, hcoord]
                  simp [P', FinProb.expect]
        have hscale : (N : ℝ) * (4 / (κ * (N : ℝ))) = 4 / κ := by
          field_simp [ne_of_gt hκ, (show (N : ℝ) ≠ 0 by positivity)]
        calc
          (∑ σ : (∀ k : Γ.Key, M.ι),
              (∏ k, (Function.update qprof g T.w) k (σ k)) * Xout g σ r) =
            (N : ℝ) * ∑ i, T.w i * (M.μ i).w x := hEq
          _ ≤ (N : ℝ) * (4 / (κ * (N : ℝ))) :=
            mul_le_mul_of_nonneg_left (hμbound x) (by positivity)
          _ = 4 / κ := hscale
    | inr y =>
        have hEq :
            (∑ σ : (∀ k : Γ.Key, M.ι),
              (∏ k, (Function.update qprof g T.w) k (σ k)) * Xout g σ r) =
            (N : ℝ) * ∑ i, T.w i * v i y := by
          have hrowmean :
              (FinProb.pi P').expect (fun σ =>
                (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                  rawCellMean_q_s07_prof Γ M σ (g, t) y)) =
              (N : ℝ) * ∑ i, T.w i * v i y := by
            rw [FinProb.expect_smul, FinProb.expect_smul]
            calc
              (N : ℝ) * (coeff *
                  (FinProb.pi P').expect (fun σ => ∑ t : Γ.AuxWord,
                    rawCellMean_q_s07_prof Γ M σ (g, t) y)) =
                (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                    (FinProb.pi P').expect (fun σ =>
                      rawCellMean_q_s07_prof Γ M σ (g, t) y)) := by
                    congr 2
                    exact (expect_sum_q_s07_prof (FinProb.pi P')
                      (fun t σ => rawCellMean_q_s07_prof Γ M σ (g, t) y)).symm
              _ = (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                    rawRowMean Γ M P' (g, t) y) := by
                    congr 2
              _ = (N : ℝ) * ∑ i, T.w i * v i y := by
                    congr 1
                    change coeff * ∑ t : Γ.AuxWord,
                      rawRowMean Γ M (Function.update Q g T) (g, t) y =
                      ∑ i, T.w i * (coeff * ∑ t : Γ.AuxWord,
                        rawRowMean Γ M (Function.update Q g
                          (pointProb_q_s07_prof i)) (g, t) y)
                    exact rawRowAverage_update_mix_q_s07_prof Γ M Q g T y coeff
          calc
            _ = ∑ σ : (∀ k : Γ.Key, M.ι),
                  (∏ k, (Function.update qprof g T.w) k (σ k)) *
                    ((N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                      rawCellMean_q_s07_prof Γ M σ (g, t) y)) := by
                  apply Finset.sum_congr rfl
                  intro σ hσ
                  simp [Xout, hd]
            _ = (FinProb.pi P').expect (fun σ =>
                  (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                    rawCellMean_q_s07_prof Γ M σ (g, t) y)) := hpayexp _
            _ = (N : ℝ) * ∑ i, T.w i * v i y := hrowmean
        have hscale : (N : ℝ) * (4 / (κ * (N : ℝ))) = 4 / κ := by
          field_simp [ne_of_gt hκ, (show (N : ℝ) ≠ 0 by positivity)]
        calc
          (∑ σ : (∀ k : Γ.Key, M.ι),
              (∏ k, (Function.update qprof g T.w) k (σ k)) * Xout g σ r) =
            (N : ℝ) * ∑ i, T.w i * v i y := hEq
          _ ≤ (N : ℝ) * (4 / (κ * (N : ℝ))) :=
            mul_le_mul_of_nonneg_left (hvbound y) (by positivity)
          _ = 4 / κ := hscale
  obtain ⟨qprof, hq0, hqsum, hqout⟩ := simultaneous_profiles Xout b hresp
  let Qfinal : Γ.Key → FinProb M.ι := fun g =>
    ⟨qprof g, hq0 g, hqsum g⟩
  have hfinalpay (F : (∀ k : Γ.Key, M.ι) → ℝ) :
      (∑ σ : (∀ k : Γ.Key, M.ι),
        (∏ k, qprof k (σ k)) * F σ) = (FinProb.pi Qfinal).expect F := by
    simp [FinProb.expect, FinProb.pi, Qfinal]
  refine ⟨{
    Q := Qfinal
    mu_mean := ?_
    row_mean := ?_
  }⟩
  · intro g x
    have h := hqout g (finSumFinEquiv (Sum.inl x))
    have hEq :
        (∑ σ : (∀ k : Γ.Key, M.ι),
          (∏ k, qprof k (σ k)) * Xout g σ (finSumFinEquiv (Sum.inl x))) =
        (N : ℝ) * ∑ i, qprof g i * (M.μ i).w x := by
      calc
        _ = (FinProb.pi Qfinal).expect (fun σ =>
              (N : ℝ) * (M.μ (σ g)).w x) := by
                calc
                  _ = ∑ σ : (∀ k : Γ.Key, M.ι),
                        (∏ k, qprof k (σ k)) *
                          ((N : ℝ) * (M.μ (σ g)).w x) := by
                            apply Finset.sum_congr rfl
                            intro σ hσ
                            simp [Xout, decode]
                  _ = _ := hfinalpay _
        _ = (N : ℝ) * ∑ i, qprof g i * (M.μ i).w x := by
              have hcoord := pi_expect_coordinate_q_s07_prof Qfinal g
                (fun i => (M.μ i).w x)
              rw [FinProb.expect_smul, hcoord]
              simp [Qfinal, FinProb.expect]
    rw [hEq] at h
    exact h
  · intro g y
    have h := hqout g (finSumFinEquiv (Sum.inr y))
    have hdecode : decode (finSumFinEquiv (Sum.inr y)) = Sum.inr y := by
      simpa [decode] using finSumFinEquiv_symm_apply_natAdd (m := N) (n := N) y
    have hEq :
        (∑ σ : (∀ k : Γ.Key, M.ι),
          (∏ k, qprof k (σ k)) * Xout g σ (finSumFinEquiv (Sum.inr y))) =
        (N : ℝ) * (coeff * ∑ t : Γ.AuxWord, rawRowMean Γ M Qfinal (g, t) y) := by
      calc
        _ = (FinProb.pi Qfinal).expect (fun σ =>
            (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
              rawCellMean_q_s07_prof Γ M σ (g, t) y)) := by
              calc
                _ = ∑ σ : (∀ k : Γ.Key, M.ι),
                      (∏ k, qprof k (σ k)) *
                        ((N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                          rawCellMean_q_s07_prof Γ M σ (g, t) y)) := by
                  apply Finset.sum_congr rfl
                  intro σ hσ
                  have hX : Xout g σ (finSumFinEquiv (Sum.inr y)) =
                      (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                        rawCellMean_q_s07_prof Γ M σ (g, t) y) := by
                    change (match decode (finSumFinEquiv (Sum.inr y)) with
                      | Sum.inl x => (N : ℝ) * (M.μ (σ g)).w x
                      | Sum.inr z => (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
                          rawCellMean_q_s07_prof Γ M σ (g, t) z)) = _
                    rw [hdecode]
                  rw [hX]
                _ = _ := hfinalpay _
        _ = (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
              (FinProb.pi Qfinal).expect (fun σ =>
                rawCellMean_q_s07_prof Γ M σ (g, t) y)) := by
                  rw [FinProb.expect_smul, FinProb.expect_smul]
                  congr 2
                  exact (expect_sum_q_s07_prof (FinProb.pi Qfinal)
                    (fun t σ => rawCellMean_q_s07_prof Γ M σ (g, t) y)).symm
        _ = (N : ℝ) * (coeff * ∑ t : Γ.AuxWord,
              rawRowMean Γ M Qfinal (g, t) y) := by
              congr 2
    rw [hEq] at h
    simpa [Qfinal, coeff] using h

end HypercubeRamsey.S07
