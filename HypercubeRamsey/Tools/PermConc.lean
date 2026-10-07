import HypercubeRamsey.Tools.Concentration

/-!
# Random-order concentration

X-PermConc is the finite permutation bounded-differences estimate, obtained from the reveal martingale and
the finite Azuma tool. A transposition changes at most two images.
-/

namespace HypercubeRamsey

/-- Uniform finite law on permutations of a finite type. -/
noncomputable def uniformPermutationLaw {ι : Type*} [Fintype ι] [DecidableEq ι] :
    FinProb (Equiv.Perm ι) := by
  classical
  exact FinProb.uniform Finset.univ ⟨Equiv.refl ι, by simp⟩

private theorem FinProb.expect_bind_const {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α × β → ℝ) :
    (FinProb.bind P (fun _ => Q)).expect f =
      P.expect (fun a => Q.expect (fun b => f (a, b))) := by
  classical
  unfold FinProb.expect FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem FinProb.expect_uniform_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (ha : (Finset.univ : Finset α).Nonempty) (hb : (Finset.univ : Finset β).Nonempty)
    (f : β → ℝ) :
    (FinProb.uniform Finset.univ ha).expect (fun x => f (e x)) =
      (FinProb.uniform Finset.univ hb).expect f := by
  classical
  let P := FinProb.uniform (Finset.univ : Finset α) ha
  let Q := FinProb.uniform (Finset.univ : Finset β) hb
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  have hw (x : α) : P.w x = Q.w (e x) := by
    simp [P, Q, FinProb.uniform, hcard]
  unfold FinProb.expect
  calc
    _ = ∑ x, Q.w (e x) * f (e x) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hw]
    _ = ∑ y, Q.w y * f y := Equiv.sum_comp e (fun y : β => Q.w y * f y)

private def permFiberEquiv {n : ℕ} (p : Fin (n + 1)) :
    Equiv.Perm (Fin n) ≃ {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = p} where
  toFun σ := ⟨Equiv.Perm.decomposeFin.symm (p, σ), by simp⟩
  invFun σ := (Equiv.Perm.decomposeFin σ.1).2
  left_inv σ := by simp
  right_inv σ := by
    apply Subtype.ext
    have hp : (Equiv.Perm.decomposeFin σ.1).1 = p := by
      calc
        _ = σ.1 0 := by simp [Equiv.Perm.decomposeFin]
        _ = p := σ.2
    have hpair : (p, (Equiv.Perm.decomposeFin σ.1).2) = Equiv.Perm.decomposeFin σ.1 :=
      Prod.ext hp.symm rfl
    calc
      Equiv.Perm.decomposeFin.symm (p, (Equiv.Perm.decomposeFin σ.1).2) =
          Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin σ.1) :=
        congrArg Equiv.Perm.decomposeFin.symm hpair
      _ = σ.1 := Equiv.Perm.decomposeFin.symm_apply_apply σ.1

private def permFiberSwap {n : ℕ} (p p' : Fin (n + 1)) :
    {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = p} ≃
      {σ : Equiv.Perm (Fin (n + 1)) // σ 0 = p'} where
  toFun σ := ⟨Equiv.swap p p' * σ.1, by simp [σ.2]⟩
  invFun σ := ⟨Equiv.swap p p' * σ.1, by simp [σ.2]⟩
  left_inv σ := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv σ := by
    apply Subtype.ext
    simp [mul_assoc]

private def permTailCouple {n : ℕ} (p p' : Fin (n + 1)) :
    Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
  (permFiberEquiv p).trans ((permFiberSwap p p').trans (permFiberEquiv p').symm)

private theorem permTailCouple_full {n : ℕ} (p p' : Fin (n + 1))
    (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p', permTailCouple p p' σ) =
      Equiv.swap p p' * Equiv.Perm.decomposeFin.symm (p, σ) := by
  have h := (permFiberEquiv p').apply_symm_apply
    (permFiberSwap p p' (permFiberEquiv p σ))
  exact congrArg Subtype.val h

private theorem perm_swap_hamming_le_two {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (a b : α) :
    (Finset.univ.filter (fun x : α => σ x ≠ (Equiv.swap a b * σ) x)).card ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun x : α => σ x ≠ (Equiv.swap a b * σ) x)
  have hsub : s ⊆ ({σ.symm a, σ.symm b} : Finset α) := by
    intro x hx
    have hchange : σ x ≠ Equiv.swap a b (σ x) := (Finset.mem_filter.mp hx).2
    have hcase : σ x = a ∨ σ x = b := by
      by_cases hxa : σ x = a
      · exact Or.inl hxa
      · by_cases hxb : σ x = b
        · exact Or.inr hxb
        · exfalso
          apply hchange
          simp [Equiv.swap_apply_def, hxa, hxb]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcase with h | h
    · left
      apply σ.injective
      simpa using h
    · right
      apply σ.injective
      simpa using h
  have hcard : s.card ≤ ({σ.symm a, σ.symm b} : Finset α).card := Finset.card_le_card hsub
  calc
    _ = s.card := rfl
    _ ≤ 2 := hcard.trans Finset.card_le_two

private theorem uniformPermutation_expect_decompose {n : ℕ}
    (F : Equiv.Perm (Fin (n + 1)) → ℝ) :
    (uniformPermutationLaw (ι := Fin (n + 1))).expect F =
      (FinProb.bind
        (FinProb.uniform Finset.univ ⟨0, Finset.mem_univ _⟩)
        (fun _ => uniformPermutationLaw (ι := Fin n))).expect
          (fun pair => F (Equiv.Perm.decomposeFin.symm pair)) := by
  classical
  let P0 : FinProb (Fin (n + 1)) := FinProb.uniform Finset.univ ⟨0, Finset.mem_univ _⟩
  let Pt : FinProb (Equiv.Perm (Fin n)) := uniformPermutationLaw (ι := Fin n)
  let Dec : (Fin (n + 1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n + 1)) :=
    Equiv.Perm.decomposeFin.symm
  have hcard : Fintype.card (Equiv.Perm (Fin (n + 1))) =
      Fintype.card (Fin (n + 1)) * Fintype.card (Equiv.Perm (Fin n)) := by
    have h := Fintype.card_congr (Equiv.Perm.decomposeFin (n := n))
    rw [Fintype.card_prod] at h
    exact h
  have hcardNat : Fintype.card (Equiv.Perm (Fin (n + 1))) =
      (n + 1) * Fintype.card (Equiv.Perm (Fin n)) := by
    calc
      _ = Fintype.card (Fin (n + 1)) * Fintype.card (Equiv.Perm (Fin n)) := hcard
      _ = _ := by simp
  have hcardR : (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) =
      (n + 1 : ℝ) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast hcardNat
  have hpos0 : (0 : ℝ) < (Fintype.card (Fin (n + 1)) : ℝ) := by positivity
  have hposTail : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have hn : Nonempty (Equiv.Perm (Fin n)) := ⟨Equiv.refl _⟩
    exact_mod_cast (Fintype.card_pos_iff.mpr hn)
  have hweight (pair : Fin (n + 1) × Equiv.Perm (Fin n)) :
      (uniformPermutationLaw (ι := Fin (n + 1))).w (Dec pair) =
        P0.w pair.1 * Pt.w pair.2 := by
    simp [P0, Pt, Dec, uniformPermutationLaw, FinProb.uniform]
    rw [hcardR]
    field_simp [ne_of_gt hpos0, ne_of_gt hposTail]
  unfold FinProb.expect
  calc
    _ = ∑ pair, (uniformPermutationLaw (ι := Fin (n + 1))).w (Dec pair) * F (Dec pair) :=
      (Equiv.sum_comp Dec
        (fun σ => (uniformPermutationLaw (ι := Fin (n + 1))).w σ * F σ)).symm
    _ = ∑ pair, (P0.w pair.1 * Pt.w pair.2) * F (Dec pair) := by
      apply Finset.sum_congr rfl
      intro pair hp
      rw [hweight]
    _ = _ := by rfl

private theorem FinProb.expect_abs_sub_le {α : Type*} [Fintype α]
    (P : FinProb α) (X Y : α → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hXY : ∀ x, |X x - Y x| ≤ c) : |P.expect X - P.expect Y| ≤ c := by
  have hbound (A B : α → ℝ) (hAB : ∀ x, |A x - B x| ≤ c) :
      P.expect A ≤ P.expect B + c := by
    unfold FinProb.expect
    calc
      _ ≤ ∑ x, P.w x * (B x + c) := by
        apply Finset.sum_le_sum
        intro x hx
        have h := (abs_le.mp (hAB x)).2
        exact mul_le_mul_of_nonneg_left (by linarith) (P.nonneg x)
      _ = P.expect B + c := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        simp [FinProb.expect, P.sum_eq_one]
  have hle := hbound X Y hXY
  have hge := hbound Y X (fun x => by simpa [abs_sub_comm] using hXY x)
  have hge' : P.expect Y ≤ P.expect X + c := hge
  have hle' : P.expect X ≤ P.expect Y + c := hle
  apply abs_le.mpr
  constructor <;> linarith

private theorem FinProb.pr_le_one {α : Type*} [Fintype α]
    (P : FinProb α) (A : α → Prop) : P.pr A ≤ 1 := by
  classical
  unfold FinProb.pr
  calc
    _ ≤ ∑ x, P.w x := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases h : A x <;> simp [h, P.nonneg]
    _ = 1 := P.sum_eq_one

private theorem permDecomposeFin_tail_hamming_le {n : ℕ} (p : Fin (n + 1))
    (σ τ : Equiv.Perm (Fin n))
    (hστ : (Finset.univ.filter (fun j : Fin n => σ j ≠ τ j)).card ≤ 2) :
    (Finset.univ.filter (fun i : Fin (n + 1) =>
      Equiv.Perm.decomposeFin.symm (p, σ) i ≠ Equiv.Perm.decomposeFin.symm (p, τ) i)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => σ j ≠ τ j)
  let T := Finset.univ.filter (fun i : Fin (n + 1) =>
    Equiv.Perm.decomposeFin.symm (p, σ) i ≠ Equiv.Perm.decomposeFin.symm (p, τ) i)
  have hsub : T ⊆ S.image Fin.succ := by
    intro i hi
    have hdiff : Equiv.Perm.decomposeFin.symm (p, σ) i ≠
        Equiv.Perm.decomposeFin.symm (p, τ) i := (Finset.mem_filter.mp hi).2
    obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
    · simp [T] at hi
    · refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      intro hEq
      apply hdiff
      simp [hEq]
  calc
    _ = T.card := rfl
    _ ≤ (S.image Fin.succ).card := Finset.card_le_card hsub
    _ = S.card := Finset.card_image_of_injective _ (Fin.succ_injective n)
    _ ≤ 2 := hστ


private theorem permFin_mgf :
    ∀ n (f : Equiv.Perm (Fin n) → ℝ) (c : ℝ) (hc : 0 ≤ c)
      (hlip : ∀ σ τ : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card ≤ 2 → |f σ - f τ| ≤ c)
      (r : ℝ),
      (uniformPermutationLaw (ι := Fin n)).expect
        (fun σ => Real.exp (r * (f σ - (uniformPermutationLaw (ι := Fin n)).expect f))) ≤
          Real.exp (r ^ 2 * (n : ℝ) * c ^ 2 / 8) := by
  intro n
  induction n with
  | zero =>
      intro f c hc hlip r
      let P := uniformPermutationLaw (ι := Fin 0)
      let a : ℝ := f (Equiv.refl _)
      have hconst (σ : Equiv.Perm (Fin 0)) : f σ = a := by
        have hσ : σ = Equiv.refl _ := by
          ext x
          exact Fin.elim0 x
        simp [a, hσ]
      have hbound (σ : Equiv.Perm (Fin 0)) : a ≤ f σ ∧ f σ ≤ a := by
        rw [hconst σ]
        exact ⟨le_rfl, le_rfl⟩
      have h := xHoeffdingLemma P f a a r le_rfl hbound
      simpa [P, a] using h
  | succ n ih =>
      intro f c hc hlip r
      let P0 : FinProb (Fin (n + 1)) :=
        FinProb.uniform Finset.univ ⟨0, Finset.mem_univ _⟩
      let Pt : FinProb (Equiv.Perm (Fin n)) := uniformPermutationLaw (ι := Fin n)
      let Dec : (Fin (n + 1) × Equiv.Perm (Fin n)) ≃ Equiv.Perm (Fin (n + 1)) :=
        Equiv.Perm.decomposeFin.symm
      let K : Fin (n + 1) × Equiv.Perm (Fin n) → ℝ := fun z => f (Dec z)
      let g : Fin (n + 1) → ℝ := fun p => Pt.expect (fun σ => K (p, σ))
      let I : ℝ := (uniformPermutationLaw (ι := Fin (n + 1))).expect f
      let V : ℝ := (n : ℝ) * c ^ 2
      have hmean : I = P0.expect g := by
        calc
          _ = (FinProb.bind P0 (fun _ => Pt)).expect K :=
            by simpa [I, K, Dec] using uniformPermutation_expect_decompose f
          _ = P0.expect g := by
            simpa [g, K] using FinProb.expect_bind_const P0 Pt K
      have htailLip (p : Fin (n + 1)) :
          ∀ σ τ : Equiv.Perm (Fin n),
            (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card ≤ 2 →
              |K (p, σ) - K (p, τ)| ≤ c := by
        intro σ τ hστ
        apply hlip (Dec (p, σ)) (Dec (p, τ))
        exact permDecomposeFin_tail_hamming_le p σ τ hστ
      have htailMgf (p : Fin (n + 1)) :
          Pt.expect (fun σ => Real.exp (r * (K (p, σ) - g p))) ≤
            Real.exp (r ^ 2 * V / 8) := by
        have h := ih (fun σ => K (p, σ)) c hc (htailLip p) r
        simpa [g, V, K, Pt, mul_assoc] using h
      have hgd (p p' : Fin (n + 1)) : |g p - g p'| ≤ c := by
        let C := permTailCouple p p'
        have hcomp :
            Pt.expect (fun σ => K (p', C σ)) = g p' := by
          simpa [Pt, g, K, C, uniformPermutationLaw] using
            FinProb.expect_uniform_equiv C
              (⟨Equiv.refl _, Finset.mem_univ _⟩ : (Finset.univ : Finset (Equiv.Perm (Fin n))).Nonempty)
              ⟨Equiv.refl _, Finset.mem_univ _⟩
              (fun σ => K (p', σ))
        have hpoint (σ : Equiv.Perm (Fin n)) : |K (p, σ) - K (p', C σ)| ≤ c := by
          apply hlip (Dec (p, σ)) (Dec (p', C σ))
          rw [permTailCouple_full]
          exact perm_swap_hamming_le_two (Dec (p, σ)) p p'
        have h := FinProb.expect_abs_sub_le Pt (fun σ => K (p, σ))
          (fun σ => K (p', C σ)) c hc hpoint
        simpa [g, hcomp] using h
      have hα : (Finset.univ : Finset (Fin (n + 1))).Nonempty :=
        ⟨0, Finset.mem_univ _⟩
      have hhead : P0.expect (fun p => Real.exp (r * (g p - P0.expect g))) ≤
          Real.exp (r ^ 2 * c ^ 2 / 8) := by
        obtain ⟨pLo, hpLo, hLo⟩ := Finset.exists_min_image
          (Finset.univ : Finset (Fin (n + 1))) g hα
        obtain ⟨pHi, hpHi, hHi⟩ := Finset.exists_max_image
          (Finset.univ : Finset (Fin (n + 1))) g hα
        let lo : ℝ := g pLo
        let hi : ℝ := g pHi
        have hbounds (p : Fin (n + 1)) : lo ≤ g p ∧ g p ≤ hi := by
          constructor
          · exact hLo p (Finset.mem_univ _)
          · exact hHi p (Finset.mem_univ _)
        have hwidth : hi - lo ≤ c := by
          have h := (abs_le.mp (hgd pHi pLo)).2
          dsimp [hi, lo]
          linarith
        have hinterval : lo ≤ hi := (hbounds pHi).1
        have hhoeff := xHoeffdingLemma P0 g lo hi r hinterval hbounds
        have hsq : (hi - lo) ^ 2 ≤ c ^ 2 := by
          have hnonneg : 0 ≤ hi - lo := sub_nonneg.mpr hinterval
          nlinarith [mul_nonneg (sub_nonneg.mpr hwidth) (add_nonneg hc hnonneg)]
        calc
          _ ≤ Real.exp (r ^ 2 * (hi - lo) ^ 2 / 8) := hhoeff
          _ ≤ Real.exp (r ^ 2 * c ^ 2 / 8) := by
            apply Real.exp_le_exp.mpr
            nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hsq)]
      have hsplit (r : ℝ) :
          (uniformPermutationLaw (ι := Fin (n + 1))).expect
              (fun σ => Real.exp (r * (f σ - I))) =
            P0.expect (fun p => Pt.expect
              (fun σ => Real.exp (r * (K (p, σ) - I)))) := by
        calc
          _ = (FinProb.bind P0 (fun _ => Pt)).expect
                (fun z => Real.exp (r * (K z - I))) := by
              simpa [K, I] using
                uniformPermutation_expect_decompose
                  (fun σ => Real.exp (r * (f σ - I)))
          _ = P0.expect (fun p => Pt.expect
                (fun σ => Real.exp (r * (K (p, σ) - I)))) := by
              simpa using FinProb.expect_bind_const P0 Pt
                (fun z => Real.exp (r * (K z - I)))
      have hfactor (p : Fin (n + 1)) :
          Pt.expect (fun σ => Real.exp (r * (K (p, σ) - I))) =
            Real.exp (r * (g p - I)) *
              Pt.expect (fun σ => Real.exp (r * (K (p, σ) - g p))) := by
        unfold FinProb.expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ hσ
        have he : r * (K (p, σ) - I) =
            r * (g p - I) + r * (K (p, σ) - g p) := by ring
        change Pt.w σ * Real.exp (r * (K (p, σ) - I)) =
          Real.exp (r * (g p - I)) * (Pt.w σ * Real.exp (r * (K (p, σ) - g p)))
        rw [he, Real.exp_add]
        ring
      have hterm (p : Fin (n + 1)) :
          Pt.expect (fun σ => Real.exp (r * (K (p, σ) - I))) ≤
            Real.exp (r * (g p - I)) * Real.exp (r ^ 2 * V / 8) := by
        calc
          _ = Real.exp (r * (g p - I)) *
                Pt.expect (fun σ => Real.exp (r * (K (p, σ) - g p))) := hfactor p
          _ ≤ _ := mul_le_mul_of_nonneg_left (htailMgf p) (Real.exp_nonneg _)
      have hheadI : P0.expect (fun p => Real.exp (r * (g p - I))) ≤
          Real.exp (r ^ 2 * c ^ 2 / 8) := by simpa [hmean] using hhead
      have hmgf :
          (uniformPermutationLaw (ι := Fin (n + 1))).expect
              (fun σ => Real.exp (r * (f σ - I))) ≤
            Real.exp (r ^ 2 * (V + c ^ 2) / 8) := by
        calc
          _ = P0.expect (fun p => Pt.expect
                (fun σ => Real.exp (r * (K (p, σ) - I)))) := hsplit r
          _ ≤ P0.expect (fun p =>
                Real.exp (r * (g p - I)) * Real.exp (r ^ 2 * V / 8)) := by
            unfold FinProb.expect
            apply Finset.sum_le_sum
            intro p hp
            exact mul_le_mul_of_nonneg_left (hterm p) (P0.nonneg p)
          _ ≤ Real.exp (r ^ 2 * V / 8) *
                Real.exp (r ^ 2 * c ^ 2 / 8) := by
            calc
              _ = Real.exp (r ^ 2 * V / 8) *
                    P0.expect (fun p => Real.exp (r * (g p - I))) := by
                  unfold FinProb.expect
                  simp [Finset.mul_sum, mul_left_comm, mul_comm]
              _ ≤ _ := mul_le_mul_of_nonneg_left hheadI (Real.exp_nonneg _)
          _ = Real.exp (r ^ 2 * (V + c ^ 2) / 8) := by
            rw [← Real.exp_add]
            congr 1
            ring
      have hV : V + c ^ 2 = (n + 1 : ℝ) * c ^ 2 := by
        dsimp [V]
        push_cast
        ring
      have hmgf' :
          (uniformPermutationLaw (ι := Fin (n + 1))).expect
              (fun σ => Real.exp (r * (f σ - I))) ≤
            Real.exp (r ^ 2 * ((n + 1 : ℝ) * c ^ 2) / 8) := by
        simpa only [hV] using hmgf
      simpa [I, Nat.cast_add, mul_assoc] using hmgf'

private theorem permCongr_hamming_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (σ τ : Equiv.Perm β) :
    (Finset.univ.filter (fun i : α => (Equiv.permCongr e).symm σ i ≠
      (Equiv.permCongr e).symm τ i)).card =
    (Finset.univ.filter (fun j : β => σ j ≠ τ j)).card := by
  classical
  let E := Equiv.permCongr e
  let S := Finset.univ.filter (fun i : α => E.symm σ i ≠ E.symm τ i)
  let T := Finset.univ.filter (fun j : β => σ j ≠ τ j)
  have hset : S.map e.toEmbedding = T := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
      have hchange : E.symm σ i ≠ E.symm τ i := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro hEq
        apply hchange
        change σ (e i) = τ (e i) at hEq
        simpa [E, Equiv.permCongr_symm_apply, hEq]
    · intro hj
      have hchange : σ j ≠ τ j := (Finset.mem_filter.mp hj).2
      apply Finset.mem_map.mpr
      refine ⟨e.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply j⟩
      intro hEq
      apply hchange
      have hEq' : e.symm (σ j) = e.symm (τ j) := by
        simpa [E, Equiv.permCongr_symm_apply] using hEq
      exact e.symm.injective hEq'
  calc
    _ = S.card := rfl
    _ = (S.map e.toEmbedding).card := by simp
    _ = T.card := by rw [hset]

/-- X-PermConc: a statistic changing by at most `c` under any transposition has a sub-Gaussian tail under
the uniform random order. -/
theorem xPermConc {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Equiv.Perm ι → ℝ)
    (c t : ℝ) (hc : 0 < c) (ht : 0 < t)
    (hlip : ∀ σ τ : Equiv.Perm ι,
      (Finset.univ.filter (fun i : ι => σ i ≠ τ i)).card ≤ 2 → |f σ - f τ| ≤ c) :
    (uniformPermutationLaw (ι := ι)).pr
        (fun σ => t ≤ |f σ - (uniformPermutationLaw (ι := ι)).expect f|) ≤
      2 * Real.exp (-2 * t ^ 2 / ((Fintype.card ι : ℝ) * c ^ 2)) := by
  classical
  by_cases hι : Nonempty ι
  · let n := Fintype.card ι
    let e : ι ≃ Fin n := Fintype.equivFin ι
    let E := Equiv.permCongr e
    let fFin : Equiv.Perm (Fin n) → ℝ := fun σ => f (E.symm σ)
    have hc0 : 0 ≤ c := by
      have h := hlip (Equiv.refl ι) (Equiv.refl ι) (by simp)
      simpa using h
    have hperm : (Finset.univ : Finset (Equiv.Perm ι)).Nonempty :=
      ⟨Equiv.refl ι, Finset.mem_univ _⟩
    have hpermFin :
        (Finset.univ : Finset (Equiv.Perm (Fin n))).Nonempty :=
      ⟨Equiv.refl _, Finset.mem_univ _⟩
    have hmean : (uniformPermutationLaw (ι := ι)).expect f =
        (uniformPermutationLaw (ι := Fin n)).expect fFin := by
      calc
        _ = (uniformPermutationLaw (ι := ι)).expect (fun σ => fFin (E σ)) := by
          congr 1
          funext σ
          exact congrArg f (E.symm_apply_apply σ).symm
        _ = (uniformPermutationLaw (ι := Fin n)).expect fFin :=
          FinProb.expect_uniform_equiv E hperm hpermFin fFin
    have hLipFin : ∀ σ τ : Equiv.Perm (Fin n),
        (Finset.univ.filter (fun i : Fin n => σ i ≠ τ i)).card ≤ 2 →
          |fFin σ - fFin τ| ≤ c := by
      intro σ τ hστ
      apply hlip (E.symm σ) (E.symm τ)
      rw [permCongr_hamming_card e σ τ]
      exact hστ
    have hmgf (r : ℝ) :
        (uniformPermutationLaw (ι := ι)).expect
          (fun σ => Real.exp (r * (f σ - (uniformPermutationLaw (ι := ι)).expect f))) ≤
            Real.exp (r ^ 2 * (Fintype.card ι : ℝ) * c ^ 2 / 8) := by
      have hfin := permFin_mgf n fFin c hc0 hLipFin r
      have htrans := FinProb.expect_uniform_equiv E hperm hpermFin
        (fun σ => Real.exp (r * (fFin σ - (uniformPermutationLaw (ι := Fin n)).expect fFin)))
      have hfun :
          (fun σ => Real.exp (r * (f σ - (uniformPermutationLaw (ι := ι)).expect f))) =
            (fun σ => Real.exp (r *
              (fFin (E σ) - (uniformPermutationLaw (ι := Fin n)).expect fFin))) := by
        funext σ
        simp [fFin, hmean]
      calc
        _ = (uniformPermutationLaw (ι := ι)).expect
              (fun σ => Real.exp (r *
                (fFin (E σ) - (uniformPermutationLaw (ι := Fin n)).expect fFin))) := by
              rw [hfun]
        _ = (uniformPermutationLaw (ι := Fin n)).expect
              (fun σ => Real.exp (r *
                (fFin σ - (uniformPermutationLaw (ι := Fin n)).expect fFin))) := htrans
        _ ≤ Real.exp (r ^ 2 * (n : ℝ) * c ^ 2 / 8) := hfin
        _ = Real.exp (r ^ 2 * (Fintype.card ι : ℝ) * c ^ 2 / 8) := by
          simp [n]
    have hmgfNeg (r : ℝ) :
        (uniformPermutationLaw (ι := ι)).expect
          (fun σ => Real.exp (r * -(f σ - (uniformPermutationLaw (ι := ι)).expect f))) ≤
            Real.exp (r ^ 2 * (Fintype.card ι : ℝ) * c ^ 2 / 8) := by
      have h := hmgf (-r)
      have hfun : (fun σ => Real.exp (r * -(f σ - (uniformPermutationLaw (ι := ι)).expect f))) =
          (fun σ => Real.exp ((-r) * (f σ - (uniformPermutationLaw (ι := ι)).expect f))) := by
        funext σ
        congr 1
        ring
      have hr2 : (-r) ^ 2 = r ^ 2 := by ring
      rw [hfun]
      simpa [hr2] using h
    let S : ℝ := (Fintype.card ι : ℝ) * c ^ 2
    have hS : 0 < S := by
      dsimp [S]
      have hN : (0 : ℝ) < (Fintype.card ι : ℝ) := by
        exact_mod_cast (Fintype.card_pos_iff.mpr hι)
      positivity
    let r : ℝ := 4 * t / S
    have hr : 0 < r := by dsimp [r]; positivity
    have hupper :
        (uniformPermutationLaw (ι := ι)).pr
          (fun σ => t ≤ f σ - (uniformPermutationLaw (ι := ι)).expect f) ≤
            Real.exp (-2 * t ^ 2 / S) := by
      calc
        _ ≤ Real.exp (-r * t) *
            (uniformPermutationLaw (ι := ι)).expect
              (fun σ => Real.exp (r * (f σ - (uniformPermutationLaw (ι := ι)).expect f))) :=
          FinProb.pr_exp_markov _ _ r t hr.le
        _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * S / 8) :=
          mul_le_mul_of_nonneg_left (by simpa [S, mul_assoc] using hmgf r) (Real.exp_nonneg _)
        _ = Real.exp (-2 * t ^ 2 / S) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [r]
          field_simp [ne_of_gt hS]
          ring
    have hlower :
        (uniformPermutationLaw (ι := ι)).pr
          (fun σ => t ≤ -(f σ - (uniformPermutationLaw (ι := ι)).expect f)) ≤
            Real.exp (-2 * t ^ 2 / S) := by
      calc
        _ ≤ Real.exp (-r * t) *
            (uniformPermutationLaw (ι := ι)).expect
              (fun σ => Real.exp (r * -(f σ - (uniformPermutationLaw (ι := ι)).expect f))) :=
          FinProb.pr_exp_markov _ _ r t hr.le
        _ ≤ Real.exp (-r * t) * Real.exp (r ^ 2 * S / 8) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          simpa [S, mul_assoc] using hmgfNeg r
        _ = Real.exp (-2 * t ^ 2 / S) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [r]
          field_simp [ne_of_gt hS]
          ring
    have hsplit (σ : Equiv.Perm ι) :
        t ≤ |f σ - (uniformPermutationLaw (ι := ι)).expect f| →
          (t ≤ f σ - (uniformPermutationLaw (ι := ι)).expect f ∨
            t ≤ -(f σ - (uniformPermutationLaw (ι := ι)).expect f)) := by
      intro h
      by_cases hnonneg : 0 ≤ f σ - (uniformPermutationLaw (ι := ι)).expect f
      · left
        simpa [abs_of_nonneg hnonneg] using h
      · right
        have habs : |f σ - (uniformPermutationLaw (ι := ι)).expect f| =
            -(f σ - (uniformPermutationLaw (ι := ι)).expect f) :=
          abs_of_neg (lt_of_not_ge hnonneg)
        rw [habs] at h
        exact h
    have hfinal :
        (uniformPermutationLaw (ι := ι)).pr
            (fun σ => t ≤ |f σ - (uniformPermutationLaw (ι := ι)).expect f|) ≤
          2 * Real.exp (-2 * t ^ 2 / S) := by
      calc
        _ ≤ (uniformPermutationLaw (ι := ι)).pr
            (fun σ => t ≤ f σ - (uniformPermutationLaw (ι := ι)).expect f ∨
              t ≤ -(f σ - (uniformPermutationLaw (ι := ι)).expect f)) :=
          FinProb.pr_mono _ _ _ (fun σ => hsplit σ)
        _ ≤ (uniformPermutationLaw (ι := ι)).pr
            (fun σ => t ≤ f σ - (uniformPermutationLaw (ι := ι)).expect f) +
              (uniformPermutationLaw (ι := ι)).pr
                (fun σ => t ≤ -(f σ - (uniformPermutationLaw (ι := ι)).expect f)) :=
          FinProb.pr_union_le _ _ _
        _ ≤ 2 * Real.exp (-2 * t ^ 2 / S) := by linarith [hupper, hlower]
    simpa [S] using hfinal
  · have hprob := FinProb.pr_le_one (uniformPermutationLaw (ι := ι))
      (fun σ => t ≤ |f σ - (uniformPermutationLaw (ι := ι)).expect f|)
    haveI : IsEmpty ι := not_nonempty_iff.mp hι
    simpa using le_trans hprob (by norm_num : (1 : ℝ) ≤ 2)

end HypercubeRamsey
